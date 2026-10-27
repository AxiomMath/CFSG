module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.Quasithin.Background.B6Defs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

section Setting

variable {X : Type} [Group X]

@[expose] def gnV (T : Subgroup X) : Subgroup X :=
  Subgroup.normalClosure (Quasithin.omegaOneCenterOf T : Set X)

@[expose] def gnC (T : Subgroup X) : Subgroup X := Subgroup.centralizer (gnV T : Set X)

instance gnC_normal (T : Subgroup X) : (gnC T).Normal where
  conj_mem n hn g := by
    rw [gnC, Subgroup.mem_centralizer_iff] at hn ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ gnV T := by
      have : g⁻¹ * y * (g⁻¹)⁻¹ ∈ gnV T :=
        (Subgroup.normalClosure_normal (s := (Quasithin.omegaOneCenterOf T : Set X))).conj_mem y hy
          g⁻¹
      simpa using this
    have h := hn _ hy'
    calc y * (g * n * g⁻¹) = g * ((g⁻¹ * y * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * n * g⁻¹ * y := by group

@[expose] def gnImg (T Y : Subgroup X) : Subgroup (X ⧸ gnC T) :=
  Y.map (QuotientGroup.mk' (gnC T))

@[expose] def pElementSubgroup {Y : Type*} [Group Y] (p : ℕ) (A : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ A ∧ ∃ k : ℕ, orderOf x = p ^ k}

theorem pElementSubgroup_le {Y : Type*} [Group Y] {p : ℕ} (A : Subgroup Y) :
    pElementSubgroup p A ≤ A :=
  (Subgroup.closure_le A).mpr fun _ hx => hx.1

@[expose] def IsChevIndexTwo : TauCeti.LieTypeIndex → Prop
  | .A _ q | .twistedA _ q | .B _ q | .C _ q | .D _ q | .twistedD _ q | .E6 q | .E7 q | .E8 q
  | .F4 q | .G2 q | .twistedE6 q | .trialityD4 q => q.p = 2
  | .suzuki _ | .reeF4 _ | .tits => True
  | .reeG2 _ => False

@[expose] def IsChevTwo (Y : Type) [Group Y] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsChevIndexTwo d.1 ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))

theorem isChevIndexTwo_of_classical {i : TauCeti.LieTypeIndex} (h : IsClassicalOrG2Index i) :
    IsChevIndexTwo i := by
  cases i <;> simp_all [IsChevIndexTwo, IsClassicalOrG2Index]

theorem isChevTwo_of_classicalTwoOrG2 {Y : Type} [Group Y] (h : IsClassicalTwoOrG2 Y) :
    IsChevTwo Y := by
  rcases h with ⟨d, hd, he⟩ | h | h
  · exact Or.inl ⟨d, isChevIndexTwo_of_classical hd, he⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

@[expose] def IsMinOverBorel {Y : Type*} [Group Y] (L S₀ P : Subgroup Y) : Prop :=
  P ≤ L ∧ L ⊓ Subgroup.normalizer (S₀ : Set Y) < P ∧
    ∀ Q : Subgroup Y, L ⊓ Subgroup.normalizer (S₀ : Set Y) ≤ Q → Q ≤ P →
      Q = L ⊓ Subgroup.normalizer (S₀ : Set Y) ∨ Q = P

structure GNSetting (X : Type) [Group X] [Finite X] (T : Subgroup X) : Prop where
  kGroup : IsKGroup X
  sylow : IsSylowTwoOf T ⊤
  charTwo : CharTwo (⊤ : Subgroup X)
  noXBlock : ∀ Y : Subgroup X, IsSubnormal Y ⊤ → InClassXBlock Y → False

variable [Finite X]

theorem GNSetting.subsingleton_of_eq_bot {T : Subgroup X} (hX : GNSetting X T) (hT : T = ⊥) :
    Subsingleton X := by
  have hQ : pCoreOf 2 (⊤ : Subgroup X) = ⊥ :=
    le_bot_iff.mp (hT ▸ CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow)
  have h : (⊤ : Subgroup X) ⊓ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) ≤
      pCoreOf 2 ⊤ := hX.charTwo
  rw [hQ] at h
  have hc : ∀ a : X, a ∈ (⊤ : Subgroup X) ⊓ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
    intro a
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top a, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
    rw [hg, one_mul, mul_one]
  refine ⟨fun a b => ?_⟩
  rw [Subgroup.mem_bot.mp (h (hc a)), Subgroup.mem_bot.mp (h (hc b))]

theorem GNSetting.ne_bot_of_isComponentOf {T : Subgroup X} (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤) : T ≠ ⊥ := by
  intro hT
  have h1 := hX.subsingleton_of_eq_bot hT
  have h2 : Subsingleton (X ⧸ gnC T) := ⟨fun a b => by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a' b']⟩
  have h3 : Subsingleton ↥L := ⟨fun a b => Subtype.ext (Subsingleton.elim (a : X ⧸ gnC T) b)⟩
  have h4 : Subsingleton (↥L ⧸ Subgroup.center ↥L) := ⟨fun a b => by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a' b']⟩
  have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  exact hab (Subsingleton.elim a b)

@[expose] def GNYComponent (T T₁ T₂ : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Prop :=
  IsComponentOf L ⊤ ∧ ¬ L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∧
    ¬ L ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))

@[expose] def gnA (T Ti : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup (X ⧸ gnC T) :=
  gnImg T (Subgroup.normalizer (Ti : Set X)) ⊓ L

@[expose] def GNParabolic (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) →
    ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
      pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
        pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))

@[expose] def GNThree (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ L →
    ¬ pElementSubgroup 3 (gnA T T₁ L) ≤ (Subgroup.center ↥L).map L.subtype ∧
      ((IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) ∨
          (IsChevTwo (↥L ⧸ Subgroup.center ↥L) ∧
            ¬ ∃ m : ℕ, 5 ≤ m ∧
              Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin m)))) →
        ¬ pElementSubgroup 3 (gnA T T₂ L) ≤ (Subgroup.center ↥L).map L.subtype)

@[expose] def GNCentre (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ L →
    gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) → ∀ p : ℕ, p.Prime →
    p ∣ Nat.card (Subgroup.center ↥L) →
      1 < Open.pRank p (gnA T T₁ L) ∨ 1 < Open.pRank p (gnA T T₂ L)

@[expose] def GNAlt7 (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ →
    gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
    Nonempty (↥L ≃* alternatingGroup (Fin 7)) →
    1 < Open.pRank 3 (gnA T T₁ L) ∨ 1 < Open.pRank 3 (gnA T T₂ L)

@[expose] def GNAltBig (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ∀ n : ℕ, 8 < n →
    Nonempty (↥L ≃* alternatingGroup (Fin n)) →
      1 < Open.pRank 3 (gnA T T₁ L) ∨ 1 < Open.pRank 3 (gnA T T₂ L)

structure IsGNPair (T T₁ T₂ : Subgroup X) : Prop where
  ne_bot₁ : T₁ ≠ ⊥
  ne_bot₂ : T₂ ≠ ⊥
  le_center : T₁ ≤ Quasithin.omegaOneCenterOf T
  le₂ : T₂ ≤ T
  char₁ : (T₁.subgroupOf T).Characteristic
  char₂ : (T₂.subgroupOf T).Characteristic

end Setting

@[expose] def GlaubermanNilesInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∃ T₁ T₂ : Subgroup X, IsGNPair T T₁ T₂ ∧ GNParabolic T T₁ T₂ ∧ GNThree T T₁ T₂ ∧
      GNCentre T T₁ T₂ ∧ GNAlt7 T T₁ T₂ ∧ GNAltBig T T₁ T₂

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
