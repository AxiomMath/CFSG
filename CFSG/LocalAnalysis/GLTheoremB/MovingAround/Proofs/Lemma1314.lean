module

public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Lemma1314

@[expose] def fixSub {K : Type} [Group K] (x : MulAut K) : Subgroup K where
  carrier := {k | x k = k}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

@[expose] def PumpupVia (p : ℕ) (J : Type) [Group J] (K : Type) [Group K] [Finite K]
    (x : MulAut K) : Prop :=
  orderOf x = p ∧ ∃ J1 : Subgroup K, GLAPComponent p (fixSub x) J1 ∧ Nonempty (barOf p J1 ≃* J)

@[expose] def GammaPrimeOf {Y : Type} [Group Y] [Finite Y] (p : ℕ) (B : Subgroup Y) (r : ℕ)
    (X : Subgroup Y) : Subgroup Y :=
  ⨆ (A : Subgroup Y) (_ : A ≤ B ∧ r ≤ CFSG.Open.pRank p A), Subgroup.centralizer (A : Set Y) ⊓ X

@[expose] def IsGClass {Y : Type} [Group Y] [Finite Y] (p : ℕ) (B K : Subgroup Y) (r : ℕ) : Prop :=
  (⨆ g ∈ B, GLBConj g K) = GammaPrimeOf p B r (⨆ g ∈ B, GLBConj g K)

@[expose] def IsGMinusOne {Y : Type} [Group Y] [Finite Y] (p : ℕ) (B K : Subgroup Y) : Prop :=
  IsGClass p B K (CFSG.Open.pRank p B - 1)

@[expose] def IsTitsGroup (X : Type) [Group X] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex, idx.1 = TauCeti.LieTypeIndex.tits ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)

@[expose] def IsSz32Group (X : Type) [Group X] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex, idx.1 = TauCeti.LieTypeIndex.suzuki 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)

@[expose] def IsReeF4_32Group (X : Type) [Group X] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex, idx.1 = TauCeti.LieTypeIndex.reeF4 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)

@[expose] def I2310Exc5 {Y : Type} [Group Y] (K : Subgroup Y) : Prop :=
  IsTitsGroup (↥K ⧸ Subgroup.center ↥K) ∨ IsReeF4_32Group (↥K ⧸ Subgroup.center ↥K) ∨
    IsSz32Group (↥K ⧸ Subgroup.center ↥K)

@[expose] def Input14_15 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K],
    CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore p K = ⊥ →
    (∃ x : MulAut K, PumpupVia p ↥(alternatingGroup (Fin (p + 2))) K x) →
      (∃ k : ℕ, 2 ≤ k ∧ IsAltType (k * p + 2) K) ∨ (p = 5 ∧ IsSporType .Fi23 K)

@[expose] def Input23_10 : Prop :=
  ∀ (p q : ℕ), p.Prime → 5 ≤ p → q.Prime → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], GLAPPrimeCore p Y = ⊥ →
      ∀ (K B : Subgroup Y), IsComponentOf K ⊤ → IsElemAbelian p B → Nat.card B ≤ p ^ 3 →
        IsLieChar (· = q) ↥K → (p = 5 → ¬ I2310Exc5 K) → IsGMinusOne p B K

@[expose] def Input23_24Fi23 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], GLAPPrimeCore 5 Y = ⊥ →
    ∀ (K B : Subgroup Y), IsComponentOf K ⊤ → IsElemAbelian 5 B →
      IsSporType .Fi23 ↥K → IsGMinusOne 5 B K

abbrev L0bOf (p : ℕ) {G : Type} [Group G] (L0 : Subgroup G) (b : G) : Subgroup G :=
  GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))

abbrev LOf (p : ℕ) {G : Type} [Group G] (L0 : Subgroup G) (d b : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G)), GLBConj g (L0bOf p L0 b)

@[expose] def PumpupBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1),
    ∃ x : MulAut (barOf p (LOf p L0 d b)), PumpupVia p (barOf p (L0bOf p L0 b)) (barOf p (LOf p L0 d b)) x

@[expose] def KHatBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1),
    CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf p (LOf p L0 d b))

@[expose] def ExcBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1),
    p = 5 →
    (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p (L0bOf p L0 b)) ∧
      HasFixedPointFreeOrder ε n p) →
    (IsLieChar (· = 2) (barOf p (LOf p L0 d b)) ∨ IsLieChar (· = 3) (barOf p (LOf p L0 d b))) →
      ¬ I2310Exc5 (barX p (Subgroup.centralizer ({d} : Set G)) (LOf p L0 d b))

@[expose] def ConnBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D), 4 ≤ CFSG.Open.pRank p A →
    IsKConnectedIn p 3 ⊤ A B

section Transport

theorem isAltType_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsAltType n Y) : IsAltType n X :=
  h.map fun f => e.trans f

theorem isSporType_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (name : TauCeti.SporadicName) (h : IsSporType name Y) : IsSporType name X :=
  h.map fun f => e.trans f

theorem isOmegaTwo_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (ε : Bool) (n : ℕ)
    (h : IsOmegaTwo ε n Y) : IsOmegaTwo ε n X := by
  cases ε with
  | true => exact h.map fun f => e.trans f
  | false => exact h.map fun f => e.trans f

theorem isLieChar_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (P : ℕ → Prop)
    (h : IsLieChar P Y) : IsLieChar P X := by
  obtain ⟨idx, ⟨f⟩, hP⟩ := h
  exact ⟨idx, ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e
    (Subgroup.map_center_eq e)).trans f⟩, hP⟩

theorem isComponentOf_barX_of_glaPComponent {G : Type} [Group G] [Finite G] {p : ℕ}
    {C L : Subgroup G} (h : GLAPComponent p C L) :
    IsComponentOf (barX p C L) ⊤ := by
  obtain ⟨-, -, hc, -⟩ := h
  exact hc

theorem pumpupVia_of_equiv {p : ℕ} {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    {K : Type} [Group K] [Finite K] {x : MulAut K} (h : PumpupVia p J K x) :
    PumpupVia p J' K x := by
  obtain ⟨hx, J1, hJ1, ⟨f⟩⟩ := h
  exact ⟨hx, J1, hJ1, ⟨f.trans e⟩⟩

theorem type_of_iso {G : Type} [Group G] {p : ℕ} {L0b LI : Subgroup G}
    (eI : barOf p L0b ≃* barOf p LI)
    (htype : IsAltType (p + 2) (barOf p LI) ∨
      ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p LI) ∧
        HasFixedPointFreeOrder ε n p) :
    IsAltType (p + 2) (barOf p L0b) ∨
      ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p L0b) ∧
        HasFixedPointFreeOrder ε n p := by
  rcases htype with h | ⟨ε, n, hn, hO, hF⟩
  · exact Or.inl (isAltType_of_equiv eI h)
  · exact Or.inr ⟨ε, n, hn, isOmegaTwo_of_equiv eI ε (n + 1) hO, hF⟩

end Transport

section PiExclusion

theorem openQuasi_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hX : CFSG.Open.IsQuasisimple X) : CFSG.Open.IsQuasisimple Y := by
  obtain ⟨hc, hs⟩ := hX
  have hcen : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  refine ⟨?_, (MulEquiv.isSimpleGroup_congr (QuotientGroup.congr _ _ e hcen)).mp hs⟩
  rw [_root_.commutator_def] at hc ⊢
  rw [← Subgroup.map_top_of_surjective (e : X →* Y) e.surjective, ← Subgroup.map_commutator, hc]

theorem openQuasi_alt {n : ℕ} (hn : 5 ≤ n) : CFSG.Open.IsQuasisimple (alternatingGroup (Fin n)) := by
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hcard4 : 4 ≤ Nat.card (Fin n) := by omega
  have hc : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot hcard4
  have e : (alternatingGroup (Fin n)) ⧸ Subgroup.center (alternatingGroup (Fin n)) ≃*
      alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact ⟨commutator_alternatingGroup_eq_top hcard,
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup hcard)⟩

theorem isPiGroup_of_alt_equiv {p k : ℕ} {X : Type} [Group X] (hcore : GLAPPrimeCore p X = ⊥)
    (hn : 5 ≤ k * p + 2) (e : X ≃* alternatingGroup (Fin (k * p + 2))) : IsPiGroup p X := by
  have hcard4 : 4 ≤ Nat.card (Fin (k * p + 2)) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hc : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : e x ∈ (Subgroup.center X).map
        (e : X →* alternatingGroup (Fin (k * p + 2))) := ⟨x, hx, rfl⟩
    rw [Subgroup.map_center_eq e, alternatingGroup.center_eq_bot hcard4] at hmem
    have h1 : e x = e 1 := by
      rw [map_one]
      exact Subgroup.mem_bot.1 hmem
    rw [Subgroup.mem_bot]
    exact e.injective h1
  have eq : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin (k * p + 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)
  unfold IsPiGroup
  exact ⟨openQuasi_of_equiv e.symm (openQuasi_alt hn), hcore, Or.inl ⟨k, ⟨eq⟩⟩⟩

theorem le_piOf_of_alt {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {d : G} {L : Subgroup G} (hL : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) L)
    {k : ℕ} (hk : 1 ≤ k) (halt : IsAltType (k * p + 2) (barOf p L)) :
    L ≤ piOf p d := by
  obtain ⟨e⟩ := halt
  have hn : 5 ≤ k * p + 2 := by nlinarith
  have hcore : GLAPPrimeCore p (barOf p L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hPi : IsPiGroup p (↥L ⧸ GLAPPrimeCore p ↥L) := isPiGroup_of_alt_equiv hcore hn e
  unfold piOf piLayer
  exact le_iSup₂ (f := fun (L' : Subgroup G) (_ : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) L' ∧
    IsPiGroup p (↥L' ⧸ GLAPPrimeCore p ↥L')) => L') L ⟨hL, hPi⟩

end PiExclusion

section Containment

theorem le_glbCore_of_isGClass {Y : Type} [Group Y] [Finite Y] {p r : ℕ} {B K : Subgroup Y}
    (h : IsGClass p B K r) : K ≤ GLBCore p r B := by
  have hK : K ≤ ⨆ g ∈ B, GLBConj g K := by
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun g (_ : g ∈ B) => GLBConj g K) 1 B.one_mem)
    ext x
    simp [GLBConj, Subgroup.mem_map]
  rw [h] at hK
  refine hK.trans ?_
  unfold GammaPrimeOf
  refine iSup₂_le fun Q hQ => ?_
  unfold GLBCore
  exact inf_le_left.trans ((Subgroup.centralizer_le_normalizer (Q : Set Y)).trans
    (le_sSup ⟨Q, hQ.1, hQ.2, rfl⟩))

theorem le_of_gMinusOne {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C F L M : Subgroup G} (hLC : L ≤ C) (hFC : F ≤ C) (hF : IsPGroup p ↥F)
    (hnorm : ∀ E : Subgroup G, E ≤ F → 2 ≤ CFSG.Open.pRank p E → Subgroup.normalizer (E : Set G) ≤ M)
    (hcore : GLAPPrimeCoreOf p C ≤ M) (hG : IsGMinusOne p (barX p C F) (barX p C L))
    (hk : 3 ≤ CFSG.Open.pRank p F) : L ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : CFSG.Open.pRank p (barX p C F) = CFSG.Open.pRank p F :=
    rank_barX_of_isPGroup hp hF hFC
  have h1 : barX p C L ≤ GLBCore p (CFSG.Open.pRank p F - 1) (barX p C F) := by
    have := le_glbCore_of_isGClass hG
    rwa [hrank] at this
  exact le_of_barX_le_glbCore hp (CFSG.Open.pRank p F - 1) hF hFC hLC
    (fun E hE hEr => hnorm E hE (by omega)) hcore h1

end Containment

end Lemma1314

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
