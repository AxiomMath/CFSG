module

public import CFSG.CGT.T75P.JCore
public import CFSG.CGT.Timmesfeld75.StdPair

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75
open scoped commutatorElement

@[expose] def NonBender (K : Type) [Group K] : Prop :=
  (∃ m s : ℕ, 3 ≤ m ∧ 1 ≤ s ∧ StatedClassicalModel K .PSL m 2 s) ∨
  (∃ k : ℕ, 6 ≤ k ∧ k ≤ 9 ∧ Nonempty (K ≃* alternatingGroup (Fin k))) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic K .M22 ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic K .M23 ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic K .M24

theorem card_map_of_inf_ker_eq_bot {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (A : Subgroup X) (h : A ⊓ φ.ker = ⊥) : Nat.card (A.map φ) = Nat.card A := by
  let f : A → A.map φ := fun a => ⟨φ a, Subgroup.mem_map_of_mem φ a.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : φ (a : X) = φ (b : X) := congrArg Subtype.val hab
      have hk : (a : X)⁻¹ * b ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h2 : (a : X)⁻¹ * b ∈ A ⊓ φ.ker := ⟨A.mul_mem (A.inv_mem a.2) b.2, hk⟩
      rw [h, Subgroup.mem_bot] at h2
      exact Subtype.ext (inv_mul_eq_one.1 h2)
    · rintro ⟨y, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem borel_of_bender {K : Type} [Group K] {Tb : Subgroup K} (hstd : StdPair K Tb)
    (hB : (∃ f : ℕ, StatedClassicalModel K .PSL 2 2 f) ∨
      (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel K .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel K .PSU 3 2 s)) :
    ∃ S : Sylow 2 K, Subgroup.normalizer (Tb : Set K) =
      Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  rcases hB with ⟨f, hf⟩ | ⟨s, hs, hs3, hG⟩ | ⟨s, hs, hG⟩
  · exact (hstd.of_psl2 hf).2.2.2
  · exact (hstd.of_sz hs hs3 hG).2.2.2
  · exact (hstd.of_psu3 hs hG).2.2.2

theorem mem_sylow_of_mem_normalizer {K : Type} [Group K] [Finite K] (S : Sylow 2 K) {x : K}
    (hx : x * x = 1) (hxN : x ∈ Subgroup.normalizer ((S : Subgroup K) : Set K)) :
    x ∈ (S : Subgroup K) := by
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨a, ha⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    refine ⟨1, Subtype.ext ?_⟩
    show (x ^ j) ^ 2 ^ 1 = 1
    have hg2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]
  have h1 := hP.inf_normalizer_sylow S
  have hmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (S : Set K) :=
    ⟨Subgroup.mem_zpowers x, hxN⟩
  rw [h1] at hmem
  exact hmem.2

variable {G : Type} [Group G]

theorem jMap_injOn_of_natural [Finite G] {T H Y : Subgroup G} (hTY : T ≤ Y)
    (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHC : H ⊓ Subgroup.centralizer (T : Set G) = T)
    (hTO : T.subgroupOf Y ⊓ CFSG.pCore 2 ↥Y = ⊥)
    (hker : T.subgroupOf Y ⊓ (jMap ↥Y).ker = T.subgroupOf Y ⊓ CFSG.pCore 2 ↥Y)
    {w : ↥Y} (hwH : (w : G) ∈ H) (hw : jMap ↥Y w = 1) : w = 1 := by
  have hwk : w ∈ (jMap ↥Y).ker := hw
  have hcomm : ∀ t ∈ T, (w : G) * t = t * (w : G) := by
    intro t ht
    have h1 := mem_ker_jMap.1 hwk ⟨t, hTY ht⟩
    have h2 : ⁅w, (⟨t, hTY ht⟩ : ↥Y)⁆ ∈ T.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      have hwt : (w : G) * t * (w : G)⁻¹ ∈ T := conj_mem_of_mem_normalizer (hHN hwH) ht
      have : (((⁅w, (⟨t, hTY ht⟩ : ↥Y)⁆ : ↥Y)) : G) = ((w : G) * t * (w : G)⁻¹) * t⁻¹ := by
        simp [commutatorElement_def]
      rw [this]
      exact T.mul_mem hwt (T.inv_mem ht)
    have h3 : ⁅w, (⟨t, hTY ht⟩ : ↥Y)⁆ ∈ T.subgroupOf Y ⊓ CFSG.pCore 2 ↥Y := ⟨h2, h1⟩
    rw [hTO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    have := congrArg Subtype.val h3
    simpa using this
  have hwC : (w : G) ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun t ht => (hcomm t ht).symm
  have hwT : (w : G) ∈ T := by
    have : (w : G) ∈ H ⊓ Subgroup.centralizer (T : Set G) := ⟨hwH, hwC⟩
    rwa [hHC] at this
  have hwTy : w ∈ T.subgroupOf Y := Subgroup.mem_subgroupOf.2 hwT
  have : w ∈ T.subgroupOf Y ⊓ (jMap ↥Y).ker := ⟨hwTy, hwk⟩
  rw [hker, hTO, Subgroup.mem_bot] at this
  exact this

theorem ident_gen [Finite G] {T H Y : Subgroup G} {m : ℕ} (hInd : SimpleCaseUpTo m)
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) (hWC : IsWC T) (hTH : T ≤ H) (hHY : H ≤ Y)
    (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHC : H ⊓ Subgroup.centralizer (T : Set G) = T)
    (hHgen : H ≤ Subgroup.closure {x | x ∈ H ∧ x * x = 1}) (hH2 : ¬ IsPGroup 2 H)
    (hcl : Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤)
    (hTO : T.subgroupOf Y ⊓ CFSG.pCore 2 ↥Y = ⊥) (h4 : 4 ≤ Nat.card T)
    (hlt : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) < m) :
    IsSimpleGroup (jQuot ↥Y) ∧ ListGroup (jQuot ↥Y) ∧
      StdPair (jQuot ↥Y) ((T.subgroupOf Y).map (jMap ↥Y)) ∧
      Nat.card ((T.subgroupOf Y).map (jMap ↥Y)) = Nat.card T ∧ NonBender (jQuot ↥Y) := by
  classical
  set O := CFSG.pCore 2 ↥Y with hO
  set Ty : Subgroup ↥Y := T.subgroupOf Y with hTy
  have hTY : T ≤ Y := hTH.trans hHY
  have hWCy : IsWC Ty := isWC_subgroupOf hWC Y hTY
  have hcardTy : Nat.card Ty = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
  have hkerO : (QuotientGroup.mk' O).ker = O := QuotientGroup.ker_mk' O
  have h4' : 4 ≤ Nat.card (Ty.map (QuotientGroup.mk' O)) := by
    rw [card_map_of_inf_ker_eq_bot _ Ty (by rw [hkerO]; exact hTO), hcardTy]
    exact h4
  obtain ⟨hsimple, hlist, hWCb, h4b, -, hker⟩ := jCore' hInd h215 hWCy hcl h4' hlt
  have hker' : Ty ⊓ (jMap ↥Y).ker = ⊥ := by rw [hker]; exact hTO
  have hcard : Nat.card (Ty.map (jMap ↥Y)) = Nat.card T := by
    rw [card_map_of_inf_ker_eq_bot _ Ty hker', hcardTy]
  have : IsSimpleGroup (jQuot ↥Y) := hsimple
  have hstd : StdPair (jQuot ↥Y) (Ty.map (jMap ↥Y)) := hL (jQuot ↥Y) hlist _ hWCb h4b
  have hnb : ¬ ((∃ f : ℕ, StatedClassicalModel (jQuot ↥Y) .PSL 2 2 f) ∨
      (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel (jQuot ↥Y) .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel (jQuot ↥Y) .PSU 3 2 s)) := by
    intro hB
    obtain ⟨S, hS⟩ := borel_of_bender hstd hB
    have hinvS : ∀ g ∈ Subgroup.closure {x | x ∈ H ∧ x * x = 1},
        ∃ hg : g ∈ Y, jMap ↥Y ⟨g, hg⟩ ∈ (S : Subgroup (jQuot ↥Y)) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        have hxY : x ∈ Y := hHY hx.1
        refine ⟨hxY, ?_⟩
        set u : jQuot ↥Y := jMap ↥Y ⟨x, hxY⟩ with hu
        have huu : u * u = 1 := by
          rw [hu, ← map_mul]
          have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : ↥Y) = 1 := Subtype.ext hx.2
          rw [this, map_one]
        have hconj : ∀ k : jQuot ↥Y, k ∈ Ty.map (jMap ↥Y) → u * k * u⁻¹ ∈ Ty.map (jMap ↥Y) := by
          intro k hk
          obtain ⟨t', ht', rfl⟩ := hk
          refine ⟨⟨x, hxY⟩ * t' * ⟨x, hxY⟩⁻¹, ?_, by rw [hu, map_mul, map_mul, map_inv]⟩
          have ht'' : t' ∈ T.subgroupOf Y := ht'
          show _ ∈ T.subgroupOf Y
          rw [Subgroup.mem_subgroupOf] at ht'' ⊢
          have := conj_mem_of_mem_normalizer (hHN hx.1) ht''
          simpa using this
        have huN : u ∈ Subgroup.normalizer ((Ty.map (jMap ↥Y) : Subgroup (jQuot ↥Y)) :
            Set (jQuot ↥Y)) := by
          rw [Subgroup.mem_normalizer_iff]
          intro k
          refine ⟨fun hk => hconj k hk, fun hk => ?_⟩
          have := hconj _ hk
          have e : u * (u * k * u⁻¹) * u⁻¹ = k := by
            calc u * (u * k * u⁻¹) * u⁻¹ = (u * u) * k * (u * u)⁻¹ := by group
              _ = k := by rw [huu]; group
          rwa [e] at this
        rw [hS] at huN
        exact mem_sylow_of_mem_normalizer S huu huN
      | one =>
        refine ⟨Y.one_mem, ?_⟩
        rw [show (⟨1, Y.one_mem⟩ : ↥Y) = 1 from rfl, map_one]
        exact (S : Subgroup (jQuot ↥Y)).one_mem
      | mul a b ha hb iha ihb =>
        obtain ⟨hay, ha'⟩ := iha
        obtain ⟨hby, hb'⟩ := ihb
        refine ⟨Y.mul_mem hay hby, ?_⟩
        have : jMap ↥Y ⟨a * b, Y.mul_mem hay hby⟩ =
            jMap ↥Y ⟨a, hay⟩ * jMap ↥Y ⟨b, hby⟩ := by
          rw [← map_mul]
          rfl
        rw [this]
        exact (S : Subgroup (jQuot ↥Y)).mul_mem ha' hb'
      | inv a ha iha =>
        obtain ⟨hay, ha'⟩ := iha
        refine ⟨Y.inv_mem hay, ?_⟩
        have : jMap ↥Y ⟨a⁻¹, Y.inv_mem hay⟩ = (jMap ↥Y ⟨a, hay⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact (S : Subgroup (jQuot ↥Y)).inv_mem ha'
    apply hH2
    intro h
    obtain ⟨hy, hS'⟩ := hinvS h.1 (hHgen h.2)
    obtain ⟨n, hn⟩ := (S.isPGroup' : IsPGroup 2 (S : Subgroup (jQuot ↥Y))) ⟨_, hS'⟩
    refine ⟨n, ?_⟩
    have h1 : jMap ↥Y (⟨(h : G), hy⟩ ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have h2 : (⟨(h : G), hy⟩ ^ 2 ^ n : ↥Y) = 1 :=
      jMap_injOn_of_natural hTY hHN hHC hTO hker (w := ⟨(h : G), hy⟩ ^ 2 ^ n)
        (by
          have : (((⟨(h : G), hy⟩ ^ 2 ^ n : ↥Y)) : G) = (h : G) ^ 2 ^ n := by simp
          rw [this]
          exact H.pow_mem h.2 _) h1
    apply Subtype.ext
    have := congrArg Subtype.val h2
    simpa using this
  refine ⟨hsimple, hlist, hstd, hcard, ?_⟩
  rcases hlist with ⟨mm, s, hm2, hs1, hmod⟩ | ⟨s, hs2, hmod⟩ | ⟨s, hso, hs3, hmod⟩ |
      ⟨k, hk6, hk9, hk⟩ | h22 | h23 | h24
  · by_cases hm : mm = 2
    · subst hm
      exact absurd (Or.inl ⟨s, hmod⟩) hnb
    · exact Or.inl ⟨mm, s, by omega, hs1, hmod⟩
  · exact absurd (Or.inr (Or.inr ⟨s, hs2, hmod⟩)) hnb
  · exact absurd (Or.inr (Or.inl ⟨s, hso, hs3, hmod⟩)) hnb
  · exact Or.inr (Or.inl ⟨k, hk6, hk9, hk⟩)
  · exact Or.inr (Or.inr (Or.inl h22))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h23)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h24)))

end CFSG.CGT.T75P
