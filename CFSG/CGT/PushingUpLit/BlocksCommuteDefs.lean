module

public import CFSG.CGT.PushingUpLit.Defs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

@[expose] def IsBlockOf {G : Type} [Group G] [Finite G] (X : Subgroup G) : Prop :=
  X.IsSubnormal ∧ IsShortGroup ↥X

section Transport

variable {L L' : Type} [Group L] [Group L']

theorem isPGroup_two_quotient_iff (N : Subgroup L) [N.Normal] :
    IsPGroup 2 (L ⧸ N) ↔ ∀ g : L, ∃ k : ℕ, g ^ 2 ^ k ∈ N := by
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (g : L ⧸ N)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h g
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk

theorem oResidualTwo_eq_top_iff :
    oResidualTwo L = ⊤ ↔ ∀ N : Subgroup L, N.Normal → (∀ g : L, ∃ k : ℕ, g ^ 2 ^ k ∈ N) →
      N = ⊤ := by
  constructor
  · intro h N hN hpow
    have := hN
    have hle : oResidualTwo L ≤ N :=
      sInf_le ⟨hN, (isPGroup_two_quotient_iff N).2 hpow⟩
    exact eq_top_iff.2 (h ▸ hle)
  · intro h
    refine eq_top_iff.2 (le_sInf fun N hN => ?_)
    obtain ⟨hNn, hNp⟩ := hN
    have := hNn
    exact le_of_eq (h N hNn ((isPGroup_two_quotient_iff N).1 hNp)).symm

theorem shortU_le_center_iff :
    shortU L ≤ (Subgroup.center (pCore 2 L)).map (pCore 2 L).subtype ↔
      ∀ u ∈ shortU L, u ∈ pCore 2 L ∧ ∀ r ∈ pCore 2 L, u * r = r * u := by
  constructor
  · intro h u hu
    obtain ⟨c, hc, rfl⟩ := h hu
    refine ⟨c.2, fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨r, hr⟩
    exact (congrArg Subtype.val this).symm
  · intro h u hu
    obtain ⟨h1, h2⟩ := h u hu
    refine ⟨⟨u, h1⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (h2 g g.2).symm

theorem isShortGroup_of_mulEquiv [Finite L] [Finite L'] (e : L ≃* L') (h : IsShortGroup L) :
    IsShortGroup L' := by
  have hp : (pCore 2 L).map (e : L →* L') = pCore 2 L' := pCore_map_iso 2 e
  have hU : (shortU L).map (e : L →* L') = shortU L' := by
    unfold shortU
    rw [Subgroup.map_commutator, hp, Subgroup.map_top_of_surjective _ e.surjective]
  have hC : (shortC L).map (e : L →* L') = shortC L' := by
    unfold shortC
    rw [Subgroup.map_inf _ _ _ e.injective, hU, Subgroup.map_center_eq e]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (isCharacteristicP_iff_generalizedFitting_eq_pCore L' 2).mp ?_
    have hc : IsCharacteristicP 2 L :=
      (isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mpr h.fitting_eq
    intro c' hc'
    have hmem : e.symm c' ∈ pCore 2 L := by
      refine hc ?_
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : e r ∈ pCore 2 L' := by
        rw [← hp]
        exact Subgroup.mem_map_of_mem _ hr
      have h1 := (Subgroup.mem_centralizer_iff.mp hc') (e r) hr'
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact h1
    rw [← e.apply_symm_apply c', ← hp]
    exact Subgroup.mem_map_of_mem _ hmem
  · refine (oResidualTwo_eq_top_iff).2 fun N' hN' hpow => ?_
    have hN : (N'.comap (e : L →* L')).Normal := hN'.comap _
    have hpow' : ∀ g : L, ∃ k : ℕ, g ^ 2 ^ k ∈ N'.comap (e : L →* L') := by
      intro g
      obtain ⟨k, hk⟩ := hpow (e g)
      exact ⟨k, by simpa using hk⟩
    have htop := (oResidualTwo_eq_top_iff).1 h.residual_eq _ hN hpow'
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    have : e.symm x ∈ N'.comap (e : L →* L') := by rw [htop]; trivial
    simpa using this
  · have eq' : (L ⧸ pCore 2 L) ≃* (L' ⧸ pCore 2 L') := QuotientGroup.congr _ _ e hp
    rcases h.quotient_type with hq | hq
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv eq' hq)
    · exact Or.inr (by rwa [← Nat.card_congr eq'.toEquiv])
  · refine shortU_le_center_iff.2 fun u' hu' => ?_
    rw [← hU] at hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    obtain ⟨h1, h2⟩ := shortU_le_center_iff.1 h.U_le_center u hu
    refine ⟨?_, fun r' hr' => ?_⟩
    · rw [← hp]
      exact Subgroup.mem_map_of_mem _ h1
    · rw [← hp] at hr'
      obtain ⟨r, hr, rfl⟩ := hr'
      simp only [MonoidHom.coe_ofClass]
      rw [← map_mul, ← map_mul, h2 r hr]
  · rw [← hC, ← hU]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).2 h.nonzero
  · intro N' hN' hNU hCN
    have hN : (N'.comap (e : L →* L')).Normal := hN'.comap _
    have hNU' : N'.comap (e : L →* L') ≤ shortU L := by
      intro x hx
      have : e x ∈ shortU L' := hNU hx
      rw [← hU] at this
      obtain ⟨u, hu, hux⟩ := this
      have : u = x := e.injective hux
      rwa [← this]
    have hCN' : shortC L ≤ N'.comap (e : L →* L') := by
      intro x hx
      have : e x ∈ shortC L' := by
        rw [← hC]
        exact Subgroup.mem_map_of_mem _ hx
      exact hCN this
    have hsurj := Subgroup.map_comap_eq_self_of_surjective (f := (e : L →* L'))
      e.surjective N'
    rcases h.irreducible _ hN hNU' hCN' with h1 | h1
    · left
      rw [← hsurj, h1, hC]
    · right
      rw [← hsurj, h1, hU]

noncomputable def quotTopEquiv (e : L ≃* L') [Finite L] [Finite L'] :
    (L ⧸ pCore 2 L) ≃* (L' ⧸ pCore 2 L') :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

end Transport

section Ambient

variable {G : Type} [Group G]

@[expose] def blockU (X : Subgroup G) : Subgroup G := ⁅oTwoIn X, X⁆

@[expose] def blockZ (X : Subgroup G) : Subgroup G :=
  blockU X ⊓ Subgroup.centralizer (X : Set G)

theorem oTwoIn_eq_map (X : Subgroup G) : oTwoIn X = (pCore 2 ↥X).map X.subtype := rfl

theorem oTwoIn_le (X : Subgroup G) : oTwoIn X ≤ X := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

theorem isPGroup_oTwoIn (X : Subgroup G) : IsPGroup 2 (oTwoIn X) :=
  IsPGroup.map pCore_isPGroup X.subtype

theorem normalizer_le_normalizer_oTwoIn (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoIn X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_oTwoIn hg hc, fun hc => ?_⟩
  have := conj_mem_oTwoIn (inv_mem hg) hc
  simpa [mul_assoc] using this

theorem blockU_le_oTwoIn (X : Subgroup G) : blockU X ≤ oTwoIn X := by
  refine Subgroup.commutator_le.2 fun r hr x hx => ?_
  have h1 : x * r⁻¹ * x⁻¹ ∈ oTwoIn X :=
    conj_mem_oTwoIn (Subgroup.le_normalizer hx) (inv_mem hr)
  have : ⁅r, x⁆ = r * (x * r⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact mul_mem hr h1

theorem blockU_le (X : Subgroup G) : blockU X ≤ X := (blockU_le_oTwoIn X).trans (oTwoIn_le X)

theorem blockZ_le_blockU (X : Subgroup G) : blockZ X ≤ blockU X := inf_le_left

theorem conj_mem_blockU {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {u : G} (hu : u ∈ blockU X) : g * u * g⁻¹ ∈ blockU X := by
  have h1 : (oTwoIn X).map (MulAut.conj g).toMonoidHom ≤ oTwoIn X := by
    rintro _ ⟨c, hc, rfl⟩
    exact conj_mem_oTwoIn hg hc
  have h2 : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨c, hc, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg c).1 hc
  have := Subgroup.commutator_mono h1 h2
  rw [← Subgroup.map_commutator] at this
  exact this ⟨u, hu, rfl⟩

theorem le_normalizer_blockU (X : Subgroup G) :
    X ≤ Subgroup.normalizer (blockU X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_blockU (Subgroup.le_normalizer hg) hu, fun hu => ?_⟩
  have := conj_mem_blockU (Subgroup.le_normalizer (inv_mem hg)) hu
  simpa [mul_assoc] using this

theorem conj_mem_blockZ {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {z : G} (hz : z ∈ blockZ X) : g * z * g⁻¹ ∈ blockZ X := by
  refine Subgroup.mem_inf.2 ⟨conj_mem_blockU hg hz.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hc' : g⁻¹ * c * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) c).1 hc
    simpa using this
  have h1 := (Subgroup.mem_centralizer_iff.1 hz.2) _ hc'
  calc c * (g * z * g⁻¹) = g * ((g⁻¹ * c * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * c * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * c := by group

theorem map_shortU_subtype (X : Subgroup G) : (shortU ↥X).map X.subtype = blockU X := by
  unfold shortU blockU
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rfl

theorem map_center_subtype (X : Subgroup G) :
    (Subgroup.center ↥X).map X.subtype = X ⊓ Subgroup.centralizer (X : Set G) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
    exact congrArg Subtype.val this
  · intro hg
    obtain ⟨hgX, hg⟩ := Subgroup.mem_inf.1 hg
    refine ⟨⟨g, hgX⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hg y y.2)

theorem map_shortC_subtype (X : Subgroup G) : (shortC ↥X).map X.subtype = blockZ X := by
  unfold shortC blockZ
  rw [Subgroup.map_inf _ _ _ X.subtype_injective, map_shortU_subtype, map_center_subtype,
    ← inf_assoc, inf_eq_left.2 (blockU_le X)]

theorem oTwoIn_map_equiv {G' : Type} [Group G'] (f : G ≃* G') (X : Subgroup G) :
    oTwoIn (X.map (f : G →* G')) = (oTwoIn X).map (f : G →* G') := by
  have hp := pCore_map_iso 2 (f.subgroupMap X)
  rw [oTwoIn_eq_map, oTwoIn_eq_map, ← hp, Subgroup.map_map, Subgroup.map_map]
  rfl

variable [Finite G]

theorem noTwoQuot_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) (N : Subgroup G)
    (hN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hpow : ∀ g ∈ X, ∃ k : ℕ, g ^ 2 ^ k ∈ N) : X ≤ N := by
  have hnorm : (N.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN g g.2 n hn⟩
  have hpow' : ∀ g : ↥X, ∃ k : ℕ, g ^ 2 ^ k ∈ N.subgroupOf X := by
    intro g
    obtain ⟨k, hk⟩ := hpow g g.2
    exact ⟨k, by simpa [Subgroup.mem_subgroupOf] using hk⟩
  have htop := (oResidualTwo_eq_top_iff).1 hX.residual_eq _ hnorm hpow'
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ N.subgroupOf X := by rw [htop]; trivial
  exact this

theorem blockU_comm_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) :
    ∀ u ∈ blockU X, ∀ r ∈ oTwoIn X, u * r = r * u := by
  intro u hu r hr
  rw [← map_shortU_subtype] at hu
  obtain ⟨u0, hu0, rfl⟩ := hu
  obtain ⟨r0, hr0, rfl⟩ := hr
  obtain ⟨-, h2⟩ := shortU_le_center_iff.1 hX.U_le_center u0 hu0
  exact congrArg Subtype.val (h2 r0 hr0)

theorem blockZ_lt_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) : blockZ X < blockU X := by
  rw [← map_shortC_subtype, ← map_shortU_subtype]
  exact (Subgroup.map_lt_map_iff_of_injective X.subtype_injective).2 hX.nonzero

theorem blockU_ne_bot_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) : blockU X ≠ ⊥ :=
  fun h => (not_lt_of_ge (h ▸ bot_le : blockU X ≤ blockZ X)) (blockZ_lt_of_short hX)

theorem blockU_irred_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) (N : Subgroup G)
    (hZN : blockZ X ≤ N) (hNU : N ≤ blockU X) (hNn : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    N = blockZ X ∨ N = blockU X := by
  have hnorm : (N.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hNn g g.2 n hn⟩
  have h1 : N.subgroupOf X ≤ shortU ↥X := by
    intro x hx
    have : (x : G) ∈ blockU X := hNU hx
    rw [← map_shortU_subtype] at this
    obtain ⟨s, hs, hsx⟩ := this
    have : s = x := Subtype.ext hsx
    rwa [← this]
  have h2 : shortC ↥X ≤ N.subgroupOf X := by
    intro x hx
    have : (x : G) ∈ blockZ X := by
      rw [← map_shortC_subtype]
      exact Subgroup.mem_map_of_mem _ hx
    exact hZN this
  have hNX : N ≤ X := hNU.trans (blockU_le X)
  rcases hX.irreducible _ hnorm h1 h2 with h3 | h3
  · left
    rw [← map_shortC_subtype, ← h3, Subgroup.map_subgroupOf_eq_of_le hNX]
  · right
    rw [← map_shortU_subtype, ← h3, Subgroup.map_subgroupOf_eq_of_le hNX]

theorem IsBlockOf.map_conj {X : Subgroup G} (hX : IsBlockOf X) (g : G) :
    IsBlockOf (X.map (MulAut.conj g).toMonoidHom) :=
  ⟨hX.1.map (MulAut.conj g).surjective,
    isShortGroup_of_mulEquiv ((MulAut.conj g).subgroupMap X) hX.2⟩

end Ambient

end CFSG.CGT.PushingUpLit
