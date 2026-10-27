module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecCorr

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

section General

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPerfect_sup {A C : Subgroup G} [Group.IsPerfect A] [Group.IsPerfect C] :
    Group.IsPerfect ↥(A ⊔ C) := by
  have hA : A ≤ ⁅A ⊔ C, A ⊔ C⁆ :=
    (Subgroup.commutator_eq_self (H := A)).symm.le.trans (commutator_mono le_sup_left le_sup_left)
  have hC : C ≤ ⁅A ⊔ C, A ⊔ C⁆ :=
    (Subgroup.commutator_eq_self (H := C)).symm.le.trans
      (commutator_mono le_sup_right le_sup_right)
  exact Subgroup.isPerfect_iff.mpr (le_antisymm (commutator_le_self _) (sup_le hA hC))

omit [Finite G] in
theorem conj_mem_oddCoreIn {V : Subgroup G} {o v : G} (ho : o ∈ oddCoreIn V) (hv : v ∈ V) :
    v⁻¹ * o * v ∈ oddCoreIn V := by
  obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
  have h1 := (inferInstance : (pPrimeCore 2 ↥V).Normal).conj_mem o' ho' ⟨v, hv⟩⁻¹
  refine mem_map.mpr ⟨_, h1, ?_⟩
  simp only [coe_subtype, coe_mul, coe_inv, inv_inv]

omit [Finite G] in
theorem mem_coreActionKernel_sup {K₁ K₂ : Subgroup G}
    (hO₁ : oddCoreIn K₁ ≤ oddCoreIn (K₁ ⊔ K₂)) (hO₂ : oddCoreIn K₂ ≤ oddCoreIn (K₁ ⊔ K₂))
    {s : G} (hs₁ : s ∈ coreActionKernel K₁) (hs₂ : s ∈ coreActionKernel K₂) :
    s ∈ coreActionKernel (K₁ ⊔ K₂) := by
  have hsN := mem_normalizer_sup (mem_coreActionKernel.mp hs₁).1 (mem_coreActionKernel.mp hs₂).1
  refine mem_coreActionKernel.mpr ⟨hsN, fun v hv => ?_⟩
  rw [sup_eq_closure] at hv
  refine closure_induction (p := fun v _ => v⁻¹ * s⁻¹ * v * s ∈ oddCoreIn (K₁ ⊔ K₂))
    ?_ ?_ ?_ ?_ hv
  · rintro x (hx | hx)
    · exact hO₁ ((mem_coreActionKernel.mp hs₁).2 x hx)
    · exact hO₂ ((mem_coreActionKernel.mp hs₂).2 x hx)
  · simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
    exact one_mem _
  · intro x z hx hz hpx hpz
    have hz' : z ∈ K₁ ⊔ K₂ := by rw [sup_eq_closure]; exact hz
    rw [show (x * z)⁻¹ * s⁻¹ * (x * z) * s = z⁻¹ * (x⁻¹ * s⁻¹ * x * s) * z *
      (z⁻¹ * s⁻¹ * z * s) by group]
    exact mul_mem (conj_mem_oddCoreIn hpx hz') hpz
  · intro x hx hpx
    have hx' : x ∈ K₁ ⊔ K₂ := by rw [sup_eq_closure]; exact hx
    rw [show x⁻¹⁻¹ * s⁻¹ * x⁻¹ * s = x⁻¹⁻¹ * (x⁻¹ * s⁻¹ * x * s)⁻¹ * x⁻¹ by group]
    exact conj_mem_oddCoreIn (inv_mem hpx) (inv_mem hx')

theorem pComponent_sup_facts {C K₁ K₂ : Subgroup G} (h1 : K₁ ≤ C) (h2 : K₂ ≤ C)
    (hc1 : IsPComponent 2 (K₁.subgroupOf C)) (hc2 : IsPComponent 2 (K₂.subgroupOf C)) :
    K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) ∧ K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) ∧
      oddCoreIn K₁ ≤ oddCoreIn (K₁ ⊔ K₂) ∧ oddCoreIn K₂ ≤ oddCoreIn (K₁ ⊔ K₂) := by
  have hN12 : K₂ ≤ normalizer (K₁ : Set G) ∧ K₁ ≤ normalizer (K₂ : Set G) := by
    by_cases heq : K₁ = K₂
    · subst heq
      exact ⟨le_normalizer, le_normalizer⟩
    · exact ⟨fun k hk => (mem_coreActionKernel.mp (le_coreActionKernel_of_ne h1 h2 hc1 hc2
        heq hk)).1, fun k hk => (mem_coreActionKernel.mp (le_coreActionKernel_of_ne h2 h1 hc2 hc1
        (Ne.symm heq) hk)).1⟩
  have hn1 : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) := sup_le le_normalizer hN12.1
  have hn2 : K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) := sup_le hN12.2 le_normalizer
  exact ⟨hn1, hn2, oddCoreIn_le_of_le_normalizer le_sup_left hn1,
    oddCoreIn_le_of_le_normalizer le_sup_right hn2⟩

end General

end B5a

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem K_le_V : h.K ≤ h.V :=
  le_sup_left.trans h.layer_eq_K.le

theorem conjugate_K_le_V : conjugate h.K h.a ≤ h.V :=
  le_sup_right.trans h.layer_eq_K.le

theorem V_le_W : h.V ≤ h.W := map_subtype_le _

theorem isPerfect_V : Group.IsPerfect h.V := by
  have : Group.IsPerfect h.K :=
    B5a.isPerfect_of_isPComponent_subgroupOf h.isPComponent_K.1 h.isPComponent_K.2
  have hKa := OddQuot.isPComponent_conjugate_subgroupOf h.a_mem_normalizer h.isPComponent_K.1
    h.isPComponent_K.2
  have : Group.IsPerfect (conjugate h.K h.a) :=
    B5a.isPerfect_of_isPComponent_subgroupOf hKa.1 hKa.2
  have h1 := B5a.isPerfect_sup (A := h.K) (C := conjugate h.K h.a)
  rw [h.layer_eq_K] at h1
  exact h1

theorem isSolvable_kernel_V : Group.IsSolvable ↥(h.W ⊓ coreActionKernel h.V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := h.W ⊓ coreActionKernel h.V with hC
  obtain ⟨R, hR⟩ := h.B_sylow_kernel
  have hBC : h.B ≤ C := h.B_le_kernel
  have hn : (h.B.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBC).mpr fun c hc => (mem_inf.mp hc).1
  have h1 : IsPGroup 2 (h.B.subgroupOf C) := (B5a.isPGroup_B h).comap_subtype
  have : Group.IsNilpotent (h.B.subgroupOf C) := h1.isNilpotent
  have h2 : ¬ 2 ∣ (h.B.subgroupOf C).index := by
    rw [← hR]
    exact R.not_dvd_index
  have h3 : Odd (Nat.card (↥C ⧸ h.B.subgroupOf C)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have : Group.IsSolvable (↥C ⧸ h.B.subgroupOf C) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ h3
  exact Group.isSolvable_of_subgroup_quotient (h.B.subgroupOf C)

theorem secFixedLayer_B (hc : h.SecCond y) :
    GSLit.fixedLayer (h.secImage y (h.secJ0 y)) (h.secImage y h.B) =
      h.secImage y (GSLit.fixedLayer h.J h.B) := by
  rw [← secImage_fixedLayer (h.secJ0_le_G0 y) ((h.secJ0_le y).trans inf_le_right)
    (h.secB0_le_B y) hc.B_le_G0, fixedLayer_secJ0 (h.secB0_le_B y) hc.B_le_G0 h.B_le]

theorem secImage_W_inf (Y : Subgroup X) : h.secImage y (Y ⊓ h.secG0 y) = h.secImage y Y := by
  show ((Y ⊓ h.secG0 y).subgroupOf (h.secG0 y)).map (h.secMk y) =
    (Y.subgroupOf (h.secG0 y)).map (h.secMk y)
  rw [inf_subgroupOf_right]

theorem isPComponent_secK (hc : h.SecCond y) {L : Subgroup X}
    (hL : L = h.K ∨ L = conjugate h.K h.a) :
    h.secImage y L ≤ normalizer (h.secImage y h.B : Set (h.secBar y)) ∧
      IsPComponent 2 ((h.secImage y L).subgroupOf
        (normalizer (h.secImage y h.B : Set (h.secBar y)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLW, hLc⟩ : L ≤ h.W ∧ IsPComponent 2 (L.subgroupOf h.W) := by
    rcases hL with rfl | rfl
    · exact h.isPComponent_K
    · exact OddQuot.isPComponent_conjugate_subgroupOf h.a_mem_normalizer h.isPComponent_K.1
        h.isPComponent_K.2
  have hLV : L ≤ h.V := by
    rcases hL with rfl | rfl
    · exact K_le_V
    · exact conjugate_K_le_V
  have hLG : L ≤ h.secG0 y := hLV.trans (h.V_le_G0 y)
  have hLB : L ≤ centralizer (h.secB0 y : Set X) := hLV.trans (h.V_le_centralizer_secB0 y)
  have h1 : IsPComponent 2 (L.subgroupOf (h.W ⊓ h.secG0 y)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLW hLG) inf_le_left hLc
  have h2 := secImage_isPComponent (le_inf hLW hLG) inf_le_right hLB h1
  rw [secImage_W_inf] at h2
  rw [hc.normalizer_secB]
  exact ⟨secImage_mono hLW, h2⟩

theorem secImage_V (hc : h.SecCond y) :
    h.secImage y h.V = h.secImage y h.K ⊔ conjugate (h.secImage y h.K) hc.secA := by
  rw [← secImage_conjugate h.K hc.a_mem_G0, ← secImage_sup (K_le_V.trans (h.V_le_G0 y))
    (conjugate_K_le_V.trans (h.V_le_G0 y)), h.layer_eq_K]

theorem layerIn_secW (hc : h.SecCond y) :
    layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))) = h.secImage y h.V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Wp := normalizer (h.secImage y h.B : Set (h.secBar y)) with hWp
  obtain ⟨hK1, hK1c⟩ := isPComponent_secK hc (Or.inl rfl)
  obtain ⟨hK2, hK2c⟩ := isPComponent_secK hc (Or.inr rfl)
  rw [secImage_conjugate h.K hc.a_mem_G0] at hK2 hK2c
  have hV' := secImage_V hc
  obtain ⟨-, -, hO1, hO2⟩ := B5a.pComponent_sup_facts hK1 hK2 hK1c hK2c
  apply le_antisymm
  · refine map_le_iff_le_comap.mpr (sSup_le fun M hM => ?_)
    rw [← map_le_iff_le_comap]
    set M₀ := M.map Wp.subtype with hM₀
    have hM₀W : M₀ ≤ Wp := map_subtype_le _
    have hM₀c : IsPComponent 2 (M₀.subgroupOf Wp) := by
      rw [show M₀.subgroupOf Wp = M from comap_map_eq_self_of_injective Wp.subtype_injective M]
      exact hM
    by_cases hM1 : M₀ = h.secImage y h.K
    · rw [hM1, hV']
      exact le_sup_left
    by_cases hM2 : M₀ = conjugate (h.secImage y h.K) hc.secA
    · rw [hM2, hV']
      exact le_sup_right
    exfalso
    have hMK : M₀ ≤ coreActionKernel (h.secImage y h.V) := by
      intro m hm
      rw [hV']
      exact B5a.mem_coreActionKernel_sup hO1 hO2
        (B5a.le_coreActionKernel_of_ne hK1 hM₀W hK1c hM₀c (Ne.symm hM1) hm)
        (B5a.le_coreActionKernel_of_ne hK2 hM₀W hK2c hM₀c (Ne.symm hM2) hm)
    have hpre : h.secPre y M₀ ≤ h.W ⊓ coreActionKernel h.V := by
      intro g hg
      have hgG := secPre_le_G0 M₀ hg
      have hg' := secMk_mem_of_mem_secPre hg
      have hgW : g ∈ h.W := by
        have h1 := hM₀W hg'
        rw [hWp, hc.normalizer_secB,
          secMk_mem_secImage_iff ((h.secB0_le_B y).trans le_normalizer)] at h1
        exact h1
      have : Group.IsPerfect h.V := isPerfect_V
      exact mem_inf.mpr ⟨hgW, mem_coreActionKernel_of_secMk (h.V_le_G0 y)
        (h.V_le_centralizer_secB0 y) hgG (OddQuot.le_normalizer_layerIn _ hgW) (hMK hg')⟩
    have : Group.IsSolvable ↥(h.W ⊓ coreActionKernel h.V) := isSolvable_kernel_V
    have : Group.IsSolvable ↥(h.secPre y M₀) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hpre)
    have : Group.IsSolvable ↥((h.secPre y M₀).subgroupOf (h.secG0 y)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (secPre_le_G0 M₀)).toMonoidHom)
        (subgroupOfEquivOfLe (secPre_le_G0 M₀)).injective
    have : Group.IsSolvable ↥(h.secImage y (h.secPre y M₀)) :=
      Group.isSolvable_of_surjective ((h.secMk y).subgroupMap_surjective _)
    have : Group.IsSolvable ↥M₀ := Group.isSolvable_of_isSolvable_injective
      (f := (MulEquiv.subgroupCongr (secImage_secPre M₀).symm).toMonoidHom)
      (MulEquiv.subgroupCongr (secImage_secPre M₀).symm).injective
    have : Group.IsPerfect M₀ := B5a.isPerfect_of_isPComponent_subgroupOf hM₀W hM₀c
    have : Nontrivial M₀ := B5a.nontrivial_of_isPComponent_subgroupOf hM₀W hM₀c
    exact Group.IsPerfect.not_isSolvable M₀ inferInstance
  · rw [hV']
    refine sup_le ?_ ?_
    · have h1 := map_mono (f := Wp.subtype)
        (show (h.secImage y h.K).subgroupOf Wp ≤ pLayer ↥Wp 2 from le_sSup hK1c)
      rwa [map_subgroupOf_eq_of_le hK1] at h1
    · have h1 := map_mono (f := Wp.subtype)
        (show (conjugate (h.secImage y h.K) hc.secA).subgroupOf Wp ≤ pLayer ↥Wp 2 from
          le_sSup hK2c)
      rwa [map_subgroupOf_eq_of_le hK2] at h1

theorem secImage_conjClosure {T Y : Subgroup X} (hT : T ≤ h.secG0 y) (hY : Y ≤ h.secG0 y) :
    h.secImage y (conjClosure T Y) = conjClosure (h.secImage y T) (h.secImage y Y) := by
  apply le_antisymm
  · have h1 : conjClosure T Y ≤ h.secPre y (conjClosure (h.secImage y T) (h.secImage y Y)) := by
      refine iSup₂_le fun g hg => ?_
      intro z hz
      have hgG : g ∈ h.secG0 y := hY hg
      have hzG : z ∈ h.secG0 y := by
        rw [mem_conjugate_iff] at hz
        have h2 := mul_mem (mul_mem (inv_mem hgG) (hT hz)) hgG
        rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h2
      refine ⟨⟨z, hzG⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      have h3 : h.secMk y ⟨z, hzG⟩ ∈ conjugate (h.secImage y T) (h.secMk y ⟨g, hgG⟩) := by
        rw [← secImage_conjugate T hgG]
        exact mem_map_of_mem _ (show (⟨z, hzG⟩ : ↥(h.secG0 y)) ∈
          (conjugate T g).subgroupOf (h.secG0 y) from hz)
      exact (show conjugate (h.secImage y T) (h.secMk y ⟨g, hgG⟩) ≤
          conjClosure (h.secImage y T) (h.secImage y Y) from
        le_iSup₂_of_le (h.secMk y ⟨g, hgG⟩) (mem_map_of_mem _
          (show (⟨g, hgG⟩ : ↥(h.secG0 y)) ∈ Y.subgroupOf (h.secG0 y) from hg)) le_rfl) h3
    exact (secImage_mono h1).trans (secImage_secPre _).le
  · refine iSup₂_le fun g' hg' => ?_
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hg'
    rw [← secImage_conjugate T g.2]
    exact secImage_mono (le_iSup₂_of_le (g : X) hg le_rfl)

theorem secImage_commutator {A C : Subgroup X} (hA : A ≤ h.secG0 y) (hC : C ≤ h.secG0 y) :
    h.secImage y ⁅A, C⁆ = ⁅h.secImage y A, h.secImage y C⁆ := by
  show (⁅A, C⁆.subgroupOf (h.secG0 y)).map (h.secMk y) = _
  have h1 : ⁅A, C⁆.subgroupOf (h.secG0 y) = ⁅A.subgroupOf (h.secG0 y), C.subgroupOf (h.secG0 y)⁆
      := by
    apply map_injective (h.secG0 y).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le ((commutator_mono hA hC).trans
      (commutator_le_self _)), map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hC]
  rw [h1, map_commutator]

theorem conjClosure_secW (hc : h.SecCond y) :
    conjClosure (GSLit.fixedLayer (h.secImage y (h.secJ0 y)) (h.secImage y h.B))
      (layerIn (normalizer (h.secImage y h.B : Set (h.secBar y)))) =
      layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))) := by
  have hJBV : GSLit.fixedLayer h.J h.B ≤ h.V := B5a.fixedLayer_le_V h
  rw [layerIn_secW hc, secFixedLayer_B hc, ← secImage_conjClosure (hJBV.trans (h.V_le_G0 y))
    (h.V_le_G0 y), h.conjClosure_eq]

theorem commutator_secW (hc : h.SecCond y) :
    ⁅layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))), zpowers hc.secA⁆ =
      layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))) := by
  rw [layerIn_secW hc, ← secImage_zpowers hc.a_mem_G0, ← secImage_commutator (h.V_le_G0 y)
    (zpowers_le.mpr hc.a_mem_G0), h.commutator_eq]

theorem secB_le_kernel (hc : h.SecCond y) :
    h.secImage y h.B ≤ normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓
      coreActionKernel (layerIn (normalizer (h.secImage y h.B : Set (h.secBar y)))) := by
  rw [layerIn_secW hc]
  refine le_inf le_normalizer ?_
  rintro _ ⟨b, hb, rfl⟩
  have hb' : (b : X) ∈ h.B := hb
  exact secMk_mem_coreActionKernel (h.V_le_G0 y) b.2 (mem_inf.mp (h.B_le_kernel hb')).2

theorem secPre_kernel_le (hc : h.SecCond y) :
    h.secPre y (normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓
      coreActionKernel (h.secImage y h.V)) ≤ h.W ⊓ coreActionKernel h.V := by
  intro g hg
  have hgG := secPre_le_G0 _ hg
  obtain ⟨hgW', hgK'⟩ := mem_inf.mp (secMk_mem_of_mem_secPre hg)
  have hgW : g ∈ h.W := by
    have h1 : h.secMk y ⟨g, hgG⟩ ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) := hgW'
    rw [hc.normalizer_secB, secMk_mem_secImage_iff ((h.secB0_le_B y).trans le_normalizer)]
      at h1
    exact h1
  have : Group.IsPerfect h.V := isPerfect_V
  exact mem_inf.mpr ⟨hgW, mem_coreActionKernel_of_secMk (h.V_le_G0 y)
    (h.V_le_centralizer_secB0 y) hgG (OddQuot.le_normalizer_layerIn _ hgW) hgK'⟩

theorem secB_sylow_kernel (hc : h.SecCond y) :
    ∃ R : Sylow 2 ↥(normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓
      coreActionKernel (layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))))),
      (R : Subgroup _) = (h.secImage y h.B).subgroupOf
        (normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓
          coreActionKernel (layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [layerIn_secW hc]
  set C' := normalizer (h.secImage y h.B : Set (h.secBar y)) ⊓
    coreActionKernel (h.secImage y h.V) with hC'
  set Cs := h.secPre y C' with hCs
  set CW := h.W ⊓ coreActionKernel h.V with hCW
  have hBC' : h.secImage y h.B ≤ C' := by
    have h1 := secB_le_kernel hc
    rwa [layerIn_secW hc] at h1
  have hBCs : h.B ≤ Cs := by
    intro b hb
    refine ⟨⟨b, hc.B_le_G0 hb⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap]
    exact hBC' (mem_map_of_mem _ (show (⟨b, hc.B_le_G0 hb⟩ : ↥(h.secG0 y)) ∈
      h.B.subgroupOf (h.secG0 y) from hb))
  have hCsW : Cs ≤ CW := secPre_kernel_le hc
  obtain ⟨R, hR⟩ := h.B_sylow_kernel
  have hodd : ¬ 2 ∣ h.B.relIndex CW := by
    rw [relIndex, ← hR]
    exact R.not_dvd_index
  have hrel := Subgroup.relIndex_mul_relIndex h.B Cs CW hBCs hCsW
  have hodd' : ¬ 2 ∣ h.B.relIndex Cs := fun h2 => hodd (hrel ▸ dvd_mul_of_dvd_left h2 _)
  have hB0 : h.secB0 y ≤ h.B := h.secB0_le_B y
  have hcB := card_secImage hB0 hc.B_le_G0
  have hcC := card_secImage (hB0.trans hBCs) (secPre_le_G0 C')
  rw [secImage_secPre] at hcC
  have hB0pos : 0 < Nat.card (h.secB0 y) := Nat.card_pos
  have hidx : ((h.secImage y h.B).subgroupOf C').index = h.B.relIndex Cs := by
    have e1 := Subgroup.card_mul_index ((h.secImage y h.B).subgroupOf C')
    have e2 := Subgroup.card_mul_index (h.B.subgroupOf Cs)
    rw [Nat.card_congr (subgroupOfEquivOfLe hBC').toEquiv] at e1
    rw [Nat.card_congr (subgroupOfEquivOfLe hBCs).toEquiv] at e2
    have hpos : 0 < Nat.card (h.secImage y h.B) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hB0pos)
    calc Nat.card (h.secImage y h.B) * Nat.card (h.secB0 y) *
          ((h.secImage y h.B).subgroupOf C').index
        = Nat.card C' * Nat.card (h.secB0 y) := by rw [← e1]; ring
      _ = Nat.card Cs := hcC
      _ = Nat.card h.B * (h.B.subgroupOf Cs).index := e2.symm
      _ = Nat.card (h.secImage y h.B) * Nat.card (h.secB0 y) * h.B.relIndex Cs := by
          rw [← hcB]; rfl
  have hB2 : IsPGroup 2 (h.secImage y h.B) :=
    ((B5a.isPGroup_B h).comap_subtype (K := h.secG0 y)).map (h.secMk y)
  have h2 : IsPGroup 2 ((h.secImage y h.B).subgroupOf C') := hB2.comap_subtype
  refine ⟨h2.toSylow (by rw [hidx]; exact hodd'), ?_⟩
  rw [IsPGroup.toSylow_coe]

theorem secIsQuasisimple_K : IsQuasisimple (↥h.K ⧸ pPrimeCore 2 ↥h.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.K h.W h.isPComponent_K.1).mp
    h.isPComponent_K.2).2.2

theorem K_le_centralizer_secB0 : h.K ≤ centralizer (h.secB0 y : Set X) :=
  K_le_V.trans (h.V_le_centralizer_secB0 y)

theorem K_le_secG0 : h.K ≤ h.secG0 y := K_le_V.trans (h.V_le_G0 y)

theorem nonempty_secK_fusionZStar_equiv :
    Nonempty (↥(h.secImage y h.K) ⧸ Open.fusionZStar ↥(h.secImage y h.K) ≃*
      ↥h.K ⧸ Open.fusionZStar ↥h.K) := by
  let e₁ : ↥(h.K.subgroupOf (h.secG0 y)) ≃* ↥h.K := subgroupOfEquivOfLe K_le_secG0
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  have hq : IsQuasisimple (↥(h.K.subgroupOf (h.secG0 y)) ⧸
      pPrimeCore 2 ↥(h.K.subgroupOf (h.secG0 y))) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr e₂).2 secIsQuasisimple_K
  obtain ⟨e₃⟩ := TwoQuot.nonempty_fusionZStar_equiv_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y K_le_centralizer_secB0) hq
  obtain ⟨e₄⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv e₂
  exact ⟨e₃.symm.trans e₄⟩

theorem nonempty_secK_pPrimeCore_equiv (hZ : center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥) :
    Nonempty (↥(h.secImage y h.K) ⧸ pPrimeCore 2 ↥(h.secImage y h.K) ≃*
      ↥h.K ⧸ pPrimeCore 2 ↥h.K) := by
  let e₁ : ↥(h.K.subgroupOf (h.secG0 y)) ≃* ↥h.K := subgroupOfEquivOfLe K_le_secG0
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₁
  have hZ' : center (↥(h.K.subgroupOf (h.secG0 y)) ⧸
      pPrimeCore 2 ↥(h.K.subgroupOf (h.secG0 y))) = ⊥ :=
    B5a.center_eq_bot_of_equiv e₂.symm hZ
  obtain ⟨e₃⟩ := TwoQuot.nonempty_pPrimeCore_equiv_map (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y K_le_centralizer_secB0) (h.isPGroup_ker_secMk y) hZ'
  exact ⟨e₃.symm.trans e₂⟩

theorem conjugate_secK_eq_iff (hc : h.SecCond y) :
    conjugate (h.secImage y h.K) hc.secA = h.secImage y h.K ↔ conjugate h.K h.a = h.K := by
  rw [← secImage_conjugate h.K hc.a_mem_G0]
  constructor
  · intro heq
    have : Group.IsNilpotent ↥(h.secMk y).ker := (h.isPGroup_ker_secMk y).isNilpotent
    have hKa := OddQuot.isPComponent_conjugate_subgroupOf h.a_mem_normalizer
      h.isPComponent_K.1 h.isPComponent_K.2
    have : Group.IsPerfect (h.K.subgroupOf (h.secG0 y)) :=
      have : Group.IsPerfect h.K :=
        B5a.isPerfect_of_isPComponent_subgroupOf h.isPComponent_K.1 h.isPComponent_K.2
      Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (K_le_secG0 (h := h) (y := y))).symm.toMonoidHom)
        (subgroupOfEquivOfLe (K_le_secG0 (h := h) (y := y))).symm.surjective
    have hKaG : conjugate h.K h.a ≤ h.secG0 y := conjugate_K_le_V.trans (h.V_le_G0 y)
    have : Group.IsPerfect ((conjugate h.K h.a).subgroupOf (h.secG0 y)) :=
      have : Group.IsPerfect (conjugate h.K h.a) :=
        B5a.isPerfect_of_isPComponent_subgroupOf hKa.1 hKa.2
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKaG).symm.toMonoidHom)
        (subgroupOfEquivOfLe hKaG).symm.surjective
    have h1 := TwoQuot.eq_of_map_eq_of_le_centralizer (h.secMk y)
      (h.subgroupOf_le_centralizer_ker y
        (conjugate_K_le_V.trans (h.V_le_centralizer_secB0 y)))
      (h.subgroupOf_le_centralizer_ker y K_le_centralizer_secB0) heq
    rw [subgroupOf_inj, inf_of_le_left hKaG, inf_of_le_left K_le_secG0] at h1
    exact h1
  · intro heq
    rw [heq]

theorem type_secK (hc : h.SecCond y) :
    GSRestricted (↥(h.secImage y h.K) ⧸ Open.fusionZStar ↥(h.secImage y h.K)) ∨
      (conjugate (h.secImage y h.K) hc.secA ≠ h.secImage y h.K ∧
        Nonempty (↥(h.secImage y h.K) ⧸ Open.fusionZStar ↥(h.secImage y h.K) ≃*
          ↥(h.secImage y (h.secJ0 y)) ⧸ Open.fusionZStar ↥(h.secImage y (h.secJ0 y)))) := by
  obtain ⟨eK⟩ := nonempty_secK_fusionZStar_equiv (h := h) (y := y)
  obtain ⟨eJ⟩ := nonempty_secJ_fusionZStar_equiv (h := h) (y := y)
  rcases h.type_K with hR | ⟨hne, ⟨e⟩⟩
  · exact Or.inl (OddQuot.gsRestricted_of_mulEquiv eK.symm hR)
  · refine Or.inr ⟨fun heq => hne ((conjugate_secK_eq_iff hc).mp heq), ⟨eK.trans (e.trans eJ.symm)⟩⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
