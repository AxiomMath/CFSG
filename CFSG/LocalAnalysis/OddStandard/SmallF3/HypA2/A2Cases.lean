module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSwap
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

private theorem ne_bot_of_isPComponent_two {G : Type*} [Group G] {X : Subgroup G}
    (hX : IsPComponent 2 X) : X ≠ ⊥ := by
  obtain ⟨K, hK, -, hmap, -⟩ := hX
  intro hbot
  have hKbot : K = ⊥ := by rw [← hmap, hbot, Subgroup.map_bot]
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  rw [hKbot] at hnt
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt

private theorem a2Config_vertical {G : Type} [Group G] [Finite G] {x y : G} {X K : Subgroup G}
    (h : A2Config G x y X K) (hK'eq : K.map (MulAut.conj x).toMonoidHom = K) :
    K.map (MulAut.conj x).toMonoidHom = K ∧ X ≤ K ∧
      ComponentClassification.HarrisLit.IsTwoComponentIn X (K ⊓ centralizer ({x} : Set G)) := by
  have hXK : X ≤ K := by
    have hX := h.X_le_KK
    rw [hK'eq, sup_idem] at hX
    exact hX
  have hXCx : X ≤ centralizer ({x} : Set G) :=
    h.X_le.trans (Subgroup.centralizer_le (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      simp))
  obtain ⟨-, hsubC2, hqX⟩ :=
    (ComponentClassification.HarrisLit.isTwoComponentIn_iff h.X_le).mpr h.X_comp
  have hN : K ⊓ centralizer ({x} : Set G) ≤ centralizer ({x, y} : Set G) := by
    intro z hz
    obtain ⟨hzK, hzCx⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    by_cases hax : a = x
    · rw [hax]
      exact Subgroup.mem_centralizer_iff.mp hzCx x (by simp)
    · have hay : a = y := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        tauto
      rw [hay]
      exact Subgroup.mem_centralizer_iff.mp (h.K_le hzK) y (by simp)
  have hsub : (X.subgroupOf (K ⊓ centralizer ({x} : Set G))).IsSubnormal := by
    have h1 := hsubC2.comap (Subgroup.inclusion hN)
    have heq : (X.subgroupOf (centralizer ({x, y} : Set G))).comap
        (Subgroup.inclusion hN) = X.subgroupOf (K ⊓ centralizer ({x} : Set G)) := by
      ext t; rfl
    rwa [heq] at h1
  exact ⟨hK'eq, hXK, le_inf hXK hXCx, hsub, hqX⟩

private theorem a2Config_diagonal {G : Type} [Group G] [Finite G] {x y : G} {X K : Subgroup G}
    (h : A2Config G x y X K)
    (hK : Omega.IsComponentIn K (centralizer ({y} : Set G)))
    (hK' : Omega.IsComponentIn (K.map (MulAut.conj x).toMonoidHom)
      (centralizer ({y} : Set G)))
    (hne : K.map (MulAut.conj x).toMonoidHom ≠ K) :
    K.map (MulAut.conj x).toMonoidHom ≠ K ∧
      ⁅K, K.map (MulAut.conj x).toMonoidHom⁆ = ⊥ ∧
      ∃ φ : ↥K →* G, (∀ k : ↥K, φ k = (k : G) * (x * k * x⁻¹)) ∧ X = φ.range ∧
        φ.ker ≤ center ↥K := by
  let K' : Subgroup G := K.map (MulAut.conj x).toMonoidHom
  have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
    Omega.IsComponentIn.commute_of_ne hK hK' (Ne.symm hne)
  have hc : K ≤ centralizer (K' : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have hcommutator : ⁅K, K'⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hx2 : x ^ 2 = 1 := by
    have hx := pow_orderOf_eq_one x
    rwa [h.ox] at hx
  have hKperf : Group.IsPerfect ↥K := (Omega.IsComponentIn.isQuasisimple hK).1
  let φ : ↥K →* G := ComponentClassification.HarrisLit.swapDiag K x hc
  have hφapply : ∀ k : ↥K, φ k = (k : G) * (x * k * x⁻¹) := by
    intro k
    change ComponentClassification.HarrisLit.swapDiag K x hc k = (k : G) * (x * k * x⁻¹)
    rw [ComponentClassification.HarrisLit.swapDiag_apply, MulAut.conj_apply]
  have hker : φ.ker ≤ center ↥K := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hm_eq : (m : G) = x * (m : G)⁻¹ * x⁻¹ := by
      have h1 : (m : G) * (x * (m : G) * x⁻¹) = 1 := by
        rw [hφapply m] at hm
        exact hm
      calc (m : G) = ((m : G) * (x * (m : G) * x⁻¹)) * (x * (m : G) * x⁻¹)⁻¹ := by group
        _ = (x * (m : G) * x⁻¹)⁻¹ := by rw [h1, one_mul]
        _ = x * (m : G)⁻¹ * x⁻¹ := by group
    have hmK' : (m : G) ∈ K' := by
      refine ⟨(m : G)⁻¹, K.inv_mem m.2, ?_⟩
      change MulAut.conj x (m : G)⁻¹ = (m : G)
      rw [MulAut.conj_apply]
      exact hm_eq.symm
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hcomm (k : G) k.2 (m : G) hmK')
  have hXCx : X ≤ centralizer ({x} : Set G) :=
    h.X_le.trans (Subgroup.centralizer_le (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      simp))
  obtain ⟨hXleC2, hsubC2, hqX⟩ :=
    (ComponentClassification.HarrisLit.isTwoComponentIn_iff h.X_le).mpr h.X_comp
  have hperfX : Group.IsPerfect ↥X := hqX.1
  have hXleRange : X ≤ φ.range := by
    have h1 : X ≤ ComponentClassification.HarrisLit.centralizerResidual (K ⊔ K') x :=
      ComponentClassification.HarrisLit.le_perfectResidual_map
        (le_inf h.X_le_KK hXCx) hperfX
    have h2 : ComponentClassification.HarrisLit.centralizerResidual (K ⊔ K') x = φ.range :=
      ComponentClassification.HarrisLit.centralizerResidual_sup_eq_range K hx2 hc hKperf
    rwa [h2] at h1
  have hRleC2 : φ.range ≤ centralizer ({x, y} : Set G) := by
    rintro r ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    by_cases hax : a = x
    · rw [hax]
      have hfix := ComponentClassification.HarrisLit.conj_swapDiag K hx2 hc k
      rw [MulAut.conj_apply] at hfix
      calc x * ComponentClassification.HarrisLit.swapDiag K x hc k =
            x * ComponentClassification.HarrisLit.swapDiag K x hc k * x⁻¹ * x := by group
        _ = ComponentClassification.HarrisLit.swapDiag K x hc k * x := by rw [hfix]
    · have hay : a = y := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        tauto
      rw [hay]
      have hsup : K ⊔ K' ≤ centralizer ({y} : Set G) := sup_le h.K_le (Omega.IsComponentIn.le hK')
      have hmem : ComponentClassification.HarrisLit.swapDiag K x hc k ∈ K ⊔ K' := by
        rw [ComponentClassification.HarrisLit.swapDiag_apply]
        exact Subgroup.mul_mem_sup k.2
          ⟨(k : G), k.2, by simp [MulAut.conj_apply]⟩
      exact Subgroup.mem_centralizer_iff.mp (hsup hmem) y (by simp)
  have hRangeX : φ.range ≤ X := by
    have hsubXR : (X.subgroupOf φ.range).IsSubnormal := by
      have h1 := hsubC2.comap (Subgroup.inclusion hRleC2)
      have heq : (X.subgroupOf (centralizer ({x, y} : Set G))).comap
          (Subgroup.inclusion hRleC2) = X.subgroupOf φ.range := by
        ext t; rfl
      rwa [heq] at h1
    have hRq : CFSG.IsQuasisimple ↥φ.range :=
      CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
        (Omega.IsComponentIn.isQuasisimple hK) φ hker
    have hcomp_top : IsComponent (⊤ : Subgroup ↥φ.range) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hRq,
        Subgroup.IsSubnormal.top⟩
    rcases CFSG.LocalCores.component_subnormal_subgroup hcomp_top hsubXR with htop | hcen
    · exact Subgroup.subgroupOf_eq_top.mp (eq_top_iff.mpr htop)
    · exfalso
      have hUleZ : X.subgroupOf φ.range ≤ Subgroup.center ↥φ.range :=
        Subgroup.commutator_top_left_eq_bot_iff_le_center.mp hcen
      have hUcomm : IsMulCommutative ↥(X.subgroupOf φ.range) :=
        IsMulCommutative.of_comm fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.mp (hUleZ a.2) (b : ↥φ.range)).symm
      have hXnt : X ≠ ⊥ := by
        intro hbot
        exact ne_bot_of_isPComponent_two h.X_comp
          (by rw [hbot]; exact Subgroup.bot_subgroupOf (centralizer ({x, y} : Set G)))
      haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXnt
      haveI : Nontrivial ↥(X.subgroupOf φ.range) :=
        (Subgroup.subgroupOfEquivOfLe hXleRange).surjective.nontrivial
      haveI : Group.IsPerfect ↥X := hperfX
      have hUperf : Group.IsPerfect ↥(X.subgroupOf φ.range) :=
        Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hXleRange).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hXleRange).symm.surjective
      haveI : Group.IsPerfect ↥(X.subgroupOf φ.range) := hUperf
      exact (Group.IsPerfect.not_isMulCommutative ↥(X.subgroupOf φ.range)) hUcomm
  exact ⟨hne, hcommutator, φ, hφapply, le_antisymm hXleRange hRangeX, hker⟩

theorem a2Config_cases {G : Type} [Group G] [Finite G] {x y : G} {X K : Subgroup G}
    (hbal : oddCore (centralizer ({y} : Set G)) = ⊥) (h : A2Config G x y X K) :
    Omega.IsComponentIn K (centralizer ({y} : Set G)) ∧
    ((K.map (MulAut.conj x).toMonoidHom = K ∧ X ≤ K ∧
        ComponentClassification.HarrisLit.IsTwoComponentIn X (K ⊓ centralizer ({x} : Set G))) ∨
      (K.map (MulAut.conj x).toMonoidHom ≠ K ∧ ⁅K, K.map (MulAut.conj x).toMonoidHom⁆ = ⊥ ∧
        ∃ φ : ↥K →* G, (∀ k : ↥K, φ k = (k : G) * (x * k * x⁻¹)) ∧ X = φ.range ∧
          φ.ker ≤ center ↥K)) := by
  have hxC : x ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact h.comm.symm
  have hK : Omega.IsComponentIn K (centralizer ({y} : Set G)) :=
    isComponentIn_of_isPComponent hbal h.K_le h.K_comp
  have hK' : Omega.IsComponentIn (K.map (MulAut.conj x).toMonoidHom)
      (centralizer ({y} : Set G)) := Omega.IsComponentIn.map_conj hK hxC
  refine ⟨hK, ?_⟩
  by_cases hne : K.map (MulAut.conj x).toMonoidHom = K
  · exact Or.inl (a2Config_vertical h hne)
  · exact Or.inr (a2Config_diagonal h hK hK' hne)

end CFSG.OddStandard.SmallF3.HypA2
