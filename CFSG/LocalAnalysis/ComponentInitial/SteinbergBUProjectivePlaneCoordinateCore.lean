module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneGivenFrame
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCycleFrame

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ] {K : Type*} [Field K] {p : ℕ}

noncomputable abbrev frameFullTorus (L : Γ →* G) (τ : Γ →* GL (Fin p) K)
    (hker : ∀ x, L x = 1 ↔ ∃ u : Kˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)
    (P : GL (Fin p) K) : Subgroup G :=
  ((torusHom P).range.subgroupOf (projHom τ).range).map (rangeLift L τ hker)

theorem coordinate_torus_of_given_frame (hp : p.Prime) (L : Γ →* G) (τ : Γ →* GL (Fin p) K)
    (hker : ∀ x, L x = 1 ↔ ∃ u : Kˣ, τ x = GeneralLinearGroup.scalar (Fin p) u)
    {d : G} {A : Γ} (hAd : L A = d) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (P : GL (Fin p) K)
    (hP : (τ A : Matrix (Fin p) (Fin p) K) = (P : Matrix (Fin p) (Fin p) K) *
      diagonal (fun i : Fin p => ζ ^ (i : ℕ)) * ((P⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    (W : GL (Fin p) K)
    (hW : (W : Matrix (Fin p) (Fin p) K) * diagonal (fun i : Fin p => ζ ^ (i : ℕ)) =
      ζ⁻¹ • (diagonal (fun i : Fin p => ζ ^ (i : ℕ)) * W))
    (hWp : W ^ p = 1) (hWJ : mk (P * W * P⁻¹) ∈ (projHom τ).range) :
    (∀ α, α ∈ frameTorus L τ hker P ↔ α ∈ frameFullTorus L τ hker P ∧ α ^ p = 1) ∧
      frameFullTorus L τ hker P ≤ L.range ⊓ Subgroup.centralizer {d} ∧
      ((frameFullTorus L τ hker P).subgroupOf (L.range ⊓ Subgroup.centralizer {d})).Normal ∧
      rangeLift L τ hker ⟨_, hWJ⟩ ∈ L.range ⊓ Subgroup.centralizer {d} ∧
      orderOf (rangeLift L τ hker ⟨_, hWJ⟩) = p ∧
      frameFullTorus L τ hker P ⊓ Subgroup.zpowers (rangeLift L τ hker ⟨_, hWJ⟩) = ⊥ ∧
      frameFullTorus L τ hker P ⊔ Subgroup.zpowers (rangeLift L τ hker ⟨_, hWJ⟩) =
        L.range ⊓ Subgroup.centralizer {d} := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set ζu : Kˣ := Units.mk0 ζ hζ0
  have hζu : IsPrimitiveRoot (ζu : K) p := hζ
  have hroot : (fun i : Fin p => ((rootVec ζu i : Kˣ) : K)) = fun i : Fin p => ζ ^ (i : ℕ) :=
    funext fun i => by simp [rootVec, ζu]
  have hAP : τ A = P * TauCeti.diagGL (rootVec ζu) * P⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, hroot, hP]
  have hWrel : W * TauCeti.diagGL (rootVec ζu) =
      GeneralLinearGroup.scalar (Fin p) ζu⁻¹ * (TauCeti.diagGL (rootVec ζu) * W) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, hroot, hW,
      GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_eq_diagonal_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0]
  set J := (projHom τ).range
  set ι := rangeLift L τ hker
  have hιinj := rangeLift_injective L τ hker
  have hιrange := range_rangeLift L τ hker
  have hd'J : frameElt P ζu ∈ J := ⟨A, by rw [MonoidHom.comp_apply, hAP]; rfl⟩
  have hιd' : ι ⟨frameElt P ζu, hd'J⟩ = d := by
    rw [← hAd, ← rangeLift_apply L τ hker A]
    congr 1
    exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, MonoidHom.comp_apply, hAP]; rfl)
  have hpull : ∀ j : J, ι j * d = d * ι j →
      (j : ProjGenLinGroup (Fin p) K) ∈ Subgroup.centralizer {frameElt P ζu} := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    rw [← hιd', ← map_mul, ← map_mul] at hj
    exact (congrArg Subtype.val (hιinj hj)).symm
  have hw'C := mk_cycle_mem_centralizer P hWrel
  have hΩ : ∀ α, α ∈ frameTorus L τ hker P ↔ α ∈ frameFullTorus L τ hker P ∧ α ^ p = 1 := by
    intro α
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' := Subgroup.mem_subgroupOf.1 hj
      refine ⟨⟨j, Subgroup.mem_subgroupOf.2 ?_, rfl⟩, ?_⟩
      · obtain ⟨x, -, hx⟩ := mem_omegaTorus.1 hj'
        exact ⟨x, hx⟩
      · rw [← map_pow, ← map_one ι]
        exact congrArg ι (Subtype.ext (by
          rw [SubmonoidClass.coe_pow]; exact omegaTorus_pow P _ hj'))
    · rintro ⟨⟨j, hj, rfl⟩, hp1⟩
      obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 hj
      refine ⟨j, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
      have hjp : j ^ p = 1 := hιinj (by rw [map_pow, hp1, map_one])
      rw [← hx]
      apply mem_omegaTorus_of_pow
      rw [hx, ← SubmonoidClass.coe_pow, hjp, OneMemClass.coe_one]
  have hTC : frameFullTorus L τ hker P ≤ L.range ⊓ Subgroup.centralizer {d} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_inf.2 ⟨by rw [← hιrange]; exact ⟨j, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, ← hιd', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 hj
    change frameElt P ζu * (j : ProjGenLinGroup (Fin p) K) =
      (j : ProjGenLinGroup (Fin p) K) * frameElt P ζu
    rw [← hx]
    exact torusHom_comm P _ _
  have hwC : ι ⟨_, hWJ⟩ ∈ L.range ⊓ Subgroup.centralizer {d} := by
    refine Subgroup.mem_inf.2 ⟨by rw [← hιrange]; exact ⟨_, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, ← hιd', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hw'C _ rfl
  have hword : orderOf (ι ⟨_, hWJ⟩) = p := by
    rw [orderOf_injective ι hιinj, Subgroup.orderOf_mk]
    exact orderOf_cycleElt P hWrel hp hζu hWp
  have hinf : frameFullTorus L τ hker P ⊓ Subgroup.zpowers (ι ⟨_, hWJ⟩) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨j, hj, rfl⟩, hjw⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hjw
    rw [← map_zpow] at hk
    have hjk : (⟨_, hWJ⟩ : J) ^ k = j := hιinj hk
    have hmem : mk (P * W * P⁻¹) ^ k ∈ (torusHom P).range := by
      have h1 := Subgroup.mem_subgroupOf.1 hj
      rw [← hjk, SubgroupClass.coe_zpow] at h1
      exact h1
    have h1 := eq_one_of_zpow_mem_torus P hWrel hζu hWp hmem
    have hj1 : j = 1 := by
      rw [← hjk]
      exact Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact h1)
    rw [Subgroup.mem_bot, hj1, map_one]
  have hsup : frameFullTorus L τ hker P ⊔ Subgroup.zpowers (ι ⟨_, hWJ⟩) =
      L.range ⊓ Subgroup.centralizer {d} := by
    apply le_antisymm (sup_le hTC ((Subgroup.zpowers_le).2 hwC))
    intro g hg
    obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.1 hg
    rw [← hιrange] at hgL
    obtain ⟨j, rfl⟩ := hgL
    have hjc := hpull j (Subgroup.mem_centralizer_iff.1 hgC d rfl).symm
    obtain ⟨x, k, hxk⟩ := exists_torus_mul_pow P hWrel hζu ⟨_, hjc⟩
    have hxJ : torusHom P x ∈ J := by
      rw [eq_mul_inv_of_mul_eq hxk.symm]
      exact J.mul_mem j.2 (J.inv_mem (J.pow_mem hWJ k))
    have hj : j = ⟨torusHom P x, hxJ⟩ * (⟨_, hWJ⟩ : J) ^ k :=
      Subtype.ext (by rw [Subgroup.coe_mul, SubgroupClass.coe_pow]; exact hxk)
    rw [hj, map_mul ι, map_pow ι]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ⟨_, Subgroup.mem_subgroupOf.2 ⟨x, rfl⟩, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  have hnorm : ((frameFullTorus L τ hker P).subgroupOf
      (L.range ⊓ Subgroup.centralizer {d})).Normal := by
    refine ⟨fun t ht c => Subgroup.mem_subgroupOf.2 ?_⟩
    obtain ⟨jt, hjt, hjteq⟩ := Subgroup.mem_subgroupOf.1 ht
    obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.1 c.2
    have hcL' : (c : G) ∈ ι.range := by rw [hιrange]; exact hcL
    obtain ⟨jc, hjc⟩ := hcL'
    have hjcC := hpull jc (by rw [hjc]; exact (Subgroup.mem_centralizer_iff.1 hcC d rfl).symm)
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 hjt
    obtain ⟨x', hx'⟩ := conj_mem_torus P hζu ⟨_, hjcC⟩ x
    refine ⟨jc * jt * jc⁻¹, Subgroup.mem_subgroupOf.2 ⟨x', ?_⟩, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [map_mul ι, map_mul ι, map_inv ι, hjc, hjteq]
      rfl
  exact ⟨hΩ, hTC, hnorm, hwC, hword, hinf, hsup⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
