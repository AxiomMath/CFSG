module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

variable {G : Type*} [Group G]

@[expose] def conjAut (H : Subgroup G) (g : G) (hg : g ∈ normalizer (H : Set G)) : MulAut H where
  toFun h := ⟨g * h * g⁻¹, (hg h.1).1 h.2⟩
  invFun h := ⟨g⁻¹ * h * g, by
    have := ((inv_mem hg : g⁻¹ ∈ normalizer (H : Set G)) h.1).1 h.2
    simpa using this⟩
  left_inv h := by
    apply Subtype.ext
    group
  right_inv h := by
    apply Subtype.ext
    group
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem conjAut_coe (H : Subgroup G) (g : G) (hg : g ∈ normalizer (H : Set G)) (h : H) :
    ((conjAut H g hg h : H) : G) = g * h * g⁻¹ := by
  rfl

private theorem conjAut_congr (H : Subgroup G) {g g' : G}
    (hg : g ∈ normalizer (H : Set G)) (hg' : g' ∈ normalizer (H : Set G)) (h : g = g') :
    conjAut H g hg = conjAut H g' hg' := by
  subst h
  rfl

theorem conjAut_mul (H : Subgroup G) {g k : G} (hg : g ∈ normalizer (H : Set G))
    (hk : k ∈ normalizer (H : Set G)) (hgk : g * k ∈ normalizer (H : Set G)) :
    conjAut H (g * k) hgk = conjAut H g hg * conjAut H k hk := by
  ext h
  simp only [conjAut_coe, MulAut.mul_apply, Subgroup.coe_mul]
  group

theorem conjAut_one (H : Subgroup G) (h1 : (1 : G) ∈ normalizer (H : Set G)) :
    conjAut H 1 h1 = 1 := by
  ext h
  simp only [conjAut_coe, MulAut.one_apply]
  simp

theorem conjAut_inv (H : Subgroup G) {g : G} (hg : g ∈ normalizer (H : Set G))
    (hg' : g⁻¹ ∈ normalizer (H : Set G)) : conjAut H g⁻¹ hg' = (conjAut H g hg)⁻¹ := by
  refine MulEquiv.ext (fun h => ?_)
  apply (conjAut H g hg).injective
  rw [MulAut.apply_inv_self]
  apply Subtype.ext
  simp only [conjAut_coe]
  group

theorem conjAut_pow (H : Subgroup G) {g : G} (hg : g ∈ normalizer (H : Set G)) (n : ℕ)
    (hgn : g ^ n ∈ normalizer (H : Set G)) : conjAut H (g ^ n) hgn = conjAut H g hg ^ n := by
  revert hgn
  induction n with
  | zero =>
    intro h1
    simpa [pow_zero] using conjAut_one H (one_mem (normalizer (H : Set G)))
  | succ n ih =>
    intro h1
    rw [conjAut_congr H h1 (mul_mem (pow_mem hg n) hg) (pow_succ g n)]
    rw [conjAut_mul H (pow_mem hg n) hg (mul_mem (pow_mem hg n) hg)]
    rw [ih (pow_mem hg n)]
    rw [pow_succ]

theorem conjAut_eq_one_iff (H : Subgroup G) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    conjAut H g hg = 1 ↔ ∀ h ∈ H, g * h = h * g := by
  constructor
  · intro heq a ha
    have h1 : (conjAut H g hg) ⟨a, ha⟩ = (1 : MulAut H) ⟨a, ha⟩ :=
      congrArg (fun f : MulAut H => f ⟨a, ha⟩) heq
    rw [MulAut.one_apply] at h1
    have h2 : g * (⟨a, ha⟩ : H) * g⁻¹ = (⟨a, ha⟩ : H) := by
      have := congrArg (fun x : H => (x : G)) h1
      simpa [conjAut_coe] using this
    rw [mul_inv_eq_iff_eq_mul] at h2
    simpa using h2
  · intro hc
    ext a
    simp only [conjAut_coe, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact hc a a.2

theorem mem_fixSub_conjAut (H : Subgroup G) {g : G} (hg : g ∈ normalizer (H : Set G)) (h : H) :
    h ∈ fixSub (conjAut H g hg) ↔ g * (h : G) = h * g := by
  rw [mem_fixSub, Subtype.ext_iff, conjAut_coe, mul_inv_eq_iff_eq_mul]

theorem map_fixSub_conjAut (H : Subgroup G) {g : G} (hg : g ∈ normalizer (H : Set G)) :
    (fixSub (conjAut H g hg)).map H.subtype = H ⊓ Subgroup.centralizer ({g} : Set G) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, (mem_fixSub_conjAut H hg x).mp hx⟩
  · rintro ⟨hy, hgy⟩
    exact ⟨⟨y, hy⟩, (mem_fixSub_conjAut H hg ⟨y, hy⟩).mpr hgy, rfl⟩

theorem sigma3Rel_conjAut (H : Subgroup G) {ρ x : G} (hρ : ρ ∈ normalizer (H : Set G))
    (hx : x ∈ normalizer (H : Set G)) (h3 : orderOf ρ = 3) (h2 : orderOf x = 2)
    (hrel : x * ρ * x⁻¹ = ρ⁻¹) (hfρ : ∃ h ∈ H, ρ * h ≠ h * ρ) (hfx : ∃ h ∈ H, x * h ≠ h * x) :
    Sigma3Rel (conjAut H ρ hρ) (conjAut H x hx) := by
  have hρ3 : ρ ^ 3 = 1 := by
    have := pow_orderOf_eq_one ρ
    rwa [h3] at this
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h2] at this
  refine ⟨?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · have hp : conjAut H ρ hρ ^ 3 = conjAut H (ρ ^ 3) (pow_mem hρ 3) :=
        (conjAut_pow H hρ 3 (pow_mem hρ 3)).symm
      rw [hp, conjAut_congr H (pow_mem hρ 3) (one_mem _) hρ3]
      exact conjAut_one H (one_mem _)
    · intro hconj
      obtain ⟨h, hh, hne⟩ := hfρ
      exact hne ((conjAut_eq_one_iff H hρ).mp hconj h hh)
  · apply orderOf_eq_prime
    · have hp : conjAut H x hx ^ 2 = conjAut H (x ^ 2) (pow_mem hx 2) :=
        (conjAut_pow H hx 2 (pow_mem hx 2)).symm
      rw [hp, conjAut_congr H (pow_mem hx 2) (one_mem _) hx2]
      exact conjAut_one H (one_mem _)
    · intro hconj
      obtain ⟨h, hh, hne⟩ := hfx
      exact hne ((conjAut_eq_one_iff H hx).mp hconj h hh)
  · have hxρ : x * ρ * x⁻¹ ∈ normalizer (H : Set G) := mul_mem (mul_mem hx hρ) (inv_mem hx)
    have hρi : ρ⁻¹ ∈ normalizer (H : Set G) := inv_mem hρ
    have key : conjAut H (x * ρ * x⁻¹) hxρ = conjAut H ρ⁻¹ hρi :=
      conjAut_congr H hxρ hρi hrel
    have expand : conjAut H (x * ρ * x⁻¹) hxρ
        = conjAut H x hx * conjAut H ρ hρ * (conjAut H x hx)⁻¹ := by
      rw [conjAut_mul H (mul_mem hx hρ) (inv_mem hx) hxρ,
          conjAut_mul H hx hρ (mul_mem hx hρ),
          conjAut_inv H hx (inv_mem hx)]
    rw [expand, conjAut_inv H hρ hρi] at key
    exact key

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
