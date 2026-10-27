module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

open scoped Pointwise

variable {G : Type} [Group G]

private lemma mul_four {g t a b : G} (hg2 : g ^ 2 = 1) (ht2 : t ^ 2 = 1) (hgt : g * t = t * g)
    (ha : a = 1 ∨ a = g ∨ a = t ∨ a = g * t)
    (hb : b = 1 ∨ b = g ∨ b = t ∨ b = g * t) :
    a * b = 1 ∨ a * b = g ∨ a * b = t ∨ a * b = g * t := by
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hgt' : t * g = g * t := hgt.symm
  have hgtg : t * (g * t) = g := by rw [← mul_assoc, hgt', mul_assoc, htt, mul_one]
  have hggt : (g * t) * g = t := by rw [mul_assoc, hgt', ← mul_assoc, hgg, one_mul]
  have hgtt : (g * t) * t = g := by rw [mul_assoc, htt, mul_one]
  have hgtr : (g * t) * (g * t) = 1 := by rw [mul_assoc, hgtg, hgg]
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [← mul_assoc, one_mul, mul_one, hgg, htt, hgt', hgtg, hggt, hgtt, hgtr] <;> simp

private lemma conj_mem_closure_pair {H : Type*} [Group H] (x : H) {g t : H}
    (hxg : x * g * x⁻¹ = g) (hxt : x * t * x⁻¹ = g * t) (h : H)
    (hh : h ∈ closure ({g, t} : Set H)) :
    x * h * x⁻¹ ∈ closure ({g, t} : Set H) := by
  refine Subgroup.closure_induction (p := fun h _ => x * h * x⁻¹ ∈ closure ({g, t} : Set H))
    ?_ ?_ ?_ ?_ hh
  · intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · rw [hxg]; exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, hxt]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

theorem y6f4a_closure_pair_cases {g t : G} (hg2 : g ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hgt : g * t = t * g) {x : G} (hx : x ∈ closure ({g, t} : Set G)) :
    x = 1 ∨ x = g ∨ x = t ∨ x = g * t := by
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = g ∨ x = t ∨ x = g * t)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl
  · intro a b _ _ ha hb; exact mul_four hg2 ht2 hgt ha hb
  · intro a _ ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hgg))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right htt)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hgg, inv_eq_of_mul_eq_one_right htt]
      exact hgt.symm

theorem y6f4a_no_conj_of_normalizer {g t : G} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1)
    (hgt : g * t = t * g)
    (hNH : centralizer ({g} : Set G) ⊓ normalizer ((zpowers g ⊔ zpowers t : Subgroup G) : Set G) ≤
      centralizer ({t} : Set G)) :
    ∀ x ∈ centralizer ({g} : Set G), x * t * x⁻¹ ≠ g * t := by
  intro x hx hxt
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hxg : x * g * x⁻¹ = g := by
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [Subgroup.mem_centralizer_singleton_iff.mp hx]
      _ = g := by group
  have hxgt : x * (g * t) * x⁻¹ = t := by
    calc x * (g * t) * x⁻¹ = (x * g * x⁻¹) * (x * t * x⁻¹) := by group
      _ = g * (g * t) := by rw [hxg, hxt]
      _ = t := by rw [← mul_assoc, hgg, one_mul]
  have hxig : x⁻¹ * g * x = g := by
    calc x⁻¹ * g * x = x⁻¹ * (x * g * x⁻¹) * x := by rw [hxg]
      _ = g := by group
  have hxigt : x⁻¹ * (g * t) * x = t := by
    calc x⁻¹ * (g * t) * x = x⁻¹ * (x * t * x⁻¹) * x := by rw [hxt]
      _ = t := by group
  have hx_it : x⁻¹ * t * x = g * t := by
    have h1 : g * (x⁻¹ * t * x) = t := by
      have h2 : (x⁻¹ * g * x) * (x⁻¹ * t * x) = t := by
        rw [show (x⁻¹ * g * x) * (x⁻¹ * t * x) = x⁻¹ * (g * t) * x by group, hxigt]
      rwa [hxig] at h2
    calc x⁻¹ * t * x = g⁻¹ * (g * (x⁻¹ * t * x)) := by group
      _ = g⁻¹ * t := by rw [h1]
      _ = g * t := by rw [hgi]
  have hVeq : (zpowers g ⊔ zpowers t : Subgroup G) = closure ({g, t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure g, Subgroup.zpowers_eq_closure t, ← Subgroup.closure_union]
    congr 1
  have hxV : x ∈ normalizer ((zpowers g ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [hVeq, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact conj_mem_closure_pair x hxg hxt h hh
    · intro hh
      have hk := conj_mem_closure_pair x⁻¹ (by simpa using hxig) (by simpa using hx_it)
        (x * h * x⁻¹) hh
      rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at hk
  have hxt_comm : x * t = t * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hNH (Subgroup.mem_inf.mpr ⟨hx, hxV⟩))
  have hxt' : x * t = g * t * x := by rw [← hxt]; group
  have hgtx : g * t * x = t * x := by rw [← hxt']; exact hxt_comm
  have hgt_eq_t : g * t = t := mul_right_cancel hgtx
  exact hg1 (mul_right_cancel (show g * t = 1 * t by rw [hgt_eq_t, one_mul]))

theorem y6f4a_P_inf_of_not_mem {g t : G} {P L : Subgroup G} (hP : P ≤ L) (hg2 : g ^ 2 = 1)
    (ht2 : t ^ 2 = 1) (hgt : g * t = t * g) (hg : g ∉ L) (ht : t ∉ L) (hgt' : g * t ∉ L) :
    P ⊓ closure ({g, t} : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hxP, hxV⟩ := Subgroup.mem_inf.mp hx
  rcases y6f4a_closure_pair_cases hg2 ht2 hgt hxV with rfl | rfl | rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact absurd (hP hxP) hg
  · exact absurd (hP hxP) ht
  · exact absurd (hP hxP) hgt'

theorem y6f4a_sq_eq_one_of_sylow_exp_two {Γ : Type} [Group Γ] [Finite Γ] {V F : Subgroup Γ}
    (hF : IsSylowIn 2 V F) (hexp : ∀ x ∈ F, x ^ 2 = 1) {p : Γ} (hp : p ∈ V) (hp4 : p ^ 4 = 1) :
    p ^ 2 = 1 := by
  have hFV : F ≤ V := hF.1
  have hF'group : IsPGroup 2 (F.subgroupOf V) :=
    hF.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hFV).symm
  have hF'idx : ¬ 2 ∣ (F.subgroupOf V).index := by
    simpa only [Subgroup.relIndex] using hF.2.2
  let F'' : Sylow 2 ↥V := hF'group.toSylow hF'idx
  let x : ↥V := ⟨p, hp⟩
  have hx4 : x ^ 4 = 1 := Subtype.ext (by simpa [x] using hp4)
  have hdvd : Nat.card (zpowers x) ∣ 2 ^ 2 := by
    rw [Nat.card_zpowers]
    have h : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hx4
    rwa [show (4 : ℕ) = 2 ^ 2 from rfl] at h
  have hzpg : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow hdvd
  obtain ⟨Q, hQle⟩ := hzpg.exists_le_sylow
  have hxQ : x ∈ Q := hQle (Subgroup.mem_zpowers x)
  haveI : Finite (Sylow 2 ↥V) := Sylow.finite_of_finiteIndex F''
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥V) F'' Q
  have hxmem : x ∈ (c • F'' : Sylow 2 ↥V) := by rw [hc]; exact hxQ
  have hmem : x ∈ MulAut.conj c • (F'' : Subgroup ↥V) := by
    rw [← Sylow.coe_subgroup_smul]
    exact hxmem
  obtain ⟨f, hf, hfx⟩ :=
    (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj c) (F'' : Subgroup ↥V)).mp hmem
  have hfF : (f : Γ) ∈ F := by
    exact Subgroup.mem_subgroupOf.mp (show f ∈ F.subgroupOf V from hf)
  have hf2 : f ^ 2 = 1 := Subtype.ext (by simpa using hexp (f : Γ) hfF)
  have hx2 : x ^ 2 = 1 := by
    rw [← hfx]
    have hcf : MulAut.conj c • f = c * f * c⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_apply]
    rw [hcf, pow_two]
    calc (c * f * c⁻¹) * (c * f * c⁻¹) = c * (f * f) * c⁻¹ := by group
      _ = c * 1 * c⁻¹ := by rw [← pow_two, hf2]
      _ = 1 := by group
  have h2 : ((x ^ 2 : ↥V) : Γ) = 1 := congrArg Subtype.val hx2
  simpa [x] using h2

end CFSG.OddStandard.HigherRank.YamadaG23
