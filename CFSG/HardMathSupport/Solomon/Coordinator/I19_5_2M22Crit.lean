module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2Crit
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {M : Type*} [Group M]

theorem conj_apply_eq_mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (k : G) :
    MulAut.conj (α k) = α * MulAut.conj k * α⁻¹ := by
  ext h
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem m22crit_apply_eq_of_commute_conj (N : Subgroup M) (hcenter : Subgroup.center N = ⊥)
    (α : MulAut N) (k : N) (h : α * MulAut.conj k = MulAut.conj k * α) : α k = k := by
  apply conj_injective_of_center N hcenter
  rw [conj_apply_eq_mul_conj_mul_inv, h, mul_inv_cancel_right]

section OneOuter

variable (N : Subgroup M) [Finite N] (δ : M) (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N)
  (hcenter : Subgroup.center N = ⊥) (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
  (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N)
include hδ hδ2 hcenter houter hcard

theorem oneOuter_mul_self_mem_inner (α : MulAut N) : α * α ∈ inner N := by
  by_cases hα : α ∈ inner N
  · exact (inner N).mul_mem hα hα
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  have hu2N : g * δ * (g * δ) ∈ N := by
    have : g * δ * (g * δ) = g * (δ * g * δ⁻¹) * (δ * δ) := by group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  refine ⟨⟨_, hu2N⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  simp only [MulAut.conj_apply, MulAut.mul_apply, Subgroup.coe_mul, Subgroup.coe_inv, hαg]
  group

theorem oneOuter_mem_inner_of_odd {α : MulAut N} {n : ℕ} (hn : Odd n) (hα : α ^ n = 1) :
    α ∈ inner N := by
  obtain ⟨m, rfl⟩ := hn
  have : α = (α * α) ^ (m + 1) := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hα, one_mul]
  rw [this]
  exact (inner N).pow_mem (oneOuter_mul_self_mem_inner N δ hδ hδ2 hcenter houter hcard α) _

theorem oneOuter_exists_involution (α : MulAut N) (hα2 : α * α = 1) (hα : α ∉ inner N) :
    ∃ u : M, δ⁻¹ * u ∈ N ∧ orderOf u = 2 ∧ ∀ h : N, (α h : M) = u * h * u⁻¹ := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  exact ⟨u, hu, orderOf_eq_prime (by rw [sq]; exact hu2) hu1, hαg⟩

theorem isLocallyBalancedAbs_three_two_of_oneOuter
    (hinv : ∀ u ∈ N, orderOf u = 2 → ¬ 9 ∣ Nat.card (centralizerIn N u))
    (hout : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ¬ 9 ∣ Nat.card (centralizerIn N u))
    (hodd : ∀ x : N, Odd (orderOf x) → 3 ∣ orderOf x → orderOf x = 3) :
    IsLocallyBalancedAbs 3 2 N := by
  apply isLocallyBalancedAbs_three_two_of_central
  intro D hD hD9 y hy hcop
  have hinj := conj_injective_of_center N hcenter
  have hfinA : Finite (MulAut N) :=
    Finite.of_injective (fun α : MulAut N => (α : N → N)) DFunLike.coe_injective
  have hDin : D ≤ inner N := fun d hd =>
    oneOuter_mem_inner_of_odd N δ hδ hδ2 hcenter houter hcard (n := 3) ⟨1, rfl⟩ (hD.2 d hd)
  set D₀ := D.comap (MulAut.conj : N →* MulAut N) with hD₀
  have hD₀card : Nat.card D₀ = 9 := by
    have hmap : D₀.map (MulAut.conj : N →* MulAut N) = D := by
      rw [hD₀, Subgroup.map_comap_eq,
        (inf_eq_right (a := (MulAut.conj : N →* MulAut N).range)).2 hDin]
    rw [← hD9, ← hmap, Subgroup.card_map_of_injective hinj]
  have hfix : ∀ z ∈ Subgroup.centralizer (D : Set (MulAut N)), D₀ ≤ fixSub z := by
    intro z hz k hk
    exact m22crit_apply_eq_of_commute_conj N hcenter z k
      (Subgroup.mem_centralizer_iff.1 hz _ hk).symm
  by_contra hy1
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hn1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  rcases Nat.even_or_odd (orderOf y) with heven | hodd'
  ·
    set z := y ^ (orderOf y / 2) with hz
    have hz2 : orderOf z = 2 := orderOf_pow_orderOf_div hn0 (even_iff_two_dvd.1 heven)
    have hzc : z ∈ Subgroup.centralizer (D : Set (MulAut N)) := Subgroup.pow_mem _ hy _
    have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
    obtain ⟨u, hzu, h9⟩ : ∃ u : M, (∀ h : N, (z h : M) = u * h * u⁻¹) ∧
        ¬ 9 ∣ Nat.card (centralizerIn N u) := by
      by_cases hzi : z ∈ inner N
      · obtain ⟨u₀, hu₀⟩ := hzi
        have ho : orderOf (u₀ : M) = 2 := by
          rw [Subgroup.orderOf_coe, ← orderOf_injective _ hinj u₀]
          exact (congrArg orderOf hu₀).trans hz2
        refine ⟨u₀, fun h => ?_, hinv _ u₀.2 ho⟩
        rw [← hu₀]
        rfl
      · obtain ⟨u, hu, hu2, hzu⟩ :=
          oneOuter_exists_involution N δ hδ hδ2 hcenter houter hcard z hzz hzi
        exact ⟨u, hzu, hout u hu hu2⟩
    apply h9
    rw [← map_fixSub_conjOn N z u hzu, Subgroup.card_map_of_injective N.subtype_injective,
      ← hD₀card]
    exact Subgroup.card_dvd_of_le (hfix z hzc)
  ·
    obtain ⟨g, rfl⟩ := oneOuter_mem_inner_of_odd N δ hδ hδ2 hcenter houter hcard hodd'
      (pow_orderOf_eq_one y)
    have hg : orderOf (MulAut.conj g) = orderOf g := orderOf_injective _ hinj g
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ D₀, k ≠ 1 := by
      by_contra hall
      push Not at hall
      have : Nat.card D₀ = 1 := Subgroup.card_eq_one.2 (Subgroup.eq_bot_iff_forall _ |>.2 hall)
      rw [hD₀card] at this
      norm_num at this
    have hk3 : k ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hD.2 _ hk)
    have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
    have hcomm : Commute g k := by
      have h1 : MulAut.conj g k = k := hfix _ hy hk
      rw [MulAut.conj_apply] at h1
      calc g * k = g * k * g⁻¹ * g := by group
        _ = k * g := by rw [h1]
    have hmul : orderOf (g * k) = orderOf g * 3 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hko, ← hg]; exact hcop.symm), hko]
    have h3 := hodd (g * k) (by rw [hmul, ← hg]; exact hodd'.mul ⟨1, rfl⟩)
      (by rw [hmul]; exact dvd_mul_left 3 _)
    rw [hmul] at h3
    rw [hg] at hn1
    omega

end OneOuter

end CFSG.HardMathSupport.Solomon.Coordinator
