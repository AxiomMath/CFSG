module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameFacts

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.HarrisU33.K28

open scoped Pointwise

private theorem mulAut_conj_conj {G : Type*} [Group G] (α : MulAut G) (x : G) :
    MulAut.conj α (MulAut.conj x) = MulAut.conj (α x) := by
  ext z
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

private theorem WreathRel.exists_zpow_mul_of_mem_baseGrp {G : Type*} [Group G]
    {x₁ x₂ lam : G} (h : WreathRel x₁ x₂ lam) {w : G} (hw : w ∈ baseGrp x₁ x₂) :
    ∃ a b : ℤ, w = x₁ ^ a * x₂ ^ b := by
  have hcomm : Commute x₁ x₂ := h.comm
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, b, rfl⟩ := ihx
    obtain ⟨c, d, rfl⟩ := ihy
    refine ⟨a + c, b + d, ?_⟩
    have hc : Commute (x₂ ^ b) (x₁ ^ c) := (hcomm.zpow_zpow c b).symm
    calc x₁ ^ a * x₂ ^ b * (x₁ ^ c * x₂ ^ d)
        = x₁ ^ a * (x₂ ^ b * x₁ ^ c) * x₂ ^ d := by group
      _ = x₁ ^ a * (x₁ ^ c * x₂ ^ b) * x₂ ^ d := by rw [hc.eq]
      _ = x₁ ^ (a + c) * x₂ ^ (b + d) := by rw [zpow_add, zpow_add]; group
  | inv x _ ih =>
    obtain ⟨a, b, rfl⟩ := ih
    refine ⟨-a, -b, ?_⟩
    calc (x₁ ^ a * x₂ ^ b)⁻¹ = (x₂ ^ b)⁻¹ * (x₁ ^ a)⁻¹ := mul_inv_rev _ _
      _ = x₂ ^ (-b) * x₁ ^ (-a) := by rw [zpow_neg, zpow_neg]
      _ = x₁ ^ (-a) * x₂ ^ (-b) := (hcomm.zpow_zpow (-a) (-b)).eq.symm

private theorem exists_fin_four_of_zpow {G : Type*} [Group G] {x : G} (hx : orderOf x = 4)
    (a : ℤ) : ∃ a' : Fin 4, x ^ a = x ^ a'.val := by
  have h1 : 0 ≤ a % 4 := Int.emod_nonneg a (by norm_num)
  have h2 : a % 4 < 4 := Int.emod_lt_of_pos a (by norm_num)
  refine ⟨⟨(a % 4).toNat, (Int.toNat_lt h1).2 h2⟩, ?_⟩
  rw [← zpow_mod_orderOf x a, hx]
  rw [← zpow_natCast x ((a % 4).toNat), Int.toNat_of_nonneg h1]
  rfl

private theorem WreathRel.exists_pow_pow_of_mem_baseGrp {G : Type*} [Group G]
    {x₁ x₂ lam : G} (h : WreathRel x₁ x₂ lam) {w : G} (hw : w ∈ baseGrp x₁ x₂) :
    ∃ a b : Fin 4, w = x₁ ^ a.val * x₂ ^ b.val := by
  obtain ⟨i, j, hij⟩ := h.exists_zpow_mul_of_mem_baseGrp hw
  obtain ⟨a, ha⟩ := exists_fin_four_of_zpow h.ord_x₁ i
  obtain ⟨b, hb⟩ := exists_fin_four_of_zpow h.ord_x₂ j
  exact ⟨a, b, by rw [hij, ha, hb]⟩

section KLevel

variable
  {K : Type} [Group K]

variable {x₁ x₂ lam rho : K} {α : MulAut K}

theorem frame_of_model (m : Model28 K) :
    ∃ (x₁ x₂ lam rho : K) (α : MulAut K),
      x₁ = m.e.symm ⟨fx₁, fx₁_mem⟩ ∧ x₂ = m.e.symm ⟨fx₂, fx₂_mem⟩ ∧
      lam = m.e.symm ⟨flam, flam_mem⟩ ∧ rho = m.e.symm ⟨frho, frho_mem⟩ ∧
      α = m.Φ.symm ⟨ftau, ftau_mem_A⟩ ∧ U33Frame x₁ x₂ lam rho α := by
  let x₁ : K := m.e.symm ⟨fx₁, fx₁_mem⟩
  let x₂ : K := m.e.symm ⟨fx₂, fx₂_mem⟩
  let lam : K := m.e.symm ⟨flam, flam_mem⟩
  let rho : K := m.e.symm ⟨frho, frho_mem⟩
  let α : MulAut K := m.Φ.symm ⟨ftau, ftau_mem_A⟩
  have hx₁ : m.ε x₁ = fx₁ := by simp [Model28.ε, x₁]
  have hx₂ : m.ε x₂ = fx₂ := by simp [Model28.ε, x₂]
  have hlam : m.ε lam = flam := by simp [Model28.ε, lam]
  have hrho : m.ε rho = frho := by simp [Model28.ε, rho]
  have hα : m.ι α = ftau := by simp [Model28.ι, α]
  have hwr : WreathRel x₁ x₂ lam := by
    refine WreathRel.of_injective m.ε m.ε_injective ?_
    rw [hx₁, hx₂, hlam]
    exact wreathRel_frame
  refine ⟨x₁, x₂, lam, rho, α, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine
    { wreath := hwr
      ord_rho := ?_
      rho_x₁ := ?_
      rho_x₂ := ?_
      lam_rho := ?_
      cent_rho := ?_
      alpha_sq := ?_
      alpha_x₁ := ?_
      alpha_x₂ := ?_
      alpha_lam := ?_
      alpha_rho := ?_
      alpha_outer := ?_ }
  · rw [← orderOf_injective m.ε m.ε_injective rho, hrho]
    exact frho_ord
  · apply m.ε_injective
    simpa only [map_mul, map_inv, hrho, hx₁, hx₂] using frho_x₁
  · apply m.ε_injective
    simpa only [map_mul, map_inv, hrho, hx₁, hx₂] using frho_x₂
  · apply m.ε_injective
    simpa only [map_mul, map_inv, hlam, hrho] using flam_frho
  · intro w hw hcomm
    obtain ⟨a, b, rfl⟩ := hwr.exists_pow_pow_of_mem_baseGrp hw
    have hmap : frho * (fx₁ ^ a.val * fx₂ ^ b.val)
        = (fx₁ ^ a.val * fx₂ ^ b.val) * frho := by
      have := congrArg m.ε hcomm
      simpa only [map_mul, map_pow, hx₁, hx₂, hrho] using this
    obtain ⟨ha, hb⟩ := frho_cent_base a b hmap
    rw [ha, hb]
    simp
  · apply m.ι_injective
    rw [map_mul, map_one, hα, ← pow_two, ftau_pow.1]
  · apply m.ε_injective
    rw [Model28.ε_apply, hα, hx₁, map_inv, hx₁, ftau_x₁]
  · apply m.ε_injective
    rw [Model28.ε_apply, hα, hx₂, map_inv, hx₂, ftau_x₂]
  · apply m.ε_injective
    rw [Model28.ε_apply, hα, hlam]
    rw [show ftau * flam * ftau⁻¹ = flam by rw [← ftau_flam]; group]
  · apply m.ε_injective
    rw [Model28.ε_apply, hα, hrho]
    rw [show ftau * frho * ftau⁻¹ = frho by rw [ftau_frho]; group]
  · intro k hk
    have h1 : m.ι α = m.ι (MulAut.conj k) := by rw [hk]
    rw [hα, Model28.ι_conj] at h1
    exact ftau_not_mem_P (h1.symm ▸ m.ε_mem k)

theorem exists_frame_of_psu33 (h : LieModel K .PSU 3 3 1) :
    ∃ (x₁ x₂ lam rho : K) (α : MulAut K), U33Frame x₁ x₂ lam rho α := by
  obtain ⟨m⟩ := exists_model28 h
  obtain ⟨x₁, x₂, lam, rho, α, -, -, -, -, -, hf⟩ := frame_of_model m
  exact ⟨x₁, x₂, lam, rho, α, hf⟩

theorem U33Frame.m12 (h : LieModel K .PSU 3 3 1) (hf : U33Frame x₁ x₂ lam rho α) :
    M12Rel (MulAut.conj x₁) (MulAut.conj x₂) (MulAut.conj lam) α := by
  have hα1 : α ≠ 1 := by
    intro h1
    exact hf.alpha_outer 1 (h1.trans (map_one (MulAut.conj : K →* MulAut K)).symm)
  have hα2 : α ^ 2 = 1 := by rw [pow_two]; exact hf.alpha_sq
  refine
    { toWreathRel := WreathRel.map' (MulAut.conj : K →* MulAut K)
        (conj_injective_of_psu33 h) hf.wreath
      ord_tau := orderOf_eq_prime hα2 hα1
      comm_lam_tau := ?_
      tau_x₁ := ?_
      tau_x₂ := ?_ }
  · have h2 : α * MulAut.conj lam * α⁻¹ = MulAut.conj lam := by
      rw [show α * MulAut.conj lam * α⁻¹ = MulAut.conj (α lam) from
          mulAut_conj_conj α lam, hf.alpha_lam]
    calc MulAut.conj lam * α = (α * MulAut.conj lam * α⁻¹) * α := by
          conv_lhs => rw [← h2]
      _ = α * MulAut.conj lam := by group
  · calc α * MulAut.conj x₁ * α⁻¹ = MulAut.conj (α x₁) := mulAut_conj_conj α x₁
      _ = MulAut.conj x₁⁻¹ := by rw [hf.alpha_x₁]
      _ = (MulAut.conj x₁)⁻¹ := map_inv (MulAut.conj : K →* MulAut K) x₁
  · calc α * MulAut.conj x₂ * α⁻¹ = MulAut.conj (α x₂) := mulAut_conj_conj α x₂
      _ = MulAut.conj x₂⁻¹ := by rw [hf.alpha_x₂]
      _ = (MulAut.conj x₂)⁻¹ := map_inv (MulAut.conj : K →* MulAut K) x₂

theorem U33Frame.card_wreathGrp (hf : U33Frame x₁ x₂ lam rho α) :
    Nat.card (wreathGrp x₁ x₂ lam) = 32 :=
  hf.wreath.card_wreathGrp

end KLevel

end CFSG.OddStandard.SmallF3.HarrisU33
