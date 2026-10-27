module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheck
public import CFSG.RankThree.PartOne.U5K.Hyp.Irred
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem mat_four_three {g : SU52} (hg : g ∈ Ssub) : mat g 4 3 = bar (mat g 1 0) := by
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, -, -, -⟩ :=
    exists_eq_nf_coord hg
  rw [k₂, mat_mul, mat_mul, mat_mul, e₁, e₂, e₃, e₄]
  simp [x₁Mat, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem mem_A₂sub_iff_ρ {g : SU52} :
    g ∈ A₂sub ↔ ρ g ∈ CFSG.RankThree.PartOne.U5K.Hyp.Ssub hF4 := by
  rw [mem_A₂sub]
  constructor
  · rintro ⟨hgS, h0⟩
    have hU := mem_Ssub_iff_ρ.1 hgS
    refine (CFSG.RankThree.PartOne.U5K.Hyp.mem_Ssub_iff hU).2 ?_
    change CFSG.RankThree.PartOne.U5K.Hyp.mat (ρ g) (yIdx 4) (yIdx 3) = 0
    rw [mat_ρ_apply, mat_four_three hgS, h0, map_zero]
  · intro h
    have hU := CFSG.RankThree.PartOne.U5K.Hyp.Ssub_le_Usub h
    have hgS := mem_Ssub_iff_ρ.2 hU
    have h0 := (CFSG.RankThree.PartOne.U5K.Hyp.mem_Ssub_iff hU).1 h
    change CFSG.RankThree.PartOne.U5K.Hyp.mat (ρ g) (yIdx 4) (yIdx 3) = 0 at h0
    rw [mat_ρ_apply, mat_four_three hgS] at h0
    refine ⟨hgS, ?_⟩
    rw [← bar_bar (mat g 1 0), h0, map_zero]

theorem A₂sub_eq_comap_Ssub :
    A₂sub = (CFSG.RankThree.PartOne.U5K.Hyp.Ssub hF4).comap ρ.toMonoidHom := by
  ext g
  exact mem_A₂sub_iff_ρ

theorem Fsub_comm_A₂ {a z : SU52} (ha : a ∈ A₂sub) (hz : z ∈ Fsub) : a * z = z * a := by
  rw [mem_A₂sub_iff_ρ] at ha
  rw [Fsub_eq_comap_Vsub] at hz
  exact ρ.injective (by
    rw [map_mul, map_mul]
    exact (CFSG.RankThree.PartOne.U5K.Hyp.commute_Vsub_iff
      (CFSG.RankThree.PartOne.U5K.Hyp.Ssub_le_Usub ha)).2 ha _ hz)

theorem mem_Fsub_of_central {z : SU52} (hz : z ∈ A₂sub) (h : ∀ a ∈ A₂sub, a * z = z * a) :
    z ∈ Fsub := by
  rw [mem_A₂sub_iff_ρ] at hz
  rw [Fsub_eq_comap_Vsub]
  refine (CFSG.RankThree.PartOne.U5K.Hyp.central_Ssub_iff hz).1 fun s hs => ?_
  have hs' : ρ.symm s ∈ A₂sub := by rw [mem_A₂sub_iff_ρ, MulEquiv.apply_symm_apply]; exact hs
  have := congrArg ρ (h _ hs')
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem mem_A₂sub_of_comm_Fsub {s : SU52} (hs : s ∈ Ssub) (h : ∀ z ∈ Fsub, s * z = z * s) :
    s ∈ A₂sub := by
  rw [mem_A₂sub_iff_ρ]
  refine (CFSG.RankThree.PartOne.U5K.Hyp.commute_Vsub_iff (mem_Ssub_iff_ρ.1 hs)).1 fun v hv => ?_
  have hv' : ρ.symm v ∈ Fsub := by
    rw [Fsub_eq_comap_Vsub, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact hv
  have := congrArg ρ (h _ hv')
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem mul_self_mem_Fsub {a : SU52} (ha : a ∈ A₂sub) : a * a ∈ Fsub := by
  rw [mem_A₂sub_iff_ρ] at ha
  obtain ⟨-, x, C, hxC⟩ := ha
  rw [Fsub_eq_comap_Vsub, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul]
  exact CFSG.RankThree.PartOne.U5K.Hyp.mem_Vsub_of_mat
    (Y := Matrix.vecMulVec x fun j => hF4.bar (x j)) (by
      rw [CFSG.RankThree.PartOne.U5K.Hyp.mat_mul, hxC,
        CFSG.RankThree.PartOne.U5K.Hyp.oddUni_mul_self])

theorem commutator_mem_Fsub {a b : SU52} (ha : a ∈ A₂sub) (hb : b ∈ A₂sub) :
    ⁅a, b⁆ ∈ Fsub := by
  rw [mem_A₂sub_iff_ρ] at ha hb
  obtain ⟨-, x, C, hxC⟩ := ha
  obtain ⟨-, y, C', hyC⟩ := hb
  rw [Fsub_eq_comap_Vsub, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, commutatorElement_def,
    map_mul, map_mul, map_mul, map_inv, map_inv]
  exact CFSG.RankThree.PartOne.U5K.Hyp.mem_Vsub_of_mat
    (CFSG.RankThree.PartOne.U5K.Hyp.comm_Ssub hxC hyC)

theorem omega_omega_rel : F4.ω * bar F4.ω = F4.ω + bar F4.ω := by
  simp only [bar_apply]
  decide

theorem X₁sub_le_A₂sub : X₁sub ≤ A₂sub := le_sup_left.trans le_sup_left

theorem X₄sub_le_A₂sub : X₄sub ≤ A₂sub := le_sup_right

theorem commutator_x₁_x₁_eq :
    ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₁SU F4.ω F4.ω omega_omega_rel)⁻¹⁆ =
      x₁SU 0 1 zero_one_rel := by
  refine ext_mat ?_
  rw [commutatorElement_def, inv_inv, inv_inv, mat_mul, mat_mul, mat_mul,
    mat_inv_of_x₁ (mat_x₁SU _ _ _), mat_inv_of_x₁ (mat_x₁SU _ _ _), mat_x₁SU, mat_x₁SU, mat_x₁SU,
    x₁Mat_mul, x₁Mat_mul, x₁Mat_mul]
  simp only [bar_apply]
  congr 1

theorem commutator_x₄_x₄_eq :
    ⁅(x₄SU 1 F4.ω one_omega_rel)⁻¹, (x₄SU F4.ω F4.ω omega_omega_rel)⁻¹⁆ =
      x₄SU 0 1 zero_one_rel := by
  refine ext_mat ?_
  rw [commutatorElement_def, inv_inv, inv_inv, mat_mul, mat_mul, mat_mul,
    mat_inv_of_x₄ (mat_x₄SU _ _ _), mat_inv_of_x₄ (mat_x₄SU _ _ _), mat_x₄SU, mat_x₄SU, mat_x₄SU,
    x₄Mat_mul, x₄Mat_mul, x₄Mat_mul]
  simp only [bar_apply]
  congr 1

theorem commutator_x₁_x₄ω_eq :
    ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₄SU F4.ω F4.ω omega_omega_rel)⁻¹⁆ = x₃SU F4.ω := by
  refine ext_mat ?_
  have h := commutator_x₁_x₄ (mat_x₁SU 1 F4.ω one_omega_rel) (mat_x₄SU F4.ω F4.ω omega_omega_rel)
  rw [show bar (1 : F4) * F4.ω = F4.ω by rw [map_one, one_mul]] at h
  rw [commutatorElement_def, inv_inv, inv_inv, h, mat_x₃SU]

theorem exists_genFSU_eq_commutator (j : Fin 4) :
    ∃ a ∈ A₂sub, ∃ b ∈ A₂sub, genFSU j = ⁅a, b⁆ := by
  have h1 : (x₁SU 1 F4.ω one_omega_rel)⁻¹ ∈ A₂sub := inv_mem (X₁sub_le_A₂sub (x₁SU_mem _ _ _))
  fin_cases j
  · exact ⟨_, h1, _, inv_mem (X₁sub_le_A₂sub (x₁SU_mem _ _ _)), commutator_x₁_x₁_eq.symm⟩
  · exact ⟨_, h1, _, inv_mem (X₄sub_le_A₂sub (x₄SU_mem _ _ _)), commutator_x₁_x₄_eq.symm⟩
  · exact ⟨_, h1, _, inv_mem (X₄sub_le_A₂sub (x₄SU_mem _ _ _)), commutator_x₁_x₄ω_eq.symm⟩
  · exact ⟨_, inv_mem (X₄sub_le_A₂sub (x₄SU_mem _ _ _)), _,
      inv_mem (X₄sub_le_A₂sub (x₄SU_mem _ _ _)), commutator_x₄_x₄_eq.symm⟩

@[expose] def DiagSub : Subgroup SU52 where
  carrier := {g | ∃ a b c : F4, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ mat g = Matrix.diagonal ![a, b, c, b, a]}
  mul_mem' := by
    rintro g g' ⟨a, b, c, ha, hb, hc, hg⟩ ⟨a', b', c', ha', hb', hc', hg'⟩
    refine ⟨a * a', b * b', c * c', mul_ne_zero ha ha', mul_ne_zero hb hb', mul_ne_zero hc hc', ?_⟩
    rw [mat_mul, hg, hg', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> rfl
  one_mem' := ⟨1, 1, 1, one_ne_zero, one_ne_zero, one_ne_zero, by
    rw [mat_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl⟩
  inv_mem' := by
    rintro g ⟨a, b, c, ha, hb, hc, hg⟩
    refine ⟨a⁻¹, b⁻¹, c⁻¹, inv_ne_zero ha, inv_ne_zero hb, inv_ne_zero hc, mat_inv_eq ?_⟩
    rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [ha, hb, hc]

theorem Esub_le_DiagSub : Esub ≤ DiagSub := by
  refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
  · exact ⟨1, F4.ω, F4.ω, one_ne_zero, by decide, by decide, by rw [mat_e₁SU, e₁Mat]⟩
  · exact ⟨F4.ω, F4.ω, bar F4.ω, by decide, by decide, by rw [bar_apply]; decide, by
      rw [mat_e₂SU, e₂Mat]⟩

theorem mat_conj_diag {g x : SU52} {d : Fin 5 → F4} (hd : ∀ i, d i ≠ 0)
    (hg : mat g = Matrix.diagonal d) (i j : Fin 5) :
    mat (g * x * g⁻¹) i j = d i * mat x i j * (d j)⁻¹ := by
  have hinv : mat g⁻¹ = Matrix.diagonal fun i => (d i)⁻¹ := mat_inv_eq (by
    rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i))
  rw [mat_mul, mat_mul, hg, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem DiagSub_conj_mem_A₂sub {g a : SU52} (hg : g ∈ DiagSub) (ha : a ∈ A₂sub) :
    g * a * g⁻¹ ∈ A₂sub := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hgm⟩ := hg
  have hd : ∀ i, (![α, β, γ, β, α] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simpa
  obtain ⟨haS, ha0⟩ := mem_A₂sub.1 ha
  obtain ⟨h1, h2⟩ := mem_Ssub.1 haS
  refine mem_A₂sub.2 ⟨mem_Ssub.2 ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · rw [mat_conj_diag hd hgm, h1 i j hij, mul_zero, zero_mul]
  · rw [mat_conj_diag hd hgm, h2 i, mul_one, mul_inv_cancel₀ (hd i)]
  · rw [mat_conj_diag hd hgm, ha0, mul_zero, zero_mul]

theorem x₁_x₄_mem_A₂sub :
    x₁SU 1 F4.ω one_omega_rel ∈ A₂sub ∧ x₄SU 1 F4.ω one_omega_rel ∈ A₂sub :=
  ⟨X₁sub_le_A₂sub (x₁SU_mem _ _ _), X₄sub_le_A₂sub (x₄SU_mem _ _ _)⟩

theorem F4_eq_one_of_add_one : ∀ x : F4, x + 1 = 0 → x = 1 := by decide

theorem eq_one_of_conj_mul_inv_mem_Fsub {g : SU52} (hg : g ∈ DiagSub)
    (h : ∀ a ∈ A₂sub, g * a * g⁻¹ * a⁻¹ ∈ Fsub) : g = 1 := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hgm⟩ := hg
  have hd : ∀ i, (![α, β, γ, β, α] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simpa
  have hS : ∀ a ∈ A₂sub, g * a * g⁻¹ ∈ Ssub := fun a ha =>
    A₂sub_le_Ssub (DiagSub_conj_mem_A₂sub ⟨α, β, γ, hα, hβ, hγ, hgm⟩ ha)
  have hγβ : γ = β := by
    have hx := x₁_x₄_mem_A₂sub.1
    have hxS : (x₁SU 1 F4.ω one_omega_rel)⁻¹ ∈ Ssub := A₂sub_le_Ssub (inv_mem hx)
    have h21 := (mem_Fsub.1 (h _ hx)).2.1
    rw [mat_mul_two_one (hS _ hx) hxS, mat_conj_diag hd hgm,
      mat_inv_of_x₁ (mat_x₁SU _ _ _), mat_x₁SU] at h21
    change γ * 1 * β⁻¹ + 1 = 0 at h21
    have e := F4_eq_one_of_add_one _ h21
    rw [mul_one, mul_inv_eq_one₀ hβ] at e
    exact e
  have hγα : γ = α := by
    have hx := x₁_x₄_mem_A₂sub.2
    have hxS : (x₄SU 1 F4.ω one_omega_rel)⁻¹ ∈ Ssub := A₂sub_le_Ssub (inv_mem hx)
    have h20 := (mem_Fsub.1 (h _ hx)).2.2.2
    rw [mat_mul_two_zero (hS _ hx) hxS, mat_conj_diag hd hgm, mat_conj_diag hd hgm,
      mat_inv_of_x₄ (mat_x₄SU _ _ _), mat_x₄SU] at h20
    change γ * 1 * α⁻¹ + γ * 0 * β⁻¹ * 0 + 1 = 0 at h20
    simp only [mul_zero, zero_mul, add_zero] at h20
    have e := F4_eq_one_of_add_one _ h20
    rw [mul_one, mul_inv_eq_one₀ hα] at e
    exact e
  obtain rfl : β = α := hγβ.symm.trans hγα
  obtain rfl : γ = β := hγβ
  have hdet := (mem_SU52.1 g.2).2
  change (mat g).det = 1 at hdet
  rw [hgm, Matrix.det_diagonal, Fin.prod_univ_five] at hdet
  change γ * γ * γ * γ * γ = 1 at hdet
  have h1 : γ = 1 := F4_eq_one_of_pow_five γ (by rw [← hdet]; ring)
  subst h1
  refine ext_mat ?_
  rw [hgm, mat_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

@[expose] def Diag0Sub : Subgroup SU52 where
  carrier := {g | ∃ a c : F4, a ≠ 0 ∧ c ≠ 0 ∧ mat g = Matrix.diagonal ![a, a, c, a, a]}
  mul_mem' := by
    rintro g g' ⟨a, c, ha, hc, hg⟩ ⟨a', c', ha', hc', hg'⟩
    refine ⟨a * a', c * c', mul_ne_zero ha ha', mul_ne_zero hc hc', ?_⟩
    rw [mat_mul, hg, hg', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> rfl
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, by
    rw [mat_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl⟩
  inv_mem' := by
    rintro g ⟨a, c, ha, hc, hg⟩
    refine ⟨a⁻¹, c⁻¹, inv_ne_zero ha, inv_ne_zero hc, mat_inv_eq ?_⟩
    rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [ha, hc]

theorem zpowers_e₁_inf_zpowers_e₂ : zpowers e₁SU ⊓ zpowers e₂SU = ⊥ := by
  have he₂ : zpowers e₂SU ≤ Diag0Sub := zpowers_le.2
    ⟨F4.ω, bar F4.ω, by decide, by rw [bar_apply]; decide, by rw [mat_e₂SU, e₂Mat]⟩
  have he₁ : e₁SU ∉ zpowers e₂SU := fun h => by
    obtain ⟨a, c, -, -, hm⟩ := he₂ h
    have h0 := congrFun (congrFun hm 0) 0
    have h1 := congrFun (congrFun hm 1) 1
    rw [mat_e₁SU] at h0 h1
    change (1 : F4) = a at h0
    change F4.ω = a at h1
    exact absurd (h0.trans h1.symm) (by decide)
  have hdvd : Nat.card (zpowers e₁SU ⊓ zpowers e₂SU : Subgroup SU52) ∣ 3 := by
    rw [← orderOf_e₁SU, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    have hle : zpowers e₁SU ≤ zpowers e₂SU := by
      have heq : zpowers e₁SU ⊓ zpowers e₂SU = zpowers e₁SU :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, orderOf_e₁SU])
      rw [← heq]
      exact inf_le_right
    exact he₁ (hle (mem_zpowers _))

theorem card_Esub : Nat.card Esub = 9 := by
  obtain ⟨h, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers e₁SU)
    (zpowers e₂SU) fun x hx y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hy
      exact ((Commute.zpow_zpow (e₁SU_mul_e₂SU : Commute e₁SU e₂SU)) k l).eq
  rw [zpowers_e₁_inf_zpowers_e₂, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_e₁SU, orderOf_e₂SU] at h
  rw [Esub, h]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
