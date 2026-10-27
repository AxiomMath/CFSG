module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem EF_le_E : fr.EF ≤ fr.E := by rw [fr.EF_eq]; exact inf_le_left

theorem EF_le_F : fr.EF ≤ fr.F := by rw [fr.EF_eq]; exact inf_le_right

theorem exists_P₁_mul_EF {e : G} (he : e ∈ fr.E) : ∃ p ∈ fr.P₁, ∃ f ∈ fr.EF, p * f = e := by
  have hle : fr.P₁ ≤ normalizer (fr.EF : Set G) :=
    le_normalizer_of_comm fr.E_comm P₁_le_E EF_le_E
  have : Finite fr.E := Nat.finite_of_card_ne_zero (by rw [fr.card_E]; norm_num)
  have hsup : fr.P₁ ⊔ fr.EF = fr.E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le P₁_le_E EF_le_E) ?_
    have h := card_sup_mul_card_inf hle
    have hbot : fr.P₁ ⊓ fr.EF = ⊥ :=
      le_bot_iff.mp (fr.P₁_inf_F ▸ inf_le_inf_left _ EF_le_F)
    rw [hbot, Subgroup.card_bot, mul_one, card_P₁, fr.card_EF] at h
    rw [h, fr.card_E]
  exact exists_mul_of_mem_sup hle (hsup ▸ he)

theorem z_mem_of_even [Finite G] {B : Subgroup G} (hBF : B ≤ fr.F) (heven : Even (Nat.card B)) :
    z ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 (even_iff_two_dvd.mp heven)
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  rw [← fr.eq_z_of_mem_F y (hBF y.2) hy']
  exact y.2

theorem M_inf_centralizer_of_mem_EF [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {f₀ : G} (hf : f₀ ∈ fr.EF) (hf1 : f₀ ≠ 1) :
    fr.M ⊓ centralizer ({f₀} : Set G) = fr.ZN := by
  have hfE : f₀ ∈ fr.E := EF_le_E hf
  have hfF : f₀ ∈ fr.F := EF_le_F hf
  have hle : fr.ZN ≤ fr.M ⊓ centralizer ({f₀} : Set G) := fun x hx =>
    ⟨ZN_le_M p10 hx, mem_centralizer_singleton_iff.mpr (comm_of_mem_ZN hx (E_le_N hfE)).symm⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_ZN p7 p10 hz]
  have hdvd : Nat.card (fr.M ⊓ centralizer ({f₀} : Set G) : Subgroup G) ∣ 3 ^ 5 :=
    p10.card_M ▸ Subgroup.card_dvd_of_le inf_le_left
  have h27 : 27 ≤ Nat.card (fr.M ⊓ centralizer ({f₀} : Set G) : Subgroup G) :=
    card_ZN p7 p10 hz ▸ Subgroup.card_le_of_le hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hk'] at h27 ⊢
  interval_cases k
  · norm_num at h27
  · norm_num at h27
  · norm_num at h27
  · norm_num
  ·
    exfalso
    set A := fr.M ⊓ centralizer ({f₀} : Set G) with hA
    have hord : orderOf f₀ = 3 := orderOf_eq_prime (fr.E_pow_three f₀ hfE) hf1
    obtain ⟨g, hgF, heven⟩ := fr.exists_even_card f₀ hfF hord
    set B := closure ({f₀, g * f₀ * g⁻¹} : Set G) with hB
    have hBF : B ≤ fr.F := by
      rw [hB, closure_le]
      rintro _ (rfl | rfl)
      · exact hfF
      · exact mul_mem (mul_mem hgF hfF) (inv_mem hgF)
    have hzB : z ∈ B := z_mem_of_even hBF heven
    have hgM : g ∈ normalizer (fr.M : Set G) := F_le_normalizer_M hgF
    set A' := fr.M ⊓ centralizer ({g * f₀ * g⁻¹} : Set G) with hA'
    have hA'card : Nat.card A' = 3 ^ 4 := by
      rw [hA', ← map_conj_inf_centralizer hgM f₀,
        Subgroup.card_map_of_injective (MulAut.conj g).injective, ← hA, hk']
    have hAA' := card_sup_mul_card_inf (X := A) (Y := A')
      (le_normalizer_of_comm p10.M_comm inf_le_left inf_le_left)
    rw [hk', hA'card] at hAA'
    have hsup : Nat.card (A ⊔ A' : Subgroup G) ≤ 3 ^ 5 :=
      p10.card_M ▸ Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
    have hinf : 27 ≤ Nat.card (A ⊓ A' : Subgroup G) := by
      have h1 : 3 ^ 5 * 27 ≤ 3 ^ 5 * Nat.card (A ⊓ A' : Subgroup G) := by
        calc 3 ^ 5 * 27 = 3 ^ 4 * 3 ^ 4 := by norm_num
          _ = Nat.card (A ⊔ A' : Subgroup G) * Nat.card (A ⊓ A' : Subgroup G) := hAA'.symm
          _ ≤ 3 ^ 5 * Nat.card (A ⊓ A' : Subgroup G) := Nat.mul_le_mul_right _ hsup
      exact Nat.le_of_mul_le_mul_left h1 (by norm_num)
    have hP : A ⊓ A' ≤ fr.P₁ := by
      rw [← p10.M_inf_centralizer_z]
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      have hxB : x ∈ centralizer (B : Set G) := by
        rw [hB, centralizer_closure]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro _ (rfl | rfl)
        · exact (mem_centralizer_singleton_iff.mp hx.1.2).symm
        · exact (mem_centralizer_singleton_iff.mp hx.2.2).symm
      exact mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxB z hzB).symm
    have h3 := Subgroup.card_le_of_le hP
    rw [card_P₁] at h3
    omega
  ·
    exfalso
    have heq : fr.M ⊓ centralizer ({f₀} : Set G) = fr.M :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', p10.card_M])
    have hfM : f₀ ∈ fr.M := by
      rw [← p10.centralizer_M]
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun m hm => ?_, fr.F_le_centralizer hfF⟩
      exact mem_centralizer_singleton_iff.mp (heq.symm ▸ hm : m ∈ fr.M ⊓ _).2
    have h1 : f₀ ∈ fr.M ⊓ fr.F := ⟨hfM, hfF⟩
    rw [p10.M_inf_F, Subgroup.mem_bot] at h1
    exact hf1 h1

theorem M_inf_centralizer [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) :
    ∀ x ∈ fr.N, x ∉ fr.M → fr.M ⊓ centralizer ({x} : Set G) = fr.ZN := by
  intro x hx hxM
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_N hx
  obtain ⟨p, hp, f₀, hf₀, rfl⟩ := exists_P₁_mul_EF he
  have hpM : p ∈ fr.M := p10.P₁_le_M hp
  have hf1 : f₀ ≠ 1 := fun h => hxM (by rw [h, mul_one]; exact mul_mem hpM hm)
  rw [← M_inf_centralizer_of_mem_EF p7 p10 hz hf₀ hf1]
  ext y
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun hy => ?_
  have hyp : Commute y p := p10.M_comm y hy p hpM
  have hym : Commute y m := p10.M_comm y hy m hm
  constructor
  · intro h
    have h' : Commute y (p⁻¹ * (p * f₀ * m) * m⁻¹) :=
      (hyp.inv_right.mul_right h).mul_right hym.inv_right
    rwa [show p⁻¹ * (p * f₀ * m) * m⁻¹ = f₀ by group] at h'
  · intro h
    exact (hyp.mul_right h).mul_right hym

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
