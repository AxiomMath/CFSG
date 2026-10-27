module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameExtras

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem cent_fourGrp_of_ctx0 (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ k ∈ L, k * x₁ ^ 2 = x₁ ^ 2 * k → k * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * k →
      k ∈ baseGrp x₁ x₂ := by
  obtain ⟨hx₁L, hx₂L, hlamL⟩ := generators_mem_L h
  intro k hkL hk1 hk2
  let x₁' : L := ⟨x₁, hx₁L⟩
  let x₂' : L := ⟨x₂, hx₂L⟩
  let lam' : L := ⟨lam, hlamL⟩
  let k' : L := ⟨k, hkL⟩
  have hW' : WreathRel x₁' x₂' lam' :=
    WreathRel.of_injective L.subtype L.subtype_injective h.wreath
  have hk1' : k' * x₁' ^ 2 = x₁' ^ 2 * k' := Subtype.ext hk1
  have hk2' : k' * (x₁' * x₂') ^ 2 = (x₁' * x₂') ^ 2 * k' := Subtype.ext hk2
  obtain ⟨a₁, a₂, b, r, α, hf, he⟩ := exists_frame_extras_of_psu33 h.hyp.lieModel
  let T' : Subgroup L := wreathGrp x₁' x₂' lam'
  let T₀ : Subgroup L := wreathGrp a₁ a₂ b
  let A₀ : Subgroup L := baseGrp a₁ a₂
  let A' : Subgroup L := baseGrp x₁' x₂'
  let V' : Subgroup L := fourGrp x₁' x₂'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardL : Nat.card L = 6048 := card_K_of_psu33 h.hyp.lieModel
  have hfacL : (Nat.card L).factorization 2 = 5 := by
    rw [hcardL, show (6048 : ℕ) = 2 ^ 5 * 189 from by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hcardT' : Nat.card T' = 2 ^ (Nat.card L).factorization 2 := by
    dsimp only [T']
    rw [hW'.card_wreathGrp, hfacL]
    norm_num
  have hcardT₀ : Nat.card T₀ = 2 ^ (Nat.card L).factorization 2 := by
    dsimp only [T₀]
    rw [hf.card_wreathGrp, hfacL]
    norm_num
  let T's : Sylow 2 L := Sylow.ofCard T' hcardT'
  let T₀s : Sylow 2 L := Sylow.ofCard T₀ hcardT₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq L T₀s T's
  have hTmap : T₀.map (MulAut.conj c).toMonoidHom = T' := by
    have hQ' : ((c • T₀s : Sylow 2 L) : Subgroup L) =
        T₀.map (MulAut.conj c).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    rw [← hQ', hc]
    rfl
  have hA₀le : A₀ ≤ T₀ := by
    dsimp only [A₀, T₀, baseGrp, wreathGrp]
    exact Subgroup.closure_mono (by
      intro y hy
      rcases hy with rfl | rfl <;> simp)
  haveI : IsMulCommutative A₀ := (hf.wreath.baseGrp_eq).1
  have hBle : A₀.map (MulAut.conj c).toMonoidHom ≤ T' := by
    rw [← hTmap]
    exact Subgroup.map_mono hA₀le
  have hBcard : Nat.card (A₀.map (MulAut.conj c).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective, (hf.wreath.baseGrp_eq).2.2]
  have hA : A₀.map (MulAut.conj c).toMonoidHom = A' :=
    WreathRel.eq_baseGrp_of_card_sixteen hW' hBle inferInstance hBcard
  have hk_cent : k' ∈ Subgroup.centralizer (V' : Set L) := by
    dsimp only [V', fourGrp]
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact hk1'.symm
    · exact hk2'.symm
  have hy₀ : c * a₁ ^ 2 * c⁻¹ ∈ V' := by
    have hV' : V' = closure {y : L | ∃ a ∈ A', y = a ^ 2} :=
      (WreathRel.fourGrp_eq_mho hW')
    rw [hV']
    apply Subgroup.subset_closure
    refine ⟨c * a₁ * c⁻¹, ?_, ?_⟩
    · rw [← hA]
      have ha₁ : a₁ ∈ A₀ := Subgroup.subset_closure (by simp)
      exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom ha₁
    · simp only [pow_two]
      group
  have hz₀ : c * (a₁ * a₂) ^ 2 * c⁻¹ ∈ V' := by
    have hV' : V' = closure {y : L | ∃ a ∈ A', y = a ^ 2} :=
      (WreathRel.fourGrp_eq_mho hW')
    rw [hV']
    apply Subgroup.subset_closure
    refine ⟨c * (a₁ * a₂) * c⁻¹, ?_, ?_⟩
    · rw [← hA]
      have hmul : a₁ * a₂ ∈ A₀ :=
        Subgroup.mul_mem A₀ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hmul
    · simp only [pow_two]
      group
  have hky : k' * (c * a₁ ^ 2 * c⁻¹) = (c * a₁ ^ 2 * c⁻¹) * k' :=
    (Subgroup.mem_centralizer_iff.mp hk_cent _ hy₀).symm
  have hkz : k' * (c * (a₁ * a₂) ^ 2 * c⁻¹) = (c * (a₁ * a₂) ^ 2 * c⁻¹) * k' :=
    (Subgroup.mem_centralizer_iff.mp hk_cent _ hz₀).symm
  have hky' : (c⁻¹ * k' * c) * a₁ ^ 2 = a₁ ^ 2 * (c⁻¹ * k' * c) := by
    calc (c⁻¹ * k' * c) * a₁ ^ 2
        = c⁻¹ * (k' * (c * a₁ ^ 2 * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a₁ ^ 2 * c⁻¹) * k') * c := by rw [hky]
      _ = a₁ ^ 2 * (c⁻¹ * k' * c) := by group
  have hkz' : (c⁻¹ * k' * c) * (a₁ * a₂) ^ 2 = (a₁ * a₂) ^ 2 * (c⁻¹ * k' * c) := by
    calc (c⁻¹ * k' * c) * (a₁ * a₂) ^ 2
        = c⁻¹ * (k' * (c * (a₁ * a₂) ^ 2 * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * (a₁ * a₂) ^ 2 * c⁻¹) * k') * c := by rw [hkz]
      _ = (a₁ * a₂) ^ 2 * (c⁻¹ * k' * c) := by group
  have hwA₀ : c⁻¹ * k' * c ∈ A₀ := he.cent_E (c⁻¹ * k' * c) hky' hkz'
  have hk'A : k' ∈ A' := by
    have hmem : (MulAut.conj c).toMonoidHom (c⁻¹ * k' * c) ∈
        A₀.map (MulAut.conj c).toMonoidHom := Subgroup.mem_map_of_mem _ hwA₀
    rw [hA] at hmem
    have hval : (MulAut.conj c).toMonoidHom (c⁻¹ * k' * c) = k' := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [hval] at hmem
  have hmap : (baseGrp x₁' x₂').map L.subtype = baseGrp x₁ x₂ := by
    rw [baseGrp, MonoidHom.map_closure, Set.image_pair, baseGrp]
    rfl
  have hcomap : baseGrp x₁' x₂' = (baseGrp x₁ x₂).comap L.subtype := by
    rw [← hmap, Subgroup.comap_map_eq_self_of_injective (f := L.subtype) L.subtype_injective]
  have hk'A'' : k' ∈ baseGrp x₁' x₂' := hk'A
  rw [hcomap] at hk'A''
  exact Subgroup.mem_comap.mp hk'A''

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
