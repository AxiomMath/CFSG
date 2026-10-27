module

public import CFSG.LargeExtraspecial.S14C13Inner
public import CFSG.LargeExtraspecial.S14C13Schur
public import CFSG.LargeExtraspecial.S6SevenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_mem_Rbar_apply_eq (hCE : CentralExtInput.{0}) {t : S.O} (hSt : Stage S g t)
    (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) {x : S.O} (hx : x ∈ Ct S t) :
    ∃ r ∈ Rbar S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  have haQ := hSt.hyp4.conj_mem
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  have hxV := apply_mem_Vt_of_mem_Ct haQ hx (cl_a_mem_Vt hSt.mem)
  have horb : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ orbit S g t := by
    rcases S6.timmesfeld_6_7 hCE hSt.hyp4 hNo hSt.cons hSt.mem hSt.ne_one with ho | ⟨-, -, h4⟩
    · rw [ho]
      exact ⟨hxV, x, (Subgroup.mem_inf.mp hx).1, rfl⟩
    · omega
  obtain ⟨r, hr, e⟩ := horb
  exact ⟨r, hr, e⟩

theorem Ct_le_Rbar (hCE : CentralExtInput.{0}) {t : S.O} {c : Config} (hSt : Stage S g t)
    (hocc : c.Occurs S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (hc : c = .sp6 ∨ c = .omegaPlus8a ∨ c = .omegaPlus12) (h7 : Concl14_7 S g t) :
    Ct S t ≤ Rbar S g t := by
  intro x hx
  have haQ := hSt.hyp4.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  obtain ⟨-, -, -, -, -, -, h6⟩ := case_of_occurs hocc
  have hr0 := exists_mem_Rbar_apply_eq hCE hSt h6 hx
  rcases hr0 with ⟨r, hr, hra⟩
  have hrC : r ∈ Ct S t := Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar hr, Rbar_le_centralizer haQ hr⟩
  let y : Ct S t := ⟨r⁻¹ * x, mul_mem (inv_mem hrC) hx⟩
  have hya : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    show ((r⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = _
    rw [coe_mul_apply, hra, inv_apply_apply_O]
  have hyL : (y : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) haQ hSt.hyp4.conj_ne
      (Subgroup.mem_inf.mp y.2).1 (by simpa using hya)
    simpa using this
  have hinner : ∃ r₀ : Rbar S g t, ∀ e : RmodN S g t,
      (autC haQ y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
        resV haQ t r₀ * e * (resV haQ t r₀)⁻¹ := by
    rcases hc with rfl | rfl | rfl
    · obtain ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩ := hocc.1
      exact inner_of_sp hSp (m := 3) (by norm_num) (by rw [hdim]) hyL
    · exact inner_of_omega hCE hSt hocc (m := 4) (by norm_num) hocc.1.1
        (fun _ => finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 8) hocc.2.2) hyL
    · exact inner_of_omega hCE hSt hocc (m := 6) (by norm_num) hocc.1.1
        (fun _ => finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 32) hocc.2.2) hyL
  rcases hinner with ⟨r₀, hr₀⟩
  have hr₀C : (r₀ : S.O) ∈ Ct S t :=
    Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar r₀.2, Rbar_le_centralizer haQ r₀.2⟩
  have hz : (r₀ : S.O)⁻¹ * y ∈ Ct S t := mul_mem (inv_mem hr₀C) y.2
  have hzN := mem_Nbar_of_comm_Rbar hCE hSt hocc hext hc h7 hz
    (comm_mem_Nbar_of_autC_eq haQ y r₀ hr₀)
  have e : x = r * (r₀ * ((r₀ : S.O)⁻¹ * (r⁻¹ * x))) := by group
  rw [e]
  exact mul_mem hr (mul_mem r₀.2 (Nbar_le_Rbar hzN))

end CFSG.LargeExtraspecial.S14
