module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B5Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B2Ind

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

theorem eq_of_cube {A : Type*} [Group A] (hc : ∀ a b : A, a * b = b * a)
    (hA : ∀ a : A, a * a = 1) {w : MulAut A} (hw : w ^ 3 = 1) {e : A}
    (h : w (w e * e⁻¹) = w e * e⁻¹) : w e = e := by
  have hinv : ∀ a : A, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hA a)
  have h1 : w (w e) * (w e)⁻¹ = w e * e⁻¹ := by
    rw [← h, map_mul, map_inv]
  rw [hinv (w e), hinv e] at h1
  have h2 : w (w e) = e := mul_right_cancel (h1.trans (hc (w e) e))
  have h4 : w (w (w e)) = e := by
    have h5 : (w ^ 3) e = e := by rw [hw]; rfl
    simpa [pow_succ, MulAut.mul_apply] using h5
  rwa [h2] at h4

theorem cohom_core {A : Type*} [Group A] (hc : ∀ a b : A, a * b = b * a)
    (hA : ∀ a : A, a * a = 1) {x0 w0 : MulAut A} (hw : w0 ^ 3 = 1)
    (himg : ∀ c : A, w0 (x0 c * c⁻¹) = x0 c * c⁻¹)
    (hinter : ∀ b : A, w0 b = b → x0 b = b → ∃ c : A, b = x0 c * c⁻¹)
    {e b3 : A} (hxe : x0 e = e) (hwe : w0 e = x0 b3 * e * b3) : ∃ c : A, e = x0 c * c⁻¹ := by
  have hinv : ∀ a : A, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hA a)
  have h1 : w0 e * e⁻¹ = x0 b3 * b3⁻¹ := by
    rw [hwe, hinv b3, hinv e]
    calc x0 b3 * e * b3 * e = x0 b3 * (e * b3) * e := by rw [mul_assoc (x0 b3) e b3]
      _ = x0 b3 * (b3 * e) * e := by rw [hc e b3]
      _ = x0 b3 * b3 * (e * e) := by rw [← mul_assoc (x0 b3) b3 e, mul_assoc (x0 b3 * b3) e e]
      _ = x0 b3 * b3 := by rw [hA e, mul_one]
  have h2 : w0 (w0 e * e⁻¹) = w0 e * e⁻¹ := by
    rw [h1]
    exact himg b3
  exact hinter e (eq_of_cube hc hA hw h2) hxe

structure S6Data {G : Type} [Group G] (B : Subgroup G) (x0 w0 : MulAut ↥B) : Prop where
  w_cube : w0 ^ 3 = 1
  img : ∀ c : ↥B, w0 (x0 c * c⁻¹) = x0 c * c⁻¹
  inter : ∀ b : ↥B, w0 b = b → x0 b = b → ∃ c : ↥B, b = x0 c * c⁻¹

namespace Induces

variable {G : Type} [Group G] {B : Subgroup G} {y : G} {α : MulAut ↥B}

theorem conj_mem (h : Induces B y α) {b : G} (hb : b ∈ B) : y * b * y⁻¹ ∈ B := by
  have h1 := (α ⟨b, hb⟩).2
  rwa [h ⟨b, hb⟩] at h1

end Induces

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem mem_cent_of_rhoG_eq_one (hE : Sec8E G t L S z g B E) {n : G}
    (hn : n ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) (h : rhoG hE n = 1) :
    n ∈ centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : n * e * n⁻¹ = e := by
    have h2 := rhoG_apply_X hE (XCt_le_N hE hn) (Subgroup.mem_inf.mp hn).1 ⟨e, he⟩
    rw [h, MulAut.one_apply] at h2
    exact h2.symm
  calc e * n = (n * e * n⁻¹) * n := by rw [h1]
    _ = n * e := by group

theorem exists_inv (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {x0 w0 : MulAut ↥B}
    (hS : S6Data B x0 w0) {j w : G}
    (hj : j ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G))
    (hw : w ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G))
    (hjB : Induces B j x0) (hwB : Induces B w w0) (hjj : j * j ∈ B)
    (hcomm : rhoG hE w * rhoG hE j = rhoG hE j * rhoG hE w) :
    ∃ c ∈ B, (j * c) * (j * c) = 1 := by
  have hBsq : ∀ a : ↥B, a * a = 1 := fun a => Subtype.ext (E_sq hE (B_le_E hE a.2))
  have hBc : ∀ a b : ↥B, a * b = b * a :=
    fun a b => Subtype.ext (E_comm hE (B_le_E hE a.2) (B_le_E hE b.2))
  have hjX : j ∈ normalizer (E : Set G) := (Subgroup.mem_inf.mp hj).1
  have hjN : j ∈ Nsub8 t B := XCt_le_N hE hj
  have hwN : w ∈ Nsub8 t B := XCt_le_N hE hw
  obtain ⟨c3, hc3def⟩ : ∃ c3 : G, c3 = j⁻¹ * w * j * w⁻¹ := ⟨_, rfl⟩
  have hc3mem : c3 ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) := by
    rw [hc3def]
    exact mul_mem (mul_mem (mul_mem (inv_mem hj) hw) hj) (inv_mem hw)
  have hrho3 : rhoG hE c3 = 1 := by
    rw [hc3def, rhoG_mul hE ((Nsub8 t B).mul_mem ((Nsub8 t B).mul_mem ((Nsub8 t B).inv_mem hjN)
        hwN) hjN) ((Nsub8 t B).inv_mem hwN),
      rhoG_mul hE ((Nsub8 t B).mul_mem ((Nsub8 t B).inv_mem hjN) hwN) hjN,
      rhoG_mul hE ((Nsub8 t B).inv_mem hjN) hwN, rhoG_inv hE hjN, rhoG_inv hE hwN]
    calc (rhoG hE j)⁻¹ * rhoG hE w * rhoG hE j * (rhoG hE w)⁻¹
        = (rhoG hE j)⁻¹ * (rhoG hE w * rhoG hE j) * (rhoG hE w)⁻¹ := by group
      _ = (rhoG hE j)⁻¹ * (rhoG hE j * rhoG hE w) * (rhoG hE w)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  have hc3cent : c3 ∈ centralizer (E : Set G) := mem_cent_of_rhoG_eq_one hE hc3mem hrho3
  have hc3t : c3 * t = t * c3 := Subgroup.mem_centralizer_singleton_iff.mp hc3mem.2
  obtain ⟨b3, hb3, o3, ho3, -, hc3eq⟩ := cent_decomp F hE hc3cent hc3t
  have ho4 : j⁻¹ * o3 * j ∈ oddCoreIn (normalizer (E : Set G)) := by
    simpa using OX_conj_mem (inv_mem hjX) ho3
  have hcomm4 : b3 * (j⁻¹ * o3 * j) = (j⁻¹ * o3 * j) * b3 :=
    Subgroup.mem_centralizer_iff.mp ((F.hCE G t L S z g B E hE).2 ho4) b3 (B_le_E hE hb3)
  have hwj : w * j * w⁻¹ = j * c3 := by rw [hc3def]; group
  have hstar : w * (j * j) * w⁻¹ =
      ((j * b3 * j⁻¹) * (j * j) * b3) * ((j⁻¹ * o3 * j) * o3) := by
    calc w * (j * j) * w⁻¹ = (w * j * w⁻¹) * (w * j * w⁻¹) := by group
      _ = (j * c3) * (j * c3) := by rw [hwj]
      _ = (j * (b3 * o3)) * (j * (b3 * o3)) := by rw [hc3eq]
      _ = (j * b3 * j) * ((j⁻¹ * o3 * j) * b3) * o3 := by group
      _ = (j * b3 * j) * (b3 * (j⁻¹ * o3 * j)) * o3 := by rw [hcomm4]
      _ = ((j * b3 * j⁻¹) * (j * j) * b3) * ((j⁻¹ * o3 * j) * o3) := by group
  have hbq : (j * b3 * j⁻¹) * (j * j) * b3 ∈ B :=
    mul_mem (mul_mem (hjB.conj_mem hb3) hjj) hb3
  have hwe : w * (j * j) * w⁻¹ ∈ B := hwB.conj_mem hjj
  have hoo : (j⁻¹ * o3 * j) * o3 = 1 := by
    have h1 : (j⁻¹ * o3 * j) * o3 =
        ((j * b3 * j⁻¹) * (j * j) * b3)⁻¹ * (w * (j * j) * w⁻¹) := by
      rw [hstar, inv_mul_cancel_left]
    apply E_inf_OX hE
    · rw [h1]
      exact B_le_E hE (mul_mem (inv_mem hbq) hwe)
    · exact mul_mem ho4 ho3
  have hwe' : w * (j * j) * w⁻¹ = (j * b3 * j⁻¹) * (j * j) * b3 := by
    rw [hstar, hoo, mul_one]
  obtain ⟨eB, heB⟩ : ∃ eB : ↥B, (eB : G) = j * j := ⟨⟨j * j, hjj⟩, rfl⟩
  obtain ⟨bB, hbB⟩ : ∃ bB : ↥B, (bB : G) = b3 := ⟨⟨b3, hb3⟩, rfl⟩
  have hxe : x0 eB = eB := Subtype.ext (by rw [hjB eB, heB]; group)
  have hwe_B : w0 eB = x0 bB * eB * bB := by
    apply Subtype.ext
    have h1 : ((x0 bB * eB * bB : ↥B) : G) = (j * b3 * j⁻¹) * (j * j) * b3 := by
      simp only [Subgroup.coe_mul, hjB bB, heB, hbB]
    rw [h1, hwB eB, heB]
    exact hwe'
  obtain ⟨c, hc⟩ := cohom_core hBc hBsq hS.w_cube hS.img hS.inter hxe hwe_B
  refine ⟨c, c.2, ?_⟩
  have h1 : (eB : G) = ((x0 c : ↥B) : G) * (c : G)⁻¹ := congrArg Subtype.val hc
  have h2 : (j * (c : G)) * (j * (c : G)) = ((x0 c : ↥B) : G) * (eB : G) * (c : G) := by
    rw [hjB c, heB]
    group
  rw [h2, h1]
  calc ((x0 c : ↥B) : G) * (((x0 c : ↥B) : G) * (c : G)⁻¹) * (c : G)
      = (((x0 c : ↥B) : G) * ((x0 c : ↥B) : G)) * ((c : G)⁻¹ * (c : G)) := by group
    _ = 1 := by rw [E_sq hE (B_le_E hE (x0 c).2), inv_mul_cancel, one_mul]

end B89

end CFSG.OddStandard.SmallF3.Omega
