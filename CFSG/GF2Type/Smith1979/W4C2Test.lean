module

public import CFSG.GF2Type.Smith1979.W4C2Model
public import Certificates.Certificate330390
import CFSG.GF2Type.Smith1979.W4C2TestN
import CFSG.GF2Type.Smith1979.W4C2TestM
public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

open Module QuadraticMap CFSG.LargeExtraspecial

theorem localTest_model {b : Vm} (hb0 : b ≠ 0) (hbq : q0 b = 0)
    (L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)) (hLH : L ≤ Hm)
    (hLc : ∀ a ∈ L, ∀ a' ∈ L, a * a' = a' * a) (hLs : ∀ a ∈ L, a * a = 1)
    (hL8 : 8 ≤ Nat.card L) (hLb : ∀ ℓ ∈ L, ℓ b = b)
    (hLn : ∀ m ∈ Hm, m b = b → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L)
    (D : Submodule (ZMod 2) Vm) (hbD : b ∈ D)
    (hLD : ∀ ℓ ∈ L, ∀ v, polar q0 b v = 0 → ℓ v - v ∈ D)
    (hcard : Nat.card L * 2 ^ (finrank (ZMod 2) D + 1) = 2 ^ 8)
    (hfaith : finrank (ZMod 2) D = 4 → ∀ ℓ ∈ L, (∀ v ∈ D, ℓ v = v) → ℓ = 1) :
    (b ∈ Nsub ∨ b ∈ Nssub) ∧ ∀ ℓ ∈ L, ℓ ≠ 1 → IsTypeA q0 ℓ 2 := by
  have hchk := Certificates.certificate330390
  obtain ⟨hv, ho, -, -⟩ := LocalTest.chk_parts hchk
  obtain ⟨E, hE, hcase⟩ := LocalTest.exists_conj_rep hv ho hb0 hbq
  have H : LocalTest.Hyp b L D :=
    ⟨hb0, hbq, hLH, hLc, hLs, hL8, hLb, hLn, hbD, hLD, hcard, hfaith⟩
  have key : ∃ h : Vm ≃ₗ[ZMod 2] Vm, h ∈ Hm ∧
      (((b ∈ Nsub ∨ b ∈ Nssub) ∧ h b = LocalTest.vecE LocalTest.bN) ∨
        (¬ (b ∈ Nsub ∨ b ∈ Nssub) ∧ h b = LocalTest.vecE LocalTest.bM)) := by
    refine ⟨(LocalTest.dec E)⁻¹, Hm.inv_mem (LocalTest.dec_mem_Hm hE), ?_⟩
    rcases hcase with ⟨hNb, hEb⟩ | ⟨hNb, hEb⟩
    · exact Or.inl ⟨hNb, by rw [← hEb]; exact LocalTest.inv_apply_apply' _ _⟩
    · exact Or.inr ⟨hNb, by rw [← hEb]; exact LocalTest.inv_apply_apply' _ _⟩
  obtain ⟨h, hhm, hcase'⟩ := key
  have hiso : ∀ v, q0 (h v) = q0 v := (mem_Hm_iff.mp hhm).1
  rcases hcase' with ⟨hNb, hb'⟩ | ⟨hNb, hb'⟩
  · refine ⟨hNb, ?_⟩
    have H' := H.conj hhm
    rw [hb'] at H'
    have hT := LocalTest.typeA_of_comm_N hchk H'.LH H'.Lc H'.Ls H'.Lb H'.Ln
    intro ℓ hℓ hℓ1
    have hmem : h * ℓ * h⁻¹ ∈ LocalTest.conjSub h L :=
      LocalTest.mem_conjSub.mpr (by simpa [mul_assoc] using hℓ)
    have hne : h * ℓ * h⁻¹ ≠ 1 := by
      intro h1
      apply hℓ1
      calc ℓ = h⁻¹ * (h * ℓ * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    exact LocalTest.isTypeA_of_conj hiso (hT _ hmem hne)
  · exfalso
    have H' := H.conj hhm
    rw [hb'] at H'
    exact LocalTest.false_of_M hchk H'

end CFSG.GF2Type.Smith1979.W4C2
