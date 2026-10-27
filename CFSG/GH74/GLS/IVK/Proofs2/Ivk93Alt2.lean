module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open Equiv

theorem ivk93_alt_cfg2 {n : ℕ} (hn : n ≤ 11) {x : alternatingGroup (Fin n)} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup (alternatingGroup (Fin n))} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) : False := by
  have hx2 : x * x = 1 := h.mul_self_eq_one
  have hx1 : x ≠ 1 := h.ne_one
  set σ : Perm (Fin n) := (x : Perm (Fin n)) with hσdef
  have hσ : σ * σ = 1 := by
    have := congrArg Subtype.val hx2
    simpa [σ] using this
  have hσ1 : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hx1
    apply Subtype.ext
    exact Equiv.ext fun a => hcon a
  obtain ⟨hsupp, hsign⟩ := GHInv.involution_cycle_data hσ
  have hsign1 : Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 x.2
  have hle : σ.support.card ≤ 11 := by
    calc σ.support.card ≤ Finset.univ.card := Finset.card_le_univ _
      _ = n := by simp
      _ ≤ 11 := hn
  have hkeven : Even σ.cycleType.card := by
    rw [hsign] at hsign1
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 hsign1
  have hc : σ.cycleType.card ≤ 4 := by
    obtain ⟨j, hj⟩ := hkeven
    omega
  have : Group.IsPerfect ↥L₁ := h.perfect₁
  have hP : Group.IsPerfect ↥(L₁.map (alternatingGroup (Fin n)).subtype) :=
    Group.IsPerfect.map _
  have hPc : ∀ y ∈ L₁.map (alternatingGroup (Fin n)).subtype, y * σ = σ * y := by
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (h.le₁ hk))
  obtain ⟨a, ha⟩ := hσ1
  exact ha (GHInv.perfect_fixes_support hσ hc hP hPc σ ⟨x, h.mem₁, rfl⟩ a ha)

theorem ivk93_alt2 : ∀ n : ℕ, 7 ≤ n → n ≤ 11 →
    Ivk93Empty2 (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro n _ hn
  refine ivk93_empty2_of_cfg fun J _ _ hJ x hx q₁ q₂ L₁ L₂ hc => ?_
  obtain ⟨e⟩ := hJ
  exact ivk93_alt_cfg2 hn (Ivk93Cfg2.of_equiv e hc)

end CFSG.GH74.GLS.IVK.Proofs2
