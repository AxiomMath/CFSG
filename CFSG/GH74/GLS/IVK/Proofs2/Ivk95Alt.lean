module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open Equiv

theorem ivk95_alt_cfg {n : ℕ} (hn : n ≤ 11) {z : alternatingGroup (Fin n)} (h : Ivk95Cfg z) :
    False := by
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← h.ord]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.ord
    rw [h1, orderOf_one] at this
    omega
  set σ : Perm (Fin n) := (z : Perm (Fin n)) with hσdef
  have hσ : σ * σ = 1 := by
    have := congrArg Subtype.val hz2
    simpa [σ] using this
  have hσ1 : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hz1
    apply Subtype.ext
    exact Equiv.ext fun a => hcon a
  obtain ⟨hsupp, hsign⟩ := GHInv.involution_cycle_data hσ
  have hsign1 : Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 z.2
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
  have : Group.IsPerfect ↥(Ez z) := h.quasi.1
  have hP : Group.IsPerfect ↥((Ez z).map (alternatingGroup (Fin n)).subtype) :=
    Group.IsPerfect.map _
  have hPc : ∀ x ∈ (Ez z).map (alternatingGroup (Fin n)).subtype, x * σ = σ * x := by
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (h.central k hk)
  obtain ⟨a, ha⟩ := hσ1
  exact ha (GHInv.perfect_fixes_support hσ hc hP hPc σ ⟨z, h.mem, rfl⟩ a ha)

theorem ivk95_alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 →
    Ivk95Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro n _ hn
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := hJ
  exact ivk95_alt_cfg hn (hz.of_equiv e)

end CFSG.GH74.GLS.IVK.Proofs2
