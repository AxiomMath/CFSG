module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
open Equiv

theorem ivk93cov_alt_cfg {m : ℕ} (hm : m ≤ 11) {x : alternatingGroup (Fin m)} {n : ℕ}
    {B : Subgroup (alternatingGroup (Fin m))} (h : Ivk93Cov x n B) : False := by
  have hx2 : x * x = 1 := h.mul_self_eq_one
  have hx1 : x ≠ 1 := h.ne_one
  set σ : Perm (Fin m) := (x : Perm (Fin m)) with hσdef
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
      _ = m := by simp
      _ ≤ 11 := hm
  have hkeven : Even σ.cycleType.card := by
    rw [hsign] at hsign1
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 hsign1
  have hc : σ.cycleType.card ≤ 4 := by
    obtain ⟨j, hj⟩ := hkeven
    omega
  have : Group.IsPerfect ↥B := h.perfect
  have hP : Group.IsPerfect ↥(B.map (alternatingGroup (Fin m)).subtype) :=
    Group.IsPerfect.map _
  have hPc : ∀ y ∈ B.map (alternatingGroup (Fin m)).subtype, y * σ = σ * y := by
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (h.le hk))
  obtain ⟨a, ha⟩ := hσ1
  exact ha (GHInv.perfect_fixes_support hσ hc hP hPc σ ⟨x, h.mem, rfl⟩ a ha)

theorem ivk93cov_alt : ∀ m : ℕ, 7 ≤ m → m ≤ 11 →
    Ivk93CovEmpty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin m))) := by
  intro m _ hm
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x hx n B hc => ?_
  obtain ⟨e⟩ := hJ
  exact ivk93cov_alt_cfg hm (hc.of_equiv e)

end CFSG.GH74.GLS.IVK.Proofs2
