module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Mathieu
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Sporadic.Schreier CFSG.OddStandard CFSG.LieType.Ree
open Equiv

theorem ivk93w_alt_cfg {n : ℕ} (hn : n ≤ 11) {x : alternatingGroup (Fin n)} {q : ℕ}
    {B : Subgroup (alternatingGroup (Fin n))} (h : Ivk93W x q B) : False := by
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
  have : Group.IsPerfect ↥B := h.perfect
  have hP : Group.IsPerfect ↥(B.map (alternatingGroup (Fin n)).subtype) :=
    Group.IsPerfect.map _
  have hPc : ∀ y ∈ B.map (alternatingGroup (Fin n)).subtype, y * σ = σ * y := by
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (h.le hk))
  obtain ⟨a, ha⟩ := hσ1
  exact ha (GHInv.perfect_fixes_support hσ hc hP hPc σ ⟨x, h.mem, rfl⟩ a ha)

theorem ivk93w_alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 →
    Ivk93WEmpty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro n _ hn J _ _ hJ x q B h _
  obtain ⟨e⟩ := hJ
  exact ivk93w_alt_cfg hn (h.of_equiv e)

theorem ivk93w_m11 :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M11 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m11_innerRecordsValid e' h.mul_self_eq_one h.ne_one
  have hshape : recordShape m11Records = [(165, 48)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 48 := by simp at hp; rw [hp]
  exact h.false_of_card_cent_dvd (N := 48) (by rw [hcard, hp2])
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk93w_m22 :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M22 := e
  obtain ⟨p, hp, hcard⟩ := mathieu_card_cent_mem m22_innerRecordsValid e' h.mul_self_eq_one h.ne_one
  have hshape : recordShape m22Records = [(1155, 384)] := rfl
  rw [hshape] at hp
  have hp2 : p.2 = 384 := by simp at hp; rw [hp]
  exact h.false_of_card_cent_dvd (N := 384) (by rw [hcard, hp2]) not_sl2_dvd_384

theorem ivk93w_j1 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e0⟩ := hJ
  let e : J ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  exact (h.of_equiv e).false_of_abelian_sylow CFSG.Walter.J1Props.hasAbelianSylowTwo

theorem ivk93w_ree :
    ∀ f : ℕ, Ivk93WEmpty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f J _ _ hJ x q B h _
  have hR : ReeTitsModel J .twistedG2 3 f := by
    rcases hJ with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := GHInv.ree_model_data hR
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  exact (h.of_equiv e).false_of_abelian_sylow
    (CFSG.Walter.Ree.Model.hasAbelianSylowTwo_reeGamma hK hw₀)

end CFSG.GH74.GLS.IVK.Proofs2
