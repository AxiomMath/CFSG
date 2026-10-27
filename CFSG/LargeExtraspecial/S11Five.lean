module

public import CFSG.LargeExtraspecial.S11Conj
public import CFSG.LargeExtraspecial.S4SevenA6
public import CFSG.LargeExtraspecial.S11Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

theorem card_ker_resL (haQ : g * S.z * g⁻¹ ∈ S.QG) (ht : t ∈ S.Lbar g) :
    Nat.card (resL haQ ht).ker = Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
  have hker : (resL haQ ht).ker = (Nbar S g t).subgroupOf (S.Lbar g) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    have h := restrictHom_eq_one_iff (S.O.subtype.comp (S.Lbar g).subtype) (Vt S g t)
      (fun x _ hu => apply_mem_Vt_of_mem_Rbar haQ (Lbar_le_Rbar ht x.2) hu) x
    exact h.trans ⟨fun h' => ⟨Lbar_le_Rbar ht x.2, h'⟩, fun h' => h'.2⟩
  rw [hker, ← inf_subgroupOf_right, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : Nbar S g t ⊓ S.Lbar g ≤ S.Lbar g)).toEquiv,
    inf_comm]

theorem card_Lbar_inf_Nbar (H : Hyp4 S g) (C : Cons311 S g) {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) =
      2 ^ (S.width - 1) := by
  have h1 := Subgroup.card_ker_mul_card_range (resL H.conj_mem ht)
  rw [card_ker_resL, range_resL, hL.LmodN_eq, card_centreGroup (aV_ne_zero H ht),
    C.card_Lbar] at h1
  exact h1

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.Lbar_inf_Nbar_eq {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    S.Lbar k ⊓ Nbar S g t = (((S.Qa k ⊓ S.Qa u) ⊓ S.M).subgroupOf S.M).map S.ρ := by
  obtain ⟨hkz, htk⟩ := K.base_of_mem hk
  have hy' := hy.of_conj hk.1 hkz
  have hL := (hy'.lin htk K.ne_one).resolve_left fun hR => by
    have h1 := K.lin.two_le_finrank
    rw [← hy.Vt_eq hk.1 hkz] at h1
    have h2 := Submodule.finrank_mono (Vt_le_span_of_Rbar_eq hy'.hyp4 hy'.cons hR)
    have h3 := finrank_span_singleton_le_one (S.cl (k * S.z * k⁻¹))
    omega
  have hN := hy.Nbar_eq hk.1 hkz t
  have hU8 : S.clSub (S.QG ⊓ S.Qa u) ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S k t := by
    rw [hy.Vt_eq hk.1 hkz, ← K.timmesfeld_11_3 hy]
    exact inf_le_left
  have hle := map_le_Lbar_inf_Nbar hy'.hyp4 K.rho_eq K.conj_eq hy'.noA2' K.ne_one hL hU8
  rw [hN] at hle
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hc1 := card_Lbar_inf_Nbar hy'.hyp4 hy'.cons hL
  rw [hN, hy.Vt_eq hk.1 hkz] at hc1
  have hc2 := card_Qa_inf_Qa hy'.hyp4 K.ne_one K.rho_eq K.conj_eq hy'.cons hy'.fusion hk.2
  have hc3 := card_le_two_mul hy'.hyp4 u
  have hc4 := card_eq_card_map_mul (S := S) (X := (S.Qa k ⊓ S.Qa u) ⊓ S.M) inf_le_right
  have hc5 := card_ker_inf_le (S := S) (X := (S.Qa k ⊓ S.Qa u) ⊓ S.M) (u := u)
    (inf_le_left.trans inf_le_right)
  rw [K.card_QG_inf_Qa hy] at hc5
  have hm := K.lin.two_le_finrank
  have hw := hy.hyp4.two_lt_width
  have e1 : Nat.card (S.Lbar k ⊓ Nbar S g t : Subgroup S.O) *
      2 ^ finrank (ZMod 2) (Vt S g t) = 2 ^ S.width := by
    have h1 : 2 ^ finrank (ZMod 2) (Vt S g t) = 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have h2 : 2 ^ S.width = 2 ^ (S.width - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h1, ← mul_assoc, hc1, ← h2]
  have e2 : 2 ^ S.width ≤ Nat.card ((((S.Qa k ⊓ S.Qa u) ⊓ S.M).subgroupOf S.M).map S.ρ) *
      2 ^ finrank (ZMod 2) (Vt S g t) := by
    have h1 : 2 ^ S.width * 2 ≤ 2 * Nat.card ((S.Qa k ⊓ S.Qa u) ⊓ S.M : Subgroup G) := by
      rw [← pow_succ, ← hc2]
      exact hc3
    have h2 : 2 ^ S.width ≤ Nat.card ((S.Qa k ⊓ S.Qa u) ⊓ S.M : Subgroup G) := by omega
    rw [hc4] at h2
    exact h2.trans (Nat.mul_le_mul_left _ hc5)
  rw [← e1] at e2
  exact Nat.le_of_mul_le_mul_right e2 (by positivity)

theorem Conf.Rbar_ne : Rbar S g t ≠ S.Lbar g := fun hR => by
  have h1 := K.lin.two_le_finrank
  have h2 := Submodule.finrank_mono (Vt_le_span_of_Rbar_eq hy.hyp4 hy.cons hR)
  have h3 := finrank_span_singleton_le_one (S.cl (g * S.z * g⁻¹))
  omega

theorem Conf.timmesfeld_11_5 (hCE : CentralExtInput.{u_G}) : Nbar S g t ≤ S.Lbar u := by
  have hP : ∀ hVQ : ¬ V S g t ≤ S.Qa g,
      ¬ PGL25Case hy.hyp4 hy.cons K.mem_Lbar K.ne_one hVQ :=
    fun hVQ => absurd K.lin.le_Qa hVQ
  rcases timmesfeld_4_7_a hCE hy.hyp4 hy.noA2' hy.cons K.mem_Lbar K.ne_one (K.Rbar_ne hy) hP
    with ⟨-, -, hN⟩ | ⟨hA, -⟩
  · rw [hN]
    refine iSup₂_le fun X hX => ?_
    obtain ⟨h, rfl, htX⟩ := hX
    have hcQ := conj_mem_QG' S h.2 hy.hyp4.conj_mem
    have hcz := conj_ne_z' S h.2 hy.hyp4.conj_ne
    obtain ⟨b, k, hbE, hk, hbcl⟩ :=
      K.exists_coimage hy (cl_mem_Vt htX) (cl_conj_z_ne_zero S hcQ hcz)
    subst hk
    obtain ⟨hkz, -⟩ := K.base_of_mem hbE
    rw [Lbar_eq_of_cl_eq S hbE.1 hkz hcQ hbcl.symm, K.Lbar_inf_Nbar_eq hy hbE]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr ⟨(mem_subgroupOf.mp hx).1.2, x.2⟩, rfl⟩
  · exact absurd hA (not_a6Pair_of_linCase hy.hyp4 K.lin)

end CFSG.LargeExtraspecial.S11
