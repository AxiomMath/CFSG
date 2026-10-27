module

public import CFSG.GH74.Uniqueness.SU.SU5A8
public import CFSG.GH74.Uniqueness.SU.SU5J2R
public import CFSG.CGT.T75P.A8ExclGen

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.GH74.Uniqueness.SU.SU5
open CFSG.CGT.T75P

abbrev S8 : Type := ↥(J2Syl.sylA8 : Subgroup (alternatingGroup (Fin 8)))

private def psi : J2Syl →* S8 :=
  (J2Syl.permRep.codRestrict (alternatingGroup (Fin 8))
      (fun s => J2Syl.range_permRep_le ⟨s, rfl⟩)).codRestrict
    J2Syl.imgA8
    (fun s => Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨s, rfl⟩))

private theorem psi_apply (s : J2Syl) : (psi s).1.1 = J2Syl.permRep s := rfl

private theorem mem_sylA8_iff {x : alternatingGroup (Fin 8)} :
    x ∈ J2Syl.sylA8 ↔ x.1 ∈ J2Syl.permRep.range := by
  change x ∈ J2Syl.imgA8 ↔ x.1 ∈ J2Syl.permRep.range
  exact Subgroup.mem_subgroupOf

private theorem psi_surjective : Function.Surjective psi := by
  intro x
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (mem_sylA8_iff.1 x.2)
  exact ⟨s, Subtype.ext (Subtype.ext hs)⟩

private theorem psi_eq_one_iff (s : J2Syl) : psi s = 1 ↔ J2Syl.permRep s = 1 := by
  constructor
  · intro h
    have h1 : (psi s).1.1 = (1 : S8).1.1 := congrArg (fun x : S8 => x.1.1) h
    rw [psi_apply] at h1
    exact h1
  · intro h
    exact Subtype.ext (Subtype.ext h)

private theorem psi_ker : psi.ker = Subgroup.zpowers J2Syl.z0 := by
  ext s
  rw [MonoidHom.mem_ker, psi_eq_one_iff, J2Syl.permRep_eq_one_iff, J2Syl.mem_zpowers_z0]

private theorem psi_ker_card : Nat.card psi.ker = 2 := by
  rw [psi_ker, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact J2Syl.z0_sq) J2Syl.z0_ne_one

private theorem card_S8 : Nat.card S8 = 64 := by
  have h : Nat.card (J2Syl.imgA8) = 64 := by
    rw [J2Syl.card_imgA8, J2Syl.card_A8_factorization]
    norm_num
  exact h

private theorem psi_pow_four : ∀ s : J2Syl, (psi s) ^ 4 = 1 :=
  (by decide +kernel : ∀ s : J2Syl, (psi s) ^ 4 = 1)

theorem S8_pow_four (x : S8) : x ^ 4 = 1 := by
  obtain ⟨s, rfl⟩ := psi_surjective x
  exact psi_pow_four s

private def c0 : J2Syl := ⟨⟨0, 0, F4c.w⟩, 1⟩

private theorem psi_c0_ne_one : psi c0 ≠ 1 :=
  (by decide +kernel : psi c0 ≠ 1)

private theorem psi_c0_sq : psi c0 * psi c0 = 1 :=
  (by decide +kernel : psi c0 * psi c0 = 1)

private theorem psi_c0_central : ∀ s : J2Syl, psi s * psi c0 = psi c0 * psi s :=
  (by decide +kernel : ∀ s : J2Syl, psi s * psi c0 = psi c0 * psi s)

private theorem psi_center_check :
    ∀ w : J2Syl, (∀ s : J2Syl, psi w * psi s = psi s * psi w) →
      psi w = 1 ∨ psi w = psi c0 :=
  (by decide +kernel : ∀ w : J2Syl, (∀ s : J2Syl, psi w * psi s = psi s * psi w) →
      psi w = 1 ∨ psi w = psi c0)

theorem S8_card_center : Nat.card (Subgroup.center S8) = 2 := by
  have hcenter : Subgroup.center S8 = Subgroup.zpowers (psi c0) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨w, rfl⟩ := psi_surjective x
      have hw : ∀ s : J2Syl, psi w * psi s = psi s * psi w := by
        intro s
        exact ((Subgroup.mem_center_iff.1 hx) (psi s)).symm
      rw [J2Syl.mem_zpowers_of_sq_eq_one psi_c0_ne_one psi_c0_sq]
      exact psi_center_check w hw
    · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro y
      obtain ⟨s, rfl⟩ := psi_surjective y
      exact psi_c0_central s
  rw [hcenter, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact psi_c0_sq) psi_c0_ne_one

private theorem psi_R_sq : ∀ r : J2Syl, r ∈ J2Syl.R → (psi r) ^ 2 = 1 :=
  (by decide +kernel : ∀ r : J2Syl, r ∈ J2Syl.R → (psi r) ^ 2 = 1)

private theorem z0_mem_R : J2Syl.z0 ∈ J2Syl.R := by
  rw [J2Syl.mem_R]; decide +kernel

theorem S8_exists_e16 : ∃ E : Subgroup S8, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  refine ⟨J2Syl.R.map psi, ?_, ?_⟩
  · have hle : psi.ker ≤ J2Syl.R := by
      rw [psi_ker]; exact Subgroup.zpowers_le.2 z0_mem_R
    have hRidx : J2Syl.R.index = 4 := by
      have h := Subgroup.card_mul_index (H := J2Syl.R)
      rw [J2Syl.card_R, card_J2Syl] at h
      omega
    have hKidx : psi.ker.index = 64 := by
      have h := Subgroup.card_mul_index (H := psi.ker)
      rw [psi_ker_card, card_J2Syl] at h
      omega
    have hmain : Nat.card (J2Syl.R.map psi) * 4 = 64 := by
      rw [← Subgroup.relIndex_ker (K := J2Syl.R) psi]
      have h := Subgroup.relIndex_mul_index hle
      rw [hRidx, hKidx] at h
      exact h
    omega
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact psi_R_sq r hr

private theorem noncomm_exists :
    ∃ a b : J2Syl, (psi a) ^ 2 = 1 ∧ (psi b) ^ 2 = 1 ∧ psi a * psi b ≠ psi b * psi a :=
  (by decide +kernel : ∃ a b : J2Syl,
      (psi a) ^ 2 = 1 ∧ (psi b) ^ 2 = 1 ∧ psi a * psi b ≠ psi b * psi a)

theorem S8_exists_noncomm_involutions :
    ∃ a b : S8, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a := by
  obtain ⟨a, b, ha, hb, hab⟩ := noncomm_exists
  exact ⟨psi a, psi b, ha, hb, hab⟩

private def v1 : J2Syl := ⟨⟨0, 1, 0⟩, 1⟩

private def v2 : J2Syl := ⟨⟨0, F4c.w, 0⟩, 1⟩

private def gensJ : Finset J2Syl := {J2Syl.q2, J2Syl.rho, v1, v2}

private def Wj : ℕ → Finset J2Syl
  | 0 => {1}
  | n + 1 => Wj n ∪ (Wj n).biUnion (fun x => gensJ.image (fun g => x * g))
      ∪ (Wj n).image (fun x => x⁻¹)

private def CJ : Subgroup J2Syl := Subgroup.closure (gensJ : Set J2Syl)

private theorem Wj_subset : ∀ n p, p ∈ Wj n → p ∈ CJ := by
  intro n
  induction n with
  | zero =>
    intro p hp
    rw [Wj, Finset.mem_singleton] at hp
    subst hp
    exact Subgroup.one_mem _
  | succ n ih =>
    intro p hp
    simp only [Wj, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_singleton] at hp
    rcases hp with (hp | hp) | hp
    · exact ih p hp
    · obtain ⟨x, hx, g, hg, rfl⟩ := hp
      refine Subgroup.mul_mem _ (ih x hx) (Subgroup.subset_closure ?_)
      simp only [gensJ, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp [gensJ]
    · obtain ⟨x, hx, rfl⟩ := hp
      exact Subgroup.inv_mem _ (ih x hx)

private def Wj6 : Finset J2Syl := Wj 6

private theorem all_mem_Wj6 : ∀ p : J2Syl, p ∈ Wj6 :=
  (by decide +kernel : ∀ p : J2Syl, p ∈ Wj6)

set_option maxRecDepth 10000 in
private theorem Wj_subset6 : ∀ p, p ∈ Wj6 → p ∈ CJ := by
  intro p hp
  exact Wj_subset 6 p hp

set_option maxRecDepth 10000 in
private theorem CJ_eq_top : CJ = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro p
  exact Wj_subset6 p (all_mem_Wj6 p)

private theorem closure_gensJ_eq_top : Subgroup.closure (gensJ : Set J2Syl) = ⊤ := by
  change CJ = ⊤
  exact CJ_eq_top

private theorem closure_image_gensJ :
    Subgroup.closure ((gensJ.image psi : Finset S8) : Set S8) = ⊤ := by
  have h1 := MonoidHom.map_closure psi (gensJ : Set J2Syl)
  rw [closure_gensJ_eq_top, ← MonoidHom.range_eq_map psi,
      psi.range_eq_top_of_surjective psi_surjective] at h1
  rw [Finset.coe_image, ← h1]

set_option maxRecDepth 10000 in
private theorem exists_sq_ne_one_of_card_32 (R : Subgroup S8) (h32 : Nat.card R = 32) :
    ∃ x ∈ R, x ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  set P : Subgroup J2Syl := R.comap psi with hPdef
  have hle : psi.ker ≤ P := by
    intro s hs
    rw [hPdef]
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.1 hs]
    exact R.one_mem
  have hPmap : P.map psi = R := by
    rw [hPdef, Subgroup.map_comap_eq, psi.range_eq_top_of_surjective psi_surjective,
      top_inf_eq]
  have hPcard : Nat.card P = 64 := by
    have hrel : psi.ker.relIndex P = 32 := by
      rw [Subgroup.relIndex_ker (K := P) psi, hPmap, h32]
    have hmul := Subgroup.relIndex_mul_index hle
    rw [hrel] at hmul
    have hKidx : psi.ker.index = 64 := by
      have hc := Subgroup.card_mul_index (H := psi.ker)
      rw [psi_ker_card, card_J2Syl] at hc
      omega
    rw [hKidx] at hmul
    have hPidx : P.index = 2 := by omega
    have hc := Subgroup.card_mul_index (H := P)
    rw [hPidx, card_J2Syl] at hc
    omega
  have hsubset : ∀ s ∈ P, s * s = 1 ∨ s * s = J2Syl.z0 := by
    intro s hs
    have hsR : psi s ∈ R := by
      rw [hPdef] at hs
      exact hs
    have h1 : psi (s * s) = 1 := by
      rw [map_mul, ← pow_two]
      exact h (psi s) hsR
    rw [psi_eq_one_iff, J2Syl.permRep_eq_one_iff] at h1
    exact h1
  have hFcard : ((Finset.univ : Finset J2Syl).filter
      (fun s => s * s = 1 ∨ s * s = J2Syl.z0)).card = 56 := by
    decide +kernel
  have hsubset' : ∀ s ∈ P, s ∈ (Finset.univ : Finset J2Syl).filter
      (fun s => s * s = 1 ∨ s * s = J2Syl.z0) :=
    fun s hs => Finset.mem_filter.2 ⟨Finset.mem_univ s, hsubset s hs⟩
  have hlecard : Nat.card P ≤ ((Finset.univ : Finset J2Syl).filter
      (fun s => s * s = 1 ∨ s * s = J2Syl.z0)).card :=
    card_le_card_of_subset_finset hsubset'
  rw [hPcard, hFcard] at hlecard
  omega

theorem S8_gen_four (R : Subgroup S8) :
    ∃ s : Finset S8, s.card ≤ 4 ∧ Subgroup.closure (s : Set S8) = R := by
  have hdvd : Nat.card R ∣ 64 := by
    rw [← card_S8]
    exact Subgroup.card_subgroup_dvd_card R
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num] at hdvd
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases k
  · obtain ⟨s, hs, hcl⟩ := a8x_exists_closure_card_le_log R 0 (by rw [hk])
    exact ⟨s, by omega, hcl⟩
  · obtain ⟨s, hs, hcl⟩ := a8x_exists_closure_card_le_log R 1 (by rw [hk])
    exact ⟨s, by omega, hcl⟩
  · obtain ⟨s, hs, hcl⟩ := a8x_exists_closure_card_le_log R 2 (by rw [hk])
    exact ⟨s, by omega, hcl⟩
  · obtain ⟨s, hs, hcl⟩ := a8x_exists_closure_card_le_log R 3 (by rw [hk])
    exact ⟨s, by omega, hcl⟩
  · obtain ⟨s, hs, hcl⟩ := a8x_exists_closure_card_le_log R 4 (by rw [hk])
    exact ⟨s, by omega, hcl⟩
  · obtain ⟨x, hxR, hx2⟩ := exists_sq_ne_one_of_card_32 R (by rw [hk]; norm_num)
    obtain ⟨s, hs, hcl⟩ := a8x_exists_closure_card_le_four R (by rw [hk]; norm_num) hxR
      (a8x_four_le_orderOf (by rw [hk]; norm_num) hxR hx2)
    exact ⟨s, hs, hcl⟩
  · have htop : R = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hk, card_S8]
      norm_num
    refine ⟨gensJ.image psi, ?_, ?_⟩
    · calc (gensJ.image psi).card ≤ gensJ.card := Finset.card_image_le
        _ ≤ 4 := by decide +kernel
    · rw [htop]
      exact closure_image_gensJ

end CFSG.EvenSporadicStandard.HNRecog.GH73
