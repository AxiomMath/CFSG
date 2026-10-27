module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverSetup
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.ProperTwoGeneratedCore.Lemma37 DihedralGroup
open scoped commutatorElement

section Dihedral

variable {n : ℕ}

theorem sr_zero_mul_r_one_mul_inv : (sr 0 : DihedralGroup n) * r 1 * (sr 0)⁻¹ = (r 1)⁻¹ := by
  rw [inv_sr, sr_mul_r, sr_mul_sr, inv_r]
  congr 1
  ring

theorem inv_sq_r_one_zpow_eq_one_iff (j : ℤ) :
    ((r 1 : DihedralGroup n)⁻¹ * (r 1)⁻¹) ^ j = 1 ↔ (n : ℤ) ∣ 2 * j := by
  have h1 : (r 1 : DihedralGroup n)⁻¹ * (r 1)⁻¹ = (r 1) ^ (-2 : ℤ) := by
    rw [zpow_neg, ← mul_inv_rev, ← pow_two]
    norm_cast
  rw [h1, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, orderOf_r_one,
    show (-2 : ℤ) * j = -(2 * j) by ring, dvd_neg]

end Dihedral

section Abstract

variable {P : Type*} [Group P] {n : ℕ} [NeZero n]

theorem map_eq_one_of_mem_center_of_dihedral_cover (ψ : P →* DihedralGroup n)
    (hψ : Function.Surjective ψ) (hcen : ∀ c, ψ c = 1 → ∀ g, g * c = c * g)
    (hcomm : ∀ c, ψ c = 1 → c ∈ commutator P) (hne : ∃ c, ψ c = 1 ∧ c ≠ 1) :
    ∀ l ∈ Subgroup.center P, ψ l = 1 := by
  intro l hl
  by_contra hl1
  obtain ⟨c₀, hc₀, hc₀1⟩ := hne
  obtain ⟨u, hu⟩ := hψ (r 1)
  obtain ⟨a, ha⟩ := hψ (sr 0)
  have hidx : (Subgroup.zpowers (ψ u)).index = 2 := by
    rw [hu]
    exact dihedral_index_zpowers_r_one
  have hnot : ψ a ∉ Subgroup.zpowers (ψ u) := by
    rw [ha, hu]
    exact dihedral_sr_not_mem_zpowers
  set w : P := u⁻¹ * (a * u * a⁻¹) with hw
  have hP' : commutator P ≤ Subgroup.zpowers w :=
    commutator_le_zpowers_of_index_two ψ hψ hcen hidx hnot
  have hψauai : ψ (a * u * a⁻¹) = (ψ u)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ha, hu, sr_zero_mul_r_one_mul_inv]
  have hcu : u * (a * u * a⁻¹) = (a * u * a⁻¹) * u :=
    commute_of_mem_zpowers ψ hcen (r := u) (Subgroup.mem_zpowers _)
      (by rw [hψauai]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
  have hcuw : Commute u w := (Commute.refl u).inv_right.mul_right hcu
  have hψw : ψ w = (r 1)⁻¹ * (r 1)⁻¹ := by
    rw [hw, map_mul, map_inv, hψauai, hu]
  have hmul : a * u * a⁻¹ = u * w := by rw [hw, mul_inv_cancel_left]
  obtain ⟨j₀, hj₀⟩ := Subgroup.mem_zpowers_iff.mp (hP' (hcomm c₀ hc₀))
  have hcentral : ∀ g, g * l = l * g := Subgroup.mem_center_iff.mp hl
  have central_of : ∀ y : P, ψ y = ψ l → ∀ g, g * y = y * g := by
    intro y hy g
    have hc : ψ (l⁻¹ * y) = 1 := by rw [map_mul, map_inv, hy, inv_mul_cancel]
    have hy' : y = l * (l⁻¹ * y) := by rw [mul_inv_cancel_left]
    rw [hy', ← mul_assoc, hcentral g, mul_assoc, hcen _ hc g, ← mul_assoc]
  cases hψl : ψ l with
  | r i =>
    have hk0 : i.val ≠ 0 := by
      intro hk
      apply hl1
      rw [hψl, (ZMod.val_eq_zero i).mp hk]
      rfl
    have hklt : i.val < n := ZMod.val_lt i
    have huk : ψ (u ^ i.val) = ψ l := by
      rw [map_pow, hu, r_one_pow, hψl, ZMod.natCast_zmod_val]
    have hukc : ∀ g, g * u ^ i.val = u ^ i.val * g := central_of _ huk
    have hconj : a * u ^ i.val * a⁻¹ = u ^ i.val := by
      rw [hukc a, mul_inv_cancel_right]
    have hwk : w ^ i.val = 1 := by
      have h1 : (a * u * a⁻¹) ^ i.val = u ^ i.val := by rw [conj_pow, hconj]
      rw [hmul, hcuw.mul_pow] at h1
      exact mul_eq_left.mp h1
    have hdvd : (n : ℤ) ∣ 2 * (i.val : ℤ) := by
      rw [← inv_sq_r_one_zpow_eq_one_iff, ← hψw, ← map_zpow, zpow_natCast, hwk, map_one]
    have hn2 : 2 * i.val = n := by
      obtain ⟨t, ht⟩ := hdvd
      have hnpos : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
      have hk0' : (0 : ℤ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hklt' : (i.val : ℤ) < n := by exact_mod_cast hklt
      have ht1 : t = 1 := by
        have h1 : 0 < t := by
          by_contra h
          push Not at h
          nlinarith
        have h2 : t < 2 := by
          by_contra h
          push Not at h
          nlinarith
        omega
      rw [ht1, mul_one] at ht
      exact_mod_cast ht
    have hdvd2 : (i.val : ℤ) ∣ j₀ := by
      have h1 : ψ (w ^ j₀) = 1 := by rw [hj₀]; exact hc₀
      rw [map_zpow, hψw, inv_sq_r_one_zpow_eq_one_iff] at h1
      have h2 : (2 * (i.val : ℤ)) ∣ 2 * j₀ := by
        have : (n : ℤ) = 2 * (i.val : ℤ) := by exact_mod_cast hn2.symm
        rwa [this] at h1
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    obtain ⟨s, hs⟩ := hdvd2
    apply hc₀1
    rw [← hj₀, hs, zpow_mul, zpow_natCast, hwk, one_zpow]
  | sr i =>
    have huk : ψ (a * u ^ i.val) = ψ l := by
      rw [map_mul, map_pow, hu, ha, r_one_pow, hψl, sr_mul_r, ZMod.natCast_zmod_val, zero_add]
    have hc := central_of _ huk
    have hau : a * u = u * a := by
      have h1 := hc u
      have h2 : a * u ^ i.val * u = a * u * u ^ i.val := by
        rw [mul_assoc, mul_assoc, ← pow_succ, ← pow_succ']
      have h3 : u * (a * u ^ i.val) = u * a * u ^ i.val := by rw [mul_assoc]
      rw [h2, h3] at h1
      exact (mul_right_cancel h1).symm
    have hw1 : w = 1 := by
      rw [hw, hau, mul_inv_cancel_right, inv_mul_cancel]
    apply hc₀1
    rw [← hj₀, hw1, one_zpow]

end Abstract

theorem sylowCentralizerCentral_of_hasDihedralSylowTwo {K : Type} [Group K] [Finite K]
    (hD : CFSG.GorensteinWalter.HasDihedralSylowTwo K) : SylowCentralizerCentral K := by
  intro L _ _ hperf hZ hne ⟨e⟩ P x hxP _ hx
  have := hperf
  obtain ⟨m, hm, ⟨e'⟩⟩ := CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e hD
    (centralSylow P)
  have e'' : (centralSylow P : Subgroup (L ⧸ Subgroup.center L)) ≃* DihedralGroup (2 ^ m) := e'
  have hψ := coverHom_surjective (Q := P) (e := e'')
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hzP : (z : L) ∈ (P : Subgroup L) := hZ.le_sylow_of_normal P z.2
  have hne' : ∃ c : (P : Subgroup L), coverHom P e'' c = 1 ∧ c ≠ 1 :=
    ⟨⟨z, hzP⟩, (coverHom_eq_one_iff _).mpr z.2,
      fun h => hz (Subtype.ext (congrArg (fun y : (P : Subgroup L) => (y : L)) h))⟩
  have hl : (⟨x, hxP⟩ : (P : Subgroup L)) ∈ Subgroup.center (P : Subgroup L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) g g.2)
  have h1 := map_eq_one_of_mem_center_of_dihedral_cover (coverHom P e'') hψ
    (fun c hc g => coverHom_central c hc g)
    (fun c hc => coverHom_mem_commutator (Group.IsPerfect.commutator_eq_top (G := L)) c hc) hne'
    _ hl
  exact (coverHom_eq_one_iff _).mp h1

theorem sylowCentralizerCentral_of_psl_two_odd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : StatedClassicalModel X .PSL 2 p f) :
    SylowCentralizerCentral X := by
  obtain ⟨K, _, _, _, e, hcard, -, -⟩ := K1.psl2_model_data hp2 h
  have hp : p.Prime := h.1.1
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, by rw [Nat.card_eq_fintype_card, hcard]⟩
  exact sylowCentralizerCentral_of_hasDihedralSylowTwo
    (CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd))

theorem sylowCentralizerCentral_of_small
    {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5)) ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
      StatedClassicalModel X .PSL 2 2 2 ∨ StatedClassicalModel X .PSL 3 2 1) :
    SylowCentralizerCentral X := by
  obtain ⟨ℓ, e, hℓ, hodd, he, hmodel⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.small_models_odd_linear_two_aliases X h
  exact sylowCentralizerCentral_of_psl_two_odd (by rintro rfl; exact absurd hodd (by decide)) he
    hmodel

theorem sylowCentralizerCentral_of_alt_seven {X : Type} [Group X] [Finite X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 7))) : SylowCentralizerCentral X := by
  obtain ⟨e⟩ := h
  exact sylowCentralizerCentral_of_hasDihedralSylowTwo
    (CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven)

end CFSG.QuasithinUnique.Ch1
