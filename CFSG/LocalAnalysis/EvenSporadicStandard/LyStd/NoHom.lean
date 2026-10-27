module

public import CFSG.LocalAnalysis.EvenSporadicStandard.LyStd.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.HomReduction
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame

public section

namespace CFSG.EvenSporadicStandard.LyStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std

theorem exists_orderOf_four_of_doubleCover_eleven {C : Type} [Group C]
    (h : IsDoubleCoverOfAlt C 11) : ∃ w : C, orderOf w = 4 := by
  obtain ⟨hq, hc, ⟨e⟩⟩ := h
  have hfin : Finite (center C) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  let σ : Equiv.Perm (Fin 11) :=
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5
  have hσ2 : σ ^ 2 ≠ 1 := by decide
  have hσ4 : σ ^ 4 = 1 := by decide
  have hσsign : σ ∈ alternatingGroup (Fin 11) := by
    simp [σ, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  let x : alternatingGroup (Fin 11) := ⟨σ, hσsign⟩
  have hx2 : x ^ 2 ≠ 1 := fun h2 => hσ2 (congrArg Subtype.val h2)
  have hx4 : x ^ 4 = 1 := Subtype.ext hσ4
  have hxord : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using hx2)
      (by simpa using hx4)
    simpa using this
  let φ : C →* alternatingGroup (Fin 11) := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  obtain ⟨y, hy⟩ : ∃ y : C, φ y = x := by
    obtain ⟨q, hq'⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, hq'⟩
  have hdvd4 : 4 ∣ orderOf y := by
    rw [← hxord, ← hy]
    exact orderOf_map_dvd φ y
  have hy4 : y ^ 4 ∈ center C := by
    have h1 : φ (y ^ 4) = 1 := by rw [map_pow, hy, hx4]
    have h2 : e ((y ^ 4 : C) : C ⧸ center C) = 1 := h1
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff] at h2
    exact h2
  have hy8 : y ^ 8 = 1 := by
    have h2 : (⟨y ^ 4, hy4⟩ : center C) ^ 2 = 1 := by
      rw [← hc]
      exact pow_card_eq_one'
    have := congrArg Subtype.val h2
    simpa [← pow_mul] using this
  have h8 : orderOf y ∣ 8 := orderOf_dvd_of_pow_eq_one hy8
  have hle : orderOf y ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  have hcases : orderOf y = 4 ∨ orderOf y = 8 := by
    interval_cases hord : orderOf y <;> omega
  rcases hcases with h4 | h8'
  · exact ⟨y, h4⟩
  · refine ⟨y ^ 2, ?_⟩
    rw [orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), h8']
    norm_num

theorem ly_involution_isSq
    {u : NativeSporadic.Ly} (hu : orderOf u = 2) :
    ∃ s : NativeSporadic.Ly, s * s = u := by
  have : Finite NativeSporadic.Ly := (CFSG.Sporadic.Ly.fam_ly_simplicity).1
  obtain ⟨t₀, ht₀⟩ := exists_involution_of_isSporadic_ly
    (T := NativeSporadic.Ly) ⟨MulEquiv.refl _⟩
  obtain ⟨w, hw⟩ := exists_orderOf_four_of_doubleCover_eleven
    (isDoubleCoverOfAlt_ly (T := NativeSporadic.Ly) ⟨MulEquiv.refl _⟩ ht₀)
  have hy : orderOf (w : NativeSporadic.Ly) = 4 := by rw [Subgroup.orderOf_coe]; exact hw
  have hyy : orderOf ((w : NativeSporadic.Ly) * w) = 2 := by
    rw [← pow_two, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hy]
    norm_num
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.Sporadic.Recognition.LyonsSims.ly_isConj_of_involutions hyy hu)
  refine ⟨c * w * c⁻¹, ?_⟩
  calc c * (w : NativeSporadic.Ly) * c⁻¹ * (c * w * c⁻¹)
      = c * ((w : NativeSporadic.Ly) * w) * c⁻¹ := by group
    _ = u := hc

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem ly_oneClassData
    (h : StdHyp G L) (hL : IsSporadic L .Ly) {z t : G} (hz : z ∈ centralizer (L : Set G))
    (hz2 : orderOf z = 2) (ht : t ∈ L) (ht2 : orderOf t = 2) : OneClassData L z t := by
  have := h.simple
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_ly hL
  obtain ⟨hC, hd, hcomm⟩ := h.centralizer_eq_prod_ly hL hz hz2
  obtain ⟨e₀⟩ := hL
  have e : L ≃* NativeSporadic.Ly := e₀
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; exact absurd ht2 (by decide)
  have hzpow : ∀ b ∈ Subgroup.zpowers z, b = 1 ∨ b = z := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_mod_orderOf, hz2]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left; simp [h0]
    · right; simp [h0]
  have hord : ∀ u : L, u * u = 1 → u ≠ 1 → orderOf (e u) = 2 := by
    intro u hu2 hu1
    have hsq : (e u) ^ 2 = 1 := by rw [pow_two, ← map_mul, hu2, map_one]
    have hne : e u ≠ 1 := fun h' => hu1 (e.injective (by rw [h', map_one]))
    exact orderOf_eq_prime hsq hne
  let t' : L := ⟨t, ht⟩
  have ht'2 : t' * t' = 1 := Subtype.ext (by simpa using htt)
  have ht'1 : t' ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  exact
    { z_mul_self := hzz
      z_ne_one := hz1
      t_mul_self := htt
      t_ne_one := ht1
      t_mem := ht
      z_comm := fun l hl => (mem_centralizer_iff.1 hz l hl).symm
      z_not_mem := fun hzL => hz1 (mem_bot.1 (hd.le_bot ⟨hzL, mem_zpowers z⟩))
      centralizer_z := by
        intro g hg
        have hg' : g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hg.symm
        rw [hC] at hg'
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcomm hg'
        rcases hzpow b hb with rfl | rfl
        · exact ⟨a, ha, Or.inl (by simp)⟩
        · exact ⟨a, ha, Or.inr rfl⟩
      oneClass := by
        intro u hu hu2 hu1
        let u' : L := ⟨u, hu⟩
        have hu'2 : u' * u' = 1 := Subtype.ext (by simpa using hu2)
        have hu'1 : u' ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
        obtain ⟨c, hc⟩ := isConj_iff.1
          (CFSG.Sporadic.Recognition.LyonsSims.ly_isConj_of_involutions (hord u' hu'2 hu'1)
            (hord t' ht'2 ht'1))
        refine ⟨((e.symm c⁻¹ : L) : G), (e.symm c⁻¹ : L).2, ?_⟩
        have hx : u' = e.symm c⁻¹ * t' * (e.symm c⁻¹)⁻¹ := by
          apply e.injective
          simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
          rw [← hc]
          group
        simpa using congrArg Subtype.val hx
      t_sq := by
        obtain ⟨s, hs⟩ := ly_involution_isSq (hord t' ht'2 ht'1)
        refine ⟨((e.symm s : L) : G), (e.symm s : L).2, ?_⟩
        have : e.symm s * e.symm s = t' := by
          apply e.injective
          rw [map_mul, MulEquiv.apply_symm_apply, hs]
        simpa using congrArg Subtype.val this }

theorem ly_no_hom
    (h : StdHyp G L) (hL : IsSporadic L .Ly) {t u : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hu : u ∈ L) (hu2 : orderOf u = 2)
    (φ : centralizer ({u} : Set G) →* Multiplicative (ZMod 2))
    (htu : t ∈ centralizer ({u} : Set G)) (hφ : φ ⟨t, htu⟩ ≠ 1) : False := by
  have := h.simple
  exact (ly_oneClassData h hL ht ht2 hu hu2).false_of_hom h.nonabelian (centralizer ({u} : Set G))
    (fun g => mem_centralizer_singleton_iff) φ htu hφ

end CFSG.EvenSporadicStandard.LyStd
