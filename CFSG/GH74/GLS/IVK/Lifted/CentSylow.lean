module

public import CFSG.GH74.GLS.IVK.Lifted.FCent

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.DisconnectedInvolutionGraph CFSG.DisconnectedInvolutionGraph.Helpers
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Pure

theorem pow_fixes_pointwise {Q : Type} [Group Q] (φ : MulAut Q) (P : Subgroup Q)
    (hP : ∀ p ∈ P, φ p = p) (m : ℕ) : ∀ p ∈ P, (φ ^ m) p = p := by
  intro p hp
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, hP p hp]

theorem card_fixedSubgroup_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (φ : MulAut Q) :
    Nat.card ↥(fixedSubgroup Q' (MulAut.congr e φ)) = Nat.card ↥(fixedSubgroup Q φ) := by
  rw [fixedSubgroup_congr e φ]
  exact Nat.card_congr (MulEquiv.subgroupMap e _).symm.toEquiv

end Pure

section SL2

variable {F : Type} [Field F] [Finite F] {Q : Type} [Group Q] [Finite Q]

theorem sl2_no_central_sylow
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (e : Q ≃* SpecialLinearGroup (Fin 2) F) (hq : CFSG.IsQuasisimple Q)
    (hno : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (φ : MulAut Q) {k : ℕ} (hk : orderOf φ = 2 ^ k) (P : Sylow 2 Q)
    (hP : ∀ p ∈ (P : Subgroup Q), φ p = p) : φ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hφ1
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hφ1
    rw [pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  set ψ : MulAut Q := φ ^ (2 ^ (k - 1)) with hψdef
  have hψ1 : ψ ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hk] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hψ2 : ψ * ψ = 1 := by
    rw [hψdef, ← pow_add]
    have : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    rw [this, ← hk]
    exact pow_orderOf_eq_one φ
  have hψP : ∀ p ∈ (P : Subgroup Q), ψ p = p := pow_fixes_pointwise φ (P : Subgroup Q) hP _
  have hα2 : MulAut.congr e ψ * MulAut.congr e ψ = 1 := by rw [← map_mul, hψ2, map_one]
  have hα1 : MulAut.congr e ψ ≠ 1 := fun h =>
    hψ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  by_cases hσ : (gammaOf hodd h3 (MulAut.congr e ψ)).right = 1
  · obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 _ hσ
    have hcomm : ∀ a ∈ fixedSubgroup Q ψ, ∀ b ∈ fixedSubgroup Q ψ, a * b = b * a := by
      apply comm_fixed_of_congr e ψ
      rw [hG]
      exact fixed_comm_of_slConjugation G (hG ▸ hα1)
    obtain ⟨a, ha, b, hb, hab⟩ := sylow_exists_noncomm hq hno P
    exact hab (hcomm a (hψP a ha) b (hψP b hb))
  · have hγ2 : gammaOf hodd h3 (MulAut.congr e ψ) * gammaOf hodd h3 (MulAut.congr e ψ) = 1 := by
      rw [← map_mul, hα2, map_one]
    have hσσ : (gammaOf hodd h3 (MulAut.congr e ψ)).right *
        (gammaOf hodd h3 (MulAut.congr e ψ)).right = 1 := by
      have := congrArg SemidirectProduct.right hγ2
      simpa using this
    have hord : orderOf (gammaOf hodd h3 (MulAut.congr e ψ)).right = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ
    obtain ⟨β, hβ⟩ := exists_conj_slFieldAut hodd h3 _ hα2 hσ
    obtain ⟨σ, hσdef⟩ : ∃ σ : F ≃+* F, σ = (gammaOf hodd h3 (MulAut.congr e ψ)).right := ⟨_, rfl⟩
    rw [← hσdef] at hβ hord
    have hαeq : MulAut.congr e ψ = MulAut.congr β (slFieldAut σ) := by
      rw [← hβ]
      ext x
      simp [MulAut.congr_apply, MulAut.mul_apply]
    have hq0 : Nat.card ↥(fixedField σ) ^ 2 = Nat.card F := by
      simpa [hord] using fixedField_card_pow σ
    have hq0odd : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hodd
    have hcardD : Nat.card ↥(fixedSubgroup Q ψ) =
        Nat.card ↥(fixedField σ) * (Nat.card ↥(fixedField σ) ^ 2 - 1) := by
      rw [← card_fixedSubgroup_congr e ψ, hαeq, card_fixedSubgroup_congr β (slFieldAut σ),
        ← range_map_subtype σ]
      rw [Nat.card_congr (MonoidHom.ofInjective (map_subtype_injective σ)).toEquiv.symm,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hcardQ : Nat.card Q = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hPD : (P : Subgroup Q) ≤ fixedSubgroup Q ψ := fun p hp => hψP p hp
    have h1 : (fixedSubgroup Q ψ).index ∣ (P : Subgroup Q).index := Subgroup.index_dvd_of_le hPD
    have hodd' : ¬ 2 ∣ (P : Subgroup Q).index := Sylow.not_dvd_index P
    obtain ⟨a, ha⟩ : ∃ a, a = Nat.card ↥(fixedField σ) := ⟨_, rfl⟩
    rw [← ha] at hcardD hq0 hq0odd
    have ha1 : 1 < a := by rw [ha]; exact one_lt_card_fixedField σ
    obtain ⟨b, hb⟩ : ∃ b, a ^ 2 = b + 1 := ⟨a ^ 2 - 1, by
      have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega⟩
    have hbpos : 0 < b := by
      have : 4 ≤ a ^ 2 := by nlinarith
      omega
    have hmul := Subgroup.card_mul_index (fixedSubgroup Q ψ)
    rw [hcardD, hcardQ, ← hq0] at hmul
    have e1 : a ^ 2 - 1 = b := by omega
    have e2 : (a ^ 2) ^ 2 - 1 = b * (b + 2) := by
      rw [hb]
      have : (b + 1) ^ 2 = b * (b + 2) + 1 := by ring
      omega
    rw [e1, e2, hb] at hmul
    have hidx : (fixedSubgroup Q ψ).index = a * (b + 2) := by
      have hpos : 0 < a * b := Nat.mul_pos (by omega) hbpos
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc a * b * (fixedSubgroup Q ψ).index = (b + 1) * (b * (b + 2)) := hmul
        _ = a * b * (a * (b + 2)) := by
          calc (b + 1) * (b * (b + 2)) = a ^ 2 * (b * (b + 2)) := by rw [hb]
            _ = a * b * (a * (b + 2)) := by ring
    have hev : 2 ∣ (fixedSubgroup Q ψ).index := by
      rw [hidx]
      have hb2 : Odd (a ^ 2) := hq0odd.pow
      have hbe : Even b := by
        have : Odd (b + 1) := hb ▸ hb2
        have hh := (Nat.odd_add_one.1 this)
        exact Nat.not_odd_iff_even.1 hh
      have hbe2 : Even (b + 2) := by
        obtain ⟨r, hr⟩ := hbe
        exact ⟨r + 1, by omega⟩
      exact Dvd.dvd.mul_left (even_iff_two_dvd.1 hbe2) a
    exact hodd' (hev.trans h1)

end SL2

theorem not_sl2_of_double_cover_alt7 {Q : Type} [Group Q] (h7 : IsDoubleCoverOfAlt Q 7)
    {F : Type} [Field F] [Finite F] (e : Q ≃* StatedSL 2 F) : False := by
  have hQ5040 : Nat.card Q = 5040 := by
    obtain ⟨-, hZ, ⟨iso⟩⟩ := h7
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q), Nat.card_congr iso.toEquiv, hZ,
      Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hQ' : Nat.card Q = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  rw [hQ5040] at hQ'
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  by_cases hq : Nat.card F ≤ 17
  · interval_cases (Nat.card F) <;> omega
  · push Not at hq
    have h1 : 323 ≤ Nat.card F ^ 2 - 1 := by
      have : 324 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have h2 : 18 * 323 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul (by omega) h1
    omega

theorem three_lt_of_sl2_model {Q : Type} [Group Q] (hQ : IsSL2Or2A7 Q) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : Q ≃* StatedSL 2 F) : 3 < Nat.card F := by
  rcases sl_or_a7 hQ with ⟨F', _, _, hodd', h3', ⟨e'⟩⟩ | h7
  · by_contra hle
    push Not at hle
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    have hF3 : Nat.card F = 3 := by
      obtain ⟨r, hr⟩ := hodd
      omega
    have hcardF : Nat.card Q = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hcardF' : Nat.card Q = Nat.card F' * (Nat.card F' ^ 2 - 1) := by
      rw [Nat.card_congr e'.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hcard := hcardF.symm.trans hcardF'
    rw [hF3] at hcard
    have h4 : 4 ≤ Nat.card F' := by omega
    have h5 : 15 ≤ Nat.card F' ^ 2 - 1 := by
      have : 16 ≤ Nat.card F' ^ 2 := by nlinarith
      omega
    have h6 : 4 * 15 ≤ Nat.card F' * (Nat.card F' ^ 2 - 1) := Nat.mul_le_mul h4 h5
    omega
  · exact (not_sl2_of_double_cover_alt7 h7 e).elim

section HatGlue

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_hatImg {S K : Subgroup G}
    (hSyl : ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K) :
    ∃ Pbar : Sylow 2 (Hat K), (Pbar : Subgroup (Hat K)) = hatImg K (S ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hSyl
  refine ⟨P.mapSurjective (hatMk_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, hatImg_eq_map]
  have hPsub : (S ⊓ K).subgroupOf K = (P : Subgroup ↥K) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [hPsub]

theorem std4_exists_sylow_P {z : G} {S K₁ K₂ K : Subgroup G} (h : Std4 G z S K₁ K₂)
    (hKc : K = K₁ ∨ K = K₂) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K := by
  have hKC := h.comp_isPCompIn hKc
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 h.sylow
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hKC.1 hsub
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1 hSK

omit [Finite G] in
theorem phi_fixes_hatImg {S K : Subgroup G} {s : G} (hsN : s ∈ normalizer (K : Set G))
    (hcomm : ∀ p ∈ S ⊓ K, s * p = p * s) {x : Hat K} (hx : x ∈ hatImg K (S ⊓ K)) :
    phi K s hsN x = x := by
  obtain ⟨a, haS, rfl⟩ := mem_hatImg.1 hx
  rw [phi_mk]
  congr 1
  apply Subtype.ext
  show s * (a : G) * s⁻¹ = (a : G)
  rw [hcomm a haS]
  group

end HatGlue

end CFSG.GH74.GLS.IVK.Lifted
