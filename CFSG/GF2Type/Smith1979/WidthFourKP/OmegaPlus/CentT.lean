module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Orbit
public import CFSG.Quasithin.SteinbergCCOddPlaneActionBound
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Ct_dvd (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hplus : PlusTypeAt S g ht)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4) :
    Nat.card (S14.Ct S t) ∣ 288 := by
  obtain ⟨Q, hQ, hpol, hR, hE, hsing⟩ := hΩ.exists_form
  have hplusQ : CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    obtain ⟨P₀, hP₀2, hP₀⟩ := hplus
    refine ⟨P₀, by rw [hP₀2, h4], fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    · exact (hsing v hv0).mpr (hP₀ v hv hv0)
  let ρ : S14.Ct S t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := S8.resCV S g H.conj_mem t
  have hker4 : Nat.card ρ.ker ∣ 4 := by
    let T : Subgroup S.O := ρ.ker.map (S14.Ct S t).subtype
    have hTle : T ≤ S14.Ct S t := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hTfix : ∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      rintro σ ⟨x, hx, rfl⟩ v hv
      have hx1 : ρ x = 1 := hx
      change (S8.resCV S g H.conj_mem t) x = 1 at hx1
      have h1 := S8.coe_resCV_apply H.conj_mem (show ↥(S8.CMt S t) from x) ⟨v, hv⟩
      rw [hx1] at h1
      simp at h1
      exact h1.symm
    have h := hK4 T hTle hTfix
    rwa [Subgroup.card_map_of_injective (S14.Ct S t).subtype_injective] at h
  have hrange72 : Nat.card ρ.range ∣ 72 := by
    have hcardO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 72 := by
      have hcardZ := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
        (V := Vt S g t) hQ (m := 1) (by rw [h4]) (ε := 1) (Or.inl ⟨rfl, hplusQ⟩)
      have h72 : (2 * (Nat.card (ZMod 2) : ℤ) ^ (1 * (1 + 1)) *
          ((Nat.card (ZMod 2) : ℤ) ^ (1 + 1) - 1) *
            ∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1)) = 72 := by
        norm_num [Nat.card_zmod]
      rw [h72] at hcardZ
      exact Nat.cast_injective hcardZ
    have hle : ρ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro _ ⟨x, rfl⟩
      exact W4As.resCV_mem_orthogonalGroup_omega H hNo C ht ht1 hVQ hΩ hsing x
    have := Subgroup.card_dvd_of_le hle
    rwa [hcardO] at this
  calc Nat.card (S14.Ct S t) = Nat.card ρ.ker * Nat.card ρ.range :=
        (Subgroup.card_ker_mul_card_range ρ).symm
    _ ∣ 4 * 72 := Nat.mul_dvd_mul hker4 hrange72
    _ = 288 := by norm_num


theorem pow_thirtyTwo_mem (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hplus : PlusTypeAt S g ht) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP9 : Nat.card P = 9)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    ∀ c ∈ S14.Ct S t, c ^ 32 ∈ P := by
  intro c hc
  have hPC : P ≤ S14.Ct S t := hPR.trans (S8.Rbar_le_CMt H.conj_mem)
  have hPnorm : (P.subgroupOf (S14.Ct S t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hPn (g : S.O) g.2 (n : S.O) hn
  let q : S14.Ct S t →* (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) :=
    QuotientGroup.mk' (P.subgroupOf (S14.Ct S t))
  have hcardCt := card_Ct_dvd H hNo C ht ht1 hVQ hΩ h4 hplus hK4
  have h9sub : Nat.card (P.subgroupOf (S14.Ct S t)) = 9 := by
    rw [← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hmul : Nat.card (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) *
      Nat.card (P.subgroupOf (S14.Ct S t)) ∣ 288 := by
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf (S14.Ct S t))]
    exact hcardCt
  have hquot : Nat.card (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) ∣ 32 := by
    rw [h9sub] at hmul
    have h288 : (288 : ℕ) = 32 * 9 := by norm_num
    rw [h288] at hmul
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hmul
  have hpow : ∀ x : S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t), x ^ 32 = 1 := by
    intro x
    obtain ⟨k, hk⟩ := hquot
    rw [hk, pow_mul, pow_card_eq_one', one_pow]
  have hmem : q ⟨c, hc⟩ ^ 32 = 1 := hpow (q ⟨c, hc⟩)
  have hmem' : q (⟨c, hc⟩ ^ 32) = 1 := by rw [map_pow, hmem]
  have hmem'' : (⟨c, hc⟩ : S14.Ct S t) ^ 32 ∈ P.subgroupOf (S14.Ct S t) :=
    (QuotientGroup.eq_one_iff (N := P.subgroupOf (S14.Ct S t)) _).mp hmem'
  exact Subgroup.mem_subgroupOf.mp hmem''


theorem fix_of_normalized {t : S.O} {P : Subgroup S.O} (hP9 : Nat.card P = 9)
    (hKP : ∀ c ∈ S14.Ct S t, (∃ k : ℕ, c ^ 2 ^ k = 1) → (∀ x ∈ P, c * x = x * c) →
      ∀ v ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    ∀ T : Subgroup S.O, T ≤ S14.Ct S t → IsPGroup 2 T → (∀ p ∈ P, ∀ x ∈ T, p * x * p⁻¹ ∈ T) →
      ∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  intro T hT hP2 hnorm σ hσ v hv
  have hσCt : σ ∈ S14.Ct S t := hT hσ
  have hTP : T ⊓ P = ⊥ := by
    obtain ⟨n, hn⟩ := hP2.exists_card_dvd_pow
    have h2 : Nat.card (T ⊓ P : Subgroup S.O) ∣ 2 ^ n :=
      (Subgroup.card_dvd_of_le inf_le_left).trans hn
    have h9 : Nat.card (T ⊓ P : Subgroup S.O) ∣ 9 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ P ≤ P)
      rwa [hP9] at this
    have hcop : Nat.Coprime (2 ^ n) 9 := (by norm_num : Nat.Coprime 2 9).pow_left n
    have h1 : Nat.card (T ⊓ P : Subgroup S.O) ∣ 1 := by
      have := Nat.dvd_gcd h2 h9
      rwa [hcop.gcd_eq_one] at this
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h1)
  have hcomm : ∀ p ∈ P, σ * p = p * σ := by
    intro p hp
    have hmemT : p * σ * p⁻¹ * σ⁻¹ ∈ T := by
      have h := T.mul_mem (hnorm p hp σ hσ) (T.inv_mem hσ)
      simpa [mul_assoc] using h
    have hmemP : p * σ * p⁻¹ * σ⁻¹ ∈ P := by
      have h := P.mul_mem hp (hPn σ hσCt p⁻¹ (P.inv_mem hp))
      simpa [mul_assoc] using h
    have hmem : p * σ * p⁻¹ * σ⁻¹ ∈ T ⊓ P := ⟨hmemT, hmemP⟩
    rw [hTP] at hmem
    have h1 : p * σ * p⁻¹ * σ⁻¹ = 1 := by simpa using hmem
    have h2 : p * σ * p⁻¹ = σ := (mul_inv_eq_one.mp h1)
    exact (mul_inv_eq_iff_eq_mul (a := p * σ) (b := p) (c := σ) |>.mp h2).symm
  have hex : ∃ k : ℕ, σ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hP2.exists_pow_pow_eq_one ⟨σ, hσ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact hKP σ hσCt hex hcomm v hv


theorem exists_mem_Lbar_inv (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    ∃ l ∈ S.Lbar g, ∀ x ∈ P, l * x * l⁻¹ = x⁻¹ := by
  have hLCt : S.Lbar g ≤ S14.Ct S t :=
    (S4.Lbar_le_Rbar ht).trans (S8.Rbar_le_CMt H.conj_mem)
  have hLnorm : S.Lbar g ≤ Subgroup.normalizer (P : Set S.O) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hPn l (hLCt hl) x hx
    · intro hx
      have h2 := hPn l⁻¹ (hLCt ((S.Lbar g).inv_mem hl)) (l * x * l⁻¹) hx
      simpa [mul_assoc] using h2
  let ψ : S.Lbar g →* MulAut P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hLnorm)
  have hψ : ∀ (l : S.Lbar g) (x : P),
      ((ψ l x : P) : S.O) = (l : S.O) * (x : S.O) * (l : S.O)⁻¹ := by
    intro l x
    rfl
  have hψself : ψ ⟨t, ht⟩ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hψ]
    have hxt : (x : S.O) * t = t * (x : S.O) :=
      S4.commute_of_mem_Rbar H.conj_mem (hPR x.2)
    calc t * (x : S.O) * t⁻¹ = (x : S.O) * t * t⁻¹ := by rw [hxt]
      _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hker : ψ.ker = zpowers (⟨t, ht⟩ : S.Lbar g) := by
    refine le_antisymm ?_ ?_
    · intro l hl
      have hcomm : ∀ x ∈ P, (l : S.O) * x = x * (l : S.O) := by
        intro x hx
        have h2 : ψ l ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [MonoidHom.mem_ker.mp hl]; rfl
        have h3 := congrArg Subtype.val h2
        rw [hψ] at h3
        exact mul_inv_eq_iff_eq_mul (a := (l : S.O) * x) (b := (l : S.O)) (c := x) |>.mp h3
      rcases eq_one_or_eq_of_commute_card_nine hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9
        l.2 hcomm with h1 | h1
      · have h1' : l = 1 := Subtype.ext h1
        rw [h1']; exact Subgroup.one_mem _
      · have h1' : l = (⟨t, ht⟩ : S.Lbar g) := Subtype.ext h1
        rw [h1']; exact Subgroup.mem_zpowers _
    · refine Subgroup.zpowers_le.mpr ?_
      rw [MonoidHom.mem_ker]
      exact hψself
  have hcardLbar : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  have hcard_range : Nat.card ψ.range = 4 := by
    have ht2 : (⟨t, ht⟩ : S.Lbar g) * ⟨t, ht⟩ = 1 :=
      Subtype.ext (S4.mul_self_of_mem_Lbar S H.conj_mem ht)
    have htne : (⟨t, ht⟩ : S.Lbar g) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    have hcardzp : Nat.card ↥(zpowers (⟨t, ht⟩ : S.Lbar g)) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime ht2 htne
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hker, hcardzp, hcardLbar] at h
    omega
  have hA2 : ∀ a ∈ ψ.range, a * a = 1 := by
    rintro a ⟨l, rfl⟩
    rw [← map_mul]
    have hll : (l : S.Lbar g) * l = 1 :=
      Subtype.ext (S4.mul_self_of_mem_Lbar S H.conj_mem l.2)
    rw [hll, map_one]
  have hAcomm : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    rintro a ⟨l, rfl⟩ b ⟨m, rfl⟩
    have hlm : (l * m : S.Lbar g) = m * l :=
      Subtype.ext (S4.Lbar_comm S H.conj_mem l.2 m.2)
    calc ψ l * ψ m = ψ (l * m) := (map_mul ψ l m).symm
      _ = ψ (m * l) := by rw [hlm]
      _ = ψ m * ψ l := map_mul ψ m l
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPcomm : ∀ a b : P, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (G := P) (p := 3) (by rw [hP9]; norm_num)
  have hPexp : ∀ v : P, v ^ 3 = 1 := fun v => Subtype.ext (hP3 v.1 v.2)
  have hPcard : Nat.card P = 3 ^ 2 := by rw [hP9]; norm_num
  have hcardA : Nat.card ↥ψ.range = 4 := hcard_range
  letI : Fintype ↥ψ.range := Fintype.ofFinite _
  have hAle : 1 < Fintype.card ↥ψ.range := by
    rw [← Nat.card_eq_fintype_card, hcardA]
    norm_num
  obtain ⟨a0, ha0ne⟩ := Fintype.exists_ne_of_one_lt_card hAle (1 : ↥ψ.range)
  let aMul : MulAut P := a0
  have haMul_mem : aMul ∈ ψ.range := a0.2
  have haMul_ne : aMul ≠ 1 := fun h => ha0ne (Subtype.ext h)
  have haMul2 : aMul * aMul = 1 := hA2 aMul haMul_mem
  obtain ⟨b, hb1, hba⟩ := Cardinal.exists_ne_ne_of_three_le
    (by rw [← Nat.cast_card, hcard_range]; norm_num) (1 : ↥ψ.range) a0
  have hbA : (b : MulAut P) ∈ ψ.range := b.2
  have hb2 : (b : MulAut P) * b = 1 := hA2 b hbA
  have hcomm_ab : aMul * b = b * aMul := hAcomm aMul haMul_mem b hbA
  have hpm := CFSG.Quasithin.SteinbergCC.pm_of_commuting_involutions (V := P) (p := 3)
    (by norm_num) (by norm_num) hPcomm hPexp hPcard haMul2 hb2 hcomm_ab
  have key : ∀ s : MulAut P, s ∈ ψ.range → (∀ v : P, s v = v⁻¹) →
      ∃ l ∈ S.Lbar g, ∀ x ∈ P, l * x * l⁻¹ = x⁻¹ := by
    intro s hs hinv
    obtain ⟨l, hl⟩ := hs
    refine ⟨l, l.2, fun x hx => ?_⟩
    have h1 : ψ l ⟨x, hx⟩ = ⟨x⁻¹, P.inv_mem hx⟩ := by
      rw [hl]
      apply Subtype.ext
      have h := congrArg Subtype.val (hinv ⟨x, hx⟩)
      simpa using h
    have h2 := congrArg Subtype.val h1
    rw [hψ] at h2
    exact h2
  have ext_one : ∀ s : MulAut P, (∀ v, s v = v) → s = 1 := by
    intro s hs
    refine MulEquiv.ext fun v => ?_
    rw [hs v]
    rfl
  rcases hpm with (h1 | h1) | (h2 | h2) | (h3 | h3)
  · exact absurd (ext_one aMul h1) haMul_ne
  · exact key aMul haMul_mem h1
  · exact absurd (Subtype.ext (ext_one (b : MulAut P) h2)) hb1
  · exact key b hbA h2
  · refine absurd (ext_one (aMul * b) h3) ?_
    intro h
    have hmul : aMul * (b : MulAut P) = 1 := h
    have hab : aMul = b := by
      have h := congrArg (fun x => x * (b : MulAut P)) hmul
      simpa [mul_assoc, hb2] using h
    exact hba (Subtype.ext (by simpa [aMul] using hab.symm))
  · have hmem : aMul * b ∈ ψ.range := ψ.range.mul_mem haMul_mem hbA
    exact key (aMul * b) hmem h3


theorem card_Ct_inf_normalizer_dvd (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9)
    (hK4 : ∀ T : Subgroup S.O, T ≤ S14.Ct S t →
      (∀ σ ∈ T, ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Nat.card T ∣ 4)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPn : ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    Nat.card (S14.Ct S t ⊓ normalizer (S.Lbar g : Set S.O) : Subgroup S.O) ∣ 32 := by
  obtain ⟨l, hlL, hlinv⟩ := exists_mem_Lbar_inv hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus
    hPR hP9 hP3 hPn
  let N : Subgroup S.O := S14.Ct S t ⊓ normalizer (S.Lbar g : Set S.O)
  have hcardLbar : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  have hLbarP : S.Lbar g ⊓ P = ⊥ := by
    have h8 : Nat.card (S.Lbar g ⊓ P : Subgroup S.O) ∣ 8 := by
      simpa [hcardLbar] using
        Subgroup.card_dvd_of_le (inf_le_left : S.Lbar g ⊓ P ≤ S.Lbar g)
    have h9 : Nat.card (S.Lbar g ⊓ P : Subgroup S.O) ∣ 9 := by
      simpa [hP9] using Subgroup.card_dvd_of_le (inf_le_right : S.Lbar g ⊓ P ≤ P)
    have h1 : Nat.card (S.Lbar g ⊓ P : Subgroup S.O) ∣ 1 := by
      have := Nat.dvd_gcd h8 h9
      rwa [show Nat.gcd 8 9 = 1 by norm_num] at this
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h1)
  have hNP : N ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have hpN : p ∈ N := hp.1
    have hpP : p ∈ P := hp.2
    have hpNorm : p ∈ normalizer (S.Lbar g : Set S.O) := hpN.2
    have hp2L : p ^ 2 ∈ S.Lbar g := by
      have hmem1 : p * l * p⁻¹ ∈ S.Lbar g :=
        (Subgroup.mem_normalizer_iff.mp hpNorm l).mp hlL
      have hmem2 : l⁻¹ ∈ S.Lbar g := (S.Lbar g).inv_mem hlL
      have hprod : p * l * p⁻¹ * l⁻¹ ∈ S.Lbar g := (S.Lbar g).mul_mem hmem1 hmem2
      have hlp : l * p⁻¹ * l⁻¹ = p := by
        have h := hlinv p hpP
        calc l * p⁻¹ * l⁻¹ = (l * p * l⁻¹)⁻¹ := by group
          _ = (p⁻¹)⁻¹ := by rw [h]
          _ = p := inv_inv p
      have heq : p * l * p⁻¹ * l⁻¹ = p ^ 2 := by
        rw [show p * l * p⁻¹ * l⁻¹ = p * (l * p⁻¹ * l⁻¹) by group, hlp, pow_two]
      rwa [heq] at hprod
    have hp2P : p ^ 2 ∈ P := P.mul_mem hpP hpP
    have hp2 : p ^ 2 = 1 := by
      have hmem : p ^ 2 ∈ S.Lbar g ⊓ P := ⟨hp2L, hp2P⟩
      rw [hLbarP] at hmem
      simpa using hmem
    have hp3 : p ^ 3 = 1 := hP3 p hpP
    have hp1 : p = 1 := by
      have h : p ^ 3 = p := by rw [pow_succ, hp2, one_mul]
      rw [hp3] at h
      exact h.symm
    rw [hp1]
    exact Subgroup.one_mem _
  have hPC : P ≤ S14.Ct S t := hPR.trans (S8.Rbar_le_CMt H.conj_mem)
  have hPnorm : (P.subgroupOf (S14.Ct S t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hPn (g : S.O) g.2 (n : S.O) hn
  have hNCt : N ≤ S14.Ct S t := inf_le_left
  let φ : N →* (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) :=
    (QuotientGroup.mk' (P.subgroupOf (S14.Ct S t))).comp (Subgroup.inclusion hNCt)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hmem : (Subgroup.inclusion hNCt x)⁻¹ * (Subgroup.inclusion hNCt y) ∈
        P.subgroupOf (S14.Ct S t) :=
      QuotientGroup.eq.mp (show φ x = φ y from hxy)
    have hval : ((x : N) : S.O)⁻¹ * ((y : N) : S.O) ∈ P := by
      have h := Subgroup.mem_subgroupOf.mp hmem
      simpa [Subgroup.inclusion] using h
    let z : N := (x : N)⁻¹ * y
    have hzP : (z : S.O) ∈ P := by
      have hzval : (z : S.O) = ((x : N) : S.O)⁻¹ * ((y : N) : S.O) := rfl
      rw [hzval]
      exact hval
    have hmemN : (z : S.O) ∈ N ⊓ P := ⟨z.2, hzP⟩
    rw [hNP] at hmemN
    have hone : z = 1 := Subtype.ext (by simpa using hmemN)
    exact inv_mul_eq_one.mp (by simpa [z] using hone)
  have hcardN : Nat.card N = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
  have hcardCt := card_Ct_dvd H hNo C ht ht1 hVQ hΩ h4 hplus hK4
  have h9sub : Nat.card (P.subgroupOf (S14.Ct S t)) = 9 := by
    rw [← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hmul : Nat.card (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) *
      Nat.card (P.subgroupOf (S14.Ct S t)) ∣ 288 := by
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf (S14.Ct S t))]
    exact hcardCt
  have hquot : Nat.card (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) ∣ 32 := by
    rw [h9sub] at hmul
    have h288 : (288 : ℕ) = 32 * 9 := by norm_num
    rw [h288] at hmul
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hmul
  have hrange : Nat.card φ.range ∣ Nat.card (S14.Ct S t ⧸ P.subgroupOf (S14.Ct S t)) :=
    Subgroup.card_subgroup_dvd_card φ.range
  change Nat.card N ∣ 32
  rw [hcardN]
  exact hrange.trans hquot
end CFSG.GF2Type.Smith1979.OmegaPlus
