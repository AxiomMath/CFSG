module

public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Abs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Defs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53M
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L55B

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

section Apply

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS Blueprint
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem ivk73_apply_g4
    (h73 : IVK.IVK_7_3_g4) (hY : IsKGroupNative Y)
    (hgen : Gen4 Y)
    (hGH : ∀ L : Subgroup Y, IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) → GHList ↥L)
    (hO : pPrimeCore 2 Y = ⊥) {n : ℕ} (hn : n = 5 ∨ n = 7)
    (hord : n = 5 → ∀ R : Subgroup Y, IsPGroup 2 ↥R → Nat.card ↥R ≤ 2 ^ 6)
    {K Q : Subgroup Y} (eK : ↥K ≃* alternatingGroup (Fin n))
    (hQel : IsElementaryAbelian 2 ↥Q) (hQcard : Nat.card ↥Q = 4)
    (hQS : IsSylowOf 2 Q (centralizer (K : Set Y)))
    (hterm : ∀ u ∈ Q, orderOf u = 2 → IsCompIn (centralizer ({u} : Set Y)) K)
    (hns : ¬ IsComponent K) :
    ∃ e : Y ≃* alternatingGroup (Fin (n + 4)), K.map e.toMonoidHom = stdAlt n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimpA : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
  have hKs : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hKnsolv : ¬ Group.IsSolvable ↥K := fun hs =>
    alt_not_isSolvable n hn (Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective)
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hKnsolv ((IsSimpleGroup.comm_iff_isSolvable (G := ↥K)).1 h)
  obtain ⟨hKq, hKcen⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥K) hnc
  have hcardK : Nat.card ↥K = Nat.factorial n / 2 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card]
    rcases hn with rfl | rfl
    · rw [card_alternatingGroup]; simp
    · rw [card_alternatingGroup]; simp
  have hev : 2 ∣ Nat.card ↥K := by
    rw [hcardK]
    rcases hn with rfl | rfl <;> norm_num [Nat.factorial]
  have hOK : pPrimeCore 2 ↥K = ⊥ := CFSG.Walter.pPrimeCore_eq_bot_of_isSimpleGroup hnc
  let eKb : ↥K ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOK.symm)
  have hcardKb : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = Nat.card ↥K := (Nat.card_congr eKb.toEquiv).symm
  have hcenterKb : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ := by
    rw [← Subgroup.map_center_eq eKb, hKcen, Subgroup.map_bot]
  have hrank : 2 ≤ pRank 2 ↥Q := by
    have h := C3.Layer1.Back.card_eq_two_pow_pRank hQel
    rw [hQcard] at h
    have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥Q := by simpa using h
    have h3 := Nat.pow_right_injective le_rfl h2
    omega
  obtain ⟨u, huQ, v, hvQ, hu2, hv2, hne, hcomm⟩ := C3.Layer1.U1a.exists_commuting_involutions hrank
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  have hvv : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, pow_two] at this
  have hw2 : orderOf (u * v) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (u * v) ^ 2 = u * v * (u * v) := sq _
        _ = u * (v * u) * v := by simp only [mul_assoc]
        _ = u * (u * v) * v := by rw [← hcomm]
        _ = (u * u) * (v * v) := by simp only [mul_assoc]
        _ = 1 := by rw [huu, hvv, one_mul]
    · intro h
      apply hne
      have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact (inv_eq_of_mul_eq_one_right hvv).symm ▸ rfl
  have huvQ : u * v ∈ Q := Q.mul_mem huQ hvQ
  have hKP := fun (b : Y) (hb : b ∈ Q) (hb2 : orderOf b = 2) =>
    TwoThin.isPCompIn_two_iff.mp (isPCompIn_two_of_isCompIn_of_even (hterm b hb hb2) hev)
  obtain ⟨L, hLc, hKL⟩ := EvenCore.exists_component_ge_of_fourGroup hO hu2 hv2 hcomm hne
    (hKP u huQ hu2) (hKP v hvQ hv2) (hKP (u * v) huvQ hw2)
  have hne' : K ≠ L := fun h => hns (by rw [h]; exact hLc)
  obtain ⟨hLn, hLs, hLC⟩ := ivk73_socle hO hKq hQS hterm hLc hKL hne'
  have hterm_all : ∀ y ∈ (⊤ : Subgroup Y), orderOf y = 2 → y ∈ centralizer (K : Set Y) →
      IsCompIn (centralizer ({y} : Set Y) ⊓ (⊤ : Subgroup Y)) K := by
    intro y _ hy2 hyC
    obtain ⟨c, hc, hcQ⟩ := EvenCore.exists_conj_mem_Q hQS hyC hy2
    have hu2' : orderOf (c⁻¹ * y * c) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) y
      simpa [MulAut.conj_apply] using this.trans hy2
    have h1 := isCompIn_centralizer_conj hc (hterm _ hcQ hu2')
    have hcc : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
    rw [hcc] at h1
    rwa [inf_top_eq]
  have hU2 : InU2 (↥K ⧸ pPrimeCore 2 ↥K) := by
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eKb hKq, ?_⟩
    rcases hn with h5 | h7
    · subst h5
      exact Or.inl (TwoThin.hasL2Model_of_mulEquiv eKb
        ⟨5, 1, by norm_num, le_rfl, by decide, E2.lieModel_psl_two_five_of_alt ⟨eK⟩⟩)
    · subst h7
      exact Or.inr (Or.inl ⟨eKb.symm.trans eK⟩)
  obtain ⟨-, -, hcases⟩ := h73 Y ⊤ L K Q (Gen4.of_mulEquiv Subgroup.topEquiv.symm hgen)
    (hGH L hLs (IVK.exists_noncomm_of_le_isQuasisimple hKL hKq))
    (SectionRank.IsKGroupCat.of_mulEquiv hY Subgroup.topEquiv)
    ⟨le_top, fun n _ l hl => hLn.conj_mem l hl n, hLs, fun n _ hn => hLC n hn⟩ hKL hKq hU2
    (by rwa [inf_top_eq]) hrank hterm_all
  have hn5 : ∀ {X : Type} [Group X], Nonempty (X ≃* alternatingGroup (Fin 5)) →
      Nat.card X = 60 := fun {X} _ ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  have h5of : Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 5)) → n = 5 := by
    intro hA5
    have h60 := hn5 hA5
    rw [hcardKb, hcardK] at h60
    rcases hn with rfl | rfl
    · rfl
    · simp [Nat.factorial] at h60
  rcases hcases with ⟨hA5, hM, hN⟩ | ⟨hA5, hJ, hN⟩ | ⟨hNL, m, hm, hAm, hLm⟩ | ⟨hL34, hcen, -⟩ |
    ⟨hL34, -, hc4, -⟩
  · exfalso
    have h5 := h5of hA5
    have hcL := CFSG.GH74.card_of_isSporadic_M12 hM
    rw [Subgroup.card_top, hcL] at hN
    have hdvd : 2 ^ 7 ∣ Nat.card Y := by rw [hN]; norm_num
    obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    have := hord h5 R (IsPGroup.of_card hR)
    rw [hR] at this
    norm_num at this
  · exfalso
    have h5 := h5of hA5
    have hcL := CFSG.GH74.card_of_isSporadic_J2 hJ
    have hdvd : 2 ^ 7 ∣ Nat.card Y :=
      (show 2 ^ 7 ∣ Nat.card ↥L by rw [hcL]; norm_num).trans (Subgroup.card_subgroup_dvd_card L)
    obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    have := hord h5 R (IsPGroup.of_card hR)
    rw [hR] at this
    norm_num at this
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    obtain ⟨eAm⟩ := hAm
    have hcm : Nat.card ↥K = Nat.factorial m / 2 := by
      rw [← hcardKb, Nat.card_congr eAm.toEquiv, Nat.card_eq_fintype_card]
      rcases hm with rfl | rfl | rfl <;> (rw [card_alternatingGroup]; simp)
    have hnm : n = m := by
      rw [hcardK] at hcm
      rcases hn with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;>
        first | rfl | (exfalso; simp [Nat.factorial] at hcm)
    subst hnm
    obtain ⟨eL⟩ := hLm
    let e0 : Y ≃* alternatingGroup (Fin (n + 4)) :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hNL).trans eL)
    let K' : Subgroup (alternatingGroup (Fin (n + 4))) := K.map e0.toMonoidHom
    have eK' : ↥K' ≃* alternatingGroup (Fin n) := (e0.subgroupMap K).symm.trans eK
    have hu2' : orderOf (e0 u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu2
    have hKu : ∀ k ∈ K', k * e0 u = e0 u * k := by
      rintro _ ⟨k, hk, rfl⟩
      have h1 : k * u = u * k := (mem_centralizer_iff.1 (hQS.le huQ)) k hk
      show e0 k * e0 u = e0 u * e0 k
      rw [← map_mul, ← map_mul, h1]
    obtain ⟨σ, hσ⟩ := exists_conj_stdAlt hn K' eK' hu2' hKu
    refine ⟨e0.trans (conjA σ), ?_⟩
    rw [← hσ, Subgroup.map_map]
    rfl
  · exfalso
    have h1 := GLS.card_eq_of_lieModel_L34 hL34
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥K ⧸ pPrimeCore 2 ↥K))
    rw [h1, hcen, Subgroup.card_bot, mul_one, hcardKb, hcardK] at h2
    rcases hn with rfl | rfl <;> simp [Nat.factorial] at h2
  · exfalso
    rw [hcenterKb, Subgroup.card_bot] at hc4
    omega

end Apply

end CFSG.GH74.GLS.C3.Layer1.Bk
