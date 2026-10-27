module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTits
import CFSG.Adapters.CatalogueFieldBridges.Linear
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
open CFSG.StandardType.TitsOvergroup CFSG.StandardType.TitsThree CFSG.StandardType.TitsGenerators
open CFSG.StandardType.SylowPair
open CFSG.Sporadic.Schreier.Tits (titsD)

section Tits

@[expose] def TitsThreeOvergroupShape (A : Type) [Group A] : Prop :=
  Nat.card A ∣ 11232 ∧
    (Nat.card A = 11232 → ∃ M : Subgroup A, M.Normal ∧ M.index = 2 ∧ IsSimpleGroup ↥M ∧
      IsPSLType 3 (ZMod 3) ↥M)

theorem TitsThreeOvergroupShape.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : TitsThreeOvergroupShape A) : TitsThreeOvergroupShape B := by
  have hcard : Nat.card A = Nat.card B := Nat.card_congr e.toEquiv
  refine ⟨hcard ▸ h.1, fun hB => ?_⟩
  obtain ⟨M, hMn, hMi, hMs, ⟨ePSL⟩⟩ := h.2 (hcard.trans hB)
  have eM : ↥M ≃* ↥(M.map e.toMonoidHom) := M.equivMapOfInjective e.toMonoidHom e.injective
  have := hMs
  refine ⟨M.map e.toMonoidHom, hMn.map _ e.surjective, ?_, eM.symm.isSimpleGroup,
    ⟨eM.symm.trans ePSL⟩⟩
  rw [Subgroup.index_map_of_bijective e.bijective]
  exact hMi

theorem card_zmod_three_threeFourTwoQThree : Nat.card (ZMod 3) = threeFourTwoQThree.card := by
  rw [Nat.card_eq_fintype_card, ZMod.card, threeFourTwoQThree, TauCeti.PrimePower.card_def]
  norm_num

theorem nonempty_catL33_mulEquiv_psl :
    Nonempty ((TauCeti.CFSGIndex.lie threeFourTwoL33Index).Group ≃* PSL(3, ZMod 3)) := by
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := 2) (k := ZMod 3) threeFourTwoQThree valid_A_two_threeFourTwoQThree
    card_zmod_three_threeFourTwoQThree
  exact ⟨e.symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      (ZMod 3)).symm⟩

theorem titsThreeOvergroupShape_of_pairP_le
    {Y : Subgroup (Equiv.Perm (Fin 1755))} (hPY : pairP pairData titsS ≤ Y) (hYG : Y ≤ titsD)
    (hY : Y ≠ titsD) : TitsThreeOvergroupShape ↥Y := by
  obtain ⟨k, hk, hYM⟩ := le_pairSide_of_pairP_le hPY hYG hY
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, -, -⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, -, -, -, hSide, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hcardL : Nat.card ↥(pairSide pairData titsS k) = 5616 :=
    (card_pairSide hS hSide (k := k) (by simp; omega)).trans (sideOrder_getD hk).1
  have hcardM : Nat.card ↥(pairSide pairData titsS (k + 2)) = 11232 :=
    (card_pairSide hS hSide (k := k + 2) (by simp; omega)).trans (sideOrder_getD hk).2
  refine ⟨hcardM ▸ Subgroup.card_dvd_of_le hYM, fun hcard => ?_⟩
  have hYeq : Y = pairSide pairData titsS (k + 2) :=
    Subgroup.eq_of_le_of_card_ge hYM (by rw [hcardM, hcard])
  subst hYeq
  have hLM : pairSide pairData titsS k ≤ pairSide pairData titsS (k + 2) :=
    pairSide_le_pairSide hk
  have eM : ↥((pairSide pairData titsS k).subgroupOf (pairSide pairData titsS (k + 2))) ≃*
      ↥(pairSide pairData titsS k) := Subgroup.subgroupOfEquivOfLe hLM
  have hMcard : Nat.card ↥((pairSide pairData titsS k).subgroupOf
      (pairSide pairData titsS (k + 2))) = 5616 := (Nat.card_congr eM.toEquiv).trans hcardL
  have hMidx : ((pairSide pairData titsS k).subgroupOf (pairSide pairData titsS (k + 2))).index =
      2 := by
    have h := ((pairSide pairData titsS k).subgroupOf
      (pairSide pairData titsS (k + 2))).card_mul_index
    rw [hMcard, hcardM] at h
    omega
  have := (isSimpleGroup_pairSide hc hk).1
  obtain ⟨e⟩ := nonempty_pairSide_mulEquiv_catL33 hk
  obtain ⟨e'⟩ := nonempty_catL33_mulEquiv_psl
  exact ⟨_, Subgroup.normal_of_index_eq_two hMidx, hMidx, eM.isSimpleGroup,
    ⟨eM.trans (e.trans e')⟩⟩

theorem titsThreeOvergroupShape_of_not_dvd_index
    {Y : Subgroup ↥titsD} (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) : TitsThreeOvergroupShape ↥Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, -, -⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, hP, -, -, -, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  have hPG : pairP pairData titsS ≤ titsD := hG ▸ pairP_le_pairG
  have hP27 : Nat.card ↥(pairP pairData titsS) = 3 ^ 3 := by
    rw [card_pairP hS hP]
    rfl
  have hD : Nat.card ↥titsD = 3 ^ 3 * 665600 := by
    rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
    norm_num
  let S : Sylow 3 ↥titsD := Sylow.ofCard ((pairP pairData titsS).subgroupOf titsD) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hP27]
    exact CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization hD (by norm_num))
  have hSdef : (S : Subgroup ↥titsD) = (pairP pairData titsS).subgroupOf titsD :=
    Sylow.coe_ofCard _ _
  refine CFSG.StandardType.SylowOvergroup.forall_of_sylow_le S (fun Y => TitsThreeOvergroupShape ↥Y)
    ?_ ?_ hY h3
  · intro g Y hY'
    exact hY'.of_mulEquiv
      (Y.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  · intro Y hSY hYtop
    have hinj := titsD.subtype_injective
    have hPY : pairP pairData titsS ≤ Y.map titsD.subtype := fun x hx =>
      ⟨⟨x, hPG hx⟩, hSY (by rw [hSdef]; exact hx), rfl⟩
    have hYne : Y.map titsD.subtype ≠ titsD := by
      intro heq
      apply hYtop
      have htop : (⊤ : Subgroup ↥titsD).map titsD.subtype = titsD := by
        rw [Subgroup.map_top titsD.subtype, Subgroup.range_subtype]
      exact (Subgroup.map_subtype_inj (H := titsD)).mp (heq.trans htop.symm)
    exact (titsThreeOvergroupShape_of_pairP_le hPY (Subgroup.map_subtype_le Y) hYne).of_mulEquiv
      (Y.equivMapOfInjective titsD.subtype hinj).symm

theorem threeNineThreeTits_holds :
    ThreeNineThreeTits := by
  intro X _ _ K E D X₁ d h hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  obtain ⟨φ⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥K 2 1 hK
  have hcardK : Nat.card ↥K = 17971200 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  have hZ : Subgroup.center ↥K = ⊥ := by
    have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ
    rw [CFSG.Sporadic.Schreier.Tits.titsD_center] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have hout : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer ↥K) := by
    intro q hq hq2 hdq
    have : Fact q.Prime := ⟨hq⟩
    have h2 := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier (G := ↥K) (p := 2) (f := 1)
      hK).1
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Outer ↥K) q hdq
    obtain ⟨k, hk⟩ := h2 x
    have h3 : q ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h3))
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := hout d h.d_prime h.d_ne_two
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ houtd
  obtain ⟨hYtop, hm3, hmd, h3Y, hdY, hdK⟩ :=
    h.index_facts hZ (hout 3 Nat.prime_three (by norm_num)) houtd
  rw [hcardK] at h3Y hdY hdK
  have hv3 : (3 : ℕ) ^ (17971200 : ℕ).factorization 3 = 3 ^ 3 :=
    (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 3) (k := 665600)
      (N := 17971200) (by norm_num) (by norm_num)).symm
  rw [hv3] at h3Y
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  rw [inf_eq_left.mpr hDK] at hDsylK
  have hDcard := hDsylK.card_eq
  rw [hcardK] at hDcard
  have hd513 : d = 5 ∨ d = 13 := by
    have hfac : (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp
          (h.d_prime.dvd_of_dvd_pow h1))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  set Y : Subgroup ↥K := X₁.subgroupOf K with hYdef
  have h3idx : ¬ 3 ∣ Y.index := by
    intro h3
    have := hm3
    unfold Nat.ModEq at this
    omega
  have hdata : TitsThreeOvergroupShape ↥Y :=
    CFSG.StandardType.SylowOvergroup.forall_of_mulEquiv (p := 3) φ
      (fun A _ => TitsThreeOvergroupShape A) (fun A B _ _ f hA => hA.of_mulEquiv f)
      (fun Y hY h3 => titsThreeOvergroupShape_of_not_dvd_index hY h3) Y hYtop h3idx
  rcases hd513 with rfl | rfl
  ·
    exfalso
    have hv5 : (5 : ℕ) ^ (17971200 : ℕ).factorization 5 = 5 ^ 2 :=
      (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 5) (a := 2)
        (k := 718848) (N := 17971200) (by norm_num) (by norm_num)).symm
    rw [hv5] at hdY
    have := hdY.trans hdata.1
    norm_num at this
  ·
    have hv13 : (13 : ℕ) ^ (17971200 : ℕ).factorization 13 = 13 ^ 1 :=
      (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 13) (a := 1)
        (k := 1382400) (N := 17971200) (by norm_num) (by norm_num)).symm
    rw [hv13] at hdY hDcard
    have h351 : 351 ∣ Nat.card Y :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 13) h3Y
        (by simpa using hdY)
    have hidx := Y.card_mul_index
    rw [hcardK] at hidx
    have hYcard : Nat.card Y = 11232 := by
      have hpos : 0 < Nat.card Y := Nat.card_pos
      have hqdiv : 17971200 / Nat.card Y = Y.index := Nat.div_eq_of_eq_mul_right hpos hidx.symm
      have key : ∀ n ∈ Nat.divisors 11232, 351 ∣ n → 17971200 / n ≡ 1 [MOD 3] →
          17971200 / n ≡ 1 [MOD 13] → n = 11232 := by
        decide +kernel
      exact key _ (Nat.mem_divisors.mpr ⟨hdata.1, by norm_num⟩) h351 (by rw [hqdiv]; exact hm3)
        (by rw [hqdiv]; exact hmd)
    have hX₁K : X₁ ≤ K := by
      have h1 := h.lt
      rw [sup_eq_left.mpr hDK] at h1
      exact h1.le
    have eY : ↥Y ≃* ↥X₁ := Subgroup.subgroupOfEquivOfLe hX₁K
    have hX1card : Nat.card ↥X₁ = 11232 := (Nat.card_congr eY.toEquiv).symm.trans hYcard
    obtain ⟨M, hMn, hMi, hMs, ⟨eM⟩⟩ := (hdata.of_mulEquiv eY).2 hX1card
    have := hMn
    have := hMs
    have hMcard : Nat.card ↥M = 5616 := by
      have h1 := M.card_mul_index
      rw [hX1card, hMi] at h1
      omega
    obtain ⟨e1⟩ := SporCent.nonempty_oPrimeModPrimeComplement_mulEquiv (G := X) (d := 13)
      (by norm_num) (Y := X₁) M (by rw [hMcard]; norm_num) (by rw [hMi]; norm_num)
    have hDc : Nat.card D = 13 := by
      rw [hDcard]
      rfl
    exact ⟨isCyclic_of_prime_card hDc, hDK, Or.inl ⟨rfl, rfl, hK, ⟨e1.trans eM⟩⟩⟩

end Tits

end CFSG.LocalAnalysis.AGL81I.Section3
