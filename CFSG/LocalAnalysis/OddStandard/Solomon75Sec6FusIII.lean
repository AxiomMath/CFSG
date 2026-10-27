module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Fusion
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin Sec6Fus

open scoped commutatorElement

namespace Sec6FusIIIProof

variable {X : Type} [Group X] [Finite X]

private theorem eq_top_of_isPComponent {G : Type} [Group G] [Finite G] (hG : IsQuasisimple G)
    {K : Subgroup G} (hK : IsPComponent 2 K) : K = ⊤ := by
  obtain ⟨hsub, hq⟩ := isPComponent_two_iff.1 hK
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hG hsub with h | h
  · exact h
  · exfalso
    refine not_commutator_le_of_odd hq (R := ⊥) (by simp) ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 (h ha) b).symm

private theorem isDoubleCoverOfAlt_of_witness
    {n : ℕ} {L J : Subgroup X} {v : X} (hT : IsSec6MType n (↥L ⧸ pPrimeCore 2 ↥L)) (hvL : v ∈ L)
    (hv : orderOf v = 2) (hJ : IsAhatIntr X v J) (hJcov : J ≤ (L ⊓ cen v) ⊔ oddCoreOf (cen v)) :
    IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJC, -, hJpc, -⟩ := hJ
  obtain ⟨J', hJ'CL, hJ'pc, -, -, ⟨q₁⟩⟩ := exists_isPComponent_inf_of_covered
    (C := cen v) (H := L) (O := oddCoreOf (cen v)) (E := L ⊓ cen v) (J := J)
    (oddCoreOf_le _) (le_normalizer_oddCoreOf _) (odd_card_oddCoreOf _) inf_le_right inf_le_left
    hJC hJpc hJcov
  have hJ'C : J' ≤ cen v := hJ'CL.trans inf_le_left
  have hJ'L : J' ≤ L := hJ'CL.trans inf_le_right
  set v' : ↥L := ⟨v, hvL⟩ with hv'def
  have hY : centralizer ({v'} : Set ↥L) = (cen v).subgroupOf L :=
    centralizer_singleton_subgroup hvL
  have hJ''Y : J'.subgroupOf L ≤ centralizer ({v'} : Set ↥L) := by
    rw [hY]
    exact Subgroup.subgroupOf_mono L hJ'C
  have hJ''pc : IsPComponent 2 ((J'.subgroupOf L).subgroupOf (centralizer ({v'} : Set ↥L))) := by
    rw [hY]
    exact (isPComponent_subgroupOf_subgroupOf_iff hJ'C hJ'L).2 hJ'pc
  set π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' (pPrimeCore 2 ↥L)
  have hker : ¬ 2 ∣ Nat.card π.ker :=
    CFSG.ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker
  have hv'2 : v' * v' = 1 := by
    apply Subtype.ext
    show v * v = 1
    rw [← sq, ← hv]
    exact pow_orderOf_eq_one v
  have hCeq : centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L)) =
      (centralizer ({v'} : Set ↥L)).map π :=
    CFSG.ComponentClassification.GSThmB.OddQuot.centralizer_singleton_map_eq hv'2
  have hK := CFSG.ComponentClassification.GSThmB.OddQuot.isPComponent_map π hker hJ''Y hJ''pc
  rw [← hCeq] at hK
  have hπv : orderOf (π v') = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, hv'2, map_one]
    · intro h1
      have hmem : v' ∈ pPrimeCore 2 ↥L := (QuotientGroup.eq_one_iff v').1 h1
      have h3 := Subgroup.orderOf_dvd_natCard _ hmem
      have h4 : orderOf v' = 2 := by
        rw [hv'def, Subgroup.orderOf_mk]
        exact hv
      rw [h4] at h3
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
        Nat.coprime_two_left.1 pPrimeCore_coprime_card
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  have hC : IsDoubleCoverOfAlt ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) n := by
    rcases hT with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, h2, h3⟩ :=
        CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate
          he hπv
      exact isDoubleCoverOfAlt_of_cover hπv (by norm_num) h1 h2 h3
    · obtain ⟨h1, h2, h3⟩ :=
        CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple he (π v') hπv
      exact ⟨h1, h2, h3⟩
  have htop : ((J'.subgroupOf L).map π).subgroupOf
      (centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) = ⊤ :=
    eq_top_of_isPComponent hC.1 hK
  have hmapC : (J'.subgroupOf L).map π = centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L)) := by
    refine le_antisymm ?_ (Subgroup.subgroupOf_eq_top.1 htop)
    rw [hCeq]
    exact Subgroup.map_mono hJ''Y
  obtain ⟨q₂⟩ :=
    CFSG.ComponentClassification.GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv π hker
      (J'.subgroupOf L)
  obtain ⟨q₃⟩ := nonempty_quotPPrimeCore_equiv (MulEquiv.subgroupCongr hmapC)
  obtain ⟨q₅⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ'L)
  have hbot := pPrimeCore_eq_bot_of_doubleCover hC
  let q₄ : ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) ⧸
      pPrimeCore 2 ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) ≃*
      ↥(centralizer ({π v'} : Set (↥L ⧸ pPrimeCore 2 ↥L))) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact isDoubleCoverOfAlt_congr' (q₁.symm.trans (q₅.symm.trans (q₂.trans (q₃.trans q₄)))).symm hC

private theorem mem_QOf_witness {F J : Subgroup X} {y s : X} (hyF : y ∈ normalizer (F : Set X))
    (hys : y ∈ cen s) (hq : y * s⁻¹ ∈ QOf F) (hJC : J ≤ cen s)
    (hJpc : IsPComponent 2 (J.subgroupOf (cen s)))
    (hJcov : J ≤ (F ⊓ cen s) ⊔ oddCoreOf (cen s)) : y ∈ QOf J := by
  set W : Subgroup X := oddCoreOf (cen s) ⊔ (oddCoreOf F ⊓ cen s)
  set Y : Subgroup X := J ⊔ W with hY
  have hWC : W ≤ cen s := sup_le (oddCoreOf_le _) inf_le_right
  have hYC : Y ≤ cen s := sup_le hJC hWC
  have hJY : J ≤ Y := le_sup_left
  have hWY : W ≤ Y := le_sup_right
  have hFCn : F ⊓ cen s ≤ normalizer (W : Set X) := fun c hc =>
    mem_normalizer_sup (le_normalizer_oddCoreOf _ hc.2)
      (mem_normalizer_inf (le_normalizer_oddCoreOf F hc.1) (Subgroup.le_normalizer hc.2))
  have hWn : W ≤ normalizer (W : Set X) := Subgroup.le_normalizer
  have hJn : J ≤ normalizer (W : Set X) :=
    hJcov.trans (sup_le hFCn ((le_sup_left : oddCoreOf (cen s) ≤ W).trans hWn))
  have hYn : Y ≤ normalizer (W : Set X) := sup_le hJn hWn
  have hWodd : Odd (Nat.card W) := by
    have h1 := card_sup_mul_card_inf (A := oddCoreOf (cen s)) (B := oddCoreOf F ⊓ cen s)
      (fun c hc => le_normalizer_oddCoreOf _ hc.2)
    have h2 : Odd (Nat.card (oddCoreOf (cen s)) * Nat.card ↥(oddCoreOf F ⊓ cen s)) :=
      (odd_card_oddCoreOf _).mul
        ((odd_card_oddCoreOf F).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [← h1] at h2
    exact (Nat.odd_mul.1 h2).1
  have hWO : W ≤ oddCoreOf Y := le_oddCoreOf_of_normalized hWY hYn hWodd
  have hJYpc : IsPCompIn 2 Y J := ⟨hJY, isPComponent_subgroupOf_mono hJY hYC hJpc⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = y * s⁻¹ := ⟨_, rfl⟩
  rw [← hqdef] at hq
  have hyqs : y = q * s := by rw [hqdef]; group
  have hcomm : ∀ j ∈ J, ⁅j, y⁆ ∈ W := by
    intro j hj
    obtain ⟨c, hc, o, ho, rfl⟩ := exists_mul_of_mem_sup
      (fun c hc => le_normalizer_oddCoreOf (cen s) (Subgroup.mem_inf.1 hc).2) (hJcov hj)
    have hcF : c ∈ F := (Subgroup.mem_inf.1 hc).1
    have hcs' : c ∈ cen s := (Subgroup.mem_inf.1 hc).2
    have hcs : c * s = s * c := Subgroup.mem_centralizer_singleton_iff.1 hcs'
    have hsc : s * c⁻¹ * s⁻¹ = c⁻¹ := by
      calc s * c⁻¹ * s⁻¹ = c⁻¹ * (c * s) * c⁻¹ * s⁻¹ := by group
        _ = c⁻¹ * (s * c) * c⁻¹ * s⁻¹ := by rw [hcs]
        _ = c⁻¹ := by group
    have h1 : ⁅c, y⁆ = ⁅c, q⁆ := by
      rw [hyqs, commutatorElement_def, commutatorElement_def]
      calc c * (q * s) * c⁻¹ * (q * s)⁻¹ = c * q * (s * c⁻¹ * s⁻¹) * q⁻¹ := by group
        _ = c * q * c⁻¹ * q⁻¹ := by rw [hsc]
    have h2 : ⁅c, y⁆ ∈ oddCoreOf F ⊓ cen s := by
      refine Subgroup.mem_inf.2 ⟨h1 ▸ (mem_QOf_iff.1 hq).2 c hcF, ?_⟩
      rw [commutatorElement_def]
      exact (cen s).mul_mem ((cen s).mul_mem ((cen s).mul_mem hcs' hys) ((cen s).inv_mem hcs'))
        ((cen s).inv_mem hys)
    have h3 : c * ⁅o, y⁆ * c⁻¹ ∈ oddCoreOf (cen s) := by
      have h4 : ⁅o, y⁆ ∈ oddCoreOf (cen s) := by
        have h5 : y * o⁻¹ * y⁻¹ ∈ oddCoreOf (cen s) :=
          (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ hys) _).1 (inv_mem ho)
        have e : ⁅o, y⁆ = o * (y * o⁻¹ * y⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ho h5
      exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ hcs') _).1 h4
    have e : ⁅c * o, y⁆ = (c * ⁅o, y⁆ * c⁻¹) * ⁅c, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact W.mul_mem (le_sup_left (b := oddCoreOf F ⊓ cen s) h3)
      (le_sup_right (a := oddCoreOf (cen s)) h2)
  have hyW : y ∈ normalizer (W : Set X) :=
    mem_normalizer_sup (le_normalizer_oddCoreOf _ hys)
      (mem_normalizer_inf (mem_normalizer_oddCoreOf_of_mem_normalizer hyF)
        (Subgroup.le_normalizer hys))
  have hyY : y ∈ normalizer (Y : Set X) := by
    have hle : Y.map (MulAut.conj y).toMonoidHom ≤ Y := by
      rw [hY, Subgroup.map_sup, map_conj_eq_of_mem_normalizer hyW]
      refine sup_le ?_ le_sup_right
      rintro _ ⟨j, hj, rfl⟩
      have e : (MulAut.conj y).toMonoidHom j = j * ⁅j⁻¹, y⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem_sup hj (hcomm _ (J.inv_mem hj))
    have hcard : Nat.card (Y.map (MulAut.conj y).toMonoidHom) = Nat.card Y :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    exact mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  exact normalizes_isPCompIn_of_comm_mem hJYpc hyY fun j hj => hWO (hcomm j hj)

private theorem mem_sec6K_cen_of_mem_QOf
    {n : ℕ} (hK : Sec6Lemma51 X n) {H F : Subgroup X} (hF : Sec6MComp X n H F) {y s : X}
    (hy : orderOf y = 2) (hs : orderOf s = 2) (hsF : s ∈ F) (hsy : s ∈ cen y)
    (hyF : y ∈ normalizer (F : Set X)) (hq : y * s⁻¹ ∈ QOf F) : s ∈ Sec6K X n (cen y) := by
  have hy2 : y ^ 2 = 1 := sq_eq_one_of_orderOf hy
  have hs2 : s ^ 2 = 1 := sq_eq_one_of_orderOf hs
  have hys : y ∈ cen s := Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 hsy).symm
  obtain ⟨J, hJ, hJcov⟩ := hF.1.2.2 s hsF hs
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n :=
    isDoubleCoverOfAlt_of_witness hF.2 hsF hs hJ hJcov
  have hJ5 : Sec5Comp X n (cen s) J := ⟨⟨s, hJ.isIntrinsicIn hs⟩, hJn⟩
  have hyJ : y ∈ QOf J := mem_QOf_witness hyF hys hq hJ.1 hJ.2.2.1 hJcov
  have hres := sec5Comp_restrict hJ5 hy2 hyJ
  have hsD : s ∈ oTwoPrimeOf (J ⊓ cen y) :=
    mem_oTwoPrimeOf ⟨hJ.2.1, hsy⟩ 1 (by simpa using hs2)
  have h1 : oTwoPrimeOf (J ⊓ cen y) ≤ Sec6K X n (cen s ⊓ cen y) := le_sSup (Or.inl hres)
  exact (hK.sub y hy (cen s ⊓ cen y) inf_le_right).1 (h1 hsD)

private theorem exists_sq_eq_one_of_mul_inv_mem_QOf {F : Subgroup X}
    (hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥) {y f : X} (hy2 : y ^ 2 = 1) (hf : f ∈ F)
    (hq : y * f⁻¹ ∈ QOf F) : ∃ s ∈ F, s ∈ cen y ∧ s ^ 2 = 1 ∧ s⁻¹ * f ∈ oddCoreOf F := by
  set O := oddCoreOf F
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreOf F
  have hOF : O ≤ F := oddCoreOf_le F
  have hFnO : F ≤ normalizer (O : Set X) := le_normalizer_oddCoreOf F
  have hconjO' : ∀ {g o : X}, g ∈ normalizer (O : Set X) → o ∈ O → g⁻¹ * o * g ∈ O :=
    fun hg ho => by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) _).1 ho
      rwa [inv_inv] at this
  obtain ⟨q, hqdef⟩ : ∃ q, q = y * f⁻¹ := ⟨_, rfl⟩
  rw [← hqdef] at hq
  have hyqf : y = q * f := by rw [hqdef]; group
  have hqN : q ∈ normalizer (F : Set X) := (mem_QOf_iff.1 hq).1
  have hqO : q ∈ normalizer (O : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hqN
  have hqc : ∀ a ∈ F, ⁅a, q⁆ ∈ O := (mem_QOf_iff.1 hq).2
  have ho1 : ⁅f, q⁆ ∈ O := hqc f hf
  have hr2 : q * f * (q * f) = 1 := by rw [← hyqf, ← sq]; exact hy2
  have hq2 : q * q = f⁻¹ * ⁅f, q⁆ * f⁻¹ := by
    have h1 : f * q * f * q = 1 := by
      calc f * q * f * q = q⁻¹ * (q * f * (q * f)) * q := by group
        _ = 1 := by rw [hr2]; group
    have hfqf : f * q * f = q⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [commutatorElement_def]
    calc q * q = q * f⁻¹ * (f * q * f) * f⁻¹ := by group
      _ = q * f⁻¹ * q⁻¹ * f⁻¹ := by rw [hfqf]
      _ = f⁻¹ * (f * q * f⁻¹ * q⁻¹) * f⁻¹ := by group
  have hq2F : q * q ∈ F := by
    rw [hq2]
    exact F.mul_mem (F.mul_mem (F.inv_mem hf) (hOF ho1)) (F.inv_mem hf)
  have hq2O : q * q ∈ O := zStar_le_oddCoreOf_of_center hZ ⟨hq2F, (QOf F).mul_mem hq hq⟩
  have hf2 : f * f ∈ O := by
    have h1 : f⁻¹ * ⁅f, q⁆ * f⁻¹ ∈ O := hq2 ▸ hq2O
    have h2 : f⁻¹ * ⁅f, q⁆ * f ∈ O := hconjO' (hFnO hf) ho1
    have h3 : (f * f)⁻¹ = (f⁻¹ * ⁅f, q⁆ * f)⁻¹ * (f⁻¹ * ⁅f, q⁆ * f⁻¹) := by group
    have h4 : (f * f)⁻¹ ∈ O := h3 ▸ O.mul_mem (O.inv_mem h2) h1
    have h5 := O.inv_mem h4
    rwa [inv_inv] at h5
  have hyO : y ∈ normalizer (O : Set X) := by
    rw [hyqf]
    exact Subgroup.mul_mem _ hqO (hFnO hf)
  have hyy : y * y = 1 := by rw [← sq]; exact hy2
  have hcos : f⁻¹ * (y * f * y⁻¹) ∈ O := by
    have e : f⁻¹ * (y * f * y⁻¹) = ⁅f⁻¹, q⁆ := by
      rw [hyqf, commutatorElement_def]
      group
    rw [e]
    exact hqc _ (F.inv_mem hf)
  obtain ⟨o, ho, hfo⟩ := exists_mul_mem_cen_of_coset hOodd hyy hyO hcos
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = f * o := ⟨_, rfl⟩
  rw [← hs₀] at hfo
  have hs₀F : s₀ ∈ F := by
    rw [hs₀]
    exact F.mul_mem hf (hOF ho)
  have hs₀2 : s₀ * s₀ ∈ O := by
    have e : s₀ * s₀ = (f * f) * (f⁻¹ * o * f) * o := by
      rw [hs₀]
      group
    rw [e]
    exact O.mul_mem (O.mul_mem hf2 (hconjO' (hFnO hf) ho)) ho
  have hs₀f : s₀⁻¹ * f = o⁻¹ := by
    rw [hs₀]
    group
  obtain ⟨k, hk⟩ := hOodd
  have hs_eq : s₀ ^ Nat.card O = s₀ * (s₀ * s₀) ^ k := by
    rw [hk, pow_succ', ← sq, ← pow_mul]
  refine ⟨s₀ ^ Nat.card O, F.pow_mem hs₀F _, (cen y).pow_mem hfo _, ?_, ?_⟩
  · have h2 : (s₀ * s₀) ^ Nat.card O = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard O hs₀2)
    rw [← pow_mul, mul_comm, pow_mul, sq]
    exact h2
  · rw [hs_eq, mul_inv_rev, mul_assoc, hs₀f]
    exact O.mul_mem (O.inv_mem (O.pow_mem hs₀2 k)) (O.inv_mem ho)

private theorem sec6R_le_QOf {n : ℕ}
    {N A : Subgroup X} (hA : Sec5Comp X n N A) : Sec6R X n N ≤ QOf A := by
  have hApc : IsPCompIn 2 N A := isPCompIn_of_sec6KComp (Or.inl hA)
  have hAK : A ≤ K0 X n N := le_sSup hA
  have hKnA : K0 X n N ≤ normalizer (A : Set X) :=
    sSup_le_normalizer hApc fun J hJ => isPCompIn_of_sec6KComp (Or.inl hJ)
  have hle : A ⊓ oddCoreOf (K0 X n N) ≤ oddCoreOf A := by
    refine le_oddCoreOf_of_normalized inf_le_left (fun a ha => ?_) ?_
    · exact mem_normalizer_inf (Subgroup.le_normalizer ha)
        (le_normalizer_oddCoreOf _ (hAK ha))
    · exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_right)
  refine sup_le ?_ (sSup_le fun M hM => le_QOf_of_ne hApc hM.1.1
    (ne_of_sec5Comp_of_sec6MComp mcLLyCenterFree hA hM))
  rintro z ⟨hzK, -, -, hz⟩
  have hzA : z ∈ normalizer (A : Set X) := hKnA hzK
  refine mem_QOf_iff.2 ⟨hzA, fun a ha => hle ⟨?_, hz a (hAK ha)⟩⟩
  have h1 : z * a⁻¹ * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hzA _).1 (A.inv_mem ha)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc z]
  exact A.mul_mem ha h1

private theorem mem_of_mem_sSup {n : ℕ} {N P : Subgroup X} {y : X}
    (hA : ∀ G, Sec5Comp X n N G → G ≤ P)
    (hM : ∀ F, Sec6MComp X n N F → ∀ f ∈ F, y * f⁻¹ ∈ QOf F → f ∈ P) :
    ∀ S : Finset (Subgroup X), (∀ F ∈ S, Sec6KComp X n N F) →
      ∀ w ∈ sSup (S : Set (Subgroup X)), (∀ F ∈ S, y * w⁻¹ ∈ QOf F) → w ∈ P := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ w hw _
    rw [Finset.coe_empty, sSup_empty, Subgroup.mem_bot] at hw
    rw [hw]
    exact P.one_mem
  | insert F S hFS ih =>
    intro hS w hw hwQ
    have hF := hS F (Finset.mem_insert_self F S)
    have hS' : ∀ G ∈ S, Sec6KComp X n N G := fun G hG => hS G (Finset.mem_insert_of_mem hG)
    have hFpc := isPCompIn_of_sec6KComp hF
    have hSN : sSup (S : Set (Subgroup X)) ≤ normalizer (F : Set X) :=
      sSup_le_normalizer hFpc fun G hG => isPCompIn_of_sec6KComp (hS' G hG)
    have hSQ : sSup (S : Set (Subgroup X)) ≤ QOf F := sSup_le fun G hG =>
      le_QOf_of_ne hFpc (isPCompIn_of_sec6KComp (hS' G hG)) fun h => hFS (h ▸ hG)
    rw [Finset.coe_insert, sSup_insert, sup_comm] at hw
    obtain ⟨w', hw', f, hf, rfl⟩ := exists_mul_of_mem_sup hSN hw
    have hyf : y * f⁻¹ ∈ QOf F := by
      have h1 := (QOf F).mul_mem (hwQ F (Finset.mem_insert_self F S)) (hSQ hw')
      have e : y * (w' * f)⁻¹ * w' = y * f⁻¹ := by group
      rwa [e] at h1
    have hfP : f ∈ P := by
      rcases hF with hF5 | hF6
      · exact hA F hF5 hf
      · exact hM F hF6 f hf hyf
    have hw'P : w' ∈ P := by
      refine ih hS' w' hw' fun G hG => ?_
      have hGpc := isPCompIn_of_sec6KComp (hS' G hG)
      have hFQ : F ≤ QOf G := le_QOf_of_ne hGpc hFpc fun h => hFS (h ▸ hG)
      have hconj : w' * f * w'⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 (hSN hw') f).1 hf
      have h1 := (QOf G).mul_mem (hwQ G (Finset.mem_insert_of_mem hG)) (hFQ hconj)
      have e : y * (w' * f)⁻¹ * (w' * f * w'⁻¹) = y * w'⁻¹ := by group
      rwa [e] at h1
    exact P.mul_mem hw'P hfP

end Sec6FusIIIProof

open Sec6FusIIIProof

theorem sec6FusIII_of
    {X : Type} [Group X] [Finite X] {n : ℕ} (hK : Sec6Lemma51 X n) (N : Subgroup X) :
    Sec6FusIII X n N := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hyR hy
  have hy2 : y ^ 2 = 1 := sq_eq_one_of_orderOf hy
  have hyy : y * y = 1 := by rw [← sq]; exact hy2
  have hyN : y ∈ N := sec6R_le n N hyR
  have hA : ∀ G, Sec5Comp X n N G → G ≤ (Sec6K X n (cen y) ⊓ N) ⊔ oddCoreOf N := by
    intro G hG
    have hyG : y ∈ QOf G := sec6R_le_QOf hG hyR
    have hGpc : IsPCompIn 2 N G := isPCompIn_of_sec6KComp (Or.inl hG)
    obtain ⟨-, hcov⟩ := isPCompIn_restrict hGpc hy2 hyG
    have hDG : oTwoPrimeOf (G ⊓ cen y) ≤ G := (oTwoPrimeOf_le _).trans inf_le_left
    have hDK : oTwoPrimeOf (G ⊓ cen y) ≤ Sec6K X n (cen y) := by
      have h1 : oTwoPrimeOf (G ⊓ cen y) ≤ Sec6K X n (N ⊓ cen y) :=
        le_sSup (Or.inl (sec5Comp_restrict hG hy2 hyG))
      exact h1.trans (hK.sub y hy (N ⊓ cen y) inf_le_right).1
    have hGeq := (covers_subgroupOf_iff hDG).1 hcov
    exact hGeq.ge.trans (sup_le_sup (le_inf hDK (hDG.trans hGpc.1))
      (pPrimeCoreOf_le_oddCoreOf hGpc.1 (isPComponent_two_iff.1 hGpc.2).1))
  have hM : ∀ F, Sec6MComp X n N F → ∀ f ∈ F, y * f⁻¹ ∈ QOf F →
      f ∈ (Sec6K X n (cen y) ⊓ N) ⊔ oddCoreOf N := by
    intro F hF f hf hq
    have hZ : center (↥F ⧸ pPrimeCore 2 ↥F) = ⊥ := mcLLyCenterFree _ hF.1.2.1
    obtain ⟨s, hsF, hsy, hs2, hsf⟩ := exists_sq_eq_one_of_mul_inv_mem_QOf hZ hy2 hf hq
    have hFN : F ≤ N := hF.1.1.1
    have hOFN : oddCoreOf F ≤ oddCoreOf N :=
      pPrimeCoreOf_le_oddCoreOf hFN (isPComponent_two_iff.1 hF.1.1.2).1
    have hsK : s ∈ Sec6K X n (cen y) := by
      by_cases hs1 : s = 1
      · rw [hs1]
        exact one_mem _
      have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
      have hyF : y ∈ normalizer (F : Set X) := by
        have h1 : y * f⁻¹ * f ∈ normalizer (F : Set X) :=
          Subgroup.mul_mem _ (mem_QOf_iff.1 hq).1 (Subgroup.le_normalizer hf)
        rwa [inv_mul_cancel_right] at h1
      have hq' : y * s⁻¹ ∈ QOf F := by
        have h1 : f * (s⁻¹ * f) * f⁻¹ ∈ oddCoreOf F :=
          (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf F hf) _).1 hsf
        have h2 := (QOf F).mul_mem hq (oddCoreOf_le_QOf F h1)
        have e : y * f⁻¹ * (f * (s⁻¹ * f) * f⁻¹) = y * s⁻¹ := by group
        rwa [e] at h2
      exact mem_sec6K_cen_of_mem_QOf hK hF hy hso hsF hsy hyF hq'
    have e : f = s * (s⁻¹ * f) := by group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hsK, hFN hsF⟩ (hOFN hsf)
  have hRK : Sec6R X n N ≤ Sec6K X n N := by
    rw [sec6K_eq]
    exact sup_le ((zStar_le _).trans le_sup_left) le_sup_right
  have hfin : {F | Sec6KComp X n N F}.Finite := Set.toFinite _
  have hcov : y ∈ (Sec6K X n (cen y) ⊓ N) ⊔ oddCoreOf N := by
    refine mem_of_mem_sSup hA hM hfin.toFinset (fun F hF => hfin.mem_toFinset.1 hF) y ?_
      fun F _ => ?_
    · rw [hfin.coe_toFinset]
      exact hRK hyR
    · rw [mul_inv_cancel]
      exact one_mem _
  obtain ⟨o, ho, a, haP, ha2, hya⟩ := exists_conj_twoElt_of_mem_sup_odd_X
    (fun c hc => le_normalizer_oddCoreOf N (Subgroup.mem_inf.1 hc).2) (odd_card_oddCoreOf N) hcov
    (j := 1) (by simpa using hy2)
  have haK : a ∈ Sec6K X n (cen y) := (Subgroup.mem_inf.1 haP).1
  have hay : a * y = y * a := Subgroup.mem_centralizer_singleton_iff.1 (sec6K_le n (cen y) haK)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have haa : a * a = 1 := by
    rw [← sq]
    simpa using ha2
  have ha : a = o⁻¹ * y * o := by
    rw [hya]
    group
  have h1 : y⁻¹ * a ∈ oddCoreOf N := by
    have h2 : y⁻¹ * o⁻¹ * y⁻¹⁻¹ ∈ oddCoreOf N :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf N (N.inv_mem hyN)) o⁻¹).1
        (inv_mem ho)
    rw [inv_inv] at h2
    have e : y⁻¹ * a = y⁻¹ * o⁻¹ * y * o := by
      rw [ha]
      group
    rw [e]
    exact mul_mem h2 ho
  have h3 : (y⁻¹ * a) ^ (2 ^ 1) = 1 := by
    rw [pow_one, sq, hyinv]
    calc y * a * (y * a) = y * (a * y) * a := by group
      _ = y * (y * a) * a := by rw [hay]
      _ = (y * y) * (a * a) := by group
      _ = 1 := by rw [hyy, haa, one_mul]
  have h4 := eq_one_of_pow_two_pow_of_mem_odd_subgroup (odd_card_oddCoreOf N) h1 h3
  have hya' : y = a := inv_mul_eq_one.1 h4
  rw [← hya'] at haK
  exact haK

end CFSG.OddStandard.Solomon75
