module

public import CFSG.LocalAnalysis.OddStandard.AltStdWeakExact
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupCons
public import CFSG.LocalAnalysis.OddStandard.AltStdWeakDich

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne

section HN

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem card_centralizer_le_of_HN (hHN : HNLocalComponentsInput)
    (hOut : SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput) {W : Subgroup X}
    [W.Normal] (h : WeakShape t A m) (hm : 9 ≤ m) (hAW : A ≤ W)
    (hCW : centralizer (W : Set X) = ⊥) (hWs : IsSimpleGroup W)
    (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hcomp : CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X)))
    (eHN : W ≃* NativeSporadic.HN) :
    Nat.card (centralizer ({t} : Set X)) ≤ 2 * Nat.factorial 10 := by
  have htW : t ∉ W := by
    intro htW
    obtain ⟨B, hB, ⟨φ⟩⟩ :=
      CFSG.ComponentClassification.RestrictedStd.exists_isComponent_centralizer_of_mem htW hAW
        hcomp
    have ht' : orderOf (⟨t, htW⟩ : W) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact h.order
    obtain ⟨eA⟩ := h.iso
    exact not_isLargeAlt_of_card_quotient (c := 44352000)
      (fun m' _ => lookup_factorial_div_two_ne (k := 11) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) m')
      (hHN W eHN _ ht' B hB) ⟨m, hm, ⟨φ.trans eA⟩⟩
  have hout : Nat.card (Outer W) ≤ 2 :=
    hOut .HN (Or.inr (Or.inr (Or.inl rfl))) W hWnab ⟨eHN⟩
  have hidx : W.index ≤ 2 := (index_le_card_outer W hCW).trans hout
  have hσ2 : (MulAut.conjNormal t : MulAut W) * MulAut.conjNormal t = 1 :=
    conjNormal_mul_self h.order
  have hσ1 : (MulAut.conjNormal t : MulAut W) ≠ 1 := by
    intro h1
    have h2 : t ∈ centralizer (W : Set X) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h3 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc w * t = t * w * t⁻¹ * t := by rw [h3]
        _ = t * w := by group
    rw [hCW, mem_bot] at h2
    have h4 := h.order
    rw [h2, orderOf_one] at h4
    omega
  have hσ : orderOf (MulAut.conjNormal t : MulAut W) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨-, -, -, -, -, hcard, -⟩ :=
    hFour W hWs hWnab (Or.inr (Or.inl ⟨eHN⟩)) _ hσ (conjNormal_not_mem_inner hCW htW)
  have hCt : Nat.card (W ⊓ centralizer ({t} : Set X) : Subgroup X) = 3628800 := by
    rw [← map_fixSub_conjNormal, Subgroup.card_map_of_injective W.subtype_injective]
    exact hcard
  have h1 := Subgroup.relIndex_mul_card (H := W) (K := centralizer ({t} : Set X))
  have h2 : W.relIndex (centralizer ({t} : Set X)) ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal W _)).trans hidx
  rw [hCt] at h1
  have h10 : Nat.factorial 10 = 3628800 := by norm_num [Nat.factorial]
  rw [h10, ← h1]
  omega

end HN

section Main

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem almostSimple_setup_of_component (hK : CFSG.SectionRank.IsKGroupCat X)
    (hF : CFSG.fittingSubgroup X = ⊥) {K : Subgroup X} (hKc : CFSG.IsComponent K)
    (hall : ∀ L : Subgroup X, CFSG.IsComponent L → L = K) :
    K.Normal ∧ IsSimpleGroup K ∧ (∃ x y : K, x * y ≠ y * x) ∧
      centralizer (K : Set X) = ⊥ ∧ Catalog K := by
  have hlayer : CFSG.layer X = K := by
    apply le_antisymm
    · exact sSup_le (fun L hL => (hall L hL).le)
    · exact le_sSup hKc
  have hKN : K.Normal := by
    have : (CFSG.layer X).Normal := by
      have := CFSG.LocalCores.layer_characteristic (G := X)
      infer_instance
    rw [hlayer] at this
    exact this
  have hZK : center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzL : (z : X) ∈ CFSG.layer X := by rw [hlayer]; exact z.2
    have hmem : (z : X) ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype := by
      refine ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext ?_), rfl⟩
      have hgK : (g : X) ∈ K := by rw [← hlayer]; exact g.2
      have h1 : (g : X) * z = z * g :=
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hgK⟩)
      exact h1
    have h2 := center_layer_le_fitting (X := X) hmem
    rw [hF] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  have hquotK : (↥K ⧸ center K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  have hsK : IsSimpleGroup (↥K ⧸ center K) := hKc.1.2.1
  have hsimpleK : IsSimpleGroup ↥K := hquotK.symm.isSimpleGroup
  have hnab : ∃ x y : K, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hKc.1.2.2
    exact ⟨hquotK a, hquotK b, fun hc => hab (hquotK.injective (by rw [map_mul, map_mul, hc]))⟩
  have hCK : centralizer (K : Set X) = ⊥ := by
    rw [← hlayer]
    exact centralizer_layer_eq_bot hF
  have hcat : Catalog K := by
    have hq : IsSimpleGroup (↥K ⧸ (⊥ : Subgroup ↥K)) :=
      (QuotientGroup.quotientBot (G := ↥K)).isSimpleGroup
    exact CFSG.SectionRank.catalog_of_mulEquiv (QuotientGroup.quotientBot (G := ↥K)).symm
      (hK K ⊥ hq)
  exact ⟨hKN, hsimpleK, hnab, hCK, hcat⟩

theorem exactShape_of_weakShape (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (hK : CFSG.SectionRank.IsKGroupCat X) (hO : CFSG.oddCore X = ⊥) (h : WeakShape t A m)
    (hm : 9 ≤ m) : ExactShape t A m := by
  classical
  by_cases hP : CFSG.pCore 2 X = ⊥
  swap
  · exact h.exactShape_of_le (inf_le_zpowers_of_mem_center hO h
      (mem_center_of_pCore_ne_bot_of_weakShape h (by omega) hP))
  have hpp : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]; exact hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup X = ⊥ := (CFSG.Fitting_eq_pcore X 2 hpp).trans hP
  obtain ⟨K, hKc, hall, hKK1, hKK2⟩ := exists_component_of_weakShape hO h (by omega)
  by_cases hKK : K.map (MulAut.conj t).toMonoidHom = K
  · have hall' : ∀ L : Subgroup X, CFSG.IsComponent L → L = K := fun L hL =>
      (hall L hL).elim id (fun h' => h'.trans hKK)
    obtain ⟨hKN, hKs, hKnab, hCK, hcat⟩ := almostSimple_setup_of_component hK hF hKc hall'
    have := hKN
    have hAK : A ≤ K := hKK1 hKK
    have hcomp : CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X)) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
        h.le_cent).2 (isComponent_subgroupOf_centralizer_of_weakShape h (by omega))
    rcases hlookup X K hKs hKnab hCK hcat t h.order A hAK hcomp m hm h.iso with
      ⟨N, ⟨eW⟩⟩ | ⟨hm10, ⟨eHN⟩⟩
    · exact h.exactShape_of_card_centralizer_le (by omega)
        (card_centralizer_le_of_alt h (by omega) hAK hCK hcomp eW)
    · have hC := card_centralizer_le_of_HN hHN hOut hFour h hm hAK hCK hKs hKnab hcomp eHN
      rw [← hm10] at hC
      exact h.exactShape_of_card_centralizer_le (by omega) hC
  · obtain ⟨hcomm, hA⟩ := hKK2 hKK
    exact h.exactShape_of_le (inf_le_zpowers_of_wreath hF h hKc hall hcomm hA)

end Main

end CFSG.OddStandard.AltStdSec
