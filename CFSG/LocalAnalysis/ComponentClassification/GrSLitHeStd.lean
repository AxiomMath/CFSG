module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMaxWeak
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputsHe
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Matrix commutatorElement Pointwise

theorem isQuasisimple_of_simple_nonab {D : Type} [Group D] [IsSimpleGroup D]
    (hnab : ∃ a b : D, a * b ≠ b * a) : IsQuasisimple D := by
  have hc : center D = ⊥ := center_eq_bot_of_simple hnab
  let e : D ⧸ center D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hcomm : commutator D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator D := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
      exact hmem
    · exact h
  refine ⟨Group.isPerfect_def.mpr hcomm, ?_, ?_⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ ‹IsSimpleGroup D› e
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

@[expose] def HeldOddCoreStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) →
    ∀ t : X, orderOf t = 2 → L ≤ centralizer ({t} : Set X) →
      pPrimeCore 2 ↥(⨆ (c : X) (_ : c ∈ centralizer ({t} : Set X)), conjugate L c) = ⊥

theorem heldStandardStep_of_inputs
    (hOdd : HeldOddCoreStep) (hMax : MaximalTwoComponentInputHe)
    (hS : SchreierFor Blueprint.Catalog) (hHN : HeldNotProperFixedInput)
    (h64 : HeldSylowElementarySixtyFour) : HeldStandardStep := by
  intro X _ _ L hset hW
  obtain ⟨hsimp, hnab, hK, hU, -, ⟨a, ha2, hLa, hLc⟩, ⟨e⟩⟩ := id hset
  have hmax : GSWeakMaximalComponent L :=
    gsWeakMaximalComponent_of_held hS hHN hnab hK ha2 hLa hLc (nonempty_fusionZStar_equiv_held e)
  have haN : a ∈ normalizer (L : Set X) := mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hLa hx)).symm
  obtain ⟨S, hSyl, -⟩ := exists_isSylowTwoIn_mem haN ha2
  obtain ⟨E, hET, -, hEe, hE64⟩ := exists_elem_sixtyFour e h64 inf_le_right
    (hSyl.isPGroup.to_le inf_le_left) (card_inf_eq_1024 e hSyl)
  have hrank : 3 ≤ pRank 2 ↥L := three_le_pRank_of_le hEe (by omega) (hET.trans inf_le_right)
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hLie : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup X) := fun h => hU (Or.inl h)
  have hT9 := fun (t : X) (ht : orderOf t = 2) (htL : L ≤ centralizer ({t} : Set X)) =>
    hMax X hsF hnF hLie hK L hmax (by omega) (Sol78.not_psp4_of_held e)
      (nonempty_fusionZStar_equiv_held e) t ht htL
  have hclos : ∀ t : X, orderOf t = 2 → L ≤ centralizer ({t} : Set X) →
      (⨆ (c : X) (_ : c ∈ centralizer ({t} : Set X)), conjugate L c) = L := by
    intro t ht htL
    set C := centralizer ({t} : Set X) with hC
    set M : Subgroup X := ⨆ (c : X) (_ : c ∈ C), conjugate L c with hM
    set O : Subgroup X := (pPrimeCore 2 ↥C).map C.subtype with hO
    have hLM : L ≤ M := by
      refine le_iSup₂_of_le 1 (one_mem C) (le_of_eq ?_)
      ext x
      simp only [conjugate, inv_one, map_one, mem_map, MulEquiv.coe_toMonoidHom, MulAut.one_apply,
        exists_eq_right]
    have hconjC : ∀ c ∈ C, conjugate L c ≤ C := by
      intro c hc
      rintro _ ⟨l, hl, rfl⟩
      exact mul_mem (mul_mem (inv_mem hc) (htL hl)) (inv_mem (inv_mem hc))
    have hMC : M ≤ C := iSup₂_le hconjC
    have hMOL : M ≤ O ⊔ L := by
      refine iSup₂_le fun c hc => ?_
      exact (le_iSup₂_of_le c (hconjC c hc) le_rfl).trans (hT9 t ht htL).1
    have hOM : pPrimeCore 2 ↥M = ⊥ := hOdd X L hset hW t ht htL
    have hCO : C ≤ normalizer (O : Set X) := le_normalizer_oddIn
    have hMO : M ⊓ O = ⊥ := by
      have hn : ((M ⊓ O).subgroupOf M).Normal := by
        refine ⟨fun x hx m => ?_⟩
        rw [mem_subgroupOf] at hx ⊢
        obtain ⟨hxM, hxO⟩ := mem_inf.mp hx
        refine mem_inf.mpr ⟨mul_mem (mul_mem m.2 hxM) (inv_mem m.2), ?_⟩
        exact (mem_normalizer_iff.mp (hCO (hMC m.2)) _).mp hxO
      have hcop : Nat.Coprime 2 (Nat.card ((M ⊓ O).subgroupOf M)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
        have hOodd : Odd (Nat.card O) := by
          rw [hO, card_map_of_injective C.subtype_injective]
          exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
        exact Nat.coprime_two_left.mpr (hOodd.of_dvd_nat (card_dvd_of_le inf_le_right))
      have hbot := (pPrimeCore_eq_bot_iff.mp hOM) _ hn hcop
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, (mem_inf.mp hx).1⟩ : M) ∈ (M ⊓ O).subgroupOf M := mem_subgroupOf.mpr hx
      rw [hbot, mem_bot] at hx'
      exact (mem_bot).mpr (congrArg Subtype.val hx')
    refine le_antisymm (fun m hm => ?_) hLM
    have hmset : m ∈ (O : Set X) * (L : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left O L (htL.trans hCO)]
      exact hMOL hm
    obtain ⟨o, ho, l, hl, rfl⟩ := hmset
    have hoM : o ∈ M := by
      have := mul_mem hm (inv_mem (hLM hl))
      rwa [mul_inv_cancel_right] at this
    have ho1 : o = 1 := by
      have : o ∈ M ⊓ O := mem_inf.mpr ⟨hoM, ho⟩
      rw [hMO, mem_bot] at this
      exact this
    show o * l ∈ L
    rw [ho1, one_mul]
    exact hl
  have hOL : pPrimeCore 2 ↥L = ⊥ := by
    have h := hOdd X L hset hW a ha2 hLa
    rw [hclos a ha2 hLa] at h
    exact h
  obtain ⟨eL⟩ := nonempty_mulEquiv_held_of_pPrimeCore_eq_bot hOL e
  have hLs : IsSimpleGroup L := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He eL
  have hLnab : ∃ u v : L, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := exists_mul_ne_held
    exact ⟨eL.symm u, eL.symm v, fun h => huv (eL.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hnorm : ∀ t : X, orderOf t = 2 → L ≤ centralizer ({t} : Set X) →
      centralizer ({t} : Set X) ≤ normalizer (L : Set X) := by
    intro t ht htL c hc
    refine mem_normalizer_of_map_conj_le ?_
    have h1 : conjugate L c⁻¹ ≤ L :=
      (le_iSup₂_of_le c⁻¹ (inv_mem hc) le_rfl).trans (le_of_eq (hclos t ht htL))
    simpa [conjugate] using h1
  have hcomm : ∀ g : X, ⁅L, conjugate L g⁆ ≠ ⊥ := by
    intro g hg
    apply (hT9 a ha2 hLa).2 hrank g
    rw [hg]
    exact bot_le
  have hkey : ∀ (g t : X), orderOf t = 2 → L ≤ centralizer ({t} : Set X) →
      conjugate L g ≤ centralizer ({t} : Set X) → conjugate L g = L := by
    intro g t ht htL htLg
    set Lg : Subgroup X := conjugate L g with hLg
    have hLN : centralizer ({t} : Set X) ≤ normalizer (L : Set X) := hnorm t ht htL
    have hLgN : centralizer ({t} : Set X) ≤ normalizer (Lg : Set X) := by
      have ht' : orderOf (g * t * g⁻¹) = 2 := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
      have hLt' : L ≤ centralizer ({g * t * g⁻¹} : Set X) := by
        intro l hl
        have hmem : g⁻¹ * l * g ∈ Lg := ⟨l, hl, by simp⟩
        have h1 := mem_centralizer_singleton_iff.mp (htLg hmem)
        rw [mem_centralizer_singleton_iff]
        calc l * (g * t * g⁻¹) = g * ((g⁻¹ * l * g) * t) * g⁻¹ := by group
          _ = g * (t * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
          _ = g * t * g⁻¹ * l := by group
      intro c hc
      have hc' : g * c * g⁻¹ ∈ centralizer ({g * t * g⁻¹} : Set X) := by
        rw [mem_centralizer_singleton_iff] at hc ⊢
        calc g * c * g⁻¹ * (g * t * g⁻¹) = g * (c * t) * g⁻¹ := by group
          _ = g * (t * c) * g⁻¹ := by rw [hc]
          _ = g * t * g⁻¹ * (g * c * g⁻¹) := by group
      have hcN := hnorm _ ht' hLt' hc'
      refine mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨y, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨(g * c * g⁻¹) * l * (g * c * g⁻¹)⁻¹, (mem_normalizer_iff.mp hcN l).mp hl, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    by_contra hne
    have hc1 : ⁅L, Lg⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp (htLg.trans hLN)
    have hc2 : ⁅L, Lg⁆ ≤ Lg := by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp (htL.trans hLgN)
    have hn : ((L ⊓ Lg).subgroupOf L).Normal := by
      refine ⟨fun x hx l => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      obtain ⟨hxL, hxLg⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨mul_mem (mul_mem l.2 hxL) (inv_mem l.2),
        (mem_normalizer_iff.mp (hLgN (htL l.2)) x).mp hxLg⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ Lg).subgroupOf L) with h | h
    · apply hcomm g
      refine le_bot_iff.mp fun x hx => ?_
      have hx' : (⟨x, hc1 hx⟩ : L) ∈ (L ⊓ Lg).subgroupOf L :=
        mem_subgroupOf.mpr (mem_inf.mpr ⟨hc1 hx, hc2 hx⟩)
      rw [h, mem_bot] at hx'
      exact (mem_bot).mpr (congrArg Subtype.val hx')
    · apply hne
      refine (eq_of_le_of_card_ge (fun x hx => ?_) ?_).symm
      · have hx' : (⟨x, hx⟩ : L) ∈ (L ⊓ Lg).subgroupOf L := h ▸ mem_top _
        exact (mem_inf.mp (mem_subgroupOf.mp hx')).2
      · rw [hLg, conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hNLC : normalizer (L : Set X) ≤ normalizer (centralizer (L : Set X) : Set X) := by
    intro g hg
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      rwa [inv_inv] at this
    have h1 := (mem_centralizer_iff.mp hx) _ hl'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * l := by group
  have hfix : ∀ (g t : X), orderOf t = 2 → t ∈ centralizer (L : Set X) →
      t ∈ conjugate (centralizer (L : Set X)) g → g ∈ normalizer (L : Set X) := by
    intro g t ht htC htCg
    have htL : L ≤ centralizer ({t} : Set X) := fun l hl =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp htC) l hl)
    have htLg : conjugate L g ≤ centralizer ({t} : Set X) := by
      obtain ⟨c, hc, rfl⟩ := htCg
      rintro _ ⟨l, hl, rfl⟩
      have h1 := (mem_centralizer_iff.mp hc) l hl
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * l * g * (g⁻¹ * c * g) = g⁻¹ * (l * c) * g := by group
        _ = g⁻¹ * (c * l) * g := by rw [h1]
        _ = g⁻¹ * c * g * (g⁻¹ * l * g) := by group
    have heq := hkey g t ht htL htLg
    have h1 : g⁻¹ ∈ normalizer (L : Set X) := mem_normalizer_iff_map_conj_eq.mpr heq
    simpa using inv_mem h1
  have haC : a ∈ centralizer (L : Set X) := mem_centralizer_iff.mpr fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLa hl))
  refine ⟨⟨isQuasisimple_of_simple_nonab hLnab, ?_, ?_, ?_, hcomm⟩, hOL⟩
  · have h1 : orderOf (⟨a, haC⟩ : centralizer (L : Set X)) = 2 := by
      rw [Subgroup.orderOf_mk, ha2]
    exact even_iff_two_dvd.mpr (h1 ▸ orderOf_dvd_natCard _)
  · intro g hg
    by_contra hodd
    have heven : 2 ∣ Nat.card ↥(centralizer (L : Set X) ⊓
        conjugate (centralizer (L : Set X)) g) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 heven
    obtain ⟨hwC, hwCg⟩ := mem_inf.mp w.2
    exact hg (hNLC (hfix g w (by rw [← hw, Subgroup.orderOf_coe]) hwC hwCg))
  · refine le_antisymm (fun g hg => ?_) hNLC
    have hCg : conjugate (centralizer (L : Set X)) g = centralizer (L : Set X) :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem hg)
    exact hfix g a ha2 haC (by rw [hCg]; exact haC)

end CFSG.ComponentClassification.GrSLit
