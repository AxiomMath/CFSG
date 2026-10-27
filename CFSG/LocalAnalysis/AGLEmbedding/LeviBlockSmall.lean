module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace LeviBlock

theorem card_dvd_card_centerQuotient {Y : Type*} [Group Y] [Finite Y] {L W : Subgroup Y}
    (hWL : W ≤ L) (hodd : Odd (Nat.card (Subgroup.center ↥L))) {U : Type*} [Group U]
    [Finite U] [IsSimpleGroup U] (h2 : 2 ∣ Nat.card U) (ψ : ↥W →* U)
    (hψ : Function.Surjective ψ) : Nat.card U ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  set f : ↥W →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hWL) with hf
  have hk : f.ker ≤ ψ.ker := by
    have : (f.ker.map ψ).Normal := (MonoidHom.normal_ker f).map ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map ψ) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hU : Nat.card U ∣ Nat.card f.ker := by
        have := Subgroup.card_map_dvd f.ker ψ
        rwa [h, Subgroup.card_top] at this
      have hZ : Nat.card f.ker ∣ Nat.card (Subgroup.center ↥L) := by
        have hle : f.ker.map (Subgroup.inclusion hWL) ≤ Subgroup.center ↥L := by
          rintro _ ⟨w, hw, rfl⟩
          have : QuotientGroup.mk' (Subgroup.center ↥L) (Subgroup.inclusion hWL w) = 1 := hw
          exact (QuotientGroup.eq_one_iff _).mp this
        have := Subgroup.card_dvd_of_le hle
        rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWL)] at this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((h2.trans hU).trans hZ))
  obtain ⟨ψ', hψ', -⟩ := exists_factor f.rangeRestrict f.rangeRestrict_surjective ψ hψ
    (by rw [MonoidHom.ker_rangeRestrict]; exact hk)
  exact (Subgroup.card_dvd_of_surjective hψ').trans (Subgroup.card_subgroup_dvd_card _)

theorem card_small_cases {X : Type} [Group X] (hS : IsSmallTwoOrG2 X) :
    Nat.card X = 60 ∨ Nat.card X = 360 ∨ Nat.card X = 20160 ∨ Nat.card X = 168 ∨
      Nat.card X = 6048 := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl <;>
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] <;> decide
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
      rw [TauCeti.PrimePower.card_def] at hq7
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
    have hc := statedClassicalModel_of_typeA hv e
    rw [hp, hf] at hc
    have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num) hc).1 rfl
    rw [this]
    unfold ordA
    decide
  · simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ : q.p = 3 ∧ q.exponent = 1 := by
      rw [TauCeti.PrimePower.card_def] at hq3
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq3
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at hc
    have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num) hc).2.1 rfl
    rw [this]
    unfold ordTwistedA
    decide

end LeviBlock

theorem kFactCompParabSU38_small : KFactCompParabSU38On IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS O W hO hPO hOc hW hPWO hWW d ψ hd hψ
  exfalso
  have hd' := hd
  obtain ⟨q, hqp, -, hdq⟩ := hd'
  have : IsSimpleGroup (CatGroup d) := unitaryTarget_isSimpleGroup ⟨q, hqp, hdq⟩
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have h1 := LeviBlock.card_dvd_card_centerQuotient (hW.trans hCP.parab.1) hCP.odd
    (by rw [LeviBlock.card_catGroup_u38 hd]; norm_num) ψ hψ
  rw [LeviBlock.card_catGroup_u38 hd] at h1
  have := h1.trans (ToralCensus.card_dvd_of_small hS)
  norm_num at this

theorem kFactCompParabLeviU42_small : KFactCompParabLeviU42On IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS _ O W hO hPO hOc hW hPWO _ hWW d ψ hd hψ _ _
  exfalso
  obtain ⟨hcard, hsimp⟩ := LeviBlock.catGroup_u42_facts hd
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have h1 := LeviBlock.card_dvd_card_centerQuotient (hW.trans hCP.parab.1) hCP.odd
    (by rw [hcard]; norm_num) ψ hψ
  rw [hcard] at h1
  rcases LeviBlock.card_small_cases hS with h | h | h | h | h <;> rw [h] at h1 <;> norm_num at h1

theorem kFactCompParabThreeFives_small : KFactCompParabThreeFivesOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS O J hOP hPO _ _ hJ hJc
  exfalso
  have hPL : P ≤ L := hCP.parab.1
  set Z : Subgroup Y := L ⊓ Subgroup.centralizer (L : Set Y) with hZdef
  have hcen : ∀ z ∈ Z, ∀ t ∈ L, z * t * z⁻¹ = t := fun z hz t ht => by
    rw [← Subgroup.mem_centralizer_iff.mp hz.2 t ht, mul_inv_cancel_right]
  have hZP : Z ≤ P := by
    obtain ⟨-, T, hT, hNT⟩ := hCP.parab
    intro z hz
    refine hNT ⟨hz.1, Subgroup.mem_normalizer_iff.mpr fun t => ?_⟩
    constructor
    · intro ht
      rw [hcen z hz t (hT.1 ht)]
      exact ht
    · intro ht
      have hzi : z⁻¹ ∈ Z := Z.inv_mem hz
      have h1 := hcen z⁻¹ hzi _ (hT.1 ht)
      rw [inv_inv] at h1
      rw [show t = z⁻¹ * (z * t * z⁻¹) * z by group, h1]
      exact ht
  set O' := O.subgroupOf P with hO'
  set Zp := Z.subgroupOf P with hZp
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOP).mpr hPO
  have hZpn : Zp.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have : ((g * n * g⁻¹ : ↥P) : Y) = n := by
      have hc := Subgroup.mem_centralizer_iff.mp hn.2 (g : Y) (hPL g.2)
      simp [hc]
    rw [this]
    exact hn⟩
  set R := O' ⊔ Zp with hR
  have : R.Normal := Subgroup.sup_normal O' Zp
  set μ := QuotientGroup.mk' R with hμ
  have hstep : ∀ i, ∃ A : Subgroup (↥P ⧸ R), Nat.card A = 60 ∧ Subgroup.center ↥A = ⊥ ∧
      ∀ a ∈ A, ∃ x : ↥P, (x : Y) ∈ J i ∧ μ x = a := by
    intro i
    obtain ⟨hJP, φ, hφ, hφO⟩ := hJ i
    set ν : ↥(J i) →* ↥P ⧸ R := μ.comp (Subgroup.inclusion hJP) with hν
    have hA5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hA5card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hA5nc : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a :=
      ThreeFives.exists_noncomm_of_simple hA5 (by rw [hA5card]; norm_num)
    have hA5Z : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center ↥(alternatingGroup (Fin 5))) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hA5nc
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hker : ν.ker = φ.ker := by
      apply le_antisymm
      · intro x hx
        rw [MonoidHom.mem_ker, hν, MonoidHom.comp_apply, hμ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hx
        obtain ⟨o, ho, z, hz, hoz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
        have hcomm : ∀ y : ↥(J i), φ x * φ y = φ y * φ x := by
          intro y
          have hxy : (⁅x, y⁆ : ↥(J i)) ∈ φ.ker := by
            rw [MonoidHom.mem_ker, hφO]
            have hx' : (x : Y) = (o : Y) * (z : Y) := by
              have := congrArg Subtype.val hoz
              simpa using this.symm
            have hzc : ∀ t ∈ L, (z : Y) * t = t * (z : Y) := fun t ht =>
              (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hz).2 t ht).symm
            have hyL : (y : Y) ∈ L := hPL (hJP y.2)
            have he : ((⁅x, y⁆ : ↥(J i)) : Y) =
                (o : Y) * ((y : Y) * (o : Y)⁻¹ * (y : Y)⁻¹) := by
              have h1 := hzc _ hyL
              have h2 := hzc _ (L.inv_mem hyL)
              simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hx',
                mul_inv_rev]
              calc (o : Y) * z * y * ((z : Y)⁻¹ * (o : Y)⁻¹) * (y : Y)⁻¹
                  = o * (z * y) * (z : Y)⁻¹ * (o : Y)⁻¹ * (y : Y)⁻¹ := by group
                _ = o * (y * z) * (z : Y)⁻¹ * (o : Y)⁻¹ * (y : Y)⁻¹ := by rw [h1]
                _ = o * (y * (o : Y)⁻¹ * (y : Y)⁻¹) := by group
            rw [he]
            have hoO : (o : Y) ∈ O := Subgroup.mem_subgroupOf.mp ho
            have hyP : (y : Y) ∈ P := hJP y.2
            refine O.mul_mem hoO ?_
            have := (Subgroup.mem_normalizer_iff.mp (hPO hyP) _).mp (O.inv_mem hoO)
            exact this
          rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
            at hxy
          exact hxy
        have hxZ : φ x ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
          rw [Subgroup.mem_center_iff]
          intro a
          obtain ⟨y, rfl⟩ := hφ a
          exact (hcomm y).symm
        rw [hA5Z, Subgroup.mem_bot] at hxZ
        exact hxZ
      · intro x hx
        rw [MonoidHom.mem_ker, hφO] at hx
        rw [MonoidHom.mem_ker, hν, MonoidHom.comp_apply, hμ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hx)
    let iso : ↥ν.range ≃* ↥(alternatingGroup (Fin 5)) :=
      (QuotientGroup.quotientKerEquivRange ν).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφ))
    refine ⟨ν.range, ?_, ?_, ?_⟩
    · rw [Nat.card_congr iso.toEquiv, hA5card]
    · rw [← LeviBlock.map_center_mulEquiv iso.symm, hA5Z, Subgroup.map_bot]
    · rintro a ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hJP x, x.2, rfl⟩
  choose A hAcard hAZ hAx using hstep
  have hAcomm : ∀ i k, i ≠ k → ∀ a ∈ A i, ∀ b ∈ A k, a * b = b * a := by
    intro i k hik a ha b hb
    obtain ⟨x, hxJ, rfl⟩ := hAx i a ha
    obtain ⟨y, hyJ, rfl⟩ := hAx k b hb
    rw [← map_mul, ← map_mul, hμ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    refine Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr ?_)
    have e : (((x * y)⁻¹ * (y * x) : ↥P) : Y) = ⁅(y : Y)⁻¹, (x : Y)⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact hJc k i (Ne.symm hik)
      (Subgroup.commutator_mem_commutator ((J k).inv_mem hyJ) ((J i).inv_mem hxJ))
  have hdvd := LeviBlock.card_mul_dvd_of_commute (A 0) (A 1) (A 2) (hAcomm 0 1 (by decide))
    (hAcomm 0 2 (by decide)) (hAcomm 1 2 (by decide)) (hAZ 0) (hAZ 1)
  rw [hAcard, hAcard, hAcard] at hdvd
  have h1 : Nat.card (↥P ⧸ R) ∣ Nat.card (↥P ⧸ Zp) := by
    show R.index ∣ Zp.index
    exact Subgroup.index_dvd_of_le le_sup_right
  have h2 : Nat.card (↥P ⧸ Zp) ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    have hZc : Nat.card (Subgroup.center ↥L) = Nat.card Z :=
      LeviBlock.card_center_eq_card_inf_centralizer L
    have hZpc : Nat.card Zp = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
    have hP := Subgroup.card_eq_card_quotient_mul_card_subgroup Zp
    have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    have hPLd : Nat.card P ∣ Nat.card L := Subgroup.card_dvd_of_le hPL
    rw [hP, hL, hZpc, hZc] at hPLd
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hPLd
  have h3 := ToralCensus.card_dvd_of_small hS
  have := (hdvd.trans h1).trans (h2.trans h3)
  norm_num at this

end CFSG.AGLEmbedding
