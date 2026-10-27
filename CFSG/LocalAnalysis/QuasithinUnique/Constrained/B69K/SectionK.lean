module

public import CFSG.Quasithin.Background.FFC11D
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69K

open CFSG.Quasithin.B69

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem sectionB42K_of (hB42 : AsB42) (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) (hSQL : SQTKGroup ↥L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    ∃ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) ∧
      IsFFStarOffender (autSec (L ⊔ A) W (W ⊓ fixV L)) B ∧
      B42Conclusion (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec L W (W ⊓ fixV L)) B := by
  obtain ⟨-, hmp, hO2, hFF, hns, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAoff : IsFFStarOffender X A := hA.1
  have hAel : IsElemAbelian2 A := hAoff.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAZ : ∀ b ∈ A, ∀ w ∈ W ⊓ fixV L, b w ∈ W ⊓ fixV L :=
    isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn)
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) := B1.le_stabSub_of_invariant hAZ
  have hMW : L ⊔ A ≤ stabSub W := sup_le hLW hAWs
  have hMZ : L ⊔ A ≤ stabSub (W ⊓ fixV L) := sup_le hLZ hAZs
  have hsupn : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hy
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq2 : ∀ y ∈ L ⊔ A, y ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  obtain ⟨ℓ, hℓs, hℓk⟩ := exists_surj_autSec hLW hLZ
  have hmapL := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_left : L ≤ L ⊔ A)
  have hmapA := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_right : A ≤ L ⊔ A)
  have hrange := B5.range_secHom (L ⊔ A) hMW hMZ
  have hLG : autSec L W (W ⊓ fixV L) ≤ autSec (L ⊔ A) W (W ⊓ fixV L) :=
    autSec_mono le_sup_left W _
  have hLbn : ∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
      g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L) := by
    intro g hg l hl
    rw [← hrange] at hg
    obtain ⟨m, rfl⟩ := hg
    rw [← hmapL] at hl ⊢
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hl
    refine Subgroup.mem_map.2 ⟨m * l' * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hl' ⊢
    exact hsupn m m.2 l' hl'
  have hHb2 : ∀ y ∈ autSec (L ⊔ A) W (W ⊓ fixV L), y ^ 2 ∈ autSec L W (W ⊓ fixV L) := by
    intro y hy
    rw [← hrange] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [← hmapL]
    refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp [map_pow]⟩
    rw [Subgroup.mem_subgroupOf]
    exact hsq2 m m.2
  have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
  have hne : ℓ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨x, rfl⟩ := hℓs a
    obtain ⟨y, rfl⟩ := hℓs b
    apply hab
    have hx : x ∈ ℓ.ker := by rw [htop]; trivial
    have hy : y ∈ ℓ.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have hcent : ℓ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq ℓ.ker hne
  have hLbq : CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective (B1Red.isQuasisimple_of_open hLq) ℓ hℓs hcent
  obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  have hIrr : XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ :=
    B5.isIrrSec_autSec hlt hirr hLW hLZ
  have hO2G : pCoreOf 2 (autSec (L ⊔ A) W (W ⊓ fixV L)) = ⊥ := n1_pCoreOf_eq_bot hS2 hLG hIrr
  have hFstar : quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLG hLbn (B1Red.isQuasisimple_to_open hLbq) hHb2 hO2G
  have hSQLt : SQTKGroup ↥(autSec L W (W ⊓ fixV L)) := by
    let π : ↥(⊤ : Subgroup ↥L) →* ↥(autSec L W (W ⊓ fixV L)) := ℓ.comp (⊤ : Subgroup ↥L).subtype
    refine sqtk_of_surj hA21 hSQL π (fun y => ?_) hLbq
    obtain ⟨x, hx⟩ := hℓs y
    exact ⟨⟨x, trivial⟩, hx⟩
  have hSQG : SQTKGroup ↥(autSec (L ⊔ A) W (W ⊓ fixV L)) := by
    set G := autSec (L ⊔ A) W (W ⊓ fixV L) with hGdef
    set Lt := autSec L W (W ⊓ fixV L) with hLtdef
    have hnorm : (Lt.subgroupOf G).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := hLbn (g : MulAut (Sec W (W ⊓ fixV L))) g.2 x hx
      simpa using this
    have hq2 : IsPGroup 2 (↥G ⧸ Lt.subgroupOf G) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        refine ⟨1, ?_⟩
        rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hHb2 y y.2
    let e : ↥(Lt.subgroupOf G) ≃* ↥Lt := Subgroup.subgroupOfEquivOfLe hLG
    have hLm : SQTKGroup ↥(Lt.subgroupOf G) := by
      refine ⟨fun p hp hp2 => ?_, hSQLt.2.of_mulEquiv e⟩
      show CFSG.Open.pRank p (⊤ : Subgroup ↥(Lt.subgroupOf G)) ≤ 2
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact hSQLt.1 p hp hp2
    exact ⟨B5.sqt_of_two_quotient _ hq2 hLm.1, B5.kGroup_of_two_quotient _ hq2 hLm.2⟩
  have hB4 : B4Hyp (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec L W (W ⊓ fixV L)) :=
    ⟨hSQG, hFstar.symm, hLbq, hIrr⟩
  have hnA : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  have hineq := sec_card_le_of_offender hAoff hLq hAn hW hAW hnA
  have hA2 : IsA2 (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec A W (W ⊓ fixV L)) := by
    refine ⟨autSec_mono le_sup_right W _, ?_, ?_, ?_⟩
    · intro hbot
      apply hnA
      rw [commSub_eq_bot_iff]
      intro w hw a ha
      have hmem : B5.secHom A hAWs hAZs ⟨a, ha⟩ ∈ autSec A W (W ⊓ fixV L) := by
        rw [← B5.range_secHom A hAWs hAZs]
        exact ⟨⟨a, ha⟩, rfl⟩
      rw [hbot] at hmem
      have h1 : B5.secHom A hAWs hAZs ⟨a, ha⟩ = 1 := Subgroup.mem_bot.1 hmem
      exact sec_triv_imp_triv hLq hAn hW hAW ha
        (fun w' hw' => (((B5.mem_ker_secHom A hAWs hAZs ⟨a, ha⟩).1 (MonoidHom.mem_ker.2 h1)).2 w' hw').2)
        w hw
    · intro φ hφ ψ hψ
      rw [← hmapA] at hφ hψ
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hψ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAel.1 _ ha _ hb)
    · intro φ hφ
      rw [← hmapA] at hφ
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hAel.2 _ ha)
      rw [this, map_one]
  have hr : rAV (autSec A W (W ⊓ fixV L)) ≤ 1 := (rAV_le_one_iff hS2 hA2).2 hineq
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le hS2 hA2 hr
  exact ⟨B, hBA, hB, hB42 _ hS2 _ _ hB4 B hB⟩

end Main

section Section

variable {V : Type} [CommGroup V] [Finite V]

theorem sectionDataK (hA21 : AsA21SQTKSection) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) (hSQL : SQTKGroup ↥L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    B4Hyp (wtLA A L W) (wtL L W) ∧
      (∀ g ∈ wtLA A L W, ∀ l ∈ wtL L W, g * l * g⁻¹ ∈ wtL L W) ∧
      (∀ y ∈ wtLA A L W, y ^ 2 ∈ wtL L W) := by
  obtain ⟨-, hmp, hO2, hFF, hns, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAoff : IsFFStarOffender X A := hA.1
  have hAel : IsElemAbelian2 A := hAoff.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAZ : ∀ b ∈ A, ∀ w ∈ W ⊓ fixV L, b w ∈ W ⊓ fixV L :=
    isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn)
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) := B1.le_stabSub_of_invariant hAZ
  have hMW : L ⊔ A ≤ stabSub W := sup_le hLW hAWs
  have hMZ : L ⊔ A ≤ stabSub (W ⊓ fixV L) := sup_le hLZ hAZs
  have hsupn : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hy
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq2 : ∀ y ∈ L ⊔ A, y ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  obtain ⟨ℓ, hℓs, hℓk⟩ := exists_surj_autSec hLW hLZ
  have hmapL := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_left : L ≤ L ⊔ A)
  have hrange := B5.range_secHom (L ⊔ A) hMW hMZ
  have hLG : autSec L W (W ⊓ fixV L) ≤ autSec (L ⊔ A) W (W ⊓ fixV L) :=
    autSec_mono le_sup_left W _
  have hLbn : ∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
      g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L) := by
    intro g hg l hl
    rw [← hrange] at hg
    obtain ⟨m, rfl⟩ := hg
    rw [← hmapL] at hl ⊢
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hl
    refine Subgroup.mem_map.2 ⟨m * l' * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hl' ⊢
    exact hsupn m m.2 l' hl'
  have hHb2 : ∀ y ∈ autSec (L ⊔ A) W (W ⊓ fixV L), y ^ 2 ∈ autSec L W (W ⊓ fixV L) := by
    intro y hy
    rw [← hrange] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [← hmapL]
    refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp [map_pow]⟩
    rw [Subgroup.mem_subgroupOf]
    exact hsq2 m m.2
  have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
  have hne : ℓ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨x, rfl⟩ := hℓs a
    obtain ⟨y, rfl⟩ := hℓs b
    apply hab
    have hx : x ∈ ℓ.ker := by rw [htop]; trivial
    have hy : y ∈ ℓ.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have hcent : ℓ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq ℓ.ker hne
  have hLbq : CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective (B1Red.isQuasisimple_of_open hLq) ℓ hℓs hcent
  obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  have hIrr : XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ :=
    B5.isIrrSec_autSec hlt hirr hLW hLZ
  have hO2G : pCoreOf 2 (autSec (L ⊔ A) W (W ⊓ fixV L)) = ⊥ := n1_pCoreOf_eq_bot hS2 hLG hIrr
  have hFstar : quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) =
      autSec L W (W ⊓ fixV L) :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLG hLbn (B1Red.isQuasisimple_to_open hLbq) hHb2 hO2G
  have hSQLt : SQTKGroup ↥(autSec L W (W ⊓ fixV L)) := by
    let π : ↥(⊤ : Subgroup ↥L) →* ↥(autSec L W (W ⊓ fixV L)) := ℓ.comp (⊤ : Subgroup ↥L).subtype
    refine sqtk_of_surj hA21 hSQL π (fun y => ?_) hLbq
    obtain ⟨x, hx⟩ := hℓs y
    exact ⟨⟨x, trivial⟩, hx⟩
  have hSQG : SQTKGroup ↥(autSec (L ⊔ A) W (W ⊓ fixV L)) := by
    set G := autSec (L ⊔ A) W (W ⊓ fixV L) with hGdef
    set Lt := autSec L W (W ⊓ fixV L) with hLtdef
    have hnorm : (Lt.subgroupOf G).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := hLbn (g : MulAut (Sec W (W ⊓ fixV L))) g.2 x hx
      simpa using this
    have hq2 : IsPGroup 2 (↥G ⧸ Lt.subgroupOf G) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        refine ⟨1, ?_⟩
        rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hHb2 y y.2
    let e : ↥(Lt.subgroupOf G) ≃* ↥Lt := Subgroup.subgroupOfEquivOfLe hLG
    have hLm : SQTKGroup ↥(Lt.subgroupOf G) := by
      refine ⟨fun p hp hp2 => ?_, hSQLt.2.of_mulEquiv e⟩
      show CFSG.Open.pRank p (⊤ : Subgroup ↥(Lt.subgroupOf G)) ≤ 2
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact hSQLt.1 p hp hp2
    exact ⟨B5.sqt_of_two_quotient _ hq2 hLm.1, B5.kGroup_of_two_quotient _ hq2 hLm.2⟩
  exact ⟨⟨hSQG, hFstar.symm, hLbq, hIrr⟩, hLbn, hHb2⟩

end Section

end B69K

end CFSG.Quasithin
