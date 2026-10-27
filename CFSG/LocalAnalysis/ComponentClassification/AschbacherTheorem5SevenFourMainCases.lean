module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainThm3
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourSimple
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainAlpha
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainConfig
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainFixed

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools

@[expose] def CaseDImpossible : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D 2 Abar → ∀ t g r : G, t ∈ Subgroup.normalizer (D : Set G) →
      orderOf t = 2 → g ∉ Subgroup.normalizer (D : Set G) →
      (∀ k : Fin 2, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
        aschbacherThm5Preimage D (Abar k)) →
      (∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) →
      orderOf r = 2 → r * t = t * r → r ∈ D →
      (∀ k : Fin 2, aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (Abar k)) r) →
      (∀ k : Fin 2, aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (Abar k)) (g * t * g⁻¹)) →
      (∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate D g)
          (conjFactors D Abar g k)).map (MulAut.conj r).toMonoidHom =
        aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k)) →
      False

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem factor_odd_normal_eq_bot (hyp : Hyp61 G D r Abar) (k : Fin r) :
    ∀ N : Subgroup (Abar k), N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hN hodd
  have hAn : (Abar k).Normal := commuting_factors_normal Abar hyp.hcomm hyp.hgen k
  have hNO : N ≤ aschbacherThm5OddCore (Abar k) := le_sSup ⟨hN, hodd⟩
  have : (aschbacherThm5OddCore (Abar k)).Characteristic := oddCore_characteristic _
  set O' := (aschbacherThm5OddCore (Abar k)).map (Abar k).subtype with hO'
  have hO'n : O'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro y _
    apply AschbacherTheorem3.mem_normalizer_map_of_characteristic
    rw [Subgroup.normalizer_eq_top_iff.mpr hAn]
    exact Subgroup.mem_top y
  have hO'odd : Odd (Nat.card O') := by
    rw [hO', Subgroup.card_map_of_injective (Abar k).subtype_injective]
    exact oddCore_odd _
  have hO'bot : O' = ⊥ := by
    have h1 : O' ≤ aschbacherThm5OddCore (D ⧸ aschbacherThm5OddCore D) := le_sSup ⟨hO'n, hO'odd⟩
    rw [quotient_oddCore_eq_bot] at h1
    exact le_bot_iff.mp h1
  have hbot : aschbacherThm5OddCore (Abar k) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Abar k).subtype_injective).mp hO'bot
  exact le_bot_iff.mp (hbot ▸ hNO)

theorem conj_mem_normalizer_factor {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hyp : Hyp61 G D 2 Abar) {x y : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hy : y ∈ Subgroup.normalizer (D : Set G)) {i : Fin 2}
    (hyA : y ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    x * y * x⁻¹ ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := by
  have hyall : ∀ k : Fin 2, (aschbacherThm5Preimage D (Abar k)).map
      (MulAut.conj y).toMonoidHom = aschbacherThm5Preimage D (Abar k) := by
    intro k
    by_cases hki : k = i
    · rw [hki]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyA
    · exact map_other_of_map hyp hy (Ne.symm hki) (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyA)
  obtain ⟨l, hl⟩ := hyp.hperm x⁻¹ (Subgroup.inv_mem _ hx) i
  have hl' : (aschbacherThm5Preimage D (Abar l)).map (MulAut.conj x).toMonoidHom =
      aschbacherThm5Preimage D (Abar i) := by
    rw [← hl, ← map_conj_mul, mul_inv_cancel]
    ext z
    simp
  have key : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj (x * y * x⁻¹)).toMonoidHom =
      aschbacherThm5Preimage D (Abar i) := by
    rw [map_conj_mul, map_conj_mul, hl, hyall l, hl']
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key

namespace FieldHyps

variable {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)} {t g : G}

theorem false_of_le_normalizer (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) {j m : Fin 2}
    (hjm : j ≠ m) {r : G} (hrA : r ∈ aschbacherThm5Preimage D (Abar i)) (hr2 : orderOf r = 2)
    (hrt : r * t = t * r)
    (hrnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate D g)
        (conjFactors D Abar g k)).map (MulAut.conj r).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k))
    (htm : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    {R : Subgroup G} (hR : IsSylowOf 2 R (aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.centralizer ({t} : Set G))) (hrR : r ∈ R)
    (hRL : R ≤ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' := hC.conj g
  have hnd' : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g k) :=
    fun k => not_dihedral_conjFactor (hnd k) g
  have hKL := hF.isSylowOf_inf_normalizer hin hC hii' hjm (hnd' m) htm hR
  have hAK := inf_normalizer_le_normalizer hC hjm hKL hRL
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hr2
    omega
  have hCr : Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    centralizer_le_of_mem_factor hC hrA (two_power_of_orderOf hr2) hr1
  have htLr : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ⊓
      Subgroup.centralizer ({r} : Set G) :=
    ⟨htm, Subgroup.mem_centralizer_singleton_iff.mpr hrt.symm⟩
  obtain ⟨T, hT, htT'⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr htLr)
    (isPGroup_zpowers_two (k := 1) (by rw [pow_one, ← hF.two]; exact pow_orderOf_eq_one t))
  have htT : t ∈ T := htT' (Subgroup.mem_zpowers t)
  set N₀ := (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ⊓
    Subgroup.centralizer ({r} : Set G)) ⊓
    Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) with hN₀
  have hN₀n : aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ⊓
      Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro x hx
    have hxH : x ∈ Subgroup.normalizer (D : Set G) := hCr hx.2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyX, hyA⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hyX) (Subgroup.inv_mem _ hx),
        conj_mem_normalizer_factor hC.hyp hxH (hCr hyX.2) hyA⟩
    · rintro ⟨hyX, hyA⟩
      have hyX' : y ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ⊓
          Subgroup.centralizer ({r} : Set G) := by
        have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hyX) hx
        simpa [mul_assoc] using h1
      refine ⟨hyX', ?_⟩
      have h1 := conj_mem_normalizer_factor hC.hyp (Subgroup.inv_mem _ hxH) (hCr hyX.2) hyA
      simpa [mul_assoc] using h1
  have hT₀syl : IsSylowOf 2 (T ⊓ N₀) N₀ := hT.inf_of_le_normalizer inf_le_left hN₀n
  set T₀ := T ⊓ N₀ with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT.isPGroup.to_le inf_le_left
  have htT₀ : t ∈ T₀ :=
    ⟨htT, htLr, Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hF.norm i)⟩
  have hT₀L : T₀ ≤ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) :=
    inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hT₀A : T₀ ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) :=
    inf_le_right.trans inf_le_right
  have hT₀H : T₀ ≤ Subgroup.normalizer (D : Set G) :=
    (inf_le_right.trans (inf_le_left.trans inf_le_right)).trans hCr
  have hlt : Nat.card T₀ < Nat.card R := by
    by_contra hge
    push Not at hge
    refine hF.false_of_thm3 hin hC hii' (hnd i) hjm hT₀2 htT₀ hT₀L hT₀A hT₀H hAK ?_
    intro C hCle hC2
    have hCt : C ≤ aschbacherThm5Preimage D (Abar i) ⊓ Subgroup.centralizer ({t} : Set G) :=
      fun c hc => ⟨(hCle hc).1, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hCle hc).2 t htT₀).symm⟩
    exact (IsSylowOf.card_le_of_le hR hCt hC2).trans hge
  have hF' := hF.mirror hC hii' hrA hr2 hrt hrnorm
  have hrN : r ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hrnorm m)
  have hRA : R ⊓ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) ≤ aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
          (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ i) := by
    rw [preimage_conjFactors_inv]
    exact inf_le_left.trans (hR.le.trans inf_le_left)
  obtain ⟨C, hCle, hC2, hCcard⟩ := hF'.exists_large_centralizer hin hC' hjm.symm (hnd' m)
    hii'.symm (not_dihedral_conjFactor (hnd' i) g⁻¹) (hR.isPGroup.to_le inf_le_left)
    ⟨hrR, hrN⟩ hRA inf_le_right
  rw [inf_eq_left.mpr hRL] at hCle hCcard
  have hCr' : C ≤ Subgroup.centralizer ({r} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hCle hx).2 r hrR).symm
  have hCA : C ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := by
    intro x hx
    have hxH := hCr (hCr' hx)
    by_contra hxA
    have hne : (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj x).toMonoidHom ≠
        aschbacherThm5Preimage D (Abar i) := fun h =>
      hxA (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hmap := map_eq_other_of_ne hC.hyp hxH hii' hne
    apply hF.false_of_le_other hin hC hii' hR
    intro ρ hρ
    rw [← hmap]
    refine ⟨ρ, (hR.le hρ).1, ?_⟩
    change x * ρ * x⁻¹ = ρ
    rw [← Subgroup.mem_centralizer_iff.mp (hCle hx).2 ρ hρ, mul_inv_cancel_right]
  have hCN₀ : C ≤ N₀ := fun x hx => ⟨⟨(hCle hx).1, hCr' hx⟩, hCA hx⟩
  have h1 := IsSylowOf.card_le_of_le hT₀syl hCN₀ hC2
  omega

theorem false_of_not_dihedral (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) (hd : CaseDImpossible)
    (hnd : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' := hC.conj g
  obtain ⟨j, hj⟩ := hF.cent
  obtain ⟨m, hjm⟩ : ∃ m : Fin 2, j ≠ m := by
    by_cases hj0 : j = 0
    · exact ⟨1, by rw [hj0]; decide⟩
    · exact ⟨0, hj0⟩
  have hii' : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨e, heA, het, -, hr2, hrnorm, htm⟩ := hF.exists_config hin hC hii' (hnd 0) hjm hj
  set r := e * e with hrdef
  have hrA : r ∈ aschbacherThm5Preimage D (Abar 0) := Subgroup.mul_mem _ heA heA
  have hrt : r * t = t * r := by rw [hrdef, mul_assoc, het, ← mul_assoc, het, mul_assoc]
  have hr1 : r ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hr2
    omega
  have hnd' : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g k) :=
    fun k => not_dihedral_conjFactor (hnd k) g
  have hrY : r ∈ aschbacherThm5Preimage D (Abar 0) ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨hrA, Subgroup.mem_centralizer_singleton_iff.mpr hrt⟩
  obtain ⟨R, hR, hrR'⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hrY)
    (isPGroup_zpowers_two (k := 1) (by rw [pow_one, ← hr2]; exact pow_orderOf_eq_one r))
  have hrR : r ∈ R := hrR' (Subgroup.mem_zpowers r)
  have htX : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) ⊓
      Subgroup.centralizer ({r} : Set G) :=
    ⟨htm, Subgroup.mem_centralizer_singleton_iff.mpr hrt.symm⟩
  obtain ⟨T, hT, htT'⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr htX)
    (isPGroup_zpowers_two (k := 1) (by rw [pow_one, ← hF.two]; exact pow_orderOf_eq_one t))
  have htT : t ∈ T := htT' (Subgroup.mem_zpowers t)
  have hRL : ¬ R ≤ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) := fun h =>
    hF.false_of_le_normalizer hin hC hii' hnd hjm hrA hr2 hrt hrnorm htm hR hrR h
  have hTA : ¬ T ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar 0) : Set G) := by
    intro h
    have hF' := hF.mirror hC hii' hrA hr2 hrt hrnorm
    have htnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
        (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k)).map
          (MulAut.conj t).toMonoidHom =
        aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
          (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k) := by
      intro k
      rw [preimage_conjFactors_inv]
      exact hF.norm k
    have hrm : r ∈ aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
        (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ 0) := by
      rw [preimage_conjFactors_inv]
      exact hrA
    have hTA' : T ≤ Subgroup.normalizer ((aschbacherThm5Preimage
        (rightConjugate (rightConjugate D g) g⁻¹)
        (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ 0) : Subgroup G) :
          Set G) := by
      rw [preimage_conjFactors_inv]
      exact h
    exact hF'.false_of_le_normalizer hin hC' hjm.symm hnd' hii'.symm htm hF.two hrt.symm
      htnorm hrm hT htT hTA'
  obtain ⟨y, hyR, hyL⟩ := Set.not_subset.mp hRL
  obtain ⟨x, hxT, hxA⟩ := Set.not_subset.mp hTA
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hR.le hyR).2
  have hyK : y ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [normalizer_rightConjugate]
    exact (hF.hyp71 hC).centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hyt)
  have hymap := map_eq_other_of_ne hC'.hyp hyK hjm.symm
    (fun h => hyL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  have htj : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j) := by
    rw [← hymap]
    refine ⟨t, htm, ?_⟩
    change y * t * y⁻¹ = t
    rw [hyt, mul_inv_cancel_right]
  have hxr : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.mp (hT.le hxT).2
  have hxH : x ∈ Subgroup.normalizer (D : Set G) :=
    centralizer_le_of_mem_factor hC hrA (two_power_of_orderOf hr2) hr1
      (Subgroup.mem_centralizer_singleton_iff.mpr hxr)
  have hxmap := map_eq_other_of_ne hC.hyp hxH hii'
    (fun h => hxA (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  have hrA' : r ∈ aschbacherThm5Preimage D (Abar 1) := by
    rw [← hxmap]
    refine ⟨r, hrA, ?_⟩
    change x * r * x⁻¹ = r
    rw [hxr, mul_inv_cancel_right]
  apply hd hC t g r hF.mem hF.two hF.not_mem hF.norm hnd hr2 hrt (preimage_le D _ hrA) ?_ ?_
    hrnorm
  · intro k
    rcases fin_two_cases hii' k with h | h
    · rw [h]
      exact cross_factor_centralizes D Abar hC.hyp.hcomm 0 1 hii' r hrA'
    · rw [h]
      exact cross_factor_centralizes D Abar hC.hyp.hcomm 1 0 hii'.symm r hrA
  · intro k
    apply (centralizes_conj_iff D Abar g k t).mp
    rcases fin_two_cases hjm k with h | h
    · rw [h]
      exact cross_factor_centralizes _ (conjFactors D Abar g) hC'.hyp.hcomm j m hjm t htm
    · rw [h]
      exact cross_factor_centralizes _ (conjFactors D Abar g) hC'.hyp.hcomm m j hjm.symm t htj

end FieldHyps

theorem lemma_7_4_dihedral_holds (hin : SectionSevenBase) (hd : CaseDImpossible) :
    ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
      {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
      Counterexample G D r Abar → ∀ t g : G, t ∈ Subgroup.normalizer (D : Set G) →
        orderOf t = 2 → g ∉ Subgroup.normalizer (D : Set G) →
        (∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
          (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)) →
        (∀ k : Fin r, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
          aschbacherThm5Preimage D (Abar k)) →
        ∀ k : Fin r,
          IsSimpleGroup (Abar k) ∧ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k) := by
  intro G _ _ D r Abar hC t g htH ht2 hg hcent hnorm
  have hF : FieldHyps D Abar t g := ⟨htH, ht2, hg, hcent, hnorm⟩
  have hdih : ∀ k : Fin r, AschbacherKnownGroup.HasDihedralSylowTwo (Abar k) := by
    have hr := hF.r_eq_two hin hC
    subst hr
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀⟩ := hcon
    exact hF.false_of_not_dihedral hin hC hd (not_dihedral_factor hin hC hk₀)
  intro k
  exact ⟨isSimpleGroup_of_semisimple_dihedral (Abar k) (hC.hyp.hsemisimple k)
    (factor_odd_normal_eq_bot hC.hyp k) (hdih k), hdih k⟩

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
