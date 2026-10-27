module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndThm3
public import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.Mathlib.GroupTheory.ConjCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndTight

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_isKleinFour_le_of_bar {D : Subgroup G} {V : Subgroup (Bar D)} (hV : IsKleinFour V)
    (hVD : V ≤ bar D D) {τ : G} (hτN : τ ∈ normalizer (D : Set G)) (hτ2 : τ ^ 2 = 1)
    (hVτ : V ≤ centralizer ({toBar D ⟨τ, hτN⟩} : Set (Bar D))) :
    ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ D ⊓ centralizer ({τ} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := Open.aschbacherThm5Core D with hOdef
  have hOD : O ≤ D := AschbacherTheorem5.core_le D
  have hOodd : Odd (Nat.card O) := AschbacherTheorem5.core_odd D
  have hNO : ∀ x ∈ normalizer (D : Set G), x ∈ normalizer (O : Set G) := fun x hx =>
    normalizer_le_normalizer_core D hx
  set Vt := (V.comap (toBar D)).map (normalizer (D : Set G)).subtype ⊓ D with hVtdef
  have hVtN : Vt ≤ normalizer (D : Set G) := inf_le_left.trans (map_subtype_le _)
  have hbar : bar D Vt = V := by
    apply le_antisymm
    · intro x hx
      obtain ⟨h, hh, rfl⟩ := (mem_bar_iff D Vt x).mp hx
      obtain ⟨⟨h', hh'V, hh'⟩, -⟩ := mem_inf.mp hh
      have : h' = h := Subtype.ext hh'
      rw [← this]
      exact hh'V
    · intro x hx
      obtain ⟨h, hhD, rfl⟩ := (mem_bar_iff D D x).mp (hVD hx)
      exact toBar_mem_bar D (mem_inf.mpr ⟨⟨h, hx, rfl⟩, hhD⟩)
  obtain ⟨W₀, hW₀⟩ := exists_isSylowOf 2 Vt
  have hW₀p := hW₀.isPGroup
  have hW₀N : W₀ ≤ normalizer (D : Set G) := hW₀.le.trans hVtN
  have hsyl := isSylowOf_bar (D := D) hW₀ hVtN
  rw [hbar] at hsyl
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hW₀V : bar D W₀ = V := (hsyl.eq_of_le hsyl.le le_rfl hVp).symm
  have hW₀4 : Nat.card W₀ = 4 := by
    rw [← card_bar_of_isPGroup (D := D) hW₀p hW₀N, hW₀V, hV.card_four]
  have hW₀2 : ∀ w ∈ W₀, w ^ 2 = 1 := by
    intro w hw
    have hwN := hW₀N hw
    have h1 : toBar D ⟨w, hwN⟩ ∈ V := hW₀V ▸ toBar_mem_bar D hw
    have h2 : toBar D (⟨w, hwN⟩ ^ 2) = toBar D 1 := by
      rw [map_pow, map_one]
      exact sq_eq_one_of_isKleinFour hV h1
    have h3 := toBar_injOn_of_isPGroup (D := D) hW₀p (u := ⟨w, hwN⟩ ^ 2) (v := 1)
      (by simpa using pow_mem hw 2) (one_mem _) h2
    exact congrArg Subtype.val h3
  have hτO : τ ∈ normalizer (O : Set G) := hNO τ hτN
  have hW₀O : W₀ ≤ normalizer (O : Set G) := fun w hw => hNO w (hW₀N hw)
  have hwF : ∀ w ∈ W₀, w⁻¹ * (τ * w * τ⁻¹) ∈ O := by
    intro w hw
    have hwN := hW₀N hw
    have h1 : toBar D ⟨w, hwN⟩ ∈ V := hW₀V ▸ toBar_mem_bar D hw
    have h2 := mem_centralizer_singleton_iff.mp (hVτ h1)
    have h3 : toBar D (⟨w, hwN⟩⁻¹ * (⟨τ, hτN⟩ * ⟨w, hwN⟩ * ⟨τ, hτN⟩⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
      group
    exact (toBar_eq_one_iff D _).mp h3
  obtain ⟨k, hk, hkC⟩ := exists_conj_le_centralizer_of_odd hOodd hW₀O hW₀p hτ2 hτO hwF
  have hW₀D : W₀ ≤ D := hW₀.le.trans inf_le_right
  have hkD : k ∈ D := (sup_le hW₀D hOD) hk
  refine ⟨conjugate W₀ k, ?_, le_inf (fun x hx => ?_) hkC⟩
  · exact isKleinFour_of_card_eq_four (by rw [card_conjugate_eq_card, hW₀4])
      (sq_eq_one_of_mem_conjugate hW₀2 k)
  · rw [mem_conjugate_iff] at hx
    have h1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rw [← h1]
    exact mul_mem (mul_mem (inv_mem hkD) (hW₀D hx)) hkD

theorem isSylowOf_P {C Cg A : Subgroup G} (hASyl : IsSylowOf 2 A (Cg ⊓ normalizer (C : Set G)))
    (hAN : A ≤ normalizer (C : Set G)) :
    IsSylowOf 2 A ((Cg ⊓ (C ⊔ A)) ⊔ Open.aschbacherThm5Core C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := Open.aschbacherThm5Core C with hOdef
  set B := Cg ⊓ (C ⊔ A) with hBdef
  have hCAN : C ⊔ A ≤ normalizer (C : Set G) := sup_le le_normalizer hAN
  have hAB : A ≤ B := le_inf (hASyl.le.trans inf_le_left) le_sup_right
  have hAsylB : IsSylowOf 2 A B := hASyl.of_le hAB (inf_le_inf_left _ hCAN)
  have hBO : B ≤ normalizer (O : Set G) := fun b hb =>
    normalizer_le_normalizer_core C (hCAN (mem_inf.mp hb).2)
  have hOP : O ≤ B ⊔ O := le_sup_right
  have : (O.subgroupOf (B ⊔ O)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOP).mpr (sup_le hBO le_normalizer)
  have hfac : ∀ p ∈ B ⊔ O, ∃ b ∈ B, ∃ o ∈ O, p = b * o := by
    intro p hp
    have h1 : p ∈ ((B : Set G) * O) := by
      rw [← coe_mul_of_left_le_normalizer_right B O hBO]
      exact hp
    obtain ⟨b, hb, o, ho, rfl⟩ := Set.mem_mul.mp h1
    exact ⟨b, hb, o, ho, rfl⟩
  have hidx := relIndex_eq_relIndex_inf_of_mul le_sup_left hOP hfac
  have hodd : ¬ 2 ∣ B.relIndex (B ⊔ O) := by
    rw [hidx]
    intro h2
    exact (Nat.not_even_iff_odd.mpr (AschbacherTheorem5.core_odd C)) (even_iff_two_dvd.mpr
      (h2.trans (Subgroup.relIndex_dvd_card _ _)))
  have hA' := isSylowOf_iff.mp hAsylB
  refine isSylowOf_iff.mpr ⟨hAB.trans le_sup_left, hA'.2.1, fun h2 => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex A B (B ⊔ O) hAB le_sup_left] at h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  exacts [hA'.2.2 h, hodd h]

theorem tight_P {C Cg A : Subgroup G} (hCg : TightlyEmbedded Cg)
    (hASyl : IsSylowOf 2 A (Cg ⊓ normalizer (C : Set G))) (hAN : A ≤ normalizer (C : Set G)) :
    ∀ y ∈ C ⊔ A, y ∉ normalizer (((Cg ⊓ (C ⊔ A)) ⊔ Open.aschbacherThm5Core C : Subgroup G) :
        Set G) →
      Odd (Nat.card (((Cg ⊓ (C ⊔ A)) ⊔ Open.aschbacherThm5Core C) ⊓
        rightConjugate ((Cg ⊓ (C ⊔ A)) ⊔ Open.aschbacherThm5Core C) y : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := Open.aschbacherThm5Core C with hOdef
  set B := Cg ⊓ (C ⊔ A) with hBdef
  set P := B ⊔ O with hPdef
  have hOC : O ≤ C := AschbacherTheorem5.core_le C
  have hCAN : C ⊔ A ≤ normalizer (C : Set G) := sup_le le_normalizer hAN
  have hBO : B ≤ normalizer (O : Set G) := fun b hb =>
    normalizer_le_normalizer_core C (hCAN (mem_inf.mp hb).2)
  have hAP : IsSylowOf 2 A P := isSylowOf_P hASyl hAN
  have hAB : A ≤ B := le_inf (hASyl.le.trans inf_le_left) le_sup_right
  have hconjB : ∀ v ∈ P, orderOf v = 2 → ∃ o ∈ O, o⁻¹ * v * o ∈ B := by
    intro v hv hv2
    have hvp : IsPGroup 2 (zpowers v) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hv2, pow_one])
    obtain ⟨k, hkP, hk⟩ := exists_conj_le_of_isSylowOf hAP (zpowers_le.mpr hv) hvp
    have h1 : k ∈ ((O : Set G) * B) := by
      rw [← coe_mul_of_right_le_normalizer_left O B hBO, sup_comm]
      exact hkP
    obtain ⟨o, ho, b, hb, rfl⟩ := Set.mem_mul.mp h1
    refine ⟨o, ho, ?_⟩
    have h2 : (o * b)⁻¹ * v * (o * b) ∈ B := hAB (hk v (mem_zpowers v))
    have h3 : o⁻¹ * v * o = b * ((o * b)⁻¹ * v * (o * b)) * b⁻¹ := by group
    rw [h3]
    exact mul_mem (mul_mem hb h2) (inv_mem hb)
  intro y hy hyP
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ rightConjugate P y)) 2
    (even_iff_two_dvd.mp hodd)
  have hv2 : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv
  obtain ⟨hvP, hvPy⟩ := mem_inf.mp v.2
  have hyvP : y * v * y⁻¹ ∈ P := (mem_rightConjugate_iff P y v).mp hvPy
  have hyv2 : orderOf (y * v * y⁻¹) = 2 := by
    rw [← hv2]
    exact MulEquiv.orderOf_eq (MulAut.conj y) v
  obtain ⟨o, ho, hoB⟩ := hconjB v hvP hv2
  obtain ⟨o', ho', ho'B⟩ := hconjB _ hyvP hyv2
  set z := o'⁻¹ * y * o with hzdef
  set v₁ := o⁻¹ * v * o with hv₁def
  have hv₁ : orderOf v₁ = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj o⁻¹) v
    rw [MulAut.conj_apply, inv_inv] at h
    rw [hv₁def, h, hv2]
  have hzv : z * v₁ * z⁻¹ = o'⁻¹ * (y * v * y⁻¹) * o' := by rw [hzdef, hv₁def]; group
  have hzCg : z ∈ normalizer (Cg : Set G) := by
    by_contra hz
    have h1 := hCg.2 z hz
    have hmem : v₁ ∈ Cg ⊓ rightConjugate Cg z := mem_inf.mpr ⟨(mem_inf.mp hoB).1, by
      rw [mem_rightConjugate_iff, hzv]
      exact (mem_inf.mp ho'B).1⟩
    have h2 : 2 ∣ Nat.card (Cg ⊓ rightConjugate Cg z : Subgroup G) := by
      rw [← hv₁]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  have hzCA : z ∈ C ⊔ A := mul_mem (mul_mem (inv_mem (le_sup_left (a := C) (hOC ho'))) hy)
    (le_sup_left (a := C) (hOC ho))
  have hzB : conjugate B z = B := by
    rw [hBdef, conjugate, Subgroup.map_inf_eq _ _ _ (MulAut.conj z⁻¹).injective]
    change conjugate Cg z ⊓ conjugate (C ⊔ A) z = Cg ⊓ (C ⊔ A)
    rw [conjugate_eq_of_mem_normalizer hzCg, conjugate_eq_of_mem_normalizer (le_normalizer hzCA)]
  have hzO : conjugate O z = O :=
    conjugate_eq_of_mem_normalizer (normalizer_le_normalizer_core C (hCAN hzCA))
  have hzP : z ∈ normalizer (P : Set G) := by
    apply mem_normalizer_of_conjugate_eq
    rw [hPdef, UnbalancedLayer.conjugate_sup, hzB, hzO]
  apply hyP
  have hOP : O ≤ P := le_sup_right
  have h1 : y = o' * z * o⁻¹ := by rw [hzdef]; group
  rw [h1]
  exact mul_mem (mul_mem (le_normalizer (hOP ho')) hzP) (inv_mem (le_normalizer (hOP ho)))

omit [Finite G] in
private theorem centralizer_le_normalizer_rightConjugate {C : Subgroup G}
    (hCcent : ∀ t : G, t ∈ C → orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (C : Set G))
    {g t : G} (ht : t ∈ rightConjugate C g) (ht2 : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer (rightConjugate C g : Set G) := by
  rw [rightConjugate] at ht
  obtain ⟨c, hcC, hct⟩ := Subgroup.mem_map.mp ht
  have hct' : g⁻¹ * c * g = t := by simpa [MulAut.conj_apply] using hct
  have hc2 : orderOf c = 2 := by
    have h := ht2
    rw [← hct'] at h
    have h' : orderOf ((MulAut.conj g⁻¹) c) = 2 := by
      simpa [MulAut.conj_apply] using h
    simpa using ((MulEquiv.orderOf_eq (MulAut.conj g⁻¹) c).symm.trans h')
  have hcentc := hCcent c hcC hc2
  have hmapnorm : (Subgroup.normalizer (C : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      Subgroup.normalizer (rightConjugate C g : Set G) := by
    simpa [rightConjugate, conjugate] using (GSThmB.conjugate_normalizer C g)
  calc
    Subgroup.centralizer ({t} : Set G) =
        (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_conj_centralizer_singleton g⁻¹ c]
      rw [show g⁻¹ * c * (g⁻¹)⁻¹ = t by simpa using hct']
    _ ≤ (Subgroup.normalizer (C : Set G)).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono hcentc
    _ = Subgroup.normalizer (rightConjugate C g : Set G) := hmapnorm

theorem exists_isKleinFour_le_of_tight_thm3
    {C : Subgroup G} (hCtight : TightlyEmbedded C)
    {g : G} (hg : g ∉ Subgroup.normalizer (C : Set G))
    {A : Subgroup G}
    (hASyl : IsSylowOf 2 A (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)))
    {a : G} (haA : a ∈ A) (ha2 : orderOf a = 2)
    (huniqA : ∀ x ∈ A, orderOf x = 2 → x = a)
    (hE8 : ∃ E : Subgroup G, E ≤ C ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8)
    (h3 : AschbacherTheorem3.Theorem3Statement) :
    ∃ W : Subgroup G, IsKleinFour W ∧
      W ≤ C ⊓ Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : C ≤ Subgroup.normalizer (C : Set G) := le_normalizer
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha2
    omega
  obtain ⟨T, hAT⟩ := hASyl
  subst A
  have hASyl : IsSylowOf 2 (sylowImage (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)) T)
      (rightConjugate C g ⊓ Subgroup.normalizer (C : Set G)) := ⟨T, rfl⟩
  have hAN : sylowImage (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)) T ≤ Subgroup.normalizer (C : Set G) :=
    overlap_sylow_le_normalizer C g T
  have hAp : IsPGroup 2 (sylowImage (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)) T) := hASyl.isPGroup
  have hA1 : sylowImage (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)) T ≠ ⊥ := by
    intro hbot
    have : a ∈ (⊥ : Subgroup G) := hbot ▸ haA
    rw [Subgroup.mem_bot] at this
    exact ha1 this
  have hAC : sylowImage (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)) T ⊓ C = ⊥ :=
    overlap_sylow_inf_eq_bot C hCtight g hg T
  let A : Subgroup G := sylowImage (rightConjugate C g ⊓
    Subgroup.normalizer (C : Set G)) T
  have haA' : a ∈ sylowImage (rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)) T := haA
  set CA := C ⊔ A with hCAdef
  have hCAN : CA ≤ Subgroup.normalizer (C : Set G) := sup_le hCN hAN
  obtain ⟨S₀, hS₀, hAS₀⟩ := exists_isSylowOf_ge_of_le
    (le_inf le_sup_right le_normalizer : A ≤ CA ⊓ Subgroup.normalizer (A : Set G)) hAp
  obtain ⟨S, hS, hS₀S⟩ := exists_isSylowOf_ge_of_le (hS₀.le.trans inf_le_left) hS₀.isPGroup
  have hAS : A ≤ S := hAS₀.trans hS₀S
  have hSN : IsSylowOf 2 (S ⊓ Subgroup.normalizer (A : Set G))
      (CA ⊓ Subgroup.normalizer (A : Set G)) := by
    have h1 : S ⊓ Subgroup.normalizer (A : Set G) = S₀ := hS₀.eq_of_le
      (le_inf hS₀S (hS₀.le.trans inf_le_right)) (inf_le_inf_right _ hS.le)
      hS.isPGroup.to_inf_left
    rw [h1]
    exact hS₀
  have hS'' := hS
  obtain ⟨S', hS'⟩ := hS''
  have hSS' : sylowImage CA S' = S := hS'
  have hAsS' : A ≤ sylowImage CA S' := hSS' ▸ hAS
  obtain ⟨-, -, hcomm, mult, factor, -, -⟩ :=
    theorem_2_part_one C hCtight g hg T S' hAsS' hA1
  set R := relativeNormalizer A (sylowImage CA S') ⊓ C with hRdef
  have hNrel : relativeNormalizer A (sylowImage CA S') = S ⊓ Subgroup.normalizer (A : Set G) := by
    rw [relativeNormalizer, hSS', inf_comm]
  have hRA : Nat.card R = Nat.card A := (Nat.card_congr factor.toEquiv).symm
  have hidx : A.relIndex (S ⊓ Subgroup.normalizer (A : Set G)) ≤ Nat.card A := by
    have h1 : Nat.card (relativeNormalizer A (sylowImage CA S')) = Nat.card A * Nat.card R := by
      rw [← Nat.card_prod, Nat.card_congr mult.toEquiv]
    have hAle : A ≤ S ⊓ Subgroup.normalizer (A : Set G) := le_inf hAS le_normalizer
    have h2 := Subgroup.relIndex_mul_card A (S ⊓ Subgroup.normalizer (A : Set G))
    rw [inf_eq_left.mpr hAle, ← hNrel, h1, hRA] at h2
    have hpos : 0 < Nat.card A := Nat.card_pos
    have h3 : A.relIndex (S ⊓ Subgroup.normalizer (A : Set G)) = Nat.card A := by
      rw [← hNrel]
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    omega
  have hCtight' : TightlyEmbedded (rightConjugate C g) :=
    CFSG.StandardSubgroupAPI.tightlyEmbedded_rightConjugate hCtight g
  set O := Open.aschbacherThm5Core C with hOdef
  have hOC : O ≤ C := AschbacherTheorem5.core_le _
  have hPCA : (rightConjugate C g ⊓ (C ⊔ A)) ⊔ O ≤ C ⊔ A :=
    sup_le inf_le_right (hOC.trans le_sup_left)
  have hTP := isSylowOf_P hASyl hAN
  have heven : Even (Nat.card ↥((rightConjugate C g ⊓ (C ⊔ A)) ⊔ O)) := by
    have h1 : 2 ∣ Nat.card ↥((rightConjugate C g ⊓ (C ⊔ A)) ⊔ O) := by
      rw [← ha2]
      exact Subgroup.orderOf_dvd_natCard _ (hTP.le haA)
    exact even_iff_two_dvd.mpr h1
  have hconc := thm3_bar h3 (D := C) le_rfl hOC hCN hAN hAN hAp hA1 hAC hPCA hTP
    heven (tight_P hCtight' hASyl hAN) hS hAS hSN hidx
  have haN : a ∈ Subgroup.normalizer (C : Set G) := hAN haA
  obtain ⟨E, hEC, hEel, hE8card⟩ := hE8
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := hEel.2
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE8card]; norm_num)
  have habar1 : toBar C ⟨a, haN⟩ ≠ 1 := by
    intro h1
    have h2 : a ∈ A ⊓ C :=
      mem_inf.mpr ⟨haA, hOC ((toBar_eq_one_iff _ _).mp h1)⟩
    rw [hAC, mem_bot] at h2
    exact ha1 h2
  have habar : orderOf (toBar C ⟨a, haN⟩) = 2 := by
    refine orderOf_eq_prime ?_ habar1
    rw [← map_pow]
    have hsq : (⟨a, haN⟩ : normalizer (C : Set G)) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← ha2]
      exact pow_orderOf_eq_one a)
    rw [hsq, map_one]
  have huniqbar : ∀ x ∈ bar C A, orderOf x = 2 → x = toBar C ⟨a, haN⟩ := by
    intro x hx hx2
    obtain ⟨y, hyA, rfl⟩ := (mem_bar_iff _ A x).mp hx
    have hy2 : y ^ 2 = 1 := by
      have h1 : toBar C (y ^ 2) = toBar C 1 := by
        rw [map_pow, map_one, ← hx2]
        exact pow_orderOf_eq_one _
      exact toBar_injOn_of_isPGroup hAp (by simpa using pow_mem hyA 2) (one_mem _) h1
    have hy1 : y ≠ 1 := fun h1 => by rw [h1, map_one, orderOf_one] at hx2; omega
    have hy2' : (y : G) ^ 2 = 1 := by
      have := congrArg Subtype.val hy2
      simpa using this
    have hyord : orderOf (y : G) = 2 :=
      orderOf_eq_prime hy2' fun h1 => hy1 (Subtype.ext h1)
    rw [show y = ⟨a, haN⟩ from Subtype.ext (huniqA y hyA hyord)]
  have hE2bar : ∀ x ∈ bar C E, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hyE, rfl⟩ := (mem_bar_iff _ E x).mp hx
    have : y ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE2 _ hyE)
    rw [← map_pow, this, map_one]
  have hE8bar : Nat.card (bar C E) = 8 := by
    rw [card_bar_of_isPGroup hEp (hEC.trans hCN), hE8card]
  have hbot : bar C A ⊓ bar C C = ⊥ := by
    rw [← bar_inf_of_core_le hOC, hAC, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hSbar : IsSylowOf 2 (bar C S) (bar C C ⊔ bar C A) := by
    rw [← bar_sup hCN hAN]
    exact isSylowOf_bar hS (sup_le hCN hAN)
  obtain ⟨V, hV, hVle⟩ := exists_isKleinFour_of_thm3Conclusion hconc
    (bar_le_normalizer hAN hCN) hbot hSbar (bar_mono _ hAS) (toBar_mem_bar _ haA')
    habar huniqbar (bar_mono _ hEC) hE2bar hE8bar
  obtain ⟨W, hW, hWle⟩ := exists_isKleinFour_le_of_bar hV
    (hVle.trans inf_le_left) haN (by rw [← ha2]; exact pow_orderOf_eq_one a)
    (hVle.trans inf_le_right)
  exact ⟨W, hW, hWle⟩


theorem false_of_sylow_unique_involution_of_tight
    {C : Subgroup G}
    (hCtight : TightlyEmbedded C)
    (hCcent : ∀ t : G, t ∈ C → orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (C : Set G))
    (hE8 : ∃ E : Subgroup G, E ≤ C ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8)
    (h3 : AschbacherTheorem3.Theorem3Statement)
    {g : G} (hg : g ∉ Subgroup.normalizer (C : Set G))
    (hmax : ∀ g' : G, g' ∉ Subgroup.normalizer (C : Set G) →
      (Nat.card ↥(rightConjugate C g' ⊓
        Subgroup.normalizer (C : Set G))).factorization 2 ≤
      (Nat.card ↥(rightConjugate C g ⊓
        Subgroup.normalizer (C : Set G))).factorization 2)
    (T : Sylow 2 ↥(rightConjugate C g ⊓
      Subgroup.normalizer (C : Set G)))
    (hT1 : sylowImage _ T ≠ ⊥)
    (hrank : ∀ U : Subgroup G, U ≤ sylowImage _ T → ¬ IsKleinFour U) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : C ≤ normalizer (C : Set G) := le_normalizer
  set A := sylowImage (rightConjugate (C) g ⊓
    normalizer (C : Set G)) T with hAdef
  have hAp : IsPGroup 2 A := sylowImage_isPGroup _ T
  have hAN : A ≤ normalizer (C : Set G) := overlap_sylow_le_normalizer _ g T
  have hACg : A ≤ rightConjugate (C) g := overlap_sylow_le_conjugate _ g T
  have hAC : A ⊓ C = ⊥ := overlap_sylow_inf_eq_bot _ hCtight g hg T
  have hASyl : IsSylowOf 2 A (rightConjugate (C) g ⊓
      normalizer (C : Set G)) := ⟨T, rfl⟩
  obtain ⟨τ, hτA, hτ, hτZ⟩ := exists_involution_central hAp hT1
  have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hτ; omega
  have huniq : ∀ x ∈ A, orderOf x = 2 → x = τ := by
    intro x hx hx2
    by_contra hxτ
    have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx2; omega
    have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    exact hrank _ (sup_le (zpowers_le.mpr hτA) (zpowers_le.mpr hx))
      (isKleinFour_sup_zpowers hτ2 hx2' hτ1 hx1 hxτ (hτZ x hx).symm)
  set CA := C ⊔ A with hCAdef
  have hCAN : CA ≤ normalizer (C : Set G) := sup_le hCN hAN
  obtain ⟨S₀, hS₀, hAS₀⟩ := exists_isSylowOf_ge_of_le
    (le_inf le_sup_right le_normalizer : A ≤ CA ⊓ normalizer (A : Set G)) hAp
  obtain ⟨S, hS, hS₀S⟩ := exists_isSylowOf_ge_of_le (hS₀.le.trans inf_le_left) hS₀.isPGroup
  have hAS : A ≤ S := hAS₀.trans hS₀S
  have hSN : IsSylowOf 2 (S ⊓ normalizer (A : Set G)) (CA ⊓ normalizer (A : Set G)) := by
    have h1 : S ⊓ normalizer (A : Set G) = S₀ := hS₀.eq_of_le
      (le_inf hS₀S (hS₀.le.trans inf_le_right)) (inf_le_inf_right _ hS.le)
      hS.isPGroup.to_inf_left
    rw [h1]
    exact hS₀
  have hS'' := hS
  obtain ⟨S', hS'⟩ := hS''
  have hSS' : sylowImage CA S' = S := hS'
  have hAsS' : A ≤ sylowImage CA S' := hSS' ▸ hAS
  obtain ⟨-, -, hcomm, mult, factor, -, -⟩ :=
    theorem_2_part_one C hCtight g hg T S' hAsS' hT1
  set R := relativeNormalizer A (sylowImage CA S') ⊓ C with hRdef
  have hNrel : relativeNormalizer A (sylowImage CA S') = S ⊓ normalizer (A : Set G) := by
    rw [relativeNormalizer, hSS', inf_comm]
  have hRA : Nat.card R = Nat.card A := (Nat.card_congr factor.toEquiv).symm
  have hidx : A.relIndex (S ⊓ normalizer (A : Set G)) ≤ Nat.card A := by
    have h1 : Nat.card (relativeNormalizer A (sylowImage CA S')) = Nat.card A * Nat.card R := by
      rw [← Nat.card_prod, Nat.card_congr mult.toEquiv]
    have hAle : A ≤ S ⊓ normalizer (A : Set G) := le_inf hAS le_normalizer
    have h2 := Subgroup.relIndex_mul_card A (S ⊓ normalizer (A : Set G))
    rw [inf_eq_left.mpr hAle, ← hNrel, h1, hRA] at h2
    have hpos : 0 < Nat.card A := Nat.card_pos
    have h3 : A.relIndex (S ⊓ normalizer (A : Set G)) = Nat.card A := by
      rw [← hNrel]
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    omega
  have hτCg : τ ∈ rightConjugate C g := hACg hτA
  have hCτN : centralizer ({τ} : Set G) ≤
      normalizer (rightConjugate C g : Set G) :=
    centralizer_le_normalizer_rightConjugate hCcent hτCg hτ
  set Y := C ⊓ normalizer (rightConjugate C g : Set G) with hYdef
  have hRY : R ≤ Y := le_inf inf_le_right fun r hr =>
    hCτN (mem_centralizer_singleton_iff.mpr (hcomm τ hτA r hr).symm)
  have hYconj : Y = conjugate (rightConjugate (C) g⁻¹ ⊓
      normalizer (C : Set G)) g := by
    rw [conjugate, Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective]
    change Y = conjugate (conjugate (C) g⁻¹) g ⊓
      conjugate (normalizer (C : Set G)) g
    rw [UnbalancedLayer.conjugate_conjugate, inv_mul_cancel, UnbalancedLayer.conjugate_one,
      GSThmB.conjugate_normalizer]
    rfl
  have hginv : g⁻¹ ∉ normalizer (C : Set G) := fun h1 => hg (by simpa using inv_mem h1)
  have hYcard : Nat.card Y = Nat.card ↥(rightConjugate (C) g⁻¹ ⊓
      normalizer (C : Set G)) := by rw [hYconj, card_conjugate_eq_card]
  have hRSyl : IsSylowOf 2 R Y := by
    refine isSylowOf_of_card hRY ?_
    have hYpos : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    have h1 := hmax g⁻¹ hginv
    rw [← hYcard] at h1
    have h2 : Nat.card R = 2 ^ (Nat.card ↥(rightConjugate (C) g ⊓
        normalizer (C : Set G))).factorization 2 := by
      rw [hRA, hASyl.card_eq]
    have h3 : 2 ^ (Nat.card ↥(rightConjugate (C) g ⊓
        normalizer (C : Set G))).factorization 2 ∣ Nat.card Y := by
      rw [← h2]
      exact Subgroup.card_dvd_of_le hRY
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hYpos).mp h3
    rw [h2, le_antisymm h1 h4]
  have hnoV : ∀ V : Subgroup G, IsKleinFour V →
      V ≤ C ⊓ centralizer ({τ} : Set G) → False := by
    intro V hV hVle
    have hVY : V ≤ Y := le_inf (hVle.trans inf_le_left) (hVle.trans (inf_le_right.trans hCτN))
    have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hRSyl hVY hVp
    set V' := conjugate V k with hV'def
    have hV'R : V' ≤ R := conjugate_le_of_forall hk
    have hV'2 : ∀ x ∈ V', x ^ 2 = 1 :=
      sq_eq_one_of_mem_conjugate (fun x hx => sq_eq_one_of_isKleinFour hV hx) k
    set U := ((V'.subgroupOf R).map factor.symm.toMonoidHom).map A.subtype with hUdef
    refine hrank U (map_subtype_le _) (isKleinFour_of_card_eq_four ?_ ?_)
    · rw [hUdef, card_map_of_injective A.subtype_injective,
        card_map_of_injective factor.symm.injective,
        Nat.card_congr (subgroupOfEquivOfLe hV'R).toEquiv, hV'def, card_conjugate_eq_card,
        hV.card_four]
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hu2 : u ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hV'2 _ hu)
      show ((factor.symm u : A) : G) ^ 2 = 1
      rw [← SubgroupClass.coe_pow, ← map_pow, hu2, map_one, OneMemClass.coe_one]
  obtain ⟨W, hW, hWle⟩ := exists_isKleinFour_le_of_tight_thm3 hCtight hg hASyl
    hτA hτ huniq hE8 h3
  exact hnoV W hW hWle


theorem false_of_sylow_unique_involution (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (h3 : AschbacherTheorem3.Theorem3Statement)
    {M : Subgroup G} (hM : IsFooteM L M) (hne : FooteNoEscape M) {g : G}
    (hg : g ∉ normalizer (M : Set G))
    (hmax : ∀ g' : G, g' ∉ normalizer (M : Set G) →
      (Nat.card ↥(rightConjugate (coreActionKernel M) g' ⊓
        normalizer (coreActionKernel M : Set G))).factorization 2 ≤
      (Nat.card ↥(rightConjugate (coreActionKernel M) g ⊓
        normalizer (coreActionKernel M : Set G))).factorization 2)
    (T : Sylow 2 ↥(rightConjugate (coreActionKernel M) g ⊓
      normalizer (coreActionKernel M : Set G)))
    (hT1 : sylowImage _ T ≠ ⊥)
    (hrank : ∀ U : Subgroup G, U ≤ sylowImage _ T → ¬ IsKleinFour U) : False := by
  have hNC := normalizer_coreActionKernel_eq h h47 hST hM
  have htight := tightlyEmbedded_coreActionKernel h h47 hST hM hne
  have hgC : g ∉ normalizer (coreActionKernel M : Set G) := by
    rw [hNC]
    exact hg
  have hCcent : ∀ t : G, t ∈ coreActionKernel M → orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer (coreActionKernel M : Set G) := by
    intro t ht ht2
    rw [hNC]
    exact hne t ht ht2
  obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
  have hEel : CFSG.Open.IsElemAbelian 2 E :=
    ⟨isMulCommutative_of_sq_eq_one hE2, hE2⟩
  exact false_of_sylow_unique_involution_of_tight htight hCcent
    ⟨E, hEC, hEel, hE8⟩ h3 hgC (by simpa [hNC] using hmax) T hT1 hrank

end CFSG.ComponentClassification.FooteLit
