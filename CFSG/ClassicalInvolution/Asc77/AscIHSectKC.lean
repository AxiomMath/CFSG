module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Main

public section

namespace CFSG.ClassicalInvolution.Asc77.Hub

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups

section Coordinates

variable {F : Type} [Field F]

abbrev Idx := Fin 4 ⊕ Fin 4

@[expose] def dvec (c : Fin 4 → F) : Idx → F := Sum.elim c c

theorem quadPlus_dvec (c : Fin 4 → F) : quadPlus 4 F (dvec c) = ∑ a, c a * c a := by
  rw [quadPlus_apply]; simp [dvec]

theorem polar_right_dvec (x : Idx → F) (c : Fin 4 → F) :
    polar (quadPlus 4 F) x (dvec c) = ∑ a, c a * (x (.inl a) + x (.inr a)) := by
  rw [polar_quadPlus]; simp [dvec]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem polar_dvec_dvec (c d : Fin 4 → F) :
    polar (quadPlus 4 F) (dvec c) (dvec d) = ∑ a, (c a * d a + d a * c a) := by
  rw [polar_quadPlus]; simp [dvec]

@[expose] def hubE1 (a b : F) : Idx → F := dvec ![1, 0, a, b]

@[expose] def hubF1 (a b w : F) : Idx → F := dvec ![w, 0, -(w * a), -(w * b)]

@[expose] def hubE2 (a b : F) : Idx → F := dvec ![0, 1, -b, a]

@[expose] def hubF2 (a b w : F) : Idx → F := dvec ![0, w, w * b, -(w * a)]

theorem hubQ_e1 (a b : F) (hab : a * a + b * b = -1) : quadPlus 4 F (hubE1 a b) = 0 := by
  simp [hubE1, quadPlus_dvec, Fin.sum_univ_four]
  linear_combination hab

theorem hubQ_f1 (a b w : F) (hab : a * a + b * b = -1) : quadPlus 4 F (hubF1 a b w) = 0 := by
  simp [hubF1, quadPlus_dvec, Fin.sum_univ_four]
  linear_combination (w * w) * hab

theorem hubP_ef1 (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    polar (quadPlus 4 F) (hubE1 a b) (hubF1 a b w) = 1 := by
  simp [hubE1, hubF1, polar_dvec_dvec, Fin.sum_univ_four]
  linear_combination (-2 * w) * hab + hw

theorem hubQ_e2 (a b : F) (hab : a * a + b * b = -1) : quadPlus 4 F (hubE2 a b) = 0 := by
  simp [hubE2, quadPlus_dvec, Fin.sum_univ_four]
  linear_combination hab

theorem hubQ_f2 (a b w : F) (hab : a * a + b * b = -1) : quadPlus 4 F (hubF2 a b w) = 0 := by
  simp [hubF2, quadPlus_dvec, Fin.sum_univ_four]
  linear_combination (w * w) * hab

theorem hubP_ef2 (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    polar (quadPlus 4 F) (hubE2 a b) (hubF2 a b w) = 1 := by
  simp [hubE2, hubF2, polar_dvec_dvec, Fin.sum_univ_four]
  linear_combination (-2 * w) * hab + hw

theorem hubP_e1e2 (a b : F) : polar (quadPlus 4 F) (hubE1 a b) (hubE2 a b) = 0 := by
  simp [hubE1, hubE2, polar_dvec_dvec, Fin.sum_univ_four]

theorem hubP_e1f2 (a b w : F) : polar (quadPlus 4 F) (hubE1 a b) (hubF2 a b w) = 0 := by
  simp [hubE1, hubF2, polar_dvec_dvec, Fin.sum_univ_four]; ring

theorem hubP_f1e2 (a b w : F) : polar (quadPlus 4 F) (hubF1 a b w) (hubE2 a b) = 0 := by
  simp [hubF1, hubE2, polar_dvec_dvec, Fin.sum_univ_four]; ring

theorem hubP_f1f2 (a b w : F) : polar (quadPlus 4 F) (hubF1 a b w) (hubF2 a b w) = 0 := by
  simp [hubF1, hubF2, polar_dvec_dvec, Fin.sum_univ_four]

@[expose] def hubFrame (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    Frame (quadPlus 4 F) where
  P := ⟨hubE1 a b, hubF1 a b w, hubQ_e1 a b hab, hubQ_f1 a b w hab, hubP_ef1 a b w hab hw⟩
  P' := ⟨hubE2 a b, hubF2 a b w, hubQ_e2 a b hab, hubQ_f2 a b w hab, hubP_ef2 a b w hab hw⟩
  orth := ⟨hubP_e1e2 a b, hubP_e1f2 a b w, hubP_f1e2 a b w, hubP_f1f2 a b w⟩

theorem hubFrame_e₁ (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    (hubFrame a b w hab hw).e₁ = hubE1 a b := rfl

theorem hubFrame_f₁ (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    (hubFrame a b w hab hw).f₁ = hubF1 a b w := rfl

theorem hubFrame_e₂ (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    (hubFrame a b w hab hw).e₂ = hubE2 a b := rfl

theorem hubFrame_f₂ (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) :
    (hubFrame a b w hab hw).f₂ = hubF2 a b w := rfl

end Coordinates

section Involutions

variable {F : Type} [Field F]

theorem incl_coords_eq (fr : Frame (quadPlus 4 F)) (x : Idx → F) :
    fr.incl (fr.coords x) = polar (quadPlus 4 F) x fr.f₁ • fr.e₁ +
      polar (quadPlus 4 F) x fr.e₁ • fr.f₁ + polar (quadPlus 4 F) x fr.f₂ • fr.e₂ +
        polar (quadPlus 4 F) x fr.e₂ • fr.f₂ := by
  rw [Frame.incl_apply, Frame.coords_apply]
  simp

@[expose] def tauMap (x : Idx → F) : Idx → F :=
  Sum.elim (fun a => - x (.inr a)) (fun a => - x (.inl a))

theorem hubFrame_La_neg_one (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1)
    (x : Idx → F) : (hubFrame a b w hab hw).La (-1) x = tauMap x := by
  rw [Frame.La_neg_one_apply, incl_coords_eq]
  simp only [hubFrame_e₁, hubFrame_f₁, hubFrame_e₂, hubFrame_f₂]
  funext μ
  have key : ∀ k : Fin 4, 2 * (polar (quadPlus 4 F) x (hubF1 a b w) * hubE1 a b (Sum.inl k) +
      polar (quadPlus 4 F) x (hubE1 a b) * hubF1 a b w (Sum.inl k) +
      polar (quadPlus 4 F) x (hubF2 a b w) * hubE2 a b (Sum.inl k) +
      polar (quadPlus 4 F) x (hubE2 a b) * hubF2 a b w (Sum.inl k)) =
      x (Sum.inl k) + x (Sum.inr k) := by
    intro k
    simp only [hubE1, hubF1, hubE2, hubF2, polar_right_dvec]
    fin_cases k <;> simp [dvec, Fin.sum_univ_four]
    · linear_combination (x (Sum.inl 0) + x (Sum.inr 0)) * hw
    · linear_combination (x (Sum.inl 1) + x (Sum.inr 1)) * hw
    · linear_combination (-4 * w * (x (Sum.inl 2) + x (Sum.inr 2))) * hab +
        (x (Sum.inl 2) + x (Sum.inr 2)) * hw
    · linear_combination (-4 * w * (x (Sum.inl 3) + x (Sum.inr 3))) * hab +
        (x (Sum.inl 3) + x (Sum.inr 3)) * hw
  rcases μ with k | k
  · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tauMap, Sum.elim_inl]
    linear_combination (-1) * key k
  · have e1 : hubE1 a b (Sum.inr k) = hubE1 a b (Sum.inl k) := rfl
    have e2 : hubF1 a b w (Sum.inr k) = hubF1 a b w (Sum.inl k) := rfl
    have e3 : hubE2 a b (Sum.inr k) = hubE2 a b (Sum.inl k) := rfl
    have e4 : hubF2 a b w (Sum.inr k) = hubF2 a b w (Sum.inl k) := rfl
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tauMap, Sum.elim_inr, e1,
      e2, e3, e4]
    linear_combination (-1) * key k

@[expose] def blockFlip (i j : Fin 4) (x : Idx → F) : Idx → F :=
  Sum.elim (fun a => if a = i ∨ a = j then - x (.inl a) else x (.inl a))
    (fun a => if a = i ∨ a = j then - x (.inr a) else x (.inr a))

section Std

variable (hn : 3 ≤ 4) {i j : Fin 4} (hij : i ≠ j) (s t : Bool)

theorem toFrame_e₁ : ((plusFrame 4 F hn).toFrame hij s t).e₁ = plusVec 4 F i s := rfl

theorem toFrame_f₁ : ((plusFrame 4 F hn).toFrame hij s t).f₁ = plusVec 4 F i (!s) := rfl

theorem toFrame_e₂ : ((plusFrame 4 F hn).toFrame hij s t).e₂ = plusVec 4 F j t := rfl

theorem toFrame_f₂ : ((plusFrame 4 F hn).toFrame hij s t).f₂ = plusVec 4 F j (!t) := rfl

theorem stdFrame_La_neg_one (x : Idx → F) :
    ((plusFrame 4 F hn).toFrame hij s t).La (-1) x = blockFlip i j x := by
  rw [Frame.La_neg_one_apply, incl_coords_eq, toFrame_e₁, toFrame_f₁, toFrame_e₂, toFrame_f₂]
  funext μ
  cases s <;> cases t <;> rcases μ with a | a <;>
    by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp [blockFlip, polar_quadPlus_single_inl, polar_quadPlus_single_inr,
      hai, haj, hij, Ne.symm hij] <;> ring

end Std

theorem blockFlip_tauMap (i j : Fin 4) (x : Idx → F) :
    blockFlip i j (tauMap x) = tauMap (blockFlip i j x) := by
  funext μ
  rcases μ with a | a <;> by_cases h : a = i ∨ a = j <;> simp [blockFlip, tauMap, h]

theorem hub_comm (hn : 3 ≤ 4) (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1)
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    (hubFrame a b w hab hw).La (-1) * ((plusFrame 4 F hn).toFrame hij s t).La (-1) =
      ((plusFrame 4 F hn).toFrame hij s t).La (-1) * (hubFrame a b w hab hw).La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, hubFrame_La_neg_one, stdFrame_La_neg_one, blockFlip_tauMap]

theorem exists_fin_four_ne_ne (i j : Fin 4) : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  revert i j
  decide

theorem hub_ne_std (hn : 3 ≤ 4) (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1)
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    (hubFrame a b w hab hw).La (-1) ≠ ((plusFrame 4 F hn).toFrame hij s t).La (-1) := by
  intro h
  obtain ⟨k, hki, hkj⟩ := exists_fin_four_ne_ne i j
  have h1 := congrArg (fun g : (Idx → F) ≃ₗ[F] (Idx → F) => g (Pi.single (.inl k) 1) (.inl k)) h
  simp [hubFrame_La_neg_one, stdFrame_La_neg_one, tauMap, blockFlip, hki, hkj] at h1

end Involutions

section Overlap

variable {F : Type} [Field F]

@[expose] def tv (a : Fin 4) : Idx → F := dvec (Pi.single a 1)

theorem quadPlus_tv (a : Fin 4) : quadPlus 4 F (tv a) = 1 := by
  simp [tv, quadPlus_dvec, Pi.single_apply]

theorem polar_tv_tv {i j : Fin 4} (hij : i ≠ j) : polar (quadPlus 4 F) (tv i) (tv j) = 0 := by
  rw [tv, tv, polar_dvec_dvec]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = i <;> by_cases hx' : x = j <;> simp_all

@[expose] noncomputable def ovMap (i j : Fin 4) : (Fin 2 → F) →ₗ[F] (Idx → F) where
  toFun c := c 0 • tv i + c 1 • tv j
  map_add' c d := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' r c := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add]

theorem ovMap_apply (i j : Fin 4) (c : Fin 2 → F) : ovMap i j c = c 0 • tv i + c 1 • tv j := rfl

theorem ovMap_injective {i j : Fin 4} (hij : i ≠ j) : Function.Injective (ovMap (F := F) i j) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  rw [ovMap_apply] at hc
  have h1 := congrFun hc (.inl i)
  have h2 := congrFun hc (.inl j)
  simp [tv, dvec, hij, Ne.symm hij] at h1 h2
  funext k
  fin_cases k
  · simpa using h1
  · simpa using h2

theorem quadPlus_ovMap {i j : Fin 4} (hij : i ≠ j) (c : Fin 2 → F) :
    quadPlus 4 F (ovMap i j c) = c 0 * c 0 + c 1 * c 1 := by
  have h2 : polar (quadPlus 4 F) (tv i) (tv j) = 0 := polar_tv_tv hij
  rw [ovMap_apply, QuadraticMap.map_add (quadPlus 4 F), QuadraticMap.map_smul,
    QuadraticMap.map_smul, quadPlus_tv, quadPlus_tv, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, h2]
  simp

theorem ovMap_inl {i j : Fin 4} (c : Fin 2 → F) (a : Fin 4) :
    ovMap i j c (.inl a) = (if a = i then c 0 else 0) + (if a = j then c 1 else 0) := by
  simp [ovMap_apply, tv, dvec, Pi.single_apply]

theorem ovMap_inr {i j : Fin 4} (c : Fin 2 → F) (a : Fin 4) :
    ovMap i j c (.inr a) = (if a = i then c 0 else 0) + (if a = j then c 1 else 0) := by
  simp [ovMap_apply, tv, dvec, Pi.single_apply]

theorem mem_negSpace_iff_apply {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (i : V ≃ₗ[K] V) (x : V) : x ∈ negSpace i ↔ i x = -x := by
  simp [negSpace]

theorem mem_negSpace_std_iff (h2 : (2 : F) ≠ 0) (hn : 3 ≤ 4) {i j : Fin 4} (hij : i ≠ j)
    (s t : Bool) (x : Idx → F) :
    x ∈ negSpace (((plusFrame 4 F hn).toFrame hij s t).La (-1)) ↔
      ∀ a, a ≠ i → a ≠ j → x (.inl a) = 0 ∧ x (.inr a) = 0 := by
  rw [mem_negSpace_iff_apply, stdFrame_La_neg_one]
  constructor
  · intro h a hai haj
    have h1 := congrFun h (.inl a)
    have h2' := congrFun h (.inr a)
    simp only [blockFlip, Sum.elim_inl, Sum.elim_inr, hai, haj, or_self, ite_false,
      Pi.neg_apply] at h1 h2'
    have e1 : (2 : F) * x (.inl a) = 0 := by linear_combination h1
    have e2 : (2 : F) * x (.inr a) = 0 := by linear_combination h2'
    exact ⟨(mul_eq_zero.mp e1).resolve_left h2, (mul_eq_zero.mp e2).resolve_left h2⟩
  · intro h
    funext μ
    rcases μ with a | a <;> by_cases ha : a = i ∨ a = j
    · simp [blockFlip, ha]
    · push Not at ha
      simp [blockFlip, ha.1, ha.2, (h a ha.1 ha.2).1]
    · simp [blockFlip, ha]
    · push Not at ha
      simp [blockFlip, ha.1, ha.2, (h a ha.1 ha.2).2]

theorem mem_negSpace_hub_iff (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1)
    (x : Idx → F) :
    x ∈ negSpace ((hubFrame a b w hab hw).La (-1)) ↔ ∀ k, x (.inr k) = x (.inl k) := by
  rw [mem_negSpace_iff_apply, hubFrame_La_neg_one]
  constructor
  · intro h k
    have h1 := congrFun h (.inl k)
    simp only [tauMap, Sum.elim_inl, Pi.neg_apply] at h1
    linear_combination -h1
  · intro h
    funext μ
    rcases μ with k | k
    · simp [tauMap, h k]
    · simp [tauMap, h k]

theorem inf_negSpace_eq_range (h2 : (2 : F) ≠ 0) (hn : 3 ≤ 4) (a b w : F)
    (hab : a * a + b * b = -1) (hw : 4 * w = 1) {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    negSpace ((hubFrame a b w hab hw).La (-1)) ⊓
        negSpace (((plusFrame 4 F hn).toFrame hij s t).La (-1)) = LinearMap.range (ovMap i j) := by
  ext x
  rw [Submodule.mem_inf, mem_negSpace_hub_iff, mem_negSpace_std_iff h2 hn hij,
    LinearMap.mem_range]
  constructor
  · rintro ⟨h1, h2'⟩
    refine ⟨![x (.inl i), x (.inl j)], ?_⟩
    funext μ
    rcases μ with k | k
    · rw [ovMap_inl]
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj, (h2' k hki hkj).1]
    · rw [ovMap_inr, h1 k]
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj, (h2' k hki hkj).1]
  · rintro ⟨c, rfl⟩
    refine ⟨fun k => ?_, fun k hki hkj => ?_⟩
    · rw [ovMap_inl, ovMap_inr]
    · rw [ovMap_inl, ovMap_inr]
      simp [hki, hkj]

theorem finrank_inf_negSpace_hub (h2 : (2 : F) ≠ 0) (hn : 3 ≤ 4) (a b w : F)
    (hab : a * a + b * b = -1) (hw : 4 * w = 1) {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    Module.finrank F ↥(negSpace ((hubFrame a b w hab hw).La (-1)) ⊓
        negSpace (((plusFrame 4 F hn).toFrame hij s t).La (-1))) = 2 := by
  rw [inf_negSpace_eq_range h2 hn a b w hab hw hij s t,
    LinearMap.finrank_range_of_inj (ovMap_injective hij)]
  simp

theorem not_hasSingularVector_hub (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) (hn : 3 ≤ 4)
    (a b w : F) (hab : a * a + b * b = -1) (hw : 4 * w = 1) {i j : Fin 4} (hij : i ≠ j)
    (s t : Bool) :
    ¬ HasSingularVector (quadPlus 4 F) (negSpace ((hubFrame a b w hab hw).La (-1)) ⊓
        negSpace (((plusFrame 4 F hn).toFrame hij s t).La (-1))) := by
  rw [inf_negSpace_eq_range h2 hn a b w hab hw hij s t]
  rintro ⟨v, ⟨c, rfl⟩, hv0, hQ⟩
  rw [quadPlus_ovMap hij] at hQ
  apply hv0
  have h1 : c 1 = 0 := by
    by_contra h1
    exact hneg ⟨c 0 / c 1, by field_simp; linear_combination (-1 : F) * hQ⟩
  have h0 : c 0 = 0 := by
    rw [h1] at hQ
    simpa using hQ
  have : c = 0 := funext fun k => by fin_cases k <;> simp [h0, h1]
  rw [this, map_zero]

end Overlap

section FramePair

variable {K K' V : Type} [Field K] [Finite K] [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime]
  [CharP K' p] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem unitaryPair_of_frames (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (fr₁ fr₂ : Frame Q)
    (hc : fr₁.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₁.La (-1))
    (hdim : Module.finrank K ↥(negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1))) = 2)
    (hs : ¬ HasSingularVector Q (negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1)))) :
    UnitaryBlockStandardPair K' p f (fr₁.La.range ⊔ fr₂.La.range) fr₁.La.range fr₂.La.range := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have h₁ : IsFundamental Q fr₁.La.range (fr₁.La (-1)) := ⟨fr₁, rfl, rfl⟩
  have h₂ : IsFundamental Q fr₂.La.range (fr₂.La (-1)) := ⟨fr₂, rfl, rfl⟩
  have hN : fr₂.La (-1) ∈ Subgroup.normalizer (fr₁.La.range : Set (V ≃ₗ[K] V)) :=
    (mem_normalizer_iff_even hodd h₁ h₂ hc).mpr (by rw [hdim]; exact even_two)
  have hC : fr₂.La (-1) ∉ Subgroup.centralizer (fr₁.La.range : Set (V ≃ₗ[K] V)) := by
    intro hcent
    have hcent' : ∀ A : SL(2, K), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := fun A =>
      ((Subgroup.mem_centralizer_iff.mp hcent) _ ⟨A, rfl⟩).symm
    rcases Frame.orth_or_eq h2 hc.symm hcent' with horth | heq
    · obtain ⟨v, hv, hv0⟩ : ∃ v ∈ negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1)), v ≠ 0 := by
        have : (negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1))) ≠ ⊥ := by
          rw [← Submodule.one_le_finrank_iff, hdim]
          norm_num
        exact Submodule.exists_mem_ne_zero_of_ne_bot this
      refine hs ⟨v, hv, hv0, ?_⟩
      rw [Submodule.mem_inf, negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hv
      obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hv
      have hp : polar Q v v = 0 := by
        have := horth X Y
        rw [hX, hY] at this
        exact this
      have h' : (2 : K) * Q v = 0 := by
        rw [QuadraticMap.polar_self, nsmul_eq_mul] at hp
        simpa using hp
      exact (mul_eq_zero.mp h').resolve_left h2
    · rw [heq, inf_idem, negSpace_La_neg_one h2, Frame.finrank_span] at hdim
      omega
  exact lemma_6_10_unitary hK hK' hodd h₁ h₂ hc hN hC hs

end FramePair

theorem hub_unitaryPair {F K' : Type} [Field F] [Finite F] [Field K'] [Finite K'] {p f : ℕ}
    [Fact p.Prime] [CharP K' p] (hK : Nat.card F = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card F)) (hneg : ¬ IsSquare (-1 : F)) (hn : 3 ≤ 4) (a b w : F)
    (hab : a * a + b * b = -1) (hw : 4 * w = 1) {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    UnitaryBlockStandardPair K' p f
      ((hubFrame a b w hab hw).La.range ⊔ ((plusFrame 4 F hn).toFrame hij s t).La.range)
      (hubFrame a b w hab hw).La.range ((plusFrame 4 F hn).toFrame hij s t).La.range :=
  unitaryPair_of_frames hK hK' hodd _ _ (hub_comm hn a b w hab hw hij s t)
    (finrank_inf_negSpace_hub (IsFundamental.two_ne_zero_of_odd hodd) hn a b w hab hw hij s t)
    (not_hasSingularVector_hub (IsFundamental.two_ne_zero_of_odd hodd) hneg hn a b w hab hw
      hij s t)

end CFSG.ClassicalInvolution.Asc77.Hub
