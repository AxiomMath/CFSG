module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

@[expose] def K37RCoverRankFour (C : Type) [Group C] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : Y →* C), Function.Surjective f →
    f.ker ≤ Subgroup.center Y → 4 ≤ localRank 3 Y

section Commutator

variable {Y : Type*} [Group Y]

private theorem commute_commutator_of_central {x a b : Y} (hu : ⁅x, a⁆ ∈ Subgroup.center Y)
    (hv : ⁅x, b⁆ ∈ Subgroup.center Y) : x * ⁅a, b⁆ = ⁅a, b⁆ * x := by
  have hu' : ∀ g : Y, g * ⁅x, a⁆ = ⁅x, a⁆ * g := fun g => Subgroup.mem_center_iff.1 hu g
  have hv' : ∀ g : Y, g * ⁅x, b⁆ = ⁅x, b⁆ * g := fun g => Subgroup.mem_center_iff.1 hv g
  have hxa : x * a * x⁻¹ = ⁅x, a⁆ * a := by rw [commutatorElement_def]; group
  have hxb : x * b * x⁻¹ = ⁅x, b⁆ * b := by rw [commutatorElement_def]; group
  have hxa' : x * a⁻¹ * x⁻¹ = a⁻¹ * ⁅x, a⁆⁻¹ := by
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group, hxa, mul_inv_rev]
  have hxb' : x * b⁻¹ * x⁻¹ = b⁻¹ * ⁅x, b⁆⁻¹ := by
    rw [show x * b⁻¹ * x⁻¹ = (x * b * x⁻¹)⁻¹ by group, hxb, mul_inv_rev]
  have key : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
    set u := ⁅x, a⁆
    set v := ⁅x, b⁆
    have e1 : x * ⁅a, b⁆ * x⁻¹ =
        (x * a * x⁻¹) * (x * b * x⁻¹) * (x * a⁻¹ * x⁻¹) * (x * b⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e1, hxa, hxb, hxa', hxb']
    have hu2 : ∀ g : Y, u⁻¹ * g = g * u⁻¹ := fun g => by
      have := hu' g
      calc u⁻¹ * g = u⁻¹ * (g * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * g) * u⁻¹ := by rw [this]
        _ = g * u⁻¹ := by group
    have hv2 : ∀ g : Y, v⁻¹ * g = g * v⁻¹ := fun g => by
      have := hv' g
      calc v⁻¹ * g = v⁻¹ * (g * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * g) * v⁻¹ := by rw [this]
        _ = g * v⁻¹ := by group
    rw [commutatorElement_def]
    calc u * a * (v * b) * (a⁻¹ * u⁻¹) * (b⁻¹ * v⁻¹)
        = u * (a * v * b * a⁻¹) * u⁻¹ * (b⁻¹ * v⁻¹) := by group
      _ = (a * v * b * a⁻¹) * u * u⁻¹ * (b⁻¹ * v⁻¹) := by rw [← hu']
      _ = a * (v * (b * a⁻¹ * b⁻¹)) * v⁻¹ := by group
      _ = a * ((b * a⁻¹ * b⁻¹) * v) * v⁻¹ := by rw [← hv']
      _ = a * b * a⁻¹ * b⁻¹ := by group
  calc x * ⁅a, b⁆ = x * ⁅a, b⁆ * x⁻¹ * x := by group
    _ = ⁅a, b⁆ * x := by rw [key]

theorem k37R_commute_of_mem_commutator {H : Subgroup Y} {x : Y}
    (hx : ∀ w ∈ H, ⁅x, w⁆ ∈ Subgroup.center Y) {y : Y} (hy : y ∈ ⁅H, H⁆) :
    x * y = y * x := by
  have hle : ⁅H, H⁆ ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact commute_commutator_of_central (hx a ha) (hx b hb)
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x (Set.mem_singleton x)

end Commutator

section Cover

variable {Y S C : Type} [Group Y] [Group S] [Group C]

@[expose] def k37R_derivedPreimage (ψ : Y →* S) (M : Subgroup S) : Subgroup Y :=
  ⁅M.comap ψ, M.comap ψ⁆

theorem k37R_derivedPreimage_le (ψ : Y →* S) (M : Subgroup S) :
    k37R_derivedPreimage ψ M ≤ M.comap ψ := by
  rw [k37R_derivedPreimage, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact (M.comap ψ).mul_mem ((M.comap ψ).mul_mem ((M.comap ψ).mul_mem ha hb)
    ((M.comap ψ).inv_mem ha)) ((M.comap ψ).inv_mem hb)

@[expose] noncomputable def k37R_coverHom (ψ : Y →* S) {M : Subgroup S} (φ₀ : M →* C) :
    ↥(k37R_derivedPreimage ψ M) →* C :=
  φ₀.comp ((ψ.comp (k37R_derivedPreimage ψ M).subtype).codRestrict M
    (fun y => k37R_derivedPreimage_le ψ M y.2))

theorem k37R_coverHom_apply (ψ : Y →* S) {M : Subgroup S} (φ₀ : M →* C)
    (y : ↥(k37R_derivedPreimage ψ M)) :
    k37R_coverHom ψ φ₀ y = φ₀ ⟨ψ y, k37R_derivedPreimage_le ψ M y.2⟩ := rfl

theorem k37R_coverHom_surjective {ψ : Y →* S} (hψ : Function.Surjective ψ)
    (hperf : commutator C = ⊤) {M : Subgroup S} {φ₀ : M →* C} (hφ₀ : Function.Surjective φ₀) :
    Function.Surjective (k37R_coverHom ψ φ₀) := by
  intro c
  have hc : c ∈ (commutator M).map φ₀ := by
    rw [map_commutator_eq ↥M φ₀, MonoidHom.range_eq_top.2 hφ₀, ← _root_.commutator_def, hperf]
    exact Subgroup.mem_top c
  obtain ⟨m, hm, rfl⟩ := hc
  have hmS : (m : S) ∈ (k37R_derivedPreimage ψ M).map ψ := by
    rw [k37R_derivedPreimage, Subgroup.map_commutator,
      Subgroup.map_comap_eq_self_of_surjective hψ M, ← Subgroup.map_subtype_commutator M]
    exact ⟨m, hm, rfl⟩
  obtain ⟨y, hy, hym⟩ := hmS
  exact ⟨⟨y, hy⟩, by rw [k37R_coverHom_apply]; congr 1; exact Subtype.ext hym⟩

theorem k37R_coverHom_ker_le_center {ψ : Y →* S} (hker : ψ.ker ≤ Subgroup.center Y)
    {M : Subgroup S} {φ₀ : M →* C} (hk : φ₀.ker ≤ Subgroup.center M) :
    (k37R_coverHom ψ φ₀).ker ≤ Subgroup.center ↥(k37R_derivedPreimage ψ M) := by
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro z
  have hψy : (⟨ψ y, k37R_derivedPreimage_le ψ M y.2⟩ : M) ∈ Subgroup.center M := hk hy
  have hx : ∀ w ∈ M.comap ψ, ⁅(y : Y), w⁆ ∈ Subgroup.center Y := by
    intro w hw
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have := Subgroup.mem_center_iff.1 hψy ⟨ψ w, hw⟩
    exact (congrArg Subtype.val this).symm
  exact Subtype.ext (k37R_commute_of_mem_commutator hx z.2).symm

theorem K37RCoverRankFour.of_section {C S : Type} [Group C] [Group S] (hC : K37RCoverRankFour C)
    (hperf : commutator C = ⊤) {M : Subgroup S} (φ₀ : M →* C) (hφ₀ : Function.Surjective φ₀)
    (hk : φ₀.ker ≤ Subgroup.center M) : K37RCoverRankFour S := by
  intro Y _ _ ψ hψ hker
  have h4 := hC ↥(k37R_derivedPreimage ψ M) (k37R_coverHom ψ φ₀)
    (k37R_coverHom_surjective hψ hperf hφ₀) (k37R_coverHom_ker_le_center hker hk)
  exact h4.trans (CFSG.RankThree.PartOne.OddCore37.localRank_subgroup_le Nat.prime_three _)

theorem K37RCoverRankFour.of_centralizer {C S : Type} [Group C] [Group S]
    (hcov : ∀ (Y : Type) [Group Y] [Finite Y] (f : Y →* C), Function.Surjective f →
      f.ker ≤ Subgroup.center Y → ∃ V : Subgroup Y, IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 4)
    (hperf : commutator C = ⊤) {a : S} (ha : orderOf a = 2) {M : Subgroup S}
    (hMa : ∀ m ∈ M, m * a = a * m) (φ₀ : M →* C) (hφ₀ : Function.Surjective φ₀)
    (hk : φ₀.ker ≤ Subgroup.center M) : K37RCoverRankFour S := by
  intro Y _ _ ψ hψ hker
  obtain ⟨V, hV, hVc⟩ := hcov ↥(k37R_derivedPreimage ψ M) (k37R_coverHom ψ φ₀)
    (k37R_coverHom_surjective hψ hperf hφ₀) (k37R_coverHom_ker_le_center hker hk)
  obtain ⟨x, hx⟩ := hψ a
  have hxC : ∀ y ∈ k37R_derivedPreimage ψ M, x * y = y * x := by
    intro y hy
    refine k37R_commute_of_mem_commutator (H := M.comap ψ) ?_ hy
    intro w hw
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, hx, commutatorElement_eq_one_iff_mul_comm]
    exact (hMa _ hw).symm
  have hdvd : 2 ∣ orderOf x := by
    rw [← ha, ← hx]
    exact orderOf_map_dvd ψ x
  have hu : orderOf (x ^ (orderOf x / 2)) = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd
  have hV' : IsElemAbelian 3 (V.map (k37R_derivedPreimage ψ M).subtype) :=
    CFSG.SectionRank.isElemAbelian_map hV _
  have hVc' : Nat.card (V.map (k37R_derivedPreimage ψ M).subtype) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective (k37R_derivedPreimage ψ M).subtype_injective, hVc]
  refine CFSG.RankThree.PartTwo.Census.le_localRank_of_commute_involution Nat.prime_three hu hV'
    hVc' ?_
  rintro _ ⟨v, -, rfl⟩
  exact (Commute.pow_right (show Commute (v : Y) x from (hxC v v.2).symm) _).eq

theorem K37RCoverRankFour.of_mulEquiv {C C' : Type} [Group C] [Group C']
    (h : K37RCoverRankFour C) (e : C' ≃* C) : K37RCoverRankFour C' := by
  intro Y _ _ f hf hker
  refine h Y (e.toMonoidHom.comp f) (e.surjective.comp hf) ?_
  intro y hy
  apply hker
  rw [MonoidHom.mem_ker] at hy ⊢
  exact e.injective (by simpa using hy)

theorem K37RCoverRankFour.four_le_localRank {S : Type} [Group S] (h : K37RCoverRankFour S)
    {K : Type} [Group K] [Finite K] (e : K ⧸ Subgroup.center K ≃* S) : 4 ≤ localRank 3 K := by
  refine h K (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  simpa [QuotientGroup.eq_one_iff] using hx

theorem k37R_commutator_eq_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab h1
  · exact h

theorem k37R_exists_hom_of_quotCenter {M C : Type} [Group M] [Group C]
    (e : M ⧸ Subgroup.center M ≃* C) :
    ∃ φ₀ : M →* C, Function.Surjective φ₀ ∧ φ₀.ker ≤ Subgroup.center M := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center M)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  simpa [QuotientGroup.eq_one_iff] using hx

theorem K37RCoverRankFour.of_section_quotCenter {C S : Type} [Group C] [Group S]
    (hC : K37RCoverRankFour C) (hperf : commutator C = ⊤) {M : Subgroup S}
    (e : ↥M ⧸ Subgroup.center ↥M ≃* C) : K37RCoverRankFour S := by
  obtain ⟨φ₀, hφ₀, hk⟩ := k37R_exists_hom_of_quotCenter e
  exact hC.of_section hperf φ₀ hφ₀ hk

theorem K37RCoverRankFour.of_centralizer_quotCenter {C S : Type} [Group C] [Group S]
    (hcov : ∀ (Y : Type) [Group Y] [Finite Y] (f : Y →* C), Function.Surjective f →
      f.ker ≤ Subgroup.center Y → ∃ V : Subgroup Y, IsElemAbelian 3 V ∧ Nat.card V = 3 ^ 4)
    (hperf : commutator C = ⊤) {a : S} (ha : orderOf a = 2) {M : Subgroup S}
    (hMa : ∀ m ∈ M, m * a = a * m) (e : ↥M ⧸ Subgroup.center ↥M ≃* C) : K37RCoverRankFour S := by
  obtain ⟨φ₀, hφ₀, hk⟩ := k37R_exists_hom_of_quotCenter e
  exact K37RCoverRankFour.of_centralizer hcov hperf ha hMa φ₀ hφ₀ hk

theorem k37R_commutator_eq_top_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : commutator B = ⊤) : commutator A = ⊤ := by
  have h1 : (commutator A).map e.toMonoidHom = commutator B := by
    rw [map_commutator_eq A e.toMonoidHom, MonoidHom.range_eq_top.2 e.surjective,
      ← _root_.commutator_def]
  rw [h] at h1
  rw [eq_top_iff]
  intro a _
  have h2 : e a ∈ (commutator A).map e.toMonoidHom := by rw [h1]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxa⟩ := h2
  have h3 : x = a := e.injective hxa
  rwa [h3] at hx

end Cover

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
