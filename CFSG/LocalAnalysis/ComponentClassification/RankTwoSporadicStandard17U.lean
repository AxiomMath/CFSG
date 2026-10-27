module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicUWitness
public import CFSG.Monster.Schur.Defs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G W U : Type*} [Group G] [Group W] [Group U]

section Multiplier

theorem exists_surjective_zmod_two {H : Type*} [Group H] [Finite H]
    (hcomm : ∀ a b : H, a * b = b * a) (heven : Even (Nat.card H)) :
    ∃ f : H →* Multiplicative (ZMod 2), Function.Surjective f := by
  classical
  let _ : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  obtain ⟨ι, _, n, -, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite H
  have hcard : Nat.card H = ∏ i, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => by
      rw [show Nat.card (Multiplicative (ZMod (n i))) = Nat.card (ZMod (n i)) from rfl,
        Nat.card_zmod]
  rw [hcard] at heven
  obtain ⟨i, -, hi⟩ := Nat.prime_two.prime.exists_mem_finset_dvd (even_iff_two_dvd.mp heven)
  let g : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod 2) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hi (ZMod 2)).toAddMonoidHom
  refine ⟨(g.comp (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i)).comp
    e.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hi (Multiplicative.toAdd y)
  refine ⟨e.symm (Pi.mulSingle i (Multiplicative.ofAdd x)), ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
  change Multiplicative.ofAdd ((ZMod.castHom hi (ZMod 2)) x) = y
  rw [hx]
  rfl

theorem oddMultiplier_of_noPerfectDoubleCover {X₀ : Type*} [Group X₀]
    (h : CFSG.Monster.Schur.NoPerfectDoubleCover X₀) : OddMultiplier X₀ := by
  intro A _ _ hA ⟨e⟩
  by_contra hodd
  have heven : Even (Nat.card (center A)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨f, hf⟩ := exists_surjective_zmod_two (H := ↥(center A))
    (fun a b => Subtype.ext (mem_center_iff.mp b.2 a)) heven
  let Z₀ : Subgroup A := f.ker.map (center A).subtype
  have hZ₀ : Z₀ ≤ center A := map_subtype_le _
  have : Z₀.Normal := normal_of_le_center hZ₀
  have hle : Z₀ ≤ (center A).comap (MonoidHom.id A) := hZ₀
  let q : A ⧸ Z₀ →* A ⧸ center A := QuotientGroup.map Z₀ (center A) (MonoidHom.id A) hle
  let π : A ⧸ Z₀ →* X₀ := e.toMonoidHom.comp q
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center A) y
    exact ⟨QuotientGroup.mk' Z₀ x, rfl⟩
  have hπ : Function.Surjective π := e.surjective.comp hq
  have : Group.IsPerfect A := Group.isPerfect_def.mpr hA
  have hperf : Group.IsPerfect (A ⧸ Z₀) := inferInstance
  have hker : π.ker = q.ker := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hqker : q.ker = ((QuotientGroup.mk' Z₀).comp (center A).subtype).range := by
    rw [QuotientGroup.ker_map, MonoidHom.range_comp, range_subtype, comap_id]
  have hcomp_ker : ((QuotientGroup.mk' Z₀).comp (center A).subtype).ker = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hcard : Nat.card π.ker = 2 := by
    rw [hker, hqker, ← index_ker, hcomp_ker, index_ker, MonoidHom.range_eq_top.mpr hf,
      card_top]
    exact Nat.card_zmod 2
  exact h (A ⧸ Z₀) π hπ hperf hcard

theorem card_inf_centralizer_eq_card_center (A : Subgroup G) :
    Nat.card ↥(A ⊓ centralizer (A : Set G)) = Nat.card (center ↥A) := by
  have hmap : (center ↥A).map A.subtype = A ⊓ centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, mem_centralizer_iff.mpr fun z hz => ?_⟩
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)
    · rintro ⟨hxA, hxC⟩
      refine ⟨⟨x, hxA⟩, mem_center_iff.mpr fun z => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.mp hxC z z.2
  rw [← hmap, card_map_of_injective A.subtype_injective]

end Multiplier

section Transport

variable (ι : W →* U) (hι : Function.Injective ι)
include hι

theorem map_centralizer_eq (E : Subgroup W) :
    (centralizer (E : Set W)).map ι = ι.range ⊓ centralizer ((E.map ι : Subgroup U) : Set U) := by
  ext y
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, hx e he]
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, fun e he => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hx (ι e) ⟨e, he, rfl⟩

theorem map_inf_centralizer_eq (X E : Subgroup W) :
    (X ⊓ centralizer (E : Set W)).map ι =
      X.map ι ⊓ centralizer ((E.map ι : Subgroup U) : Set U) := by
  rw [map_inf_eq _ _ _ hι, map_centralizer_eq ι hι, ← inf_assoc,
    inf_eq_left.mpr (map_le_range ι X)]

theorem uWitness_map_iff (X E : Subgroup W) :
    UWitness (X.map ι) (E.map ι) ↔ UWitness X E := by
  have hD : (⁅X ⊓ centralizer (E : Set W), X ⊓ centralizer (E : Set W)⁆).map ι =
      ⁅X.map ι ⊓ centralizer ((E.map ι : Subgroup U) : Set U),
        X.map ι ⊓ centralizer ((E.map ι : Subgroup U) : Set U)⁆ := by
    rw [map_commutator, map_inf_centralizer_eq ι hι]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hs1, ⟨_, ⟨t, ht, rfl⟩, ht1, _, ⟨c, hc, rfl⟩, hct, hc2, _,
      ⟨v, hv, rfl⟩, hvc⟩, P', hP'le, hP'perf, hsP'⟩
    have hle : P' ≤ ι.range := hP'le.trans (by rw [← hD]; exact map_le_range ι _)
    set P := P'.comap ι
    have hPmap : P.map ι = P' := map_comap_eq_self hle
    refine ⟨s, hs, fun h => hs1 (by rw [h, map_one]), ⟨t, ht, fun h => ht1 (by rw [h, map_one]),
      c, hc, hι (by rw [map_mul, map_mul, hct]), ?_, v, hv,
      hι (by rw [map_commutatorElement, hvc])⟩, P, ?_, ?_, hsP'⟩
    · have := hc2.comap_of_injective ι hι
      rwa [← MonoidHom.map_zpowers, comap_map_eq_self_of_injective hι] at this
    · rw [← map_le_map_iff_of_injective hι, hPmap, hD]
      exact hP'le
    · apply map_injective hι
      rw [map_commutator, hPmap, hP'perf]
  · rintro ⟨s, hs, hs1, ⟨t, ht, ht1, c, hc, hct, hc2, v, hv, hvc⟩, P, hPle, hPperf, hsP⟩
    refine ⟨ι s, ⟨s, hs, rfl⟩, fun h => hs1 (hι (h.trans (map_one ι).symm)),
      ⟨ι t, ⟨t, ht, rfl⟩, fun h => ht1 (hι (h.trans (map_one ι).symm)), ι c, ⟨c, hc, rfl⟩,
        by rw [← map_mul, ← map_mul, hct], ?_, ι v, ⟨v, hv, rfl⟩,
        by rw [← map_commutatorElement, hvc]⟩, P.map ι, ?_, ?_, ⟨s, hsP, rfl⟩⟩
    · rw [← MonoidHom.map_zpowers]
      exact hc2.map ι
    · rw [← hD]
      exact map_mono hPle
    · rw [← map_commutator, hPperf]

end Transport

theorem yCensus17U_of_le_sylow [Finite W] {X S : Subgroup W} (hX : X.Normal)
    (hS : IsSylowOf 2 S ⊤) {Exc : Subgroup W → Prop}
    (hExc : ∀ (E : Subgroup W) (w : W), Exc (E.map (MulAut.conj w).toMonoidHom) → Exc E)
    (h : ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E → ¬ Exc E →
      YWitness X E ∨ PWitness X E ∨ UWitness X E) :
    YCensus17U X Exc := by
  intro E hE hE4 hExcE
  obtain ⟨m, -, hm⟩ := exists_conj_le_of_isSylowOf hS (isPGroup_of_isElemAbelian hE) le_top
  set σ := MulAut.conj m⁻¹
  have hle : E.map σ.toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [σ, MulAut.conj_apply] using hm x hx
  have hw := h _ hle (isElemAbelian_map hE _)
    (by rwa [card_map_of_injective σ.injective])
    (fun hc => hExcE (hExc E m⁻¹ hc))
  rwa [← map_conj_eq_of_normal hX m⁻¹, yWitness_map_iff σ.toMonoidHom σ.injective,
    pWitness_map_iff σ.toMonoidHom σ.injective,
    uWitness_map_iff σ.toMonoidHom σ.injective] at hw

theorem exc_of_yCensus17U (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} (hA : AS76b.Hyp31 A) {X₀ W : Type*} [Group X₀] [Group W]
    [Finite W] {X : Subgroup W} (hW : AutModel X₀ W X) (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X)
    (e : ↥A ⧸ center ↥A ≃* X₀) (hZ : Odd (Nat.card (center ↥A))) :
    ∃ ψ : normalizer (A : Set G) →* W, IsActionHom A X ψ ∧
      ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) ∧
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
        ∀ Exc : Subgroup W → Prop, YCensus17U X Exc →
          Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, g, hg, T, hT1, hT2, hY⟩ := exc_of_yCensus17 h32 h33 hA hW hWX e
  refine ⟨ψ, hψ, g, hg, T, hT1, hT2, fun Exc hc => ?_⟩
  have hYc : YCensus17 X (fun E => Exc E ∨ UWitness X E) := fun E h1 h2 h3 =>
    ((hc E h1 h2 (fun h => h3 (Or.inl h))).imp_right fun h =>
      h.resolve_right fun h' => h3 (Or.inr h'))
  rcases hY _ hYc with hExc | hUW
  · exact hExc
  exfalso
  have hR := h32 G A hA
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.standard.2.2.2.1]
    exact hg
  set A' := rightConjugate A g
  have hCA' : centralizer (A' : Set G) = rightConjugate (centralizer (A : Set G)) g :=
    centralizer_rightConjugate A g
  have hTab : ∀ x ∈ T, x ^ 2 = 1 := by
    intro x hx
    have hxK : g * x * g⁻¹ ∈ centralizer (A : Set G) :=
      (mem_rightConjugate_iff _ g x).mp (hT2.le hx)
    have h2 : IsPGroup 2 (zpowers (g * x * g⁻¹)) := by
      have hx2 : IsPGroup 2 (zpowers x) := hT2.isPGroup.to_le (zpowers_le.mpr hx)
      have := hx2.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    have hsq := sq_eq_one_of_isPGroup_zpowers hR hxK h2
    have hc' : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
    rw [hc'] at hsq
    have := congrArg (fun y => g⁻¹ * y * g) hsq
    simpa [mul_assoc] using this
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (A' : Set G) := by
    intro t ht ht1 c _ hct
    have hcK := mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 (hTab t ht) hct
    rw [mem_normalizer_rightConjugate_iff, hA.standard.2.2.2.1] at hcK
    exact mem_normalizer_rightConjugate_iff.mpr hcK
  let eA : ↥A' ≃* ↥A := rightConjugateEquiv' A g
  have hA'p : commutator ↥A' = ⊤ := by
    have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.standard.1.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective)
  let e' : ↥A' ⧸ center ↥A' ≃* X₀ :=
    (QuotientGroup.congr (center ↥A') (center ↥A) eA (map_center_eq eA)).trans e
  obtain ⟨ψ', hψ'⟩ := exists_isActionHom hW hA'p e'
  have hKK : Odd (Nat.card ↥(centralizer (A : Set G) ⊓ centralizer (A' : Set G))) := by
    rw [hCA']
    exact hK.2 g hgK
  have hZA : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G))) := by
    rwa [card_inf_centralizer_eq_card_center]
  have hZA' : Odd (Nat.card ↥(A' ⊓ centralizer (A' : Set G))) := by
    rw [card_inf_centralizer_eq_card_center,
      ← card_map_of_injective (f := (eA : ↥A' →* ↥A)) eA.injective, map_center_eq eA]
    exact hZ
  have hT2' : IsSylowOf 2 T (centralizer (A' : Set G)) := by
    rw [hCA']
    exact hT2
  exact not_uWitness_map hψ hψ' hWX (hT1.le.trans inf_le_right) hT2' hTab hQ hKK hZA hZA' hUW

theorem sporadicCaseOdd_of_yCensus17U (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {s : TauCeti.SporadicName} (hM : OddMultiplier (Blueprint.NativeSporadic.Carrier s))
    {W : Type*} [Group W] [Finite W] {X : Subgroup W}
    (hW : AutModel (Blueprint.NativeSporadic.Carrier s) W X) (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X)
    (hcII : YCensus X (· ≤ X)) (hc : YCensus17U X (fun _ => False)) : SporadicCaseOdd s := by
  intro G _ _ A hH hodd ⟨e⟩
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus hW hcII hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  have hZ : Odd (Nat.card (center ↥A)) := hM ↥A hH.standard.1.1 ⟨e⟩
  obtain ⟨ψ, -, g, -, T, -, -, hExc⟩ := exc_of_yCensus17U h32 h33 hyp hW hWX e hZ
  exact hExc _ hc

end CFSG.ComponentClassification.RankTwoSporadic
