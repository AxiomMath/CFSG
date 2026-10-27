module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryCentralizers
public import CFSG.CharacterTheory.Wreathed.SameFieldLinearRecognition

public section

open scoped Classical
open Polynomial

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_quadratic_extension {F : Type} [Field F] [Fintype F] {b : Fˣ}
    (hb : ¬ IsSquare b) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Module.Basis (Fin 2) F E) (y : Eˣ),
      (y : E) * (y : E) ^ Nat.card F = -1 := by
  set P : F[X] := X ^ 2 - C (b : F) with hP
  have hdeg : P.natDegree = 2 := natDegree_X_pow_sub_C
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hroots : ∀ r : F, P.eval r ≠ 0 := by
    intro r hr
    apply hb
    have : r ^ 2 = (b : F) := by
      simp only [hP, eval_sub, eval_pow, eval_X, eval_C] at hr
      exact sub_eq_zero.mp hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact b.ne_zero (by rw [← this]; ring)
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [← this, sq])⟩
  have hirr : Irreducible P := by
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · rw [Multiset.eq_zero_iff_forall_notMem]
      intro r hr
      exact hroots r ((mem_roots hP0).mp hr)
    · rw [hdeg]
    · rw [hdeg]; norm_num
  have : Fact (Irreducible P) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hP0
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis_dim, hdeg]
  let basis : Module.Basis (Fin 2) F (AdjoinRoot P) := pb.basis.reindex (finCongr hdim)
  obtain ⟨y, hy⟩ := CFSG.Wreathed.CentralSL2.exists_norm_eq F (AdjoinRoot P) basis (-1)
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, basis, y, ?_⟩
  rw [hy]
  simp

section NonsplitModel

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem exists_nonsplit_conj_of_involution {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : Nat.card F % 4 = 3) (hb : ¬ IsSquare b)
    {n : ℕ} (hmn : m = 2 ^ n) (E : Type) [Field E] [Algebra F E]
    (basis : Module.Basis (Fin 2) F E) (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1)
    {i : CentralExtension F b m hm heven} (hi2 : i ^ 2 = 1)
    (hiA : i ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    ∃ t ∈ nonsplitTorus F b m hm heven E basis,
      t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ∧ IsConj i t ∧
      Subgroup.centralizer {t} = nonsplitTorus F b m hm heven E basis := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htypes, -, -, -, -, -, -, hAU, hcomm,
      -, -, -, -, -, hTminus, -⟩ :=
    base_conjugacy_classes_and_centralizers hp hpodd hf hF b hb m hm heven E basis y hy
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  rcases htypes i with hA | ⟨α, hα, hconj⟩ | ⟨t, ht, htA, hconj⟩ | ⟨t, ht, htA, hconj⟩
  · exact absurd hA hiA
  ·
    exfalso
    have h1 : (α * unipotentElement F b m hm heven 1) ^ 2 = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc, conj_pow, hi2, mul_one, mul_inv_cancel]
    have hsq : (α * unipotentElement F b m hm heven 1) ^ 2 =
        α ^ 2 * unipotentElement F b m hm heven 2 := by
      have hαU := hcomm α hα 1
      calc (α * unipotentElement F b m hm heven 1) ^ 2 =
            α * (unipotentElement F b m hm heven 1 * α) * unipotentElement F b m hm heven 1 := by
            rw [pow_two]
            group
        _ = α * (α * unipotentElement F b m hm heven 1) * unipotentElement F b m hm heven 1 := by
            rw [← hαU]
        _ = α ^ 2 * (unipotentElement F b m hm heven 1 * unipotentElement F b m hm heven 1) := by
            rw [pow_two]
            group
        _ = α ^ 2 * unipotentElement F b m hm heven 2 := by
            rw [← unipotentElement_add]
            norm_num
    rw [hsq] at h1
    have hU2 : unipotentElement F b m hm heven 2 ∈
        Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ⊓
          unipotentSubgroup F b m hm heven := by
      refine ⟨?_, (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨2, rfl⟩⟩
      have : unipotentElement F b m hm heven 2 = (α ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hα 2)
    rw [hAU, Subgroup.mem_bot, ← unipotentElement_zero F b m hm heven] at hU2
    exact h2 (unipotentElement_injective hU2)
  ·
    exfalso
    have hT : t ∈ splitTorus F b m hm heven := by rw [splitTorus_eq_comap]; exact ht
    have hcyc := splitTorus_isCyclic (hm := hm) (heven := heven) hq hb hmn
    have ht2 : t ^ 2 = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc, conj_pow, hi2, mul_one, mul_inv_cancel]
    have hx2 : (cyclicGenerator F b m hm heven ^ m) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm m 2]
      exact cyclicGenerator_pow_two_m F b m hm heven
    obtain ⟨k, hk⟩ := id heven
    have hxk : cyclicGenerator F b m hm heven ^ m = (cyclicGenerator F b m hm heven ^ 2) ^ k := by
      rw [← pow_mul]
      congr 1
      omega
    have hxA : cyclicGenerator F b m hm heven ^ m ∈
        Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
      rw [hxk]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    have hxT : cyclicGenerator F b m hm heven ^ m ∈ splitTorus F b m hm heven := by
      rw [hxk]
      exact Subgroup.pow_mem _ (cyclicGenerator_sq_mem_splitTorus F b m hm _) _
    have hx1 : cyclicGenerator F b m hm heven ^ m ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (by omega)
      rw [orderOf_cyclicGenerator F b m hm _ h2]
      omega
    have ht1 : t ≠ 1 := fun h => htA (h ▸ Subgroup.one_mem _)
    have heq : (⟨t, hT⟩ : splitTorus F b m hm heven) = ⟨_, hxT⟩ :=
      CFSG.Semidihedral.UnitaryBranch.eq_of_sq_eq_one_of_isCyclic
        (Subtype.ext (by simpa using ht2)) (fun h => ht1 (congrArg Subtype.val h))
        (Subtype.ext (by simpa using hx2)) (fun h => hx1 (congrArg Subtype.val h))
    apply htA
    rw [show t = cyclicGenerator F b m hm _ ^ m from congrArg Subtype.val heq]
    exact hxA
  · exact ⟨t, ht, htA, hconj, (hTminus t ht htA).2.2.1⟩

theorem centralizer_eq_nonsplitTorus {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hb : ¬ IsSquare b) (E : Type) [Field E] [Algebra F E]
    (basis : Module.Basis (Fin 2) F E) (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1)
    {t : CentralExtension F b m hm heven} (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Subgroup.centralizer {t} = nonsplitTorus F b m hm heven E basis := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, hTminus, -⟩ :=
    base_conjugacy_classes_and_centralizers hp hpodd hf hF b hb m hm heven E basis y hy
  exact (hTminus t ht htA).2.2.1

variable (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)

theorem pow_m_mem_nonsplitDiag_range (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
    {g : CentralExtension F b m hm heven} (hg : g ∈ nonsplitTorus F b m hm heven E basis) :
    g ^ m ∈ (nonsplitDiag F b m hm heven E basis).range := by
  obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
  have hcomm : Commute (nonsplitDiag F b m hm heven E basis t)
      (nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ)) :=
    (Commute.pow_left (nonsplitGenerator_mul_nonsplitDiag z hz t) k).symm
  rw [hcomm.mul_pow, ← pow_mul, Nat.mul_comm (k : ℕ) m, pow_mul, nonsplitGenerator_pow_m z hz h2,
    ← map_pow, ← map_pow, ← map_mul]
  exact ⟨_, rfl⟩

theorem mem_nonsplitDiag_range_of_odd (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) {n : ℕ} (hmn : m = 2 ^ n)
    {g : CentralExtension F b m hm heven} (hg : g ∈ nonsplitTorus F b m hm heven E basis)
    (hodd : Odd (orderOf g)) : g ∈ (nonsplitDiag F b m hm heven E basis).range := by
  have hcop : Nat.Coprime m (orderOf g) := by
    have h' := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    rwa [← hmn] at h'
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hs]
  exact Subgroup.pow_mem _ (pow_m_mem_nonsplitDiag_range E basis h2 z hz hg) s

theorem mem_zpowers_of_odd (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) {n : ℕ} (hmn : m = 2 ^ n)
    (hmq : m ∣ Nat.card F + 1) {γ : normOne F E}
    (hγ : ∀ τ : normOne F E, τ ∈ Subgroup.zpowers γ)
    {g : CentralExtension F b m hm heven} (hg : g ∈ nonsplitTorus F b m hm heven E basis)
    (hgodd : Odd (orderOf g)) :
    g ∈ Subgroup.zpowers (nonsplitDiag F b m hm heven E basis (γ ^ m)) := by
  have : Finite E := finite_of_basis F E basis
  obtain ⟨τ, rfl⟩ := mem_nonsplitDiag_range_of_odd E basis h2 z hz hmn hg hgodd
  have hτodd : Odd (orderOf τ) := by
    rwa [orderOf_injective _ nonsplitDiag_injective] at hgodd
  have hγord : orderOf γ = Nat.card F + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, card_normOne F E basis]
  have hcard : Nat.card (Subgroup.zpowers (γ ^ m)) = (Nat.card F + 1) / m := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hm.ne' (hγord ▸ hmq), hγord]
  have hτdvd : orderOf τ ∣ (Nat.card F + 1) / m := by
    have h1 : orderOf τ ∣ Nat.card F + 1 := by
      rw [← card_normOne F E basis]
      exact orderOf_dvd_natCard τ
    obtain ⟨c, hc⟩ := hmq
    have hc' : (Nat.card F + 1) / m = c := by
      rw [hc, Nat.mul_div_cancel_left c hm]
    rw [hc']
    rw [hc] at h1
    have hcop : Nat.Coprime (orderOf τ) m := by
      rw [hmn]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hτodd)
    exact hcop.dvd_of_dvd_mul_left h1
  have hτ : τ ∈ Subgroup.zpowers (γ ^ m) :=
    CFSG.Semidihedral.UnitaryBranch.mem_of_orderOf_dvd_of_isCyclic _ (hcard ▸ hτdvd)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  exact ⟨j, by rw [map_zpow]⟩

end NonsplitModel

theorem eq_one_of_sq_eq_one_of_odd {X : Type*} [Group X] [Finite X] (hX : Odd (Nat.card X))
    {g : X} (hg : g ^ 2 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  have h2 : Odd (orderOf g) := hX.of_dvd_nat (orderOf_dvd_natCard g)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd h2 (by decide)

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField

open CFSG.Wreathed.PrimewiseConfinedCentralCore in
theorem four_group_centralizer_data
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e) :
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let z : G := wreathModelHom S e (Original.x2 (2 ^ n))
    let y : G := wreathModelHom S e (Original.z (2 ^ n))
    let A : Subgroup G := (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype
    let C : Subgroup G := Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z}
    (∀ a ∈ C, ∀ c ∈ C, a * c = c * a) ∧
    Nat.card C = 2 ^ n * Nat.card A * (p ^ f + 1) ∧
    ∃ W : Subgroup G, W ≤ C ∧ IsCyclic W ∧ 2 ^ n * Nat.card W = p ^ f + 1 ∧ W ⊓ A = ⊥ ∧
      (∀ w ∈ W, y * w * y⁻¹ = w⁻¹) ∧
      ∀ w ∈ W, w ≠ 1 →
        Subgroup.centralizer {x} ⊓ Subgroup.centralizer {w} ≤ Subgroup.centralizer {z} := by
  intro x z y A C
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  obtain ⟨hRq, F, hF, hFfin, b, hFcard, hb, Φ, hΦinj, hΦN, hNΦ, hΦR⟩ :=
    exists_centralizer_model hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  let _ : Fintype F := Fintype.ofFinite F
  have h2F : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  have hF3 : Nat.card F % 4 = 3 := by rw [hFcard]; exact hq3
  obtain ⟨E, hE, hEalg, basis, yE, hyE⟩ := exists_quadratic_extension hb
  obtain ⟨zE, hzE⟩ := exists_norm_eq F E basis b
  have hRodd : Odd (Nat.card (centralizerOddCore n S e)) := centralizerOddCore_card_odd n S e
  have hRcomm : ∀ a b : centralizerOddCore n S e, a * b = b * a := by
    have := (original_primewise_coverage_and_confinement_give_central_cyclic_odd_core hnonab n hn
      S e hfour p f hp hp2 hf hmodel hcov (fun r hr hr1 =>
        ((ComponentCoverConfinement.stationarity_and_original_coverage_confine_all_odd_core_elements
          hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel hrec hst hcov) r hr hr1).1)).2.2.2.2.1
    exact fun a b => IsCyclic.commGroup.mul_comm a b
  have hxN : x ∈ involutionCentralizer n S e := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzS : z ∈ (S : Subgroup G) := BrauerWong.wreathModelHom_mem S e _
  have hzN : z ∈ involutionCentralizer n S e := sylow_le_involutionCentralizer n hn S e hzS
  have hxord : orderOf x = 2 := CompatibleFamilies.orderOf_x S e hn
  have hzord : orderOf z = 2 := CompatibleFamilies.orderOf_x2 S e hn
  have hxz : x ≠ z := BrauerWong.modelHom_x_ne_x2 S e (by omega)
  have hsq : ∀ {g : G}, orderOf g = 2 → g ^ 2 = 1 := fun h => by rw [← h, pow_orderOf_eq_one]
  have hinvol : ∀ ζ : centralizerOddCore n S e × CentralExtension F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn), (Φ ζ) ^ 2 = 1 → ζ.1 = 1 ∧ ζ.2 ^ 2 = 1 := by
    intro ζ hζ
    have h1 : ζ ^ 2 = 1 := hΦinj (by rw [map_pow, hζ, map_one])
    have h2 : ζ.1 ^ 2 = 1 := by simpa using congrArg Prod.fst h1
    exact ⟨eq_one_of_sq_eq_one_of_odd hRodd h2, by simpa using congrArg Prod.snd h1⟩
  obtain ⟨ζ, hζ⟩ := hNΦ z hzN
  obtain ⟨hζ1, hi2⟩ := hinvol ζ (by rw [hζ]; exact hsq hzord)
  obtain ⟨ξ, hξ⟩ := hNΦ x hxN
  obtain ⟨hξ1, hξ2⟩ := hinvol ξ (by rw [hξ]; exact hsq hxord)
  have hξc : ξ.2 ∈ Subgroup.zpowers (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) ^ 2) := by
    rw [← CFSG.Wreathed.CentralSL2.center_eq_zpowers hb, Subgroup.mem_center_iff]
    intro w
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hΦN ((1 : centralizerOddCore n S e), w))
    change Φ (1, w) * x = x * Φ (1, w) at h
    rw [← hξ, ← map_mul, ← map_mul] at h
    have := congrArg Prod.snd (hΦinj h)
    simpa using this
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hξ21 : ξ.2 ≠ 1 := by
    intro h
    apply hx1
    rw [← hξ, show ξ = 1 from Prod.ext hξ1 h, map_one]
  have hiA : ζ.2 ∉ Subgroup.zpowers (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) ^ 2) := by
    intro hi
    apply hxz
    have hζ21 : ζ.2 ≠ 1 := by
      intro h
      apply hz1
      rw [← hζ, show ζ = 1 from Prod.ext hζ1 h, map_one]
    have heq : (⟨ξ.2, hξc⟩ : Subgroup.zpowers (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) ^ 2)) = ⟨ζ.2, hi⟩ :=
      CFSG.Semidihedral.UnitaryBranch.eq_of_sq_eq_one_of_isCyclic
        (Subtype.ext (by simpa using hξ2)) (fun h => hξ21 (congrArg Subtype.val h))
        (Subtype.ext (by simpa using hi2)) (fun h => hζ21 (congrArg Subtype.val h))
    rw [← hξ, ← hζ]
    congr 1
    exact Prod.ext (hξ1.trans hζ1.symm) (congrArg Subtype.val heq)
  obtain ⟨t, htT, htA, hconj, hCt⟩ := exists_nonsplit_conj_of_involution hp hpodd hf hFcard hF3
    hb rfl E basis yE hyE hi2 hiA
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  set Ψ := Φ.comp ((MonoidHom.id (centralizerOddCore n S e)).prodMap
    (MulAut.conj c⁻¹).toMonoidHom) with hΨ
  have hΨapp : ∀ r w, Ψ (r, w) = Φ (r, c⁻¹ * w * c) := by
    intro r w
    simp [hΨ]
  have hΨinj : Function.Injective Ψ := by
    intro a a' h
    rw [show a = (a.1, a.2) from rfl, show a' = (a'.1, a'.2) from rfl, hΨapp, hΨapp] at h
    have h' := hΦinj h
    simp only [Prod.mk.injEq, mul_left_inj, mul_right_inj] at h'
    exact Prod.ext h'.1 h'.2
  have hΨN : ∀ g ∈ involutionCentralizer n S e, ∃ r w, Ψ (r, w) = g := by
    intro g hg
    obtain ⟨ω, rfl⟩ := hNΦ g hg
    exact ⟨ω.1, c * ω.2 * c⁻¹, by rw [hΨapp]; congr; group⟩
  have hΨmem : ∀ r w, Ψ (r, w) ∈ involutionCentralizer n S e := fun r w => by
    rw [hΨapp]; exact hΦN _
  have hΨz : Ψ (1, t) = z := by
    rw [hΨapp, ← hζ, ← hc]
    congr 1
    exact Prod.ext hζ1.symm (by group)
  have hΨx : Ψ (1, ξ.2) = x := by
    rw [hΨapp, ← hξ]
    congr 1
    refine Prod.ext hξ1.symm ?_
    have hcomm := (Subgroup.mem_center_iff.mp
      ((CFSG.Wreathed.CentralSL2.center_eq_zpowers hb).ge hξc) c).symm
    simp only
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  have hΨR : ∀ r, Ψ (r, 1) = ((r : involutionCentralizer n S e) : G) := by
    intro r
    rw [hΨapp, show c⁻¹ * 1 * c = 1 by group, hΦR]
  have hTcomm : ∀ a ∈ nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
      basis, ∀ a' ∈ nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
      basis, a * a' = a' * a := fun a ha a' ha' => nonsplitTorus_mul_comm zE hzE ha ha'
  have hCmem : ∀ g : G, g ∈ C ↔ ∃ r, ∃ w ∈ nonsplitTorus F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) E basis, Ψ (r, w) = g := by
    intro g
    constructor
    · rintro ⟨hgx, hgz⟩
      obtain ⟨r, w, rfl⟩ := hΨN g hgx
      refine ⟨r, w, ?_, rfl⟩
      rw [← hCt]
      change Ψ (r, w) ∈ Subgroup.centralizer {z} at hgz
      rw [Subgroup.mem_centralizer_singleton_iff] at hgz ⊢
      rw [← hΨz, ← map_mul, ← map_mul] at hgz
      have := congrArg Prod.snd (hΨinj hgz)
      simpa using this
    · rintro ⟨r, w, hw, rfl⟩
      refine ⟨hΨmem r w, ?_⟩
      show Ψ (r, w) ∈ Subgroup.centralizer {z}
      rw [Subgroup.mem_centralizer_singleton_iff, ← hΨz, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simpa using hTcomm w hw t htT)
  have hC_comm : ∀ a ∈ C, ∀ c' ∈ C, a * c' = c' * a := by
    intro a ha c' hc'
    obtain ⟨r, w, hw, rfl⟩ := (hCmem a).mp ha
    obtain ⟨r', w', hw', rfl⟩ := (hCmem c').mp hc'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simpa using hRcomm r r') (by simpa using hTcomm w hw w' hw')
  have hCeq : C = ((⊤ : Subgroup (centralizerOddCore n S e)).prod
      (nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E basis)).map Ψ := by
    ext g
    rw [hCmem g]
    constructor
    · rintro ⟨r, w, hw, rfl⟩
      exact ⟨(r, w), ⟨Subgroup.mem_top _, hw⟩, rfl⟩
    · rintro ⟨⟨r, w⟩, ⟨-, hw⟩, rfl⟩
      exact ⟨r, w, hw, rfl⟩
  have hAcard : Nat.card A = Nat.card (centralizerOddCore n S e) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hCcard : Nat.card C = 2 ^ n * Nat.card A * (p ^ f + 1) := by
    rw [hCeq, Subgroup.card_map_of_injective hΨinj, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,
      Nat.card_prod, Subgroup.card_top, card_nonsplitTorus zE hzE, hAcard, hFcard]
    ring
  have htwo := NormalComponentLift.two_pow_eq_two_part (n := n) (hn := hn) (S := S) (e := e)
    hnonab hfour hp hp2 hf hmodel
  have hε : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by simp [hq3]
  rw [hε] at htwo
  have hval : (p ^ f + 2 - 1).factorization 2 = n := by
    have hv : padicValInt 2 ((p ^ f : ℕ) - (-1 : ℤ)) = n :=
      (Nat.pow_right_injective (le_refl 2) htwo).symm
    rw [show ((p ^ f : ℕ) : ℤ) - (-1 : ℤ) = ((p ^ f + 2 - 1 : ℕ) : ℤ) by push_cast; ring,
      padicValInt.of_nat, ← Nat.factorization_def _ Nat.prime_two] at hv
    exact hv
  obtain ⟨k₀, hk₀, hqk₀⟩ :=
    SameFieldLinearRecognition.exists_odd_of_two_part (p ^ f + 2) n (by omega) hval
  have hqk : p ^ f + 1 = 2 ^ n * k₀ := by rw [← hqk₀]; omega
  have h2q : 2 ^ n ∣ p ^ f + 1 := ⟨k₀, hqk⟩
  have hk₀q : (p ^ f + 1) / 2 ^ n = k₀ := by rw [hqk, Nat.mul_div_cancel_left _ (by positivity)]
  have : Finite E := finite_of_basis F E basis
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := normOne F E)
  set hW := nonsplitDiag F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E basis
    (γ ^ 2 ^ n) with hhW
  have hhWT : hW ∈ nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
      basis := nonsplitDiag_mem _
  have hγord : orderOf γ = p ^ f + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, card_normOne F E basis, hFcard]
  have hhWord : orderOf hW = k₀ := by
    rw [hhW, orderOf_injective _ nonsplitDiag_injective, orderOf_pow_of_dvd (by positivity)
      (hγord ▸ h2q), hγord, hk₀q]
  set W : Subgroup G := Subgroup.zpowers (Ψ (1, hW)) with hWdef
  have hWelt : ∀ g ∈ W, ∃ d ∈ Subgroup.zpowers hW, Ψ (1, d) = g := by
    intro g hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨hW ^ j, Subgroup.zpow_mem_zpowers hW j, ?_⟩
    rw [show Ψ (1, hW) ^ j = Ψ ((1, hW) ^ j) from (map_zpow Ψ _ j).symm, Prod.pow_mk, one_zpow]
  have hWC : W ≤ C := by
    rw [hWdef, Subgroup.zpowers_le]
    exact (hCmem _).mpr ⟨1, hW, hhWT, rfl⟩
  have hWcard : 2 ^ n * Nat.card W = p ^ f + 1 := by
    rw [hWdef, Nat.card_zpowers, orderOf_injective Ψ hΨinj, Prod.orderOf, orderOf_one,
      Nat.lcm_one_left, hhWord, hqk]
  have hWA : W ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgW, hgA⟩
    obtain ⟨d, -, rfl⟩ := hWelt g hgW
    obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp hgA
    have hr' : Ψ (⟨r, hrR⟩, 1) = Ψ (1, d) := by
      rw [hΨR]
      exact hr
    have h := hΨinj hr'
    rw [Subgroup.mem_bot, show d = 1 from (congrArg Prod.snd h).symm]
    have : ((1 : centralizerOddCore n S e), (1 : CentralExtension F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn))) = 1 := rfl
    rw [this, map_one]
  have hdodd : ∀ d ∈ Subgroup.zpowers hW, Odd (orderOf d) := by
    intro d hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hdvd : orderOf (hW ^ j) ∣ orderOf hW := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, Int.mul_comm j, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow]
    exact hk₀.of_dvd_nat (hhWord ▸ hdvd)
  have hdT : ∀ d ∈ Subgroup.zpowers hW, d ∈ nonsplitTorus F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) E basis := fun d hd => by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact Subgroup.zpow_mem _ hhWT j
  have hdA : ∀ d ∈ Subgroup.zpowers hW, d ≠ 1 → d ∉ Subgroup.zpowers
      (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ^ 2) := by
    intro d hd hd1 hdA
    have h1 : orderOf d ∣ 2 ^ n := by
      have h := orderOf_dvd_natCard (⟨d, hdA⟩ : Subgroup.zpowers
        (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ^ 2))
      rwa [Subgroup.orderOf_mk, Nat.card_zpowers, orderOf_cyclicGenerator_sq F b _ _ _ h2F] at h
    have h2 := hdodd d hd
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases i with _ | i
    · rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hd1 hi
    · rw [hi, pow_succ] at h2
      exact absurd h2 (Nat.not_odd_iff_even.mpr (even_two.mul_left _))
  have hdC : ∀ d ∈ Subgroup.zpowers hW, d ≠ 1 → Subgroup.centralizer {d} =
      nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E basis :=
    fun d hd hd1 => centralizer_eq_nonsplitTorus hp hpodd hf hFcard hb E basis yE hyE (hdT d hd)
      (hdA d hd hd1)
  have hyS : y ∈ (S : Subgroup G) := BrauerWong.wreathModelHom_mem S e _
  have hyN : y ∈ involutionCentralizer n S e := sylow_le_involutionCentralizer n hn S e hyS
  have hyord : orderOf y = 2 := TorusSplitting.actual_orderOf_swap S e
  obtain ⟨ry, yW, hyΨ⟩ := hΨN y hyN
  have hyinv : (ry, yW) ^ 2 = 1 := hΨinj (by rw [map_pow, hyΨ, hsq hyord, map_one])
  have hry : ry = 1 := eq_one_of_sq_eq_one_of_odd hRodd (by simpa using congrArg Prod.fst hyinv)
  have hyW2 : yW * yW = 1 := by
    have := congrArg Prod.snd hyinv
    simpa [pow_two] using this
  have hyz : y * z * y⁻¹ = x * z := by
    have h1 := BrauerWong.modelHom_swap_conj_x2 S e
    have h2 := BrauerWong.modelHom_x_mul_x2 S e (n := n) (by omega)
    have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hsq hyord])
    change y * z * y⁻¹ = x * z
    rw [h2]
    rw [hyy] at h1 ⊢
    exact h1
  have hyWt : yW * t * yW⁻¹ = ξ.2 * t := by
    have h := hyz
    rw [← hyΨ, ← hΨz, ← hΨx, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hry] at h
    have := congrArg Prod.snd (hΨinj h)
    simpa using this
  have hξcent : ∀ w : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn),
      w * ξ.2 = ξ.2 * w := fun w =>
    (Subgroup.mem_center_iff.mp ((CFSG.Wreathed.CentralSL2.center_eq_zpowers hb).ge hξc) w)
  have hyd : ∀ d ∈ Subgroup.zpowers hW, yW * d * yW⁻¹ = d⁻¹ := by
    intro d hd
    have hd' : yW * d * yW⁻¹ ∈ nonsplitTorus F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) E basis := by
      rw [← hCt, Subgroup.mem_centralizer_singleton_iff]
      have hdt : d * t = t * d := hTcomm d (hdT d hd) t htT
      have key : yW * d * yW⁻¹ * (yW * t * yW⁻¹) = yW * t * yW⁻¹ * (yW * d * yW⁻¹) := by
        calc yW * d * yW⁻¹ * (yW * t * yW⁻¹) = yW * (d * t) * yW⁻¹ := by group
          _ = yW * (t * d) * yW⁻¹ := by rw [hdt]
          _ = yW * t * yW⁻¹ * (yW * d * yW⁻¹) := by group
      rw [hyWt] at key
      have key' : ξ.2 * (yW * d * yW⁻¹ * t) = ξ.2 * (t * (yW * d * yW⁻¹)) := by
        calc ξ.2 * (yW * d * yW⁻¹ * t) = yW * d * yW⁻¹ * (ξ.2 * t) := by
              rw [← mul_assoc, ← hξcent (yW * d * yW⁻¹)]; group
          _ = ξ.2 * t * (yW * d * yW⁻¹) := key
          _ = ξ.2 * (t * (yW * d * yW⁻¹)) := by group
      exact mul_left_cancel key'
    have hd'odd : Odd (orderOf (yW * d * yW⁻¹)) := by
      rw [show yW * d * yW⁻¹ = MulAut.conj yW d by simp, MulEquiv.orderOf_eq]
      exact hdodd d hd
    have hd'W : yW * d * yW⁻¹ ∈ Subgroup.zpowers hW :=
      mem_zpowers_of_odd E basis h2F zE hzE rfl (by rw [hFcard]; exact h2q) hγ hd' hd'odd
    set e' := d * (yW * d * yW⁻¹) with he'
    have he'W : e' ∈ Subgroup.zpowers hW := Subgroup.mul_mem _ hd hd'W
    by_contra hne
    have he'1 : e' ≠ 1 := by
      intro h
      apply hne
      rw [he'] at h
      exact (eq_inv_of_mul_eq_one_right h)
    have hcommW : ∀ a ∈ Subgroup.zpowers hW, ∀ a' ∈ Subgroup.zpowers hW, a * a' = a' * a :=
      fun a ha a' ha' => hTcomm a (hdT a ha) a' (hdT a' ha')
    have hfix : yW * e' * yW⁻¹ = e' := by
      have hyWinv : yW⁻¹ = yW := inv_eq_of_mul_eq_one_right hyW2
      calc yW * e' * yW⁻¹ = (yW * d * yW⁻¹) * (yW * (yW * d * yW⁻¹) * yW⁻¹) := by
            rw [he']; group
        _ = (yW * d * yW⁻¹) * d := by
            congr 1
            rw [hyWinv]
            calc yW * (yW * d * yW) * yW = (yW * yW) * d * (yW * yW) := by group
              _ = d := by rw [hyW2]; group
        _ = e' := by rw [he', hcommW _ hd'W _ hd]
    have hyWe : yW ∈ Subgroup.centralizer {e'} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc yW * e' = yW * e' * yW⁻¹ * yW := by group
        _ = e' * yW := by rw [hfix]
    rw [hdC e' he'W he'1] at hyWe
    have hyt : yW * t * yW⁻¹ = t := by
      rw [hTcomm yW hyWe t htT, mul_inv_cancel_right]
    rw [hyWt] at hyt
    exact hξ21 (by simpa using hyt)
  refine ⟨hC_comm, hCcard, W, hWC, inferInstance, hWcard, hWA, ?_, ?_⟩
  · intro w hw
    obtain ⟨d, hd, rfl⟩ := hWelt w hw
    rw [← hyΨ, hry, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Prod.ext (by simp) (by simpa using hyd d hd)
  · intro w hw hw1 g ⟨hgx, hgw⟩
    obtain ⟨d, hd, rfl⟩ := hWelt w hw
    have hd1 : d ≠ 1 := by
      rintro rfl
      apply hw1
      rw [show ((1 : centralizerOddCore n S e), (1 : CentralExtension F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn))) = 1 from rfl, map_one]
    obtain ⟨r, gW, rfl⟩ := hΨN _ hgx
    have hgC : Ψ (r, gW) ∈ C := by
      refine (hCmem _).mpr ⟨r, gW, ?_, rfl⟩
      rw [← hdC d hd hd1, Subgroup.mem_centralizer_singleton_iff]
      change Ψ (r, gW) ∈ Subgroup.centralizer {Ψ (1, d)} at hgw
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hgw
      have := congrArg Prod.snd (hΨinj hgw)
      simpa using this
    exact hgC.2

end CFSG.Wreathed.SameFieldUnitary
