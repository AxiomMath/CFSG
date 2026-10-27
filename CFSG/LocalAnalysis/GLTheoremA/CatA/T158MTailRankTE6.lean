module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailNorm
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSetup
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped MatrixGroups

section Lift

variable {Y : Type} {T : Type*} [Group Y] [Finite Y] [Group T]

theorem exists_elemAbelian_of_inversions {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {m : ℕ} (h w : Fin (m + 1) → T)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → i ≠ Fin.last m → w i * h j * (w i)⁻¹ = h j) :
    ∃ F : Subgroup Y, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ (m + 1) ∧ F ⊓ φ.ker = ⊥ ∧
      F.map φ ≤ Subgroup.closure (Set.range h) := by
  classical
  haveI : Finite T := Finite.of_surjective φ hφ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ i, h i ^ 3 = 1 := fun i => (hord i) ▸ pow_orderOf_eq_one (h i)
  set D : Subgroup T := Subgroup.closure (Set.range h) with hD
  have hDcard : 3 ^ (m + 1) ≤ Nat.card D := three_pow_le_card_closure h w hcomm hord hinv hfix
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x :=
    comap_closure_comm_of_inversions hφ hker h w hcomm hpow hinv hfix
  have hlift : ∀ e ∈ D, ∃ y : Y, φ y = e ∧ y ^ 3 = 1 := by
    intro e he
    refine exists_lift_pow_eq_one_of_mem_closure hF Subgroup.subset_closure ?_ he
    rintro _ ⟨i, rfl⟩
    exact exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide) (hpow i) (hinv i)
  obtain ⟨E, hEab, hEmap, hEcard⟩ := exists_elemAbelian_index_of_lift hF hlift
  obtain ⟨F₀, hFE, -, hFW, hFsup⟩ := exists_isCompl_of_isElemAbelian Nat.prime_three hEab
    (inf_le_left : E ⊓ φ.ker ≤ E) (bot_le : (⊥ : Subgroup Y) ≤ E) (by simp)
  have hF₀el : IsElemAbelian 3 F₀ := hEab.mono hFE
  have hF₀card : Nat.card F₀ = Nat.card D := by
    have hFN : F₀ ≤ Subgroup.normalizer ((E ⊓ φ.ker : Subgroup Y) : Set Y) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hc : a * x = x * a := hEab.comm (hFE ha) hx.1
        rw [hc, mul_inv_cancel_right]
        exact hx
      · intro hx
        have hx' : x ∈ E := by
          have := E.mul_mem (E.mul_mem (E.inv_mem (hFE ha)) hx.1) (hFE ha)
          simpa [mul_assoc] using this
        have hc : a * x = x * a := hEab.comm (hFE ha) hx'
        rw [hc, mul_inv_cancel_right] at hx
        exact hx
    have hmul :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hFN
    rw [hFsup, hFW, Subgroup.card_bot, mul_one, ← hEcard] at hmul
    have hpos : 0 < Nat.card ↥(E ⊓ φ.ker) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos hmul.symm
  have hF₀ker : F₀ ⊓ φ.ker = ⊥ := by
    have e : F₀ ⊓ φ.ker = F₀ ⊓ (E ⊓ φ.ker) := by
      rw [← inf_assoc, inf_eq_left.mpr hFE]
    rw [e, hFW]
  obtain ⟨k, hk⟩ := hF₀el.isPGroup.exists_card_eq
  have hmk : m + 1 ≤ k := by
    have h1 := hDcard
    rw [← hF₀card, hk] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥F₀) 3
    (show 3 ^ (m + 1) ∣ Nat.card F₀ from hk ▸ pow_dvd_pow 3 hmk)
  have hK'F : K'.map F₀.subtype ≤ F₀ := Subgroup.map_subtype_le K'
  refine ⟨K'.map F₀.subtype, hF₀el.mono hK'F, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective F₀.subtype_injective, hK']
  · exact le_bot_iff.mp (hF₀ker ▸ inf_le_inf_right φ.ker hK'F)
  · exact hEmap ▸ Subgroup.map_mono (hK'F.trans hFE)

end Lift

section Torus

open CFSG.RankThree.PartTwo.Census.Exceptional

variable {S : Type*} [Group S] {F : Type*} [Field F]

theorem exists_inversions_of_commuting_SL2_torus (hF : ringChar F = 2) {m : ℕ}
    (φ : Fin m → SL(2, F) →* S) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A)
    {τ g : S} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hτφ : ∀ i A, φ i A * τ = τ * φ i A)
    (hgτ : g * τ * g⁻¹ = τ⁻¹) :
    ∃ h w : Fin (m + 1) → S, (∀ i j, Commute (h i) (h j)) ∧ (∀ i, orderOf (h i) = 3) ∧
      (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      ∀ i j, i ≠ j → i ≠ Fin.last m → w i * h j * (w i)⁻¹ = h j := by
  obtain ⟨g₀, hg₀⟩ := exists_inverted_sl2Three_even hF
  have hne : sl2Three F ≠ 1 := fun h => sl2Three_not_commute F (by rw [h]; simp)
  have hw3 : orderOf (sl2Three F) = 3 := orderOf_eq_prime (sl2Three_pow_three F) hne
  refine ⟨Fin.snoc (fun i : Fin m => φ i (sl2Three F)) τ,
    Fin.snoc (fun i : Fin m => φ i g₀) g, ?_, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact Commute.refl _
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact (hτφ j _).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hτφ i _
      | cast j =>
        simp only [Fin.snoc_castSucc]
        by_cases hij : i = j
        · rw [hij]
        · exact hcomm i j hij _ _
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using orderOf_eq_prime hτ3 hτ1
    | cast i =>
      simp only [Fin.snoc_castSucc]
      rw [orderOf_injective _ (hφ i), hw3]
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hgτ
    | cast i =>
      simp only [Fin.snoc_castSucc]
      rw [← map_inv, ← map_mul, ← map_mul, hg₀, map_inv]
  · intro i j hij hi
    induction i using Fin.lastCases with
    | last => exact absurd rfl hi
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hτφ i g₀, mul_inv_cancel_right]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        have hij' : i ≠ j := fun h => hij (h ▸ rfl)
        rw [hcomm i j hij' g₀ _, mul_inv_cancel_right]

end Torus

section TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Minuscule
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.CentralCover CFSG.Assembly.RankThreeEven TauCeti
open CFSG.LieType.Steinberg.TwistedE6

private theorem nm_conj_hm_self
    {k : Type*} [Field k]
    (a : Fin (Tag.rank .E6)) (t : kˣ) :
    e6Data_valid.nm k a * e6Data_valid.hm k a t * (e6Data_valid.nm k a)⁻¹ =
      e6Data_valid.hm k a t⁻¹ := by
  rw [e6Data_valid.nm_conj_hm, Tag.cartan_self, ← e6Data_valid.hm_mul]
  congr 1
  group

private theorem nm_conj_hm_orth
    {k : Type*} [Field k]
    {a b : Fin (Tag.rank .E6)} (hba : Tag.cartan .E6 b a = 0) (t : kˣ) :
    e6Data_valid.nm k a * e6Data_valid.hm k b t * (e6Data_valid.nm k a)⁻¹ =
      e6Data_valid.hm k b t := by
  rw [e6Data_valid.nm_conj_hm, hba, neg_zero, zpow_zero, e6Data_valid.hm_one, mul_one]

private theorem nHatE_three_conj_pair
    {k : Type*} [Field k] (t s : kˣ) :
    nHatE k (nf 3) * (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
        (nHatE k (nf 3))⁻¹ =
      (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s)⁻¹ := by
  have c05 : Tag.cartan .E6 (nd 0) (nd 5) = 0 := by decide
  have c50 : Tag.cartan .E6 (nd 5) (nd 0) = 0 := by decide
  have e5 : e6Data_valid.nm k (nd 5) * (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
      (e6Data_valid.nm k (nd 5))⁻¹ = e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s⁻¹ := by
    rw [show ∀ a b c : e6Data_valid.minGroup k, a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹)
      from fun a b c => by group, nm_conj_hm_orth c05, nm_conj_hm_self]
  have e0 : e6Data_valid.nm k (nd 0) *
      (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s⁻¹) *
      (e6Data_valid.nm k (nd 0))⁻¹ =
        e6Data_valid.hm k (nd 0) t⁻¹ * e6Data_valid.hm k (nd 5) s⁻¹ := by
    rw [show ∀ a b c : e6Data_valid.minGroup k, a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹)
      from fun a b c => by group, nm_conj_hm_self, nm_conj_hm_orth c50]
  rw [nHatE_three]
  calc e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) *
        (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
        (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))⁻¹
      = e6Data_valid.nm k (nd 0) * (e6Data_valid.nm k (nd 5) *
          (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s) *
          (e6Data_valid.nm k (nd 5))⁻¹) * (e6Data_valid.nm k (nd 0))⁻¹ := by group
    _ = e6Data_valid.hm k (nd 0) t⁻¹ * e6Data_valid.hm k (nd 5) s⁻¹ := by rw [e5, e0]
    _ = (e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) s)⁻¹ := by
      have hinv : ∀ (a : Fin (Tag.rank .E6)) (u : kˣ),
          e6Data_valid.hm k a u⁻¹ = (e6Data_valid.hm k a u)⁻¹ := fun a u =>
        map_inv (e6Data_valid.hHom k a) u
      rw [mul_inv_rev, hinv, hinv]
      exact (hm_commute (k := k) (nd 0) (nd 5) t s).inv_inv.eq

private theorem nHat_three_conj_te6Torus
    {k : Type*} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (t : kˣ) :
    nHat θ (nf 3) * te6Torus θ hθ t * (nHat θ (nf 3))⁻¹ = (te6Torus θ hθ t)⁻¹ := by
  apply Subtype.ext
  change nHatE k (nf 3) * hPairE θ (nd 0) (nd 5) t * (nHatE k (nf 3))⁻¹ =
    (hPairE θ (nd 0) (nd 5) t)⁻¹
  exact nHatE_three_conj_pair t (Units.map (θ : k →* k) t)

section Generic

variable {k : Type*} [Field k] (θ : k →+* k) {F : Type*} [Field F] (j : F →+* k)
  (hj : ∀ x, θ (j x) = j x) (hθ : ∀ c, θ (θ c) = c)

include hθ in
private theorem inversions_te6
    {G : Type} [Group G]
    (Θ : fixedGroup k θ →* G) (hΘ : ∀ g, Θ g = 1 → g ∈ Subgroup.center (fixedGroup k θ))
    (hinj : ∀ i, Function.Injective (Θ.comp (te6SL2 θ j hj i))) (hF : ringChar F = 2)
    {t : kˣ} (htt : t * Units.map (θ : k →* k) t = 1) (ht3 : t ^ 3 = 1)
    (ht2 : ((t : k)) ^ 2 ≠ 1) :
    ∃ h w : Fin 5 → G, (∀ i j, Commute (h i) (h j)) ∧ (∀ i, orderOf (h i) = 3) ∧
      (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      ∀ i j, i ≠ j → i ≠ Fin.last 4 → w i * h j * (w i)⁻¹ = h j := by
  set φ : Fin 4 → SL(2, F) →* G := fun i => Θ.comp (te6SL2 θ j hj i) with hφ
  have hcomm : ∀ i i', i ≠ i' → ∀ A B : SL(2, F), φ i A * φ i' B = φ i' B * φ i A := by
    intro i i' hii A B
    simp only [hφ, MonoidHom.comp_apply, ← map_mul, te6SL2_commute θ j hj hii A B]
  set s := Θ (te6Torus θ hθ t) with hs
  have hsφ : ∀ i A, Commute (φ i A) s := fun i A =>
    (show Commute (te6Torus θ hθ t) (te6SL2 θ j hj i A) from
      te6Torus_commute θ j hj hθ htt i A).symm.map Θ
  have hτ3 : s ^ 3 = 1 := by rw [hs, ← map_pow, te6Torus_pow, ht3, te6Torus_one, map_one]
  have hτ1 : s ≠ 1 := fun h => te6Torus_not_mem_center θ hθ ht2 (hΘ _ h)
  have hgτ : Θ (nHat θ (nf 3)) * s * (Θ (nHat θ (nf 3)))⁻¹ = s⁻¹ := by
    rw [hs, ← map_inv, ← map_mul, ← map_mul, nHat_three_conj_te6Torus, map_inv]
  exact exists_inversions_of_commuting_SL2_torus hF (m := 4) φ hinj hcomm hτ3 hτ1
    (fun i A => (hsφ i A).eq) hgτ

end Generic

theorem te6_inversions
    (d : TypeTwistedE6LieIndex) (h2 : ringChar d.1.fixedField = 2)
    (h3 : d.1.fieldOrder % 3 = 2) :
    ∃ h w : Fin 5 → FixedPointCandidate d.steinberg, (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      ∀ i j, i ≠ j → i ≠ Fin.last 4 → w i * h j * (w i)⁻¹ = h j := by
  classical
  have hθ : ∀ c, quadFrob d (quadFrob d c) = c := quadFrob_quadFrob d
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  have : Fintype (quadField d) := Fintype.ofFinite _
  have hdvd : 3 ∣ Nat.card (quadField d)ˣ := by
    rw [Nat.card_units, card_quadField]
    have h1 : d.1.fieldOrder ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
    have hpos : 1 ≤ d.1.fieldOrder ^ 2 := Nat.one_le_pow _ _ d.1.fieldOrder_pos
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have ht3 : t ^ 3 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hfr : Units.map (quadFrob d : quadField d →* quadField d) t = t ^ d.1.fieldOrder :=
    Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_ofClass]
      exact Subtype.ext (by rw [coe_quadFrob, SubmonoidClass.coe_pow]))
  have htt : t * Units.map (quadFrob d : quadField d →* quadField d) t = 1 := by
    rw [hfr, ← pow_succ']
    exact orderOf_dvd_iff_pow_eq_one.1 (ht ▸ (by omega : 3 ∣ d.1.fieldOrder + 1))
  have ht2 : ((t : quadField d)) ^ 2 ≠ 1 := by
    intro h
    have h' : t ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have h'' : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h'
    rw [ht] at h''
    omega
  exact inversions_te6 (quadFrob d) (quadIncl d) hj hθ (toQuot (te6Embed d) hC)
    (fun g hg => mem_center_of_toQuot_eq_one (te6Embed_injective d) hC hg) hinj h2 htt ht3 ht2

theorem te6_inversions'
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) (h2 : q.p = 2) (hodd : Odd q.exponent) :
    ∃ h w : Fin 5 → ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩, (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      ∀ i j, i ≠ j → i ≠ Fin.last 4 → w i * h j * (w i)⁻¹ = h j := by
  set d : ValidLieTypeIndex := ⟨.twistedE6 q, hv⟩ with hd
  haveI := finite_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  have hchar : d.characteristic = q.p := LieTypeIndex.characteristic_twistedE6 q
  have h3 : q.p ^ q.exponent % 3 = 2 := by
    rw [h2]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact te6_inversions ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩
    (by rw [ringChar_fixedField_eq, hchar]; exact h2)
    (by
      show (LieTypeIndex.twistedE6 q).fieldOrder % 3 = 2
      rw [LieTypeIndex.fieldOrder_twistedE6, PrimePower.card_def]
      exact h3)

end TwistedE6

theorem t158RankTE6_holds :
    T158RankTE6 := by
  intro Y _ _ n hn _ _ hcat
  classical
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | twistedE6 q =>
    obtain ⟨hq2, hqn⟩ := hP
    obtain ⟨h, w, hcomm, hord, hinv, hfix⟩ := te6_inversions' q hv hq2 (hqn ▸ hn)
    let φ : Y →* TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩ :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
    have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hφker : φ.ker = Subgroup.center Y := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have h1 : (QuotientGroup.mk' (Subgroup.center Y)) x = 1 := by
          apply e.injective
          rw [map_one]
          exact hx
        exact (QuotientGroup.eq_one_iff _).1 h1
      · intro hx
        change e ((QuotientGroup.mk' (Subgroup.center Y)) x) = 1
        rw [show (QuotientGroup.mk' (Subgroup.center Y)) x = 1 from
          (QuotientGroup.eq_one_iff _).2 hx, map_one]
    obtain ⟨F, hF, hFcard, hFker, -⟩ :=
      exists_elemAbelian_of_inversions hφ (by rw [hφker]) h w hcomm hord hinv hfix
    exact ⟨F, hF, hFcard, by rw [← hφker]; exact hFker⟩
  | _ => exact hP.elim

section Tail

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem t158TailFaith_of_norm
    {Q : TauCeti.CFSGIndex → Prop} (hN : T158NormConj Q) : T158TailFaith Q :=
  t158TailFaith_of_te6 hN t158RankTE6_holds

theorem t158NormConj_of_tables
    (T : Tables112) (TL : TableL2) (TT : Tables112Types) {Q : TauCeti.CFSGIndex → Prop} : T158NormConj Q :=
  t158NormConj_of T TL TT t158RankTE6_holds

end Tail

end CFSG.LocalAnalysis.GLTheoremA.T158

end
