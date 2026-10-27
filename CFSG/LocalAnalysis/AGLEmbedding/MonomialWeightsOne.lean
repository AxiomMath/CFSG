module

public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeights
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOneAux
public import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRankAux
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open Subgroup CFSG.Open
open scoped commutatorElement

section Abstract

variable {A V Z : Type*} [CommGroup A] [Finite A] [CommGroup V] [Finite V]
  [MulDistribMulAction A V] [CommGroup Z]

omit [MulDistribMulAction A V] in
theorem sq_le_card_closure_pair {s : ℕ} [Fact s.Prime] (hV : ∀ v : V, v ^ s = 1) {w w' : V}
    (hw1 : w ≠ 1) (hw' : w' ∉ zpowers w) : s ^ 2 ≤ Nat.card (closure {w, w'}) := by
  have hs : s.Prime := Fact.out
  have hz : zpowers w ≤ closure {w, w'} := zpowers_le.mpr (subset_closure (Set.mem_insert _ _))
  have hw's : w' ∈ closure {w, w'} := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzs : Nat.card (zpowers w) = s := by rw [Nat.card_zpowers, orderOf_eq_prime (hV w) hw1]
  have hlt : s < Nat.card (closure {w, w'}) := by
    rw [← hzs]
    by_contra hle
    exact hw' ((eq_of_le_of_card_ge hz (not_lt.mp hle)).ge hw's)
  have hp : IsPGroup s (closure {w, w'}) := fun v => ⟨1, by rw [pow_one]; exact Subtype.ext (hV v)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at hlt ⊢
  refine Nat.pow_le_pow_right hs.pos ?_
  by_contra h
  have h1 := Nat.pow_le_pow_right hs.pos (show n ≤ 1 by omega)
  rw [pow_one] at h1
  omega

theorem exists_orthogonal_of_coordPlane {s : ℕ} [Fact s.Prime] (hs5 : s ≠ 5) (c : Fin 3 → A)
    (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤) (hAcard : Nat.card A = 5 ^ 3)
    (hV : ∀ v : V, v ^ s = 1) (B : V →* V →* Z)
    (hB : ∀ (a : A) (v w : V), B (a • v) (a • w) = B v w) (halt : ∀ v, B v v = 1)
    {ατ : MulAut A} {βτ : MulAut V} (hτ : ∀ a v, βτ (a • v) = ατ a • βτ v)
    (hτc : ατ (c 0) = c 0 ^ 2 ∧ ατ (c 1) = c 1 ∧ ατ (c 2) = c 2 ^ 2)
    (hne : ∀ j, (fixedPiece (coordPlane c j) : Subgroup V) ≠ ⊥) :
    ∃ v : Fin 4 → V, (∀ j k, B (v j) (v k) = 1) ∧ s ^ 4 ≤ Nat.card (closure (Set.range v)) := by
  have h5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨h5⟩
  have hs : s.Prime := Fact.out
  have hcop := coprime_card_of_exponent hs5 hA hV
  have hFi := index_coordPlane c hA hAc hAcard
  have hinj := coordPlane_injective c hA hAc hAcard
  choose w hw hw1 using fun j =>
    (bot_or_exists_ne_one (fixedPiece (coordPlane c j) : Subgroup V)).resolve_left (hne j)
  have hβW : ∀ v ∈ (fixedPiece (coordPlane c 0) : Subgroup V),
      βτ v ∈ (fixedPiece (coordPlane c 0) : Subgroup V) := fun v hv => by
    have h := map_fixedPiece_le hτ (coordPlane c 0) ⟨v, hv, rfl⟩
    rwa [map_coordPlane_zero_of_diag c hτc] at h
  obtain ⟨w', hw'W, hw'z, hBw'⟩ := exists_isotropic_of_fpf hs hs5 hV (hA (c 0))
    (fun v hv => smul_mem_fixedPiece (c 0) hv)
    (fun v hv hfix => eq_one_of_smul_eq_of_mem_fixedPiece c hAc hcop hv hfix)
    (fun v => by rw [hτ, hτc.1]) hβW B (hB (c 0)) halt (hw 0) (hw1 0)
  have hcross : ∀ i i' : Fin 3, i ≠ i' → ∀ u ∈ (fixedPiece (coordPlane c i) : Subgroup V),
      ∀ u' ∈ (fixedPiece (coordPlane c i') : Subgroup V), B u u' = 1 :=
    fun i i' hii' u hu u' hu' =>
      pairing_fixedPiece_eq_one h5 hcop B hB (hFi i) (hFi i') (hinj.ne hii') hu hu'
  refine ⟨![w 0, w', w 1, w 2], fun j k => ?_, ?_⟩
  · fin_cases j <;> fin_cases k <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    all_goals first
      | exact halt _
      | exact hBw'
      | rw [pairing_swap B halt, hBw', inv_one]
      | exact hcross _ _ (by decide) _ (hw _) _ (hw _)
      | exact hcross _ _ (by decide) _ hw'W _ (hw _)
      | exact hcross _ _ (by decide) _ (hw _) _ hw'W
  · have hH : ∀ i, (![closure {w 0, w'}, zpowers (w 1), zpowers (w 2)] i : Subgroup V) ≤
        fixedPiece (coordPlane c i) := by
      intro i
      fin_cases i
      · exact (closure_le _).mpr
          (Set.insert_subset_iff.mpr ⟨hw 0, Set.singleton_subset_iff.mpr hw'W⟩)
      · exact zpowers_le.mpr (hw 1)
      · exact zpowers_le.mpr (hw 2)
    have hind := (iSupIndep_fixedPiece (V := V)
      (pairwise_sup_eq_top_of_index_eq_prime h5 hinj hFi) hcop).mono hH
    have hcard := card_iSup_eq_prod_of_iSupIndep hind
    rw [Fin.prod_univ_three] at hcard
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hcard
    have hle : (⨆ i, (![closure {w 0, w'}, zpowers (w 1), zpowers (w 2)] i : Subgroup V)) ≤
        closure (Set.range ![w 0, w', w 1, w 2]) := by
      refine iSup_le fun i => ?_
      fin_cases i
      · refine closure_le _ |>.mpr (Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩)
        · exact subset_closure ⟨0, rfl⟩
        · exact subset_closure ⟨1, rfl⟩
      · exact zpowers_le.mpr (subset_closure ⟨2, rfl⟩)
      · exact zpowers_le.mpr (subset_closure ⟨3, rfl⟩)
    have h0 := sq_le_card_closure_pair hV (hw1 0) hw'z
    have hz : ∀ j, Nat.card (zpowers (w j)) = s := fun j => by
      rw [Nat.card_zpowers, orderOf_eq_prime (hV _) (hw1 j)]
    calc s ^ 4 = s ^ 2 * s * s := by ring
      _ ≤ Nat.card (closure {w 0, w'}) * Nat.card (zpowers (w 1)) * Nat.card (zpowers (w 2)) := by
        rw [hz, hz]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
      _ = _ := hcard.symm
      _ ≤ _ := card_le_of_le hle

theorem exists_orthogonal_of_monomial {s : ℕ} [Fact s.Prime] (hs5 : s ≠ 5) (c : Fin 3 → A)
    (hA : ∀ a : A, a ^ 5 = 1) (hAc : closure (Set.range c) = ⊤) (hAcard : Nat.card A = 5 ^ 3)
    (hV : ∀ v : V, v ^ s = 1) (B : V →* V →* Z)
    (hB : ∀ (a : A) (v w : V), B (a • v) (a • w) = B v w) (halt : ∀ v, B v v = 1)
    {ασ ατ : MulAut A} {βσ βτ : MulAut V} (hσ : ∀ a v, βσ (a • v) = ασ a • βσ v)
    (hσc : ∀ i, ασ (c i) = c (i + 1)) (hτ : ∀ a v, βτ (a • v) = ατ a • βτ v)
    (hτc : ατ (c 0) = c 0 ^ 2 ∧ ατ (c 1) = c 1 ∧ ατ (c 2) = c 2 ^ 2)
    (hnt : ∃ (a : A) (v : V), a • v ≠ v) :
    ∃ v : Fin 4 → V, (∀ j k, B (v j) (v k) = 1) ∧ s ^ 4 ≤ Nat.card (closure (Set.range v)) := by
  rcases exists_injective_or_forall_coordPlane c hs5 hA hAc hAcard hV hσ hσc hτ hτc hnt with
    ⟨F, hinj, hF, hne⟩ | hne
  · exact exists_orthogonal_of_injective hs5 hA hV B hB halt hinj hF hne
  · exact exists_orthogonal_of_coordPlane hs5 c hA hAc hAcard hV B hB halt hτ hτc hne

end Abstract

section ClassTwo

variable {D : Type*} [Group D] [Finite D]

open scoped IsMulCommutative

theorem exists_isMulCommutative_of_commPairing (hc : commutator D ≤ center D) {ι : Type*}
    (v : ι → D ⧸ center D) (hv : ∀ i j, commPairing hc (v i) (v j) = 1) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ Nat.card (closure (Set.range v)) ≤ Nat.card E := by
  choose d hd using fun j => QuotientGroup.mk_surjective (v j)
  have hcommute : (Set.range d).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    have h1 := hv i j
    rw [← hd i, ← hd j, commPairing_mk_mk] at h1
    exact commutatorElement_eq_one_iff_commute.mp (congrArg Subtype.val h1)
  refine ⟨closure (Set.range d), isMulCommutative_closure hcommute, ?_⟩
  have hmap : (closure (Set.range d)).map (QuotientGroup.mk' (center D)) =
      closure (Set.range v) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    have hcomp : (⇑(QuotientGroup.mk' (center D)) ∘ d) = v := funext hd
    rw [hcomp]
  rw [← hmap]
  exact Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)

omit [Finite D] in
theorem commPairing_self (hc : commutator D ≤ center D) (v : D ⧸ center D) :
    commPairing hc v v = 1 := by
  induction v using QuotientGroup.induction_on with
  | H d =>
    rw [commPairing_mk_mk]
    exact Subtype.ext (commutatorElement_self d)

theorem exists_isMulCommutative_of_monomial {A : Type*} [CommGroup A] [Finite A] {s : ℕ}
    [Fact s.Prime] (hs5 : s ≠ 5) (c : Fin 3 → A) (hA : ∀ a : A, a ^ 5 = 1)
    (hAc : closure (Set.range c) = ⊤) (hAcard : Nat.card A = 5 ^ 3) (hD : ∀ d : D, d ^ s = 1)
    (hc : commutator D ≤ center D) (ψ : A →* MulAut D) (hψ : ∃ a, ψ a ≠ 1)
    {ασ ατ : MulAut A} {σ τ : MulAut D} (hσ : ∀ a, σ * ψ a = ψ (ασ a) * σ)
    (hσc : ∀ i, ασ (c i) = c (i + 1)) (hτ : ∀ a, τ * ψ a = ψ (ατ a) * τ)
    (hτc : ατ (c 0) = c 0 ^ 2 ∧ ατ (c 1) = c 1 ∧ ατ (c 2) = c 2 ^ 2) :
    ∃ E : Subgroup D, IsMulCommutative E ∧ s ^ 4 ≤ Nat.card E := by
  have hs : s.Prime := Fact.out
  have h5 : Nat.Prime 5 := by norm_num
  by_cases hZ : ∀ a : A, ∀ z ∈ center D, ψ a z = z
  ·
    have hcomm : IsMulCommutative (D ⧸ center D) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc
    let ρ : MulAut D →* MulAut (D ⧸ center D) := quotientCenterAut
    let _ : MulDistribMulAction A (D ⧸ center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
    have hV : ∀ v : D ⧸ center D, v ^ s = 1 := fun v => by
      induction v using QuotientGroup.induction_on with
      | H d => rw [← QuotientGroup.mk_pow, hD, QuotientGroup.mk_one]
    have hnt : ∃ (a : A) (v : D ⧸ center D), a • v ≠ v := by
      obtain ⟨a, ha⟩ := hψ
      obtain ⟨d, hd⟩ : ∃ d : D, ψ a d ≠ d := by
        by_contra h
        push Not at h
        exact ha (MulEquiv.ext h)
      refine ⟨a, d, fun h => hd (apply_eq_of_mk_apply_eq ((Nat.coprime_primes h5 hs).mpr
        (Ne.symm hs5)) hD ?_ (hZ a) h)⟩
      rw [← map_pow, hA a, map_one]
    have hcompat : ∀ (f : MulAut D) (α : MulAut A), (∀ a, f * ψ a = ψ (α a) * f) →
        ∀ (a : A) (v : D ⧸ center D), ρ f (a • v) = α a • ρ f v := fun f α hf a v => by
      change (ρ f * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ f) v
      rw [← map_mul, ← map_mul, hf]
    obtain ⟨v, hv, hcard⟩ := exists_orthogonal_of_monomial hs5 c hA hAc hAcard hV
      (commPairing hc) (fun a v w => commPairing_aut hc (hZ a) v w) (commPairing_self hc)
      (hcompat σ ασ hσ) hσc (hcompat τ ατ hτ) hτc hnt
    obtain ⟨E, hE, hEcard⟩ := exists_isMulCommutative_of_commPairing hc v hv
    exact ⟨E, hE, hcard.trans hEcard⟩
  ·
    push Not at hZ
    obtain ⟨a, z, hz, haz⟩ := hZ
    let ρ : MulAut D →* MulAut (center D) := MulAut.characteristic (center D)
    let _ : MulDistribMulAction A (center D) := MulDistribMulAction.compHom _ (ρ.comp ψ)
    have hcompat : ∀ (f : MulAut D) (α : MulAut A), (∀ a, f * ψ a = ψ (α a) * f) →
        ∀ (a : A) (v : center D), ρ f (a • v) = α a • ρ f v := fun f α hf a v => by
      change (ρ f * ρ (ψ a)) v = (ρ (ψ (α a)) * ρ f) v
      rw [← map_mul, ← map_mul, hf]
    obtain ⟨v, -, hcard⟩ := exists_orthogonal_of_monomial hs5 c hA hAc hAcard
      (fun z => Subtype.ext (hD z)) (1 : center D →* center D →* center D)
      (fun _ _ _ => rfl) (fun _ => rfl) (hcompat σ ασ hσ) hσc (hcompat τ ατ hτ) hτc
      ⟨a, ⟨z, hz⟩, fun h => haz (congrArg Subtype.val h)⟩
    refine ⟨(closure (Set.range v)).map (center D).subtype, ⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨x', -, hx'⟩ := x.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx']; exact
        (mem_center_iff.mp x'.2 y).symm)
    · rwa [card_map_of_injective (center D).subtype_injective]

end ClassTwo

theorem mem_normalizer_closure_of_conj_mem {Y : Type*} [Group Y] [Finite Y] {S : Set Y} {g : Y}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ closure S) : g ∈ normalizer (closure S : Set Y) := by
  have hle : (closure S).map (MulAut.conj g).toMonoidHom ≤ closure S := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : (closure S).map (MulAut.conj g).toMonoidHom = closure S :=
    eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : y = x := (MulAut.conj g).injective hyx
    rwa [← hxy]

theorem four_le_pRank_of_monomial {Y : Type} [Group Y] [Finite Y] {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hs5 : s ≠ 5) {Sg A : Subgroup Y} (c : Fin 3 → Y) {σ τ : Y}
    (hSg : IsPGroup s Sg) (hA : IsElemAbelian 5 A) (hAc : Subgroup.closure (Set.range c) = A)
    (hAcard : Nat.card A = 5 ^ 3) (hAS : A ≤ Subgroup.normalizer (Sg : Set Y))
    (hσS : σ ∈ Subgroup.normalizer (Sg : Set Y)) (hσ : ∀ i, σ * c i * σ⁻¹ = c (i + 1))
    (hτS : τ ∈ Subgroup.normalizer (Sg : Set Y))
    (hτ : τ * c 0 * τ⁻¹ = c 0 ^ 2 ∧ τ * c 1 * τ⁻¹ = c 1 ∧ τ * c 2 * τ⁻¹ = c 2 ^ 2)
    (hfaith : A ⊓ Subgroup.centralizer (Sg : Set Y) = ⊥) : 4 ≤ Open.pRank s Sg := by
  have := Fact.mk hs
  have h5 : Nat.Prime 5 := by norm_num
  have := Fact.mk h5
  have hnt : ¬ A ≤ Subgroup.centralizer (Sg : Set Y) := fun h => by
    rw [inf_eq_left.mpr h] at hfaith
    rw [hfaith, card_bot] at hAcard
    norm_num at hAcard
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnt fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup A := @IsMulCommutative.instCommGroup _ _ hA.1
  let ψ : A →* MulAut D := φ.comp (Subgroup.inclusion hAS)
  have hcompat : ∀ (t : Y) (htS : t ∈ Subgroup.normalizer (Sg : Set Y))
      (htA : t ∈ Subgroup.normalizer (A : Set Y)) (a : A),
      φ ⟨t, htS⟩ * ψ a = ψ (A.normalizerMonoidHom ⟨t, htA⟩ a) * φ ⟨t, htS⟩ := fun t htS htA a => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hAS a) =
      φ (Subgroup.inclusion hAS (A.normalizerMonoidHom ⟨t, htA⟩ a)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (a : Y) = t * a * t⁻¹ * t
    rw [inv_mul_cancel_right]
  have hcA : ∀ i, c i ∈ A := fun i => hAc ▸ subset_closure ⟨i, rfl⟩
  let c' : Fin 3 → A := fun i => ⟨c i, hcA i⟩
  have hσA : σ ∈ Subgroup.normalizer (A : Set Y) := hAc ▸
    mem_normalizer_closure_of_conj_mem (by rintro _ ⟨i, rfl⟩; rw [hσ]; exact hAc ▸ hcA _)
  have hτA : τ ∈ Subgroup.normalizer (A : Set Y) := by
    refine hAc ▸ mem_normalizer_closure_of_conj_mem ?_
    rintro _ ⟨i, rfl⟩
    rw [hAc]
    fin_cases i
    · change τ * c 0 * τ⁻¹ ∈ A
      rw [hτ.1]
      exact pow_mem (hcA 0) 2
    · change τ * c 1 * τ⁻¹ ∈ A
      rw [hτ.2.1]
      exact hcA 1
    · change τ * c 2 * τ⁻¹ ∈ A
      rw [hτ.2.2]
      exact pow_mem (hcA 2) 2
  have hA' : ∀ a : A, a ^ 5 = 1 := fun a => Subtype.ext (hA.2 a a.2)
  have hAc' : closure (Set.range c') = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hAc
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  have hψ : ∃ a : A, ψ a ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hxA, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnt
    apply hx
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hAS hxA⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxA⟩)
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ 5 = 1 := by
      have hn : (⟨x, hAS hxA⟩ : Subgroup.normalizer (Sg : Set Y)) ^ 5 = 1 :=
        Subtype.ext (hA.2 x hxA)
      change (Sg.normalizerMonoidHom ⟨x, hAS hxA⟩) ^ 5 = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs h5).mpr hs5)),
        pow_one] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = y := congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_of_monomial hs5 c' hA' hAc' hAcard hD hc
    ψ hψ (hcompat σ hσS hσA) (fun i => Subtype.ext (hσ i)) (hcompat τ hτS hτA)
    ⟨Subtype.ext hτ.1, Subtype.ext hτ.2.1, Subtype.ext hτ.2.2⟩
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  rw [hm] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hm (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end CFSG.AGLEmbedding
