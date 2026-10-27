module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
import CFSG.FeitThompson.Representations.IntegerNormBoundEqualitySignedBlocks
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate

noncomputable section

variable {α : Type*} [Fintype α]

theorem cfInner_star_star (f h : α → ℂ) :
    cfInner (star f) (star h) = conj (cfInner f h) := by
  have hf : (star f : α → ℂ) = fun x => conj (f x) := funext fun _ => rfl
  have hh : (star h : α → ℂ) = fun x => conj (h x) := funext fun _ => rfl
  rw [hf, hh, cfInner_conj_conj]

theorem cfInner_sum_smul_right_of_gram_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ι → α → ℂ} {g : ι → ℂ} (hu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0)
    (c : ι → ℂ) (j : ι) : cfInner (∑ i, c i • u i) (u j) = c j * g j := by
  rw [cfInner_sum_left]
  have h : ∀ i ∈ Finset.univ, cfInner (c i • u i) (u j) = if i = j then c j * g j else 0 := by
    intro i _
    rw [cfInner_smul_left, hu i j]
    by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl h]
  simp

theorem cfInner_sum_smul_of_gram_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ι → α → ℂ} {g : ι → ℂ} (hu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0)
    (c c' : ι → ℂ) :
    cfInner (∑ i, c i • u i) (∑ i, c' i • u i) = ∑ i, c i * conj (c' i) * g i := by
  rw [cfInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cfInner_smul_right, cfInner_sum_smul_right_of_gram_diag hu]
  ring

theorem linearIndependent_of_gram_diag {ι : Type*} [Finite ι] [DecidableEq ι]
    {u : ι → α → ℂ} {g : ι → ℂ} (hu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0)
    (hg : ∀ i, g i ≠ 0) : LinearIndependent ℤ u := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h0 : ∑ i, ((c i : ℂ)) • u i = 0 := by
    simpa [Int.cast_smul_eq_zsmul] using hc
  have h1 := cfInner_sum_smul_right_of_gram_diag hu (fun i => (c i : ℂ)) j
  rw [h0, cfInner_zero_left] at h1
  exact_mod_cast (mul_eq_zero.1 h1.symm).resolve_right (hg j)

theorem eq_single_of_gram_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ι → α → ℂ} {g : ι → ℂ} (hu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0)
    (hg : ∀ i, g i ≠ 0) {c : ι → ℤ} {i : ι} (hc : u i = ∑ j, (c j : ℂ) • u j) :
    ∀ j, (c j : ℂ) = if i = j then 1 else 0 := by
  intro j
  have h1 := cfInner_sum_smul_right_of_gram_diag hu (fun k => (c k : ℂ)) j
  rw [← hc, hu i j] at h1
  by_cases hij : i = j
  · rw [if_pos hij] at h1 ⊢
    subst hij
    exact mul_right_cancel₀ (hg i) (h1.symm.trans (one_mul _).symm)
  · rw [if_neg hij] at h1 ⊢
    exact (mul_eq_zero.1 h1.symm).resolve_right (hg j)

theorem cfInner_sum_sum_of_subset {G : Type*} [Fintype G] [DecidableEq (G → ℂ)]
    {E A B : Finset (G → ℂ)}
    (hON : IsOrthonormalFamily fun w : {v // v ∈ E} => (w : G → ℂ))
    (hA : A ⊆ E) (hB : B ⊆ E) :
    cfInner (∑ a ∈ A, a) (∑ b ∈ B, b) = ((A ∩ B).card : ℂ) := by
  rw [cfInner_sum_left]
  have h : ∀ a ∈ A, cfInner a (∑ b ∈ B, b) = if a ∈ B then 1 else 0 := by
    intro a ha
    rw [cfInner_sum_right]
    have key : ∀ b ∈ B, cfInner a b = if b = a then 1 else 0 := by
      intro b hb
      have := hON.cfInner_eq_ite ⟨a, hA ha⟩ ⟨b, hB hb⟩
      simpa [Subtype.mk_eq_mk, eq_comm] using this
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' B a (fun _ => (1 : ℂ))]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_mem, Finset.sum_const]
  simp

section Extend

variable {L G : Type*} [Group L] [Group G] {ι : Type*} [Fintype ι]
  {S : Set (L → ℂ)} {u : ι → L → ℂ} {v : ι → G → ℂ}

def extendAlong (hS : S = Set.range u) (hu : LinearIndependent ℤ u)
    (hv : ∀ i, v i ∈ Submodule.span ℤ (Irr G)) :
    Submodule.span ℤ S →ₗ[ℤ] Submodule.span ℤ (Irr G) :=
  ((Module.Basis.span hu).constr ℤ fun i => (⟨v i, hv i⟩ : Submodule.span ℤ (Irr G))).comp
    (LinearEquiv.ofEq (Submodule.span ℤ S) (Submodule.span ℤ (Set.range u))
      (congrArg (Submodule.span ℤ) hS)).toLinearMap

omit [Group L] in
theorem exists_coe_extendAlong_eq (hS : S = Set.range u) (hu : LinearIndependent ℤ u)
    (hv : ∀ i, v i ∈ Submodule.span ℤ (Irr G)) (f : Submodule.span ℤ S) :
    ∃ c : ι → ℤ, (f : L → ℂ) = ∑ i, (c i : ℂ) • u i ∧
      (extendAlong hS hu hv f : G → ℂ) = ∑ i, (c i : ℂ) • v i := by
  set b := Module.Basis.span hu with hb
  set e := LinearEquiv.ofEq (Submodule.span ℤ S) (Submodule.span ℤ (Set.range u))
    (congrArg (Submodule.span ℤ) hS) with he
  set r : ι → ℤ := fun i => b.repr (e f) i with hr
  have h1 : ∑ i, r i • b i = e f := b.sum_repr (e f)
  have hbi : ∀ i, ((b i : Submodule.span ℤ (Set.range u)) : L → ℂ) = u i := fun i => by
    rw [hb, Module.Basis.span_apply]
  refine ⟨r, ?_, ?_⟩
  · have h2 : ((e f : Submodule.span ℤ (Set.range u)) : L → ℂ) = (f : L → ℂ) :=
      LinearEquiv.coe_ofEq_apply _ _
    rw [← h2, ← h1, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [SetLike.val_smul, hbi i, Int.cast_smul_eq_zsmul]
  · have h3 : extendAlong hS hu hv f = (b.constr ℤ fun i =>
        (⟨v i, hv i⟩ : Submodule.span ℤ (Irr G))) (e f) := rfl
    rw [h3, ← h1, map_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_zsmul, Module.Basis.constr_basis, SetLike.val_smul, Int.cast_smul_eq_zsmul]

end Extend

def spanIrrToVirtualChars (G : Type*) [Group G] :
    Submodule.span ℤ (Irr G) →+ virtualChars G :=
  (Submodule.inclusion span_Irr_le_virtualChars).toAddMonoidHom

@[simp] theorem coe_spanIrrToVirtualChars {G : Type*} [Group G] (f : Submodule.span ℤ (Irr G)) :
    ((spanIrrToVirtualChars G f : virtualChars G) : G → ℂ) = (f : G → ℂ) := (rfl)

theorem exists_isCoherentWith_of_gram_eq
    {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set (L → ℂ)} {u : ι → L → ℂ} (hS : S = Set.range u) {g : ι → ℂ}
    (hgramu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0) (hgne : ∀ i, g i ≠ 0)
    {v : ι → G → ℂ} (hvmem : ∀ i, v i ∈ Submodule.span ℤ (Irr G))
    (hgramv : ∀ i j, cfInner (v i) (v j) = if i = j then g i else 0)
    {τ : charSpanZero S →+ Submodule.span ℤ (Irr G)}
    (hτ : ∀ w : charSpanZero S, ∀ c : ι → ℤ, ((w : L → ℂ)) = ∑ i, (c i : ℂ) • u i →
      ((τ w : G → ℂ)) = ∑ i, (c i : ℂ) • v i) :
    ∃ ν : Submodule.span ℤ S →+ virtualChars G,
      IsCoherentWith S ((spanIrrToVirtualChars G).comp τ) ν ∧
      ∀ i, ∀ w : Submodule.span ℤ S, ((w : L → ℂ)) = u i →
        ((ν w : virtualChars G) : G → ℂ) = v i := by
  have hu : LinearIndependent ℤ u := linearIndependent_of_gram_diag hgramu hgne
  set ν₀ := extendAlong hS hu hvmem with hν₀
  refine ⟨(spanIrrToVirtualChars G).comp ν₀.toAddMonoidHom, ⟨?_, ?_⟩, ?_⟩
  · intro w w'
    obtain ⟨c, hc1, hc2⟩ := exists_coe_extendAlong_eq hS hu hvmem w
    obtain ⟨c', hd1, hd2⟩ := exists_coe_extendAlong_eq hS hu hvmem w'
    change cfInner (ν₀ w : G → ℂ) (ν₀ w' : G → ℂ) = _
    rw [hc1, hd1, hc2, hd2, cfInner_sum_smul_of_gram_diag hgramv,
      cfInner_sum_smul_of_gram_diag hgramu]
  · intro w
    obtain ⟨c, hc1, hc2⟩ := exists_coe_extendAlong_eq hS hu hvmem
      (Submodule.inclusion (charSpanZero_le S) w)
    refine Subtype.ext ?_
    change (ν₀ (Submodule.inclusion (charSpanZero_le S) w) : G → ℂ) = (τ w : G → ℂ)
    rw [hc2, hτ w c hc1]
  · intro i w hw
    obtain ⟨c, hc1, hc2⟩ := exists_coe_extendAlong_eq hS hu hvmem w
    have hci := eq_single_of_gram_diag hgramu hgne (hw ▸ hc1 : u i = ∑ j, (c j : ℂ) • u j)
    change (ν₀ w : G → ℂ) = v i
    rw [hc2, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => congrArg (· • v j) (hci j)]
    simp

theorem exists_isCoherentWith_of_four_member_mixed_norm
    {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
    {ξ ψ : L → ℂ} (hξL : ξ ∈ Submodule.span ℤ (Irr L)) (hψL : ψ ∈ Submodule.span ℤ (Irr L))
    {S : Set (L → ℂ)} (hS : S = {ξ, star ξ, ψ, star ψ})
    (hinj : Function.Injective ![ξ, star ξ, ψ, star ψ])
    (horth : ∀ f ∈ S, ∀ h ∈ S, f ≠ h → IsOrthogonal f h)
    {d : ℝ} (hd : 0 < d) (hdeg : ∀ f ∈ S, f 1 = (d : ℂ))
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hξn : cfInner ξ ξ = (n : ℂ)) (hψm : cfInner ψ ψ = (m : ℂ))
    {τ : charSpanZero S →+ Submodule.span ℤ (Irr G)}
    (hτiso : ∀ w w' : charSpanZero S,
      cfInner ((τ w : G → ℂ)) ((τ w' : G → ℂ)) = cfInner ((w : L → ℂ)) ((w' : L → ℂ)))
    {R T : Finset (G → ℂ)} (hRT : Disjoint R T)
    (hRmem : ∀ r ∈ R, r ∈ Submodule.span ℤ (Irr G))
    (hTmem : ∀ t ∈ T, t ∈ Submodule.span ℤ (Irr G))
    (hON : IsOrthonormalFamily fun w : {x // x ∈ R ∪ T} => (w : G → ℂ))
    (hτR : ∀ w : charSpanZero S, (w : L → ℂ) = ξ - star ξ → (τ w : G → ℂ) = ∑ r ∈ R, r)
    (hτT : ∀ w : charSpanZero S, (w : L → ℂ) = ψ - star ψ → (τ w : G → ℂ) = ∑ t ∈ T, t) :
    R.card = 2 * n ∧ T.card = 2 * m ∧
      ∃ R₀ ⊆ R, ∃ T₀ ⊆ T, R₀.card = n ∧ T₀.card = m ∧
        ∃ ν : Submodule.span ℤ S →+ virtualChars G,
          IsCoherentWith S ((spanIrrToVirtualChars G).comp τ) ν ∧
          (∀ w : Submodule.span ℤ S, (w : L → ℂ) = ξ →
            ((ν w : virtualChars G) : G → ℂ) = ∑ r ∈ R₀, r) ∧
          (∀ w : Submodule.span ℤ S, (w : L → ℂ) = star ξ →
            ((ν w : virtualChars G) : G → ℂ) = -∑ r ∈ R.filter (· ∉ R₀), r) ∧
          (∀ w : Submodule.span ℤ S, (w : L → ℂ) = ψ →
            ((ν w : virtualChars G) : G → ℂ) = ∑ t ∈ T₀, t) ∧
          (∀ w : Submodule.span ℤ S, (w : L → ℂ) = star ψ →
            ((ν w : virtualChars G) : G → ℂ) = -∑ t ∈ T.filter (· ∉ T₀), t) := by
  classical
  have hmξ : ξ ∈ S := by rw [hS]; simp
  have hmsξ : star ξ ∈ S := by rw [hS]; simp
  have hmψ : ψ ∈ S := by rw [hS]; simp
  have hmsψ : star ψ ∈ S := by rw [hS]; simp
  have hsp : ∀ f ∈ S, f ∈ Submodule.span ℤ S := fun f hf => Submodule.subset_span hf
  have ho : ∀ f ∈ S, ∀ h ∈ S, f ≠ h → cfInner f h = 0 := fun f hf h hh hne =>
    isOrthogonal_iff.1 (horth f hf h hh hne)
  have hne01 : ξ ≠ star ξ := by simpa using hinj.ne (show (0 : Fin 4) ≠ 1 by decide)
  have hne02 : ξ ≠ ψ := by simpa using hinj.ne (show (0 : Fin 4) ≠ 2 by decide)
  have hne03 : ξ ≠ star ψ := by simpa using hinj.ne (show (0 : Fin 4) ≠ 3 by decide)
  have hne12 : star ξ ≠ ψ := by simpa using hinj.ne (show (1 : Fin 4) ≠ 2 by decide)
  have hne13 : star ξ ≠ star ψ := by simpa using hinj.ne (show (1 : Fin 4) ≠ 3 by decide)
  have hne23 : ψ ≠ star ψ := by simpa using hinj.ne (show (2 : Fin 4) ≠ 3 by decide)
  have hsξ : cfInner (star ξ) (star ξ) = (n : ℂ) := by rw [cfInner_star_star, hξn]; simp
  have hsψ : cfInner (star ψ) (star ψ) = (m : ℂ) := by rw [cfInner_star_star, hψm]; simp
  have hA : ξ - star ξ ∈ charSpanZero S :=
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ (hsp _ hmξ) (hsp _ hmsξ), by
      simp [hdeg _ hmξ, hdeg _ hmsξ]⟩
  have hB : ψ - star ψ ∈ charSpanZero S :=
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ (hsp _ hmψ) (hsp _ hmsψ), by
      simp [hdeg _ hmψ, hdeg _ hmsψ]⟩
  have hC : ξ - ψ ∈ charSpanZero S :=
    mem_charSpanZero.2 ⟨Submodule.sub_mem _ (hsp _ hmξ) (hsp _ hmψ), by
      simp [hdeg _ hmξ, hdeg _ hmψ]⟩
  set A : charSpanZero S := ⟨ξ - star ξ, hA⟩ with hAdef
  set B : charSpanZero S := ⟨ψ - star ψ, hB⟩ with hBdef
  set C : charSpanZero S := ⟨ξ - ψ, hC⟩ with hCdef
  have hRsub : R ⊆ R ∪ T := Finset.subset_union_left
  have hTsub : T ⊆ R ∪ T := Finset.subset_union_right
  have hin : ∀ X ⊆ R ∪ T, ∀ Y ⊆ R ∪ T,
      cfInner (∑ x ∈ X, x) (∑ y ∈ Y, y) = ((X ∩ Y).card : ℂ) :=
    fun X hX Y hY => cfInner_sum_sum_of_subset hON hX hY
  have hRcard : R.card = 2 * n := by
    have h1 : cfInner (∑ r ∈ R, r) (∑ r ∈ R, r) = (R.card : ℂ) := by
      rw [hin _ hRsub _ hRsub]; simp
    have h2 := hτiso A A
    rw [hτR A rfl, h1] at h2
    have h3 : cfInner (ξ - star ξ) (ξ - star ξ) = 2 * (n : ℂ) := by
      rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hξn, hsξ,
        ho _ hmξ _ hmsξ hne01, ho _ hmsξ _ hmξ (Ne.symm hne01)]
      ring
    have h4 : ((R.card : ℂ)) = ((2 * n : ℕ) : ℂ) := by
      rw [h2, hAdef]
      change cfInner (ξ - star ξ) (ξ - star ξ) = _
      rw [h3]; push_cast; ring
    exact_mod_cast h4
  have hTcard : T.card = 2 * m := by
    have h1 : cfInner (∑ t ∈ T, t) (∑ t ∈ T, t) = (T.card : ℂ) := by
      rw [hin _ hTsub _ hTsub]; simp
    have h2 := hτiso B B
    rw [hτT B rfl, h1] at h2
    have h3 : cfInner (ψ - star ψ) (ψ - star ψ) = 2 * (m : ℂ) := by
      rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hψm, hsψ,
        ho _ hmψ _ hmsψ hne23, ho _ hmsψ _ hmψ (Ne.symm hne23)]
      ring
    have h4 : ((T.card : ℂ)) = ((2 * m : ℕ) : ℂ) := by
      rw [h2, hBdef]
      change cfInner (ψ - star ψ) (ψ - star ψ) = _
      rw [h3]; push_cast; ring
    exact_mod_cast h4
  set f : G → ℂ := (τ C : G → ℂ) with hfdef
  have hfmem : f ∈ Submodule.span ℤ (Irr G) := (τ C).2
  have hfnorm : cfInner f f = (n : ℂ) + (m : ℂ) := by
    have h2 := hτiso C C
    rw [hfdef, h2, hCdef]
    change cfInner (ξ - ψ) (ξ - ψ) = _
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hξn, hψm,
      ho _ hmξ _ hmψ hne02, ho _ hmψ _ hmξ (Ne.symm hne02)]
    ring
  have hfR : cfInner f (∑ r ∈ R, r) = (n : ℂ) := by
    have h2 := hτiso C A
    rw [hτR A rfl] at h2
    rw [hfdef, h2, hAdef, hCdef]
    change cfInner (ξ - ψ) (ξ - star ξ) = _
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hξn,
      ho _ hmξ _ hmsξ hne01, ho _ hmψ _ hmξ (Ne.symm hne02),
      ho _ hmψ _ hmsξ (Ne.symm hne12)]
    ring
  have hfT : cfInner f (∑ t ∈ T, t) = -(m : ℂ) := by
    have h2 := hτiso C B
    rw [hτT B rfl] at h2
    rw [hfdef, h2, hBdef, hCdef]
    change cfInner (ξ - ψ) (ψ - star ψ) = _
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hψm,
      ho _ hmξ _ hmψ hne02, ho _ hmξ _ hmsψ hne03, ho _ hmψ _ hmsψ hne23]
    ring
  obtain ⟨R₀, hR₀, T₀, hT₀, hR₀card, hT₀card, hfeq⟩ :=
    exists_subsets_eq_sum_sub_sum_of_norm_eq_card_add_card hn hm hRT hRmem hTmem hON
      hRcard hTcard hfmem hfnorm hfR hfT
  set R₁ : Finset (G → ℂ) := R.filter (· ∉ R₀) with hR₁def
  set T₁ : Finset (G → ℂ) := T.filter (· ∉ T₀) with hT₁def
  have hR₁ : R₁ ⊆ R := Finset.filter_subset _ _
  have hT₁ : T₁ ⊆ T := Finset.filter_subset _ _
  have hR₁eq : R₁ = R \ R₀ := by rw [hR₁def, Finset.sdiff_eq_filter]
  have hT₁eq : T₁ = T \ T₀ := by rw [hT₁def, Finset.sdiff_eq_filter]
  have hR₁card : R₁.card = n := by
    rw [hR₁eq, Finset.card_sdiff_of_subset hR₀, hRcard, hR₀card]; omega
  have hT₁card : T₁.card = m := by
    rw [hT₁eq, Finset.card_sdiff_of_subset hT₀, hTcard, hT₀card]; omega
  have hsumR : ∑ r ∈ R₁, r + ∑ r ∈ R₀, r = ∑ r ∈ R, r := by
    rw [hR₁eq]; exact Finset.sum_sdiff hR₀
  have hsumT : ∑ t ∈ T₁, t + ∑ t ∈ T₀, t = ∑ t ∈ T, t := by
    rw [hT₁eq]; exact Finset.sum_sdiff hT₀
  set u : Fin 4 → (L → ℂ) := ![ξ, star ξ, ψ, star ψ] with hudef
  set P : Fin 4 → Finset (G → ℂ) := ![R₀, R₁, T₀, T₁] with hPdef
  set ε : Fin 4 → ℂ := ![1, -1, 1, -1] with hεdef
  set g : Fin 4 → ℂ := ![(n : ℂ), (n : ℂ), (m : ℂ), (m : ℂ)] with hgdef
  set v : Fin 4 → (G → ℂ) := fun i => ε i • ∑ x ∈ P i, x with hvdef
  have hSrange : S = Set.range u := by
    rw [hS, hudef]; simp [Matrix.range_cons, Matrix.range_empty]; aesop
  have hmemu : ∀ i, u i ∈ S := fun i => by rw [hSrange]; exact ⟨i, rfl⟩
  have hgramu : ∀ i j, cfInner (u i) (u j) = if i = j then g i else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      fin_cases i <;> simpa [hudef, hgdef] using ‹_›
    · rw [if_neg hij]
      exact ho _ (hmemu i) _ (hmemu j) fun h => hij (hinj h)
  have hgne : ∀ i, g i ≠ 0 := by
    intro i
    fin_cases i <;> simp only [hgdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
      exact Nat.cast_ne_zero.2 (by omega)
  have hPsub : ∀ i, P i ⊆ R ∪ T := by
    intro i
    fin_cases i <;> simp only [hPdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    · exact hR₀.trans hRsub
    · exact hR₁.trans hRsub
    · exact hT₀.trans hTsub
    · exact hT₁.trans hTsub
  have hPcard : ∀ i, ((P i).card : ℂ) = g i := by
    intro i
    fin_cases i <;> simp [hPdef, hgdef, hR₀card, hR₁card, hT₀card, hT₁card]
  have hPinter : ∀ i j, i ≠ j → P i ∩ P j = ∅ := by
    have eRT : ∀ X ⊆ R, ∀ Y ⊆ T, X ∩ Y = ∅ := fun X hX Y hY =>
      Finset.disjoint_iff_inter_eq_empty.1 (hRT.mono hX hY)
    have eTR : ∀ X ⊆ T, ∀ Y ⊆ R, X ∩ Y = ∅ := fun X hX Y hY =>
      Finset.disjoint_iff_inter_eq_empty.1 (hRT.symm.mono hX hY)
    have e01 : R₀ ∩ R₁ = ∅ := by
      rw [hR₁eq]; exact Finset.disjoint_iff_inter_eq_empty.1 Finset.disjoint_sdiff
    have e10 : R₁ ∩ R₀ = ∅ := by rw [Finset.inter_comm]; exact e01
    have e23 : T₀ ∩ T₁ = ∅ := by
      rw [hT₁eq]; exact Finset.disjoint_iff_inter_eq_empty.1 Finset.disjoint_sdiff
    have e32 : T₁ ∩ T₀ = ∅ := by rw [Finset.inter_comm]; exact e23
    have a00 : R₀ ∩ T₀ = ∅ := eRT _ hR₀ _ hT₀
    have a01 : R₀ ∩ T₁ = ∅ := eRT _ hR₀ _ hT₁
    have a10 : R₁ ∩ T₀ = ∅ := eRT _ hR₁ _ hT₀
    have a11 : R₁ ∩ T₁ = ∅ := eRT _ hR₁ _ hT₁
    have b00 : T₀ ∩ R₀ = ∅ := eTR _ hT₀ _ hR₀
    have b01 : T₀ ∩ R₁ = ∅ := eTR _ hT₀ _ hR₁
    have b10 : T₁ ∩ R₀ = ∅ := eTR _ hT₁ _ hR₀
    have b11 : T₁ ∩ R₁ = ∅ := eTR _ hT₁ _ hR₁
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [hPdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    · exact absurd rfl hij
    · exact e01
    · exact a00
    · exact a01
    · exact e10
    · exact absurd rfl hij
    · exact a10
    · exact a11
    · exact b00
    · exact b01
    · exact absurd rfl hij
    · exact e23
    · exact b10
    · exact b11
    · exact e32
    · exact absurd rfl hij
  have hgramv : ∀ i j, cfInner (v i) (v j) = if i = j then g i else 0 := by
    intro i j
    rw [hvdef]
    simp only
    rw [cfInner_smul_left, cfInner_smul_right, hin _ (hPsub i) _ (hPsub j)]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Finset.inter_self, hPcard i]
      fin_cases i <;> simp [hεdef]
    · rw [if_neg hij, hPinter i j hij]
      simp
  have hvmem : ∀ i, v i ∈ Submodule.span ℤ (Irr G) := by
    have hmem : ∀ X ⊆ R ∪ T, (∑ x ∈ X, x) ∈ Submodule.span ℤ (Irr G) := by
      intro X hX
      refine Submodule.sum_mem _ fun x hx => ?_
      rcases Finset.mem_union.1 (hX hx) with h | h
      · exact hRmem x h
      · exact hTmem x h
    intro i
    rw [hvdef]
    simp only
    have hε : ε i • (∑ x ∈ P i, x) = (if i = 0 ∨ i = 2 then (1 : ℤ) else -1) • ∑ x ∈ P i, x := by
      fin_cases i <;> simp [hεdef]
    rw [hε]
    exact Submodule.smul_mem _ _ (hmem _ (hPsub i))
  have hv0 : v 0 = ∑ r ∈ R₀, r := by rw [hvdef]; simp [hεdef, hPdef]
  have hv1 : v 1 = -∑ r ∈ R₁, r := by rw [hvdef]; simp [hεdef, hPdef]
  have hv2 : v 2 = ∑ t ∈ T₀, t := by rw [hvdef]; simp [hεdef, hPdef]
  have hv3 : v 3 = -∑ t ∈ T₁, t := by rw [hvdef]; simp [hεdef, hPdef]
  have hu0 : u 0 = ξ := by rw [hudef]; simp
  have hu1 : u 1 = star ξ := by rw [hudef]; simp
  have hu2 : u 2 = ψ := by rw [hudef]; simp
  have hu3 : u 3 = star ψ := by rw [hudef]; simp
  have hτcoord : ∀ w : charSpanZero S, ∀ c : Fin 4 → ℤ,
      ((w : L → ℂ)) = ∑ i, (c i : ℂ) • u i → ((τ w : G → ℂ)) = ∑ i, (c i : ℂ) • v i := by
    intro w c hcw
    have hsum0 : c 0 + c 1 + c 2 + c 3 = 0 := by
      have h1 : ((w : L → ℂ)) 1 = 0 := charSpanZero_apply_one w
      have h2 : (∑ i, (c i : ℂ) • u i) 1 = ((c 0 + c 1 + c 2 + c 3 : ℤ) : ℂ) * (d : ℂ) := by
        rw [Fin.sum_univ_four, hu0, hu1, hu2, hu3]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hdeg _ hmξ, hdeg _ hmsξ, hdeg _ hmψ, hdeg _ hmsψ]
        push_cast
        ring
      rw [hcw, h2] at h1
      have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
      exact_mod_cast (mul_eq_zero.1 h1).resolve_right hd'
    have hc2 : (c 2 : ℂ) = -(c 0 : ℂ) - (c 1 : ℂ) - (c 3 : ℂ) := by
      have h : ((c 0 + c 1 + c 2 + c 3 : ℤ) : ℂ) = 0 := by rw [hsum0]; simp
      push_cast at h
      linear_combination h
    have hwdec : w = (-c 1) • A + (-c 3) • B + (c 0 + c 1) • C := by
      refine Subtype.ext ?_
      have hcoe : (((-c 1) • A + (-c 3) • B + (c 0 + c 1) • C : charSpanZero S) : L → ℂ)
          = ((-c 1 : ℤ) : ℂ) • (ξ - star ξ) + ((-c 3 : ℤ) : ℂ) • (ψ - star ψ)
            + ((c 0 + c 1 : ℤ) : ℂ) • (ξ - ψ) := by
        simp only [AddSubmonoid.coe_add, Submodule.coe_add, SetLike.val_smul, hAdef, hBdef,
          hCdef, Int.cast_smul_eq_zsmul]
      rw [hcoe, hcw, Fin.sum_univ_four, hu0, hu1, hu2, hu3]
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [hc2]
      ring
    have hτCf : (τ C : G → ℂ) = ∑ r ∈ R₀, r - ∑ t ∈ T₀, t := hfeq
    rw [hwdec, map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    simp only [AddSubmonoid.coe_add, Submodule.coe_add, SetLike.val_smul,
      ← Int.cast_smul_eq_zsmul ℂ, hτR A rfl, hτT B rfl, hτCf]
    rw [Fin.sum_univ_four, hv0, hv1, hv2, hv3, ← hsumR, ← hsumT]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hc2]
    ring
  obtain ⟨ν, hν, hνu⟩ :=
    exists_isCoherentWith_of_gram_eq hSrange hgramu hgne hvmem hgramv hτcoord
  refine ⟨hRcard, hTcard, R₀, hR₀, T₀, hT₀, hR₀card, hT₀card, ν, hν, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hνu 0 w (hu0 ▸ hw), hv0]
  · intro w hw
    rw [hνu 1 w (hu1 ▸ hw), hv1, hR₁def]
  · intro w hw
    rw [hνu 2 w (hu2 ▸ hw), hv2]
  · intro w hw
    rw [hνu 3 w (hu3 ▸ hw), hv3, hT₁def]

theorem isCoherent_of_four_member_mixed_norm
    {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
    {ξ ψ : L → ℂ} (hξL : ξ ∈ Submodule.span ℤ (Irr L)) (hψL : ψ ∈ Submodule.span ℤ (Irr L))
    {S : Set (L → ℂ)} (hS : S = {ξ, star ξ, ψ, star ψ})
    (hinj : Function.Injective ![ξ, star ξ, ψ, star ψ])
    (horth : ∀ f ∈ S, ∀ h ∈ S, f ≠ h → IsOrthogonal f h)
    {d : ℝ} (hd : 0 < d) (hdeg : ∀ f ∈ S, f 1 = (d : ℂ))
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hξn : cfInner ξ ξ = (n : ℂ)) (hψm : cfInner ψ ψ = (m : ℂ))
    {τ : charSpanZero S →+ Submodule.span ℤ (Irr G)}
    (hτiso : ∀ w w' : charSpanZero S,
      cfInner ((τ w : G → ℂ)) ((τ w' : G → ℂ)) = cfInner ((w : L → ℂ)) ((w' : L → ℂ)))
    {R T : Finset (G → ℂ)} (hRT : Disjoint R T)
    (hRmem : ∀ r ∈ R, r ∈ Submodule.span ℤ (Irr G))
    (hTmem : ∀ t ∈ T, t ∈ Submodule.span ℤ (Irr G))
    (hON : IsOrthonormalFamily fun w : {x // x ∈ R ∪ T} => (w : G → ℂ))
    (hτR : ∀ w : charSpanZero S, (w : L → ℂ) = ξ - star ξ → (τ w : G → ℂ) = ∑ r ∈ R, r)
    (hτT : ∀ w : charSpanZero S, (w : L → ℂ) = ψ - star ψ → (τ w : G → ℂ) = ∑ t ∈ T, t) :
    IsCoherent S ((spanIrrToVirtualChars G).comp τ) := by
  obtain ⟨-, -, R₀, -, T₀, -, -, -, ν, hν, -⟩ :=
    exists_isCoherentWith_of_four_member_mixed_norm hξL hψL hS hinj horth hd hdeg hn hm hξn hψm
      hτiso hRT hRmem hTmem hON hτR hτT
  exact hν.isCoherent

end

end CFSG.FeitThompson
