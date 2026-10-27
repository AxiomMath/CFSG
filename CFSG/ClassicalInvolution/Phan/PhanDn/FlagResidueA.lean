module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidue
public import CFSG.ClassicalInvolution.Phan.Geometry.NondegComplex
public import CFSG.ClassicalInvolution.Phan.PhanDn.SolidResidue
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K} {m : ℕ}

@[expose] def coordBlock (d : ℕ) (K : Type) [Field K] (a c : ℕ) : Submodule K (Fin d → K) :=
  Submodule.pi {i | ¬ (a ≤ (i : ℕ) ∧ (i : ℕ) < c)} fun _ => ⊥

theorem coordBlock_mem {d a c : ℕ} {x : Fin d → K} :
    x ∈ coordBlock d K a c ↔
      ∀ i : Fin d, ¬ (a ≤ (i : ℕ) ∧ (i : ℕ) < c) → x i = 0 := by
  rw [coordBlock, Submodule.mem_pi]
  simp only [Set.mem_setOf_eq, Submodule.mem_bot]

theorem coordBlock_mono {d a c a' c' : ℕ} (ha : a' ≤ a) (hc : c ≤ c') :
    coordBlock d K a c ≤ coordBlock d K a' c' := by
  intro x hx
  rw [coordBlock_mem] at hx ⊢
  intro i hi
  exact hx i (by omega)

theorem coordBlock_top (d : ℕ) : coordBlock d K 0 d = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [coordBlock_mem]
  intro i hi
  exact absurd ⟨Nat.zero_le _, i.isLt⟩ hi

theorem coordBlock_single_mem {d a c : ℕ} {i : Fin d} :
    Pi.single i (1 : K) ∈ coordBlock d K a c ↔ a ≤ (i : ℕ) ∧ (i : ℕ) < c := by
  rw [coordBlock_mem]
  constructor
  · intro h
    by_contra hcon
    have h1 := h i hcon
    simp only [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  · intro hi j hj
    exact Pi.single_eq_of_ne (by rintro rfl; exact hj hi) _

theorem coordBlock_sup {d a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    coordBlock d K a b ⊔ coordBlock d K b c = coordBlock d K a c := by
  refine le_antisymm (sup_le (coordBlock_mono le_rfl hbc) (coordBlock_mono hab le_rfl)) ?_
  intro x hx
  rw [coordBlock_mem] at hx
  have hsplit : x = (fun i : Fin d => if (i : ℕ) < b then x i else 0) +
      (fun i : Fin d => if b ≤ (i : ℕ) then x i else 0) := by
    funext i
    by_cases h : (i : ℕ) < b
    · simp [h, not_le_of_gt h]
    · have hb : b ≤ (i : ℕ) := by omega
      simp [h, hb]
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [coordBlock_mem]
    intro i hi
    by_cases h : (i : ℕ) < b
    · rw [if_pos h]
      exact hx i (by omega)
    · rw [if_neg h]
  · rw [coordBlock_mem]
    intro i hi
    by_cases h : b ≤ (i : ℕ)
    · rw [if_pos h]
      exact hx i (by omega)
    · rw [if_neg h]

theorem coordBlock_inf_eq_bot {d a b c e : ℕ} (h : b ≤ c) :
    coordBlock d K a b ⊓ coordBlock d K c e = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  rw [coordBlock_mem] at hx1 hx2
  funext i
  by_cases hi : (i : ℕ) < b
  · exact hx2 i (by omega)
  · exact hx1 i (by omega)

theorem coordBlock_orth {d a b c e : ℕ} (h : b ≤ c) :
    Orth σ (coordBlock d K a b) (coordBlock d K c e) := by
  intro u hu v hv
  rw [herm]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : (i : ℕ) < b
  · rw [coordBlock_mem] at hv
    rw [hv i (by omega), mul_zero]
  · rw [coordBlock_mem] at hu
    rw [hu i (by omega), map_zero, zero_mul]

theorem coordBlock_nondeg {d a c : ℕ} :
    Nondeg σ (coordBlock d K a c) := by
  intro u hu hper
  rw [coordBlock_mem] at hu
  funext i
  by_cases hi : a ≤ (i : ℕ) ∧ (i : ℕ) < c
  · have hmem : Pi.single i (1 : K) ∈ coordBlock d K a c :=
      coordBlock_single_mem.mpr hi
    have h := hper (Pi.single i (1 : K)) hmem
    rw [herm_single_right] at h
    exact (map_eq_zero_iff σ σ.injective).mp (by simpa using h)
  · exact hu i hi

noncomputable def aResPhi (d : ℕ) : (Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K) :=
  { toFun := fun x => ∑ i, x i • stdE (K := K) (n := d) i
    map_add' := by
      intro x y
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]
    map_smul' := by
      intro c x
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply] }

theorem aResPhi_apply_inl (d : ℕ) (x : Fin d → K) (j : Fin d) :
    aResPhi (K := K) d x (.inl j) = x j := by
  change (∑ i, x i • stdE (K := K) (n := d) i) (.inl j) = x j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [stdE]
  · intro k _ hk
    simp [stdE, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem aResPhi_apply_inr (d : ℕ) (x : Fin d → K) (j : Fin d) :
    aResPhi (K := K) d x (.inr j) = 0 := by
  change (∑ i, x i • stdE (K := K) (n := d) i) (.inr j) = 0
  rw [Finset.sum_apply]
  simp [stdE]

theorem aResPhi_single (d : ℕ) (i : Fin d) :
    aResPhi (K := K) d (Pi.single i (1 : K)) = stdE (K := K) (n := d) i := by
  ext x
  cases x with
  | inl j =>
    rw [aResPhi_apply_inl, stdE, Pi.single_apply, Pi.single_apply]
    simp only [Sum.inl.injEq]
  | inr j => simp [aResPhi_apply_inr]

theorem aResPhi_injective (d : ℕ) : Function.Injective (aResPhi (K := K) d) := by
  intro x y h
  funext j
  have := congrFun h (.inl j)
  rwa [aResPhi_apply_inl, aResPhi_apply_inl] at this

theorem aResPhi_range (d : ℕ) : LinearMap.range (aResPhi (K := K) d) = stdLag d K := by
  rw [stdLag_eq_span_stdE]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    change (∑ i, x i • stdE (K := K) (n := d) i) ∈
      Submodule.span K (Set.range (stdE (K := K) (n := d)))
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (1 : K), ?_⟩
    exact aResPhi_single d i

theorem aResPhi_flipHerm (d : ℕ) (x y : Fin d → K) :
    flipHerm σ (aResPhi (K := K) d x) (aResPhi (K := K) d y) = herm σ y x := by
  rw [flipHerm_apply]
  calc ∑ i, ((aResPhi (K := K) d x) (.inl i) * σ ((aResPhi (K := K) d y) (.inl i)) +
        (aResPhi (K := K) d x) (.inr i) * σ ((aResPhi (K := K) d y) (.inr i)))
      = ∑ i, x i * σ (y i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [aResPhi_apply_inl, aResPhi_apply_inl, aResPhi_apply_inr, aResPhi_apply_inr,
          map_zero, mul_zero, add_zero]
    _ = ∑ i, σ (y i) * x i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = herm σ y x := rfl

theorem aResPhi_coordBlock (d a c : ℕ) :
    (coordBlock d K a c).map (aResPhi (K := K) d) =
      Submodule.span K (stdE (K := K) (n := d) '' {i : Fin d | a ≤ (i : ℕ) ∧ (i : ℕ) < c}) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    change x ∈ coordBlock d K a c at hx
    rw [coordBlock_mem] at hx
    change (∑ i, x i • stdE (K := K) (n := d) i) ∈
      Submodule.span K (stdE (K := K) (n := d) '' {i : Fin d | a ≤ (i : ℕ) ∧ (i : ℕ) < c})
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : a ≤ (i : ℕ) ∧ (i : ℕ) < c
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hx i hi, zero_smul]
      exact Submodule.zero_mem _
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    refine Submodule.mem_map.mpr ⟨Pi.single i (1 : K), coordBlock_single_mem.mpr hi, ?_⟩
    exact aResPhi_single d i

theorem aRes_stdSub_eq_span (d j : ℕ) :
    (stdDChamber σ d).toFlipFrame.sub j =
      Submodule.span K (stdE (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j}) := by
  refine le_antisymm ?_ ?_
  · unfold FlipFrame.sub FlipFrame.spanAt
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_filter] at hi
    change (stdDChamber σ d).toFlipFrame.line i ≤ _
    rw [show (stdDChamber σ d).toFlipFrame.line i = K ∙ stdE (K := K) (n := d) i from rfl]
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨i, hi.2, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    unfold FlipFrame.sub FlipFrame.spanAt
    refine Finset.le_sup (f := fun l => (stdDChamber σ d).toFlipFrame.line l)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) ?_
    rw [stdDChamber_line]
    exact Submodule.mem_span_singleton_self _

theorem aRes_sup_inf_eq {d : ℕ} {A B S : Submodule K (Fin d → K)} (hS : S ≤ B)
    (hAB : A ⊓ B = ⊥) : (A ⊔ S) ⊓ B = S := by
  rw [sup_comm A S, sup_inf_assoc_of_le A hS, hAB, sup_bot_eq]

theorem aRes_inf_sup_eq {d : ℕ} {A B H : Submodule K (Fin d → K)} (hA : A ≤ H)
    (hH : H ≤ A ⊔ B) : A ⊔ (H ⊓ B) = H := by
  have h := inf_sup_assoc_of_le (x := H) B hA
  rw [sup_comm B A, inf_eq_left.2 hH, sup_comm (H ⊓ B) A] at h
  exact h

theorem aRes_sup_le_sup_iff {d : ℕ} {A B S T : Submodule K (Fin d → K)} (hS : S ≤ B)
    (hT : T ≤ B) (hAB : A ⊓ B = ⊥) : A ⊔ S ≤ A ⊔ T ↔ S ≤ T := by
  constructor
  · intro h x hx
    have h1 : x ∈ (A ⊔ S) ⊓ B := Submodule.mem_inf.mpr ⟨Submodule.mem_sup_right hx, hS hx⟩
    have h2 : (A ⊔ S) ⊓ B ≤ (A ⊔ T) ⊓ B := inf_le_inf_right _ h
    rw [aRes_sup_inf_eq hS hAB] at h1 h2
    rw [aRes_sup_inf_eq hT hAB] at h2
    exact h2 h1
  · intro h
    exact sup_le_sup_left h A

theorem aRes_sup_lt_sup_iff {d : ℕ} {A B S T : Submodule K (Fin d → K)} (hS : S ≤ B)
    (hT : T ≤ B) (hAB : A ⊓ B = ⊥) : A ⊔ S < A ⊔ T ↔ S < T := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(aRes_sup_le_sup_iff hS hT hAB).1 h1, ?_⟩
    intro hEq
    exact h2 (by rw [hEq])
  · rintro ⟨h1, h2⟩
    refine ⟨sup_le_sup_left h1 A, ?_⟩
    intro hEq
    have hTS : T ≤ S := (aRes_sup_le_sup_iff hT hS hAB).1 (le_of_eq hEq.symm)
    exact h2 (le_antisymm h1 hTS)

theorem aRes_nondeg_sup_iff (hσ : ∀ x, σ (σ x) = x) {d : ℕ}
    {A B S : Submodule K (Fin d → K)} (hAB : Orth σ A B) (hA : Nondeg σ A) (hS : S ≤ B) :
    Nondeg σ (A ⊔ S) ↔ Nondeg σ S := by
  constructor
  · intro h x hx hxorth
    refine h x (Submodule.mem_sup_right hx) fun t ht => ?_
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.mp ht
    rw [herm_add_right,
      herm_eq_zero_comm σ hσ (hAB a ha x (hS hx)), hxorth s hs, add_zero]
  · intro h x hx hxorth
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have ha0 : a = 0 := by
      refine hA a ha fun t ht => ?_
      have h1 := hxorth t (Submodule.mem_sup_left ht)
      rw [herm_add_left, herm_eq_zero_comm σ hσ (hAB t ht s (hS hs)), add_zero] at h1
      exact h1
    have hs0 : s = 0 := by
      refine h s hs fun t ht => ?_
      have h1 := hxorth t (Submodule.mem_sup_right ht)
      rw [herm_add_left, hAB a ha t (hS ht), zero_add] at h1
      exact h1
    rw [ha0, hs0, add_zero]

theorem aRes_flagTyp_of_finrank_lt {U : FlagVert σ m}
    (h : Module.finrank K U.1 < m + 1) : (flagTyp U : ℕ) = Module.finrank K U.1 - 1 := by
  have hmin : min (Module.finrank K U.1 - 1) m = Module.finrank K U.1 - 1 :=
    min_eq_left (by omega)
  simp only [flagTyp, if_neg (ne_of_lt h), Fin.val_mk, hmin]

theorem aRes_stdSub_mono (d : ℕ) {i j : ℕ} (h : i ≤ j) :
    (stdDChamber σ d).toFlipFrame.sub i ≤ (stdDChamber σ d).toFlipFrame.sub j := by
  rw [aRes_stdSub_eq_span, aRes_stdSub_eq_span]
  exact Submodule.span_mono (Set.image_mono fun k hk => lt_of_lt_of_le hk h)

theorem aRes_stdSub_zero (d : ℕ) :
    (stdDChamber σ d).toFlipFrame.sub 0 = ⊥ := by
  rw [aRes_stdSub_eq_span]
  simp

theorem aRes_stdSub_finrank (d : ℕ) {j : ℕ} (hj : j ≤ d) :
    Module.finrank K ((stdDChamber σ d).toFlipFrame.sub j) = j :=
  FlipFrame.finrank_sub _ hj

theorem aRes_stdSub_le_stdLag (d j : ℕ) :
    (stdDChamber σ d).toFlipFrame.sub j ≤ stdLag d K := by
  rw [aRes_stdSub_eq_span, stdLag_eq_span_stdE]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, -, rfl⟩
  exact Set.mem_range_self i

theorem aResPhi_stdSub (d j : ℕ) (_hj : j ≤ d) :
    (coordBlock d K 0 j).map (aResPhi (K := K) d) =
      (stdDChamber σ d).toFlipFrame.sub j := by
  rw [aResPhi_coordBlock, aRes_stdSub_eq_span]
  congr 1
  ext v
  constructor
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, ⟨Nat.zero_le _, hi⟩, rfl⟩

theorem aRes_finrank_stdE_span (d j : ℕ) (hj : j ≤ d) :
    Module.finrank K (Submodule.span K
      (stdE (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j})) = j := by
  have hli : LinearIndependent K
      (fun i : {i : Fin d // (i : ℕ) < j} => stdE (K := K) (n := d) i.1) :=
    (Pi.linearIndependent_single_one (Fin d ⊕ Fin d) K).comp
      (fun i : {i : Fin d // (i : ℕ) < j} => Sum.inl i.1)
      (fun a b hab => Subtype.ext (by simpa using hab))
  have hspan : Submodule.span K (Set.range
      (fun i : {i : Fin d // (i : ℕ) < j} => stdE (K := K) (n := d) i.1)) =
      Submodule.span K (stdE (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j}) := by
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hspan, finrank_span_eq_card hli]
  exact Fintype.card_fin_lt_of_le hj

theorem aResPhi_coordBlock_zero (d j : ℕ) :
    (coordBlock d K 0 j).map (aResPhi (K := K) d) =
      Submodule.span K (stdE (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j}) := by
  rw [aResPhi_coordBlock]
  congr 1
  ext v
  constructor
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, ⟨Nat.zero_le _, hi⟩, rfl⟩

theorem aRes_finrank_map (d : ℕ) (p : Submodule K (Fin d → K)) :
    Module.finrank K ↥(p.map (aResPhi (K := K) d)) = Module.finrank K p := by
  let f : p →ₗ[K] (Fin d ⊕ Fin d → K) :=
    { toFun := fun x => aResPhi (K := K) d x.1
      map_add' := by intro x y; simp
      map_smul' := by intro a x; simp }
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (aResPhi_injective d h)
  have hrange : LinearMap.range f = p.map (aResPhi (K := K) d) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have h := LinearMap.finrank_range_of_inj hinj
  rwa [hrange] at h

theorem aRes_finrank_coordBlock_zero (d j : ℕ) (hj : j ≤ d) :
    Module.finrank K (coordBlock d K 0 j) = j := by
  rw [← aRes_finrank_map d (coordBlock d K 0 j),
    aResPhi_coordBlock_zero (K := K) d j, aRes_finrank_stdE_span (K := K) d j hj]

theorem aRes_finrank_coordBlock (d a c : ℕ) (hac : a ≤ c) (hcd : c ≤ d) :
    Module.finrank K (coordBlock d K a c) = c - a := by
  have hsup : coordBlock d K 0 a ⊔ coordBlock d K a c = coordBlock d K 0 c :=
    coordBlock_sup (Nat.zero_le a) hac
  have hbot : coordBlock d K 0 a ⊓ coordBlock d K a c = ⊥ :=
    coordBlock_inf_eq_bot (le_refl a)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (coordBlock d K 0 a)
    (coordBlock d K a c)
  rw [hsup, hbot, finrank_bot, aRes_finrank_coordBlock_zero d a (by omega),
    aRes_finrank_coordBlock_zero d c hcd] at h
  omega

theorem aRes_isFlipflopSub_stdLag (hσ : ∀ x, σ (σ x) = x) (d : ℕ) :
    IsFlipflopSub σ (stdLag d K) := by
  rw [← stdDChamber_spanAt_univ σ d]
  exact (stdDChamber σ d).toFlipFrame.isFlipflopSub_spanAt hσ Finset.univ

theorem aRes_isSolid_alt (hσ : ∀ x, σ (σ x) = x) :
    IsSolid σ ((stdDChamber σ (m + 1)).toFlipFrame.alt) :=
  ⟨FlipFrame.isFlipflopSub_alt hσ _, FlipFrame.finrank_alt hσ _⟩

@[expose] noncomputable def aResStemFwd (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b)
    (hbm : b + 2 ≤ m)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}) :
    NdVert σ (coordBlock (m + 1) K a (b + 2)) := by
  classical
  have hσ := E.isUnitary.invol
  set A := coordBlock (m + 1) K 0 a with hA
  set B := coordBlock (m + 1) K a (b + 2) with hB
  set C := coordBlock (m + 1) K 0 (b + 2) with hC
  set L := stdLag (m + 1) K with hL
  set X := x.1.1 with hX
  set H := Submodule.comap (aResPhi (K := K) (m + 1)) X with hH
  have ht : a ≤ (flagTyp x.1 : ℕ) ∧ (flagTyp x.1 : ℕ) ≤ b := by
    have h := x.2.1
    simpa only [Set.mem_setOf_eq, not_not] using h
  have hxdim : Module.finrank K X = (flagTyp x.1 : ℕ) + 1 := by
    rw [hX]
    exact FlagVert.finrank_eq_of_flagTyp (by omega)
  have hxL : X < L := by
    have hmJ : (Fin.last m) ∈ {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
      simp only [Set.mem_setOf_eq, Fin.val_last]
      omega
    have hadj := x.2.2 (Fin.last m) hmJ
    have hdL : Module.finrank K (flagChamber E m (Fin.last m)).1 = m + 1 := by
      rw [finrank_flagChamber]
      simp
    have hlt : Module.finrank K x.1.1 <
        Module.finrank K (flagChamber E m (Fin.last m)).1 := by
      rw [← hX, hxdim, hdL]
      omega
    have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hadj
    rw [coe_flagChamber_last E, ← hL] at h
    exact h
  have hHX : H.map (aResPhi (K := K) (m + 1)) = X := by
    rw [hH, Submodule.map_comap_eq, aResPhi_range, inf_eq_right.2 hxL.le]
  have hTaX : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ X := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, aRes_stdSub_zero]
      exact bot_le
    · have haJ : (⟨a - 1, by omega⟩ : Fin (m + 1)) ∈
          {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
        simp only [Set.mem_setOf_eq]
        omega
      have hadj := x.2.2 ⟨a - 1, by omega⟩ haJ
      have hch : (flagChamber E m ⟨a - 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.sub a := by
        rw [coe_flagChamber_of_lt E (i := ⟨a - 1, by omega⟩) (by dsimp only; omega)]
        congr 1
        rw [Fin.val_mk, Nat.sub_add_cancel hapos]
      have hdimTa : Module.finrank K ((stdDChamber σ (m + 1)).toFlipFrame.sub a) = a :=
        aRes_stdSub_finrank (m + 1) (by omega)
      have hlt : Module.finrank K (flagChamber E m ⟨a - 1, by omega⟩).1 <
          Module.finrank K x.1.1 := by
        rw [hch, hdimTa, ← hX, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hadj.symm
      rw [hch] at h
      exact h.le
  have hTaX_lt : (stdDChamber σ (m + 1)).toFlipFrame.sub a < X := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, aRes_stdSub_zero]
      exact bot_lt_iff_ne_bot.mpr x.1.2.2.1
    ·
      have haJ : (⟨a - 1, by omega⟩ : Fin (m + 1)) ∈
          {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
        simp only [Set.mem_setOf_eq]
        omega
      have hadj := x.2.2 ⟨a - 1, by omega⟩ haJ
      have hch : (flagChamber E m ⟨a - 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.sub a := by
        rw [coe_flagChamber_of_lt E (i := ⟨a - 1, by omega⟩) (by dsimp only; omega)]
        congr 1
        rw [Fin.val_mk, Nat.sub_add_cancel hapos]
      have hdimTa : Module.finrank K ((stdDChamber σ (m + 1)).toFlipFrame.sub a) = a :=
        aRes_stdSub_finrank (m + 1) (by omega)
      have hlt : Module.finrank K (flagChamber E m ⟨a - 1, by omega⟩).1 <
          Module.finrank K x.1.1 := by
        rw [hch, hdimTa, ← hX, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hadj.symm
      rw [hch] at h
      exact h
  have hdimTb : Module.finrank K
      ((stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2)) = b + 2 :=
    aRes_stdSub_finrank (m + 1) (by omega)
  have hXTb : X < (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
    by_cases hlt : b + 2 < m
    · have hadj := x.2.2 ⟨b + 1, by omega⟩ (by
          simp only [Set.mem_setOf_eq]
          omega)
      have hch : (flagChamber E m ⟨b + 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
        rw [coe_flagChamber_of_lt E (i := ⟨b + 1, by omega⟩)
          (by dsimp only; omega)]
      have hlx : Module.finrank K x.1.1 <
          Module.finrank K (flagChamber E m ⟨b + 1, by omega⟩).1 := by
        rw [hch, hdimTb, ← hX, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlx).1 hadj
      rw [hch] at h
      exact h
    · have hb_eq : b + 2 = m := by omega
      have hadjAlt := x.2.2 ⟨b + 1, by omega⟩ (by
          simp only [Set.mem_setOf_eq]
          omega)
      have hb2 : (⟨b + 1, by omega⟩ : Fin (m + 1)) = ⟨m - 1, by omega⟩ := by
        apply Fin.ext
        simp only
        omega
      have hAlt : (flagChamber E m ⟨b + 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.alt := by
        rw [hb2]
        exact coe_flagChamber_of_succ_eq E (by dsimp only; omega)
      have hdimAlt : Module.finrank K
          ((stdDChamber σ (m + 1)).toFlipFrame.alt) = m + 1 :=
        FlipFrame.finrank_alt hσ _
      have hlx : Module.finrank K x.1.1 <
          Module.finrank K (flagChamber E m ⟨b + 1, by omega⟩).1 := by
        rw [hAlt, hdimAlt, ← hX, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlx).1 hadjAlt
      rw [hAlt] at h
      have hle : X ≤ (stdDChamber σ (m + 1)).toFlipFrame.alt ⊓ L :=
        le_inf h.le hxL.le
      have hinf : (stdDChamber σ (m + 1)).toFlipFrame.alt ⊓ stdLag (m + 1) K =
          (stdDChamber σ (m + 1)).toFlipFrame.sub m := by
        have h := FlipFrame.alt_inf_spanAt_univ
          (c := (stdDChamber σ (m + 1)).toFlipFrame) hσ
        rw [← stdDChamber_spanAt_univ σ (m + 1)]
        exact h
      rw [hL, hinf] at hle
      rw [lt_iff_le_and_ne]
      refine ⟨by rw [hb_eq]; exact hle, ?_⟩
      intro hEq
      have := congrArg (fun U : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) =>
        Module.finrank K U) hEq
      rw [hdimTb, hxdim, hb_eq] at this
      omega
  have hH_le_C : H ≤ C := by
    have hmap : H.map (aResPhi (K := K) (m + 1)) ≤
        (coordBlock (m + 1) K 0 (b + 2)).map (aResPhi (K := K) (m + 1)) := by
      rw [hHX, aResPhi_stdSub (m + 1) (b + 2) (by omega)]
      exact hXTb.le
    exact (Submodule.map_le_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := H) (q := C)).1 hmap
  have hA_le_H : A ≤ H := by
    have hmap : (coordBlock (m + 1) K 0 a).map (aResPhi (K := K) (m + 1)) ≤
        H.map (aResPhi (K := K) (m + 1)) := by
      rw [hHX, aResPhi_stdSub (m + 1) a (by omega)]
      exact hTaX
    exact (Submodule.map_le_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := A) (q := H)).1 hmap
  have hA_lt_H : A < H := by
    have hmap : (coordBlock (m + 1) K 0 a).map (aResPhi (K := K) (m + 1)) <
        H.map (aResPhi (K := K) (m + 1)) := by
      rw [hHX, aResPhi_stdSub (m + 1) a (by omega)]
      exact hTaX_lt
    exact (Submodule.map_lt_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := A) (q := H)).1 hmap
  have hC_eq : C = A ⊔ B := by
    rw [hC, hA]
    exact (coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := b + 2)
      (Nat.zero_le a) (by omega)).symm
  have hH_le_AB : H ≤ A ⊔ B := hC_eq ▸ hH_le_C
  have hAB : Orth σ A B := coordBlock_orth (le_refl a)
  have hbot : A ⊓ B = ⊥ := coordBlock_inf_eq_bot (le_refl a)
  have hAnd : Nondeg σ A := coordBlock_nondeg
  have hHnd : Nondeg σ H := by
    have hsolid : IsSolid σ (stdLag (m + 1) K) :=
      ⟨aRes_isFlipflopSub_stdLag hσ (m + 1), finrank_stdLag (m + 1) K⟩
    have hiff := nondeg_iff_isFlipflopSub_map (n := m + 1) hσ hsolid
      (aResPhi_injective (m + 1)) (aResPhi_range (m + 1))
      (fun x y => aResPhi_flipHerm (m + 1) x y) (W := H)
    refine hiff.2 ?_
    rw [hHX]
    exact x.1.2.1
  have hH_eq : H = A ⊔ H ⊓ B := (aRes_inf_sup_eq hA_le_H hH_le_AB).symm
  refine ⟨H ⊓ B, inf_le_right, ?_, ?_, ?_⟩
  · intro hbot'
    have hH_eq_A : H = A := by
      rw [hH_eq, hbot', sup_bot_eq]
    exact hA_lt_H.ne' hH_eq_A
  · intro hBeq
    have hH_eq_C : H = C := by
      rw [hH_eq, hBeq, hC_eq]
    have hXe : X = (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
      calc X = H.map (aResPhi (K := K) (m + 1)) := hHX.symm
        _ = C.map (aResPhi (K := K) (m + 1)) := by rw [hH_eq_C]
        _ = (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) :=
            aResPhi_stdSub (m + 1) (b + 2) (by omega)
    exact hXTb.ne hXe
  · have := (aRes_nondeg_sup_iff hσ hAB hAnd (S := H ⊓ B) inf_le_right).1
      (hH_eq ▸ hHnd)
    exact this

@[expose] noncomputable def aResStemBwd (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b)
    (hbm : b + 2 ≤ m)
    (y : NdVert σ (coordBlock (m + 1) K a (b + 2))) :
    residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
  classical
  have hσ := E.isUnitary.invol
  set S := y.1 with hS
  set A := coordBlock (m + 1) K 0 a with hA
  let B : Submodule K (Fin (m + 1) → K) := coordBlock (m + 1) K a (b + 2)
  set C := coordBlock (m + 1) K 0 (b + 2) with hC
  set L := stdLag (m + 1) K with hL
  set H := A ⊔ S with hH
  set X := H.map (aResPhi (K := K) (m + 1)) with hX
  have hS_le_B : S ≤ B := y.2.1
  have hS_ne_bot : S ≠ ⊥ := y.2.2.1
  have hS_ne_B : S ≠ B := y.2.2.2.1
  have hS_nd : Nondeg σ S := y.2.2.2.2
  have hA_le_H : A ≤ H := by rw [hH]; exact le_sup_left
  have hC_eq : C = A ⊔ B := by
    rw [hC, hA]
    exact (coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := b + 2)
      (Nat.zero_le a) (by omega)).symm
  have hH_le_C : H ≤ C := by
    rw [hH, hC_eq]
    exact sup_le le_sup_left (le_trans hS_le_B le_sup_right)
  have hASbot : A ⊓ S = ⊥ := by
    have h := inf_le_inf (le_refl A) hS_le_B
    rw [show A ⊓ B = ⊥ from coordBlock_inf_eq_bot (le_refl a)] at h
    exact le_bot_iff.mp h
  have hABorth : Orth σ A B := coordBlock_orth (le_refl a)
  have hAnd : Nondeg σ A := coordBlock_nondeg
  have hHnd : Nondeg σ H := by
    rw [hH]
    exact (aRes_nondeg_sup_iff hσ hABorth hAnd hS_le_B).2 hS_nd
  have hXflip : IsFlipflopSub σ X := by
    have hsolid : IsSolid σ (stdLag (m + 1) K) :=
      ⟨aRes_isFlipflopSub_stdLag hσ (m + 1), finrank_stdLag (m + 1) K⟩
    have hiff := nondeg_iff_isFlipflopSub_map (n := m + 1) hσ hsolid
      (aResPhi_injective (m + 1)) (aResPhi_range (m + 1))
      (fun x y => aResPhi_flipHerm (m + 1) x y) (W := H)
    rw [hX]
    exact hiff.1 hHnd
  have hAdim : Module.finrank K A = a := by
    rw [hA]
    exact aRes_finrank_coordBlock_zero (m + 1) a (by omega)
  have hBdim : Module.finrank K B = b + 2 - a :=
    aRes_finrank_coordBlock (m + 1) a (b + 2) (by omega) (by omega)
  have hSdimpos : 1 ≤ Module.finrank K S := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hS_ne_bot (Submodule.finrank_eq_zero.1 h0)
  have hSltB : Module.finrank K S < Module.finrank K B :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hS_le_B hS_ne_B)
  have hHdim : Module.finrank K H = a + Module.finrank K S := by
    rw [hH]
    have h := Submodule.finrank_sup_add_finrank_inf_eq A S
    rw [hASbot, finrank_bot, add_zero, hAdim] at h
    omega
  have hXdim : Module.finrank K X = a + Module.finrank K S := by
    rw [hX, aRes_finrank_map, hHdim]
  have hXltm : Module.finrank K X < m := by
    rw [hXdim]
    omega
  have hfin_congr : ∀ {U V : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}, U = V →
      Module.finrank K U = Module.finrank K V := by
    intro U V h
    rw [h]
  have hTa_le_X : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ X := by
    rw [hX, ← aResPhi_stdSub (σ := σ) (m + 1) a (by omega), ← hA]
    exact Submodule.map_mono hA_le_H
  have hTaX : (stdDChamber σ (m + 1)).toFlipFrame.sub a < X := by
    refine lt_of_le_of_ne hTa_le_X ?_
    intro heq
    have h1 := hfin_congr heq
    rw [aRes_stdSub_finrank (σ := σ) (m + 1) (by omega), hXdim] at h1
    omega
  have hX_ne_bot : X ≠ ⊥ := by
    intro h
    rw [h] at hTaX
    exact absurd hTaX (not_lt_of_ge bot_le)
  have hX_le_Tb : X ≤ (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
    rw [hX, ← aResPhi_stdSub (σ := σ) (m + 1) (b + 2) (by omega), ← hC]
    exact Submodule.map_mono hH_le_C
  have hTb_le_L : (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) ≤ L := by
    rw [hL]
    exact aRes_stdSub_le_stdLag (σ := σ) (m + 1) (b + 2)
  have hXTb : X < (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
    refine lt_of_le_of_ne hX_le_Tb ?_
    intro heq
    have h1 := hfin_congr heq
    rw [aRes_stdSub_finrank (σ := σ) (m + 1) (by omega), hXdim] at h1
    omega
  have hXltL : X < L := lt_of_lt_of_le hXTb hTb_le_L
  let Xv : FlagVert σ m := ⟨X, hXflip, hX_ne_bot, by rw [hXdim]; omega⟩
  have htyp : (flagTyp Xv : ℕ) = a + Module.finrank K S - 1 := by
    have hlt : Module.finrank K Xv.1 < m + 1 := by
      change Module.finrank K X < m + 1
      omega
    have h := aRes_flagTyp_of_finrank_lt (σ := σ) (U := Xv) hlt
    rwa [hXdim] at h
  have hdimS_le : Module.finrank K S ≤ b + 1 - a := by omega
  have hdimS_le' : a + Module.finrank K S ≤ b + 1 := by
    have h := Nat.add_le_add_left hdimS_le a
    rwa [Nat.add_sub_cancel' (by omega : a ≤ b + 1)] at h
  have htype_mem : a ≤ (flagTyp Xv : ℕ) ∧ (flagTyp Xv : ℕ) ≤ b := by
    rw [htyp]
    constructor <;> omega
  have htyp_notJ : flagTyp Xv ∉
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
    simp only [Set.mem_setOf_eq, not_not]
    exact htype_mem
  have hTbm : (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) ≤
      (stdDChamber σ (m + 1)).toFlipFrame.sub m :=
    aRes_stdSub_mono (σ := σ) (m + 1) (by omega)
  have hinf : (stdDChamber σ (m + 1)).toFlipFrame.alt ⊓ L =
      (stdDChamber σ (m + 1)).toFlipFrame.sub m := by
    have h := FlipFrame.alt_inf_spanAt_univ
      (c := (stdDChamber σ (m + 1)).toFlipFrame) hσ
    rw [hL, ← stdDChamber_spanAt_univ σ (m + 1)]
    exact h
  have hX_lt_alt : X < (stdDChamber σ (m + 1)).toFlipFrame.alt := by
    have hsub : X ≤ (stdDChamber σ (m + 1)).toFlipFrame.sub m :=
      le_trans hX_le_Tb hTbm
    have hle : X ≤ (stdDChamber σ (m + 1)).toFlipFrame.alt := by
      rw [← hinf] at hsub
      exact hsub.trans inf_le_left
    refine lt_of_le_of_ne hle ?_
    intro heq
    have h1 := hfin_congr heq
    rw [hXdim, FlipFrame.finrank_alt hσ] at h1
    omega
  have hadj : ∀ j : Fin (m + 1), j ∈
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} →
      (flagGraph σ m).Adj Xv (flagChamber E m j) := by
    intro j hj
    have hja_or : (j : ℕ) < a ∨ b < (j : ℕ) := by
      have h := hj
      simp only [Set.mem_setOf_eq] at h
      omega
    by_cases hja : (j : ℕ) < a
    · have hi : (j : ℕ) + 1 < m := by omega
      have hch : (flagChamber E m j).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) :=
        coe_flagChamber_of_lt E hi
      have hle : (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) ≤
          (stdDChamber σ (m + 1)).toFlipFrame.sub a :=
        aRes_stdSub_mono (σ := σ) (m + 1) (by omega)
      refine Or.inr (Or.inl ?_)
      rw [hch]
      exact lt_of_le_of_lt hle hTaX
    · by_cases hjlast : j = Fin.last m
      · subst hjlast
        refine Or.inl ?_
        rw [coe_flagChamber_last E]
        exact hXltL
      · by_cases hjalt : (j : ℕ) + 1 = m
        · have hch : (flagChamber E m j).1 =
              (stdDChamber σ (m + 1)).toFlipFrame.alt :=
            coe_flagChamber_of_succ_eq E hjalt
          refine Or.inl ?_
          rw [hch]
          exact hX_lt_alt
        · have hjne : (j : ℕ) ≠ m := by
            intro h
            exact hjlast (Fin.ext (by simpa using h))
          have hi : (j : ℕ) + 1 < m := by
            have := j.isLt
            omega
          have hch : (flagChamber E m j).1 =
              (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) :=
            coe_flagChamber_of_lt E hi
          have hle : (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) ≤
              (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) :=
            aRes_stdSub_mono (σ := σ) (m + 1) (by omega)
          have hle' : X ≤ (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) :=
            le_trans hX_le_Tb hle
          have hlt : X < (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) := by
            refine lt_of_le_of_ne hle' ?_
            intro heq
            have h1 := hfin_congr heq
            rw [hXdim, aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)] at h1
            omega
          refine Or.inl ?_
          rw [hch]
          exact hlt
  exact ⟨Xv, htyp_notJ, hadj⟩

theorem aResStemFwd_val (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b) (hbm : b + 2 ≤ m)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}) :
    (aResStemFwd E hab hbm x).1 =
      Submodule.comap (aResPhi (K := K) (m + 1)) x.1.1 ⊓
        coordBlock (m + 1) K a (b + 2) := rfl

theorem aResStemBwd_val (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b) (hbm : b + 2 ≤ m)
    (y : NdVert σ (coordBlock (m + 1) K a (b + 2))) :
    (aResStemBwd E hab hbm y).1.1 =
      ((coordBlock (m + 1) K 0 a ⊔ y.1).map (aResPhi (K := K) (m + 1))) := rfl

theorem aResStem_vert_bounds (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b)
    (hbm : b + 2 ≤ m)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}) :
    (stdDChamber σ (m + 1)).toFlipFrame.sub a < x.1.1 ∧
      x.1.1 < (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
  classical
  have hσ := E.isUnitary.invol
  set X := x.1.1 with hX
  have ht : a ≤ (flagTyp x.1 : ℕ) ∧ (flagTyp x.1 : ℕ) ≤ b := by
    have h := x.2.1
    simpa only [Set.mem_setOf_eq, not_not] using h
  have hxdim : Module.finrank K X = (flagTyp x.1 : ℕ) + 1 := by
    rw [hX]
    exact FlagVert.finrank_eq_of_flagTyp (by omega)
  constructor
  · rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, aRes_stdSub_zero]
      exact bot_lt_iff_ne_bot.mpr x.1.2.2.1
    · have haJ : (⟨a - 1, by omega⟩ : Fin (m + 1)) ∈
          {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
        simp only [Set.mem_setOf_eq]
        omega
      have hadj := x.2.2 ⟨a - 1, by omega⟩ haJ
      have hch : (flagChamber E m ⟨a - 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.sub a := by
        rw [coe_flagChamber_of_lt E (i := ⟨a - 1, by omega⟩)
          (by dsimp only; omega)]
        congr 1
        rw [Fin.val_mk, Nat.sub_add_cancel hapos]
      have hdimTa : Module.finrank K ((stdDChamber σ (m + 1)).toFlipFrame.sub a) = a :=
        aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)
      have hlt : Module.finrank K (flagChamber E m ⟨a - 1, by omega⟩).1 <
          Module.finrank K X := by
        rw [hch, hdimTa, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hadj.symm
      rw [hch] at h
      exact h
  · by_cases hlt : b + 2 < m
    · have hadj := x.2.2 ⟨b + 1, by omega⟩ (by
          simp only [Set.mem_setOf_eq]
          omega)
      have hch : (flagChamber E m ⟨b + 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2) := by
        rw [coe_flagChamber_of_lt E (i := ⟨b + 1, by omega⟩)
          (by omega)]
      have hdimTb : Module.finrank K
          ((stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2)) = b + 2 :=
        aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)
      have hlx : Module.finrank K X <
          Module.finrank K (flagChamber E m ⟨b + 1, by omega⟩).1 := by
        rw [hch, hdimTb, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlx).1 hadj
      rw [hch] at h
      exact h
    · have hb_eq : b + 2 = m := by omega
      have hadjAlt := x.2.2 ⟨b + 1, by omega⟩ (by
          simp only [Set.mem_setOf_eq]
          omega)
      have hb2 : (⟨b + 1, by omega⟩ : Fin (m + 1)) = ⟨m - 1, by omega⟩ := by
        apply Fin.ext
        simp only
        omega
      have hAlt : (flagChamber E m ⟨b + 1, by omega⟩).1 =
          (stdDChamber σ (m + 1)).toFlipFrame.alt := by
        rw [hb2]
        exact coe_flagChamber_of_succ_eq E (by dsimp only; omega)
      have hdimAlt : Module.finrank K
          ((stdDChamber σ (m + 1)).toFlipFrame.alt) = m + 1 :=
        FlipFrame.finrank_alt hσ _
      have hlx : Module.finrank K X <
          Module.finrank K (flagChamber E m ⟨b + 1, by omega⟩).1 := by
        rw [hAlt, hdimAlt, hxdim]
        omega
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlx).1 hadjAlt
      rw [hAlt] at h
      have hxL : X < stdLag (m + 1) K := by
        have hmJ : (Fin.last m) ∈
            {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} := by
          simp only [Set.mem_setOf_eq, Fin.val_last]
          omega
        have hadjL := x.2.2 (Fin.last m) hmJ
        have hdL : Module.finrank K (flagChamber E m (Fin.last m)).1 = m + 1 := by
          rw [finrank_flagChamber]
          simp
        have hltL : Module.finrank K X <
            Module.finrank K (flagChamber E m (Fin.last m)).1 := by
          rw [hdL, hxdim]
          omega
        have hL := (flagGraph_adj_iff_lt_of_finrank_lt hltL).1 hadjL
        rwa [coe_flagChamber_last E] at hL
      have hle : X ≤ (stdDChamber σ (m + 1)).toFlipFrame.alt ⊓ stdLag (m + 1) K :=
        le_inf h.le hxL.le
      have hinf : (stdDChamber σ (m + 1)).toFlipFrame.alt ⊓ stdLag (m + 1) K =
          (stdDChamber σ (m + 1)).toFlipFrame.sub m := by
        have h := FlipFrame.alt_inf_spanAt_univ
          (c := (stdDChamber σ (m + 1)).toFlipFrame) hσ
        rw [← stdDChamber_spanAt_univ σ (m + 1)]
        exact h
      rw [hinf] at hle
      refine lt_of_le_of_ne (by rw [hb_eq]; exact hle) ?_
      intro heq
      have h1 : Module.finrank K X = m := by
        rw [heq, hb_eq, aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)]
      rw [hxdim] at h1
      omega

theorem aResStemBwd_fwd (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b) (hbm : b + 2 ≤ m)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}) :
    aResStemBwd E hab hbm (aResStemFwd E hab hbm x) = x := by
  classical
  have hσ := E.isUnitary.invol
  obtain ⟨hTaX, hXTb⟩ := aResStem_vert_bounds E hab hbm x
  set X := x.1.1 with hX
  set A := coordBlock (m + 1) K 0 a with hA
  set B := coordBlock (m + 1) K a (b + 2) with hB
  set C := coordBlock (m + 1) K 0 (b + 2) with hC
  set L := stdLag (m + 1) K with hL
  set H := Submodule.comap (aResPhi (K := K) (m + 1)) X with hH
  have hxL : X ≤ L := by
    rw [hL]
    exact le_trans hXTb.le (aRes_stdSub_le_stdLag (σ := σ) (m + 1) (b + 2))
  have hHX : H.map (aResPhi (K := K) (m + 1)) = X := by
    rw [hH, Submodule.map_comap_eq, aResPhi_range, inf_eq_right.2 hxL]
  have hA_le_H : A ≤ H := by
    have hmap : A.map (aResPhi (K := K) (m + 1)) ≤ H.map (aResPhi (K := K) (m + 1)) := by
      rw [hHX, hA, aResPhi_stdSub (σ := σ) (m + 1) a (by omega)]
      exact hTaX.le
    exact (Submodule.map_le_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := A) (q := H)).1 hmap
  have hH_le_C : H ≤ C := by
    have hmap : H.map (aResPhi (K := K) (m + 1)) ≤
        C.map (aResPhi (K := K) (m + 1)) := by
      rw [hHX, hC, aResPhi_stdSub (σ := σ) (m + 1) (b + 2) (by omega)]
      exact hXTb.le
    exact (Submodule.map_le_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := H) (q := C)).1 hmap
  have hC_eq : C = A ⊔ B := by
    rw [hC, hA]
    exact (coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := b + 2)
      (Nat.zero_le a) (by omega)).symm
  have hH_le_AB : H ≤ A ⊔ B := hC_eq ▸ hH_le_C
  have hH_eq : H = A ⊔ H ⊓ B := (aRes_inf_sup_eq hA_le_H hH_le_AB).symm
  apply Subtype.ext
  apply Subtype.ext
  rw [aResStemBwd_val, aResStemFwd_val]
  change ((A ⊔ (H ⊓ B)).map (aResPhi (K := K) (m + 1))) = X
  rw [← hH_eq, hHX]

theorem aResStemFwd_bwd (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b) (hbm : b + 2 ≤ m)
    (y : NdVert σ (coordBlock (m + 1) K a (b + 2))) :
    aResStemFwd E hab hbm (aResStemBwd E hab hbm y) = y := by
  apply Subtype.ext
  rw [aResStemFwd_val, aResStemBwd_val,
    Submodule.comap_map_eq_of_injective (aResPhi_injective (m + 1))]
  exact aRes_sup_inf_eq y.2.1 (coordBlock_inf_eq_bot (le_refl a))

theorem aResStem_adj_iff (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b) (hbm : b + 2 ≤ m)
    (x y : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m)
        {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}).Adj x y ↔
      (ndGraph σ (coordBlock (m + 1) K a (b + 2))).Adj
        (aResStemFwd E hab hbm x) (aResStemFwd E hab hbm y) := by
  classical
  obtain ⟨hTaX, hXTb⟩ := aResStem_vert_bounds E hab hbm x
  obtain ⟨hTaY, hYTb⟩ := aResStem_vert_bounds E hab hbm y
  set X := x.1.1 with hX
  set Y := y.1.1 with hY
  set A := coordBlock (m + 1) K 0 a with hA
  set B := coordBlock (m + 1) K a (b + 2) with hB
  set C := coordBlock (m + 1) K 0 (b + 2) with hC
  set Hx := Submodule.comap (aResPhi (K := K) (m + 1)) X with hHx
  set Hy := Submodule.comap (aResPhi (K := K) (m + 1)) Y with hHy
  set Sx := Hx ⊓ B with hSx
  set Sy := Hy ⊓ B with hSy
  have hFxv : (aResStemFwd E hab hbm x).1 = Sx := by
    rw [aResStemFwd_val]
  have hFyv : (aResStemFwd E hab hbm y).1 = Sy := by
    rw [aResStemFwd_val]
  have hxL : X ≤ stdLag (m + 1) K :=
    le_trans hXTb.le (aRes_stdSub_le_stdLag (σ := σ) (m + 1) (b + 2))
  have hyL : Y ≤ stdLag (m + 1) K :=
    le_trans hYTb.le (aRes_stdSub_le_stdLag (σ := σ) (m + 1) (b + 2))
  have hHxX : Hx.map (aResPhi (K := K) (m + 1)) = X := by
    rw [hHx, Submodule.map_comap_eq, aResPhi_range, inf_eq_right.2 hxL]
  have hHyY : Hy.map (aResPhi (K := K) (m + 1)) = Y := by
    rw [hHy, Submodule.map_comap_eq, aResPhi_range, inf_eq_right.2 hyL]
  have hC_eq : C = A ⊔ B := by
    rw [hC, hA]
    exact (coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := b + 2)
      (Nat.zero_le a) (by omega)).symm
  have hHx_le_AB : Hx ≤ A ⊔ B := by
    have hmap : Hx.map (aResPhi (K := K) (m + 1)) ≤
        C.map (aResPhi (K := K) (m + 1)) := by
      rw [hHxX, hC, aResPhi_stdSub (σ := σ) (m + 1) (b + 2) (by omega)]
      exact hXTb.le
    exact le_trans ((Submodule.map_le_map_iff_of_injective
      (f := aResPhi (K := K) (m + 1)) (aResPhi_injective (m + 1))
      (p := Hx) (q := C)).1 hmap) (le_of_eq hC_eq)
  have hHy_le_AB : Hy ≤ A ⊔ B := by
    have hmap : Hy.map (aResPhi (K := K) (m + 1)) ≤
        C.map (aResPhi (K := K) (m + 1)) := by
      rw [hHyY, hC, aResPhi_stdSub (σ := σ) (m + 1) (b + 2) (by omega)]
      exact hYTb.le
    exact le_trans ((Submodule.map_le_map_iff_of_injective
      (f := aResPhi (K := K) (m + 1)) (aResPhi_injective (m + 1))
      (p := Hy) (q := C)).1 hmap) (le_of_eq hC_eq)
  have hA_le_Hx : A ≤ Hx := by
    have hmap : A.map (aResPhi (K := K) (m + 1)) <
        Hx.map (aResPhi (K := K) (m + 1)) := by
      rw [hHxX, hA, aResPhi_stdSub (σ := σ) (m + 1) a (by omega)]
      exact hTaX
    exact ((Submodule.map_lt_map_iff_of_injective
      (f := aResPhi (K := K) (m + 1)) (aResPhi_injective (m + 1))
      (p := A) (q := Hx)).1 hmap).le
  have hA_le_Hy : A ≤ Hy := by
    have hmap : A.map (aResPhi (K := K) (m + 1)) <
        Hy.map (aResPhi (K := K) (m + 1)) := by
      rw [hHyY, hA, aResPhi_stdSub (σ := σ) (m + 1) a (by omega)]
      exact hTaY
    exact ((Submodule.map_lt_map_iff_of_injective
      (f := aResPhi (K := K) (m + 1)) (aResPhi_injective (m + 1))
      (p := A) (q := Hy)).1 hmap).le
  have hHx_eq : Hx = A ⊔ Sx := (aRes_inf_sup_eq hA_le_Hx hHx_le_AB).symm
  have hHy_eq : Hy = A ⊔ Sy := (aRes_inf_sup_eq hA_le_Hy hHy_le_AB).symm
  have hSx_le_B : Sx ≤ B := inf_le_right
  have hSy_le_B : Sy ≤ B := inf_le_right
  have hABbot : A ⊓ B = ⊥ := coordBlock_inf_eq_bot (le_refl a)
  have hXY : X < Y ↔ Sx < Sy := by
    rw [← hHxX, ← hHyY]
    rw [Submodule.map_lt_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := Hx) (q := Hy)]
    rw [hHx_eq, hHy_eq]
    exact aRes_sup_lt_sup_iff hSx_le_B hSy_le_B hABbot
  have hYX : Y < X ↔ Sy < Sx := by
    rw [← hHyY, ← hHxX]
    rw [Submodule.map_lt_map_iff_of_injective (f := aResPhi (K := K) (m + 1))
      (aResPhi_injective (m + 1)) (p := Hy) (q := Hx)]
    rw [hHy_eq, hHx_eq]
    exact aRes_sup_lt_sup_iff hSy_le_B hSx_le_B hABbot
  have hTbdim : Module.finrank K
      ((stdDChamber σ (m + 1)).toFlipFrame.sub (b + 2)) = b + 2 :=
    aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)
  have hXd : Module.finrank K X ≠ m + 1 := by
    have h1 := Submodule.finrank_lt_finrank_of_lt hXTb
    omega
  have hYd : Module.finrank K Y ≠ m + 1 := by
    have h1 := Submodule.finrank_lt_finrank_of_lt hYTb
    omega
  have hsrc : (residueGraph (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)}).Adj x y ↔
      X < Y ∨ Y < X := by
    change (flagGraph σ m).Adj x.1 y.1 ↔ X < Y ∨ Y < X
    constructor
    · rintro (h | h | ⟨h1, -, -⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h1 hXd
    · intro h
      exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
  have htgt : (ndGraph σ (coordBlock (m + 1) K a (b + 2))).Adj
      (aResStemFwd E hab hbm x) (aResStemFwd E hab hbm y) ↔
      Sx < Sy ∨ Sy < Sx := by
    change (aResStemFwd E hab hbm x).1 < (aResStemFwd E hab hbm y).1 ∨
      (aResStemFwd E hab hbm y).1 < (aResStemFwd E hab hbm x).1 ↔ _
    rw [hFxv, hFyv]
  rw [hsrc, htgt]
  constructor
  · rintro (h | h)
    · exact Or.inl (hXY.mp h)
    · exact Or.inr (hYX.mp h)
  · rintro (h | h)
    · exact Or.inl (hXY.mpr h)
    · exact Or.inr (hYX.mpr h)

noncomputable def aResPhiAlt (d : ℕ) : (Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K) :=
  { toFun := fun x => ∑ i, x i • stdAlt (K := K) (n := d) i
    map_add' := by
      intro x y
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_smul]
    map_smul' := by
      intro c x
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply] }

theorem aResPhiAlt_single (d : ℕ) (i : Fin d) :
    aResPhiAlt (K := K) d (Pi.single i (1 : K)) = stdAlt (K := K) (n := d) i := by
  change (∑ k, ((Pi.single i (1 : K) : Fin d → K)) k • stdAlt (K := K) (n := d) k) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp only [Pi.single_eq_of_ne hk, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem aResPhiAlt_apply_inl (d : ℕ) (x : Fin d → K) {j : Fin d}
    (hj : (j : ℕ) + 1 < d) : aResPhiAlt (K := K) d x (.inl j) = x j := by
  change (∑ k, x k • stdAlt (K := K) (n := d) k) (.inl j) = x j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [stdAlt_of_lt hj]
    simp
  · intro k _ hk
    by_cases hk' : (k : ℕ) + 1 < d
    · rw [stdAlt_of_lt hk']
      simp [stdE, Ne.symm hk]
    · rw [stdAlt_of_not_lt hk']
      simp [stdF]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem aResPhiAlt_apply_inl_last (d : ℕ) (hd : 1 ≤ d) (x : Fin d → K) :
    aResPhiAlt (K := K) d x (.inl ⟨d - 1, by omega⟩) = 0 := by
  change (∑ k, x k • stdAlt (K := K) (n := d) k) (.inl ⟨d - 1, by omega⟩) = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) + 1 < d
  · have hkne : k ≠ ⟨d - 1, by omega⟩ := by
      intro h
      rw [h] at hk
      dsimp only at hk
      omega
    rw [stdAlt_of_lt hk]
    simp [stdE, hkne]
  · rw [stdAlt_of_not_lt hk]
    simp [stdF]

theorem aResPhiAlt_apply_inr (d : ℕ) (hd : 1 ≤ d) (x : Fin d → K) {j : Fin d}
    (hj : (j : ℕ) + 1 < d) : aResPhiAlt (K := K) d x (.inr j) = 0 := by
  change (∑ k, x k • stdAlt (K := K) (n := d) k) (.inr j) = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) + 1 < d
  · rw [stdAlt_of_lt hk]
    simp [stdE]
  · have hk0 : k = ⟨d - 1, by omega⟩ := last_eq_of_not_lt hd hk
    have hjk : k ≠ j := by
      intro h
      rw [hk0] at h
      rw [← h] at hj
      omega
    rw [stdAlt_of_not_lt hk]
    simp [stdF, hjk]

theorem aResPhiAlt_apply_inr_last (d : ℕ) (hd : 1 ≤ d) (x : Fin d → K) :
    aResPhiAlt (K := K) d x (.inr ⟨d - 1, by omega⟩) = x ⟨d - 1, by omega⟩ := by
  change (∑ k, x k • stdAlt (K := K) (n := d) k) (.inr ⟨d - 1, by omega⟩) = _
  rw [Finset.sum_apply, Finset.sum_eq_single ⟨d - 1, by omega⟩]
  · rw [stdAlt_of_not_lt (by
      have h1 : d - 1 + 1 = d := Nat.sub_add_cancel hd
      simp only [h1]
      omega)]
    simp
  · intro k _ hk
    by_cases hk' : (k : ℕ) + 1 < d
    · rw [stdAlt_of_lt hk']
      simp [stdE]
    · rw [stdAlt_of_not_lt hk']
      simp [stdF, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aResPhiAlt_injective (d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (aResPhiAlt (K := K) d) := by
  intro x y h
  funext j
  by_cases hj : j = ⟨d - 1, by omega⟩
  · rw [hj]
    have := congrFun h (.inr ⟨d - 1, by omega⟩)
    rwa [aResPhiAlt_apply_inr_last d hd x, aResPhiAlt_apply_inr_last d hd y] at this
  · have hjne : (j : ℕ) ≠ d - 1 := by
      intro h
      exact hj (Fin.ext (by simpa using h))
    have hj' : (j : ℕ) + 1 < d := by
      have := j.isLt
      omega
    have := congrFun h (.inl j)
    rwa [aResPhiAlt_apply_inl d x hj', aResPhiAlt_apply_inl d y hj'] at this

theorem aResPhiAlt_flipHerm (d : ℕ) (hd : 1 ≤ d) (x y : Fin d → K) :
    flipHerm σ (aResPhiAlt (K := K) d x) (aResPhiAlt (K := K) d y) = herm σ y x := by
  rw [flipHerm_apply]
  calc ∑ i, ((aResPhiAlt (K := K) d x) (.inl i) * σ ((aResPhiAlt (K := K) d y) (.inl i)) +
        (aResPhiAlt (K := K) d x) (.inr i) * σ ((aResPhiAlt (K := K) d y) (.inr i)))
      = ∑ i, x i * σ (y i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : (i : ℕ) + 1 < d
        · rw [aResPhiAlt_apply_inl d x hi, aResPhiAlt_apply_inl d y hi,
            aResPhiAlt_apply_inr d hd x hi, aResPhiAlt_apply_inr d hd y hi, map_zero, mul_zero,
            add_zero]
        · have hi0 : i = ⟨d - 1, by omega⟩ := last_eq_of_not_lt hd hi
          rw [hi0, aResPhiAlt_apply_inl_last d hd x, aResPhiAlt_apply_inl_last d hd y,
            aResPhiAlt_apply_inr_last d hd x, aResPhiAlt_apply_inr_last d hd y, map_zero,
            mul_zero, zero_add]
    _ = ∑ i, σ (y i) * x i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = herm σ y x := rfl

theorem aResPhiAlt_range (_hσ : ∀ x, σ (σ x) = x) :
    LinearMap.range (aResPhiAlt (K := K) (m + 1)) =
      (stdDChamber σ (m + 1)).toFlipFrame.alt := by
  have hd : 1 ≤ m + 1 := by omega
  have hspan : LinearMap.range (aResPhiAlt (K := K) (m + 1)) =
      Submodule.span K (Set.range (stdAlt (K := K) (n := m + 1))) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      change (∑ i, x i • stdAlt (K := K) (n := m + 1) i) ∈
        Submodule.span K (Set.range (stdAlt (K := K) (n := m + 1)))
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i (1 : K), ?_⟩
      exact aResPhiAlt_single (m + 1) i
  rw [hspan, range_stdAlt hd]
  have hset : stdE (K := K) (n := m + 1) '' {i : Fin (m + 1) | (i : ℕ) + 1 < m + 1} =
      stdE (K := K) (n := m + 1) '' {i : Fin (m + 1) | (i : ℕ) < m} := by
    congr 1
    ext i
    simp only [Set.mem_setOf_eq]
    omega
  rw [hset, Submodule.span_union]
  have hsub : Submodule.span K
      (stdE (K := K) (n := m + 1) '' {i : Fin (m + 1) | (i : ℕ) < m}) =
      (stdDChamber σ (m + 1)).toFlipFrame.sub m :=
    (aRes_stdSub_eq_span (σ := σ) (m + 1) m).symm
  have hflip : dFlipSub σ ((stdDChamber σ (m + 1)).toFlipFrame.line (Fin.last m)) =
      K ∙ stdF (K := K) (n := m + 1) (Fin.last m) := by
    change dFlipSub σ (K ∙ stdE (K := K) (n := m + 1) (Fin.last m)) = _
    rw [dFlipSub_span_singleton, dFlip_stdE]
  rw [hsub]
  change (stdDChamber σ (m + 1)).toFlipFrame.sub m ⊔
    K ∙ stdF (K := K) (n := m + 1) (Fin.last m) =
    (stdDChamber σ (m + 1)).toFlipFrame.alt
  rw [← hflip]
  rfl

theorem aResPhiAlt_coordBlock (d j : ℕ) (hj : j < d) :
    (coordBlock d K 0 j).map (aResPhiAlt (K := K) d) =
      (stdDChamber σ d).toFlipFrame.sub j := by
  have himg : (coordBlock d K 0 j).map (aResPhiAlt (K := K) d) =
      Submodule.span K
        (stdAlt (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j}) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change x ∈ coordBlock d K 0 j at hx
      rw [coordBlock_mem] at hx
      change (∑ i, x i • stdAlt (K := K) (n := d) i) ∈
        Submodule.span K (stdAlt (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j})
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : (i : ℕ) < j
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      · rw [hx i (by omega), zero_smul]
        exact Submodule.zero_mem _
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      refine Submodule.mem_map.mpr ⟨Pi.single i (1 : K), coordBlock_single_mem.mpr
        ⟨Nat.zero_le _, hi⟩, ?_⟩
      exact aResPhiAlt_single d i
  rw [himg]
  have hset : stdAlt (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j} =
      stdE (K := K) (n := d) '' {i : Fin d | (i : ℕ) < j} := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, (stdAlt_of_lt (K := K) (n := d) (i := i)
        (lt_of_le_of_lt (Nat.succ_le_of_lt hi) hj)).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, stdAlt_of_lt (K := K) (n := d) (i := i)
        (lt_of_le_of_lt (Nat.succ_le_of_lt hi) hj)⟩
  rw [hset]
  exact (aRes_stdSub_eq_span (σ := σ) d j).symm

theorem aRes_flagTyp_ge_of_solid {U : FlagVert σ m}
    (h : Module.finrank K U.1 = m + 1) : m - 1 ≤ (flagTyp U : ℕ) := by
  unfold flagTyp
  rw [if_pos h]
  split_ifs <;> simp

theorem aResLast_vert_props (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1)
    (_hstype : m ≤ (s : ℕ) + 1)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    IsFlipflopSub σ (x.1.1 ⊓ L) ∧
      (stdDChamber σ (m + 1)).toFlipFrame.sub a < x.1.1 ⊓ L ∧
      x.1.1 ⊓ L < L := by
  classical
  have hσ := E.isUnitary.invol
  have hLdim : Module.finrank K L = m + 1 := hLsolid.2
  have hJ : ∀ t : Fin (m + 1), t ∈ {u : Fin (m + 1) | (u : ℕ) < a ∨ u = s} ↔
      (t : ℕ) < a ∨ t = s := fun _ => Iff.rfl
  have ht : a ≤ (flagTyp x.1 : ℕ) ∧ flagTyp x.1 ≠ s := by
    have h := x.2.1
    simp only [Set.mem_setOf_eq, not_or, not_lt] at h
    exact h
  set X := x.1.1 with hX
  by_cases hns : (flagTyp x.1 : ℕ) + 2 ≤ m
  · have hxdim : Module.finrank K x.1.1 = (flagTyp x.1 : ℕ) + 1 :=
      FlagVert.finrank_eq_of_flagTyp hns
    have hsJ : s ∈ {u : Fin (m + 1) | (u : ℕ) < a ∨ u = s} := by
      simp only [Set.mem_setOf_eq]
      simp
    have hxadj := x.2.2 s hsJ
    have hchdim : Module.finrank K (flagChamber E m s).1 = m + 1 := by
      rw [← hLs]
      exact hLdim
    have hxdimX : Module.finrank K X = (flagTyp x.1 : ℕ) + 1 := by
      rw [hX]
      exact hxdim
    have hlt : Module.finrank K X < Module.finrank K (flagChamber E m s).1 := by
      rw [hxdimX, hchdim]
      omega
    have hxL : X < L := by
      have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hxadj
      rwa [← hLs] at h
    have hXeq : X ⊓ L = X := inf_eq_left.2 hxL.le
    have hTa : (stdDChamber σ (m + 1)).toFlipFrame.sub a < X := by
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · rw [ha0, aRes_stdSub_zero]
        exact bot_lt_iff_ne_bot.mpr x.1.2.2.1
      · have haJ : (⟨a - 1, by omega⟩ : Fin (m + 1)) ∈
            {u : Fin (m + 1) | (u : ℕ) < a ∨ u = s} := by
          simp only [Set.mem_setOf_eq]
          left
          omega
        have hadj := x.2.2 ⟨a - 1, by omega⟩ haJ
        have hch : (flagChamber E m ⟨a - 1, by omega⟩).1 =
            (stdDChamber σ (m + 1)).toFlipFrame.sub a := by
          rw [coe_flagChamber_of_lt E (i := ⟨a - 1, by omega⟩)
            (by dsimp only; omega)]
          congr 1
          rw [Fin.val_mk, Nat.sub_add_cancel hapos]
        have hdimTa : Module.finrank K
            ((stdDChamber σ (m + 1)).toFlipFrame.sub a) = a :=
          aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)
        have hlt2 : Module.finrank K (flagChamber E m ⟨a - 1, by omega⟩).1 <
            Module.finrank K x.1.1 := by
          rw [hch, hdimTa, hxdim]
          omega
        have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt2).1 hadj.symm
        rwa [hch] at h
    rw [hXeq]
    exact ⟨x.1.2.1, hTa, hxL⟩
  · have hxsolid : Module.finrank K X = m + 1 := by
      rw [hX]
      exact FlagVert.finrank_eq_of_le_flagTyp (by omega)
    have hsJ : s ∈ {u : Fin (m + 1) | (u : ℕ) < a ∨ u = s} := by
      simp only [Set.mem_setOf_eq]
      simp
    have hxadj := x.2.2 s hsJ
    have hchdim : Module.finrank K (flagChamber E m s).1 = m + 1 := by
      rw [← hLs]
      exact hLdim
    have hxsolid' : Module.finrank K x.1.1 = m + 1 := by rw [← hX]; exact hxsolid
    have hinf : Module.finrank K ↥(X ⊓ L) = m := by
      rcases hxadj with hlt | hlt | ⟨-, -, h3⟩
      · have h := Submodule.finrank_lt_finrank_of_lt hlt
        rw [hchdim, hxsolid'] at h
        omega
      · have h := Submodule.finrank_lt_finrank_of_lt hlt
        rw [hchdim, hxsolid'] at h
        omega
      · rw [hLs]
        exact h3
    have hXflip : IsFlipflopSub σ (X ⊓ L) :=
      isFlipflopSub_inf_of_isLagrangian hσ (by rw [hX]; exact x.1.2.1)
        (FlagVert.isLagrangian hxsolid) hLsolid.1 hLsolid.isLagrangian (by rw [hinf])
    have hTa_le : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ X ⊓ L := by
      refine le_inf ?_ ?_
      · rcases Nat.eq_zero_or_pos a with ha0 | hapos
        · rw [ha0, aRes_stdSub_zero]
          exact bot_le
        · have haJ : (⟨a - 1, by omega⟩ : Fin (m + 1)) ∈
              {u : Fin (m + 1) | (u : ℕ) < a ∨ u = s} := by
            simp only [Set.mem_setOf_eq]
            left
            omega
          have hadj := x.2.2 ⟨a - 1, by omega⟩ haJ
          have hch : (flagChamber E m ⟨a - 1, by omega⟩).1 =
              (stdDChamber σ (m + 1)).toFlipFrame.sub a := by
            rw [coe_flagChamber_of_lt E (i := ⟨a - 1, by omega⟩)
              (by dsimp only; omega)]
            congr 1
            rw [Fin.val_mk, Nat.sub_add_cancel hapos]
          have hdimTa : Module.finrank K
              ((stdDChamber σ (m + 1)).toFlipFrame.sub a) = a :=
            aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)
          have hlt2 : Module.finrank K (flagChamber E m ⟨a - 1, by omega⟩).1 <
              Module.finrank K X := by
            rw [hch, hdimTa, hxsolid]
            omega
          have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt2).1 hadj.symm
          rw [hch] at h
          exact h.le
      · exact hTaL
    have hTa_lt : (stdDChamber σ (m + 1)).toFlipFrame.sub a < X ⊓ L := by
      refine lt_of_le_of_ne hTa_le ?_
      intro heq
      have h1 : Module.finrank K
          ((stdDChamber σ (m + 1)).toFlipFrame.sub a) = m := by
        rw [heq, hinf]
      rw [aRes_stdSub_finrank (σ := σ) (m + 1) (by omega)] at h1
      omega
    have hLt : X ⊓ L < L := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      have h1 : Module.finrank K ↥(X ⊓ L) = Module.finrank K ↥L := by rw [heq]
      rw [hinf] at h1
      omega
    exact ⟨hXflip, hTa_lt, hLt⟩

@[expose] noncomputable def aResLastFwd (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    NdVert σ (coordBlock (m + 1) K a (m + 1)) := by
  classical
  have hσ := E.isUnitary.invol
  set A := coordBlock (m + 1) K 0 a with hA
  set B := coordBlock (m + 1) K a (m + 1) with hB
  set X := x.1.1 ⊓ L with hX
  set H := Submodule.comap ψ X with hH
  obtain ⟨hXflip, hTaX, hXltL⟩ := aResLast_vert_props E ha L hLsolid hTaL hLs hstype x
  have hABtop : A ⊔ B = ⊤ := by
    rw [hA]
    change coordBlock (m + 1) K 0 a ⊔ coordBlock (m + 1) K a (m + 1) = ⊤
    rw [coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := m + 1)
      (Nat.zero_le a) (by omega)]
    exact coordBlock_top (m + 1)
  have hHX : H.map ψ = X := by
    rw [hH, Submodule.map_comap_eq, hψrange, inf_eq_right.2 hXltL.le]
  have hA_lt_H : A < H := by
    have hmap : A.map ψ < H.map ψ := by
      rw [hA, hψa, hHX]
      exact hTaX
    exact (Submodule.map_lt_map_iff_of_injective (f := ψ) hψinj (p := A) (q := H)).1 hmap
  have hH_lt_top : H < ⊤ := by
    have hmap : H.map ψ < (⊤ : Submodule K (Fin (m + 1) → K)).map ψ := by
      rw [hHX, Submodule.map_top, hψrange]
      exact hXltL
    exact (Submodule.map_lt_map_iff_of_injective (f := ψ) hψinj (p := H) (q := ⊤)).1 hmap
  have hA_le_H : A ≤ H := hA_lt_H.le
  have hH_le_AB : H ≤ A ⊔ B := by rw [hABtop]; exact le_top
  have hH_eq : H = A ⊔ H ⊓ B := (aRes_inf_sup_eq hA_le_H hH_le_AB).symm
  have hAB : Orth σ A B := coordBlock_orth (le_refl a)
  have hbot : A ⊓ B = ⊥ := coordBlock_inf_eq_bot (le_refl a)
  have hAnd : Nondeg σ A := coordBlock_nondeg
  have hHnd : Nondeg σ H := by
    have hiff := nondeg_iff_isFlipflopSub_map (n := m + 1) hσ hLsolid hψinj hψrange hψflip
      (W := H)
    refine hiff.2 ?_
    rw [hHX]
    exact hXflip
  refine ⟨H ⊓ B, inf_le_right, ?_, ?_, ?_⟩
  · intro hbot'
    have hH_eq_A : H = A := by
      rw [hH_eq, hbot', sup_bot_eq]
    exact hA_lt_H.ne' hH_eq_A
  · intro hBeq
    have hH_eq_top : H = ⊤ := by rw [hH_eq, hBeq, hABtop]
    exact hH_lt_top.ne hH_eq_top
  · have := (aRes_nondeg_sup_iff hσ hAB hAnd (S := H ⊓ B) inf_le_right).1
      (hH_eq ▸ hHnd)
    exact this

theorem aRes_finrank_map_of_injective
    {ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hψinj : Function.Injective ψ) (H : Submodule K (Fin (m + 1) → K)) :
    Module.finrank K (H.map ψ) = Module.finrank K H :=
  (Submodule.equivMapOfInjective ψ hψinj H).finrank_eq.symm

@[expose] noncomputable def aResLastBwdAux (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (_hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (y : NdVert σ (coordBlock (m + 1) K a (m + 1))) :
    { v : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
        {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} //
      v.1.1 ⊓ L = (coordBlock (m + 1) K 0 a ⊔ y.1).map ψ ∧
        ((v.1.1 = (coordBlock (m + 1) K 0 a ⊔ y.1).map ψ ∧
            Module.finrank K y.1 < m - a) ∨
          (IsSolid σ v.1.1 ∧ v.1.1 ≠ L ∧ Module.finrank K y.1 = m - a)) } := by
  classical
  have hσ := E.isUnitary.invol
  have hLdim : Module.finrank K L = m + 1 := hLsolid.2
  have hm1 : 1 ≤ m := by omega
  set S := y.1 with hS
  set A := coordBlock (m + 1) K 0 a with hA
  let B : Submodule K (Fin (m + 1) → K) :=
    coordBlock (m + 1) K a (m + 1)
  set H := A ⊔ S with hH
  set X := H.map ψ with hX
  have hS_le_B : S ≤ B := y.2.1
  have hS_ne_bot : S ≠ ⊥ := y.2.2.1
  have hS_ne_B : S ≠ B := y.2.2.2.1
  have hS_nd : Nondeg σ S := y.2.2.2.2
  have hABtop : A ⊔ B = ⊤ := by
    rw [hA]
    change coordBlock (m + 1) K 0 a ⊔ coordBlock (m + 1) K a (m + 1) = ⊤
    rw [coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := m + 1)
      (Nat.zero_le a) (by omega)]
    exact coordBlock_top (m + 1)
  have hASbot : A ⊓ S = ⊥ := by
    have h := inf_le_inf (le_refl A) hS_le_B
    rw [show A ⊓ B = ⊥ from coordBlock_inf_eq_bot (le_refl a)] at h
    exact le_bot_iff.mp h
  have hAB : Orth σ A B := coordBlock_orth (le_refl a)
  have hAnd : Nondeg σ A := coordBlock_nondeg
  have hHnd : Nondeg σ H := by
    rw [hH]
    exact (aRes_nondeg_sup_iff hσ hAB hAnd hS_le_B).2 hS_nd
  have hXflip : IsFlipflopSub σ X := by
    have hiff := nondeg_iff_isFlipflopSub_map (n := m + 1) hσ hLsolid hψinj hψrange hψflip
      (W := H)
    rw [hX]
    exact hiff.1 hHnd
  have hX_le_L : X ≤ L := by
    rw [hX, ← hψrange]
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, rfl⟩
  have hAdim : Module.finrank K A = a := by
    rw [hA]
    exact aRes_finrank_coordBlock_zero (m + 1) a (by omega)
  have hBdim : Module.finrank K B = m + 1 - a := by
    change Module.finrank K (coordBlock (m + 1) K a (m + 1)) = m + 1 - a
    exact aRes_finrank_coordBlock (m + 1) a (m + 1) (by omega) (by omega)
  have hHdim : Module.finrank K H = a + Module.finrank K S := by
    rw [hH]
    have h := Submodule.finrank_sup_add_finrank_inf_eq A S
    rw [hASbot, finrank_bot, add_zero, hAdim] at h
    omega
  have hXdim : Module.finrank K X = a + Module.finrank K S := by
    rw [hX, aRes_finrank_map_of_injective hψinj, hHdim]
  have hdimS_le : Module.finrank K S ≤ m - a := by
    have h := Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne hS_le_B hS_ne_B)
    rw [hBdim] at h
    omega
  have hA_lt_H : A < H := by
    rw [hH, lt_iff_le_and_ne]
    refine ⟨le_sup_left, ?_⟩
    intro heq
    have hS_le_A : S ≤ A := by rw [heq]; exact le_sup_right
    have hS_le_bot : S ≤ ⊥ := by
      rw [← hASbot]
      exact le_inf hS_le_A le_rfl
    exact hS_ne_bot (le_bot_iff.mp hS_le_bot)
  have hTa_lt_X : (stdDChamber σ (m + 1)).toFlipFrame.sub a < X := by
    have hmap : A.map ψ < H.map ψ :=
      (Submodule.map_lt_map_iff_of_injective (f := ψ) hψinj
        (p := A) (q := H)).mpr hA_lt_H
    rw [hA, hψa, ← hX] at hmap
    exact hmap
  by_cases hhyper : Module.finrank K S = m - a
  · have hXdim_m : Module.finrank K X = m := by
      rw [hXdim, hhyper]
      omega
    have hXltL : X < L := by
      refine lt_of_le_of_ne hX_le_L ?_
      intro heq
      have h1 : Module.finrank K X = Module.finrank K L := by rw [heq]
      rw [hXdim_m, hLdim] at h1
      omega
    have hdimX : Module.finrank K X + 1 = m + 1 := by omega
    have hWdata : ∃ W : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
        IsSolid σ W ∧ W ≠ L ∧ X ≤ W := by
      obtain ⟨M, M', hM, hM', hXM, hXM', hMeven, hM'odd, huniq⟩ :=
        hXflip.exists_two_solids (n := m + 1) hσ hdimX
      have hMM' : M ≠ M' := by
        intro h
        apply hM'odd
        rwa [h] at hMeven
      have hLcases : L = M ∨ L = M' := huniq L hLsolid.isLagrangian hX_le_L
      rcases hLcases with hLM | hLM'
      · refine ⟨M', hM', ?_, hXM'⟩
        intro h
        exact hMM' (h.trans hLM).symm
      · refine ⟨M, hM, ?_, hXM⟩
        intro h
        exact hMM' (h.trans hLM')
    let W := Classical.choose hWdata
    have hWsolid : IsSolid σ W := (Classical.choose_spec hWdata).1
    have hWneL : W ≠ L := (Classical.choose_spec hWdata).2.1
    have hXW : X ≤ W := (Classical.choose_spec hWdata).2.2
    have hWinf : Module.finrank K ↥(W ⊓ L) = m := by
      have h1 : X ≤ W ⊓ L := le_inf hXW hX_le_L
      have h2 : Module.finrank K ↥(W ⊓ L) ≤ m := by
        have hlt : W ⊓ L < L := by
          refine lt_of_le_of_ne inf_le_right ?_
          intro h
          have hle : L ≤ W := inf_eq_right.mp h
          have hdim_eq : Module.finrank K L = Module.finrank K W := by
            rw [hLdim, hWsolid.2]
          exact hWneL (Submodule.eq_of_le_of_finrank_eq hle hdim_eq).symm
        have h := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      have h3 : m ≤ Module.finrank K ↥(W ⊓ L) := by
        have := Submodule.finrank_mono h1
        omega
      omega
    have hW_ne_bot : W ≠ ⊥ := by
      intro h
      have hdim := hWsolid.2
      rw [h, finrank_bot] at hdim
      omega
    have hWnotfin : Module.finrank K W ≠ m := by
      rw [hWsolid.2]
      omega
    have hL_ne_bot : L ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hLdim
      omega
    have hL_notfin : Module.finrank K L ≠ m := by
      rw [hLdim]
      omega
    let Wv : FlagVert σ m := ⟨W, hWsolid.1, hW_ne_bot, hWnotfin⟩
    let Lv : FlagVert σ m := ⟨L, hLsolid.1, hL_ne_bot, hL_notfin⟩
    have hLv_eq : Lv = flagChamber E m s := Subtype.ext hLs
    have hLv_solid : Module.finrank K Lv.1 = m + 1 := by
      change Module.finrank K L = m + 1
      exact hLdim
    have hWtyp_ne : flagTyp Wv ≠ flagTyp Lv := by
      intro hEq
      have hpar := (flagTyp_eq_iff_even hm1 hWsolid.2 hLv_solid).1 hEq
      have hsub : m + 1 - m = 1 := by omega
      rw [hWinf, hsub] at hpar
      exact absurd hpar (by decide)
    have hWv_solid : Module.finrank K Wv.1 = m + 1 := hWsolid.2
    have htypW_ge : m - 1 ≤ (flagTyp Wv : ℕ) := aRes_flagTyp_ge_of_solid hWv_solid
    have hLs_type : flagTyp Lv = s := by
      rw [hLv_eq]
      exact flagTyp_flagChamber E s
    have htypW_ne : flagTyp Wv ≠ s := by
      intro h
      exact hWtyp_ne (h.trans hLs_type.symm)
    have htypW_notJ : flagTyp Wv ∉ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} := by
      simp only [Set.mem_setOf_eq, not_or, not_lt]
      exact ⟨by omega, htypW_ne⟩
    have hadjW : ∀ j : Fin (m + 1), j ∈ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} →
        (flagGraph σ m).Adj Wv (flagChamber E m j) := by
      intro j hj
      have hj' : (j : ℕ) < a ∨ j = s := hj
      rcases hj' with hja | hjs
      · have hi : (j : ℕ) + 1 < m := by omega
        have hch : (flagChamber E m j).1 =
            (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) :=
          coe_flagChamber_of_lt E hi
        have hle : (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) ≤
            (stdDChamber σ (m + 1)).toFlipFrame.sub a :=
          aRes_stdSub_mono (σ := σ) (m + 1) (by omega)
        have hlt : (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) < Wv.1 :=
          lt_of_le_of_lt hle (lt_of_lt_of_le hTa_lt_X hXW)
        refine Or.inr (Or.inl ?_)
        rw [hch]
        exact hlt
      · subst hjs
        have h := flagGraph_adj_of_solids hm1 hWv_solid hLv_solid hWtyp_ne
          (T := X) (by rw [hXdim_m]; omega) hXW hX_le_L
        rwa [hLv_eq] at h
    refine ⟨⟨Wv, htypW_notJ, hadjW⟩, ?_, Or.inr ⟨hWsolid, hWneL, hhyper⟩⟩
    change W ⊓ L = (coordBlock (m + 1) K 0 a ⊔ y.1).map ψ
    rw [← hX]
    exact (Submodule.eq_of_le_of_finrank_eq (le_inf hXW hX_le_L)
      (by rw [hWinf, hXdim_m])).symm
  · have hSdim_lt : Module.finrank K S < m - a := by omega
    have hXdim_lt : Module.finrank K X < m := by
      rw [hXdim]
      omega
    have hX_ne_bot : X ≠ ⊥ := by
      intro h
      rw [h] at hTa_lt_X
      exact (not_lt_of_ge bot_le) hTa_lt_X
    let Xv : FlagVert σ m := ⟨X, hXflip, hX_ne_bot, by omega⟩
    have htyp : (flagTyp Xv : ℕ) = a + Module.finrank K S - 1 := by
      have hlt : Module.finrank K Xv.1 < m + 1 := by
        change Module.finrank K X < m + 1
        omega
      have h := aRes_flagTyp_of_finrank_lt (σ := σ) (U := Xv) hlt
      rwa [hXdim] at h
    have hSpos : 1 ≤ Module.finrank K S := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact hS_ne_bot (Submodule.finrank_eq_zero.1 h0)
    have htyp_mem : a ≤ (flagTyp Xv : ℕ) ∧ (flagTyp Xv : ℕ) ≤ m - 2 := by
      rw [htyp]
      omega
    have htyp_notJ : flagTyp Xv ∉ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} := by
      simp only [Set.mem_setOf_eq, not_or, not_lt]
      refine ⟨htyp_mem.1, ?_⟩
      intro h
      have hs : m ≤ (s : ℕ) + 1 := hstype
      omega
    have hXltL : X < L := by
      refine lt_of_le_of_ne hX_le_L ?_
      intro heq
      have h1 : Module.finrank K X = Module.finrank K L := by rw [heq]
      rw [hLdim] at h1
      omega
    have hadjX : ∀ j : Fin (m + 1), j ∈ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} →
        (flagGraph σ m).Adj Xv (flagChamber E m j) := by
      intro j hj
      have hj' : (j : ℕ) < a ∨ j = s := hj
      rcases hj' with hja | hjs
      · have hi : (j : ℕ) + 1 < m := by omega
        have hch : (flagChamber E m j).1 =
            (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) :=
          coe_flagChamber_of_lt E hi
        have hle : (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) ≤
            (stdDChamber σ (m + 1)).toFlipFrame.sub a :=
          aRes_stdSub_mono (σ := σ) (m + 1) (by omega)
        have hlt : (stdDChamber σ (m + 1)).toFlipFrame.sub ((j : ℕ) + 1) < Xv.1 :=
          lt_of_le_of_lt hle hTa_lt_X
        refine Or.inr (Or.inl ?_)
        rw [hch]
        exact hlt
      · subst j
        refine Or.inl ?_
        rw [← hLs]
        exact hXltL
    refine ⟨⟨Xv, htyp_notJ, hadjX⟩, ?_, Or.inl ⟨rfl, hSdim_lt⟩⟩
    change X ⊓ L = (coordBlock (m + 1) K 0 a ⊔ y.1).map ψ
    rw [← hX]
    exact inf_eq_left.2 hX_le_L

theorem aResLastFwd_val (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1 =
      Submodule.comap ψ (x.1.1 ⊓ L) ⊓ coordBlock (m + 1) K a (m + 1) := rfl

@[expose] noncomputable def aResLastBwd (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (y : NdVert σ (coordBlock (m + 1) K a (m + 1))) :
    residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} :=
  (aResLastBwdAux E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1

theorem aResLastBwd_inf (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (y : NdVert σ (coordBlock (m + 1) K a (m + 1))) :
    (aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1.1 ⊓ L =
      (coordBlock (m + 1) K 0 a ⊔ y.1).map ψ :=
  (aResLastBwdAux E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).2.1

theorem aResLastBwd_branch (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (y : NdVert σ (coordBlock (m + 1) K a (m + 1))) :
    ((aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1.1 =
        (coordBlock (m + 1) K 0 a ⊔ y.1).map ψ ∧
      Module.finrank K y.1 < m - a) ∨
    (IsSolid σ (aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1.1 ∧
      (aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1.1 ≠ L ∧
      Module.finrank K y.1 = m - a) :=
  (aResLastBwdAux E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).2.2

theorem aResLastFwd_bwd (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (y : NdVert σ (coordBlock (m + 1) K a (m + 1))) :
    aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
        (aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y) = y := by
  apply Subtype.ext
  rw [aResLastFwd_val, aResLastBwd_inf]
  have hcomap : Submodule.comap ψ
      (Submodule.map ψ (coordBlock (m + 1) K 0 a ⊔ y.1)) =
      coordBlock (m + 1) K 0 a ⊔ y.1 :=
    Submodule.comap_map_eq_of_injective hψinj _
  rw [hcomap]
  exact aRes_sup_inf_eq y.2.1 (coordBlock_inf_eq_bot (le_refl a))

theorem aResLastBwd_fwd (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
        (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x) = x := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  have hσ := E.isUnitary.invol
  have hm1 : 1 ≤ m := by omega
  have hLdim : Module.finrank K L = m + 1 := hLsolid.2
  set A := coordBlock (m + 1) K 0 a with hA
  let B : Submodule K (Fin (m + 1) → K) := coordBlock (m + 1) K a (m + 1)
  let S : Submodule K (Fin (m + 1) → K) :=
    (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1
  let X : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := x.1.1 ⊓ L
  let U : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    (aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
      (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x)).1.1
  have hSval : S = Submodule.comap ψ X ⊓ B :=
    aResLastFwd_val E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x
  have hUinf : U ⊓ L = (A ⊔ S).map ψ :=
    aResLastBwd_inf E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
      (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x)
  have hX_le_L : X ≤ L := inf_le_right
  obtain ⟨-, hTaX, -⟩ := aResLast_vert_props E ha L hLsolid hTaL hLs hstype x
  have hAdim : Module.finrank K A = a := by
    rw [hA]
    exact aRes_finrank_coordBlock_zero (m + 1) a (by omega)
  have hA_le_C : A ≤ Submodule.comap ψ X := by
    rw [← Submodule.map_le_iff_le_comap, hA, hψa]
    exact hTaX.le
  have hC_le_AB : Submodule.comap ψ X ≤ A ⊔ B := by
    have hABtop : A ⊔ B = ⊤ := by
      rw [hA]
      change coordBlock (m + 1) K 0 a ⊔ coordBlock (m + 1) K a (m + 1) = ⊤
      rw [coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := m + 1)
        (Nat.zero_le a) (by omega)]
      exact coordBlock_top (m + 1)
    rw [hABtop]
    exact le_top
  have hH_eq : A ⊔ S = Submodule.comap ψ X := by
    rw [hSval]
    exact aRes_inf_sup_eq hA_le_C hC_le_AB
  have hmap_H : (A ⊔ S).map ψ = X := by
    rw [hH_eq, Submodule.map_comap_eq, hψrange, inf_eq_right.2 hX_le_L]
  have hAinfS : A ⊓ S = ⊥ := by
    have h := inf_le_inf (le_refl A) (show S ≤ B from by rw [hSval]; exact inf_le_right)
    rw [show A ⊓ B = ⊥ from coordBlock_inf_eq_bot (le_refl a)] at h
    exact le_bot_iff.mp h
  have hXdim : Module.finrank K X = a + Module.finrank K S := by
    have hHdim : Module.finrank K ↥(A ⊔ S) = a + Module.finrank K S := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq A S
      rw [hAinfS, finrank_bot, add_zero, hAdim] at h
      omega
    rw [← hmap_H, aRes_finrank_map_of_injective hψinj, hHdim]
  have hchdim : Module.finrank K (flagChamber E m s).1 = m + 1 := by
    rw [← hLs]
    exact hLdim
  have hsJ : s ∈ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} := by
    simp only [Set.mem_setOf_eq]
    simp
  have hxsolid_inf : IsSolid σ x.1.1 → Module.finrank K X = m := by
    intro hxs
    have hxdim_m1 : Module.finrank K x.1.1 = m + 1 := hxs.2
    have hxadj := x.2.2 s hsJ
    rcases hxadj with hlt | hlt | ⟨-, -, h3⟩
    · have h := Submodule.finrank_lt_finrank_of_lt hlt
      rw [hxdim_m1, hchdim] at h
      omega
    · have h := Submodule.finrank_lt_finrank_of_lt hlt
      rw [hxdim_m1, hchdim] at h
      omega
    · change Module.finrank K ↥(x.1.1 ⊓ L) = m
      rw [← hLs] at h3
      exact h3
  have hxL_of_nonsolid : ¬ IsSolid σ x.1.1 → x.1.1 < L := by
    intro hxns
    have hxadj := x.2.2 s hsJ
    have hle := FlagVert.finrank_le x.1
    have hne : Module.finrank K x.1.1 ≠ m := x.1.2.2.2
    have hne_solid : Module.finrank K x.1.1 ≠ m + 1 := by
      intro h
      exact hxns ⟨x.1.2.1, h⟩
    have hlt : Module.finrank K x.1.1 < Module.finrank K (flagChamber E m s).1 := by
      rw [hchdim]
      omega
    have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hxadj
    rwa [← hLs] at h
  rcases aResLastBwd_branch E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
      (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x) with
    ⟨hUeq, hSdim_lt⟩ | ⟨hUsolid, hUneL, hSdim_eq⟩
  · have hXdim_lt : Module.finrank K X < m := by
      have h2 : a + (m - a) = m := by omega
      have h1 : a + Module.finrank K S < a + (m - a) :=
        Nat.add_lt_add_left hSdim_lt a
      omega
    have hxns : ¬ IsSolid σ x.1.1 := by
      intro hxs
      have := hxsolid_inf hxs
      rw [this] at hXdim_lt
      omega
    have hxL : x.1.1 < L := hxL_of_nonsolid hxns
    have hXeq : X = x.1.1 := inf_eq_left.2 hxL.le
    rw [hUeq, hmap_H, hXeq]
  · have hXdim_m : Module.finrank K X = m := by
      rw [hXdim, hSdim_eq]
      omega
    have hxsolid : IsSolid σ x.1.1 := by
      by_contra hxns
      have hxL : x.1.1 < L := hxL_of_nonsolid hxns
      have hXeq : X = x.1.1 := inf_eq_left.2 hxL.le
      rw [hXeq] at hXdim_m
      have hle := FlagVert.finrank_le x.1
      have hne : Module.finrank K x.1.1 ≠ m := x.1.2.2.2
      omega
    have hx_ne_L : x.1.1 ≠ L := by
      intro h
      have htyp : flagTyp x.1 = s := by
        have hxch : x.1 = flagChamber E m s := Subtype.ext (h.trans hLs)
        rw [hxch]
        exact flagTyp_flagChamber E s
      have hnot : flagTyp x.1 ≠ s := by
        have hh := x.2.1
        simp only [Set.mem_setOf_eq, not_or, not_lt] at hh
        exact hh.2
      exact hnot htyp
    have hXflip : IsFlipflopSub σ X :=
      isFlipflopSub_inf_of_isLagrangian hσ x.1.2.1
        (FlagVert.isLagrangian hxsolid.2) hLsolid.1 hLsolid.isLagrangian
        (by rw [hXdim_m])
    have hxU : x.1.1 = U := by
      obtain ⟨M, M', hM, hM', hXM, hXM', hMeven, hM'odd, huniq⟩ :=
        hXflip.exists_two_solids (n := m + 1) hσ (by omega)
      have hLmem : L = M ∨ L = M' := huniq L hLsolid.isLagrangian hX_le_L
      have hxmem : x.1.1 = M ∨ x.1.1 = M' :=
        huniq x.1.1 (FlagVert.isLagrangian hxsolid.2) (by
          show X ≤ x.1.1
          exact inf_le_left)
      have hUmem : U = M ∨ U = M' :=
        huniq U hUsolid.isLagrangian (by
          rw [← hmap_H, ← hUinf]
          exact inf_le_left)
      rcases hLmem with hLM | hLM'
      · have hxM' : x.1.1 = M' := by
          rcases hxmem with hxM | hxM'
          · exact absurd (hxM.trans hLM.symm) hx_ne_L
          · exact hxM'
        have hUM' : U = M' := by
          rcases hUmem with hUM | hUM'
          · exact absurd (hUM.trans hLM.symm) hUneL
          · exact hUM'
        exact hxM'.trans hUM'.symm
      · have hxM : x.1.1 = M := by
          rcases hxmem with hxM | hxM'
          · exact hxM
          · exact absurd (hxM'.trans hLM'.symm) hx_ne_L
        have hUM : U = M := by
          rcases hUmem with hUM | hUM'
          · exact hUM
          · exact absurd (hUM'.trans hLM'.symm) hUneL
        exact hxM.trans hUM.symm
    exact hxU.symm

theorem aResLast_nonsolid_lt (E : QuadExt F K σ) {a : ℕ} (_ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hLsolid : IsSolid σ L) {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1)
    (_hstype : m ≤ (s : ℕ) + 1)
    (z : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s})
    (hz : ¬ IsSolid σ z.1.1) : z.1.1 < L := by
  classical
  have hLdim : Module.finrank K L = m + 1 := hLsolid.2
  have hchdim : Module.finrank K (flagChamber E m s).1 = m + 1 := by
    rw [← hLs]
    exact hLdim
  have hsJ : s ∈ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} := by
    simp only [Set.mem_setOf_eq]
    simp
  have hxadj := z.2.2 s hsJ
  have hle := FlagVert.finrank_le z.1
  have hne : Module.finrank K z.1.1 ≠ m := z.1.2.2.2
  have hne_solid : Module.finrank K z.1.1 ≠ m + 1 := by
    intro h
    exact hz ⟨z.1.2.1, h⟩
  have hlt : Module.finrank K z.1.1 < Module.finrank K (flagChamber E m s).1 := by
    rw [hchdim]
    omega
  have h := (flagGraph_adj_iff_lt_of_finrank_lt hlt).1 hxadj
  rwa [← hLs] at h

theorem aResLast_solid_inf (E : QuadExt F K σ) {a : ℕ} (_ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hLsolid : IsSolid σ L) {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1)
    (_hstype : m ≤ (s : ℕ) + 1)
    (z : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s})
    (hz : IsSolid σ z.1.1) : Module.finrank K ↥(z.1.1 ⊓ L) = m := by
  classical
  have hLdim : Module.finrank K L = m + 1 := hLsolid.2
  have hchdim : Module.finrank K (flagChamber E m s).1 = m + 1 := by
    rw [← hLs]
    exact hLdim
  have hsJ : s ∈ {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} := by
    simp only [Set.mem_setOf_eq]
    simp
  have hxadj := z.2.2 s hsJ
  have hz1 : Module.finrank K z.1.1 = m + 1 := hz.2
  rcases hxadj with hlt | hlt | ⟨-, -, h3⟩
  · have h := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hz1, hchdim] at h
    omega
  · have h := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hz1, hchdim] at h
    omega
  · rw [← hLs] at h3
    exact h3

theorem aResLast_fwd_sup (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (x : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    coordBlock (m + 1) K 0 a ⊔
        (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1 =
      Submodule.comap ψ (x.1.1 ⊓ L) := by
  classical
  set A := coordBlock (m + 1) K 0 a with hA
  let B : Submodule K (Fin (m + 1) → K) := coordBlock (m + 1) K a (m + 1)
  set S := (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1
    with hS
  set X := x.1.1 ⊓ L with hX
  have hSval : S = Submodule.comap ψ X ⊓ B :=
    aResLastFwd_val E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x
  obtain ⟨-, hTaX, -⟩ := aResLast_vert_props E ha L hLsolid hTaL hLs hstype x
  have hA_le_C : A ≤ Submodule.comap ψ X := by
    rw [← Submodule.map_le_iff_le_comap, hA, hψa]
    exact hTaX.le
  have hC_le_AB : Submodule.comap ψ X ≤ A ⊔ B := by
    have hABtop : A ⊔ B = ⊤ := by
      rw [hA]
      change coordBlock (m + 1) K 0 a ⊔ coordBlock (m + 1) K a (m + 1) = ⊤
      rw [coordBlock_sup (K := K) (d := m + 1) (a := 0) (b := a) (c := m + 1)
        (Nat.zero_le a) (by omega)]
      exact coordBlock_top (m + 1)
    rw [hABtop]
    exact le_top
  rw [hSval]
  exact aRes_inf_sup_eq hA_le_C hC_le_AB

theorem aResLast_fwd_lt_iff (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (x y : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1 <
        (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1 ↔
      x.1.1 ⊓ L < y.1.1 ⊓ L := by
  classical
  set A := coordBlock (m + 1) K 0 a with hA
  let B : Submodule K (Fin (m + 1) → K) := coordBlock (m + 1) K a (m + 1)
  set Sx := (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1
  set Sy := (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1
  have hSx_le : Sx ≤ B :=
    (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).2.1
  have hSy_le : Sy ≤ B :=
    (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).2.1
  have hABbot : A ⊓ B = ⊥ := by
    rw [hA]
    exact coordBlock_inf_eq_bot (le_refl a)
  have h1 : Sx < Sy ↔ A ⊔ Sx < A ⊔ Sy :=
    (aRes_sup_lt_sup_iff (A := A) (B := B) (S := Sx) (T := Sy) hSx_le hSy_le hABbot).symm
  have h2 : A ⊔ Sx < A ⊔ Sy ↔ x.1.1 ⊓ L < y.1.1 ⊓ L := by
    rw [show A ⊔ Sx = Submodule.comap ψ (x.1.1 ⊓ L) from
        aResLast_fwd_sup E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x,
      show A ⊔ Sy = Submodule.comap ψ (y.1.1 ⊓ L) from
        aResLast_fwd_sup E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y]
    rw [← Submodule.map_lt_map_iff_of_injective (f := ψ) hψinj]
    rw [Submodule.map_comap_eq, Submodule.map_comap_eq, hψrange,
      inf_eq_right.2 inf_le_right, inf_eq_right.2 inf_le_right]
  exact h1.trans h2

theorem aRes_flagTyp_solid_cases {U : FlagVert σ m} (hm1 : 1 ≤ m)
    (h : Module.finrank K U.1 = m + 1) :
    flagTyp U = Fin.last m ∨ flagTyp U = ⟨m - 1, by omega⟩ := by
  unfold flagTyp
  rw [if_pos h]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem aResLast_solid_flagTyp_eq (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    {s : Fin (m + 1)} (hstype : m ≤ (s : ℕ) + 1)
    (x y : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s})
    (hx : IsSolid σ x.1.1) (hy : IsSolid σ y.1.1) :
    flagTyp x.1 = flagTyp y.1 := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hm1' : m - 1 < m + 1 := by omega
  have hxnot : flagTyp x.1 ≠ s := by
    have h := x.2.1
    simp only [Set.mem_setOf_eq, not_or, not_lt] at h
    exact h.2
  have hynot : flagTyp y.1 ≠ s := by
    have h := y.2.1
    simp only [Set.mem_setOf_eq, not_or, not_lt] at h
    exact h.2
  have hxc := aRes_flagTyp_solid_cases (σ := σ) hm1 hx.2
  have hyc := aRes_flagTyp_solid_cases (σ := σ) hm1 hy.2
  by_cases hs : s = Fin.last m
  · rcases hxc with hxl | hxm
    · exact absurd (hxl.trans hs.symm) hxnot
    · rcases hyc with hyl | hym
      · exact absurd (hyl.trans hs.symm) hynot
      · rw [hxm, hym]
  · have hsm : s = ⟨m - 1, hm1'⟩ := by
      apply Fin.ext
      have hsval : (s : ℕ) ≠ m := by
        intro h
        exact hs (Fin.ext (by simpa using h))
      have hslt := s.isLt
      have hge : m - 1 ≤ (s : ℕ) := by omega
      have hsle : (s : ℕ) ≤ m := by simpa using hslt
      have hs_eq : (s : ℕ) = m - 1 := by omega
      simpa using hs_eq
    rcases hxc with hxl | hxm
    · rcases hyc with hyl | hym
      · rw [hxl, hyl]
      · exact absurd (hym.trans hsm.symm) hynot
    · exact absurd (hxm.trans hsm.symm) hxnot

theorem aResLast_X_adj_iff (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hLsolid : IsSolid σ L) {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1)
    (hstype : m ≤ (s : ℕ) + 1)
    (x y : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    x.1.1 ⊓ L < y.1.1 ⊓ L ∨ y.1.1 ⊓ L < x.1.1 ⊓ L ↔
      (flagGraph σ m).Adj x.1 y.1 := by
  classical
  have hm1 : 1 ≤ m := by omega
  by_cases hxs : IsSolid σ x.1.1 <;> by_cases hys : IsSolid σ y.1.1
  · have hXx : Module.finrank K ↥(x.1.1 ⊓ L) = m :=
      aResLast_solid_inf E ha L hLsolid hLs hstype x hxs
    have hXy : Module.finrank K ↥(y.1.1 ⊓ L) = m :=
      aResLast_solid_inf E ha L hLsolid hLs hstype y hys
    have hnotX : ¬ (x.1.1 ⊓ L < y.1.1 ⊓ L ∨ y.1.1 ⊓ L < x.1.1 ⊓ L) := by
      rintro (h | h)
      · have := Submodule.finrank_lt_finrank_of_lt h
        rw [hXx, hXy] at this
        omega
      · have := Submodule.finrank_lt_finrank_of_lt h
        rw [hXx, hXy] at this
        omega
    have hnotAdj : ¬ (flagGraph σ m).Adj x.1 y.1 := by
      rintro (h | h | ⟨-, -, hinf⟩)
      · have := Submodule.finrank_lt_finrank_of_lt h
        rw [hxs.2, hys.2] at this
        omega
      · have := Submodule.finrank_lt_finrank_of_lt h
        rw [hxs.2, hys.2] at this
        omega
      · have htypes := aResLast_solid_flagTyp_eq E ha hstype x y hxs hys
        have hpar := (flagTyp_eq_iff_even hm1 hxs.2 hys.2).1 htypes
        have hsub : m + 1 - m = 1 := by omega
        rw [hinf, hsub] at hpar
        exact absurd hpar (by decide)
    exact ⟨fun h => absurd h hnotX, fun h => absurd h hnotAdj⟩
  · have hXy_eq : y.1.1 ⊓ L = y.1.1 :=
      inf_eq_left.2 (aResLast_nonsolid_lt E ha L hLsolid hLs hstype y hys).le
    have hXx : Module.finrank K ↥(x.1.1 ⊓ L) = m :=
      aResLast_solid_inf E ha L hLsolid hLs hstype x hxs
    have hy_le := FlagVert.finrank_le y.1
    have hy_ne : Module.finrank K y.1.1 ≠ m := y.1.2.2.2
    have hy_ne_solid : Module.finrank K y.1.1 ≠ m + 1 := by
      intro h
      exact hys ⟨y.1.2.1, h⟩
    have hy_lt_m : Module.finrank K y.1.1 < m := by omega
    have hleft : (x.1.1 ⊓ L < y.1.1 ⊓ L ∨ y.1.1 ⊓ L < x.1.1 ⊓ L) ↔ y.1.1 < x.1.1 := by
      constructor
      · rintro (h | h)
        · exfalso
          have := Submodule.finrank_lt_finrank_of_lt h
          rw [hXx, hXy_eq] at this
          omega
        · rw [hXy_eq] at h
          exact lt_of_le_of_ne (le_trans h.le (inf_le_left : x.1.1 ⊓ L ≤ x.1.1)) (by
            intro heq
            have hdim : Module.finrank K y.1.1 = m + 1 := by
              rw [heq]
              exact hxs.2
            omega)
      · intro hyx
        right
        rw [hXy_eq]
        have hL : y.1.1 ≤ L := (aResLast_nonsolid_lt E ha L hLsolid hLs hstype y hys).le
        have hle : y.1.1 ≤ x.1.1 ⊓ L := le_inf hyx.le hL
        refine lt_of_le_of_ne hle ?_
        intro heq
        have hdim : Module.finrank K ↥(x.1.1 ⊓ L) = Module.finrank K y.1.1 := by
          rw [heq]
        rw [hXx] at hdim
        omega
    have hright : (flagGraph σ m).Adj x.1 y.1 ↔ y.1.1 < x.1.1 := by
      constructor
      · rintro (h | h | ⟨-, hysolid, -⟩)
        · exfalso
          have := Submodule.finrank_lt_finrank_of_lt h
          rw [hxs.2] at this
          omega
        · exact h
        · exact absurd hysolid hy_ne_solid
      · intro h
        exact Or.inr (Or.inl h)
    exact hleft.trans hright.symm
  · have hXx_eq : x.1.1 ⊓ L = x.1.1 :=
      inf_eq_left.2 (aResLast_nonsolid_lt E ha L hLsolid hLs hstype x hxs).le
    have hXy : Module.finrank K ↥(y.1.1 ⊓ L) = m :=
      aResLast_solid_inf E ha L hLsolid hLs hstype y hys
    have hx_le := FlagVert.finrank_le x.1
    have hx_ne : Module.finrank K x.1.1 ≠ m := x.1.2.2.2
    have hx_ne_solid : Module.finrank K x.1.1 ≠ m + 1 := by
      intro h
      exact hxs ⟨x.1.2.1, h⟩
    have hx_lt_m : Module.finrank K x.1.1 < m := by omega
    have hleft : (x.1.1 ⊓ L < y.1.1 ⊓ L ∨ y.1.1 ⊓ L < x.1.1 ⊓ L) ↔ x.1.1 < y.1.1 := by
      constructor
      · rintro (h | h)
        · rw [hXx_eq] at h
          exact lt_of_le_of_ne (le_trans h.le (inf_le_left : y.1.1 ⊓ L ≤ y.1.1)) (by
            intro heq
            have hdim : Module.finrank K x.1.1 = m + 1 := by
              rw [heq]
              exact hys.2
            omega)
        · exfalso
          have := Submodule.finrank_lt_finrank_of_lt h
          rw [hXx_eq, hXy] at this
          omega
      · intro hxy
        left
        rw [hXx_eq]
        have hL : x.1.1 ≤ L := (aResLast_nonsolid_lt E ha L hLsolid hLs hstype x hxs).le
        have hle : x.1.1 ≤ y.1.1 ⊓ L := le_inf hxy.le hL
        refine lt_of_le_of_ne hle ?_
        intro heq
        have hdim : Module.finrank K ↥(y.1.1 ⊓ L) = Module.finrank K x.1.1 := by
          rw [← heq]
        rw [hXy] at hdim
        omega
    have hright : (flagGraph σ m).Adj x.1 y.1 ↔ x.1.1 < y.1.1 := by
      constructor
      · rintro (h | h | ⟨hxsolid, -, -⟩)
        · exact h
        · exfalso
          have := Submodule.finrank_lt_finrank_of_lt h
          rw [hys.2] at this
          omega
        · exact absurd hxsolid hx_ne_solid
      · intro h
        exact Or.inl h
    exact hleft.trans hright.symm
  · have hXx_eq : x.1.1 ⊓ L = x.1.1 :=
      inf_eq_left.2 (aResLast_nonsolid_lt E ha L hLsolid hLs hstype x hxs).le
    have hXy_eq : y.1.1 ⊓ L = y.1.1 :=
      inf_eq_left.2 (aResLast_nonsolid_lt E ha L hLsolid hLs hstype y hys).le
    rw [hXx_eq, hXy_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | ⟨hxsolid, -, -⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hxsolid (fun h => hxs ⟨x.1.2.1, h⟩)

theorem aResLast_adj_iff (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1)
    (x y : residueVertex (flagGraph σ m) flagTyp (flagChamber E m)
      {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s}) :
    (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1 <
        (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1 ∨
      (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y).1 <
        (aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x).1 ↔
      (flagGraph σ m).Adj x.1 y.1 := by
  rw [aResLast_fwd_lt_iff E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x y,
    aResLast_fwd_lt_iff E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype y x]
  exact aResLast_X_adj_iff E ha L hLsolid hLs hstype x y

noncomputable def aResLastIso (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m)
    (L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hψinj : Function.Injective ψ) (hψrange : LinearMap.range ψ = L)
    (hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x)
    (hψa : (coordBlock (m + 1) K 0 a).map ψ = (stdDChamber σ (m + 1)).toFlipFrame.sub a)
    (hLsolid : IsSolid σ L) (hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L)
    {s : Fin (m + 1)} (hLs : L = (flagChamber E m s).1) (hstype : m ≤ (s : ℕ) + 1) :
    residueGraph (flagGraph σ m) flagTyp (flagChamber E m)
        {t : Fin (m + 1) | (t : ℕ) < a ∨ t = s} ≃g
      ndGraph σ (coordBlock (m + 1) K a (m + 1)) :=
  RelIso.mk
    { toFun := aResLastFwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
      invFun := aResLastBwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
      left_inv := aResLastBwd_fwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype
      right_inv := aResLastFwd_bwd E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype }
    (fun {x y} => aResLast_adj_iff E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype x y)

theorem nonempty_residueGraph_iso_ndGraph_stem (E : QuadExt F K σ) {a b : ℕ} (hab : a ≤ b)
    (hbm : b + 2 ≤ m) :
    Nonempty (residueGraph (flagGraph σ m) flagTyp (flagChamber E m)
        {t | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b)} ≃g
      ndGraph σ (coordBlock (m + 1) K a (b + 2))) := by
  refine ⟨RelIso.mk
    { toFun := aResStemFwd E hab hbm
      invFun := aResStemBwd E hab hbm
      left_inv := aResStemBwd_fwd E hab hbm
      right_inv := aResStemFwd_bwd E hab hbm }
    (fun {x y} => (aResStem_adj_iff E hab hbm x y).symm)⟩
theorem nonempty_residueGraph_iso_ndGraph_last (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m) :
    Nonempty (residueGraph (flagGraph σ m) flagTyp (flagChamber E m)
        {t | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) + 1 ≤ m)} ≃g
      ndGraph σ (coordBlock (m + 1) K a (m + 1))) := by
  classical
  have hσ := E.isUnitary.invol
  let L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := stdLag (m + 1) K
  let ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    aResPhi (K := K) (m + 1)
  have hLsolid : IsSolid σ L :=
    ⟨aRes_isFlipflopSub_stdLag hσ (m + 1), finrank_stdLag (m + 1) K⟩
  have hψinj : Function.Injective ψ := aResPhi_injective (m + 1)
  have hψrange : LinearMap.range ψ = L := aResPhi_range (m + 1)
  have hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x :=
    fun x y => aResPhi_flipHerm (m + 1) x y
  have hψa : (coordBlock (m + 1) K 0 a).map ψ =
      (stdDChamber σ (m + 1)).toFlipFrame.sub a :=
    aResPhi_stdSub (m + 1) a (by omega)
  have hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L :=
    aRes_stdSub_le_stdLag (σ := σ) (m + 1) a
  have hLs : L = (flagChamber E m (Fin.last m)).1 := (coe_flagChamber_last E).symm
  have hstype : m ≤ ((Fin.last m : Fin (m + 1)) : ℕ) + 1 := by simp
  have hJ : {t : Fin (m + 1) | (t : ℕ) < a ∨ t = Fin.last m} =
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ (t : ℕ) + 1 ≤ m)} := by
    ext t
    simp only [Set.mem_setOf_eq, Fin.ext_iff, Fin.val_last]
    have ht : (t : ℕ) < m + 1 := t.isLt
    omega
  rw [← hJ]
  exact ⟨aResLastIso E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype⟩

theorem nonempty_residueGraph_iso_ndGraph_alt (E : QuadExt F K σ) {a : ℕ} (ha : a + 1 ≤ m) :
    Nonempty (residueGraph (flagGraph σ m) flagTyp (flagChamber E m)
        {t | ¬ (a ≤ (t : ℕ) ∧ ((t : ℕ) + 2 ≤ m ∨ (t : ℕ) = m))} ≃g
      ndGraph σ (coordBlock (m + 1) K a (m + 1))) := by
  classical
  have hσ := E.isUnitary.invol
  let L : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := (stdDChamber σ (m + 1)).alt
  let ψ : (Fin (m + 1) → K) →ₗ[K] (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    aResPhiAlt (K := K) (m + 1)
  let sm : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hLsolid : IsSolid σ L := aRes_isSolid_alt hσ
  have hψinj : Function.Injective ψ := aResPhiAlt_injective (m + 1) (by omega)
  have hψrange : LinearMap.range ψ = L := aResPhiAlt_range hσ
  have hψflip : ∀ x y, flipHerm σ (ψ x) (ψ y) = herm σ y x :=
    fun x y => aResPhiAlt_flipHerm (m + 1) (by omega) x y
  have hψa : (coordBlock (m + 1) K 0 a).map ψ =
      (stdDChamber σ (m + 1)).toFlipFrame.sub a :=
    aResPhiAlt_coordBlock (m + 1) a (by omega)
  have hTaL : (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤ L := by
    change (stdDChamber σ (m + 1)).toFlipFrame.sub a ≤
      (stdDChamber σ (m + 1)).toFlipFrame.alt
    refine le_trans (aRes_stdSub_mono (σ := σ) (d := m + 1) (i := a) (j := m) (by omega)) ?_
    unfold FlipFrame.alt
    exact le_sup_left
  have hLs : L = (flagChamber E m sm).1 :=
    (coe_flagChamber_of_succ_eq E (i := sm) (by simp only [sm]; omega)).symm
  have hstype : m ≤ (sm : ℕ) + 1 := by simp only [sm]; omega
  have hJ : {t : Fin (m + 1) | (t : ℕ) < a ∨ t = sm} =
      {t : Fin (m + 1) | ¬ (a ≤ (t : ℕ) ∧ ((t : ℕ) + 2 ≤ m ∨ (t : ℕ) = m))} := by
    ext t
    simp only [Set.mem_setOf_eq, Fin.ext_iff, sm]
    have ht : (t : ℕ) < m + 1 := t.isLt
    omega
  rw [← hJ]
  exact ⟨aResLastIso E ha L ψ hψinj hψrange hψflip hψa hLsolid hTaL hLs hstype⟩

end CFSG.ClassicalInvolution.PhanDn
