module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearSiegel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataFaithful
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearQuadratic

public section

namespace CFSG.SeitzReduction

open QuadraticMap Module

namespace OrthogonalShearAB

section Shear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsShear (Q : QuadraticForm K V) (W L : Submodule K V) (w u : V) (g : V → V) :
    Prop :=
  (∀ v ∈ L, g v = v + polar Q v u • w) ∧ ∀ v, g v - v - polar Q v w • u ∈ W

variable {Q : QuadraticForm K V} {W L : Submodule K V}

theorem isShear_zero_left (u : V) : IsShear Q W L 0 u id :=
  ⟨fun v _ => by rw [smul_zero, add_zero]; rfl, fun v => by
    rw [id, sub_self, polar_zero_right, zero_smul, sub_zero]; exact W.zero_mem⟩

theorem IsShear.of_sub_mem (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {w u u' : V}
    {g : V → V} (h : IsShear Q W L w u g) (hu : u' - u ∈ W) : IsShear Q W L w u' g := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h0 : polar Q v (u' - u) = 0 := by rw [polar_comm]; exact (hL v).1 hv _ hu
    rw [h.1 v hv, show u' = u + (u' - u) by abel, polar_add_right, h0, add_zero]
  · have e : g v - v - polar Q v w • u' =
        (g v - v - polar Q v w • u) - polar Q v w • (u' - u) := by
      rw [smul_sub]; abel
    rw [e]
    exact W.sub_mem (h.2 v) (W.smul_mem _ hu)

theorem IsShear.neg {w u : V} {g : V → V} (h : IsShear Q W L w (-u) g) :
    IsShear Q W L (-w) u g := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [h.1 v hv, polar_neg_right, neg_smul, smul_neg]
  · have h2 := h.2 v
    rw [smul_neg, sub_neg_eq_add] at h2
    rw [polar_neg_right, neg_smul, sub_neg_eq_add]
    exact h2

theorem IsShear.comp (hWL : W ≤ L) (hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0)
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {w₁ w₂ u : V} (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W)
    (hu : u ∈ L) {g₁ g₂ : V → V} (h₁ : IsShear Q W L w₁ u g₁) (h₂ : IsShear Q W L w₂ u g₂) :
    IsShear Q W L (w₁ + w₂) u (g₁ ∘ g₂) := by
  have hw₂u : polar Q w₂ u = 0 := (hL u).1 hu w₂ hw₂
  have huw₁ : polar Q u w₁ = 0 := by rw [polar_comm]; exact (hL u).1 hu w₁ hw₁
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hg₂ : g₂ v ∈ L := by
      rw [h₂.1 v hv]
      exact L.add_mem hv (L.smul_mem _ (hWL hw₂))
    rw [Function.comp_apply, h₁.1 _ hg₂, h₂.1 v hv, polar_add_left, polar_smul_left, hw₂u,
      smul_zero, add_zero, smul_add]
    abel
  · set h := g₂ v - v - polar Q v w₂ • u with hh
    have hg : polar Q (g₂ v) w₁ = polar Q v w₁ := by
      have e : g₂ v = v + (h + polar Q v w₂ • u) := by rw [hh]; abel
      rw [e, polar_add_left, polar_add_left, polar_smul_left, hWiso h (h₂.2 v) w₁ hw₁, huw₁,
        smul_zero, add_zero, add_zero]
    have e2 : (g₁ ∘ g₂) v - v - polar Q v (w₁ + w₂) • u =
        (g₁ (g₂ v) - g₂ v - polar Q (g₂ v) w₁ • u) + h := by
      rw [hh, Function.comp_apply, hg, polar_add_right, add_smul]
      abel
    rw [e2]
    exact W.add_mem (h₁.2 _) (h₂.2 v)

theorem IsShear.congr_left {w w' u : V} {g : V → V} (h : IsShear Q W L w u g) (hw : w = w') :
    IsShear Q W L w' u g :=
  hw ▸ h

theorem isShear_eichler [CharP K 2] (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {w u : V}
    (hw : w ∈ W) (hQw : Q w = 0) (hu : u ∈ L) :
    IsShear Q W L w u (CFSG.ClassicalGroups.Orthogonal.eichler Q w u) :=
  eichler_shear hL hw hQw hu

end Shear

section OrderThree

open CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 2]
  {Q : QuadraticForm K V} {W L : Submodule K V}

theorem pow_two_pow_apply_add (g : V ≃ₗ[K] V) {w : V} (h : g (g w) + g w + w = 0) (k : ℕ) :
    (g ^ 2 ^ k) ((g ^ 2 ^ k) w) + (g ^ 2 ^ k) w + w = 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    set f := g ^ 2 ^ k with hf
    have e1 : f (f w) = f w + w := by
      rw [← CFSG.RankThree.OrthogonalInvolutions.neg_vec_eq K (f w + w)]
      exact eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact ih)
    have e2 : f (f (f w)) = w := by
      rw [e1, map_add, e1, add_comm (f w) w, add_assoc,
        CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, add_zero]
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul, ← hf, _root_.sq,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2, e1, ← add_assoc,
      CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, zero_add,
      CFSG.RankThree.OrthogonalInvolutions.add_self_vec K]

theorem eichler_mul_eichler_apply_add {w w' x x' : V} (hQw : Q w = 0) (hQw' : Q w' = 0)
    (hwx : polar Q w x = 0) (hwx' : polar Q w' x' = 0) (hww' : polar Q w w' = 0)
    (h1 : polar Q w x' = 1) (h2 : polar Q w' x = 1) :
    (eichler Q w x * eichler Q w' x') ((eichler Q w x * eichler Q w' x') w) +
      (eichler Q w x * eichler Q w' x') w + w = 0 := by
  have hw'w : polar Q w' w = 0 := by rw [polar_comm]; exact hww'
  have hww : polar Q w w = 0 := CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q w
  have hw'w' : polar Q w' w' = 0 := CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q w'
  have e2w : eichler Q w' x' w = w + w' := by
    rw [eichler_apply hQw' hwx', hww', h1, zero_smul, add_zero, mul_zero, add_zero, one_smul,
      CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K]
  have e1 : eichler Q w x (w + w') = w' := by
    rw [eichler_apply hQw hwx, polar_add_left, polar_add_left, hww, hw'w, hwx, h2, add_zero,
      zero_smul, add_zero, mul_zero, add_zero, zero_add, one_smul, add_sub_cancel_left]
  have e2w' : eichler Q w' x' w' = w' := eichler_apply_self w' x'
  have e1w' : eichler Q w x w' = w' + w := by
    rw [eichler_apply hQw hwx, hw'w, h2, zero_smul, add_zero, mul_zero, add_zero, one_smul,
      CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K]
  have hg : (eichler Q w x * eichler Q w' x') w = w' := by rw [LinearEquiv.mul_apply, e2w, e1]
  rw [hg, LinearEquiv.mul_apply, e2w', e1w',
    show w' + w + w' + w = (w' + w') + (w + w) by abel,
    CFSG.RankThree.OrthogonalInvolutions.add_self_vec K,
    CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, add_zero]

omit [CharP K 2] in
theorem eichler_sub_mem (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {a : V} (ha : a ∈ W)
    (b : V) {u : V} (hu : u ∈ L) : eichler Q a b u - u ∈ W := by
  by_cases h : Q a = 0 ∧ polar Q a b = 0
  · have hua : polar Q u a = 0 := by rw [polar_comm]; exact (hL u).1 hu a ha
    rw [eichler_apply h.1 h.2, hua, zero_smul, add_zero, mul_zero, add_zero, sub_sub_cancel_left]
    exact W.neg_mem (W.smul_mem _ ha)
  · rw [eichler_of_not h, LinearEquiv.coe_one, id, sub_self]
    exact W.zero_mem

omit [CharP K 2] in
theorem sub_mem_comp (hWL : W ≤ L) {f g : V → V} (hf : ∀ u ∈ L, f u - u ∈ W)
    (hg : ∀ u ∈ L, g u - u ∈ W) {u : V} (hu : u ∈ L) : f (g u) - u ∈ W := by
  have hgu : g u ∈ L := by
    have h := L.add_mem (hWL (hg u hu)) hu
    rwa [sub_add_cancel] at h
  rw [show f (g u) - u = (f (g u) - g u) + (g u - u) by abel]
  exact W.add_mem (hf _ hgu) (hg u hu)

omit [CharP K 2] in
theorem pow_sub_mem (hWL : W ≤ L) {g : V ≃ₗ[K] V} (hg : ∀ u ∈ L, g u - u ∈ W) (n : ℕ) {u : V}
    (hu : u ∈ L) : (g ^ n) u - u ∈ W := by
  induction n generalizing u with
  | zero => rw [pow_zero, LinearEquiv.coe_one, id, sub_self]; exact W.zero_mem
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply]
    exact sub_mem_comp hWL (fun v hv => ih hv) hg hu

omit [CharP K 2] in
theorem mem_of_sub_mem (hWL : W ≤ L) {f : V → V} (hf : ∀ u ∈ L, f u - u ∈ W) :
    (∀ v ∈ W, f v ∈ W) ∧ ∀ v ∈ L, f v ∈ L := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have h := W.add_mem (hf v (hWL hv)) hv
    rwa [sub_add_cancel] at h
  · have h := L.add_mem (hWL (hf v hv)) hv
    rwa [sub_add_cancel] at h

omit [CharP K 2] in
theorem eichler_mul_comm {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a b : V} (hQa : Q a = 0) (ha : g a = a) (c : K) (hb : g b = b + c • a) :
    eichler Q a b * g = g * eichler Q a b := by
  have h1 := eichler_conj hg a b
  rw [ha, hb, eichler_add_smul_self hQa, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

end OrderThree

section Types

open CFSG.RankThree.OrthogonalInvolutions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_pair_of_two_le_finrank [FiniteDimensional K V] {S : Submodule K V}
    (hS : 2 ≤ finrank K S) : ∃ w₁ ∈ S, ∃ w₂ ∈ S, LinearIndependent K ![w₁, w₂] := by
  have hS0 : S ≠ ⊥ := by
    rintro rfl
    simp at hS
  rcases ShearRigidity.exists_pair_or_eq_span hS0 with h | ⟨w₀, hw₀, rfl⟩
  · exact h
  · rw [finrank_span_singleton hw₀] at hS
    omega

theorem finrank_le_finrank_singularSubspace_add_one [Finite K] [CharP K 2]
    [FiniteDimensional K V] {W : Submodule K V} (hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) :
    finrank K W ≤ finrank K (singularSubspace Q W hWiso) + 1 := by
  by_cases h : ∀ x ∈ W, Q x = 0
  · have he : singularSubspace Q W hWiso = W :=
      le_antisymm (fun x hx => hx.1) (fun x hx => ⟨hx, h x hx⟩)
    rw [he]
    omega
  push Not at h
  obtain ⟨h₀, hh₀, hQh₀⟩ := h
  have hh₀0 : h₀ ≠ 0 := by
    rintro rfl
    exact hQh₀ (QuadraticMap.map_zero Q)
  have hle : W ≤ singularSubspace Q W hWiso ⊔ K ∙ h₀ := by
    intro x hx
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q x / Q h₀)
    have hmem : x + r • h₀ ∈ singularSubspace Q W hWiso := by
      refine ⟨W.add_mem hx (W.smul_mem r hh₀), ?_⟩
      rw [QuadraticMap.map_add Q x (r • h₀), QuadraticMap.map_smul, hWiso x hx _ (W.smul_mem r hh₀),
        add_zero,
        smul_eq_mul, ← hr, div_mul_cancel₀ _ hQh₀, CharTwo.add_self_eq_zero]
    have e : x = (x + r • h₀) + (-r) • h₀ := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.add_mem_sup hmem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self h₀))
  calc finrank K W ≤ finrank K ↥(singularSubspace Q W hWiso ⊔ K ∙ h₀) := Submodule.finrank_mono hle
    _ ≤ finrank K (singularSubspace Q W hWiso) + finrank K (K ∙ h₀) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = finrank K (singularSubspace Q W hWiso) + 1 := by rw [finrank_span_singleton hh₀0]

variable {t : V ≃ₗ[K] V}

theorem wall_of_forall_eq_zero (hQ : Q.polarBilin.Nondegenerate)
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hzero : ∀ x ∈ commSpace t, Q x = 0) :
    ∀ y, (∀ w ∈ commSpace t, Q w = 0 → polar Q y w = 0) → Q (t y - y) = 0 → t y - y = 0 := by
  intro y hy _
  have hyL : y ∈ fixSpace t := by
    rw [fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    change polar Q w y = 0
    rw [polar_comm]
    exact hy w hw (hzero w hw)
  rw [mem_fixSpace.mp hyL, sub_self]

theorem wall_of_odd [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) (hodd : Odd (finrank K (commSpace t))) :
    ∀ y, (∀ w ∈ commSpace t, Q w = 0 → polar Q y w = 0) → Q (t y - y) = 0 → t y - y = 0 := by
  intro y hy hQy
  set L := fixSpace t with hLdef
  set Bt := wallForm Q t with hBtdef
  have hsymm : ∀ a b, Bt a b = Bt b a := wallForm_symm ht htt
  have hrefl : Bt.IsRefl := (wallForm_isSymm ht htt).isRefl
  have hWiso : ∀ x ∈ commSpace t, ∀ z ∈ commSpace t, polar Q x z = 0 := fun x hx z hz =>
    polar_commSpace_eq_zero ht htt hx hz
  set Y₀ : Submodule K V :=
    (singularSubspace Q (commSpace t) hWiso).comap ((t : V →ₗ[K] V) - 1) with hY₀def
  have hY : ∀ a, a ∈ Y₀ ↔ Q (t a - a) = 0 := fun a =>
    ⟨fun h => h.2, fun h => ⟨LinearMap.mem_range_self _ a, h⟩⟩
  have hLY : L ≤ Y₀ := fun a ha =>
    (hY a).2 (by rw [mem_fixSpace.mp ha, sub_self, QuadraticMap.map_zero])
  have hrad : Bt.orthogonal ⊤ = L := by
    ext a
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact mem_fixSpace_of_wallForm hQ ht htt fun b => by rw [hsymm]; exact h b Submodule.mem_top
    · intro ha b _
      exact wallForm_apply_fixSpace Q b ha
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, Q (t a₀ - a₀) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact (Nat.not_even_iff_odd.mpr hodd) (even_finrank_commSpace_of_forall_eq_zero hQ ht htt
      fun x hx => by obtain ⟨v, rfl⟩ := mem_commSpace.mp hx; exact hc v)
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero, QuadraticMap.map_zero] at ha₀
    exact ha₀ rfl
  have hsup : Y₀ ⊔ K ∙ a₀ = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
      (Q (t a - a) / Q (t a₀ - a₀))
    have hmem : a + r • a₀ ∈ Y₀ := (hY _).2 (by
      rw [map_add, map_smul, show t a + r • t a₀ - (a + r • a₀) = (t a - a) + r • (t a₀ - a₀) by
          rw [smul_sub]; abel,
        QuadraticMap.map_add Q (t a - a) (r • (t a₀ - a₀)), QuadraticMap.map_smul,
        hWiso _ (sub_mem_commSpace t a) _ (Submodule.smul_mem _ _ (sub_mem_commSpace t a₀)),
        add_zero, smul_eq_mul, ← hr, div_mul_cancel₀ _ ha₀, CharTwo.add_self_eq_zero])
    have e : a = (a + r • a₀) + (-r) • a₀ := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.add_mem_sup hmem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a₀))
  have hY₀ : finrank K Y₀ + 1 = finrank K V := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank Y₀ (K ∙ a₀)
    rw [hsup, finrank_top, finrank_span_singleton ha₀0] at h1
    have h2 : finrank K Y₀ < finrank K V :=
      Submodule.finrank_lt fun h => ha₀ ((hY a₀).1 (h ▸ Submodule.mem_top))
    omega
  have hperp : finrank K (Bt.orthogonal Y₀) = finrank K L + 1 := by
    have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl Y₀
    rw [hrad, inf_eq_right.mpr hLY] at h
    omega
  set B₀ := Bt.restrict Y₀ with hB₀def
  set R := B₀.orthogonal ⊤ with hRdef
  obtain ⟨Z, hZ⟩ := R.exists_isCompl
  have hsepZ : (B₀.restrict Z).SeparatingLeft := by
    intro z hz
    have hzR : (z : Y₀) ∈ R := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro b _
      have hb : b ∈ R ⊔ Z := by rw [hZ.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨r, hr, z', hz', rfl⟩ := Submodule.mem_sup.mp hb
      have h1 : B₀ r z = 0 := by
        have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) z Submodule.mem_top
        change Bt z r = 0 at this
        change Bt r z = 0
        rw [hsymm]
        exact this
      have h2 : B₀ z' z = 0 := by
        have := hz ⟨z', hz'⟩
        change Bt z z' = 0 at this
        change Bt z' z = 0
        rw [hsymm]
        exact this
      change B₀ (r + z') z = 0
      rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
    exact Subtype.ext (Submodule.disjoint_def.mp hZ.disjoint _ hzR z.2)
  have hZnd : (B₀.restrict Z).Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (((wallForm_isSymm ht htt).restrict Y₀).restrict Z).isRefl).mpr hsepZ
  have hZalt : (B₀.restrict Z).IsAlt := fun z => by
    change Bt z z = 0
    rw [hBtdef, wallForm_self ht]
    exact (hY _).1 (z : Y₀).2
  have hZeven : Even (finrank K Z) := LinearMap.BilinForm.IsAlt.even_finrank hZalt hZnd
  have hRZ : finrank K R + finrank K Z = finrank K Y₀ := Submodule.finrank_add_eq_of_isCompl hZ
  have hLR : L.comap Y₀.subtype ≤ R := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b _
    change Bt b a = 0
    exact wallForm_apply_fixSpace Q b ha
  have hfinL : finrank K (L.comap Y₀.subtype) = finrank K L :=
    (Submodule.comapSubtypeEquivOfLe hLY).finrank_eq
  have hRle : R.map Y₀.subtype ≤ Bt.orthogonal Y₀ := by
    rintro _ ⟨r, hr, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hr) ⟨b, hb⟩ Submodule.mem_top
  have hfinR : finrank K R ≤ finrank K L + 1 := by
    have h := Submodule.finrank_mono hRle
    rw [Submodule.finrank_map_subtype_eq, hperp] at h
    exact h
  have hfinLR : finrank K L ≤ finrank K R := hfinL ▸ Submodule.finrank_mono hLR
  have hVWL := finrank_commSpace_add_finrank_fixSpace t
  rw [← hLdef] at hVWL
  obtain ⟨a, ha⟩ := hZeven
  obtain ⟨b, hb⟩ := hodd
  have hRL : finrank K R = finrank K L := by omega
  have hReq : L.comap Y₀.subtype = R :=
    Submodule.eq_of_le_of_finrank_eq hLR (by rw [hfinL, hRL])
  have hyR : (⟨y, (hY y).2 hQy⟩ : Y₀) ∈ R := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b _
    change Bt b y = 0
    rw [hsymm, hBtdef, wallForm_apply]
    exact hy _ (sub_mem_commSpace t b) ((hY b).1 b.2)
  rw [← hReq] at hyR
  have hyL : y ∈ fixSpace t := hyR
  rw [mem_fixSpace.mp hyL, sub_self]

end Types

section Model

open CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem pow_two_eq_one_of_semilinear [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (s : matrixIsometries Q)
    (h : ∀ x : similarityPairs Q, x ∈ unitMultiplierPairs Q →
      (∀ v, coordinateSemilinearMap x.val (matrixLinearEquiv (s : GL (Fin d) K) v) =
        matrixLinearEquiv (s : GL (Fin d) K) (coordinateSemilinearMap x.val v)) →
      (∀ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
          A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)}, ∀ v,
        coordinateSemilinearMap x.val (matrixLinearEquiv A v) =
          matrixLinearEquiv A (coordinateSemilinearMap x.val v)) →
      ∀ v, coordinateSemilinearMap x.val (coordinateSemilinearMap x.val v) = v) :
    ∀ β ∈ matrixProjectiveImage Q,
      β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) * β →
      (∀ c, matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) c = c →
        Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  intro β hβ hβx hβc
  have hd : 1 ≤ d := by
    obtain ⟨T, hT3, -⟩ := hT
    have h3 := Submodule.finrank_le T
    rw [hT3, Module.finrank_fin_fun] at h3
    omega
  have hQ0 := exists_ne_zero_of_polar_nondegenerate hd hQ
  have hβ' : β ∈ (unitKappa Q).range := by rw [range_unitKappa]; exact hβ
  obtain ⟨x, rfl⟩ := hβ'
  set σ := matrixIsometryInclusion Q s with hσdef
  have hσ : σ ∈ unitMultiplierPairs Q := fun v => by
    rw [hσdef, matrixIsometryInclusion_val, coordinateSemilinearMap_inl]
    exact (mem_matrixIsometries_iff Q s.val).mp s.2 v
  set T := coordinateSemilinearMap x.1.val with hTdef
  have hxσ : x.1 * σ = σ * x.1 := by
    have h2 : matrixProjectiveConjugationHom Q ((x.1 * σ) * (σ * x.1)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul]
      change unitKappa Q x * matrixProjectiveConjugationHom Q σ *
        (matrixProjectiveConjugationHom Q σ * unitKappa Q x)⁻¹ = 1
      rw [hβx, mul_inv_cancel]
    exact mul_inv_eq_one.mp (eq_one_of_kappa_eq_one Q hQ hT hE hd
      (mul_mem (mul_mem x.2 hσ) (inv_mem (mul_mem hσ x.2))) h2)
  have hTs : ∀ v, T (matrixLinearEquiv (s : GL (Fin d) K) v) =
      matrixLinearEquiv (s : GL (Fin d) K) (T v) := fun v => by
    have h5 := congrArg (fun y : similarityPairs Q => coordinateSemilinearMap y.val v) hxσ
    simp only [Subgroup.coe_mul, coordinateSemilinearMap_mul, hσdef, matrixIsometryInclusion_val,
      coordinateSemilinearMap_inl] at h5
    exact h5
  have hπ : Function.Injective (matrixProjectiveProjection Q) := by
    rw [← MonoidHom.ker_eq_bot_iff, matrixProjectiveProjection, QuotientGroup.ker_mk']
    exact matrixDerivedScalars_eq_bot_of_charTwo Q hQ0
  have hgen : ∀ A : GL (Fin d) K, A ∈ matrixDerived Q → A * (s : GL (Fin d) K) = s * A →
      Odd (orderOf A) → ∀ v, T (matrixLinearEquiv A v) = matrixLinearEquiv A (T v) := by
    intro A hA hAs hAo v
    set a : matrixDerived Q := ⟨A, hA⟩ with ha
    have hκa : matrixProjectiveConjugationHom Q σ (matrixProjectiveProjection Q a) =
        matrixProjectiveProjection Q a := by
      change matrixProjectiveConjugation Q σ (matrixProjectiveProjection Q a) = _
      rw [matrixProjectiveConjugation_mk]
      congr 1
      apply Subtype.ext
      rw [matrixDerivedConjugation_val]
      simp only [hσdef, matrixIsometryInclusion_val, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply]
      rw [ha, ← hAs, mul_inv_cancel_right]
    have hoa : Odd (orderOf (matrixProjectiveProjection Q a)) :=
      hAo.of_dvd_nat ((orderOf_map_dvd _ a).trans (by rw [ha, Subgroup.orderOf_mk]))
    have h1 := hβc _ hκa hoa
    change matrixProjectiveConjugation Q x.1 (matrixProjectiveProjection Q a) = _ at h1
    rw [matrixProjectiveConjugation_mk] at h1
    have h2 := congrArg Subtype.val (hπ h1)
    rw [matrixDerivedConjugation_val] at h2
    have h3 := matrixConjugation_vector x.1.val A (T v)
    rw [matrixConjugation_apply, h2, AddEquiv.symm_apply_apply] at h3
    exact h3.symm
  have hD : ∀ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
      A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)}, ∀ v,
      T (matrixLinearEquiv A v) = matrixLinearEquiv A (T v) := by
    intro A hA
    induction hA using Subgroup.closure_induction with
    | mem A hA => exact hgen A hA.1 hA.2.1 hA.2.2
    | one => intro v; simp [matrixLinearEquiv_apply]
    | mul A B _ _ hA hB =>
      intro v
      rw [matrixLinearEquiv_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hA, hB]
    | inv A _ hA =>
      intro v
      have e : ∀ y, matrixLinearEquiv A (matrixLinearEquiv A⁻¹ y) = y := fun y => by
        rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, mul_inv_cancel]
        simp [matrixLinearEquiv_apply]
      apply (matrixLinearEquiv A).injective
      rw [e, ← hA, e]
  have hTT := h x.1 x.2 hTs hD
  have hx2 : x.1.val * x.1.val = 1 := by
    apply coordinateSemilinearHom_injective hd
    change Multiplicative.ofAdd (coordinateSemilinearMap (x.1.val * x.1.val)) =
      Multiplicative.ofAdd (coordinateSemilinearMap 1)
    congr 1
    exact AddEquiv.ext fun v => by
      rw [coordinateSemilinearMap_mul, hTT, coordinateSemilinearMap_one]
  have hx2' : x * x = 1 := Subtype.ext (Subtype.ext hx2)
  rw [_root_.sq, ← map_mul, hx2', map_one]

theorem exists_shear_mem_closure_of_partner [Finite K] [CharP K 2]
    (hQ : Q.polarBilin.Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : matrixIsometries Q} (hss : s * s = 1) {x w'₀ u : Fin d → K}
    (hQw : Q (matrixLinearEquiv (s : GL (Fin d) K) x - x) = 0)
    (hw'₀ : w'₀ ∈
      CFSG.RankThree.OrthogonalInvolutions.commSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hQw'₀ : Q w'₀ = 0) (hc : polar Q x w'₀ ≠ 0)
    (hu : u ∈
      CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K))) :
    ∃ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
        A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)},
      IsShear Q (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (matrixLinearEquiv (s : GL (Fin d) K)))
        (CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
        (matrixLinearEquiv (s : GL (Fin d) K) x - x) u (matrixLinearEquiv A) := by
  open CFSG.RankThree.OrthogonalInvolutions in
  set t := matrixLinearEquiv (s : GL (Fin d) K) with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have htt : t * t = 1 := by
    rw [htdef, ← matrixLinearEquiv_mul, ← Subgroup.coe_mul, hss, Subgroup.coe_one]
    ext v
    simp [matrixLinearEquiv_apply]
  set W := commSpace t with hWdef
  set L := fixSpace t with hLdef
  have hWL : W ≤ L := commSpace_le_fixSpace htt
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  have hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0 := fun v => by
    rw [hLdef, fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hfixW : ∀ v ∈ W, t v = v := fun v hv => mem_fixSpace.mp (hWL hv)
  have hmat : ∀ g : (Fin d → K) ≃ₗ[K] (Fin d → K), g ∈ elementaryGroup Q → g * t = t * g →
      matrixLinearIso.symm g ∈ matrixDerived Q ∧
        matrixLinearIso.symm g * (s : GL (Fin d) K) = s * matrixLinearIso.symm g := by
    intro g hg hgt
    refine ⟨?_, ?_⟩
    · rw [CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff,
        MulEquiv.apply_symm_apply, hE]
      exact hg
    · apply matrixLinearIso.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hgt
  obtain ⟨w, hx⟩ : ∃ w, t x - x = w := ⟨_, rfl⟩
  rw [hx] at hQw ⊢
  have hw : w ∈ W := hx ▸ sub_mem_commSpace t x
  set w' := (polar Q x w'₀)⁻¹ • w'₀ with hw'def
  have hw' : w' ∈ W := W.smul_mem _ hw'₀
  have hQw' : Q w' = 0 := by rw [hw'def, QuadraticMap.map_smul, hQw'₀, smul_zero]
  have hxw' : polar Q x w' = 1 := by
    rw [hw'def, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hc]
  obtain ⟨x', hx'⟩ := mem_commSpace.mp hw'
  have hpol0 : ∀ z, Q (t z - z) = 0 → polar Q (t z - z) z = 0 := fun z hz => by
    rw [polar_sub_left, polar_self_eq_zero Q z, sub_zero, ← map_sub_eq_polar ht, hz]
  have hwx : polar Q w x = 0 := by rw [← hx]; exact hpol0 x (by rw [hx]; exact hQw)
  have hwx' : polar Q w' x' = 0 := by rw [← hx']; exact hpol0 x' (by rw [hx']; exact hQw')
  have hww' : polar Q w w' = 0 := hWiso w hw w' hw'
  have h1 : polar Q w x' = 1 := by rw [← hx, polar_sub_eq_polar_sub ht htt, hx', hxw']
  have h2 : polar Q w' x = 1 := by rw [polar_comm, hxw']
  have hcomm₁ : eichler Q w x * t = t * eichler Q w x :=
    eichler_mul_comm ht hQw (hfixW w hw) 1 (by rw [one_smul, ← hx]; abel)
  have hcomm₂ : eichler Q w' x' * t = t * eichler Q w' x' :=
    eichler_mul_comm ht hQw' (hfixW w' hw') 1 (by rw [one_smul, ← hx']; abel)
  set g := eichler Q w x * eichler Q w' x' with hgdef
  have hgE : g ∈ elementaryGroup Q :=
    mul_mem (eichler_mem_elementaryGroup Q w x) (eichler_mem_elementaryGroup Q w' x')
  have hgt : g * t = t * g := by
    rw [hgdef, mul_assoc, hcomm₂, ← mul_assoc, hcomm₁, mul_assoc]
  have hgL : ∀ v ∈ L, g v - v ∈ W := fun v hv =>
    sub_mem_comp hWL (fun u hu => eichler_sub_mem hL hw x hu)
      (fun u hu => eichler_sub_mem hL hw' x' hu) hv
  have hgw : g (g w) + g w + w = 0 :=
    eichler_mul_eichler_apply_add hQw hQw' hwx hwx' hww' h1 h2
  obtain ⟨hGD, hGs⟩ := hmat g hgE hgt
  set G := matrixLinearIso.symm g with hGdef
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos G).ne'
  set Y := G ^ 2 ^ k with hYdef
  have hYo : Odd (orderOf Y) := by
    rw [hYdef, orderOf_pow_of_dvd (by positivity) (Dvd.intro m hkm.symm), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hYD : Y ∈ matrixDerived Q := pow_mem hGD _
  have hYs : Y * (s : GL (Fin d) K) = s * Y := ((Commute.pow_left hGs) _).eq
  set y := g ^ 2 ^ k with hydef
  have hyY : matrixLinearIso Y = y := by rw [hYdef, map_pow, hGdef, MulEquiv.apply_symm_apply]
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    pow_mem (mul_mem (eichler_mem_orthogonalGroup Q w x) (eichler_mem_orthogonalGroup Q w' x')) _
  have hyt : y * t = t * y := ((Commute.pow_left hgt) _).eq
  have hyL : ∀ v ∈ L, y v - v ∈ W := fun v hv => pow_sub_mem hWL hgL _ hv
  have hyW := (mem_of_sub_mem hWL hyL).1
  have hyLL := (mem_of_sub_mem hWL hyL).2
  have hyw : y (y w) + y w + w = 0 := pow_two_pow_apply_add g hgw k
  have hw₁ : y w ∈ W := hyW w hw
  have hQw₁ : Q (y w) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hyO w, hQw]
  have hw₂ : y (y w) ∈ W := hyW _ hw₁
  have hQw₂ : Q (y (y w)) = 0 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hyO, hQw₁]
  have hw₁u : polar Q (y w) u = 0 := (hL u).1 hu _ hw₁
  have hcomme : eichler Q (y w) u * t = t * eichler Q (y w) u :=
    eichler_mul_comm ht hQw₁ (hfixW _ hw₁) 0 (by rw [zero_smul, add_zero]; exact mem_fixSpace.mp hu)
  obtain ⟨hED, hEs⟩ := hmat _ (eichler_mem_elementaryGroup Q (y w) u) hcomme
  set E := matrixLinearIso.symm (eichler Q (y w) u) with hEdef
  have hA₁ : E * Y * E⁻¹ ∈ {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
      A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)} := by
    refine ⟨mul_mem (mul_mem hED hYD) (inv_mem hED), ?_, ?_⟩
    · have hc1 : Commute E (s : GL (Fin d) K) := hEs
      have hc2 : Commute Y (s : GL (Fin d) K) := hYs
      exact ((hc1.mul_left hc2).mul_left hc1.inv_left).eq
    · rw [show E * Y * E⁻¹ = MulAut.conj E Y from rfl, MulEquiv.orderOf_eq]
      exact hYo
  refine ⟨E * Y * E⁻¹ * Y⁻¹, mul_mem (Subgroup.subset_closure hA₁)
    (inv_mem (Subgroup.subset_closure ⟨hYD, hYs, hYo⟩)), ?_⟩
  have hinv : (eichler Q (y w) u)⁻¹ = eichler Q (y w) (-u) := eichler_inv hw₁u
  have hconj : y * eichler Q (y w) (-u) * y⁻¹ = eichler Q (y (y w)) (-(y u)) := by
    rw [eichler_conj hyO, map_neg]
  have hfun : ⇑(matrixLinearEquiv (E * Y * E⁻¹ * Y⁻¹)) =
      ⇑(eichler Q (y w) u) ∘ ⇑(eichler Q (y (y w)) (-(y u))) := by
    funext v
    change matrixLinearIso (E * Y * E⁻¹ * Y⁻¹) v = _
    rw [map_mul, map_mul, map_inv, map_mul, map_inv, hyY, hEdef, MulEquiv.apply_symm_apply,
      hinv, mul_assoc, mul_assoc, ← mul_assoc y, hconj, LinearEquiv.mul_apply]
    rfl
  rw [hfun]
  have hyu : y u - u ∈ W := hyL u hu
  have hsh₁ : IsShear Q W L (y w) u (eichler Q (y w) u) := isShear_eichler hL hw₁ hQw₁ hu
  have hsh₂ : IsShear Q W L (-(y (y w))) u (eichler Q (y (y w)) (-(y u))) := by
    refine (IsShear.of_sub_mem hL (isShear_eichler hL hw₂ hQw₂ (L.neg_mem (hyLL u hu))) ?_).neg
    rw [sub_neg_eq_add, add_comm]
    rw [← sub_eq_add_neg]
    exact hyu
  refine (IsShear.comp hWL hWiso hL hw₁ (W.neg_mem hw₂) hu hsh₁ hsh₂).congr_left ?_
  have e : y (y w) + y w = -w := eq_neg_of_add_eq_zero_left hyw
  rw [neg_vec_eq K w] at e
  rw [neg_vec_eq K (y (y w)), add_comm]
  exact e

theorem exists_shear_mem_closure_add [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    {s : matrixIsometries Q} (hss : s * s = 1) {w₁ w₂ u : Fin d → K}
    (hw₁ : w₁ ∈
      CFSG.RankThree.OrthogonalInvolutions.commSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hw₂ : w₂ ∈
      CFSG.RankThree.OrthogonalInvolutions.commSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hu : u ∈ CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (h₁ : ∃ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
        A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)},
      IsShear Q (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (matrixLinearEquiv (s : GL (Fin d) K)))
        (CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
        w₁ u (matrixLinearEquiv A))
    (h₂ : ∃ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
        A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)},
      IsShear Q (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (matrixLinearEquiv (s : GL (Fin d) K)))
        (CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
        w₂ u (matrixLinearEquiv A)) :
    ∃ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
        A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)},
      IsShear Q (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (matrixLinearEquiv (s : GL (Fin d) K)))
        (CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
        (w₁ + w₂) u (matrixLinearEquiv A) := by
  open CFSG.RankThree.OrthogonalInvolutions in
  set t := matrixLinearEquiv (s : GL (Fin d) K) with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have htt : t * t = 1 := by
    rw [htdef, ← matrixLinearEquiv_mul, ← Subgroup.coe_mul, hss, Subgroup.coe_one]
    ext v
    simp [matrixLinearEquiv_apply]
  have hL : ∀ v, v ∈ fixSpace t ↔ ∀ w ∈ commSpace t, polar Q w v = 0 := fun v => by
    rw [fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  obtain ⟨A₁, hA₁, hs₁⟩ := h₁
  obtain ⟨A₂, hA₂, hs₂⟩ := h₂
  refine ⟨A₁ * A₂, mul_mem hA₁ hA₂, ?_⟩
  have hfun : ⇑(matrixLinearEquiv (A₁ * A₂)) =
      ⇑(matrixLinearEquiv A₁) ∘ ⇑(matrixLinearEquiv A₂) := by
    funext v
    rw [matrixLinearEquiv_mul, LinearEquiv.mul_apply]
    rfl
  rw [hfun]
  exact IsShear.comp (commSpace_le_fixSpace htt)
    (fun x hx y hy => polar_commSpace_eq_zero ht htt hx hy) hL hw₁ hw₂ hu hs₁ hs₂

theorem exists_shear_mem_closure [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : matrixIsometries Q} (hss : s * s = 1)
    (hb : ∀ y, (∀ w ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)), Q w = 0 → polar Q y w = 0) →
      Q (matrixLinearEquiv (s : GL (Fin d) K) y - y) = 0 →
        matrixLinearEquiv (s : GL (Fin d) K) y - y = 0)
    {w u : Fin d → K}
    (hw : w ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hQw : Q w = 0)
    (hu : u ∈
      CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K))) :
    ∃ A ∈ Subgroup.closure {A : GL (Fin d) K | A ∈ matrixDerived Q ∧
        A * (s : GL (Fin d) K) = s * A ∧ Odd (orderOf A)},
      IsShear Q (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (matrixLinearEquiv (s : GL (Fin d) K)))
        (CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
        w u (matrixLinearEquiv A) := by
  by_cases hw0 : w = 0
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    subst hw0
    have h1 : ⇑(matrixLinearEquiv (1 : GL (Fin d) K)) = id := by
      funext v
      simp [matrixLinearEquiv_apply]
    rw [h1]
    exact isShear_zero_left u
  obtain ⟨x, hx⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hw
  have hnb : ¬ ∀ w' ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
      (matrixLinearEquiv (s : GL (Fin d) K)), Q w' = 0 → polar Q x w' = 0 := fun hall =>
    hw0 (by rw [← hx]; exact hb x hall (by rw [hx]; exact hQw))
  push Not at hnb
  obtain ⟨w'₀, hw'₀, hQw'₀, hc⟩ := hnb
  have h := exists_shear_mem_closure_of_partner hQ hE hss (x := x) (by rw [hx]; exact hQw) hw'₀
    hQw'₀ hc hu
  rw [hx] at h
  exact h

theorem pow_two_eq_one_of_kappa_of_wall [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : matrixIsometries Q} (hss : s * s = 1)
    (hWL : CFSG.RankThree.OrthogonalInvolutions.commSpace (matrixLinearEquiv (s : GL (Fin d) K)) ≠
      CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hb : ∀ y, (∀ w ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)), Q w = 0 → polar Q y w = 0) →
      Q (matrixLinearEquiv (s : GL (Fin d) K) y - y) = 0 →
        matrixLinearEquiv (s : GL (Fin d) K) y - y = 0)
    (hW2 : ∃ w₁ ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)),
      ∃ w₂ ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)),
        Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]) :
    ∀ β ∈ matrixProjectiveImage Q,
      β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) * β →
      (∀ c, matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) c = c →
        Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  open CFSG.RankThree.OrthogonalInvolutions in
  refine pow_two_eq_one_of_semilinear hQ hT hE s fun x hx hTs hTD => ?_
  set t := matrixLinearEquiv (s : GL (Fin d) K) with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have htt : t * t = 1 := by
    rw [htdef, ← matrixLinearEquiv_mul, ← Subgroup.coe_mul, hss, Subgroup.coe_one]
    ext v
    simp [matrixLinearEquiv_apply]
  set W := commSpace t with hWdef
  set L := fixSpace t with hLdef
  have hWL' : W ≤ L := commSpace_le_fixSpace htt
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  have hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0 := fun v => by
    rw [hLdef, fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hQn : ∀ a : Fin d → K, (∀ x, polar Q x a = 0) → a = 0 := fun a ha =>
    hQ.2 a fun x => by rw [polarBilin_apply_apply]; exact ha x
  have hLW : ∃ x ∈ L, ∃ u ∈ L, polar Q x u = 1 := by
    obtain ⟨u, huL, huW⟩ : ∃ u ∈ L, u ∉ W := by
      by_contra hc
      push Not at hc
      exact hWL (le_antisymm hWL' hc)
    have hperp := ShearRigidity.mem_iff_forall_of_perp (B := polarBilin Q) hQn
      (polarBilin_isAlt Q) hL u
    rw [hperp] at huW
    push Not at huW
    obtain ⟨l, hl, hlu⟩ := huW
    rw [polarBilin_apply_apply] at hlu
    refine ⟨(polar Q l u)⁻¹ • l, L.smul_mem _ hl, u, huL, ?_⟩
    rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hlu]
  set N : (Fin d → K) →+ (Fin d → K) := ((t : (Fin d → K) →ₗ[K] (Fin d → K)) - 1).toAddMonoidHom
    with hNdef
  have hNv : ∀ v, N v = t v - v := fun v => rfl
  have hNV : ∀ v, N v ∈ W := fun v => LinearMap.mem_range_self _ v
  have hNW : ∀ h ∈ W, ∃ y, N y = h := fun h hh => LinearMap.mem_range.mp hh
  set W₀ := singularSubspace Q W hWiso with hW₀def
  have hb' : ∀ y, (∀ w ∈ W₀, polar Q y w = 0) → N y ∈ W₀ → N y = 0 := by
    intro y hy hNy
    rw [hNv] at hNy ⊢
    exact hb y (fun w hw hQw => hy w ⟨hw, hQw⟩) hNy.2
  have hW2' : ∃ w₁ ∈ W₀, ∃ w₂ ∈ W₀, LinearIndependent K ![w₁, w₂] := by
    obtain ⟨w₁, hw₁, w₂, hw₂, hQ₁, hQ₂, hind⟩ := hW2
    exact ⟨w₁, ⟨hw₁, hQ₁⟩, w₂, ⟨hw₂, hQ₂⟩, hind⟩
  set T := coordinateSemilinearMap x.val with hTdef
  have hTsm : ∀ (a : K) v, T (a • v) = x.val.right a • T v := coordinateSemilinearMap_smul x.val
  have hTQ : ∀ v, Q (T v) = x.val.right (Q v) := (mem_unitMultiplierPairs_iff Q x).mp hx
  have hTL : ∀ v ∈ L, T v ∈ L := fun v hv => mem_fixSpace.mpr (by
    rw [← hTs v, mem_fixSpace.mp hv])
  have hTN : ∀ v, T (N v) = N (T v) := fun v => by rw [hNv, hNv, map_sub, hTs]
  have hsh : ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : (Fin d → K) →+ (Fin d → K), (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + polar Q v u • w) ∧ ∀ v, g v - v - polar Q v w • u ∈ W := by
    intro w hw u hu
    obtain ⟨A, hA, hA1, hA2⟩ := exists_shear_mem_closure hQ hE hss hb hw.1 hw.2 hu
    exact ⟨(matrixLinearEquiv A).toLinearMap.toAddMonoidHom, fun v => hTD A hA v, hA1, hA2⟩
  exact (semilinear_shear_rigidity_quadratic_of_commute Q hQn hL hWL' (fun v => Iff.rfl) hW2' hLW
    hNV hNW hb' T hTsm hTQ hTL hTN hsh).2.2.2

theorem involutionCriterion_kappa_of_wall [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤) {s : matrixIsometries Q}
    (hss : s * s = 1)
    (hWL : CFSG.RankThree.OrthogonalInvolutions.commSpace (matrixLinearEquiv (s : GL (Fin d) K)) ≠
      CFSG.RankThree.OrthogonalInvolutions.fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hb : ∀ y, (∀ w ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)), Q w = 0 → polar Q y w = 0) →
      Q (matrixLinearEquiv (s : GL (Fin d) K) y - y) = 0 →
        matrixLinearEquiv (s : GL (Fin d) K) y - y = 0)
    (hW2 : ∃ w₁ ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)),
      ∃ w₂ ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
        (matrixLinearEquiv (s : GL (Fin d) K)),
        Q w₁ = 0 ∧ Q w₂ = 0 ∧ LinearIndependent K ![w₁, w₂]) :
    InvolutionCriterion (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :=
  fun β hβx hβc => pow_two_eq_one_of_kappa_of_wall hQ hT hE hss hWL hb hW2 β
    (htop ▸ Subgroup.mem_top β) hβx hβc

end Model

end OrthogonalShearAB

section TypesAB

open CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions OrthogonalShearAB

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem pow_two_eq_one_of_kappa_of_ne_ab [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {s : matrixIsometries Q} (hss : s * s = 1) (hs1 : s ≠ 1)
    (hWL : commSpace (matrixLinearEquiv (s : GL (Fin d) K)) ≠
      fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hab : (∀ x ∈ commSpace (matrixLinearEquiv (s : GL (Fin d) K)), Q x = 0) ∨
      (Odd (finrank K (commSpace (matrixLinearEquiv (s : GL (Fin d) K)))) ∧
        3 ≤ finrank K (commSpace (matrixLinearEquiv (s : GL (Fin d) K))))) :
    ∀ β ∈ matrixProjectiveImage Q,
      β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) * β →
      (∀ c, matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) c = c →
        Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  set t := matrixLinearEquiv (s : GL (Fin d) K) with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have htt : t * t = 1 := by
    rw [htdef, ← matrixLinearEquiv_mul, ← Subgroup.coe_mul, hss, Subgroup.coe_one]
    ext v
    simp [matrixLinearEquiv_apply]
  have hWiso : ∀ x ∈ commSpace t, ∀ y ∈ commSpace t, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  refine pow_two_eq_one_of_kappa_of_wall hQ hT hE hss hWL ?_ ?_
  · rcases hab with ha | ⟨hodd, -⟩
    · exact wall_of_forall_eq_zero hQ ht htt ha
    · exact wall_of_odd hQ ht htt hodd
  · rcases hab with ha | ⟨-, h3⟩
    · have ht1 : t ≠ 1 := fun h => hs1 (Subtype.ext (matrixLinearIso.injective (by
        change matrixLinearIso (s : GL (Fin d) K) = matrixLinearIso 1
        rw [map_one]
        exact h)))
      have h1 := one_le_finrank_commSpace ht1
      obtain ⟨k, hk⟩ := even_finrank_commSpace_of_forall_eq_zero hQ ht htt ha
      obtain ⟨w₁, hw₁, w₂, hw₂, hind⟩ :=
        exists_pair_of_two_le_finrank (S := commSpace t) (by omega)
      exact ⟨w₁, hw₁, w₂, hw₂, ha w₁ hw₁, ha w₂ hw₂, hind⟩
    · have h := finrank_le_finrank_singularSubspace_add_one (Q := Q) hWiso
      obtain ⟨w₁, hw₁, w₂, hw₂, hind⟩ :=
        exists_pair_of_two_le_finrank (S := singularSubspace Q (commSpace t) hWiso) (by omega)
      exact ⟨w₁, hw₁.1, w₂, hw₂.1, hw₁.2, hw₂.2, hind⟩

theorem involutionCriterion_kappa_of_ne_ab [Finite K] [CharP K 2]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (htop : matrixProjectiveImage Q = ⊤) {s : matrixIsometries Q}
    (hss : s * s = 1) (hs1 : s ≠ 1)
    (hWL : commSpace (matrixLinearEquiv (s : GL (Fin d) K)) ≠
      fixSpace (matrixLinearEquiv (s : GL (Fin d) K)))
    (hab : (∀ x ∈ commSpace (matrixLinearEquiv (s : GL (Fin d) K)), Q x = 0) ∨
      (Odd (finrank K (commSpace (matrixLinearEquiv (s : GL (Fin d) K)))) ∧
        3 ≤ finrank K (commSpace (matrixLinearEquiv (s : GL (Fin d) K))))) :
    InvolutionCriterion (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) :=
  fun β hβx hβc => pow_two_eq_one_of_kappa_of_ne_ab hQ hT hE hss hs1 hWL hab β
    (htop ▸ Subgroup.mem_top β) hβx hβc

end TypesAB

section Coordinate

open CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem pow_two_eq_one_of_kappa_of_ne_ab_plus (hn : 3 ≤ n)
    {s : matrixIsometries (coordinateQuadPlus n K)} (hss : s * s = 1) (hs1 : s ≠ 1)
    (hWL : commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)) ≠
      fixSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)))
    (hab : (∀ x ∈ commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)),
        coordinateQuadPlus n K x = 0) ∨
      (Odd (finrank K (commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)))) ∧
        3 ≤ finrank K (commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K))))) :
    ∀ β ∈ matrixProjectiveImage (coordinateQuadPlus n K),
      β * matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) =
        matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) * β →
      (∀ c, matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) c = c →
        Odd (orderOf c) → β c = c) → β ^ 2 = 1 := by
  have hreg := regular_coordinateQuadPlus n K hn
  exact pow_two_eq_one_of_kappa_of_ne_ab hreg.1 hreg.2 (commutator_coordinateQuadPlus n K hn)
    hss hs1 hWL hab

theorem involutionCriterion_kappa_of_ne_ab_plus (hn : 5 ≤ n)
    {s : matrixIsometries (coordinateQuadPlus n K)} (hss : s * s = 1) (hs1 : s ≠ 1)
    (hWL : commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)) ≠
      fixSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)))
    (hab : (∀ x ∈ commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)),
        coordinateQuadPlus n K x = 0) ∨
      (Odd (finrank K (commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)))) ∧
        3 ≤ finrank K (commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K))))) :
    InvolutionCriterion (matrixProjectiveConjugationHom (coordinateQuadPlus n K)
      (matrixIsometryInclusion _ s)) := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  exact involutionCriterion_kappa_of_ne_ab hreg.1 hreg.2
    (commutator_coordinateQuadPlus n K (by omega))
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn) hss hs1 hWL
    hab

theorem involutionCriterion_kappa_of_ne_ab_minus (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {s : matrixIsometries (coordinateQuadMinus n K (by omega) b c)} (hss : s * s = 1)
    (hs1 : s ≠ 1)
    (hWL : commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)) ≠
      fixSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)))
    (hab : (∀ x ∈ commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)),
        coordinateQuadMinus n K (by omega) b c x = 0) ∨
      (Odd (finrank K (commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K)))) ∧
        3 ≤ finrank K (commSpace (matrixLinearEquiv (s : GL (Fin (2 * n)) K))))) :
    InvolutionCriterion (matrixProjectiveConjugationHom (coordinateQuadMinus n K (by omega) b c)
      (matrixIsometryInclusion _ s)) := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  exact involutionCriterion_kappa_of_ne_ab hreg.1 hreg.2
    (commutator_coordinateQuadMinus n K b c hn hirr)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr)
    hss hs1 hWL hab

end Coordinate


end CFSG.SeitzReduction
