module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem pair_sign {i j : Fin D.rank} (hij : i ≠ j) {x y : ℤ} (h : pair i j (x, y) ∈ D.roots) :
    (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0) := by
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign _ h with h' | h'
  · left
    have hi := h' i
    have hj := h' j
    rw [pair_apply_left hij] at hi
    rw [pair_apply_right hij] at hj
    exact ⟨hi, hj⟩
  · right
    have hi := h' i
    have hj := h' j
    rw [pair_apply_left hij] at hi
    rw [pair_apply_right hij] at hj
    exact ⟨hi, hj⟩

theorem smul_single_mem_roots (hD : D.divisible = ∅) {c : ℤ} {i : Fin D.rank}
    (h : c • (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots) : c = 1 ∨ c = -1 := by
  rcases h with ⟨w, k, hk⟩ | ⟨w, k, hk, -⟩
  · have h1 := congrArg (weylAction D.isFiniteType w⁻¹) hk
    rw [weylAction_inv_apply_apply, map_zsmul] at h1
    have h2 := congrFun h1 k
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h2
    exact Int.eq_one_or_neg_one_of_mul_eq_one h2
  · rw [hD] at hk
    exact absurd hk (Set.notMem_empty k)

theorem pair_root_good (hD : D.divisible = ∅) {i j : Fin D.rank} (hij : i ≠ j) {x y : ℤ}
    (h : pair i j (x, y) ∈ D.roots) :
    ((0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0)) ∧ (x = 0 → y = 1 ∨ y = -1) ∧
      (y = 0 → x = 1 ∨ x = -1) := by
  refine ⟨pair_sign hij h, fun hx => ?_, fun hy => ?_⟩
  · subst hx
    refine smul_single_mem_roots hD (i := j) ?_
    simpa [pair_apply] using h
  · subst hy
    refine smul_single_mem_roots hD (i := i) ?_
    simpa [pair_apply] using h

theorem pair_refl_left_mem {i j : Fin D.rank} {x y x' : ℤ} (h : pair i j (x, y) ∈ D.roots)
    (hx' : x' = -x - D.cartan i j * y) : pair i j (x', y) ∈ D.roots := by
  subst hx'
  exact pair_reflection_left_mem_roots h

theorem pair_refl_right_mem {i j : Fin D.rank} {x y y' : ℤ} (h : pair i j (x, y) ∈ D.roots)
    (hy' : y' = -y - D.cartan j i * x) : pair i j (x, y') ∈ D.roots := by
  subst hy'
  exact pair_reflection_right_mem_roots h

theorem openCone_pair_eq_empty {i j : Fin D.rank} {z w : ℤ × ℤ}
    (h : ∀ a b : ℤ, 0 < a → 0 < b →
      pair i j (a * z.1 + b * w.1, a * z.2 + b * w.2) ∉ D.roots) :
    openCone D.roots (pair i j z) (pair i j w) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  refine h a b (by exact_mod_cast ha) (by exact_mod_cast hb) ?_
  have e : (a • pair i j z + b • pair i j w : Fin D.rank → ℤ) =
      pair i j ((a : ℤ) * z.1 + b * w.1, (a : ℤ) * z.2 + b * w.2) := by
    rw [← map_nsmul, ← map_nsmul, ← map_add]
    congr 1
  rwa [e] at hε

theorem linIndepPair_pair {i j : Fin D.rank} (hij : i ≠ j) {z w : ℤ × ℤ}
    (h : z.1 * w.2 - z.2 * w.1 ≠ 0) : LinIndepPair (pair i j z) (pair i j w) := by
  intro a b hab
  have e1 := congrFun hab i
  have e2 := congrFun hab j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pair_apply_left hij,
    pair_apply_right hij, Pi.zero_apply] at e1 e2
  have ha : a * (z.1 * w.2 - z.2 * w.1) = 0 := by linear_combination w.2 * e1 - w.1 * e2
  have hb : b * (z.1 * w.2 - z.2 * w.1) = 0 := by linear_combination z.1 * e2 - z.2 * e1
  exact ⟨(mul_eq_zero.1 ha).resolve_right h, (mul_eq_zero.1 hb).resolve_right h⟩

theorem commutes_rootGroup_of_openCone (hext : SteinbergExtras D n H) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hind : LinIndepPair γ δ)
    (hc : openCone D.roots γ δ = ∅) : Commutes (D.rootGroup γ) (D.rootGroup δ) := by
  intro x hx y hy
  have h := hext.commutator_mem _ hγ _ hδ hind x hx y hy
  rw [hc] at h
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem openCone_neg_neg {γ δ : Fin D.rank → ℤ} (hc : openCone D.roots γ δ = ∅) :
    openCone D.roots (-γ) (-δ) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have : (a • γ + b • δ : Fin D.rank → ℤ) ∈ openCone D.roots γ δ := by
    refine ⟨?_, a, b, ha, hb, rfl⟩
    have := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hε
    have e : -(a • -γ + b • -δ) = (a • γ + b • δ : Fin D.rank → ℤ) := by
      rw [smul_neg, smul_neg, ← neg_add, neg_neg]
    rwa [e] at this
  rw [hc] at this
  exact this

theorem linIndepPair_neg_snd {γ δ : Fin D.rank → ℤ} (h : LinIndepPair γ δ) :
    LinIndepPair γ (-δ) := fun a b hab => by
  have := h a (-b) (by simpa [neg_smul, smul_neg] using hab)
  exact ⟨this.1, neg_eq_zero.1 this.2⟩

theorem linIndepPair_neg_fst {γ δ : Fin D.rank → ℤ} (h : LinIndepPair γ δ) :
    LinIndepPair (-γ) δ := fun a b hab => by
  have := h (-a) b (by simpa [neg_smul, smul_neg] using hab)
  exact ⟨neg_eq_zero.1 this.1, this.2⟩

theorem commutes_sup_of_openCone (hext : SteinbergExtras D n H) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hind : LinIndepPair γ δ)
    (h1 : openCone D.roots γ δ = ∅) (h2 : openCone D.roots γ (-δ) = ∅) :
    Commutes (D.rootGroup γ ⊔ D.rootGroup (-γ)) (D.rootGroup δ ⊔ D.rootGroup (-δ)) := by
  have hγ' : -γ ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hγ
  have hδ' : -δ ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hδ
  have h3 : openCone D.roots (-γ) (-δ) = ∅ := openCone_neg_neg h1
  have h4 : openCone D.roots (-γ) δ = ∅ := by simpa using openCone_neg_neg h2
  refine Commutes.sup_left (Commutes.sup_right ?_ ?_) (Commutes.sup_right ?_ ?_)
  · exact commutes_rootGroup_of_openCone hext hγ hδ hind h1
  · exact commutes_rootGroup_of_openCone hext hγ hδ' (linIndepPair_neg_snd hind) h2
  · exact commutes_rootGroup_of_openCone hext hγ' hδ (linIndepPair_neg_fst hind) h4
  · exact commutes_rootGroup_of_openCone hext hγ' hδ'
      (linIndepPair_neg_snd (linIndepPair_neg_fst hind)) h3

theorem rankOne_map_conj_eq {x : K} {w : (coxeterMatrix D.isFiniteType).Group}
    (hx : ActsAs D x w) (m : Fin D.rank) :
    (rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom =
      D.rootGroup (weylAction D.isFiniteType w (Pi.single m 1)) ⊔
        D.rootGroup (-weylAction D.isFiniteType w (Pi.single m 1)) := by
  have hα : (Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m
  have hα' : (-Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  rw [rankOne, Subgroup.map_sup, hx _ hα, hx _ hα', map_neg]

theorem commutes_rankOne_map_conj (hext : SteinbergExtras D n H) {x : K}
    {w : (coxeterMatrix D.isFiniteType).Group} (hx : ActsAs D x w) (i m : Fin D.rank)
    (hind : LinIndepPair (Pi.single i 1) (weylAction D.isFiniteType w (Pi.single m 1)))
    (h1 : openCone D.roots (Pi.single i 1) (weylAction D.isFiniteType w (Pi.single m 1)) = ∅)
    (h2 : openCone D.roots (Pi.single i 1) (-weylAction D.isFiniteType w (Pi.single m 1)) = ∅) :
    Commutes (rankOne D.rootGroup i) ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom) := by
  rw [rankOne_map_conj_eq hx m]
  exact commutes_sup_of_openCone hext
    ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
    (weylAction_mem_roots D.isFiniteType w
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem m)) hind h1 h2

theorem not_mem_roots_cone_one (hD : D.divisible = ∅) {l s : Fin D.rank} (hls : l ≠ s)
    (h1 : D.cartan l s = -1) {c : ℤ} (h2 : D.cartan s l = -c) (hc : c = 2 ∨ c = 3)
    {a b x y : ℤ} (ha : 0 < a) (hb : 0 < b) (hx : x = a + b) (hy : y = 2 * b) :
    pair l s (x, y) ∉ D.roots := by
  subst hx hy
  intro h0
  have h1' := pair_refl_left_mem h0 (x' := b - a) (by rw [h1]; ring)
  have h2' := pair_refl_right_mem h1' (y' := -2 * b + c * (b - a)) (by rw [h2]; ring)
  have h3' := pair_refl_left_mem h2' (x' := -(b - a) + (-2 * b + c * (b - a))) (by rw [h1]; ring)
  have g0 := pair_root_good hD hls h0
  have g1 := pair_root_good hD hls h1'
  have g2 := pair_root_good hD hls h2'
  have g3 := pair_root_good hD hls h3'
  rcases hc with rfl | rfl <;> omega

theorem not_mem_roots_cone_two (hD : D.divisible = ∅) {l s : Fin D.rank} (hls : l ≠ s)
    (h1 : D.cartan l s = -1) {c : ℤ} (h2 : D.cartan s l = -c) (hc : c = 2 ∨ c = 3)
    {a b x y : ℤ} (ha : 0 < a) (hb : 0 < b) (hx : x = a - b) (hy : y = -2 * b) :
    pair l s (x, y) ∉ D.roots := by
  subst hx hy
  intro h0
  have h1' := pair_refl_right_mem h0 (y' := 2 * b + c * (a - b)) (by rw [h2]; ring)
  have h2' := pair_refl_left_mem h1' (x' := -(a - b) + (2 * b + c * (a - b))) (by rw [h1]; ring)
  have g0 := pair_root_good hD hls h0
  have g1 := pair_root_good hD hls h1'
  have g2 := pair_root_good hD hls h2'
  rcases hc with rfl | rfl <;> omega

theorem not_mem_roots_cone_short (hD : D.divisible = ∅) {l s : Fin D.rank} (hls : l ≠ s)
    (h1 : D.cartan l s = -1) (h2 : D.cartan s l = -3) {a b x y : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hxy : (x = 2 * b ∧ y = a + 3 * b) ∨ (x = -2 * b ∧ y = a - 3 * b)) :
    pair l s (x, y) ∉ D.roots := by
  intro h0
  have g0 := pair_root_good hD hls h0
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h1' := pair_refl_right_mem h0 (y' := 3 * b - a) (by rw [h2]; ring)
    have h2' := pair_refl_left_mem h1' (x' := b - a) (by rw [h1]; ring)
    have h3' := pair_refl_right_mem h2' (y' := -2 * a) (by rw [h2]; ring)
    have g1 := pair_root_good hD hls h1'
    have g2 := pair_root_good hD hls h2'
    have g3 := pair_root_good hD hls h3'
    omega
  · have h1' := pair_refl_left_mem h0 (x' := a - b) (by rw [h1]; ring)
    have h2' := pair_refl_right_mem h1' (y' := 2 * a) (by rw [h2]; ring)
    have g1 := pair_root_good hD hls h1'
    have g2 := pair_root_good hD hls h2'
    omega

theorem weylAction_bTwo {l s : Fin D.rank} (h2 : D.cartan s l = -2) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple s)
      (Pi.single l 1) = pair l s (1, 2) := by
  rw [single_eq_pair_left l s, weylAction_simple_pair_right, h2]
  norm_num

theorem weylAction_gTwo_long {l s : Fin D.rank} (h1 : D.cartan l s = -1)
    (h2 : D.cartan s l = -3) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple s *
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple l) (Pi.single s 1) =
      pair l s (1, 2) := by
  rw [weylAction_mul_apply, single_eq_pair_right l s, weylAction_simple_pair_left,
    weylAction_simple_pair_right, h1, h2]
  norm_num

theorem weylAction_gTwo_short {l s : Fin D.rank} (h1 : D.cartan l s = -1)
    (h2 : D.cartan s l = -3) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple l *
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple s) (Pi.single l 1) =
      pair l s (2, 3) := by
  rw [weylAction_mul_apply, single_eq_pair_left l s, weylAction_simple_pair_right,
    weylAction_simple_pair_left, h1, h2]
  norm_num

theorem commutes_rankOne_bTwo
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hD : D.divisible = ∅) {l s : Fin D.rank} (hls : l ≠ s)
    (h1 : D.cartan l s = -1) (h2 : D.cartan s l = -2) :
    Commutes (rankOne D.rootGroup l)
      ((rankOne D.rootGroup l).map (MulAut.conj (n s)).toMonoidHom) := by
  have hβ := weylAction_bTwo (l := l) h2
  refine commutes_rankOne_map_conj hext (actsAs_n hct s) l l ?_ ?_ ?_ <;>
    rw [hβ, single_eq_pair_left l s]
  · exact linIndepPair_pair hls (by norm_num)
  · exact openCone_pair_eq_empty fun a b ha hb =>
      not_mem_roots_cone_one hD hls h1 (c := 2) (by rw [h2]) (Or.inl rfl) ha hb (by ring) (by ring)
  · rw [← map_neg]
    exact openCone_pair_eq_empty fun a b ha hb =>
      not_mem_roots_cone_two hD hls h1 (c := 2) (by rw [h2]) (Or.inl rfl) ha hb (by simp; ring)
        (by simp; ring)

theorem commutes_rankOne_gTwo_long
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hD : D.divisible = ∅) {l s : Fin D.rank} (hls : l ≠ s)
    (h1 : D.cartan l s = -1) (h2 : D.cartan s l = -3) :
    Commutes (rankOne D.rootGroup l)
      ((rankOne D.rootGroup s).map (MulAut.conj (n s * n l)).toMonoidHom) := by
  have hβ := weylAction_gTwo_long h1 h2
  refine commutes_rankOne_map_conj hext ((actsAs_n hct s).mul (actsAs_n hct l)) l s ?_ ?_ ?_ <;>
    rw [hβ, single_eq_pair_left l s]
  · exact linIndepPair_pair hls (by norm_num)
  · exact openCone_pair_eq_empty fun a b ha hb =>
      not_mem_roots_cone_one hD hls h1 (c := 3) (by rw [h2]) (Or.inr rfl) ha hb (by ring) (by ring)
  · rw [← map_neg]
    exact openCone_pair_eq_empty fun a b ha hb =>
      not_mem_roots_cone_two hD hls h1 (c := 3) (by rw [h2]) (Or.inr rfl) ha hb (by simp; ring)
        (by simp; ring)

theorem commutes_rankOne_gTwo_short
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hD : D.divisible = ∅) {l s : Fin D.rank} (hls : l ≠ s)
    (h1 : D.cartan l s = -1) (h2 : D.cartan s l = -3) :
    Commutes (rankOne D.rootGroup s)
      ((rankOne D.rootGroup l).map (MulAut.conj (n l * n s)).toMonoidHom) := by
  have hβ := weylAction_gTwo_short h1 h2
  refine commutes_rankOne_map_conj hext ((actsAs_n hct l).mul (actsAs_n hct s)) s l ?_ ?_ ?_ <;>
    rw [hβ, single_eq_pair_right l s]
  · exact linIndepPair_pair hls (by norm_num)
  · exact openCone_pair_eq_empty fun a b ha hb =>
      not_mem_roots_cone_short hD hls h1 h2 ha hb (Or.inl ⟨by ring, by ring⟩)
  · rw [← map_neg]
    exact openCone_pair_eq_empty fun a b ha hb =>
      not_mem_roots_cone_short hD hls h1 h2 ha hb (Or.inr ⟨by simp; ring, by simp; ring⟩)

end CFSG.AGLEmbedding.ToralCensus
