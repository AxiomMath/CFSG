module

public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Ree.LargeReeBlockCollection

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {K : Type} [Field K]

theorem exists_nodup_list_annih {α : Type*} {S : Set α} (h : S.Finite) :
    ∃ L : List α, L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ S :=
  ⟨h.toFinset.toList, Finset.nodup_toList _, fun x => by simp⟩

theorem list_prod_map_filter_annih {G ι : Type*} [Monoid G] (l : List ι) (p : ι → Prop)
    [DecidablePred p] (g : ι → G) (h : ∀ x ∈ l, ¬ p x → g x = 1) :
    ((l.filter fun x => decide (p x)).map g).prod = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x
    · rw [List.filter_cons_of_pos (by simpa using hx), List.map_cons, List.prod_cons,
        List.map_cons, List.prod_cons, ih']
    · rw [List.filter_cons_of_neg (by simpa using hx), List.map_cons, List.prod_cons,
        h x List.mem_cons_self hx, one_mul, ih']

theorem exists_list_prod_map_mul_annih {G ι : Type*} [Group G] {P M : Subgroup G}
    (hM : ∀ p ∈ P, ∀ e ∈ M, p * e * p⁻¹ ∈ M) (a y : ι → G) :
    ∀ l : List ι, (∀ i ∈ l, a i ∈ P) → (∀ i ∈ l, y i ∈ M) →
      ∃ e ∈ M, (l.map fun i => a i * y i).prod = (l.map a).prod * e
  | [], _, _ => ⟨1, M.one_mem, by simp⟩
  | i :: l, ha, hy => by
    obtain ⟨e, he, hl⟩ := exists_list_prod_map_mul_annih hM a y l
      (fun j hj => ha j (List.mem_cons_of_mem _ hj)) (fun j hj => hy j (List.mem_cons_of_mem _ hj))
    have hA : (l.map a).prod ∈ P := list_prod_mem fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact ha j (List.mem_cons_of_mem _ hj)
    refine ⟨((l.map a).prod)⁻¹ * y i * ((l.map a).prod)⁻¹⁻¹ * e,
      M.mul_mem (hM _ (P.inv_mem hA) _ (hy i List.mem_cons_self)) he, ?_⟩
    rw [List.map_cons, List.prod_cons, hl, List.map_cons, List.prod_cons]
    group

theorem height_add_annih {τ : Tag} (u v : Fin τ.rank → ℤ) :
    height (u + v) = height u + height v := by
  simp [height, Finset.sum_add_distrib]

theorem heightSet_closed_annih {τ : Tag} (h : ℤ) :
    ∀ α ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ},
      ∀ β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ},
        ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ} := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;> nlinarith [hα.2.1, hα.2.2, hβ.2.1]

@[expose] def annRoots (τ : Tag) (S : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ 0 < height γ ∧
    ∀ δ ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • γ + b • δ)}

@[expose] def oneOneCheck (τ : Tag) : Bool :=
  (RootOps.repsOf τ).all fun r => r.2.2.isEmpty || r.2.2.any fun f => f.1 == 1 && f.2.1 == 1

theorem oneOneCheck_eq_true : ∀ τ : Tag, oneOneCheck τ = true := by
  intro τ
  cases τ <;> decide +kernel

section Basic


theorem pinnedX_mem_heightSeries_annih {τ : Tag} {h : ℤ} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hp : 0 < height α) (hh : h ≤ height α) (c : K) : pinnedX τ K α c ∈ heightSeries τ K h :=
  (le_iSup₂_of_le α ⟨hα, hp, hh⟩ le_rfl :
    rootSubgroup τ K α ≤ rootSpan τ K {γ | IsRoot τ γ ∧ 0 < height γ ∧ h ≤ height γ})
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem heightSeries_antitone_annih {τ : Tag} {h h' : ℤ} (hh : h ≤ h') :
    heightSeries τ K h' ≤ heightSeries τ K h :=
  biSup_mono fun _ hα => ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩

theorem pinnedX_mem_posUnipotent_annih {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hp : 0 < height α) (c : K) : pinnedX τ K α c ∈ posUnipotent τ K :=
  heightSeries_le_posUnipotent 1 (pinnedX_mem_heightSeries_annih hα hp (by omega) c)

theorem sq_eq_one_of_mem_rootSpan_annih [CharP K 2] {τ : Tag} {A : Set (Fin τ.rank → ℤ)}
    (hA : ∀ γ ∈ A, ∀ γ' ∈ A, ∀ c d : K,
      pinnedX τ K γ c * pinnedX τ K γ' d = pinnedX τ K γ' d * pinnedX τ K γ c)
    {z : ModGL τ K} (hz : z ∈ rootSpan τ K A) : z ^ 2 = 1 := by
  rw [rootSpan_eq_closure] at hz
  set X := {g | ∃ α ∈ A, ∃ c : K, pinnedX τ K α c = g} with hX
  have h1 : ∀ g ∈ X, ∀ b ∈ Subgroup.closure X, Commute g b := by
    intro g hg b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb =>
      obtain ⟨γ, hγ, c, rfl⟩ := hg
      obtain ⟨γ', hγ', d, rfl⟩ := hb
      exact hA γ hγ γ' hγ' c d
    | one => exact Commute.one_right g
    | mul b b' _ _ ihb ihb' => exact Commute.mul_right ihb ihb'
    | inv b _ ih => exact Commute.inv_right ih
  have h2 : ∀ a ∈ Subgroup.closure X, ∀ b ∈ Subgroup.closure X, Commute a b := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact h1 a ha
    | one => exact fun b _ => Commute.one_left b
    | mul a a' _ _ iha iha' => exact fun b hb => Commute.mul_left (iha b hb) (iha' b hb)
    | inv a _ ih => exact fun b hb => Commute.inv_left (ih b hb)
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨γ, -, c, rfl⟩ := hg
    rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  | one => rw [one_pow]
  | mul a b ha hb iha ihb => rw [(h2 a ha b hb).mul_pow, iha, ihb, one_mul]
  | inv a _ ih => rw [inv_pow, ih, inv_one]

@[expose] def annihIsRootB (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  τ.rootCertificate.roots.any fun c => CFSG.LieType.Ree.vecBEq (decodeVec c) v

theorem isRoot_iff_exists_decodeVec_annih {τ : Tag} {v : Fin τ.rank → ℤ} :
    IsRoot τ v ↔ ∃ c ∈ τ.rootCertificate.roots, decodeVec c = v := by
  rw [RootCertificate.isRoot_iff τ.rootCertificate_check]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, List.getElem_mem hk, by rw [RootCertificate.root, List.getD_eq_getElem _ _ hk]⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
    exact ⟨k, hk, by rw [RootCertificate.root, List.getD_eq_getElem _ _ hk]⟩

theorem annihIsRootB_iff {τ : Tag} {v : Fin τ.rank → ℤ} : annihIsRootB τ v = true ↔ IsRoot τ v := by
  rw [annihIsRootB, List.any_eq_true, isRoot_iff_exists_decodeVec_annih]
  simp only [CFSG.LieType.Ree.vecBEq_iff]

@[expose] def annListCheck (τ : Tag) (M : ℤ) (S L : List (Fin τ.rank → ℤ)) : Bool :=
  (τ.rootCertificate.roots.all fun c => decide (height (decodeVec c : Fin τ.rank → ℤ) ≤ M)) &&
    (S.all fun δ => annihIsRootB τ δ && decide (0 < height δ)) &&
    (L.all fun γ => annihIsRootB τ γ && decide (0 < height γ)) &&
    (τ.rootCertificate.roots.all fun c =>
      decide (height (decodeVec c : Fin τ.rank → ℤ) ≤ 0) ||
        L.any (fun γ => CFSG.LieType.Ree.vecBEq γ (decodeVec c)) ||
        S.any (fun δ => annihIsRootB τ (decodeVec c + δ))) &&
    L.all fun γ => L.all fun γ' => decide (M < height (γ + γ')) || !annihIsRootB τ (γ + γ')

theorem annListCheck_sound {τ : Tag} {M : ℤ} {S L : List (Fin τ.rank → ℤ)}
    (h : annListCheck τ M S L = true) :
    (∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ) ∧ (∀ γ ∈ L, IsRoot τ γ ∧ 0 < height γ) ∧
      (∀ γ, IsRoot τ γ → 0 < height γ → (∀ δ ∈ S, ¬ IsRoot τ (γ + δ)) → γ ∈ L) ∧
      ∀ γ ∈ L, ∀ γ' ∈ L, ¬ IsRoot τ (γ + γ') := by
  simp only [annListCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hM, hS⟩, hL⟩, hroots⟩, hpair⟩ := h
  refine ⟨fun δ hδ => ⟨annihIsRootB_iff.1 (hS δ hδ).1, (hS δ hδ).2⟩,
    fun γ hγ => ⟨annihIsRootB_iff.1 (hL γ hγ).1, (hL γ hγ).2⟩,
    fun γ hγ hγp hγS => ?_, fun γ hγ γ' hγ' hr => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := isRoot_iff_exists_decodeVec_annih.1 hγ
    rcases hroots c hc with (h1 | ⟨γ', hγ', h3⟩) | ⟨δ, hδ, h2⟩
    · exact absurd h1 (not_le.2 hγp)
    · rwa [← CFSG.LieType.Ree.vecBEq_iff.1 h3]
    · exact absurd (annihIsRootB_iff.1 h2) (hγS δ hδ)
  · obtain ⟨c, hc, hce⟩ := isRoot_iff_exists_decodeVec_annih.1 hr
    rcases hpair γ hγ γ' hγ' with h1 | h1
    · have := hM c hc
      rw [hce] at this
      exact absurd h1 (not_lt.2 this)
    · rw [annihIsRootB_iff.2 hr] at h1
      exact Bool.false_ne_true h1.symm

end Basic

section Commutators


theorem conj_mem_heightSeries_annih {τ : Tag} {h : ℤ} {p e : ModGL τ K}
    (hp : p ∈ posUnipotent τ K) (he : e ∈ heightSeries τ K h) :
    p * e * p⁻¹ ∈ heightSeries τ K h :=
  (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer K h hp) e).1 he

theorem exists_commutator_mul_eq_annih {τ : Tag} {n m : ℤ} (hn : 1 ≤ n) (hm : 0 ≤ m)
    {g h x : ModGL τ K} (hg : g ∈ heightSeries τ K n) (hh : h ∈ heightSeries τ K n)
    (hx : x ∈ heightSeries τ K m) :
    ∃ e ∈ heightSeries τ K (n + m + 1), ⁅g * h, x⁆ = ⁅g, x⁆ * ⁅h, x⁆ * e := by
  have ha : ⁅g, x⁆ ∈ heightSeries τ K (n + m) :=
    commutator_heightSeries_le K n m (Subgroup.commutator_mem_commutator hg hx)
  have hb : ⁅h, x⁆ ∈ heightSeries τ K (n + m) :=
    commutator_heightSeries_le K n m (Subgroup.commutator_mem_commutator hh hx)
  have h1 : ⁅g, ⁅h, x⁆⁆ ∈ heightSeries τ K (n + m + 1) :=
    heightSeries_antitone_annih (by omega)
      (commutator_heightSeries_le K n (n + m) (Subgroup.commutator_mem_commutator hg hb))
  have h2 : ⁅⁅h, x⁆⁻¹, ⁅g, x⁆⁻¹⁆ ∈ heightSeries τ K (n + m + 1) :=
    heightSeries_antitone_annih (by omega)
      (commutator_heightSeries_le K (n + m) (n + m)
        (Subgroup.commutator_mem_commutator (inv_mem hb) (inv_mem ha)))
  have hp : ⁅h, x⁆⁻¹ * ⁅g, x⁆⁻¹ ∈ posUnipotent τ K :=
    heightSeries_le_posUnipotent _ (mul_mem (inv_mem hb) (inv_mem ha))
  refine ⟨(⁅h, x⁆⁻¹ * ⁅g, x⁆⁻¹) * ⁅g, ⁅h, x⁆⁆ * (⁅h, x⁆⁻¹ * ⁅g, x⁆⁻¹)⁻¹ *
      ⁅⁅h, x⁆⁻¹, ⁅g, x⁆⁻¹⁆, mul_mem (conj_mem_heightSeries_annih hp h1) h2, ?_⟩
  simp only [commutatorElement_def]
  group

theorem exists_commutator_list_prod_eq_annih {τ : Tag} {n m : ℤ} (hn : 1 ≤ n) (hm : 0 ≤ m)
    {x : ModGL τ K} (hx : x ∈ heightSeries τ K m) :
    ∀ l : List (ModGL τ K), (∀ g ∈ l, g ∈ heightSeries τ K n) →
      ∃ e ∈ heightSeries τ K (n + m + 1), ⁅l.prod, x⁆ = (l.map fun g => ⁅g, x⁆).prod * e
  | [], _ => ⟨1, one_mem _, by simp⟩
  | g :: l, hl => by
    obtain ⟨e, he, hle⟩ := exists_commutator_list_prod_eq_annih hn hm hx l
      fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    have hP : l.prod ∈ heightSeries τ K n :=
      list_prod_mem fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    obtain ⟨e', he', hge⟩ := exists_commutator_mul_eq_annih hn hm (hl g List.mem_cons_self) hP hx
    refine ⟨e * e', mul_mem he he', ?_⟩
    rw [List.prod_cons, hge, hle, List.map_cons, List.prod_cons]
    group

end Commutators

section Main


theorem commutator_pinnedX_lead_annih {τ : Tag} {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hγp : 0 < height γ) (hδp : 0 < height δ)
    (hne : γ ≠ δ) (c d : K) :
    (IsRoot τ (γ + δ) → ∃ y ∈ heightSeries τ K (height γ + height δ + 1),
      ⁅pinnedX τ K γ c, pinnedX τ K δ d⁆ =
        pinnedX τ K (γ + δ) ((commConst τ γ δ (1, 1) : K) * c * d) * y) ∧
    (¬ IsRoot τ (γ + δ) →
      ⁅pinnedX τ K γ c, pinnedX τ K δ d⁆ ∈ heightSeries τ K (height γ + height δ + 1)) := by
  have hne' : γ ≠ -δ := by
    rintro rfl
    have : height (-δ) = -height δ := by simp [height]
    linarith
  obtain ⟨-, hmem, hsort, -, hF⟩ := root_commutator_formula τ hγ hδ hne hne'
  set f : ℕ × ℕ → ModGL τ K := fun p =>
    pinnedX τ K (p.1 • γ + p.2 • δ) ((commConst τ γ δ p : K) * c ^ p.1 * d ^ p.2) with hf
  have hcomm : ⁅pinnedX τ K γ c, pinnedX τ K δ d⁆ = ((commPairs τ γ δ).map f).prod := by
    rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
    exact hF K c d
  have hhigh : ∀ p ∈ commPairs τ γ δ, p ≠ (1, 1) →
      f p ∈ heightSeries τ K (height γ + height δ + 1) := by
    intro p hp hp1
    obtain ⟨h1, h2, hr⟩ := (hmem p).1 hp
    have ha' : (1 : ℤ) ≤ p.1 := by exact_mod_cast h1
    have hb' : (1 : ℤ) ≤ p.2 := by exact_mod_cast h2
    have h2' : (2 : ℤ) ≤ p.1 ∨ (2 : ℤ) ≤ p.2 := by
      by_contra hcon
      simp only [not_or, not_le] at hcon
      exact hp1 (Prod.ext (by omega) (by omega))
    refine pinnedX_mem_heightSeries_annih hr ?_ ?_ _ <;> rw [height_nsmul_add_nsmul] <;>
      rcases h2' with h2' | h2' <;> nlinarith
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have h11 : (1, 1) ∈ commPairs τ γ δ :=
      (hmem (1, 1)).2 ⟨one_pos, one_pos, by simpa using hr⟩
    obtain ⟨q, t, hqt⟩ : ∃ q t, commPairs τ γ δ = q :: t := by
      cases h : commPairs τ γ δ with
      | nil => rw [h] at h11; exact absurd h11 List.not_mem_nil
      | cons q t => exact ⟨q, t, rfl⟩
    have hq1 := (hmem q).1 (hqt ▸ List.mem_cons_self)
    rw [hqt] at hsort h11 hhigh
    have hq : q = (1, 1) := by
      rcases List.mem_cons.1 h11 with h | h
      · exact h.symm
      · have hlt := List.rel_of_pairwise_cons hsort h
        omega
    subst hq
    have ht : ∀ p ∈ t, p ≠ (1, 1) := fun p hp hp1 => by
      have hlt := List.rel_of_pairwise_cons hsort hp
      rw [hp1] at hlt
      omega
    refine ⟨(t.map f).prod, list_prod_mem fun x hx => ?_, ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hhigh p (List.mem_cons_of_mem _ hp) (ht p hp)
    · rw [hcomm, hqt, List.map_cons, List.prod_cons]
      simp [hf]
  · rw [hcomm]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    refine hhigh p hp fun hp1 => hr ?_
    have := ((hmem p).1 hp).2.2
    rwa [hp1, one_smul, one_smul] at this

theorem eq_zero_of_list_prod_mem_rootSpan_annih {τ : Tag} {T : Set (Fin τ.rank → ℤ)}
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (hTc : ∀ β ∈ T, ∀ γ ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • γ) →
      a • β + b • γ ∈ T)
    {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup) (hl : ∀ γ ∈ l, IsRoot τ γ ∧ 0 < height γ)
    (hlT : ∀ γ ∈ l, γ ∉ T) (c : (Fin τ.rank → ℤ) → K)
    (hmem : (l.map fun γ => pinnedX τ K γ (c γ)).prod ∈ rootSpan τ K T) :
    ∀ γ ∈ l, c γ = 0 := by
  classical
  obtain ⟨L, hLnd, hLT⟩ := exists_nodup_list_annih
    ((finite_setOf_isRoot τ).subset fun β hβ => (hT β hβ).1)
  obtain ⟨-, hsurj, -⟩ := CFSG.LieType.Ree.list_prod_pinnedX_bijective (K := K) hT hTc hLnd
    (Set.ext hLT)
  obtain ⟨d, hd⟩ := hsurj _ hmem
  have hLl : ∀ γ ∈ L, γ ∉ l := fun γ hγ h => hlT γ h ((hLT γ).1 hγ)
  have hnd' : (l ++ L).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, hLnd, fun a ha b hb hab => hLl b hb (hab ▸ ha)⟩
  have hpos : ∀ γ ∈ l ++ L, IsRoot τ γ ∧ 0 < height γ := fun γ hγ => by
    rcases List.mem_append.1 hγ with h | h
    · exact hl γ h
    · exact hT γ ((hLT γ).1 h)
  have e1 : (l.map fun γ => pinnedX τ K γ (if γ ∈ l then c γ else 0)) =
      l.map fun γ => pinnedX τ K γ (c γ) :=
    List.map_congr_left fun γ hγ => by simp only [hγ, ↓reduceIte]
  have e2 : (L.map fun γ => pinnedX τ K γ (if γ ∈ l then c γ else 0)) = L.map fun _ => 1 :=
    List.map_congr_left fun γ hγ => by simp only [hLl γ hγ, ↓reduceIte, pinnedX_zero]
  have e3 : (l.map fun γ => pinnedX τ K γ (if γ ∈ l then 0 else d γ)) = l.map fun _ => 1 :=
    List.map_congr_left fun γ hγ => by simp only [hγ, ↓reduceIte, pinnedX_zero]
  have e4 : (L.map fun γ => pinnedX τ K γ (if γ ∈ l then 0 else d γ)) =
      L.map fun γ => pinnedX τ K γ (d γ) :=
    List.map_congr_left fun γ hγ => by simp only [hLl γ hγ, ↓reduceIte]
  have key := pinnedX_list_prod_injective (R := K) (l ++ L) hnd' hpos
    (fun γ => if γ ∈ l then c γ else 0) (fun γ => if γ ∈ l then 0 else d γ) (by
      rw [List.map_append, List.map_append, List.prod_append, List.prod_append, e1, e2, e3, e4,
        hd]
      simp)
  intro γ hγ
  simpa [hγ] using key γ (List.mem_append_left _ hγ)

theorem exists_eq_layer_mul_annih {τ : Tag} {n : ℤ} {L : List (Fin τ.rank → ℤ)} (hLnd : L.Nodup)
    (hL : ∀ γ, γ ∈ L ↔ IsRoot τ γ ∧ 0 < height γ ∧ height γ = n) {w : ModGL τ K}
    (hw : w ∈ heightSeries τ K n) :
    ∃ c : (Fin τ.rank → ℤ) → K, ∃ y ∈ heightSeries τ K (n + 1),
      w = (L.map fun γ => pinnedX τ K γ (c γ)).prod * y := by
  classical
  obtain ⟨L', hL'nd, hL'⟩ := exists_nodup_list_annih
    (S := {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ n + 1 ≤ height γ})
    ((finite_setOf_isRoot τ).subset fun β hβ => hβ.1)
  have hnd : (L ++ L').Nodup := by
    rw [List.nodup_append]
    refine ⟨hLnd, hL'nd, fun a ha b hb hab => ?_⟩
    have h1 := ((hL a).1 ha).2.2
    have h2 := ((hL' b).1 hb).2.2
    rw [hab] at h1
    omega
  have hset : {x | x ∈ L ++ L'} =
      {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ n ≤ height γ} := by
    ext γ
    simp only [Set.mem_ofPred_eq, List.mem_append, hL, hL']
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, h2, h3.ge⟩
      · exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      rcases eq_or_lt_of_le h3 with h | h
      · exact Or.inl ⟨h1, h2, h.symm⟩
      · exact Or.inr ⟨h1, h2, by omega⟩
  obtain ⟨-, hsurj, -⟩ := CFSG.LieType.Ree.list_prod_pinnedX_bijective (K := K)
    (fun β hβ => ⟨hβ.1, hβ.2.1⟩) (heightSet_closed_annih n) hnd hset
  obtain ⟨c, hc⟩ := hsurj w hw
  refine ⟨c, (L'.map fun γ => pinnedX τ K γ (c γ)).prod, list_prod_mem fun g hg => ?_, ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, h3⟩ := (hL' γ).1 hγ
    exact pinnedX_mem_heightSeries_annih h1 h2 h3 _
  · rw [← hc, List.map_append, List.prod_append]

theorem exists_mul_of_commute_annih {τ : Tag} {S A : Set (Fin τ.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ)
    (hdet : ∀ γ, IsRoot τ γ → 0 < height γ → γ ∉ A →
      ∃ δ ∈ S, γ ≠ δ ∧ IsRoot τ (γ + δ) ∧ (commConst τ γ δ (1, 1) : K) ≠ 0)
    {n : ℤ} (hn : 1 ≤ n) {w : ModGL τ K} (hw : w ∈ heightSeries τ K n)
    (hc : ∀ δ ∈ S, w * pinnedX τ K δ 1 = pinnedX τ K δ 1 * w) :
    ∃ a ∈ rootSpan τ K A, ∃ y ∈ heightSeries τ K (n + 1), w = a * y := by
  classical
  obtain ⟨L, hLnd, hL⟩ := exists_nodup_list_annih
    (S := {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ height γ = n})
    ((finite_setOf_isRoot τ).subset fun β hβ => hβ.1)
  obtain ⟨c, y, hy, rfl⟩ := exists_eq_layer_mul_annih hLnd hL hw
  refine ⟨(L.map fun γ => pinnedX τ K γ (c γ)).prod, list_prod_mem fun g hg => ?_, y, hy, rfl⟩
  obtain ⟨γ₀, hγ₀, rfl⟩ := List.mem_map.1 hg
  by_cases hc₀ : c γ₀ = 0
  · rw [hc₀, pinnedX_zero]
    exact one_mem _
  by_cases hA : γ₀ ∈ A
  · exact (le_iSup₂_of_le γ₀ hA le_rfl : rootSubgroup τ K γ₀ ≤ rootSpan τ K A)
      (Subgroup.subset_closure ⟨c γ₀, rfl⟩)
  exfalso
  obtain ⟨hγ₀r, hγ₀p, hγ₀n⟩ := (hL γ₀).1 hγ₀
  obtain ⟨δ, hδS, hne, hr, hN⟩ := hdet γ₀ hγ₀r hγ₀p hA
  obtain ⟨hδr, hδp⟩ := hS δ hδS
  have hxm : pinnedX τ K δ 1 ∈ heightSeries τ K (height δ) :=
    pinnedX_mem_heightSeries_annih hδr hδp le_rfl 1
  have hLmem : ∀ g ∈ L.map fun γ => pinnedX τ K γ (c γ), g ∈ heightSeries τ K n := fun g hg => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, h3⟩ := (hL γ).1 hγ
    exact pinnedX_mem_heightSeries_annih h1 h2 h3.ge _
  set wn := (L.map fun γ => pinnedX τ K γ (c γ)).prod with hwn
  have hwnm : wn ∈ heightSeries τ K n := list_prod_mem hLmem
  have hcomm : ⁅wn, pinnedX τ K δ 1⁆ ∈ heightSeries τ K (n + height δ + 1) := by
    have h1 : ⁅wn * y, pinnedX τ K δ 1⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hc δ hδS)
    have h2 : ⁅y, pinnedX τ K δ 1⁆ ∈ heightSeries τ K (n + height δ + 1) := by
      have := commutator_heightSeries_le K (n + 1) (height δ)
        (Subgroup.commutator_mem_commutator hy hxm)
      rwa [show n + 1 + height δ = n + height δ + 1 by ring] at this
    have h3 : ⁅wn, pinnedX τ K δ 1⁆ = (wn * ⁅y, pinnedX τ K δ 1⁆ * wn⁻¹)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by
        rw [← h1]
        simp only [commutatorElement_def]
        group)
    rw [h3]
    exact inv_mem (conj_mem_heightSeries_annih (heightSeries_le_posUnipotent n hwnm) h2)
  set lead : (Fin τ.rank → ℤ) → ModGL τ K := fun γ =>
    if γ ≠ δ ∧ IsRoot τ (γ + δ) then
      pinnedX τ K (γ + δ) ((commConst τ γ δ (1, 1) : K) * c γ) else 1 with hlead
  have hleadγ : ∀ γ, ∃ yγ : ModGL τ K, γ ∈ L → yγ ∈ heightSeries τ K (n + height δ + 1) ∧
      ⁅pinnedX τ K γ (c γ), pinnedX τ K δ 1⁆ = lead γ * yγ := by
    intro γ
    by_cases hγL : γ ∈ L
    · obtain ⟨h1, h2, h3⟩ := (hL γ).1 hγL
      by_cases hγδ : γ = δ
      · subst hγδ
        refine ⟨1, fun _ => ⟨one_mem _, ?_⟩⟩
        rw [commutatorElement_eq_one_iff_mul_comm.2 (rootSubgroup_mul_comm K
          (Subgroup.subset_closure ⟨c γ, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩))]
        simp [hlead]
      have hlt := commutator_pinnedX_lead_annih h1 hδr h2 hδp hγδ (c γ) (1 : K)
      rw [h3] at hlt
      by_cases hγr : IsRoot τ (γ + δ)
      · obtain ⟨yγ, hyγ, he⟩ := hlt.1 hγr
        refine ⟨yγ, fun _ => ⟨hyγ, ?_⟩⟩
        rw [he, mul_one]
        simp [hlead, hγδ, hγr]
      · refine ⟨⁅pinnedX τ K γ (c γ), pinnedX τ K δ 1⁆, fun _ => ⟨hlt.2 hγr, ?_⟩⟩
        simp [hlead, hγr]
    · exact ⟨1, fun h => absurd h hγL⟩
  choose yf hyf using hleadγ
  have hleadP : ∀ γ ∈ L, lead γ ∈ posUnipotent τ K := fun γ hγ => by
    obtain ⟨-, h2, -⟩ := (hL γ).1 hγ
    by_cases hcond : γ ≠ δ ∧ IsRoot τ (γ + δ)
    · simp only [hlead]
      rw [ite_eq_left hcond]
      exact pinnedX_mem_posUnipotent_annih hcond.2 (by rw [height_add_annih]; omega) _
    · simp only [hlead]
      rw [ite_eq_right hcond]
      exact one_mem _
  have hprod : (L.map lead).prod ∈ heightSeries τ K (n + height δ + 1) := by
    obtain ⟨e₁, he₁, hexp⟩ := exists_commutator_list_prod_eq_annih hn hδp.le hxm _ hLmem
    obtain ⟨e₂, he₂, hP⟩ := exists_list_prod_map_mul_annih (P := posUnipotent τ K)
      (M := heightSeries τ K (n + height δ + 1))
      (fun p hp e he => conj_mem_heightSeries_annih hp he) lead yf L hleadP
      (fun γ hγ => (hyf γ hγ).1)
    have e : ((L.map fun γ => pinnedX τ K γ (c γ)).map fun g => ⁅g, pinnedX τ K δ 1⁆) =
        L.map fun γ => lead γ * yf γ := by
      rw [List.map_map]
      exact List.map_congr_left fun γ hγ => (hyf γ hγ).2
    rw [e, hP] at hexp
    have hl : (L.map lead).prod = ⁅wn, pinnedX τ K δ 1⁆ * e₁⁻¹ * e₂⁻¹ := by
      rw [hexp]
      group
    rw [hl]
    exact mul_mem (mul_mem hcomm (inv_mem he₁)) (inv_mem he₂)
  have hdrop : ((L.filter fun γ => decide (γ ≠ δ ∧ IsRoot τ (γ + δ))).map lead).prod =
      (L.map lead).prod :=
    list_prod_map_filter_annih L (fun γ => γ ≠ δ ∧ IsRoot τ (γ + δ)) lead fun γ _ hγ => by
      simp only [hlead]
      exact ite_eq_right hγ
  set d : (Fin τ.rank → ℤ) → K := fun ε =>
    (commConst τ (ε - δ) δ (1, 1) : K) * c (ε - δ) with hd
  have hmap : (((L.filter fun γ => decide (γ ≠ δ ∧ IsRoot τ (γ + δ))).map fun γ => γ + δ).map
      fun ε => pinnedX τ K ε (d ε)) =
      (L.filter fun γ => decide (γ ≠ δ ∧ IsRoot τ (γ + δ))).map lead := by
    rw [List.map_map]
    refine List.map_congr_left fun γ hγ => ?_
    have hγ' := (List.mem_filter.1 hγ).2
    rw [decide_eq_true_eq] at hγ'
    simp only [Function.comp_apply, hd, add_sub_cancel_right, hlead]
    rw [ite_eq_left hγ']
  have hpos : ∀ ε ∈ (L.filter fun γ => decide (γ ≠ δ ∧ IsRoot τ (γ + δ))).map fun γ => γ + δ,
      IsRoot τ ε ∧ 0 < height ε := fun ε hε => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hε
    obtain ⟨hγL, hγ'⟩ := List.mem_filter.1 hγ
    rw [decide_eq_true_eq] at hγ'
    obtain ⟨-, -, h3⟩ := (hL γ).1 hγL
    exact ⟨hγ'.2, by rw [height_add_annih]; omega⟩
  have hout : ∀ ε ∈ (L.filter fun γ => decide (γ ≠ δ ∧ IsRoot τ (γ + δ))).map fun γ => γ + δ,
      ε ∉ {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ n + height δ + 1 ≤ height γ} :=
    fun ε hε => by
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hε
    obtain ⟨hγL, -⟩ := List.mem_filter.1 hγ
    obtain ⟨-, -, h3⟩ := (hL γ).1 hγL
    rintro ⟨-, -, h⟩
    rw [height_add_annih] at h
    omega
  have hzero := eq_zero_of_list_prod_mem_rootSpan_annih (K := K)
    (T := {γ : Fin τ.rank → ℤ | IsRoot τ γ ∧ 0 < height γ ∧ n + height δ + 1 ≤ height γ})
    (fun β hβ => ⟨hβ.1, hβ.2.1⟩) (heightSet_closed_annih _)
    ((hLnd.filter _).map (add_left_injective δ)) hpos hout d
    (by rw [hmap, hdrop]; exact hprod)
    (γ₀ + δ) (List.mem_map.2 ⟨γ₀, List.mem_filter.2 ⟨hγ₀, by simp [hne, hr]⟩, rfl⟩)
  simp only [hd, add_sub_cancel_right] at hzero
  exact mul_ne_zero hN hc₀ hzero

theorem mem_rootSpan_of_commute_of_lead {τ : Tag} {S A : Set (Fin τ.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ)
    (hcent : ∀ γ ∈ A, ∀ δ ∈ S, ∀ c : K,
      pinnedX τ K γ c * pinnedX τ K δ 1 = pinnedX τ K δ 1 * pinnedX τ K γ c)
    (hdet : ∀ γ, IsRoot τ γ → 0 < height γ → γ ∉ A →
      ∃ δ ∈ S, γ ≠ δ ∧ IsRoot τ (γ + δ) ∧ (commConst τ γ δ (1, 1) : K) ≠ 0)
    {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ∈ rootSpan τ K A := by
  have hAc : ∀ a ∈ rootSpan τ K A, ∀ δ ∈ S,
      a * pinnedX τ K δ 1 = pinnedX τ K δ 1 * a := by
    intro a ha δ hδ
    rw [rootSpan_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨γ, hγ, c, rfl⟩ := hg
      exact hcent γ hγ δ hδ c
    | one => rw [one_mul, mul_one]
    | mul g h _ _ ihg ihh => exact Commute.mul_left ihg ihh
    | inv g _ ih => exact Commute.inv_left ih
  have key : ∀ k : ℕ, ∃ a ∈ rootSpan τ K A, ∃ w ∈ heightSeries τ K (1 + k), z = a * w := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, z, by simpa [heightSeries_one] using hz, (one_mul z).symm⟩
    | succ k ih =>
      obtain ⟨a, ha, w, hw, rfl⟩ := ih
      have hwc : ∀ δ ∈ S, w * pinnedX τ K δ 1 = pinnedX τ K δ 1 * w := fun δ hδ => by
        have h1 := hc δ hδ
        have h2 := hAc a ha δ hδ
        apply mul_left_cancel (a := a)
        calc a * (w * pinnedX τ K δ 1) = a * w * pinnedX τ K δ 1 := (mul_assoc _ _ _).symm
          _ = pinnedX τ K δ 1 * (a * w) := h1
          _ = pinnedX τ K δ 1 * a * w := (mul_assoc _ _ _).symm
          _ = a * pinnedX τ K δ 1 * w := by rw [h2]
          _ = a * (pinnedX τ K δ 1 * w) := mul_assoc _ _ _
      obtain ⟨a', ha', y, hy, rfl⟩ := exists_mul_of_commute_annih hS hdet (by omega) hw hwc
      refine ⟨a * a', mul_mem ha ha', y, ?_, (mul_assoc _ _ _).symm⟩
      rwa [show (1 : ℤ) + ((k + 1 : ℕ) : ℤ) = 1 + k + 1 by push_cast; ring]
  obtain ⟨a, ha, w, hw, rfl⟩ := key (maxHeight τ).toNat
  have h1 : (1 : ℤ) + ((maxHeight τ).toNat : ℤ) = maxHeight τ + 1 := by
    rw [Int.toNat_of_nonneg (by linarith [one_le_maxHeight τ])]
    ring
  rw [h1, heightSeries_maxHeight_add_one] at hw
  rw [(Subgroup.mem_bot).1 hw, mul_one]
  exact ha

theorem pinnedX_commute_of_forall_not_isRoot_annih {τ : Tag} {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hγp : 0 < height γ) (hδp : 0 < height δ)
    (h : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • γ + b • δ)) (c d : K) :
    pinnedX τ K γ c * pinnedX τ K δ d = pinnedX τ K δ d * pinnedX τ K γ c := by
  by_cases hne : γ = δ
  · subst hne
    exact rootSubgroup_mul_comm K (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨d, rfl⟩)
  have hle := commutator_rootSubgroup_le K hγ hδ hγp hδp hne
  have hbot : (⨆ (ε : Fin τ.rank → ℤ) (_ : IsRoot τ ε ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ ε = a • γ + b • δ), rootSubgroup τ K ε) = ⊥ :=
    iSup₂_eq_bot.2 fun ε ⟨hε, a, b, ha, hb, hεe⟩ => absurd (hεe ▸ hε) (h a b ha hb)
  rw [hbot] at hle
  have hmem := hle (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
    (Subgroup.subset_closure ⟨d, rfl⟩))
  exact commutatorElement_eq_one_iff_mul_comm.1 ((Subgroup.mem_bot).1 hmem)

theorem pinnedX_commute_of_mem_annRoots {τ : Tag} {S : Set (Fin τ.rank → ℤ)}
    {γ δ : Fin τ.rank → ℤ} (hγ : γ ∈ annRoots τ S) (hδ : IsRoot τ δ) (hδp : 0 < height δ)
    (hδS : δ ∈ S) (c d : K) :
    pinnedX τ K γ c * pinnedX τ K δ d = pinnedX τ K δ d * pinnedX τ K γ c :=
  pinnedX_commute_of_forall_not_isRoot_annih hγ.1 hδ hγ.2.1 hδp (hγ.2.2 δ hδS) c d

theorem ne_and_isRoot_add_of_isRoot_nsmul_add_nsmul {τ : Tag} {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hγp : 0 < height γ) (hδp : 0 < height δ) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h : IsRoot τ (a • γ + b • δ)) : γ ≠ δ ∧ IsRoot τ (γ + δ) := by
  have hne : γ ≠ δ := by
    rintro rfl
    have e : a • γ + b • γ = ((a + b : ℕ) : ℤ) • γ := by
      rw [← add_nsmul, natCast_zsmul]
    rw [e] at h
    rcases h.eq_one_or_neg_one_of_eq_smul rfl with h1 | h1 <;> omega
  have hne' : γ ≠ -δ := by
    rintro rfl
    have : height (-δ) = -height δ := by simp [height]
    linarith
  refine ⟨hne, ?_⟩
  have hmem := (mem_commPairs_iff_of_isRoot hγ hδ hne hne' (a, b)).2 ⟨ha, hb, h⟩
  obtain ⟨r, hr, hcp⟩ := exists_commPairs_eq_rep hγ hδ hne hne'
  have hchk := oneOneCheck_eq_true τ
  simp only [oneOneCheck, List.all_eq_true, Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hchk
  rcases hchk r hr with hnil | ⟨f, hf, hf1, hf2⟩
  · rw [hcp, hnil] at hmem
    exact absurd hmem List.not_mem_nil
  · have h11 : (1, 1) ∈ commPairs τ γ δ := by
      rw [hcp]
      exact List.mem_map.2 ⟨f, hf, Prod.ext hf1 hf2⟩
    simpa using ((mem_commPairs_iff_of_isRoot hγ hδ hne hne' (1, 1)).1 h11).2.2

theorem mem_annRoots_iff {τ : Tag} {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ) {γ : Fin τ.rank → ℤ} :
    γ ∈ annRoots τ S ↔ IsRoot τ γ ∧ 0 < height γ ∧ ∀ δ ∈ S, ¬ IsRoot τ (γ + δ) := by
  refine ⟨fun h => ⟨h.1, h.2.1, fun δ hδ hr => h.2.2 δ hδ 1 1 le_rfl le_rfl (by simpa using hr)⟩,
    fun h => ⟨h.1, h.2.1, fun δ hδ a b ha hb hr => h.2.2 δ hδ ?_⟩⟩
  exact (ne_and_isRoot_add_of_isRoot_nsmul_add_nsmul h.1 (hS δ hδ).1 h.2.1 (hS δ hδ).2 ha hb
    hr).2

theorem mem_rootSpan_annRoots_of_commute {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ) {z : ModGL τ K}
    (hz : z ∈ posUnipotent τ K) (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ∈ rootSpan τ K (annRoots τ S) := by
  refine mem_rootSpan_of_commute_of_lead hS (fun γ hγ δ hδ c =>
    pinnedX_commute_of_mem_annRoots hγ (hS δ hδ).1 (hS δ hδ).2 hδ c 1) (fun γ hγ hγp hA => ?_)
    hz hc
  obtain ⟨δ, hδS, hδ⟩ : ∃ δ ∈ S, ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ IsRoot τ (a • γ + b • δ) := by
    by_contra hcon
    exact hA ⟨hγ, hγp, fun δ hδ a b ha hb hr => hcon ⟨δ, hδ, a, b, ha, hb, hr⟩⟩
  obtain ⟨a, b, ha, hb, hr⟩ := hδ
  obtain ⟨hδr, hδp⟩ := hS δ hδS
  obtain ⟨hne, hadd⟩ := ne_and_isRoot_add_of_isRoot_nsmul_add_nsmul hγ hδr hγp hδp ha hb hr
  have hne' : γ ≠ -δ := by
    rintro rfl
    have : height (-δ) = -height δ := by simp [height]
    linarith
  refine ⟨δ, hδS, hne, hadd, ?_⟩
  rcases ((simply_laced_root_commutator_unit.{0} τ hτ hγ hδr hne hne').1 hadd).1 with h | h <;>
    rw [h] <;> simp

theorem commConst_cast_ne_zero_annih {τ : Tag} {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hr : IsRoot τ (γ + δ)) (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) : (commConst τ γ δ (1, 1) : K) ≠ 0 := by
  obtain ⟨-, hmem, -, hC, -⟩ := root_commutator_formula.{0} τ hγ hδ hne hne'
  obtain ⟨hl, hu⟩ := hC (1, 1) ((hmem (1, 1)).2 ⟨one_pos, one_pos, by simpa using hr⟩)
  have hcases : commConst τ γ δ (1, 1) = 1 ∨ commConst τ γ δ (1, 1) = -1 ∨
      commConst τ γ δ (1, 1) = 2 ∨ commConst τ γ δ (1, 1) = -2 ∨
      commConst τ γ δ (1, 1) = 3 ∨ commConst τ γ δ (1, 1) = -3 := by
    rcases abs_cases (commConst τ γ δ (1, 1)) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rcases hcases with h | h | h | h | h | h <;> rw [h] <;> simp [h2, h3]

theorem mem_rootSpan_annRoots_of_commute_of_two_three {τ : Tag} (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {S : Set (Fin τ.rank → ℤ)} (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ)
    {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ∈ rootSpan τ K (annRoots τ S) := by
  refine mem_rootSpan_of_commute_of_lead hS (fun γ hγ δ hδ c =>
    pinnedX_commute_of_mem_annRoots hγ (hS δ hδ).1 (hS δ hδ).2 hδ c 1) (fun γ hγ hγp hA => ?_)
    hz hc
  obtain ⟨δ, hδS, hδ⟩ : ∃ δ ∈ S, ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ IsRoot τ (a • γ + b • δ) := by
    by_contra hcon
    exact hA ⟨hγ, hγp, fun δ hδ a b ha hb hr => hcon ⟨δ, hδ, a, b, ha, hb, hr⟩⟩
  obtain ⟨a, b, ha, hb, hr⟩ := hδ
  obtain ⟨hδr, hδp⟩ := hS δ hδS
  obtain ⟨hne, hadd⟩ := ne_and_isRoot_add_of_isRoot_nsmul_add_nsmul hγ hδr hγp hδp ha hb hr
  have hne' : γ ≠ -δ := by
    rintro rfl
    have : height (-δ) = -height δ := by simp [height]
    linarith
  exact ⟨δ, hδS, hne, hadd, commConst_cast_ne_zero_annih hγ hδr hne hne' hadd h2 h3⟩

theorem sq_eq_one_of_commute_of_annRoots_pairwise [CharP K 2] {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ)
    (hpair : ∀ γ ∈ annRoots τ S, ∀ γ' ∈ annRoots τ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬ IsRoot τ (a • γ + b • γ'))
    {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ^ 2 = 1 :=
  sq_eq_one_of_mem_rootSpan_annih (fun γ hγ γ' hγ' c d =>
    pinnedX_commute_of_forall_not_isRoot_annih hγ.1 hγ'.1 hγ.2.1 hγ'.2.1 (hpair γ hγ γ' hγ') c d)
    (mem_rootSpan_annRoots_of_commute hτ hS hz hc)

theorem sq_eq_one_of_commute_of_annRoots_add [CharP K 2] {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot τ δ ∧ 0 < height δ)
    (hpair : ∀ γ ∈ annRoots τ S, ∀ γ' ∈ annRoots τ S, ¬ IsRoot τ (γ + γ'))
    {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ^ 2 = 1 :=
  sq_eq_one_of_commute_of_annRoots_pairwise hτ hS (fun γ hγ γ' hγ' _ _ ha hb hr => hpair γ hγ γ'
    hγ' (ne_and_isRoot_add_of_isRoot_nsmul_add_nsmul hγ.1 hγ'.1 hγ.2.1 hγ'.2.1 ha hb hr).2)
    hz hc

theorem mem_rootSpan_of_commute_of_annListCheck {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {S L : List (Fin τ.rank → ℤ)}
    {M : ℤ} (hchk : annListCheck τ M S L = true) {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ∈ rootSpan τ K {γ | γ ∈ L} := by
  obtain ⟨hS, -, hcov, -⟩ := annListCheck_sound hchk
  have hz' := mem_rootSpan_annRoots_of_commute (S := {δ | δ ∈ S}) hτ hS hz hc
  refine (biSup_mono fun γ hγ => ?_ : rootSpan τ K (annRoots τ {δ | δ ∈ S}) ≤
    rootSpan τ K {γ | γ ∈ L}) hz'
  rw [mem_annRoots_iff (S := {δ | δ ∈ S}) hS] at hγ
  exact hcov γ hγ.1 hγ.2.1 hγ.2.2

theorem sq_eq_one_of_commute_of_annListCheck [CharP K 2] {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {S L : List (Fin τ.rank → ℤ)}
    {M : ℤ} (hchk : annListCheck τ M S L = true) {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ δ ∈ S, z * pinnedX τ K δ 1 = pinnedX τ K δ 1 * z) :
    z ^ 2 = 1 := by
  obtain ⟨-, hL, -, hpair⟩ := annListCheck_sound hchk
  refine sq_eq_one_of_mem_rootSpan_annih (fun γ hγ γ' hγ' c d => ?_)
    (mem_rootSpan_of_commute_of_annListCheck hτ hchk hz hc)
  refine pinnedX_commute_of_forall_not_isRoot_annih (hL γ hγ).1 (hL γ' hγ').1 (hL γ hγ).2
    (hL γ' hγ').2 (fun a b ha hb hr => hpair γ hγ γ' hγ' ?_) c d
  exact (ne_and_isRoot_add_of_isRoot_nsmul_add_nsmul (hL γ hγ).1 (hL γ' hγ').1 (hL γ hγ).2
    (hL γ' hγ').2 ha hb hr).2

theorem sq_eq_one_of_commute_heightSeries_of_annListCheck [CharP K 2] {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {h : ℤ} {S L : List (Fin τ.rank → ℤ)}
    {M : ℤ} (hchk : annListCheck τ M S L = true) (hSh : ∀ δ ∈ S, h ≤ height δ) {u : ModGL τ K}
    (hu : u ∈ posUnipotent τ K) (hc : ∀ x ∈ heightSeries τ K h, u * x = x * u) :
    u ^ 2 = 1 :=
  sq_eq_one_of_commute_of_annListCheck hτ hchk hu fun δ hδ =>
    hc _ (pinnedX_mem_heightSeries_annih ((annListCheck_sound hchk).1 δ hδ).1
      ((annListCheck_sound hchk).1 δ hδ).2 (hSh δ hδ) 1)

end Main

theorem annListCheck_E6_simple :
    annListCheck .E6 11 (List.ofFn fun i => Pi.single i 1) [![1, 2, 2, 3, 2, 1]] = true := by
  decide +kernel

theorem annListCheck_E7_simple :
    annListCheck .E7 17 (List.ofFn fun i => Pi.single i 1) [![2, 2, 3, 4, 3, 2, 1]] = true := by
  decide +kernel

theorem annListCheck_E8_simple :
    annListCheck .E8 29 (List.ofFn fun i => Pi.single i 1) [![2, 3, 4, 6, 5, 4, 3, 2]] = true := by
  decide +kernel

end CFSG.SeitzReduction
