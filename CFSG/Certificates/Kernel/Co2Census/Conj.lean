module

public import CFSG.Certificates.Kernel.Co2Census.OrbSound
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Co2Census

variable {G : Type*} [Group G]

abbrev gensSub (g : ℕ → G) (ngen : ℕ) : Subgroup G := Subgroup.closure (g '' {l | l < ngen})

theorem gen_mem (g : ℕ → G) {ngen l : ℕ} (hl : l < ngen) : g l ∈ gensSub g ngen :=
  Subgroup.subset_closure ⟨l, hl, rfl⟩

@[expose] def ConjSteps (rep : G → ℕ → Prop) (step : ℕ → ℕ → ℕ) (ngen : ℕ) (g : ℕ → G) : Prop :=
  ∀ l < ngen, ∀ x M, rep x M → rep (g l * x * (g l)⁻¹) (step l M)

@[expose] def MulSteps (rep : G → ℕ → Prop) (step : ℕ → ℕ → ℕ) (ngen : ℕ) (g : ℕ → G) : Prop :=
  ∀ l < ngen, ∀ x M, rep x M → rep (x * g l) (step l M)

theorem reach_conj {rep : G → ℕ → Prop} {step : ℕ → ℕ → ℕ} {ngen : ℕ} {g : ℕ → G}
    (hs : ConjSteps rep step ngen g) {M M' : ℕ}
    (h : Relation.ReflTransGen (StepRel step ngen) M M') {x : G} (hx : rep x M) :
    ∃ w ∈ gensSub g ngen, rep (w * x * w⁻¹) M' := by
  induction h with
  | refl => exact ⟨1, Subgroup.one_mem _, by simpa using hx⟩
  | tail _ hst ih =>
    obtain ⟨w, hw, hr⟩ := ih
    obtain ⟨l, hl, rfl⟩ := hst
    refine ⟨g l * w, Subgroup.mul_mem _ (gen_mem g hl) hw, ?_⟩
    have e : g l * w * x * (g l * w)⁻¹ = g l * (w * x * w⁻¹) * (g l)⁻¹ := by group
    rw [e]
    exact hs l hl _ _ hr

theorem reach_mul {rep : G → ℕ → Prop} {step : ℕ → ℕ → ℕ} {ngen : ℕ} {g : ℕ → G}
    (hs : MulSteps rep step ngen g) {M M' : ℕ}
    (h : Relation.ReflTransGen (StepRel step ngen) M M') {x : G} (hx : rep x M) :
    ∃ w ∈ gensSub g ngen, rep (x * w) M' := by
  induction h with
  | refl => exact ⟨1, Subgroup.one_mem _, by simpa using hx⟩
  | tail _ hst ih =>
    obtain ⟨w, hw, hr⟩ := ih
    obtain ⟨l, hl, rfl⟩ := hst
    refine ⟨w * g l, Subgroup.mul_mem _ hw (gen_mem g hl), ?_⟩
    rw [← mul_assoc]
    exact hs l hl _ _ hr

theorem conj_closure {S : Set G} (hS : S.Finite) {g : ℕ → G} {ngen : ℕ}
    (hc : ∀ l < ngen, ∀ y ∈ S, g l * y * (g l)⁻¹ ∈ S) :
    ∀ w ∈ gensSub g ngen, ∀ y ∈ S, w * y * w⁻¹ ∈ S := by
  have key : ∀ w : G, (∀ y ∈ S, w * y * w⁻¹ ∈ S) → ∀ y ∈ S, w⁻¹ * y * w⁻¹⁻¹ ∈ S := by
    intro w hw
    have hmaps : Set.MapsTo (fun y => w * y * w⁻¹) S S := hw
    have hinj : Set.InjOn (fun y => w * y * w⁻¹) S := fun a _ b _ h => by
      simpa using h
    have hbij := (hS.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
    intro y hy
    obtain ⟨y', hy', e⟩ := hbij.surjOn hy
    have : w⁻¹ * y * w⁻¹⁻¹ = y' := by
      rw [← e]
      group
    rw [this]
    exact hy'
  let H : Subgroup G :=
    { carrier := {w | ∀ y ∈ S, w * y * w⁻¹ ∈ S}
      mul_mem' := fun {a b} ha hb y hy => by
        have := ha _ (hb y hy)
        have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        rw [e]
        exact this
      one_mem' := fun y hy => by simpa using hy
      inv_mem' := fun {w} hw => key w hw }
  have hle : gensSub g ngen ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hc l hl
  exact fun w hw => hle hw

theorem mul_closure {S : Set G} (hS : S.Finite) (h1 : (1 : G) ∈ S) {g : ℕ → G} {ngen : ℕ}
    (hc : ∀ l < ngen, ∀ y ∈ S, y * g l ∈ S) : ∀ w ∈ gensSub g ngen, w ∈ S := by
  have key : ∀ w : G, (∀ y ∈ S, y * w ∈ S) → ∀ y ∈ S, y * w⁻¹ ∈ S := by
    intro w hw
    have hmaps : Set.MapsTo (fun y => y * w) S S := hw
    have hinj : Set.InjOn (fun y => y * w) S := fun a _ b _ h => by
      simpa using h
    have hbij := (hS.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
    intro y hy
    obtain ⟨y', hy', e⟩ := hbij.surjOn hy
    have : y * w⁻¹ = y' := by
      rw [← e]
      group
    rw [this]
    exact hy'
  let H : Subgroup G :=
    { carrier := {w | ∀ y ∈ S, y * w ∈ S}
      mul_mem' := fun {a b} ha hb y hy => by
        rw [← mul_assoc]
        exact hb _ (ha y hy)
      one_mem' := fun y hy => by simpa using hy
      inv_mem' := fun {w} hw => key w hw }
  have hle : gensSub g ngen ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hc l hl
  intro w hw
  simpa using hle hw 1 h1

variable {rep : G → ℕ → Prop} {step : ℕ → ℕ → ℕ} {ngen N : ℕ} {P IX : ℕ → ℕ} {g : ℕ → G}

@[expose] def segSet (rep : G → ℕ → Prop) (N : ℕ) (P IX : ℕ → ℕ) (k : ℕ) : Set G :=
  {y | ∃ i < N, rtOf IX i = k ∧ rep y (P i)}

theorem pts_finite (hfun : ∀ x y M, rep x M → rep y M → x = y) :
    {y | ∃ i < N, rep y (P i)}.Finite := by
  classical
  let f : ℕ → G := fun i => if h : ∃ y, rep y (P i) then h.choose else 1
  refine Set.Finite.subset ((Finset.range N).image f).finite_toSet ?_
  rintro y ⟨i, hi, hy⟩
  have hex : ∃ y, rep y (P i) := ⟨y, hy⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, ?_⟩)
  simp only [f, dif_pos hex]
  exact hfun _ _ _ hex.choose_spec hy

theorem segSet_finite (hfun : ∀ x y M, rep x M → rep y M → x = y) (k : ℕ) :
    (segSet rep N P IX k).Finite := by
  refine (pts_finite (N := N) (P := P) hfun).subset ?_
  rintro y ⟨i, hi, -, hy⟩
  exact ⟨i, hi, hy⟩

theorem seg_class (hfun : ∀ x y M, rep x M → rep y M → x = y) (hs : ConjSteps rep step ngen g)
    (ht : ∀ i < N, treeK step ngen N P IX i = true) (hc : ∀ i < N, closK step ngen N P IX i = true)
    {k : ℕ} (hk : k < N) (hkk : rtOf IX k = k) {x : G} (hx : rep x (P k)) :
    segSet rep N P IX k = {y | ∃ w ∈ gensSub g ngen, y = w * x * w⁻¹} := by
  have tf := treeK_sound ht
  have cf := closK_sound hc
  ext y
  constructor
  · rintro ⟨i, hi, hik, hy⟩
    obtain ⟨-, -, hreach⟩ := tf.1 i hi
    rw [hik] at hreach
    obtain ⟨w, hw, hr⟩ := reach_conj hs hreach hx
    exact ⟨w, hw, hfun _ _ _ hy hr⟩
  · rintro ⟨w, hw, rfl⟩
    have hclosed : ∀ l < ngen, ∀ y ∈ segSet rep N P IX k, g l * y * (g l)⁻¹ ∈ segSet rep N P IX k := by
      rintro l hl y ⟨i, hi, hik, hy⟩
      obtain ⟨j, hj, hjr, he⟩ := cf i hi l hl
      exact ⟨j, hj, hjr.trans hik, he ▸ hs l hl _ _ hy⟩
    exact conj_closure (segSet_finite hfun k) hclosed w hw x ⟨k, hk, hkk, hx⟩

theorem seg_ncard (hfun : ∀ x y M, rep x M → rep y M → x = y)
    (huniq : ∀ x M M', rep x M → rep x M' → M = M') (hs : ConjSteps rep step ngen g)
    (ht : ∀ i < N, treeK step ngen N P IX i = true) {k : ℕ} (hk : k < N) (hkk : rtOf IX k = k)
    {x : G} (hx : rep x (P k)) :
    (segSet rep N P IX k).ncard = ((Finset.range N).filter fun i => rtOf IX i = k).card := by
  classical
  have tf := treeK_sound ht
  have hex : ∀ i ∈ (Finset.range N).filter (fun i => rtOf IX i = k), ∃ y, rep y (P i) := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨-, -, hreach⟩ := tf.1 i hi.1
    rw [hi.2] at hreach
    obtain ⟨w, -, hr⟩ := reach_conj hs hreach hx
    exact ⟨_, hr⟩
  let f : ℕ → G := fun i => if h : ∃ y, rep y (P i) then h.choose else 1
  have hf : ∀ i ∈ (Finset.range N).filter (fun i => rtOf IX i = k), rep (f i) (P i) := by
    intro i hi
    simp only [f, dif_pos (hex i hi)]
    exact (hex i hi).choose_spec
  have himg : segSet rep N P IX k = ((Finset.range N).filter fun i => rtOf IX i = k).image f := by
    ext y
    simp only [segSet, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨i, hi, hik, hy⟩
      have hm : i ∈ (Finset.range N).filter (fun i => rtOf IX i = k) := by
        rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hi, hik⟩
      exact ⟨i, hm, hfun _ _ _ (hf i hm) hy⟩
    · rintro ⟨i, hm, rfl⟩
      have hm' := hm
      rw [Finset.mem_filter, Finset.mem_range] at hm'
      exact ⟨i, hm'.1, hm'.2, hf i hm⟩
  rw [himg, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  intro i hi j hj e
  have hi' := hi
  have hj' := hj
  rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi' hj'
  have h1 := hf i hi
  have h2 := hf j hj
  rw [show f i = f j from e] at h1
  exact tf.2 i hi'.1 j hj'.1 (huniq _ _ _ h1 h2)

theorem pts_ncard (hfun : ∀ x y M, rep x M → rep y M → x = y)
    (huniq : ∀ x M M', rep x M → rep x M' → M = M') (hex : ∀ i < N, ∃ y, rep y (P i))
    (hinj : ∀ i < N, ∀ j < N, P i = P j → i = j) :
    {y | ∃ i < N, rep y (P i)}.ncard = N := by
  classical
  let f : ℕ → G := fun i => if h : ∃ y, rep y (P i) then h.choose else 1
  have hf : ∀ i < N, rep (f i) (P i) := by
    intro i hi
    simp only [f, dif_pos (hex i hi)]
    exact (hex i hi).choose_spec
  have himg : {y | ∃ i < N, rep y (P i)} = (Finset.range N).image f := by
    ext y
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hy⟩
      exact ⟨i, hi, hfun _ _ _ (hf i hi) hy⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, hf i hi⟩
  rw [himg, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj e
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  have h1 := hf i hi
  have h2 := hf j hj
  rw [show f i = f j from e] at h1
  exact hinj i hi j hj (huniq _ _ _ h1 h2)

theorem mul_record (hfun : ∀ x y M, rep x M → rep y M → x = y) (hs : MulSteps rep step ngen g)
    (ht : ∀ i < N, treeK step ngen N P IX i = true) (hc : ∀ i < N, closK step ngen N P IX i = true)
    (hN : 0 < N) (h0 : ∀ i < N, rtOf IX i = 0) (hx : rep 1 (P 0)) :
    {y | ∃ i < N, rep y (P i)} = (gensSub g ngen : Set G) := by
  have tf := treeK_sound ht
  have cf := closK_sound hc
  ext y
  constructor
  · rintro ⟨i, hi, hy⟩
    obtain ⟨-, -, hreach⟩ := tf.1 i hi
    rw [h0 i hi] at hreach
    obtain ⟨w, hw, hr⟩ := reach_mul hs hreach hx
    rw [one_mul] at hr
    exact (hfun _ _ _ hy hr) ▸ hw
  · intro hy
    refine mul_closure (pts_finite hfun) ⟨0, hN, hx⟩ (fun l hl y ⟨i, hi, hy⟩ => ?_) y hy
    obtain ⟨j, hj, -, he⟩ := cf i hi l hl
    exact ⟨j, hj, he ▸ hs l hl _ _ hy⟩

end CFSG.KC.Co2Census

end
