module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open Module

section Graded

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]

theorem finrank_range_le_of_graded (F : ι → ℤ) (s : ℤ) (ψ n : Module.End K (ι →₀ K))
    (hψ : ∀ b j, ψ (Finsupp.single b 1) j ≠ 0 → F j = F b + s)
    (hn : ∀ b j, n (Finsupp.single b 1) j ≠ 0 → F b + s < F j) :
    finrank K (LinearMap.range ψ) ≤ finrank K (LinearMap.range (ψ + n)) := by
  classical
  let v : ι → (ι →₀ K) := fun b => ψ (Finsupp.single b 1)
  obtain ⟨b, -, -, hspan, hli⟩ := exists_linearIndepOn_extension (K := K) (v := v)
    (s := (∅ : Set ι)) (t := Set.univ) (linearIndepOn_empty K v) (Set.empty_subset _)
  have hrange : LinearMap.range ψ ≤ Submodule.span K (v '' b) := by
    have hr : Set.range v ⊆ Submodule.span K (v '' b) := by
      rintro _ ⟨i, rfl⟩
      exact hspan ⟨i, Set.mem_univ _, rfl⟩
    have h1 : ∀ w : ι →₀ K, ψ w ∈ Submodule.span K (v '' b) := by
      intro w
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
      | single i x =>
        have e : (Finsupp.single i x : ι →₀ K) = x • Finsupp.single i 1 := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [e, map_smul]
        exact Submodule.smul_mem _ _ (hr ⟨i, rfl⟩)
    rintro _ ⟨w, rfl⟩
    exact h1 w
  have hb : b.Finite := Set.toFinite b
  set B : Finset ι := hb.toFinset with hBdef
  have hbB : (B : Set ι) = b := hb.coe_toFinset
  have himg : v '' b = ((B.image v : Finset (ι →₀ K)) : Set (ι →₀ K)) := by
    rw [Finset.coe_image, hbB]
  have hup : finrank K (LinearMap.range ψ) ≤ B.card := by
    have h1 : finrank K (Submodule.span K (v '' b)) ≤ (B.image v).card := by
      rw [himg]
      exact finrank_span_finset_le_card (B.image v)
    exact (Submodule.finrank_mono hrange).trans (h1.trans Finset.card_image_le)
  set φ := ψ + n with hφ
  have hli' : LinearIndepOn K (fun i => φ (Finsupp.single i 1)) b := by
    rw [linearIndepOn_iff'] at hli ⊢
    intro t g htb hsum
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, hi0t, hi0g⟩ := hcon
    set t' := t.filter (fun i => g i ≠ 0) with ht'
    have ht'ne : t'.Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0t, hi0g⟩⟩
    obtain ⟨i1, hi1, hmin⟩ := Finset.exists_min_image t' F ht'ne
    set m := F i1 with hm
    set t'' := t'.filter (fun i => F i = m) with ht''
    have ht''t : t'' ⊆ t := fun i hi => (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
    have hzero : ∑ i ∈ t'', g i • v i = 0 := by
      ext j
      rw [Finsupp.finsetSum_apply, Finsupp.zero_apply]
      simp only [Finsupp.smul_apply, smul_eq_mul, v]
      by_cases hj : F j = m + s
      · have h0 := congrArg (fun w => w j) hsum
        simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply,
          hφ, LinearMap.add_apply, Finsupp.add_apply, mul_add, Finset.sum_add_distrib] at h0
        have hn0 : ∑ i ∈ t, g i * n (Finsupp.single i 1) j = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          by_cases hgi : g i = 0
          · rw [hgi, zero_mul]
          · have hFi : m ≤ F i := hmin i (Finset.mem_filter.2 ⟨hi, hgi⟩)
            by_contra hne
            have := hn i j (fun h => hne (by rw [h, mul_zero]))
            omega
        have hψ0 : ∑ i ∈ t, g i * ψ (Finsupp.single i 1) j =
            ∑ i ∈ t'', g i * ψ (Finsupp.single i 1) j := by
          symm
          refine Finset.sum_subset ht''t fun i hi hi'' => ?_
          by_cases hgi : g i = 0
          · rw [hgi, zero_mul]
          · have hFi : m ≤ F i := hmin i (Finset.mem_filter.2 ⟨hi, hgi⟩)
            have hFne : F i ≠ m := fun h =>
              hi'' (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hi, hgi⟩, h⟩)
            by_contra hne
            have := hψ i j (fun h => hne (by rw [h, mul_zero]))
            omega
        rw [hn0, add_zero, hψ0] at h0
        exact h0
      · refine Finset.sum_eq_zero fun i hi => ?_
        have hFi : F i = m := (Finset.mem_filter.1 hi).2
        by_cases hz : ψ (Finsupp.single i 1) j = 0
        · rw [hz, mul_zero]
        · exact absurd (by have := hψ i j hz; omega) hj
    have := hli t'' g (by
      intro i hi
      exact htb (ht''t hi)) hzero i1 (Finset.mem_filter.2 ⟨hi1, rfl⟩)
    exact (Finset.mem_filter.1 hi1).2 this
  have hlow : B.card ≤ finrank K (LinearMap.range φ) := by
    have hw : LinearIndependent K (fun x : b => φ (Finsupp.single (x : ι) 1)) := hli'
    have h1 : finrank K (Submodule.span K (Set.range fun x : b => φ (Finsupp.single (x : ι) 1))) =
        Fintype.card b := finrank_span_eq_card hw
    have h2 : Submodule.span K (Set.range fun x : b => φ (Finsupp.single (x : ι) 1)) ≤
        LinearMap.range φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    have h3 := Submodule.finrank_mono h2
    have h4 : Fintype.card b = B.card := by
      rw [← hbB]; simp
    omega
  omega

end Graded

section Perm

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]

theorem card_le_finrank_range_of_perm (E : Module.End K (ι →₀ K)) (S : Finset ι) (σ : ι → ι)
    (c : ι → K) (hσ : Set.InjOn σ S) (hc : ∀ b ∈ S, c b ≠ 0)
    (hE : ∀ b ∈ S, E (Finsupp.single b 1) = c b • Finsupp.single (σ b) 1) :
    S.card ≤ finrank K (LinearMap.range E) := by
  classical
  have hli : LinearIndependent K (fun x : S => E (Finsupp.single (x : ι) 1)) := by
    have h1 : LinearIndependent K (fun x : S => (Finsupp.single (σ x) 1 : ι →₀ K)) := by
      have := (Finsupp.basisSingleOne (R := K) (ι := ι)).linearIndependent
      have h2 : LinearIndependent K (fun x : S => (Finsupp.basisSingleOne (R := K) (ι := ι)) (σ x)) :=
        this.comp (fun x : S => σ x) (fun x y h => Subtype.ext (hσ x.2 y.2 h))
      simpa using h2
    have h3 : (fun x : S => E (Finsupp.single (x : ι) 1)) =
        fun x : S => c x • (Finsupp.single (σ x) 1 : ι →₀ K) := funext fun x => hE x x.2
    rw [h3]
    have h4 := h1.units_smul (fun x => Units.mk0 (c x) (hc x x.2))
    have e : ((fun x : S => Units.mk0 (c x) (hc x x.2)) • fun x : S =>
        (Finsupp.single (σ x) 1 : ι →₀ K)) = fun x : S => c x • (Finsupp.single (σ x) 1 : ι →₀ K) := by
      funext x
      simp [Units.smul_def]
    exact e ▸ h4
  have h1 := finrank_span_eq_card hli
  have h2 : Submodule.span K (Set.range fun x : S => E (Finsupp.single (x : ι) 1)) ≤
      LinearMap.range E := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have h3 := Submodule.finrank_mono h2
  rw [h1, Fintype.card_coe] at h3
  exact h3

end Perm

section Quot

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem finrank_range_le_mapQ_add_one (φ : Module.End K V) (L : Submodule K V)
    (hL : finrank K L ≤ 1) (h : L ≤ L.comap φ) :
    finrank K (LinearMap.range φ) ≤ finrank K (LinearMap.range (L.mapQ L φ h)) + 1 := by
  set S := LinearMap.range φ with hS
  let q : S →ₗ[K] V ⧸ L := L.mkQ.domRestrict S
  have h1 := LinearMap.finrank_range_add_finrank_ker q
  have hr : LinearMap.range q = LinearMap.range (L.mapQ L φ h) := by
    ext y
    constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩
      exact ⟨Submodule.Quotient.mk x, by simp [q]⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L z
      exact ⟨⟨φ x, ⟨x, rfl⟩⟩, by simp [q]⟩
  have hk : finrank K (LinearMap.ker q) ≤ 1 := by
    let g : LinearMap.ker q →ₗ[K] L := LinearMap.codRestrict L
      (S.subtype ∘ₗ (LinearMap.ker q).subtype) (fun x => by
        have h0 : q x.1 = 0 := LinearMap.mem_ker.1 x.2
        have h1 : (Submodule.Quotient.mk (x.1 : V) : V ⧸ L) = 0 := h0
        exact (Submodule.Quotient.mk_eq_zero L).1 h1)
    have hg : Function.Injective g := by
      intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
    exact (LinearMap.finrank_le_finrank_of_injective hg).trans hL
  rw [hr] at h1
  omega

end Quot

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
