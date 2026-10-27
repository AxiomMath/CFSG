module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fk3_polar_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (x y : V) :
    QuadraticMap.polar Q x y = ∑ i, 2 * c i * (fr.b.repr x i * fr.b.repr y i) := by
  rw [QuadraticMap.polar, fr.map_eq (x + y), fr.map_eq x, fr.map_eq y, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, Finsupp.add_apply]
  ring

theorem ffOutFFE8Cent_polar_basis {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (i : ι) (x : V) :
    QuadraticMap.polar Q (fr.b i) x = 2 * c i * fr.b.repr x i := by
  rw [fk3_polar_eq fr, Finset.sum_eq_single i]
  · rw [Module.Basis.repr_self_apply, if_pos rfl]
    ring
  · intro j _ hj
    rw [Module.Basis.repr_self_apply, if_neg (Ne.symm hj)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ffOutFFE8Cent_Q_single {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (v : V) (j : ι) (h : ∀ i, i ≠ j → fr.b.repr v i = 0) :
    Q v = c j * fr.b.repr v j ^ 2 := by
  rw [fr.map_eq v, Finset.sum_eq_single j]
  · intro i _ hij
    rw [h i hij]
    ring
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem ffOutFFE8Cent_eigen_sign {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (J : Finset ι) {v : V} {s : ZMod 3}
    (h : ((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) v = s • v) {i : ι}
    (hi : fr.b.repr v i ≠ 0) : s = if i ∈ J then -1 else 1 := by
  have h' := congrArg (fun x => fr.b.repr x i) h
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, fr.repr_signChange] at h'
  by_cases hiJ : i ∈ J
  · rw [if_pos hiJ] at h'
    rw [if_pos hiJ]
    refine mul_right_cancel₀ hi ?_
    rw [neg_one_mul]
    exact h'.symm
  · rw [if_neg hiJ] at h'
    rw [if_neg hiJ]
    refine mul_right_cancel₀ hi ?_
    rw [one_mul]
    exact h'.symm

theorem ffOutFFE8Cent_group_inl {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {e : OGroup Q}
    (he : e ∈ ffE8Group fr) (i : Fin 2) :
    (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inl i)) = fr.b (Sum.inl i) := by
  rw [mem_ffE8Group_iff] at he
  obtain ⟨J, -, rfl⟩ := he
  rw [fr.signChange_basis]
  simp [ffE8Hat]

theorem ffOutFFE8Cent_group_inr {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {e : OGroup Q}
    (he : e ∈ ffE8Group fr) (k : Fin 4) :
    (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inr k)) = fr.b (Sum.inr k) ∨
      (e : V ≃ₗ[ZMod 3] V) (fr.b (Sum.inr k)) = -fr.b (Sum.inr k) := by
  rw [mem_ffE8Group_iff] at he
  obtain ⟨J, -, rfl⟩ := he
  rw [fr.signChange_basis]
  by_cases hk : k ∈ J
  · right
    rw [if_pos (by simpa [ffE8Hat] using hk)]
  · left
    rw [if_neg (by simpa [ffE8Hat] using hk)]

private theorem fk3_exists_ne (k : Fin 4) : ∃ m : Fin 4, k ≠ m := by
  have h : ∀ k : Fin 4, ∃ m : Fin 4, k ≠ m := by decide
  exact h k

private theorem fk3_exists_ne_ne (k l : Fin 4) : ∃ m : Fin 4, k ≠ m ∧ l ≠ m := by
  have h : ∀ k l : Fin 4, ∃ m : Fin 4, k ≠ m ∧ l ≠ m := by decide
  exact h k l

private theorem fk3_supp_of_mem {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u w : V}
    (hs : ∀ J : Finset (Fin 4), Even J.card → ∃ s : ZMod 3,
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = s • u ∧
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) w = s • w)
    {k : Fin 4} (hk : fr.b.repr u (Sum.inr k) ≠ 0) {J : Finset (Fin 4)} (hJ : Even J.card)
    (hkJ : k ∈ J) {i : FFE8Idx} (hi : i ∉ ffE8Hat J) :
    fr.b.repr u i = 0 ∧ fr.b.repr w i = 0 := by
  obtain ⟨s, hsu, hsw⟩ := hs J hJ
  have hkJ' : Sum.inr k ∈ ffE8Hat J := by
    rw [ffE8Hat]
    exact (Finset.mem_map' Function.Embedding.inr).2 hkJ
  have hsneg : s = -1 := by
    have h := ffOutFFE8Cent_eigen_sign fr (ffE8Hat J) hsu (i := Sum.inr k) hk
    rw [if_pos hkJ'] at h
    exact h
  have hcoord : ∀ {x : V}, ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) x = s • x →
      fr.b.repr x i = -fr.b.repr x i := by
    intro x hx
    have h := congrArg (fun y => fr.b.repr y i) hx
    rw [fr.repr_signChange, if_neg hi, map_smul, Finsupp.smul_apply, smul_eq_mul, hsneg,
      neg_one_mul] at h
    exact h
  have vanish : ∀ {x : V}, ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) x = s • x →
      fr.b.repr x i = 0 := by
    intro x hx
    have h := hcoord hx
    have h2 : (2 : ZMod 3) * fr.b.repr x i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  exact ⟨vanish hsu, vanish hsw⟩

theorem ffOutFFE8Cent_supp {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u w : V}
    (hs : ∀ J : Finset (Fin 4), Even J.card → ∃ s : ZMod 3,
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = s • u ∧
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) w = s • w)
    {k : Fin 4} (hk : fr.b.repr u (Sum.inr k) ≠ 0) {i : FFE8Idx} (hi : i ≠ Sum.inr k) :
    fr.b.repr u i = 0 ∧ fr.b.repr w i = 0 := by
  rcases i with n | l
  · obtain ⟨m, hkm⟩ := fk3_exists_ne k
    have hJ : Even ({k, m} : Finset (Fin 4)).card := by
      rw [Finset.card_pair hkm]
      decide
    have hi' : (Sum.inl n : FFE8Idx) ∉ ffE8Hat ({k, m} : Finset (Fin 4)) := by
      simp [ffE8Hat]
    exact fk3_supp_of_mem fr hs hk (J := {k, m}) hJ (by simp) hi'
  · have hlk : l ≠ k := fun h => hi (by rw [h])
    obtain ⟨m, hkm, hlm⟩ := fk3_exists_ne_ne k l
    have hJ : Even ({k, m} : Finset (Fin 4)).card := by
      rw [Finset.card_pair hkm]
      decide
    have hlm' : l ∉ ({k, m} : Finset (Fin 4)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hi' : (Sum.inr l : FFE8Idx) ∉ ffE8Hat ({k, m} : Finset (Fin 4)) := by
      simpa [ffE8Hat] using hlm'
    exact fk3_supp_of_mem fr hs hk (J := {k, m}) hJ (by simp) hi'

private theorem fk3_inW_pair {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {δ : V ≃ₗ[ZMod 3] V}
    (hδ : ∀ e ∈ ffE8Group fr, ∃ e'' ∈ ffE8Group fr, ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧
      ∀ v, (e : V ≃ₗ[ZMod 3] V) (δ v) = s • δ ((e'' : V ≃ₗ[ZMod 3] V) v))
    {i i' : Fin 2} (hii : i ≠ i') (k : Fin 4) :
    fr.b.repr (δ (fr.b (Sum.inl i))) (Sum.inr k) = 0 := by
  let u : V := δ (fr.b (Sum.inl i))
  let w : V := δ (fr.b (Sum.inl i'))
  have hs : ∀ J : Finset (Fin 4), Even J.card → ∃ s : ZMod 3,
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = s • u ∧
      ((fr.signChange (ffE8Hat J) : OGroup Q) : V ≃ₗ[ZMod 3] V) w = s • w := by
    intro J hJ
    obtain ⟨e'', he'', s, -, hact⟩ :=
      hδ (fr.signChange (ffE8Hat J)) ((mem_ffE8Group_iff fr).mpr ⟨J, hJ, rfl⟩)
    refine ⟨s, ?_, ?_⟩
    · have h := hact (fr.b (Sum.inl i))
      rw [ffOutFFE8Cent_group_inl fr he'' i] at h
      exact h
    · have h := hact (fr.b (Sum.inl i'))
      rw [ffOutFFE8Cent_group_inl fr he'' i'] at h
      exact h
  by_contra hne
  have hk : fr.b.repr u (Sum.inr k) ≠ 0 := hne
  let alpha : ZMod 3 := fr.b.repr u (Sum.inr k)
  let beta : ZMod 3 := fr.b.repr w (Sum.inr k)
  let x : V := beta • fr.b (Sum.inl i) - alpha • fr.b (Sum.inl i')
  have hrep_u : ∀ j : FFE8Idx, j ≠ Sum.inr k → fr.b.repr u j = 0 :=
    fun j hj => (ffOutFFE8Cent_supp fr hs hk hj).1
  have hrep_w : ∀ j : FFE8Idx, j ≠ Sum.inr k → fr.b.repr w j = 0 :=
    fun j hj => (ffOutFFE8Cent_supp fr hs hk hj).2
  have hcoord : ∀ j : FFE8Idx,
      fr.b.repr (δ x) j = beta * fr.b.repr u j - alpha * fr.b.repr w j := by
    intro j
    simp only [x, u, w, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  have hdelx : δ x = 0 := by
    apply fr.b.repr.injective
    ext j
    rw [hcoord j, map_zero, Finsupp.zero_apply]
    by_cases hj : j = Sum.inr k
    · subst hj
      simp only [alpha, beta]
      ring
    · rw [hrep_u j hj, hrep_w j hj]
      ring
  have hx : x = 0 := by
    apply δ.injective
    rw [hdelx, map_zero]
  have hbeta0 : beta = 0 := by
    have h1 : fr.b.repr x (Sum.inl i) = beta := by
      have hx' : fr.b.repr x (Sum.inl i) =
          beta * fr.b.repr (fr.b (Sum.inl i)) (Sum.inl i) -
            alpha * fr.b.repr (fr.b (Sum.inl i')) (Sum.inl i) := by
        simp only [x, map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [hx', Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, if_pos rfl,
        if_neg (fun h => hii (Sum.inl.inj h).symm)]
      ring
    have h2 : fr.b.repr x (Sum.inl i) = 0 := by rw [hx, map_zero, Finsupp.zero_apply]
    exact h1.symm.trans h2
  have halpha0 : alpha = 0 := by
    have h1 : fr.b.repr x (Sum.inl i') = -alpha := by
      have hx' : fr.b.repr x (Sum.inl i') =
          beta * fr.b.repr (fr.b (Sum.inl i)) (Sum.inl i') -
            alpha * fr.b.repr (fr.b (Sum.inl i')) (Sum.inl i') := by
        simp only [x, map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [hx', Module.Basis.repr_self_apply, Module.Basis.repr_self_apply,
        if_neg (fun h => hii (Sum.inl.inj h)), if_pos rfl]
      ring
    have h2 : fr.b.repr x (Sum.inl i') = 0 := by rw [hx, map_zero, Finsupp.zero_apply]
    have h3 : -alpha = 0 := h1.symm.trans h2
    exact neg_eq_zero.mp h3
  exact hne halpha0

theorem ffOutFFE8Cent_inW {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {δ : V ≃ₗ[ZMod 3] V}
    (hδ : ∀ e ∈ ffE8Group fr, ∃ e'' ∈ ffE8Group fr, ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧
      ∀ v, (e : V ≃ₗ[ZMod 3] V) (δ v) = s • δ ((e'' : V ≃ₗ[ZMod 3] V) v))
    (i : Fin 2) (k : Fin 4) : fr.b.repr (δ (fr.b (Sum.inl i))) (Sum.inr k) = 0 := by
  obtain ⟨i', hii⟩ : ∃ i' : Fin 2, i' ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  exact fk3_inW_pair fr hδ (i := i) (i' := i') (fun h => hii h.symm) k

end CFSG.OddStandard.SmallF3.Omega
