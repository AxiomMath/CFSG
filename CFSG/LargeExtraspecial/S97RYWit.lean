module

public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCPermSpec
public import CFSG.LargeExtraspecial.S97RYCheck

public section

namespace CFSG.LargeExtraspecial.S11.PairCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75
  CFSG.CGT.Timmesfeld75.WCCheck

@[expose] def PairProp {X : Type*} [Group X] (T : Subgroup X) (k : ℕ) (proper : Bool) : Prop :=
  ∃ c : X, Nat.card (T ⊓ Subgroup.normalizer (conjSubgroup c T : Set X) : Subgroup X) = k ∧
    (proper = true → T ⊔ conjSubgroup c T ≠ ⊤)

theorem PairProp.of_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {T : Subgroup X}
    {k : ℕ} {pr : Bool} (h : PairProp (T.map e.toMonoidHom) k pr) : PairProp T k pr := by
  obtain ⟨c', hc, hp⟩ := h
  have hconj : (conjSubgroup (e.symm c') T).map e.toMonoidHom =
      conjSubgroup c' (T.map e.toMonoidHom) := by
    rw [map_conjSubgroup_mulEquiv, MulEquiv.apply_symm_apply]
  refine ⟨e.symm c', ?_, fun hpr htop => hp hpr ?_⟩
  · rw [← hc, ← hconj, ← Subgroup.map_normalizer_eq_of_bijective _ e.bijective,
      ← Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
  · rw [← hconj, ← Subgroup.map_sup, htop]
    exact Subgroup.map_top_of_surjective _ e.surjective

theorem memL_iff {S : List Table} {t : Table} : memL S t = true ↔ t ∈ S := by
  simp only [memL, List.any_eq_true, beq_iff_eq, exists_eq_right]

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  {T : Subgroup M} {J : List Bool}
  (hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU D J, eltG (pcG D genG) i = x)
include hn hgen hmemT

theorem exists_rep_of_mem_tabU {u : Table} (hu : u ∈ tabU D J) : ∃ x ∈ T, Rep D.n u x := by
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ⟨1, T.one_mem, Rep.idT hn⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    exact ⟨_, (hmemT _).2 (Or.inr ⟨i, hi, rfl⟩), rep_el hn hgen i⟩

theorem exists_mem_tabU_of_mem {x : M} (hx : x ∈ T) : ∃ u ∈ tabU D J, Rep D.n u x := by
  rcases (hmemT x).1 hx with rfl | ⟨i, hi, rfl⟩
  · exact ⟨_, List.mem_cons_self .., Rep.idT hn⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem hi), rep_el hn hgen i⟩

omit hmemT in
theorem rep_conjW (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (c : List ℤ) {u : Table} {x : M}
    (hu : Rep D.n u x) : Rep D.n (conjW D c u) (wG D genG c * x * (wG D genG c)⁻¹) := by
  have hri := rep_wT hn hgen (invWord c)
  rw [wG_invWord hinv] at hri
  exact Rep.compT (Rep.compT (rep_wT hn hgen c) hu) hri

theorem exists_rep_of_mem_tabUc (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (c : List ℤ)
    {s : Table} (hs : s ∈ tabUc D J c) :
    ∃ y ∈ conjSubgroup (wG D genG c) T, Rep D.n s y := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
  obtain ⟨x, hx, hux⟩ := exists_rep_of_mem_tabU hn hgen hmemT hu
  refine ⟨_, ?_, rep_conjW hn hgen hinv c hux⟩
  rw [mem_conjSubgroup]
  simpa [mul_assoc] using hx

theorem exists_mem_tabUc_of_mem (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (c : List ℤ) {y : M}
    (hy : y ∈ conjSubgroup (wG D genG c) T) : ∃ s ∈ tabUc D J c, Rep D.n s y := by
  rw [mem_conjSubgroup] at hy
  obtain ⟨u, hu, hux⟩ := exists_mem_tabU_of_mem hn hgen hmemT hy
  refine ⟨_, List.mem_map_of_mem hu, ?_⟩
  have h := rep_conjW hn hgen hinv c hux
  rwa [show wG D genG c * ((wG D genG c)⁻¹ * y * wG D genG c) * (wG D genG c)⁻¹ = y by
    group] at h

omit hn hgen hmemT in
theorem size_of_mem_tabUc {c : List ℤ} {s : Table} (hs : s ∈ tabUc D J c) : s.size = D.n := by
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hs
  exact size_compT' _ _

theorem memL_tabUc_iff (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (c : List ℤ) {t : Table} {y : M}
    (ht : Rep D.n t y) (hts : t.size = D.n) :
    memL (tabUc D J c) t = true ↔ y ∈ conjSubgroup (wG D genG c) T := by
  rw [memL_iff]
  constructor
  · intro hmem
    obtain ⟨y', hy', hr⟩ := exists_rep_of_mem_tabUc hn hgen hmemT hinv c hmem
    rwa [eq_of_rep ht hr]
  · intro hy
    obtain ⟨s, hs, hrs⟩ := exists_mem_tabUc_of_mem hn hgen hmemT hinv c hy
    have := beq_iff_eq.1 (beq_of_eq hrs ht (size_of_mem_tabUc hs) hts)
    rwa [← this]

end

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) {T : Subgroup M} {J : List Bool}
  (hmemT : ∀ x : M, x ∈ T ↔ x = 1 ∨ ∃ i ∈ idxU D J, eltG (pcG D genG) i = x)
include hn hgen hinv hmemT

theorem normU_iff (c : List ℤ) {x : M} (hxx : x * x = 1) {t : Table} (ht : Rep D.n t x) :
    normU D J c t = true ↔
      x ∈ Subgroup.normalizer (conjSubgroup (wG D genG c) T : Set M) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  rw [normU, List.all_eq_true]
  constructor
  · intro h
    refine mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le fun w hw => ?_)
    rw [mem_conjSubgroup, hxi] at hw
    obtain ⟨s, hs, hrs⟩ := exists_mem_tabUc_of_mem hn hgen hmemT hinv c hw
    have hr := Rep.compT (Rep.compT ht hrs) ht
    rw [show x * (x * w * x) * x = x * x * w * (x * x) by group, hxx, one_mul,
      mul_one] at hr
    exact (memL_tabUc_iff hn hgen hmemT hinv c hr (size_compT' _ _)).1 (h s hs)
  · intro hx s hs
    obtain ⟨y, hy, hrs⟩ := exists_rep_of_mem_tabUc hn hgen hmemT hinv c hs
    have hr := Rep.compT (Rep.compT ht hrs) ht
    refine (memL_tabUc_iff hn hgen hmemT hinv c hr (size_compT' _ _)).2 ?_
    have := (Subgroup.mem_normalizer_iff.1 hx y).1 hy
    rwa [hxi] at this

theorem mem_inf_normalizer_iff (hT : IsElemAbelian 2 T) (c : List ℤ) {nIdx : List ℕ}
    (hsub : ∀ i ∈ nIdx, i ∈ idxU D J)
    (hchk : ∀ i ∈ idxU D J, nIdx.contains i = normU D J c (el D i)) (x : M) :
    x ∈ T ⊓ Subgroup.normalizer (conjSubgroup (wG D genG c) T : Set M) ↔
      x = 1 ∨ ∃ i ∈ nIdx, eltG (pcG D genG) i = x := by
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hxT, hxN⟩
    rcases (hmemT x).1 hxT with rfl | ⟨i, hi, rfl⟩
    · exact Or.inl rfl
    · have hn' := (normU_iff hn hgen hinv hmemT c (elemAbelian_mul_self hT hxT)
        (rep_el hn hgen i)).2 hxN
      rw [← hchk i hi] at hn'
      exact Or.inr ⟨i, List.elem_iff.1 hn', rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨T.one_mem, Subgroup.one_mem _⟩
    · have hxT : eltG (pcG D genG) i ∈ T := (hmemT _).2 (Or.inr ⟨i, hsub i hi, rfl⟩)
      refine ⟨hxT, (normU_iff hn hgen hinv hmemT c (elemAbelian_mul_self hT hxT)
        (rep_el hn hgen i)).1 ?_⟩
      rw [← hchk i (hsub i hi)]
      exact List.elem_iff.2 hi

theorem sup_ne_top_of_properOK {fuel : ℕ} {c out : List ℤ}
    (h : properOK D fuel J c out = true) : T ⊔ conjSubgroup (wG D genG c) T ≠ ⊤ := by
  unfold properOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set gs := tabU D J ++ tabUc D J c with hgs
  set E := closeT D.n gs fuel [idT D.n] [idT D.n] with hE
  have hgen' : ∀ y ∈ (T : Set M) ∪ (conjSubgroup (wG D genG c) T : Set M),
      ∃ s ∈ gs, Rep D.n s y := by
    rintro y (hy | hy)
    · obtain ⟨u, hu, hr⟩ := exists_mem_tabU_of_mem hn hgen hmemT hy
      exact ⟨u, List.mem_append_left _ hu, hr⟩
    · obtain ⟨u, hu, hr⟩ := exists_mem_tabUc_of_mem hn hgen hmemT hinv c hy
      exact ⟨u, List.mem_append_right _ hu, hr⟩
  have hclos : ∀ y ∈ T ⊔ conjSubgroup (wG D genG c) T, ∃ t ∈ E, Rep D.n t y := by
    intro y hy
    rw [Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction_right with
    | one => exact ⟨idT D.n, memL_iff.1 h1, Rep.idT hn⟩
    | mul_right x hx y hy ih =>
      obtain ⟨t, htE, hrt⟩ := ih
      obtain ⟨s, hs, hrs⟩ := hgen' y hy
      exact ⟨_, memL_iff.1 ((h2 t htE).2 s hs), Rep.compT hrt hrs⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨t, htE, hrt⟩ := ih
      have hy' : y⁻¹ ∈ (T : Set M) ∪ (conjSubgroup (wG D genG c) T : Set M) := by
        rcases hy with hy | hy
        · exact Or.inl (T.inv_mem hy)
        · exact Or.inr (Subgroup.inv_mem _ hy)
      obtain ⟨s, hs, hrs⟩ := hgen' _ hy'
      exact ⟨_, memL_iff.1 ((h2 t htE).2 s hs), Rep.compT hrt hrs⟩
  intro htop
  obtain ⟨t, htE, hrt⟩ := hclos (wG D genG out) (htop ▸ Subgroup.mem_top _)
  have heq := beq_iff_eq.1 (beq_of_eq hrt (rep_wT hn hgen out) (h2 t htE).1 (size_wT out))
  rw [← heq, memL_iff.2 htE] at h3
  exact absurd h3 (by decide)

end

end CFSG.LargeExtraspecial.S11.PairCheck
