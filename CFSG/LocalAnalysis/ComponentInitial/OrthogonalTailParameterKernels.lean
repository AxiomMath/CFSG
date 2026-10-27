module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Matrix
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Except

variable (r qA) in
@[expose] noncomputable def tailUnipotentExcept (i : Fin r) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  ⨆ β ∈ posRootsB r \ {simpleRootB r i}, tailRootGroup r qA β

theorem tailRootGroup_le_tailUnipotentExcept {i : Fin r} {β : Fin r → ℤ}
    (hβ : β ∈ posRootsB r \ {simpleRootB r i}) :
    tailRootGroup r qA β ≤ tailUnipotentExcept r qA i :=
  le_iSup₂ (f := fun β (_ : β ∈ posRootsB r \ {simpleRootB r i}) => tailRootGroup r qA β) β hβ

theorem tailUnipotentExcept_le (i : Fin r) : tailUnipotentExcept r qA i ≤ tailUnipotent r qA :=
  iSup₂_le fun _ hβ => tailRootGroup_le_tailUnipotent hβ.1

theorem tailUnipotentExcept_sup (i : Fin r) :
    tailUnipotentExcept r qA i ⊔ tailRootGroup r qA (simpleRootB r i) = tailUnipotent r qA := by
  refine le_antisymm (sup_le (tailUnipotentExcept_le i)
    (tailRootGroup_le_tailUnipotent (simpleRootB_mem_posRootsB i))) (iSup₂_le fun β hβ => ?_)
  by_cases h : β = simpleRootB r i
  · rw [h]
    exact le_sup_right
  · exact le_trans (tailRootGroup_le_tailUnipotentExcept ⟨hβ, h⟩) le_sup_left

theorem uMap_single_mem_tailUnipotentExcept {i k : Fin r} (hk : eps r k ≠ simpleRootB r i)
    (b : A) : uMap qA (Pi.single k b) 0 ∈ tailUnipotentExcept r qA i := by
  rw [← eichler_inl_tail_eq_uMap]
  exact tailRootGroup_le_tailUnipotentExcept ⟨Or.inl ⟨k, rfl⟩, hk⟩
    (mem_tailRootGroup_eps.2 ⟨b, rfl⟩)

end Except

section Gen

theorem uMap_zero_mem_of_le {H : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)}
    {S : Finset (Fin r)} (hshort : ∀ k ∈ S, ∀ b : A, uMap qA (Pi.single k b) 0 ∈ H)
    (hC : ∀ C : Matrix (Fin r) (Fin r) K, Cᵀ = -C → (∀ i, C i i = 0) → uMap qA 0 C ∈ H)
    {L : Fin r → A} (hL : ∀ k, k ∉ S → L k = 0) : uMap qA L 0 ∈ H := by
  have key : ∀ s : Finset (Fin r), s ⊆ S → ∃ C : Matrix (Fin r) (Fin r) K, Cᵀ = -C ∧
      (∀ i, C i i = 0) ∧ uMap qA (fun j => if j ∈ s then L j else 0) C ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨0, by simp, fun _ => rfl, ?_⟩
      have h0 : (fun j => if j ∈ (∅ : Finset (Fin r)) then L j else 0) = 0 := funext fun j => by
        simp
      rw [h0, uMap_zero_zero]
      exact one_mem _
    | insert a s ha ih =>
      intro hs
      obtain ⟨C, hC', hd, hmem⟩ := ih ((Finset.subset_insert a s).trans hs)
      have hsum : Pi.single a (L a) + (fun j => if j ∈ s then L j else 0) =
          fun j => if j ∈ insert a s then L j else 0 := by
        funext j
        by_cases hja : j = a
        · subst hja
          simp [ha]
        · by_cases hjs : j ∈ s
          · simp [hja, hjs]
          · simp [hja, hjs]
      obtain ⟨hC'', hd''⟩ := mulParam_alternating (qA := qA) (Pi.single a (L a))
        (fun j => if j ∈ s then L j else 0) (C := 0) (C' := C) (by simp) (fun _ => rfl) hC' hd
      refine ⟨_, hC'', hd'', ?_⟩
      rw [← hsum, ← uMap_mul_uMap]
      exact mul_mem (hshort a (hs (Finset.mem_insert_self a s)) (L a)) hmem
  obtain ⟨C, hC', hd, hmem⟩ := key S le_rfl
  have hL' : (fun j => if j ∈ S then L j else 0) = L := funext fun j => by
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj, hL j hj]
  rw [hL'] at hmem
  have heq : uMap qA L 0 = (uMap qA 0 C)⁻¹ * uMap qA L C := by
    rw [← uMap_zero_mul_uMap L C, inv_mul_cancel_left]
  rw [heq]
  exact mul_mem (inv_mem (hC C hC' hd)) hmem

theorem prodHom_dBlock_one_mul_uBlock (C : Matrix (Fin r) (Fin r) K) :
    prodHom A (dBlock 1 * uBlock C) = uMap qA 0 C := by
  rw [prodHom_dBlock_mul_uBlock, dMap_one_one, one_mul]

theorem dBlock_one_mul_uBlock_mem_posUnip {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) : dBlock 1 * uBlock C ∈ posUnip r K :=
  dBlock_mul_uBlock_mem_posUnip
    (fun i j h => by rw [Units.val_one]; exact one_apply_ne (ne_of_gt h)) (fun i => by simp) hC hd

end Gen

section Long

variable (K A) in
@[expose] def hypEntry (i j : Fin r)
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) : K :=
  (g (hypVec K A (.inl j))).1 (.inl i)

theorem hypEntry_dMap_uMap (i j : Fin r) (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A)
    (C : Matrix (Fin r) (Fin r) K) :
    hypEntry K A i j (dMap D h * uMap qA L C) = (D : Matrix (Fin r) (Fin r) K) i j := by
  change (dMap D h (uMap qA L C (hypVec K A (.inl j)))).1 (.inl i) = _
  rw [uMap_apply_of_fst_inr L C (fun k => by simp [hypVec]) rfl, dMap_apply]
  have hx : (hypVec K A (.inl j) : (Fin r ⊕ Fin r → K) × A).1 ∘ Sum.inl = Pi.single j 1 := by
    funext k
    simp [hypVec, Pi.single_apply]
  change ((D : Matrix (Fin r) (Fin r) K) *ᵥ _) i = _
  rw [hx, mulVec_single_one, col_apply]

theorem hypEntry_uMap (i j : Fin r) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    hypEntry K A i j (uMap qA L C) = if i = j then 1 else 0 := by
  have h : uMap qA L C = dMap 1 1 * uMap qA L C := by rw [dMap_one_one, one_mul]
  rw [h, hypEntry_dMap_uMap, Units.val_one, one_apply]

theorem hypEntry_prodHom (i j : Fin r) (b : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
    hypEntry K A i j (prodHom A b) = b (Pi.single (.inl j) 1) (.inl i) :=
  rfl

theorem eichler_inl_apply_hypVec_inl {a j : Fin r} {w : (Fin r ⊕ Fin r → K) × A}
    (hw : polar (quadTail r qA) (hypVec K A (.inl a)) w = 0) :
    eichler (quadTail r qA) (hypVec K A (.inl a)) w (hypVec K A (.inl j)) =
      hypVec K A (.inl j) - w.1 (.inr j) • hypVec K A (.inl a) := by
  rw [eichler_apply (quadTail_hypVec _) hw, polar_hypVec_hypVec, polar_comm, polar_hypVec]
  simp

theorem hypEntry_tailLongElt {i j : Fin r} (hij : i ≠ j) {β : Fin r → ℤ} (hβ : β ∈ posRoots r)
    (t : K) : hypEntry K A i j (tailLongElt r qA β t) =
      if β = eps r i - eps r j then t else 0 := by
  obtain ⟨a, b, hab, rfl | rfl⟩ := hβ
  · have hw : polar (quadTail r qA) (hypVec K A (.inl a)) ((-t) • hypVec K A (.inr b)) = 0 := by
      rw [polar_smul_right_eq, polar_hypVec_hypVec]
      simp [hab.ne']
    rw [tailLongElt_eps_sub_eps hab, hypEntry, eichler_inl_apply_hypVec_inl hw]
    by_cases hb : b = j
    · subst hb
      by_cases ha : a = i
      · subst ha
        simp [hypVec, hij]
      · have hne : eps r a - eps r b ≠ eps r i - eps r b := fun h => ha (eps_injective
          (by simpa using h))
        simp [hypVec, hij, Ne.symm ha, hne]
    · have hne : eps r a - eps r b ≠ eps r i - eps r j := by
        intro h
        have h1 := congrFun h b
        have h2 := congrFun h j
        simp only [Pi.sub_apply, eps, Pi.single_apply] at h1 h2
        split_ifs at h1 h2 <;> omega
      simp [hypVec, hij, Ne.symm hb, hne]
  · have hw : polar (quadTail r qA) (hypVec K A (.inl a)) ((-t) • hypVec K A (.inl b)) = 0 := by
      rw [polar_smul_right_eq, polar_hypVec_hypVec]
      simp
    have hne : eps r a + eps r b ≠ eps r i - eps r j := by
      intro h
      have h1 := congrFun h a
      have h2 := congrFun h b
      have h3 := congrFun h j
      simp only [Pi.add_apply, Pi.sub_apply, eps, Pi.single_apply] at h1 h2 h3
      split_ifs at h1 h2 h3 <;> omega
    rw [tailLongElt_eps_add_eps hab, hypEntry, eichler_inl_apply_hypVec_inl hw]
    simp [hypVec, hij, hne]

variable [FiniteDimensional K A]

variable (r qA) in
@[expose] noncomputable def tailSimpleLong (hani : qA.Anisotropic) (i : Fin r)
    (hi : i.val + 1 < r) : tailUnipotent r qA →* Multiplicative K where
  toFun g := Multiplicative.ofAdd (hypEntry K A i ⟨i.val + 1, hi⟩ g.1)
  map_one' := by
    change Multiplicative.ofAdd ((Pi.single (Sum.inl ⟨i.val + 1, hi⟩) (1 : K) :
      Fin r ⊕ Fin r → K) (Sum.inl i)) = 1
    rw [Pi.single_eq_of_ne (by simp [Fin.ext_iff]), ofAdd_zero]
  map_mul' g g' := by
    obtain ⟨D, L, C, hD, h1, -, -, he⟩ := (mem_tailUnipotent_iff hani).1 g.2
    obtain ⟨D', L', C', hD', h1', -, -, he'⟩ := (mem_tailUnipotent_iff hani).1 g'.2
    change Multiplicative.ofAdd (hypEntry K A i _ (g.1 * g'.1)) =
      Multiplicative.ofAdd (hypEntry K A i _ g.1) * Multiplicative.ofAdd (hypEntry K A i _ g'.1)
    rw [he, he', dMap_uMap_mul_dMap_uMap D D' 1 (one_mem _), hypEntry_dMap_uMap,
      hypEntry_dMap_uMap, hypEntry_dMap_uMap, ← ofAdd_add]
    congr 1
    rw [Units.val_mul, Matrix.mul_apply,
      Fintype.sum_eq_add i ⟨i.val + 1, hi⟩ (by simp [Fin.ext_iff])]
    · rw [h1 i, h1' ⟨i.val + 1, hi⟩, one_mul, mul_one, add_comm]
    · rintro k ⟨hki, hkj⟩
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hD h, zero_mul]
      · have hjk : (⟨i.val + 1, hi⟩ : Fin r) < k := by
          rw [Fin.lt_def] at h ⊢
          rw [Ne, Fin.ext_iff] at hkj
          simp only at hkj ⊢
          omega
        rw [hD' hjk, mul_zero]

theorem tailSimpleLong_apply (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 < r)
    (g : tailUnipotent r qA) :
    tailSimpleLong r qA hani i hi g = Multiplicative.ofAdd (hypEntry K A i ⟨i.val + 1, hi⟩ g.1) :=
  rfl

omit [FiniteDimensional K A] in
theorem simpleRootB_mem_posRoots_of_lt {i : Fin r} (hi : i.val + 1 < r) :
    simpleRootB r i ∈ posRoots r := by
  rw [simpleRootB_of_lt hi]
  exact ⟨i, ⟨i.val + 1, hi⟩, by rw [Fin.lt_def]; simp, Or.inl rfl⟩

omit [FiniteDimensional K A] in
theorem eps_ne_simpleRootB_of_lt {i : Fin r} (hi : i.val + 1 < r) (k : Fin r) :
    eps r k ≠ simpleRootB r i := fun h =>
  eps_not_mem_roots k (h ▸ posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt hi))

theorem tailSimpleLong_tailLongElt (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 < r)
    (t : K) (hx : tailLongElt r qA (simpleRootB r i) t ∈ tailUnipotent r qA) :
    tailSimpleLong r qA hani i hi ⟨_, hx⟩ = Multiplicative.ofAdd t := by
  rw [tailSimpleLong_apply, hypEntry_tailLongElt (by simp [Fin.ext_iff])
    (simpleRootB_mem_posRoots_of_lt hi), ite_eq_left (simpleRootB_of_lt hi)]

theorem tailSimpleLong_eq_one (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 < r)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailUnipotentExcept r qA i) :
    tailSimpleLong r qA hani i hi ⟨g, tailUnipotentExcept_le i hg⟩ = 1 := by
  have hle : tailUnipotentExcept r qA i ≤
      (tailSimpleLong r qA hani i hi).ker.map (tailUnipotent r qA).subtype := by
    refine iSup₂_le fun β hβ => ?_
    rcases hβ with ⟨⟨k, rfl⟩ | hlong, hne⟩
    · rintro x hx
      obtain ⟨b, rfl⟩ := mem_tailRootGroup_eps.1 hx
      refine ⟨⟨_, tailRootGroup_le_tailUnipotent (Or.inl ⟨k, rfl⟩)
        (mem_tailRootGroup_eps.2 ⟨b, rfl⟩)⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      rw [tailSimpleLong_apply]
      change Multiplicative.ofAdd (hypEntry K A i _
        (eichler (quadTail r qA) (hypVec K A (.inl k)) (0, b))) = 1
      rw [eichler_inl_tail_eq_uMap, hypEntry_uMap, ite_eq_right (by simp [Fin.ext_iff]),
        ofAdd_zero]
    · rintro x hx
      obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long (posRoots_subset_roots hlong)).1 hx
      refine ⟨⟨_, tailRootGroup_le_tailUnipotent (Or.inr hlong) hx⟩, MonoidHom.mem_ker.2 ?_,
        rfl⟩
      rw [tailSimpleLong_apply]
      change Multiplicative.ofAdd (hypEntry K A i _ (tailLongElt r qA β t)) = 1
      rw [hypEntry_tailLongElt (by simp [Fin.ext_iff]) hlong,
        ite_eq_right (by rw [← simpleRootB_of_lt hi]; exact hne), ofAdd_zero]
  obtain ⟨g', hg', he⟩ := hle hg
  have : g' = ⟨g, tailUnipotentExcept_le i hg⟩ := Subtype.ext he
  rw [← this]
  exact hg'

omit [FiniteDimensional K A] in
theorem map_unipotentExcept_le {i : Fin r} (hi : i.val + 1 < r) :
    (unipotentExcept r K i).map (prodHom A) ≤ tailUnipotentExcept r qA i := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun β hβ => ?_
  rw [← Subgroup.map_le_iff_le_comap, ← tailLongGroup_eq_map,
    ← tailRootGroup_of_mem_roots (posRoots_subset_roots hβ.1)]
  exact tailRootGroup_le_tailUnipotentExcept
    ⟨Or.inr hβ.1, by rw [simpleRootB_eq_simpleRoot hi]; exact hβ.2⟩

theorem prodHom_mem_tailUnipotentExcept (hani : qA.Anisotropic) {i : Fin r}
    (hi : i.val + 1 < r) {b : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hb : b ∈ posUnip r K) (h0 : hypEntry K A i ⟨i.val + 1, hi⟩ (prodHom A b) = 0) :
    prodHom A b ∈ tailUnipotentExcept r qA i := by
  have hr : 2 ≤ r := by omega
  rw [← unipotent_eq_posUnip] at hb
  have hprod := (coe_eq_mul_of_normal (unipotentExcept_le_unipotent (K := K) i)
    (rootSubgroup_le_unipotent (simpleRoot_mem_posRoots hr i)) (unipotentExcept_normal hr i)
    (unipotentExcept_sup hr i)).1
  have hb' : b ∈ (unipotent r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] _)) := hb
  rw [hprod] at hb'
  obtain ⟨h, hh, x, ⟨t, rfl⟩, hbx⟩ := hb'
  replace hbx : h * rootElt r K (simpleRoot r i) t = b := hbx
  subst hbx
  have hhU : prodHom A h ∈ tailUnipotentExcept r qA i :=
    map_unipotentExcept_le hi ⟨h, hh, rfl⟩
  have hx : prodHom A (rootElt r K (simpleRoot r i) t) = tailLongElt r qA (simpleRootB r i) t := by
    rw [simpleRootB_eq_simpleRoot hi, tailLongElt_eq_prodCongr, prodHom_apply]
  have hxU : tailLongElt r qA (simpleRootB r i) t ∈ tailUnipotent r qA :=
    tailRootGroup_le_tailUnipotent (simpleRootB_mem_posRootsB i)
      ((mem_tailRootGroup_long (posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt hi))).2
        ⟨t, rfl⟩)
  have ht : t = 0 := by
    have h1 := map_mul (tailSimpleLong r qA hani i hi) ⟨prodHom A h, tailUnipotentExcept_le i hhU⟩
      ⟨_, hxU⟩
    rw [tailSimpleLong_eq_one hani hi hhU, one_mul, tailSimpleLong_tailLongElt,
      tailSimpleLong_apply] at h1
    have h2 : ((⟨prodHom A h, tailUnipotentExcept_le i hhU⟩ * ⟨_, hxU⟩ : tailUnipotent r qA) :
        ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) = prodHom A (h * rootElt r K (simpleRoot r i) t) := by
      rw [Subgroup.coe_mul, map_mul, hx]
    rw [h2, h0] at h1
    exact (Multiplicative.ofAdd.injective h1).symm
  rw [ht, rootElt_zero, mul_one]
  exact hhU

theorem mem_tailUnipotentExcept_of_long (hani : qA.Anisotropic) {i : Fin r}
    (hi : i.val + 1 < r) {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailUnipotent r qA) (h1 : tailSimpleLong r qA hani i hi ⟨g, hg⟩ = 1) :
    g ∈ tailUnipotentExcept r qA i := by
  obtain ⟨D, L, C, hD, hD1, hC, hd, rfl⟩ := (mem_tailUnipotent_iff hani).1 hg
  rw [tailSimpleLong_apply] at h1
  change Multiplicative.ofAdd (hypEntry K A i _ (dMap D 1 * uMap qA L C)) = 1 at h1
  rw [hypEntry_dMap_uMap] at h1
  have hDij : (D : Matrix (Fin r) (Fin r) K) i ⟨i.val + 1, hi⟩ = 0 :=
    Multiplicative.ofAdd.injective h1
  rw [← uMap_zero_mul_uMap L C, ← mul_assoc, ← prodHom_dBlock_mul_uBlock]
  refine mul_mem (prodHom_mem_tailUnipotentExcept hani hi
    (dBlock_mul_uBlock_mem_posUnip hD hD1 hC hd) ?_) (uMap_zero_mem_of_le (S := Finset.univ)
      (fun k _ b => uMap_single_mem_tailUnipotentExcept (eps_ne_simpleRootB_of_lt hi k) b)
      (fun C' hC' hd' => ?_) (fun k hk => absurd (Finset.mem_univ k) hk))
  · rw [prodHom_dBlock_mul_uBlock (qA := qA), hypEntry_dMap_uMap, hDij]
  · rw [← prodHom_dBlock_one_mul_uBlock]
    refine prodHom_mem_tailUnipotentExcept hani hi (dBlock_one_mul_uBlock_mem_posUnip hC' hd') ?_
    rw [prodHom_dBlock_one_mul_uBlock (qA := qA), hypEntry_uMap,
      ite_eq_right (by simp [Fin.ext_iff])]

theorem ker_tailSimpleLong (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 < r) :
    (tailSimpleLong r qA hani i hi).ker =
      (tailUnipotentExcept r qA i).subgroupOf (tailUnipotent r qA) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨mem_tailUnipotentExcept_of_long hani hi g.2, tailSimpleLong_eq_one hani hi⟩

end Long

section Short

variable (K A) in
@[expose] def tailCoord (i : Fin r)
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) : A :=
  (g (hypVec K A (.inr i))).2

theorem tailCoord_dMap_uMap (i : Fin r) (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A)
    (C : Matrix (Fin r) (Fin r) K) : tailCoord K A i (dMap D h * uMap qA L C) = h (L i) := by
  change (dMap D h (uMap qA L C (hypVec K A (.inr i)))).2 = h (L i)
  rw [dMap_apply]
  dsimp only
  rw [uMap_apply, uLin_apply_snd]
  simp [hypVec, Pi.single_apply]

theorem tailCoord_uMap (i : Fin r) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    tailCoord K A i (uMap qA L C) = L i := by
  have h : uMap qA L C = dMap 1 1 * uMap qA L C := by rw [dMap_one_one, one_mul]
  rw [h, tailCoord_dMap_uMap]
  rfl

theorem tailCoord_tailLongElt (i : Fin r) (β : Fin r → ℤ) (t : K) :
    tailCoord K A i (tailLongElt r qA β t) = 0 := by
  rw [tailCoord, tailLongElt_eq_prodCongr]
  rfl

theorem inv_apply_last {D : GL (Fin r) K} (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ k, (D : Matrix (Fin r) (Fin r) K) k k = 1) {i : Fin r} (hi : i.val + 1 = r)
    (k : Fin r) :
    ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i k = if k = i then 1 else 0 := by
  have hinv : ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).IsUpperTriangular := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hD
  split_ifs with hk
  · subst hk
    have h := mul_apply_self_of_upperTriangular hinv hD k
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq, h1, mul_one] at h
    exact h.symm
  · have hki : k < i := by
      rw [Fin.lt_def]
      have := k.isLt
      rw [Fin.ext_iff] at hk
      omega
    exact hinv hki

variable [FiniteDimensional K A]

variable (r qA) in
@[expose] noncomputable def tailSimpleShort (hani : qA.Anisotropic) (i : Fin r)
    (hi : i.val + 1 = r) : tailUnipotent r qA →* Multiplicative A where
  toFun g := Multiplicative.ofAdd (tailCoord K A i g.1)
  map_one' := rfl
  map_mul' g g' := by
    obtain ⟨D, L, C, hD, h1, -, -, he⟩ := (mem_tailUnipotent_iff hani).1 g.2
    obtain ⟨D', L', C', hD', h1', -, -, he'⟩ := (mem_tailUnipotent_iff hani).1 g'.2
    change Multiplicative.ofAdd (tailCoord K A i (g.1 * g'.1)) =
      Multiplicative.ofAdd (tailCoord K A i g.1) * Multiplicative.ofAdd (tailCoord K A i g'.1)
    rw [he, he', dMap_uMap_mul_dMap_uMap D D' 1 (one_mem _), tailCoord_dMap_uMap,
      tailCoord_dMap_uMap, tailCoord_dMap_uMap, ← ofAdd_add]
    congr 1
    simp only [mul_one, inv_one, LinearEquiv.coe_one, id_eq, Pi.add_apply, conjL]
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [inv_apply_last hD' h1' hi, ite_eq_right hk,
      zero_smul]) (by simp), inv_apply_last hD' h1' hi]
    simp

theorem tailSimpleShort_apply (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 = r)
    (g : tailUnipotent r qA) :
    tailSimpleShort r qA hani i hi g = Multiplicative.ofAdd (tailCoord K A i g.1) :=
  rfl

theorem tailSimpleShort_tailShortElt (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 = r)
    (a : A) (hx : tailShortElt r qA (simpleRootB r i) a ∈ tailUnipotent r qA) :
    tailSimpleShort r qA hani i hi ⟨_, hx⟩ = Multiplicative.ofAdd a := by
  rw [tailSimpleShort_apply]
  change Multiplicative.ofAdd (tailCoord K A i (tailShortElt r qA (simpleRootB r i) a)) = _
  rw [simpleRootB_of_not_lt (by omega), tailShortElt_eps, eichler_inl_tail_eq_uMap,
    tailCoord_uMap, Pi.single_eq_same]

theorem tailSimpleShort_eq_one (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 = r)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailUnipotentExcept r qA i) :
    tailSimpleShort r qA hani i hi ⟨g, tailUnipotentExcept_le i hg⟩ = 1 := by
  have hle : tailUnipotentExcept r qA i ≤
      (tailSimpleShort r qA hani i hi).ker.map (tailUnipotent r qA).subtype := by
    refine iSup₂_le fun β hβ => ?_
    rcases hβ with ⟨⟨k, rfl⟩ | hlong, hne⟩
    · rintro x hx
      obtain ⟨b, rfl⟩ := mem_tailRootGroup_eps.1 hx
      have hki : i ≠ k := by
        rintro rfl
        exact hne (by rw [simpleRootB_of_not_lt (by omega)]; rfl)
      refine ⟨⟨_, tailRootGroup_le_tailUnipotent (Or.inl ⟨k, rfl⟩)
        (mem_tailRootGroup_eps.2 ⟨b, rfl⟩)⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      rw [tailSimpleShort_apply]
      change Multiplicative.ofAdd (tailCoord K A i
        (eichler (quadTail r qA) (hypVec K A (.inl k)) (0, b))) = 1
      rw [eichler_inl_tail_eq_uMap, tailCoord_uMap, Pi.single_eq_of_ne hki, ofAdd_zero]
    · rintro x hx
      obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long (posRoots_subset_roots hlong)).1 hx
      refine ⟨⟨_, tailRootGroup_le_tailUnipotent (Or.inr hlong) hx⟩, MonoidHom.mem_ker.2 ?_,
        rfl⟩
      rw [tailSimpleShort_apply]
      change Multiplicative.ofAdd (tailCoord K A i (tailLongElt r qA β t)) = 1
      rw [tailCoord_tailLongElt, ofAdd_zero]
  obtain ⟨g', hg', he⟩ := hle hg
  have : g' = ⟨g, tailUnipotentExcept_le i hg⟩ := Subtype.ext he
  rw [← this]
  exact hg'

omit [FiniteDimensional K A] in
theorem prodHom_mem_tailUnipotentExcept_last {i : Fin r} (hi : ¬i.val + 1 < r)
    {b : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hb : b ∈ posUnip r K) :
    prodHom A b ∈ tailUnipotentExcept r qA i := by
  rw [← unipotent_eq_posUnip] at hb
  have hle : (unipotent r K).map (prodHom A) ≤ tailUnipotentExcept r qA i := by
    rw [unipotent, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun α hα => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← tailLongGroup_eq_map,
      ← tailRootGroup_of_mem_roots (posRoots_subset_roots hα)]
    refine tailRootGroup_le_tailUnipotentExcept ⟨Or.inr hα, fun h => ?_⟩
    rw [Set.mem_singleton_iff, simpleRootB_of_not_lt hi] at h
    exact eps_not_mem_roots i (h ▸ posRoots_subset_roots hα)
  exact hle ⟨b, hb, rfl⟩

theorem mem_tailUnipotentExcept_of_short (hani : qA.Anisotropic) {i : Fin r}
    (hi : i.val + 1 = r) {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailUnipotent r qA) (h1 : tailSimpleShort r qA hani i hi ⟨g, hg⟩ = 1) :
    g ∈ tailUnipotentExcept r qA i := by
  have hi' : ¬i.val + 1 < r := by omega
  obtain ⟨D, L, C, hD, hD1, hC, hd, rfl⟩ := (mem_tailUnipotent_iff hani).1 hg
  rw [tailSimpleShort_apply] at h1
  change Multiplicative.ofAdd (tailCoord K A i (dMap D 1 * uMap qA L C)) = 1 at h1
  rw [tailCoord_dMap_uMap] at h1
  have hLi : L i = 0 := Multiplicative.ofAdd.injective h1
  rw [← uMap_zero_mul_uMap L C, ← mul_assoc, ← prodHom_dBlock_mul_uBlock]
  refine mul_mem (prodHom_mem_tailUnipotentExcept_last hi'
    (dBlock_mul_uBlock_mem_posUnip hD hD1 hC hd)) (uMap_zero_mem_of_le
      (S := Finset.univ.erase i) (fun k hk b => uMap_single_mem_tailUnipotentExcept ?_ b)
      (fun C' hC' hd' => ?_) (fun k hk => ?_))
  · rw [simpleRootB_of_not_lt hi']
    exact fun h => Finset.ne_of_mem_erase hk (eps_injective h)
  · rw [← prodHom_dBlock_one_mul_uBlock]
    exact prodHom_mem_tailUnipotentExcept_last hi' (dBlock_one_mul_uBlock_mem_posUnip hC' hd')
  · have : k = i := by
      by_contra hki
      exact hk (Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩)
    rw [this, hLi]

theorem ker_tailSimpleShort (hani : qA.Anisotropic) {i : Fin r} (hi : i.val + 1 = r) :
    (tailSimpleShort r qA hani i hi).ker =
      (tailUnipotentExcept r qA i).subgroupOf (tailUnipotent r qA) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨mem_tailUnipotentExcept_of_short hani hi g.2, tailSimpleShort_eq_one hani hi⟩

end Short

theorem orthogonal_geometry_tail_simple_positive_parameter_kernels {K : Type*} [Field K]
    {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ}
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) :
    (∀ (i : Fin r) (hi : i.val + 1 < r),
      (∀ (D : GL (Fin r) K) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
          (hu : dMap D 1 * uMap qA L C ∈ tailUnipotent r qA),
        tailSimpleLong r qA hani i hi ⟨_, hu⟩ =
          Multiplicative.ofAdd ((D : Matrix (Fin r) (Fin r) K) i ⟨i.val + 1, hi⟩)) ∧
      Function.Surjective (tailSimpleLong r qA hani i hi) ∧
      (∀ (t : K) (hx : tailLongElt r qA (simpleRootB r i) t ∈ tailUnipotent r qA),
        tailSimpleLong r qA hani i hi ⟨_, hx⟩ = Multiplicative.ofAdd t) ∧
      (tailSimpleLong r qA hani i hi).ker =
        (tailUnipotentExcept r qA i).subgroupOf (tailUnipotent r qA)) ∧
    (∀ (i : Fin r) (hi : i.val + 1 = r),
      (∀ (D : GL (Fin r) K) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
          (hu : dMap D 1 * uMap qA L C ∈ tailUnipotent r qA),
        tailSimpleShort r qA hani i hi ⟨_, hu⟩ = Multiplicative.ofAdd (L i)) ∧
      Function.Surjective (tailSimpleShort r qA hani i hi) ∧
      (∀ (a : A) (hx : tailShortElt r qA (simpleRootB r i) a ∈ tailUnipotent r qA),
        tailSimpleShort r qA hani i hi ⟨_, hx⟩ = Multiplicative.ofAdd a) ∧
      (tailSimpleShort r qA hani i hi).ker =
        (tailUnipotentExcept r qA i).subgroupOf (tailUnipotent r qA)) ∧
    ∀ i : Fin r, tailUnipotentExcept r qA i ≤ tailUnipotent r qA ∧
      ((tailUnipotentExcept r qA i).subgroupOf (tailUnipotent r qA)).Normal ∧
      (tailUnipotent r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) =
        (tailUnipotentExcept r qA i : Set _) * (tailRootGroup r qA (simpleRootB r i) : Set _) ∧
      (tailUnipotent r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) =
        (tailRootGroup r qA (simpleRootB r i) : Set _) * (tailUnipotentExcept r qA i : Set _) := by
  have hnormal : ∀ i : Fin r,
      ((tailUnipotentExcept r qA i).subgroupOf (tailUnipotent r qA)).Normal := by
    intro i
    by_cases hi : i.val + 1 < r
    · rw [← ker_tailSimpleLong hani hi]
      exact MonoidHom.normal_ker _
    · have hi' : i.val + 1 = r := by have := i.isLt; omega
      rw [← ker_tailSimpleShort hani hi']
      exact MonoidHom.normal_ker _
  refine ⟨fun i hi => ⟨fun D L C hu => ?_, fun y => ?_, fun t hx => tailSimpleLong_tailLongElt
    hani hi t hx, ker_tailSimpleLong hani hi⟩, fun i hi => ⟨fun D L C hu => ?_, fun y => ?_,
    fun a hx => tailSimpleShort_tailShortElt hani hi a hx, ker_tailSimpleShort hani hi⟩,
    fun i => ⟨tailUnipotentExcept_le i, hnormal i, coe_eq_mul_of_normal (tailUnipotentExcept_le i)
      (tailRootGroup_le_tailUnipotent (simpleRootB_mem_posRootsB i)) (hnormal i)
      (tailUnipotentExcept_sup i)⟩⟩
  · rw [tailSimpleLong_apply]
    exact congrArg Multiplicative.ofAdd (hypEntry_dMap_uMap _ _ D 1 L C)
  · have hx : tailLongElt r qA (simpleRootB r i) (Multiplicative.toAdd y) ∈ tailUnipotent r qA :=
      tailRootGroup_le_tailUnipotent (simpleRootB_mem_posRootsB i)
        ((mem_tailRootGroup_long (posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt hi))).2
          ⟨_, rfl⟩)
    exact ⟨⟨_, hx⟩, tailSimpleLong_tailLongElt hani hi _ hx⟩
  · rw [tailSimpleShort_apply]
    exact congrArg Multiplicative.ofAdd (tailCoord_dMap_uMap _ D 1 L C)
  · have hroot : simpleRootB r i ∉ roots r := by
      rw [simpleRootB_of_not_lt (by omega)]
      exact eps_not_mem_roots i
    have hx : tailShortElt r qA (simpleRootB r i) (Multiplicative.toAdd y) ∈ tailUnipotent r qA :=
      tailRootGroup_le_tailUnipotent (simpleRootB_mem_posRootsB i)
        (by rw [tailRootGroup_of_not_mem_roots hroot]; exact ⟨_, rfl⟩)
    exact ⟨⟨_, hx⟩, tailSimpleShort_tailShortElt hani hi _ hx⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
