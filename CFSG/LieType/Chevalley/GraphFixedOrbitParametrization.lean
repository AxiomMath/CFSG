module

public import CFSG.LieType.Chevalley.GraphFixedOrbitParameters
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.LieType.Chevalley.FoldedRootOrbits
public import CFSG.LieType.Chevalley.PositiveRootCollection
public import CFSG.LieType.Chevalley.TwistUnipotent

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

open CFSG.LieType.Chevalley Matrix

variable (t : TwistTag)

theorem orbitWord_eq_map_range (a : Fin t.foldedTag.rank) :
    t.orbitWord a = (List.range (t.orbit a).card).map fun k => (t.perm ^ k) (t.orbitMin a) := by
  revert a
  cases t <;> decide

theorem perm_pow_card_orbitMin (a : Fin t.foldedTag.rank) :
    (t.perm ^ (t.orbit a).card) (t.orbitMin a) = t.orbitMin a := by
  revert a
  cases t <;> decide

theorem perm_mem_orbit {a : Fin t.foldedTag.rank} {i : Fin t.tag.rank} (hi : i ∈ t.orbit a) :
    t.perm i ∈ t.orbit a := by
  rw [t.mem_orbit_iff] at hi ⊢
  rw [t.orbitIndex_perm, hi]

theorem perm_symm_mem_orbit {a : Fin t.foldedTag.rank} {i : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) : t.perm.symm i ∈ t.orbit a := by
  rw [t.mem_orbit_iff] at hi ⊢
  rw [← t.orbitIndex_perm, Equiv.apply_symm_apply, hi]

theorem perm_pow_mem_orbit {a : Fin t.foldedTag.rank} {i : Fin t.tag.rank} (hi : i ∈ t.orbit a)
    (k : ℕ) : (t.perm ^ k) i ∈ t.orbit a := by
  induction k with
  | zero => exact hi
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact t.perm_mem_orbit ih

theorem map_perm_orbitWord_perm (a : Fin t.foldedTag.rank) :
    ((t.orbitWord a).map t.perm).Perm (t.orbitWord a) := by
  refine (List.perm_ext_iff_of_nodup ((t.nodup_orbitWord a).map t.perm.injective)
    (t.nodup_orbitWord a)).2 fun j => ?_
  rw [List.mem_map, t.mem_orbitWord]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact t.perm_mem_orbit ((t.mem_orbitWord).1 hi)
  · intro hj
    exact ⟨t.perm.symm j, (t.mem_orbitWord).2 (t.perm_symm_mem_orbit hj), t.perm.apply_symm_apply j⟩

theorem rootForm_single_single_eq_zero
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) :
    (Pi.single i 1 : Fin t.tag.rank → ℤ) ⬝ᵥ
      (t.tag.symmetrizedCartan *ᵥ (Pi.single j 1 : Fin t.tag.rank → ℤ)) = 0 := by
  have h := t.rootForm_smul_single_eq_zero 1 hi hj hij
  simpa only [one_smul] using h

theorem isSimplyLaced : t.tag = .D4 ∨ t.tag = .E6 ∨ t.tag = .E7 ∨ t.tag = .E8 := by
  cases t
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem exists_eq_perm_pow_orbitMin {a : Fin t.foldedTag.rank} {j : Fin t.tag.rank}
    (hj : j ∈ t.orbit a) : ∃ k < (t.orbit a).card, (t.perm ^ k) (t.orbitMin a) = j := by
  rw [t.orbit_eq_image_orbitMin a, Finset.mem_image] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  exact ⟨k, Finset.mem_range.1 hk, rfl⟩

theorem card_orbit_pos (a : Fin t.foldedTag.rank) : 0 < (t.orbit a).card :=
  Finset.card_pos.2 ⟨_, t.orbitMin_mem a⟩

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley Matrix

theorem list_prod_map_mul_of_commute {G ι : Type*} [Monoid G] (l : List ι) (f g : ι → G)
    (h : ∀ x ∈ l, ∀ y ∈ l, Commute (g x) (f y)) :
    (l.map fun x => f x * g x).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)]
    have hc : Commute (g a) (l.map f).prod := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      exact h a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
    rw [mul_assoc, ← mul_assoc (g a), hc.eq, mul_assoc, mul_assoc]

section Commute

variable {t : TwistTag} (K : Type) [Field K]

theorem commute_pinnedX_of_rootForm_eq_zero
    {α β : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (hβ : IsRoot t.tag β) (h0 : α ⬝ᵥ (t.tag.symmetrizedCartan *ᵥ β) = 0) (c d : K) :
    Commute (pinnedX t.tag K α c) (pinnedX t.tag K β d) :=
  (simply_laced_orthogonal_root_commutation t.tag t.isSimplyLaced).2 K α β hα hβ h0 _
    (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)

theorem commute_xUnit_xUnit
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (c d : K) :
    Commute (xUnit t.tag K i c) (xUnit t.tag K j d) := by
  by_cases hij : i = j
  · subst hij
    change xUnit t.tag K i c * xUnit t.tag K i d = xUnit t.tag K i d * xUnit t.tag K i c
    rw [← xUnit_add, ← xUnit_add, add_comm]
  · rw [← pinnedX_single, ← pinnedX_single]
    exact commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ i) (isRoot_single _ j)
      (t.rootForm_single_single_eq_zero hi hj hij) c d

theorem commute_xUnit_yUnit
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) (c d : K) :
    Commute (xUnit t.tag K i c) (yUnit t.tag K j d) := by
  rw [← pinnedX_single, ← pinnedX_neg_single]
  refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ i) (isRoot_neg_single _ j) ?_ c d
  rw [mulVec_neg, dotProduct_neg, t.rootForm_single_single_eq_zero hi hj hij, neg_zero]

theorem commute_yUnit_yUnit
    {a : Fin t.foldedTag.rank} {i j : Fin t.tag.rank}
    (hi : i ∈ t.orbit a) (hj : j ∈ t.orbit a) (hij : i ≠ j) (c d : K) :
    Commute (yUnit t.tag K i c) (yUnit t.tag K j d) := by
  rw [← pinnedX_neg_single, ← pinnedX_neg_single]
  refine commute_pinnedX_of_rootForm_eq_zero K (isRoot_neg_single _ i) (isRoot_neg_single _ j)
    ?_ c d
  rw [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
    t.rootForm_single_single_eq_zero hi hj hij]

theorem commute_weylElt_xUnit
    {a : Fin t.foldedTag.rank} {l j : Fin t.tag.rank}
    (hl : l ∈ t.orbit a) (hj : j ∈ t.orbit a) (hlj : l ≠ j) (c : K) :
    Commute (weylElt t.tag K l 1) (xUnit t.tag K j c) := by
  rw [weylElt_eq_xUnit_mul]
  exact ((commute_xUnit_xUnit K hl hj _ _).mul_left
    (commute_xUnit_yUnit K hj hl (Ne.symm hlj) _ _).symm).mul_left
      (commute_xUnit_xUnit K hl hj _ _)

theorem commute_weylElt_yUnit
    {a : Fin t.foldedTag.rank} {l j : Fin t.tag.rank}
    (hl : l ∈ t.orbit a) (hj : j ∈ t.orbit a) (hlj : l ≠ j) (c : K) :
    Commute (weylElt t.tag K l 1) (yUnit t.tag K j c) := by
  rw [weylElt_eq_xUnit_mul]
  exact ((commute_xUnit_yUnit K hl hj hlj _ _).mul_left
    (commute_yUnit_yUnit K hl hj hlj _ _)).mul_left (commute_xUnit_yUnit K hl hj hlj _ _)

end Commute

section OrbitProduct

variable (t : TwistTag) {K : Type} [Field K]

@[expose] def orbitXProd
    (a : Fin t.foldedTag.rank) (γ : Fin t.tag.rank → K) : ModGL t.tag K :=
  ((t.orbitWord a).map fun j => xUnit t.tag K j (γ j)).prod

theorem orbitXProd_congr
    {a : Fin t.foldedTag.rank} {γ γ' : Fin t.tag.rank → K}
    (h : ∀ j ∈ t.orbit a, γ j = γ' j) : orbitXProd t a γ = orbitXProd t a γ' := by
  unfold orbitXProd
  congr 1
  exact List.map_congr_left fun j hj => by rw [h j ((t.mem_orbitWord).1 hj)]

theorem orbitXProd_add
    (a : Fin t.foldedTag.rank) (γ γ' : Fin t.tag.rank → K) :
    orbitXProd t a (γ + γ') = orbitXProd t a γ * orbitXProd t a γ' := by
  unfold orbitXProd
  rw [← list_prod_map_mul_of_commute]
  · congr 1
    exact List.map_congr_left fun j _ => by rw [Pi.add_apply, xUnit_add]
  · intro x hx y hy
    exact commute_xUnit_xUnit K ((t.mem_orbitWord).1 hx) ((t.mem_orbitWord).1 hy) _ _

theorem orbitXProd_zero
    (a : Fin t.foldedTag.rank) :
    orbitXProd t a (0 : Fin t.tag.rank → K) = 1 := by
  have h := orbitXProd_add t a (0 : Fin t.tag.rank → K) 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem orbitXProd_mem_rootSpan
    (a : Fin t.foldedTag.rank) (γ : Fin t.tag.rank → K) :
    orbitXProd t a γ ∈
      rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  rw [← pinnedX_single]
  exact Subgroup.mem_iSup_of_mem (Pi.single j 1) (Subgroup.mem_iSup_of_mem
    ⟨j, (t.mem_orbitWord).1 hj, rfl⟩ (Subgroup.subset_closure ⟨_, rfl⟩))

theorem twistHom_orbitXProd
    (σ : K →+* K) (a : Fin t.foldedTag.rank) (γ : Fin t.tag.rank → K) :
    twistHom t K σ (orbitXProd t a γ) = orbitXProd t a fun j => σ (γ (t.perm.symm j)) := by
  unfold orbitXProd
  rw [map_list_prod, List.map_map]
  have h1 : (t.orbitWord a).map (twistHom t K σ ∘ fun j => xUnit t.tag K j (γ j)) =
      ((t.orbitWord a).map t.perm).map fun j => xUnit t.tag K j (σ (γ (t.perm.symm j))) := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => by simp [twistHom_xUnit]
  rw [h1]
  refine ((t.map_perm_orbitWord_perm a).map _).prod_eq' ?_
  refine List.pairwise_map.2 (((t.nodup_orbitWord a).map t.perm.injective).imp_of_mem ?_)
  intro x y hx hy _
  have hx' : x ∈ t.orbit a := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact t.perm_mem_orbit ((t.mem_orbitWord).1 hi)
  have hy' : y ∈ t.orbit a := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    exact t.perm_mem_orbit ((t.mem_orbitWord).1 hi)
  exact commute_xUnit_xUnit K hx' hy' _ _

theorem eq_of_orbitXProd_eq
    {a : Fin t.foldedTag.rank} {γ γ' : Fin t.tag.rank → K}
    (h : orbitXProd t a γ = orbitXProd t a γ') : ∀ j ∈ t.orbit a, γ j = γ' j := by
  have hinj := t.single_one_injective
  have hprod : ∀ γ'' : Fin t.tag.rank → K, orbitXProd t a γ'' =
      (((t.orbitWord a).map fun j => (Pi.single j 1 : Fin t.tag.rank → ℤ)).map fun β =>
        pinnedX t.tag K β (Function.extend (fun j => (Pi.single j 1 : Fin t.tag.rank → ℤ))
          γ'' 0 β)).prod := fun γ'' => by
    unfold orbitXProd
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun j _ => by
      simp only [Function.comp_apply, hinj.extend_apply, pinnedX_single]
  have key := pinnedX_list_prod_injective _ ((t.nodup_orbitWord a).map hinj)
    (fun β hβ => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hβ
      exact ⟨isRoot_single _ j, by rw [height_single]; exact one_pos⟩)
    (Function.extend (fun j => (Pi.single j 1 : Fin t.tag.rank → ℤ)) γ 0)
    (Function.extend (fun j => (Pi.single j 1 : Fin t.tag.rank → ℤ)) γ' 0)
    (by rw [← hprod γ, ← hprod γ', h])
  intro j hj
  have hj' := key (Pi.single j 1) (List.mem_map.2 ⟨j, (t.mem_orbitWord).2 hj, rfl⟩)
  rwa [hinj.extend_apply, hinj.extend_apply] at hj'

theorem exists_orbitXProd_eq
    {a : Fin t.foldedTag.rank} {u : ModGL t.tag K}
    (hu : u ∈
      rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))) :
    ∃ γ, orbitXProd t a γ = u := by
  set ω := t.orbitWord a
  set S := (fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)
  have hget : Function.Injective ω.get := List.nodup_iff_injective_get.1 (t.nodup_orbitWord a)
  set α : Fin ω.length → Fin t.tag.rank → ℤ := fun k => Pi.single (ω.get k) 1
  have hα : Function.Injective α := t.single_one_injective.comp hget
  have hrange : Set.range α = S := by
    ext β
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨ω.get k, (t.mem_orbitWord).1 (List.get_mem ω k), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨k, hk⟩ := List.get_of_mem ((t.mem_orbitWord).2 hj)
      refine ⟨k, ?_⟩
      change Pi.single (ω.get k) 1 = _
      rw [show ω.get k = j from hk]
  have hS : ∀ β ∈ S, IsRoot t.tag β ∧ 0 < height β := by
    rintro _ ⟨j, -, rfl⟩
    exact ⟨isRoot_single _ j, by rw [height_single]; exact one_pos⟩
  have hclosed : ∀ β ∈ S, ∀ β' ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot t.tag (m • β + n • β') →
      m • β + n • β' ∈ S := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ m n hm hn hr
    exfalso
    by_cases hij : i = j
    · subst hij
      rw [← add_smul, ← natCast_zsmul] at hr
      rcases (isRoot_smul_single_iff i _).1 hr with h | h <;> omega
    · exact not_isRoot_nsmul_single_add_nsmul_single hij (t.cartan_eq_zero_of_mem_orbit hi hj hij)
        hm hn hr
  obtain ⟨c, -, hc⟩ := ((positive_root_collection t.tag K).1 S hS hclosed α hα hrange).2.2 hu
  refine ⟨Function.extend ω.get c 0, ?_⟩
  rw [← hc]
  unfold orbitXProd
  congr 1
  refine List.ext_get (by simp [ω]) fun n h1 h2 => ?_
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]
  change xUnit t.tag K (ω.get ⟨n, by simpa using h1⟩)
    (Function.extend ω.get c 0 (ω.get ⟨n, by simpa using h1⟩)) = _
  rw [hget.extend_apply, pinnedX_single]

end OrbitProduct

section Parameters

variable (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)

@[expose] def orbitParam (a : Fin t.foldedTag.rank) (c : K) : Fin t.tag.rank → K :=
  Function.extend (fun k : Fin (t.orbit a).card => (t.perm ^ (k : ℕ)) (t.orbitMin a))
    (fun k => (σ ^ (k : ℕ)) c) 0

theorem orbitParam_pow {a : Fin t.foldedTag.rank} (c : K) {k : ℕ} (hk : k < (t.orbit a).card) :
    orbitParam t σ a c ((t.perm ^ k) (t.orbitMin a)) = (σ ^ k) c := by
  have hinj : Function.Injective
      fun k : Fin (t.orbit a).card => (t.perm ^ (k : ℕ)) (t.orbitMin a) :=
    fun k l h => Fin.ext (t.injOn_pow_orbitMin a (Finset.mem_coe.2 (Finset.mem_range.2 k.2))
      (Finset.mem_coe.2 (Finset.mem_range.2 l.2)) h)
  exact hinj.extend_apply (fun k : Fin (t.orbit a).card => (σ ^ (k : ℕ)) c) 0 ⟨k, hk⟩

theorem orbitParam_orbitMin (a : Fin t.foldedTag.rank) (c : K) :
    orbitParam t σ a c (t.orbitMin a) = c := by
  simpa using orbitParam_pow t σ c (t.card_orbit_pos a)

theorem orbitParam_add {a : Fin t.foldedTag.rank} (c c' : K) {j : Fin t.tag.rank}
    (hj : j ∈ t.orbit a) :
    orbitParam t σ a (c + c') j = orbitParam t σ a c j + orbitParam t σ a c' j := by
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk, orbitParam_pow t σ _ hk, map_add]

theorem coe_orbitX_eq_orbitXProd
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) = orbitXProd t a (orbitParam t σ a c) := by
  rw [coe_orbitX, orbitXProd, t.orbitWord_eq_map_range, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => by
    rw [Function.comp_apply, orbitParam_pow t σ _ (List.mem_range.1 hk)]

variable {t σ}

theorem orbitParam_perm {a : Fin t.foldedTag.rank} {c : K} (hc : (σ ^ (t.orbit a).card) c = c)
    {j : Fin t.tag.rank} (hj : j ∈ t.orbit a) :
    orbitParam t σ a c (t.perm j) = σ (orbitParam t σ a c j) := by
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitParam_pow t σ c hk, ← Equiv.Perm.mul_apply, ← pow_succ']
  rcases Nat.lt_or_ge (k + 1) (t.orbit a).card with hk' | hk'
  · rw [orbitParam_pow t σ c hk', pow_succ', RingHom.coe_mul, Function.comp_apply]
  · have hkd : k + 1 = (t.orbit a).card := le_antisymm (by omega) hk'
    rw [hkd, t.perm_pow_card_orbitMin, orbitParam_orbitMin, ← Function.comp_apply (f := σ),
      ← RingHom.coe_mul, ← pow_succ', hkd, hc]

variable (σ) in
theorem twistHom_orbitX
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    twistHom t K σ (orbitX t K σ a c) = orbitX t K σ a c := by
  rw [coe_orbitX_eq_orbitXProd, twistHom_orbitXProd]
  refine orbitXProd_congr t fun j hj => ?_
  have h := orbitParam_perm (mem_orbitField.1 c.2) (t.perm_symm_mem_orbit hj)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

variable (σ) in
theorem orbitX_add
    (a : Fin t.foldedTag.rank) (c c' : orbitField t K σ a) :
    orbitX t K σ a (c + c') = orbitX t K σ a c * orbitX t K σ a c' := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_orbitX_eq_orbitXProd, coe_orbitX_eq_orbitXProd,
    coe_orbitX_eq_orbitXProd, ← orbitXProd_add]
  exact orbitXProd_congr t fun j hj => by
    rw [Pi.add_apply, Subfield.coe_add, orbitParam_add t σ _ _ hj]

variable (σ) in
theorem orbitX_injective
    (a : Fin t.foldedTag.rank) : Function.Injective (orbitX t K σ a) := by
  intro c c' h
  have h' := eq_of_orbitXProd_eq t (γ := orbitParam t σ a c) (γ' := orbitParam t σ a c')
    (by rw [← coe_orbitX_eq_orbitXProd, ← coe_orbitX_eq_orbitXProd, h])
    (t.orbitMin a) (t.orbitMin_mem a)
  rw [orbitParam_orbitMin, orbitParam_orbitMin] at h'
  exact Subtype.ext h'

theorem exists_orbitX_eq
    {a : Fin t.foldedTag.rank} {u : ModGL t.tag K}
    (hu : u ∈
      rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)))
    (hfix : twistHom t K σ u = u) :
    ∃ c : orbitField t K σ a, (orbitX t K σ a c : ModGL t.tag K) = u := by
  obtain ⟨γ, rfl⟩ := exists_orbitXProd_eq t hu
  rw [twistHom_orbitXProd] at hfix
  have hγ : ∀ j ∈ t.orbit a, γ (t.perm j) = σ (γ j) := fun j hj => by
    have h := eq_of_orbitXProd_eq t hfix (t.perm j) (t.perm_mem_orbit hj)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hpow : ∀ k : ℕ, γ ((t.perm ^ k) (t.orbitMin a)) = (σ ^ k) (γ (t.orbitMin a)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hγ _ (t.perm_pow_mem_orbit (t.orbitMin_mem a) k), ih,
        pow_succ', RingHom.coe_mul, Function.comp_apply]
  have hc : γ (t.orbitMin a) ∈ orbitField t K σ a := by
    rw [mem_orbitField, ← hpow, t.perm_pow_card_orbitMin]
  refine ⟨⟨γ (t.orbitMin a), hc⟩, ?_⟩
  rw [coe_orbitX_eq_orbitXProd]
  refine orbitXProd_congr t fun j hj => ?_
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitParam_pow t σ _ hk, hpow]

end Parameters

theorem rootSpan_mono
    {τ : Tag} {R : Type*} [CommRing R] {S T : Set (Fin τ.rank → ℤ)}
    (h : S ⊆ T) : rootSpan τ R S ≤ rootSpan τ R T :=
  biSup_mono h

theorem weylElt_mul_xUnit_mul_inv
    {τ : Tag} {R : Type} [CommRing R] (j : Fin τ.rank) (c : R) :
    weylElt τ R j 1 * xUnit τ R j c * (weylElt τ R j 1)⁻¹ = yUnit τ R j (-c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit, weylElt_mul_xOp_mul_inv]
  simp

section Equivalences

variable (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)

theorem orbitX_mem
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈
      rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ :=
  Subgroup.mem_inf.2 ⟨by rw [coe_orbitX_eq_orbitXProd]; exact orbitXProd_mem_rootSpan t a _,
    (coe_mem_twistedFixedGroup_iff t K σ _).2 (Subtype.ext (twistHom_orbitX σ a c))⟩

@[expose] def orbitXAdjHom
    (a : Fin t.foldedTag.rank) :
    Multiplicative (orbitField t K σ a) →* adjointGroup t.tag K where
  toFun c := orbitX t K σ a c.toAdd
  map_one' := by
    have h := orbitX_add σ a (0 : orbitField t K σ a) 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  map_mul' c c' := orbitX_add σ a c.toAdd c'.toAdd

@[expose] def orbitXHom
    (a : Fin t.foldedTag.rank) :
    Multiplicative (orbitField t K σ a) →*
      ↥(rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ) :=
  ((adjointGroup t.tag K).subtype.comp (orbitXAdjHom t σ a)).codRestrict _
    fun c => orbitX_mem t σ a c.toAdd

theorem orbitXHom_bijective
    (a : Fin t.foldedTag.rank) : Function.Bijective (orbitXHom t σ a) := by
  refine ⟨fun c c' h => ?_, fun u => ?_⟩
  · have h1 : (orbitXHom t σ a c : ModGL t.tag K) = (orbitXHom t σ a c' : ModGL t.tag K) :=
      congrArg Subtype.val h
    have h' : orbitX t K σ a c.toAdd = orbitX t K σ a c'.toAdd := Subtype.ext h1
    exact Multiplicative.toAdd.injective (orbitX_injective σ a h')
  · obtain ⟨c, hc⟩ := exists_orbitX_eq (σ := σ) (Subgroup.mem_inf.1 u.2).1
      ((mem_twistedFixedGroup_iff_twistHom t K σ).1 (Subgroup.mem_inf.1 u.2).2).2
    exact ⟨Multiplicative.ofAdd c, Subtype.ext hc⟩

@[expose] def orbitXEquiv
    (a : Fin t.foldedTag.rank) :
    Multiplicative (orbitField t K σ a) ≃*
      ↥(rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ) :=
  MulEquiv.ofBijective _ (orbitXHom_bijective t σ a)

theorem coe_orbitXEquiv
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitXEquiv t σ a (Multiplicative.ofAdd c) : ModGL t.tag K) = orbitX t K σ a c :=
  rfl

theorem canonicalRep_conj_orbitX_mem
    (a : Fin t.foldedTag.rank) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) (c : orbitField t K σ a) :
    canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a c *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
      rootSpan t.tag K ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ := by
  have hn := canonicalRep_mem_twistedFixedGroup t K σ hw
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hn (orbitX_mem t σ a c).2) (inv_mem hn)⟩
  have h := (canonical_weyl_root_transport t.tag K).1 w
    ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))
    (by rintro _ ⟨i, -, rfl⟩; exact isRoot_single _ i)
  rw [Set.image_image] at h
  rw [← h]
  exact ⟨_, (Subgroup.mem_inf.1 (orbitX_mem t σ a c)).1, rfl⟩

@[expose] def orbitConjHom
    (a : Fin t.foldedTag.rank) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    Multiplicative (orbitField t K σ a) →*
      ↥(rootSpan t.tag K ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ) :=
  ((MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom.comp
    ((adjointGroup t.tag K).subtype.comp (orbitXAdjHom t σ a))).codRestrict _
      fun c => canonicalRep_conj_orbitX_mem t σ a hw c.toAdd

theorem orbitConjHom_bijective
    (a : Fin t.foldedTag.rank) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) : Function.Bijective (orbitConjHom t σ a hw) := by
  set n := canonicalRep (coxeterSystem t.tag) K w
  refine ⟨fun c c' h => ?_, fun ⟨u, hu⟩ => ?_⟩
  · have h' : n * orbitX t K σ a c.toAdd * n⁻¹ = n * orbitX t K σ a c'.toAdd * n⁻¹ :=
      congrArg Subtype.val h
    rw [mul_left_inj, mul_right_inj] at h'
    exact Multiplicative.toAdd.injective (orbitX_injective σ a (Subtype.ext h'))
  · have hn := canonicalRep_mem_twistedFixedGroup t K σ hw
    obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.1 hu
    have h := (canonical_weyl_root_transport t.tag K).1 w
      ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))
      (by rintro _ ⟨i, -, rfl⟩; exact isRoot_single _ i)
    rw [Set.image_image] at h
    rw [← h] at hu₁
    obtain ⟨v, hv, hvu⟩ := hu₁
    have hvu' : n * v * n⁻¹ = u := hvu
    have hvΓ : v ∈ twistedFixedGroup t K σ := by
      have : v = n⁻¹ * u * n := by rw [← hvu']; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hn) hu₂) hn
    obtain ⟨c, hc⟩ := exists_orbitX_eq (σ := σ) hv
      ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hvΓ).2
    refine ⟨Multiplicative.ofAdd c, Subtype.ext ?_⟩
    change n * orbitX t K σ a c * n⁻¹ = u
    rw [hc, hvu']

@[expose] def orbitConjEquiv
    (a : Fin t.foldedTag.rank) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    Multiplicative (orbitField t K σ a) ≃*
      ↥(rootSpan t.tag K ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ) :=
  MulEquiv.ofBijective _ (orbitConjHom_bijective t σ a hw)

theorem coe_orbitConjEquiv
    (a : Fin t.foldedTag.rank) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) (c : orbitField t K σ a) :
    (orbitConjEquiv t σ a hw (Multiplicative.ofAdd c) : ModGL t.tag K) =
      canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a c *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ :=
  rfl

theorem isReduced_orbitWord
    (a : Fin t.foldedTag.rank) :
    (coxeterSystem t.tag).IsReduced (t.orbitWord a) := by
  have h := length_mul_wordProd_of_pos (w := (1 : WeylGroup t.tag)) (t.nodup_orbitWord a)
    (fun _ hi _ hj => t.cartan_eq_zero_of_mem_orbitWord hi hj)
    (fun i _ => by rw [one_smul, height_single]; exact one_pos)
  rw [one_mul, (coxeterSystem t.tag).length_one, zero_add] at h
  exact h

theorem canonicalRep_orbitReflection
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      ((t.orbitWord a).map fun j => weylElt t.tag K j 1).prod :=
  canonicalRep_wordProd (isReduced_orbitWord t a)

theorem list_prod_weylElt_conj_xUnit
    {a : Fin t.foldedTag.rank} (ω : List (Fin t.tag.rank))
    (hω : ω.Nodup) (hωa : ∀ l ∈ ω, l ∈ t.orbit a) {j : Fin t.tag.rank} (hj : j ∈ ω) (d : K) :
    (ω.map fun l => weylElt t.tag K l 1).prod * xUnit t.tag K j d *
        ((ω.map fun l => weylElt t.tag K l 1).prod)⁻¹ = yUnit t.tag K j (-d) := by
  induction ω with
  | nil => exact absurd hj List.not_mem_nil
  | cons l ω ih =>
    rw [List.nodup_cons] at hω
    have hl := hωa l List.mem_cons_self
    have hωa' : ∀ l' ∈ ω, l' ∈ t.orbit a := fun l' hl' => hωa l' (List.mem_cons_of_mem _ hl')
    rw [List.map_cons, List.prod_cons]
    set P := (ω.map fun l => weylElt t.tag K l 1).prod
    have e : weylElt t.tag K l 1 * P * xUnit t.tag K j d * (weylElt t.tag K l 1 * P)⁻¹ =
        weylElt t.tag K l 1 * (P * xUnit t.tag K j d * P⁻¹) * (weylElt t.tag K l 1)⁻¹ := by
      group
    rw [e]
    by_cases hlj : l = j
    · subst hlj
      have hc : Commute P (xUnit t.tag K l d) := Commute.list_prod_left _ _ fun x hx => by
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hx
        exact commute_weylElt_xUnit K (hωa' l' hl') hl (fun h => hω.1 (h ▸ hl')) d
      rw [hc.eq, mul_inv_cancel_right, weylElt_mul_xUnit_mul_inv]
    · have hj' : j ∈ ω := (List.mem_cons.1 hj).resolve_left (Ne.symm hlj)
      rw [ih hω.2 hωa' hj', (commute_weylElt_yUnit K hl (hωa j hj) hlj _).eq,
        mul_inv_cancel_right]

theorem canonicalRep_orbitReflection_conj_orbitX
    (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ a) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * orbitX t K σ a (-c) *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ =
      orbitY t K σ a c := by
  rw [coe_orbitX, coe_orbitY, ← MulAut.conj_apply, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [Function.comp_apply, MulAut.conj_apply, canonicalRep_orbitReflection,
    list_prod_weylElt_conj_xUnit t (t.orbitWord a) (t.nodup_orbitWord a)
      (fun l hl => (t.mem_orbitWord).1 hl)
      ((t.mem_orbitWord).2 (t.perm_pow_mem_orbit (t.orbitMin_mem a) k)),
    Subfield.coe_neg, map_neg, neg_neg]

theorem image_orbitReflection_smul_single
    (a : Fin t.foldedTag.rank) :
    (fun i => t.orbitReflection a • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) =
      (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) :=
  Set.image_congr fun _ hi => t.orbitReflection_smul_single hi

@[expose] def orbitYEquiv
    (a : Fin t.foldedTag.rank) :
    Multiplicative (orbitField t K σ a) ≃*
      ↥(rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
        twistedFixedGroup t K σ) :=
  (AddEquiv.toMultiplicative (AddEquiv.neg (orbitField t K σ a))).trans
    ((orbitConjEquiv t σ a (t.orbitReflection_mem a)).trans
      (MulEquiv.subgroupCongr (by rw [image_orbitReflection_smul_single])))

theorem coe_orbitYEquiv
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitYEquiv t σ a (Multiplicative.ofAdd c) : ModGL t.tag K) = orbitY t K σ a c :=
  canonicalRep_orbitReflection_conj_orbitX t σ a c

theorem orbitX_mem_graphFixedPosUnipotent
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) ∈ graphFixedPosUnipotent t K σ :=
  Subgroup.mem_inf.2 ⟨rootSpan_mono (by
      rintro _ ⟨i, -, rfl⟩
      exact ⟨isRoot_single _ i, by rw [height_single]; exact one_pos⟩)
    (Subgroup.mem_inf.1 (orbitX_mem t σ a c)).1, (Subgroup.mem_inf.1 (orbitX_mem t σ a c)).2⟩

theorem orbitY_mem_graphFixedNegUnipotent
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    (orbitY t K σ a c : ModGL t.tag K) ∈ graphFixedNegUnipotent t K σ := by
  rw [← coe_orbitYEquiv t σ a c]
  obtain ⟨h₁, h₂⟩ := Subgroup.mem_inf.1 (orbitYEquiv t σ a (Multiplicative.ofAdd c)).2
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ h₁, h₂⟩
  rintro _ ⟨i, -, rfl⟩
  exact ⟨isRoot_neg_single _ i, by rw [height_neg, height_single]; omega⟩

theorem orbitN_mem_graphFixedRootGroup
    (a : Fin t.foldedTag.rank)
    (u : (orbitField t K σ a)ˣ) :
    (orbitN t K σ a u : ModGL t.tag K) ∈ graphFixedRootGroup t K σ := by
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a _))
    (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
      (orbitY_mem_graphFixedNegUnipotent t σ a _)))
    (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a _))

theorem orbitH_mem_graphFixedRootGroup
    (a : Fin t.foldedTag.rank)
    (u : (orbitField t K σ a)ˣ) :
    (orbitH t K σ a u : ModGL t.tag K) ∈ graphFixedRootGroup t K σ := by
  rw [orbitH, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mul_mem (orbitN_mem_graphFixedRootGroup t σ a u)
    (inv_mem (orbitN_mem_graphFixedRootGroup t σ a 1))

end Equivalences

theorem fixed_root_orbit_parametrization
    (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) :
    (∀ a, ∀ w ∈ relWeylTwist t, ∃ e : Multiplicative (orbitField t K σ a) ≃*
        ↥(rootSpan t.tag K ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
          twistedFixedGroup t K σ),
      ∀ c : orbitField t K σ a, (e (Multiplicative.ofAdd c) : ModGL t.tag K) =
        canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a c *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹) ∧
    (∀ a, ∃ e : Multiplicative (orbitField t K σ a) ≃*
        ↥(rootSpan t.tag K ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
          twistedFixedGroup t K σ),
      ∀ c : orbitField t K σ a, (e (Multiplicative.ofAdd c) : ModGL t.tag K) = orbitX t K σ a c) ∧
    (∀ a, ∃ e : Multiplicative (orbitField t K σ a) ≃*
        ↥(rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
          twistedFixedGroup t K σ),
      ∀ c : orbitField t K σ a, (e (Multiplicative.ofAdd c) : ModGL t.tag K) = orbitY t K σ a c) ∧
    (∀ a (c : orbitField t K σ a),
      (orbitX t K σ a c : ModGL t.tag K) ∈ graphFixedPosUnipotent t K σ ∧
        (orbitY t K σ a c : ModGL t.tag K) ∈ graphFixedNegUnipotent t K σ) ∧
    ∀ a (u : (orbitField t K σ a)ˣ),
      (orbitN t K σ a u : ModGL t.tag K) ∈ graphFixedRootGroup t K σ ∧
        (orbitH t K σ a u : ModGL t.tag K) ∈ graphFixedRootGroup t K σ :=
  ⟨fun a _ hw => ⟨orbitConjEquiv t σ a hw, coe_orbitConjEquiv t σ a hw⟩,
    fun a => ⟨orbitXEquiv t σ a, coe_orbitXEquiv t σ a⟩,
    fun a => ⟨orbitYEquiv t σ a, coe_orbitYEquiv t σ a⟩,
    fun a c => ⟨orbitX_mem_graphFixedPosUnipotent t σ a c,
      orbitY_mem_graphFixedNegUnipotent t σ a c⟩,
    fun a u => ⟨orbitN_mem_graphFixedRootGroup t σ a u, orbitH_mem_graphFixedRootGroup t σ a u⟩⟩

end CFSG.LieType.Chevalley
