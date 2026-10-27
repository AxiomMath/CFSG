module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots
import CFSG.ClassicalGroups.Symplectic.Model
import all CFSG.LieType.Universal.SymplecticExtras.RankOne

public section

namespace CFSG.AGLEmbeddingD2.SquareSymplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric

section Coord

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def coordFix (S : Finset ι) : Subgroup (GL ι F) where
  carrier := {g | ∀ a b, (a ∉ S ∨ b ∉ S) → (g : Matrix ι ι F) a b = (1 : Matrix ι ι F) a b}
  mul_mem' := by
    intro g h hg hh a b hab
    rw [Units.val_mul, Matrix.mul_apply]
    rcases hab with ha | hb
    · rw [Finset.sum_eq_single a]
      · rw [hg a a (Or.inl ha), Matrix.one_apply_eq, one_mul, hh a b (Or.inl ha)]
      · intro c _ hca
        rw [hg a c (Or.inl ha), Matrix.one_apply_ne (Ne.symm hca), zero_mul]
      · simp
    · rw [Finset.sum_eq_single b]
      · rw [hh b b (Or.inr hb), Matrix.one_apply_eq, mul_one, hg a b (Or.inr hb)]
      · intro c _ hcb
        rw [hh c b (Or.inr hb), Matrix.one_apply_ne hcb, mul_zero]
      · simp
  one_mem' := fun _ _ _ => rfl
  inv_mem' := by
    intro g hg a b hab
    have h1 : (g : Matrix ι ι F) * ((g⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((g⁻¹ : GL ι F) : Matrix ι ι F) * (g : Matrix ι ι F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rcases hab with ha | hb
    · have := congrFun (congrFun h1 a) b
      rw [Matrix.mul_apply, Finset.sum_eq_single a] at this
      · rwa [hg a a (Or.inl ha), Matrix.one_apply_eq, one_mul] at this
      · intro c _ hca
        rw [hg a c (Or.inl ha), Matrix.one_apply_ne (Ne.symm hca), zero_mul]
      · simp
    · have := congrFun (congrFun h2 a) b
      rw [Matrix.mul_apply, Finset.sum_eq_single b] at this
      · rwa [hg b b (Or.inr hb), Matrix.one_apply_eq, mul_one] at this
      · intro c _ hcb
        rw [hg c b (Or.inr hb), Matrix.one_apply_ne hcb, mul_zero]
      · simp

theorem coordFix_mono {S S' : Finset ι} (h : S ⊆ S') :
    (coordFix S : Subgroup (GL ι F)) ≤ coordFix S' := fun _ hg a b hab =>
  hg a b (hab.imp (fun ha hS => ha (h hS)) (fun hb hS => hb (h hS)))

@[expose] def restrictMat (S : Finset ι) :
    (coordFix S : Subgroup (GL ι F)) →* Matrix ↥S ↥S F where
  toFun g := (((g : GL ι F) : Matrix ι ι F)).submatrix (Subtype.val : ↥S → ι) Subtype.val
  map_one' := by
    ext a b
    simp [Matrix.one_apply]
  map_mul' g h := by
    ext a b
    have hgh : (((g * h : ↥(coordFix S)) : GL ι F) : Matrix ι ι F) =
        ((g : GL ι F) : Matrix ι ι F) * ((h : GL ι F) : Matrix ι ι F) := rfl
    rw [Matrix.submatrix_apply, hgh, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.submatrix_apply]
    rw [Finset.sum_coe_sort S (fun c => ((g : GL ι F) : Matrix ι ι F) a c *
      ((h : GL ι F) : Matrix ι ι F) c b)]
    refine (Finset.sum_subset (Finset.subset_univ S) fun c _ hc => ?_).symm
    have hac : (a : ι) ≠ c := fun h' => hc (h' ▸ a.2)
    rw [g.2 a c (Or.inr hc), Matrix.one_apply_ne hac, zero_mul]

theorem restrictMat_injective (S : Finset ι) :
    Function.Injective (restrictMat (F := F) S) := by
  intro g h hgh
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  by_cases hab : a ∈ S ∧ b ∈ S
  · exact congrFun (congrFun hgh ⟨a, hab.1⟩) ⟨b, hab.2⟩
  · rw [not_and_or] at hab
    rw [g.2 a b hab, h.2 a b hab]

theorem exists_injective_GL_coordFix (S : Finset ι) :
    ∃ φ : (coordFix S : Subgroup (GL ι F)) →* GL (Fin S.card) F, Function.Injective φ := by
  classical
  let e₂ : ↥S ≃ Fin S.card := Finset.equivFin S
  let r : GL ↥S F →* GL (Fin S.card) F :=
    Units.map (Matrix.reindexAlgEquiv F F e₂).toMonoidHom
  refine ⟨r.comp (restrictMat (F := F) S).toHomUnits, ?_⟩
  intro a b h
  apply restrictMat_injective S
  have h' := congrArg (fun u : GL (Fin S.card) F => (u : Matrix (Fin S.card) (Fin S.card) F)) h
  exact (Matrix.reindexAlgEquiv F F e₂).injective h'

variable [Fintype F] {f : ℕ}

theorem isCyclic_of_isPGroup_five_le_coordFix (hf : Odd f) (hk : Fintype.card F = 2 ^ f)
    {S : Finset ι} (hS : S.card ≤ 7) {P : Subgroup (GL ι F)} (hP : P ≤ coordFix S)
    (h5 : IsPGroup 5 P) : IsCyclic P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφ⟩ := exists_injective_GL_coordFix (F := F) S
  have hc := CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GL_two_pow hf hk hS φ hφ
    (P.subgroupOf (coordFix S)) (h5.comap_of_injective _ (Subgroup.subtype_injective _))
  exact (Subgroup.subgroupOfEquivOfLe hP).isCyclic.mp hc

theorem eq_bot_of_isPGroup_five_le_coordFix (hf : Odd f) (hk : Fintype.card F = 2 ^ f)
    {S : Finset ι} (hS : S.card ≤ 3) {P : Subgroup (GL ι F)} (hP : P ≤ coordFix S)
    (h5 : IsPGroup 5 P) : P = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφ⟩ := exists_injective_GL_coordFix (F := F) S
  have hc := CyclicSylowGL.eq_bot_of_isPGroup_five_of_injective_GL_two_pow hf hk hS φ hφ
    (P.subgroupOf (coordFix S)) (h5.comap_of_injective _ (Subgroup.subtype_injective _))
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (⟨x, hP hx⟩ : ↥(coordFix S)) ∈ P.subgroupOf (coordFix S) := hx
  rw [hc, Subgroup.mem_bot] at hx'
  exact congrArg Subtype.val hx'

end Coord

section Levi

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def leviSp (n : ℕ) (F : Type) [Field F] : GL (Fin n) F →* StatedSp n F :=
  (equivStatedSp n F).toMonoidHom.comp TauCeti.GLSymplecticFin.leviHom

theorem leviSp_injective : Function.Injective (leviSp n F) :=
  (equivStatedSp n F).injective.comp TauCeti.GLSymplecticFin.leviHom_injective

theorem mat_leviSp (A : GL (Fin n) F) :
    mat n F (leviSp n F A) =
      Matrix.fromBlocks (A : Matrix (Fin n) (Fin n) F) 0 0
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ :=
  mat_equiv_leviHom A

theorem leviSp_mem_coordFix {S : Finset (Fin n)} {A : GL (Fin n) F} (hA : A ∈ coordFix S) :
    ((leviSp n F A : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈ coordFix (S.disjSum S) := by
  intro x y hxy
  have h1 := mat_leviSp A
  rw [mat_apply] at h1
  rw [h1]
  have hA' : A⁻¹ ∈ coordFix S := inv_mem hA
  rw [← Matrix.fromBlocks_one]
  rcases x with a | a <;> rcases y with b | b
  · simp only [Matrix.fromBlocks_apply₁₁]
    exact hA a b (by simpa using hxy)
  · simp only [Matrix.fromBlocks_apply₁₂]
  · simp only [Matrix.fromBlocks_apply₂₁]
  · simp only [Matrix.fromBlocks_apply₂₂]
    have hba : b ∉ S ∨ a ∉ S := by simpa [or_comm] using hxy
    rw [Matrix.transpose_apply, hA' b a hba]
    simp [Matrix.one_apply, eq_comm]

theorem rankOne_le_comap_coordFix_long {i : Fin n} (hi : ¬ i.val + 1 < n) :
    rankOne (rootDatum n F).rootGroup i ≤
      (coordFix ({Sum.inl i, Sum.inr i} : Finset (Fin n ⊕ Fin n))).comap
        (StatedSp n F).subtype := by
  intro g hg a b hab
  have h := (rankOne_long_mem hi hg).1
  exact h a b (by simpa using hab)

theorem rankOne_le_map_coordFix_short {i : Fin n} (hi : i.val + 1 < n) :
    rankOne (rootDatum n F).rootGroup i ≤
      (coordFix ({i, ⟨i.val + 1, hi⟩} : Finset (Fin n))).map (leviSp n F) := by
  intro g hg
  obtain ⟨⟨A, hA, hgA⟩, -⟩ := rankOne_short_mem hi hg
  refine ⟨A, fun a b hab => hA a b (by simpa using hab), mat_injective ?_⟩
  exact hgA.symm

theorem rankOne_le_comap_coordFix_short {i : Fin n} (hi : i.val + 1 < n) :
    rankOne (rootDatum n F).rootGroup i ≤
      (coordFix (({i, ⟨i.val + 1, hi⟩} : Finset (Fin n)).disjSum
        {i, ⟨i.val + 1, hi⟩})).comap (StatedSp n F).subtype := by
  intro g hg
  obtain ⟨A, hA, rfl⟩ := rankOne_le_map_coordFix_short hi hg
  exact leviSp_mem_coordFix hA

end Levi

section Coords

variable {n : ℕ}

@[expose] noncomputable def coordsSp (A : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun a => ∃ i ∈ A, a.val = i.val ∨ a.val = i.val + 1

theorem mem_coordsSp {A : Set (Fin n)} {a : Fin n} :
    a ∈ coordsSp A ↔ ∃ i ∈ A, a.val = i.val ∨ a.val = i.val + 1 := by
  classical
  simp [coordsSp]

theorem self_mem_coordsSp {A : Set (Fin n)} {i : Fin n} (hi : i ∈ A) : i ∈ coordsSp A :=
  mem_coordsSp.2 ⟨i, hi, Or.inl rfl⟩

theorem succ_mem_coordsSp {A : Set (Fin n)} {i : Fin n} (hi : i ∈ A) (h : i.val + 1 < n) :
    (⟨i.val + 1, h⟩ : Fin n) ∈ coordsSp A :=
  mem_coordsSp.2 ⟨i, hi, Or.inr rfl⟩

theorem coordsSp_mono {A B : Set (Fin n)} (h : A ⊆ B) : coordsSp A ⊆ coordsSp B := fun _ ha => by
  obtain ⟨i, hi, hia⟩ := mem_coordsSp.1 ha
  exact mem_coordsSp.2 ⟨i, h hi, hia⟩

theorem coordsSp_union (A B : Set (Fin n)) : coordsSp (A ∪ B) ⊆ coordsSp A ∪ coordsSp B :=
  fun a ha => by
    obtain ⟨i, hi | hi, hia⟩ := mem_coordsSp.1 ha
    · exact Finset.mem_union_left _ (mem_coordsSp.2 ⟨i, hi, hia⟩)
    · exact Finset.mem_union_right _ (mem_coordsSp.2 ⟨i, hi, hia⟩)

theorem coordsSp_empty : coordsSp (∅ : Set (Fin n)) = ∅ := by
  ext a
  simp [mem_coordsSp]

theorem card_coordsSp_le_three (A : Set (Fin n))
    (h : ¬ ∃ a ∈ A, ∃ b ∈ A, a.val + 2 ≤ b.val) : (coordsSp A).card ≤ 3 := by
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha, hamin⟩ := Set.exists_min_image A (fun x : Fin n => x.val) A.toFinite hne
    have hall : ∀ x ∈ A, x.val ≤ a.val + 1 := by
      intro x hx
      by_contra hc
      exact h ⟨a, ha, x, hx, by omega⟩
    have : (coordsSp A).card ≤ (Finset.range 3).card := by
      refine Finset.card_le_card_of_injOn (fun y => y.val - a.val) ?_ ?_
      · intro y hy
        obtain ⟨i, hi, hyi⟩ := mem_coordsSp.1 hy
        have h1 := hamin i hi
        have h2 := hall i hi
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro y hy z hz hyz
        obtain ⟨i, hi, hyi⟩ := mem_coordsSp.1 hy
        obtain ⟨j, hj, hzj⟩ := mem_coordsSp.1 hz
        have h1 := hamin i hi
        have h2 := hamin j hj
        exact Fin.ext (by simp only at hyz; omega)
    simpa using this
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [coordsSp_empty]
    simp

theorem card_coordsSp_le_six (A : Set (Fin n))
    (h : ¬ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val) :
    (coordsSp A).card ≤ 6 := by
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha, hamin⟩ := Set.exists_min_image A (fun x : Fin n => x.val) A.toFinite hne
    set A₁ : Set (Fin n) := {x | x ∈ A ∧ x.val ≤ a.val + 1} with hA₁
    set A₂ : Set (Fin n) := {x | x ∈ A ∧ a.val + 2 ≤ x.val} with hA₂
    have h₁ : (coordsSp A₁).card ≤ 3 := by
      refine card_coordsSp_le_three A₁ ?_
      rintro ⟨x, hx, y, hy, hxy⟩
      have := hamin x hx.1
      have := hy.2
      omega
    have h₂ : (coordsSp A₂).card ≤ 3 := by
      refine card_coordsSp_le_three A₂ ?_
      rintro ⟨x, hx, y, hy, hxy⟩
      exact h ⟨a, ha, x, hx.1, y, hy.1, hx.2, hxy⟩
    have hsub : A ⊆ A₁ ∪ A₂ := fun x hx => by
      by_cases hx1 : x.val ≤ a.val + 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr ⟨hx, by omega⟩
    calc (coordsSp A).card ≤ (coordsSp A₁ ∪ coordsSp A₂).card :=
          Finset.card_le_card ((coordsSp_mono hsub).trans (coordsSp_union _ _))
      _ ≤ (coordsSp A₁).card + (coordsSp A₂).card := Finset.card_union_le _ _
      _ ≤ 6 := by omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [coordsSp_empty]
    simp

@[expose] def corner (n k : ℕ) : Finset (Fin n) := Finset.univ.filter fun a => n ≤ a.val + k

theorem mem_corner {n k : ℕ} {a : Fin n} : a ∈ corner n k ↔ n ≤ a.val + k := by
  simp [corner]

theorem card_corner_le (n k : ℕ) : (corner n k).card ≤ k := by
  have : (corner n k).card ≤ (Finset.range k).card := by
    refine Finset.card_le_card_of_injOn (fun a => a.val + k - n) ?_ ?_
    · intro a ha
      have h1 := mem_corner.1 ha
      have h2 := a.isLt
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro a ha b hb hab
      have h1 := mem_corner.1 ha
      have h2 := mem_corner.1 hb
      exact Fin.ext (by simp only at hab; omega)
  simpa using this

end Coords

section Glue

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commutes {A B : Subgroup G} (h : Commutes A B) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  have hsup : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [h a' ha' b hb]
      _ = a * a' * (b * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev]
    exact (h a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)).symm

theorem not_five_dvd_orderOf_of_forall_isPGroup_eq_bot [Finite G] {M : Subgroup G}
    (h : ∀ P : Subgroup G, P ≤ M → IsPGroup 5 P → P = ⊥) {a : G} (ha : a ∈ M) :
    ¬ 5 ∣ orderOf a := by
  intro hd
  have hfact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpos : orderOf a ≠ 0 := (orderOf_pos a).ne'
  set b := a ^ (orderOf a / 5) with hb
  have hb5 : orderOf b = 5 := orderOf_pow_orderOf_div hpos hd
  have hbM : b ∈ M := pow_mem ha _
  have hz : Subgroup.zpowers b = ⊥ := by
    apply h _ ((Subgroup.zpowers_le).2 hbM)
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb5, pow_one])
  rw [Subgroup.zpowers_eq_bot] at hz
  rw [hz, orderOf_one] at hb5
  omega

theorem isCyclic_of_isPGroup_five_le_sup_of_commutes [Finite G] {M₁ M₂ : Subgroup G}
    (hc : Commutes M₁ M₂) (h1 : ∀ P : Subgroup G, P ≤ M₁ → IsPGroup 5 P → P = ⊥)
    (h2 : ∀ P : Subgroup G, P ≤ M₂ → IsPGroup 5 P → IsCyclic P)
    {P : Subgroup G} (hP : P ≤ M₁ ⊔ M₂) (h5 : IsPGroup 5 P) : IsCyclic P := by
  refine h2 P (fun g hg => ?_) h5
  obtain ⟨a, ha, c, hcM, rfl⟩ := exists_mul_of_mem_sup_of_commutes hc (hP hg)
  obtain ⟨m, hm⟩ := h5 ⟨a * c, hg⟩
  have hm' : (a * c) ^ 5 ^ m = 1 := congrArg Subtype.val hm
  have hcomm : Commute a c := hc a ha c hcM
  rw [hcomm.mul_pow] at hm'
  have hapow : a ^ 5 ^ m ∈ M₂ := by
    have : a ^ 5 ^ m = (c ^ 5 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm'
    rw [this]
    exact inv_mem (pow_mem hcM _)
  have hcop : Nat.Coprime (5 ^ m) (orderOf a) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2
      (not_five_dvd_orderOf_of_forall_isPGroup_eq_bot h1 ha))
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  have haM : a ∈ M₂ := by
    rw [← ht]
    exact pow_mem hapow _
  exact mul_mem haM hcM

end Glue

section LeviM

variable {n : ℕ} {F : Type} [Field F]

theorem leviM_le_map_coordFix {A : Set (Fin n)} (hA : ∀ i ∈ A, i.val + 1 < n) :
    leviM (rootDatum n F) A ≤ (coordFix (coordsSp A)).map (leviSp n F) := by
  refine iSup₂_le fun (i : Fin n) hi => ?_
  have hsub : ({i, ⟨i.val + 1, hA i hi⟩} : Finset (Fin n)) ⊆ coordsSp A := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact self_mem_coordsSp hi
    · rw [Finset.mem_singleton.1 ha]
      exact succ_mem_coordsSp hi (hA i hi)
  exact (rankOne_le_map_coordFix_short (hA i hi)).trans
    (Subgroup.map_mono (coordFix_mono hsub))

@[expose] def cornerSp (n k : ℕ) : Finset (Fin n ⊕ Fin n) := (corner n k).disjSum (corner n k)

theorem card_cornerSp_le (n k : ℕ) : (cornerSp n k).card ≤ 2 * k := by
  rw [cornerSp, Finset.card_disjSum]
  have := card_corner_le n k
  omega

theorem leviM_le_comap_coordFix {C : Set (Fin n)} {k : ℕ} (hC : ∀ i ∈ C, n ≤ i.val + k) :
    leviM (rootDatum n F) C ≤ (coordFix (cornerSp n k)).comap (StatedSp n F).subtype := by
  refine iSup₂_le fun (i : Fin n) hi => ?_
  have hik := hC i hi
  by_cases hs : i.val + 1 < n
  · have hsub : ({i, ⟨i.val + 1, hs⟩} : Finset (Fin n)) ⊆ corner n k := by
      intro a ha
      rw [mem_corner]
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hik
      · rw [Finset.mem_singleton.1 ha]
        show n ≤ i.val + 1 + k
        omega
    exact (rankOne_le_comap_coordFix_short hs).trans
      (Subgroup.comap_mono (coordFix_mono (Finset.disjSum_mono hsub hsub)))
  · have hsub : ({Sum.inl i, Sum.inr i} : Finset (Fin n ⊕ Fin n)) ⊆ cornerSp n k := by
      intro a ha
      have hi' : i ∈ corner n k := mem_corner.2 hik
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact Finset.inl_mem_disjSum.2 hi'
      · rw [Finset.mem_singleton.1 ha]
        exact Finset.inr_mem_disjSum.2 hi'
    exact (rankOne_le_comap_coordFix_long hs).trans
      (Subgroup.comap_mono (coordFix_mono hsub))

variable [Fintype F] {f : ℕ}

theorem isCyclic_of_isPGroup_five_le_map_coordFix (hf : Odd f) (hk : Fintype.card F = 2 ^ f)
    {S : Finset (Fin n)} (hS : S.card ≤ 7) {P : Subgroup (StatedSp n F)}
    (hP : P ≤ (coordFix S).map (leviSp n F)) (h5 : IsPGroup 5 P) : IsCyclic P := by
  have hQ : P.comap (leviSp n F) ≤ coordFix S := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hP hx
    rwa [← leviSp_injective hyx]
  have hc := isCyclic_of_isPGroup_five_le_coordFix hf hk hS hQ
    (h5.comap_of_injective _ leviSp_injective)
  exact SquareLinear.isCyclic_of_le_range leviSp_injective
    (hP.trans (Subgroup.map_le_range _ _)) hc

theorem eq_bot_of_isPGroup_five_le_map_coordFix (hf : Odd f) (hk : Fintype.card F = 2 ^ f)
    {S : Finset (Fin n)} (hS : S.card ≤ 3) {P : Subgroup (StatedSp n F)}
    (hP : P ≤ (coordFix S).map (leviSp n F)) (h5 : IsPGroup 5 P) : P = ⊥ := by
  have hQ : P.comap (leviSp n F) ≤ coordFix S := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hP hx
    rwa [← leviSp_injective hyx]
  have hb := eq_bot_of_isPGroup_five_le_coordFix hf hk hS hQ
    (h5.comap_of_injective _ leviSp_injective)
  rw [← Subgroup.map_comap_eq_self (hP.trans (Subgroup.map_le_range _ _)), hb, Subgroup.map_bot]

theorem isCyclic_of_isPGroup_five_le_comap_coordFix (hf : Odd f) (hk : Fintype.card F = 2 ^ f)
    {S : Finset (Fin n ⊕ Fin n)} (hS : S.card ≤ 7) {P : Subgroup (StatedSp n F)}
    (hP : P ≤ (coordFix S).comap (StatedSp n F).subtype) (h5 : IsPGroup 5 P) : IsCyclic P := by
  have hinj : Function.Injective (StatedSp n F).subtype := Subgroup.subtype_injective _
  have hc := isCyclic_of_isPGroup_five_le_coordFix hf hk hS (P := P.map (StatedSp n F).subtype)
    (Subgroup.map_le_iff_le_comap.2 hP) (h5.map _)
  exact (P.equivMapOfInjective _ hinj).isCyclic.2 hc

end LeviM

section Residual

variable {n : ℕ} {F : Type} [Field F]

theorem cartan_eq_zero_of_far {a b : Fin n} (h : a.val + 2 ≤ b.val ∨ b.val + 2 ≤ a.val) :
    (rootDatum n F).cartan a b = 0 := by
  change cartanC n a b = 0
  have h1 : a ≠ b := fun h' => by rw [h'] at h; omega
  have h2 : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by omega
  simp [cartanC, h1, h2]

theorem cartan_edge {b c : Fin n} (hb : b.val + 2 = n) (hc : c.val + 1 = n) :
    (rootDatum n F).cartan c b = -1 ∧ (rootDatum n F).cartan b c = -2 := by
  have h1 : c ≠ b := fun h => by rw [h] at hc; omega
  constructor
  · change cartanC n c b = -1
    simp [cartanC, h1]
    omega
  · change cartanC n b c = -2
    simp [cartanC, h1.symm]
    omega

theorem commutes_leviM {A C : Set (Fin n)} (h : ∀ i ∈ A, ∀ j ∈ C, i.val + 2 ≤ j.val) :
    Commutes (leviM (rootDatum n F) A) (leviM (rootDatum n F) C) := by
  have hpair : ∀ i ∈ A, ∀ j ∈ C, Commutes (rankOne (rootDatum n F).rootGroup i)
      (rankOne (rootDatum n F).rootGroup j) := fun i hi j hj =>
    commutes_rankOne_of_cartan_eq_zero (steinbergExtras n F)
      (fun h' => by have := h i hi j hj; rw [h'] at this; omega)
      (cartan_eq_zero_of_far (Or.inl (h i hi j hj)))
  have h1 : ∀ i ∈ A, Commutes (rankOne (rootDatum n F).rootGroup i)
      (leviM (rootDatum n F) C) := by
    intro i hi
    refine Commutes.symm ?_
    rw [commutes_iff_le_centralizer]
    refine iSup₂_le fun j hj => ?_
    rw [← commutes_iff_le_centralizer]
    exact (hpair i hi j hj).symm
  rw [commutes_iff_le_centralizer]
  exact iSup₂_le fun i hi => commutes_iff_le_centralizer.1 (h1 i hi)

variable [Fintype F] {f : ℕ}

theorem isCyclic_of_isPGroup_five_leviM (hf : Odd f) (hk : Fintype.card F = 2 ^ f)
    {I : Set (Fin n)}
    (ho : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val)
    (hb : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a.val + 4 = n ∧ b.val + 2 = n ∧ c.val + 1 = n)
    {P : Subgroup (StatedSp n F)} (hP : P ≤ leviM (rootDatum n F) I) (h5 : IsPGroup 5 P) :
    IsCyclic P := by
  obtain ⟨k, hk3, hkI, hk0⟩ : ∃ k : ℕ, k ≤ 3 ∧ (∀ i ∈ I, i.val + k + 1 ≠ n) ∧
      (k = 0 ∨ ∃ i ∈ I, i.val + 1 = n) := by
    by_cases h1 : ∃ i ∈ I, i.val + 1 = n
    · by_cases h2 : ∃ i ∈ I, i.val + 2 = n
      · by_cases h3 : ∃ i ∈ I, i.val + 3 = n
        · refine ⟨3, le_rfl, fun i hi h4 => ?_, Or.inr h1⟩
          obtain ⟨c, hc, hc1⟩ := h1
          obtain ⟨b, hb2, hb2'⟩ := h2
          exact hb ⟨i, hi, b, hb2, c, hc, by omega, hb2', hc1⟩
        · exact ⟨2, by norm_num, fun i hi h3' => h3 ⟨i, hi, by omega⟩, Or.inr h1⟩
      · exact ⟨1, by norm_num, fun i hi h2' => h2 ⟨i, hi, by omega⟩, Or.inr h1⟩
    · exact ⟨0, by norm_num, fun i hi h1' => h1 ⟨i, hi, by omega⟩, Or.inl rfl⟩
  set A : Set (Fin n) := {i | i ∈ I ∧ i.val + k + 2 ≤ n} with hA
  set C : Set (Fin n) := {i | i ∈ I ∧ n ≤ i.val + k} with hC
  have hsplit : leviM (rootDatum n F) I ≤ leviM (rootDatum n F) A ⊔ leviM (rootDatum n F) C := by
    refine iSup₂_le fun (i : Fin n) hi => ?_
    have hik := hkI i hi
    have hlt := i.isLt
    by_cases hia : i.val + k + 2 ≤ n
    · exact (rankOne_le_leviM (D := rootDatum n F) (show i ∈ A from ⟨hi, hia⟩)).trans le_sup_left
    · exact (rankOne_le_leviM (D := rootDatum n F)
        (show i ∈ C from ⟨hi, by omega⟩)).trans le_sup_right
  have hAshort : ∀ i ∈ A, i.val + 1 < n := fun i hi => by have := hi.2; omega
  have hcomm : Commutes (leviM (rootDatum n F) A) (leviM (rootDatum n F) C) :=
    commutes_leviM fun i hi j hj => by have := hi.2; have := hj.2; omega
  rcases hk0 with hk0 | ⟨c, hcI, hc1⟩
  · have hIA : I ⊆ A := fun i hi => ⟨hi, by have := hkI i hi; have := i.isLt; omega⟩
    have hle : leviM (rootDatum n F) I ≤ leviM (rootDatum n F) A :=
      iSup₂_le fun i hi => rankOne_le_leviM (hIA hi)
    have hcard : (coordsSp A).card ≤ 6 :=
      card_coordsSp_le_six A fun ⟨a, ha, b, hb', c, hc, hab, hbc⟩ =>
        ho ⟨a, ha.1, b, hb'.1, c, hc.1, hab, hbc⟩
    exact isCyclic_of_isPGroup_five_le_map_coordFix hf hk (by omega)
      ((hP.trans hle).trans (leviM_le_map_coordFix hAshort)) h5
  · have hk1' : 1 ≤ k := by have := hkI c hcI; omega
    have hAno : ¬ ∃ a ∈ A, ∃ b ∈ A, a.val + 2 ≤ b.val := by
      rintro ⟨a, ha, b, hb', hab⟩
      have := hb'.2
      exact ho ⟨a, ha.1, b, hb'.1, c, hcI, hab, by omega⟩
    have hcard : (coordsSp A).card ≤ 3 := card_coordsSp_le_three A hAno
    have hAtriv : ∀ Q : Subgroup (StatedSp n F), Q ≤ leviM (rootDatum n F) A → IsPGroup 5 Q →
        Q = ⊥ := fun Q hQ hQ5 => eq_bot_of_isPGroup_five_le_map_coordFix hf hk hcard
      (hQ.trans (leviM_le_map_coordFix hAshort)) hQ5
    have hCcyc : ∀ Q : Subgroup (StatedSp n F), Q ≤ leviM (rootDatum n F) C → IsPGroup 5 Q →
        IsCyclic Q := by
      intro Q hQ hQ5
      have := card_cornerSp_le n k
      exact isCyclic_of_isPGroup_five_le_comap_coordFix hf hk (S := cornerSp n k) (by omega)
        (hQ.trans (leviM_le_comap_coordFix fun i hi => hi.2)) hQ5
    exact isCyclic_of_isPGroup_five_le_sup_of_commutes hcomm hAtriv hCcyc (hP.trans hsplit) h5

end Residual

section Facts

variable {n : ℕ} {F : Type} [Field F]

theorem statedScalars_subgroupOf_statedSp_eq_bot [CharP F 2] (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hmem : (c : F) ^ 2 = 1 := by
    have h := x.2
    rw [← hc, CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff hn] at h
    exact h
  have hc1 : (c : F) = 1 := by
    have h := sub_pow_char (p := 2) (c : F) 1
    rw [hmem, one_pow, sub_self] at h
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one]

theorem ker_comp_mk'_eq_bot [CharP F 2] (hn : 1 ≤ n) {Y : Type*} [Group Y]
    (e : Y ≃* StatedProj (StatedSp n F)) :
    (e.symm.toMonoidHom.comp (QuotientGroup.mk'
      ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)))).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F) := by
    simpa [MonoidHom.mem_ker, map_eq_one_iff _ e.symm.injective, QuotientGroup.eq_one_iff]
      using hx
  rw [statedScalars_subgroupOf_statedSp_eq_bot hn] at hx'
  exact hx'

theorem torus_elt_mem (k : Fin n) (c : Fˣ) :
    equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k c)) ∈ torus n F k :=
  Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨c, rfl⟩)

theorem torus_elt_pow_three (k : Fin n) {ω : Fˣ} (hω : ω ^ 3 = 1) :
    (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k ω))) ^ 3 = 1 := by
  rw [← map_pow, ← map_pow, corootVec_pow_eq_one k hω, map_one, map_one]

theorem torus_elt_ne_one (k : Fin n) {ω : Fˣ} (hω : ω ≠ 1) :
    equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal (corootVec n F k ω)) ≠ 1 := by
  intro h
  have h1 := congrArg (mat n F) h
  rw [mat_equiv_diagonal, map_one] at h1
  have h2 := congrFun (congrFun h1 (Sum.inl k)) (Sum.inl k)
  simp only [Matrix.diagonal_apply_eq, Sum.elim_inl, corootVec, ite_true,
    Matrix.one_apply_eq] at h2
  exact hω (Units.ext h2)

theorem exists_rankOne_eq_range (i : Fin n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp n F, Function.Injective φ ∧
      rankOne (rootDatum n F).rootGroup i = φ.range := by
  obtain ⟨φ, hφ, hx, hy⟩ := CFSG.LieType.Steinberg.Sp.rankOne (F := F) i
  exact ⟨φ, hφ, rankOne_eq_range_of_sl2 CFSG.LieType.Steinberg.Sp.isParametrization hx hy⟩

theorem commutes_map_conj {G : Type*} [Group G] {A B : Subgroup G} {w : G}
    (hAB : Commutes A B) (hAw : ∀ a ∈ A, a * w = w * a) :
    Commutes A (B.map (MulAut.conj w).toMonoidHom) := by
  rintro a ha _ ⟨b, hb, rfl⟩
  have h2 : a * w⁻¹ = w⁻¹ * a := (Commute.inv_right (hAw a ha : Commute a w))
  change a * (w * b * w⁻¹) = w * b * w⁻¹ * a
  calc a * (w * b * w⁻¹) = (a * w) * b * w⁻¹ := by group
    _ = w * a * b * w⁻¹ := by rw [hAw a ha]
    _ = w * (a * b) * w⁻¹ := by group
    _ = w * (b * a) * w⁻¹ := by rw [hAB a ha b hb]
    _ = w * b * (a * w⁻¹) := by group
    _ = w * b * (w⁻¹ * a) := by rw [h2]
    _ = w * b * w⁻¹ * a := by group

end Facts

section Slice

variable {n : ℕ} {F : Type} [Field F]

local notation "A₅" => alternatingGroup (Fin 5)

theorem three_le_pRank_sp [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSp n F)) {X : Type} [Group X] [Finite X]
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (hρ3 : Nat.Coprime 3 (Nat.card ρ.ker)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (hQ : LeviSection.HasSubquotient J (A₅ × A₅)) : 3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_sp e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hM := hasSubquotient_leviM_of_parab hb' hBJ hQ
  have hBJ' : (borel (rootDatum n F) (torus n F)).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
  have hr : ∀ i, ParabRealThree.HasRealOrderThree (rootDatum n F) i := fun i =>
    ParabRealThree.HasSL2Node.hasRealOrderThree (hasSL2Node_sp i)
  rcases Nat.even_or_odd (f : ℕ) with hfe | hfo
  ·
    obtain ⟨k, hk⟩ := hfe
    have hk1 : 1 ≤ k := by have := f.pos; omega
    have hq : Nat.card F = 4 ^ k := by rw [hfc, hk, ← two_mul, pow_mul]; norm_num
    have hq3 : 3 ∣ Nat.card F - 1 := by
      rw [hq]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    have hq4 : 4 ≤ Nat.card F := by
      rw [hq]
      exact le_self_pow₀ (by norm_num) (by omega)
    obtain ⟨ω, hω⟩ := SquareLinear.exists_orderOf_eq_three hq3
    by_cases hn3 : 3 ≤ n
    ·
      have hπ3 : Nat.Coprime 3 (Nat.card π'.ker) := by
        rw [hker', ker_comp_mk'_eq_bot (by omega) e, Subgroup.card_bot]
        exact Nat.coprime_one_right 3
      have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
      have hω1 : ω ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hω
        omega
      let a : Fin n := ⟨0, by omega⟩
      let b : Fin n := ⟨1, by omega⟩
      let c : Fin n := ⟨2, by omega⟩
      exact (three_le_pRank_of_torus hb'.extras hπ3 hBJ (a := a) (b := b) (c := c)
        (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
        (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
        (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) (torus_elt_mem a ω)
        (torus_elt_mem b ω) (torus_elt_mem c ω) (torus_elt_pow_three a hω3)
        (torus_elt_pow_three b hω3) (torus_elt_pow_three c hω3) (torus_elt_ne_one a hω1)
        (torus_elt_ne_one b hω1) (torus_elt_ne_one c hω1)).trans
        (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
    ·
      exfalso
      have hsub : (negIndices (rootDatum n F) (J.comap π')).Subsingleton := by
        intro x hx y hy
        have hxj : x.val ≠ j.val := fun h => hj (Fin.ext h ▸ hx)
        have hyj : y.val ≠ j.val := fun h => hj (Fin.ext h ▸ hy)
        have h1 : x.val < n := x.isLt
        have h2 : y.val < n := y.isLt
        have h3 : j.val < n := j.isLt
        exact Fin.ext (by omega)
      rcases hsub.eq_empty_or_singleton with hI | ⟨i, hI⟩
      · rw [hI, leviM_empty] at hM
        exact false_of_hasSubquotient_bot hM
      · obtain ⟨φ, hφ, hrange⟩ := exists_rankOne_eq_range (n := n) (F := F) i
        rw [hI, leviM_singleton, hrange] at hM
        refine false_of_hasSubquotient_of_isCyclic (fun P hP h3P => ?_) hM
        exact SquareLinear.isCyclic_of_le_range hφ hP
          (SquareLinear.isCyclic_of_isPGroup_three_sl2 hq4 _ (h3P.comap_of_injective _ hφ))
  ·
    by_cases ho : ∃ a ∈ negIndices (rootDatum n F) (J.comap π'),
        ∃ b ∈ negIndices (rootDatum n F) (J.comap π'),
        ∃ c ∈ negIndices (rootDatum n F) (J.comap π'), a.val + 2 ≤ b.val ∧ b.val + 2 ≤ c.val
    · obtain ⟨a, ha, b, hb2, c, hc, hab, hbc⟩ := ho
      exact three_le_pRank_of_orth hb'.extras hb'.ker_central ρ hρ hρker hBJ hr
        (fun h => by rw [h] at hab; omega) (fun h => by rw [h] at hab; omega)
        (fun h => by rw [h] at hbc; omega) (cartan_eq_zero_of_far (Or.inl hab))
        (cartan_eq_zero_of_far (Or.inl (by omega))) (cartan_eq_zero_of_far (Or.inl hbc)) ha hb2 hc
    · by_cases hb4 : ∃ a ∈ negIndices (rootDatum n F) (J.comap π'),
          ∃ b ∈ negIndices (rootDatum n F) (J.comap π'),
          ∃ c ∈ negIndices (rootDatum n F) (J.comap π'),
          a.val + 4 = n ∧ b.val + 2 = n ∧ c.val + 1 = n
      ·
        obtain ⟨a, ha, b, hb2, c, hc, ha4, hb2', hc1⟩ := hb4
        have hac : a ≠ c := fun h => by rw [h] at ha4; omega
        have hab : a ≠ b := fun h => by rw [h] at ha4; omega
        have hcb : c ≠ b := fun h => by rw [h] at hc1; omega
        have hnb : weylRep n F b ∈ rankOne (rootDatum n F).rootGroup b := hb'.ct.n_mem b
        have c12 : Commutes (rankOne (rootDatum n F).rootGroup a)
            (rankOne (rootDatum n F).rootGroup c) :=
          commutes_rankOne_of_cartan_eq_zero hb'.extras hac
            (cartan_eq_zero_of_far (Or.inl (by omega)))
        have hab' : Commutes (rankOne (rootDatum n F).rootGroup a)
            (rankOne (rootDatum n F).rootGroup b) :=
          commutes_rankOne_of_cartan_eq_zero hb'.extras hab
            (cartan_eq_zero_of_far (Or.inl (by omega)))
        have c13 : Commutes (rankOne (rootDatum n F).rootGroup a)
            ((rankOne (rootDatum n F).rootGroup c).map
              (MulAut.conj (weylRep n F b)).toMonoidHom) :=
          commutes_map_conj c12 fun x hx => hab' x hx _ hnb
        have c23 : Commutes (rankOne (rootDatum n F).rootGroup c)
            ((rankOne (rootDatum n F).rootGroup c).map
              (MulAut.conj (weylRep n F b)).toMonoidHom) :=
          ToralCensus.commutes_rankOne_bTwo hb'.ct hb'.extras rfl hcb (cartan_edge hb2' hc1).1
            (cartan_edge hb2' hc1).2
        have hbJ : π' (weylRep n F b) ∈ J := rankOne_le_of_mem_negIndices hBJ hb2 hnb
        exact three_le_pRank_of_triple hb'.ker_central ρ hρ hρker c12 c13 c23
          (realThreeOver_rankOne hBJ ha (hr a)) (realThreeOver_rankOne hBJ hc (hr c))
          ((realThreeOver_rankOne hBJ hc (hr c)).conj hbJ)
      ·
        exfalso
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        exact hM.false_of_isCyclic (fun P hP h5 => isCyclic_of_isPGroup_five_leviM hfo hf ho hb4
          hP h5) LeviSection.exists_not_isCyclic_five

end Slice

end CFSG.AGLEmbeddingD2.SquareSymplectic
