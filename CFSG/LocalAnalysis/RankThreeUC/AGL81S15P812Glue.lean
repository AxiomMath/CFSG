module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812MatA
public import CFSG.RankThree.PartTwo.Sec11.Item116Coords
public import CFSG.RankThree.PartTwo.KFacts.K74Bloom

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.P812

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def psi (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) :
    Subgroup.normalizer (A : Set G) →* GL (Fin 3) (ZMod 3) :=
  glEquiv.symm.toMonoidHom.comp (Sec12.wAction f)

theorem psi_mulVec (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (g : Subgroup.normalizer (A : Set G)) (v : Fin 3 → ZMod 3) :
    ((psi f g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
      Sec12.wAction f g v := by
  rw [← glEquiv_apply]
  simp [psi]

theorem psi_conj (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (g : Subgroup.normalizer (A : Set G)) (v : Fin 3 → ZMod 3) :
    ((f (Multiplicative.ofAdd (((psi f g : GL (Fin 3) (ZMod 3)) :
        Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v)) : A) : G) =
      (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  rw [psi_mulVec]
  exact Sec12.wAction_apply f g v

theorem gl_eq_of_mulVec_ev {g h : GL (Fin 3) (ZMod 3)}
    (H : ∀ j, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev j =
      (h : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev j) : g = h := by
  apply Units.ext
  ext i j
  have := congrFun (H j) i
  simpa [ev, Matrix.mulVec_single_one] using this

theorem psi_mulVec_ev (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (g : Subgroup.normalizer (A : Set G)) (j : Fin 3) (v : Fin 3 → ZMod 3)
    (h : (g : G) * (f (Multiplicative.ofAdd (ev j)) : G) * (g : G)⁻¹ =
      (f (Multiplicative.ofAdd v) : G)) :
    ((psi f g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev j = v := by
  have h1 := psi_conj f g (ev j)
  rw [h] at h1
  have h2 := f.injective (Subtype.ext h1)
  exact Multiplicative.ofAdd.injective h2

@[expose] def coordSub (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (W : Submodule (ZMod 3) (Fin 3 → ZMod 3)) : Subgroup G where
  carrier := {x | ∃ v ∈ W, ((f (Multiplicative.ofAdd v) : A) : G) = x}
  one_mem' := ⟨0, W.zero_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, W.add_mem hv hw, by simp [ofAdd_add]⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨-v, W.neg_mem hv, by simp [ofAdd_neg]⟩

theorem mem_normalizer_coordSub_iff [Finite G] (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (W : Submodule (ZMod 3) (Fin 3 → ZMod 3)) (g : Subgroup.normalizer (A : Set G)) :
    (g : G) ∈ Subgroup.normalizer (coordSub f W : Set G) ↔
      ∀ w ∈ W, ((psi f g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W := by
  constructor
  · intro hg w hw
    have hx : ((f (Multiplicative.ofAdd w) : A) : G) ∈ coordSub f W := ⟨w, hw, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp hx
    obtain ⟨v, hv, hveq⟩ := hconj
    rw [← psi_conj f g w] at hveq
    have h2 := f.injective (Subtype.ext hveq)
    have h3 := Multiplicative.ofAdd.injective h2
    rwa [← h3]
  · intro h
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨_, h v hv, psi_conj f g v⟩

theorem mem_cline_iff {i : Fin 3} {v : Fin 3 → ZMod 3} :
    v ∈ cline i ↔ ∀ j, j ≠ i → v j = 0 := by
  constructor
  · intro hv j hj
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [ev, Pi.single_apply, hj]
  · intro h
    refine Submodule.mem_span_singleton.mpr ⟨v i, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji
      simp [ev]
    · simp [ev, Pi.single_apply, hji, h j hji]

theorem mem_cplane_iff {i : Fin 3} {v : Fin 3 → ZMod 3} : v ∈ cplane i ↔ v i = 0 := by
  constructor
  · intro hv
    refine Submodule.span_induction (p := fun v _ => v i = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, hj, rfl⟩
      simp [ev, Pi.single_apply, Ne.symm hj]
    · simp
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro c x _ hx
      simp [hx]
  · intro h
    have hdec : v = (v 0) • ev 0 + (v 1) • ev 1 + (v 2) • ev 2 := by
      ext j
      fin_cases j <;> simp [ev, Pi.single_apply]
    have hmem : ∀ j, j ≠ i → ev j ∈ cplane i := fun j hj =>
      Submodule.subset_span ⟨j, hj, rfl⟩
    rw [hdec]
    fin_cases i
    · have h0 : v 0 = 0 := h
      rw [h0, zero_smul, zero_add]
      exact (cplane 0).add_mem ((cplane 0).smul_mem _ (hmem 1 (by decide)))
        ((cplane 0).smul_mem _ (hmem 2 (by decide)))
    · have h1 : v 1 = 0 := h
      rw [h1, zero_smul, add_zero]
      exact (cplane 1).add_mem ((cplane 1).smul_mem _ (hmem 0 (by decide)))
        ((cplane 1).smul_mem _ (hmem 2 (by decide)))
    · have h2 : v 2 = 0 := h
      rw [h2, zero_smul, add_zero]
      exact (cplane 2).add_mem ((cplane 2).smul_mem _ (hmem 0 (by decide)))
        ((cplane 2).smul_mem _ (hmem 1 (by decide)))

theorem mem_iff_of_invariant {W : Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hA : ∀ w ∈ W, ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W)
    (hB : ∀ w ∈ W, ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W)
    (v : Fin 3 → ZMod 3) : v ∈ W ↔ ∀ i, v i ≠ 0 → ev i ∈ W := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hunit : ∀ c : ZMod 3, c ≠ 0 → ∃ d : ZMod 3, d * c = 1 := fun c hc =>
    ⟨c⁻¹, inv_mul_cancel₀ hc⟩
  constructor
  · intro hv
    have h1 : v 1 ≠ 0 → ev 1 ∈ W := by
      intro hv1
      have hsub : v - ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ W :=
        W.sub_mem hv (hA v hv)
      have heq : v - ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
          (2 * v 1) • ev 1 := by
        rw [dA_mulVec]
        ext j
        fin_cases j <;> simp [ev, Pi.single_apply] <;> ring
      rw [heq] at hsub
      obtain ⟨d, hd⟩ := hunit (2 * v 1) (mul_ne_zero h2 hv1)
      have := W.smul_mem d hsub
      rwa [smul_smul, hd, one_smul] at this
    have h2' : v 2 ≠ 0 → ev 2 ∈ W := by
      intro hv2
      have hsub : v - ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ W :=
        W.sub_mem hv (hB v hv)
      have heq : v - ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v =
          (2 * v 2) • ev 2 := by
        rw [dB_mulVec]
        ext j
        fin_cases j <;> simp [ev, Pi.single_apply] <;> ring
      rw [heq] at hsub
      obtain ⟨d, hd⟩ := hunit (2 * v 2) (mul_ne_zero h2 hv2)
      have := W.smul_mem d hsub
      rwa [smul_smul, hd, one_smul] at this
    have h1' : v 1 • ev 1 ∈ W := by
      by_cases hv1 : v 1 = 0
      · simp [hv1]
      · exact W.smul_mem _ (h1 hv1)
    have h2'' : v 2 • ev 2 ∈ W := by
      by_cases hv2 : v 2 = 0
      · simp [hv2]
      · exact W.smul_mem _ (h2' hv2)
    have h0' : v 0 • ev 0 ∈ W := by
      have : v 0 • ev 0 = v - v 1 • ev 1 - v 2 • ev 2 := by
        ext j
        fin_cases j <;> simp [ev, Pi.single_apply]
      rw [this]
      exact W.sub_mem (W.sub_mem hv h1') h2''
    intro i hi
    fin_cases i
    · have : v 0 ≠ 0 := hi
      obtain ⟨d, hd⟩ := hunit _ this
      have := W.smul_mem d h0'
      rwa [smul_smul, hd, one_smul] at this
    · exact h1 hi
    · exact h2' hi
  · intro h
    have hdec : v = (v 0) • ev 0 + (v 1) • ev 1 + (v 2) • ev 2 := by
      ext j
      fin_cases j <;> simp [ev, Pi.single_apply]
    have hterm : ∀ i, v i • ev i ∈ W := by
      intro i
      by_cases hi : v i = 0
      · simp [hi]
      · exact W.smul_mem _ (h i hi)
    rw [hdec]
    exact W.add_mem (W.add_mem (hterm 0) (hterm 1)) (hterm 2)

@[expose] def IsAdapted (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (a : Fin 3 → G) : Prop :=
  ∀ v : Fin 3 → ZMod 3, ((f (Multiplicative.ofAdd v) : A) : G) =
    a 0 ^ (v 0).val * a 1 ^ (v 1).val * a 2 ^ (v 2).val

variable {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} {a : Fin 3 → G}

theorem adapted_smul_ev (h : IsAdapted f a) (i : Fin 3) (c : ZMod 3) :
    ((f (Multiplicative.ofAdd (c • ev i)) : A) : G) = a i ^ c.val := by
  rw [h]
  fin_cases i <;> simp [ev, Pi.single_apply]

theorem adapted_ev (h : IsAdapted f a) (i : Fin 3) :
    ((f (Multiplicative.ofAdd (ev i)) : A) : G) = a i := by
  have := adapted_smul_ev h i 1
  rwa [one_smul, ZMod.val_one, pow_one] at this

theorem adapted_neg_ev (h : IsAdapted f a) (i : Fin 3) :
    ((f (Multiplicative.ofAdd (-ev i)) : A) : G) = (a i)⁻¹ := by
  rw [ofAdd_neg, map_inv, Subgroup.coe_inv, adapted_ev h]

theorem coordSub_mono {W₁ W₂ : Submodule (ZMod 3) (Fin 3 → ZMod 3)} (h : W₁ ≤ W₂) :
    coordSub f W₁ ≤ coordSub f W₂ := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem coordSub_cline (h : IsAdapted f a) (ha3 : ∀ i, a i ^ 3 = 1) (i : Fin 3) :
    coordSub f (cline i) = Subgroup.zpowers (a i) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [ev] at *
    have := adapted_smul_ev h i c
    simp only [ev] at this
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rintro ⟨n, rfl⟩
    refine ⟨((n : ZMod 3)) • ev i, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    rw [adapted_smul_ev h i]
    exact (Sec11.zpow_eq_pow_val (ha3 i) n).symm

theorem coordSub_cplane_sup (h : IsAdapted f a) (ha3 : ∀ i, a i ^ 3 = 1) {i j k : Fin 3}
    (hall : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coordSub f (cplane i) = Subgroup.zpowers (a j) ⊔ Subgroup.zpowers (a k) := by
  rw [← coordSub_cline h ha3, ← coordSub_cline h ha3]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [mem_cplane_iff] at hv
    have hdec : v = (v j) • ev j + (v k) • ev k := by
      ext l
      rcases hall l with rfl | rfl | rfl
      · simp [ev, Pi.single_apply, hij.symm, hik.symm, hv]
      · simp [ev, Pi.single_apply, hjk]
      · simp [ev, Pi.single_apply, hjk.symm]
    rw [hdec]
    have hmul : ((f (Multiplicative.ofAdd ((v j) • ev j + (v k) • ev k)) : A) : G) =
        ((f (Multiplicative.ofAdd ((v j) • ev j)) : A) : G) *
          ((f (Multiplicative.ofAdd ((v k) • ev k)) : A) : G) := by
      simp [ofAdd_add]
    rw [hmul]
    exact Subgroup.mul_mem_sup
      ⟨_, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩
      ⟨_, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩
  · refine sup_le (coordSub_mono ?_) (coordSub_mono ?_)
    · rw [cline, Submodule.span_le]
      rintro _ rfl
      rw [SetLike.mem_coe, mem_cplane_iff]
      simp [ev, Pi.single_apply, hij.symm]
    · rw [cline, Submodule.span_le]
      rintro _ rfl
      rw [SetLike.mem_coe, mem_cplane_iff]
      simp [ev, Pi.single_apply, hik.symm]

theorem normalizer_le_of_centralizer_dvd [Finite G] {M X Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hM : ∀ g : G, g ∉ M →
      ¬ p ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom))
    (hY : Subgroup.normalizer (Y : Set G) ≤ M) (hXY : Y ≤ X)
    (hC : p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (X : Set G))) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hg
  by_contra hgM
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ Subgroup.centralizer (X : Set G))) p hC
  have hyM : (y : G) ∈ M := y.2.1
  have hyC : (y : G) ∈ Subgroup.centralizer (X : Set G) := y.2.2
  set y' : G := g * (y : G) * g⁻¹ with hy'
  have hgX : ∀ x ∈ X, g⁻¹ * x * g ∈ X := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using this
  have hy'C : y' ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.mp hyC (g⁻¹ * x * g) (hgX x hx)
    calc x * y' = g * ((g⁻¹ * x * g) * (y : G)) * g⁻¹ := by simp [hy', mul_assoc]
      _ = g * ((y : G) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y' * x := by simp [hy', mul_assoc]
  have hy'Y : y' ∈ Subgroup.centralizer (Y : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXY) hy'C
  have hy'M : y' ∈ M := hY (Subgroup.centralizer_le_normalizer (Y : Set G) hy'Y)
  have hy'Mg : y' ∈ M.map (MulAut.conj g).toMonoidHom :=
    ⟨(y : G), hyM, by simp [hy', MulAut.conj_apply]⟩
  apply hM g hgM
  have hmem : y' ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom := Subgroup.mem_inf.mpr ⟨hy'M, hy'Mg⟩
  have hord : orderOf (⟨y', hmem⟩ : ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) = p := by
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf y' = orderOf (y : G) := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (y : G)
      simpa [hy', MulAut.conj_apply] using this
    rw [h1, Subgroup.orderOf_coe, hy]
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem psi_eq_dA (hf : IsAdapted f a) {t : G} (ht : t ∈ Subgroup.normalizer (A : Set G))
    (h : t * a 0 * t⁻¹ = a 0 ∧ t * a 1 * t⁻¹ = (a 1)⁻¹ ∧ t * a 2 * t⁻¹ = a 2) :
    psi f ⟨t, ht⟩ = dA := by
  have e0 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 =
      ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 := by
    have hv : ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 = ev 0 := by
      rw [dA_mulVec]; ext l; fin_cases l <;> simp [ev]
    rw [hv]
    exact psi_mulVec_ev f ⟨t, ht⟩ 0 (ev 0) (by rw [adapted_ev hf]; exact h.1)
  have e1 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 =
      ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 := by
    have hv : ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 = -ev 1 := by
      rw [dA_mulVec]; ext l; fin_cases l <;> simp [ev]
    rw [hv]
    exact psi_mulVec_ev f ⟨t, ht⟩ 1 (-ev 1) (by rw [adapted_ev hf, adapted_neg_ev hf]; exact h.2.1)
  have e2 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 =
      ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 := by
    have hv : ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 = ev 2 := by
      rw [dA_mulVec]; ext l; fin_cases l <;> simp [ev]
    rw [hv]
    exact psi_mulVec_ev f ⟨t, ht⟩ 2 (ev 2) (by rw [adapted_ev hf]; exact h.2.2)
  apply gl_eq_of_mulVec_ev
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

theorem psi_eq_dB (hf : IsAdapted f a) {t : G} (ht : t ∈ Subgroup.normalizer (A : Set G))
    (h : t * a 0 * t⁻¹ = a 0 ∧ t * a 1 * t⁻¹ = a 1 ∧ t * a 2 * t⁻¹ = (a 2)⁻¹) :
    psi f ⟨t, ht⟩ = dB := by
  have e0 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 =
      ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 := by
    have hv : ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 = ev 0 := by
      rw [dB_mulVec]; ext l; fin_cases l <;> simp [ev]
    rw [hv]
    exact psi_mulVec_ev f ⟨t, ht⟩ 0 (ev 0) (by rw [adapted_ev hf]; exact h.1)
  have e1 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 =
      ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 := by
    have hv : ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 = ev 1 := by
      rw [dB_mulVec]; ext l; fin_cases l <;> simp [ev]
    rw [hv]
    exact psi_mulVec_ev f ⟨t, ht⟩ 1 (ev 1) (by rw [adapted_ev hf]; exact h.2.1)
  have e2 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 =
      ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 := by
    have hv : ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 = -ev 2 := by
      rw [dB_mulVec]; ext l; fin_cases l <;> simp [ev]
    rw [hv]
    exact psi_mulVec_ev f ⟨t, ht⟩ 2 (-ev 2) (by rw [adapted_ev hf, adapted_neg_ev hf]; exact h.2.2)
  apply gl_eq_of_mulVec_ev
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

theorem caseI_normalizer_le
    [Finite G]
    {M A : Subgroup G} {a : Fin 3 → G} {t₁ t₂ : G} {p : ℕ} (hp : p.Prime)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (haA : ∀ i, a i ∈ A) (hgen : Subgroup.closure {a 0, a 1, a 2} = A)
    (ht₁ : t₁ ∈ Subgroup.normalizer (A : Set G)) (ht₂ : t₂ ∈ Subgroup.normalizer (A : Set G))
    (h₁ : t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧ t₁ * a 2 * t₁⁻¹ = a 2)
    (h₂ : t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧ t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹)
    (hM : ∀ g : G, g ∉ M → ¬ p ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom))
    (hN : ∀ i, Subgroup.normalizer (Subgroup.zpowers (a i) : Set G) ≤ M)
    (hC : ∀ i j, i ≠ j → p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer
        ((Subgroup.zpowers (a i) ⊔ Subgroup.zpowers (a j) : Subgroup G) : Set G)))
    {S : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S) (hSidx : ¬ 3 ∣ S.relIndex M)
    (hSA : S ≤ Subgroup.centralizer (A : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  by_contra hW
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨f, -, -, -, hfv⟩ :=
    Sec11.exists_coords_triple hcomm hAel.2 h27 (haA 0) (haA 1) (haA 2) hgen
  have hf : IsAdapted f a := hfv
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => hAel.2 _ (haA i)
  have hdA : dA ∈ (psi f).range := ⟨⟨t₁, ht₁⟩, psi_eq_dA hf ht₁ h₁⟩
  have hdB : dB ∈ (psi f).range := ⟨⟨t₂, ht₂⟩, psi_eq_dB hf ht₂ h₂⟩
  have hNplane : ∀ i j, i ≠ j → Subgroup.normalizer
      ((Subgroup.zpowers (a i) ⊔ Subgroup.zpowers (a j) : Subgroup G) : Set G) ≤ M :=
    fun i j hij => normalizer_le_of_centralizer_dvd hp hM (hN i) le_sup_left (hC i j hij)
  have hcontra : ∀ X : Subgroup G,
      (∀ g : Subgroup.normalizer (A : Set G), (g : G) ∈ Subgroup.normalizer (X : Set G)) →
      Subgroup.normalizer (X : Set G) ≤ M → False :=
    fun X hX hXM => hW (fun g hg => hXM (hX ⟨g, hg⟩))
  have hirr : IsIrreducibleOn (psi f).range := by
    intro W' hW'
    have hinvA : ∀ w ∈ W', ((dA : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W' :=
      fun w hw => hW' dA hdA w hw
    have hinvB : ∀ w ∈ W', ((dB : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W' :=
      fun w hw => hW' dB hdB w hw
    have key := mem_iff_of_invariant hinvA hinvB
    have hnorm : ∀ g : Subgroup.normalizer (A : Set G),
        (g : G) ∈ Subgroup.normalizer (coordSub f W' : Set G) := fun g =>
      (mem_normalizer_coordSub_iff f W' g).mpr fun w hw => hW' (psi f g) ⟨g, rfl⟩ w hw
    have hcl : ∀ i, W' = cline i → False := by
      rintro i rfl
      refine hcontra (coordSub f (cline i)) hnorm ?_
      rw [coordSub_cline hf ha3 i]
      exact hN i
    have hpl : ∀ i j k, (∀ l : Fin 3, l = i ∨ l = j ∨ l = k) → i ≠ j → i ≠ k → j ≠ k →
        W' = cplane i → False := by
      rintro i j k hall hij hik hjk rfl
      refine hcontra (coordSub f (cplane i)) hnorm ?_
      rw [coordSub_cplane_sup hf ha3 hall hij hik hjk]
      exact hNplane j k hjk
    by_cases h0 : ev 0 ∈ W' <;> by_cases h1 : ev 1 ∈ W' <;> by_cases h2 : ev 2 ∈ W'
    · right
      refine eq_top_iff.mpr fun v _ => (key v).mpr fun i _ => ?_
      fin_cases i <;> assumption
    ·
      exfalso
      refine hpl 2 0 1 (by decide) (by decide) (by decide) (by decide) ?_
      ext v
      rw [key v, mem_cplane_iff]
      constructor
      · intro h; by_contra hne; exact h2 (h 2 hne)
      · intro h i hi
        fin_cases i
        · exact h0
        · exact h1
        · exact absurd h hi
    ·
      exfalso
      refine hpl 1 0 2 (by decide) (by decide) (by decide) (by decide) ?_
      ext v
      rw [key v, mem_cplane_iff]
      constructor
      · intro h; by_contra hne; exact h1 (h 1 hne)
      · intro h i hi
        fin_cases i
        · exact h0
        · exact absurd h hi
        · exact h2
    ·
      exfalso
      refine hcl 0 ?_
      ext v
      rw [key v, mem_cline_iff]
      constructor
      · intro h j hj
        by_contra hne
        have := h j hne
        fin_cases j
        · exact hj rfl
        · exact h1 this
        · exact h2 this
      · intro h i hi
        fin_cases i
        · exact h0
        · exact absurd (h 1 (by decide)) hi
        · exact absurd (h 2 (by decide)) hi
    ·
      exfalso
      refine hpl 0 1 2 (by decide) (by decide) (by decide) (by decide) ?_
      ext v
      rw [key v, mem_cplane_iff]
      constructor
      · intro h; by_contra hne; exact h0 (h 0 hne)
      · intro h i hi
        fin_cases i
        · exact absurd h hi
        · exact h1
        · exact h2
    ·
      exfalso
      refine hcl 1 ?_
      ext v
      rw [key v, mem_cline_iff]
      constructor
      · intro h j hj
        by_contra hne
        have := h j hne
        fin_cases j
        · exact h0 this
        · exact hj rfl
        · exact h2 this
      · intro h i hi
        fin_cases i
        · exact absurd (h 0 (by decide)) hi
        · exact h1
        · exact absurd (h 2 (by decide)) hi
    ·
      exfalso
      refine hcl 2 ?_
      ext v
      rw [key v, mem_cline_iff]
      constructor
      · intro h j hj
        by_contra hne
        have := h j hne
        fin_cases j
        · exact h0 this
        · exact h1 this
        · exact hj rfl
      · intro h i hi
        fin_cases i
        · exact absurd (h 0 (by decide)) hi
        · exact absurd (h 1 (by decide)) hi
        · exact h2
    · left
      refine eq_bot_iff.mpr fun v hv => ?_
      have := (key v).mp hv
      have hv0 : v = 0 := by
        ext i
        by_contra hne
        have hi := this i hne
        fin_cases i <;> contradiction
      rw [hv0]
      exact Submodule.zero_mem _
  obtain ⟨w, hwN, hwM⟩ := SetLike.not_le_iff_exists.mp hW
  rcases caseA_matrix _ hirr hdA hdB with ⟨i0, hall⟩ | ⟨h27H, htrans⟩
  ·
    rcases hall (psi f ⟨w, hwN⟩) ⟨⟨w, hwN⟩, rfl⟩ with hpres | hmap
    · have : w ∈ Subgroup.normalizer (Subgroup.zpowers (a i0) : Set G) := by
        rw [← coordSub_cline hf ha3 i0]
        exact (mem_normalizer_coordSub_iff f (cline i0) ⟨w, hwN⟩).mpr hpres
      exact hwM (hN i0 this)
    ·
      obtain ⟨j, k, hjk, hB⟩ : ∃ j k : Fin 3, j ≠ k ∧
          coordSub f (cplane i0) = Subgroup.zpowers (a j) ⊔ Subgroup.zpowers (a k) := by
        fin_cases i0
        · exact ⟨1, 2, by decide, coordSub_cplane_sup hf ha3 (by decide) (by decide) (by decide)
            (by decide)⟩
        · exact ⟨0, 2, by decide, coordSub_cplane_sup hf ha3 (by decide) (by decide) (by decide)
            (by decide)⟩
        · exact ⟨0, 1, by decide, coordSub_cplane_sup hf ha3 (by decide) (by decide) (by decide)
            (by decide)⟩
      have hwa : w * a i0 * w⁻¹ ∈ Subgroup.zpowers (a j) ⊔ Subgroup.zpowers (a k) := by
        rw [← hB]
        have h1 := psi_conj f ⟨w, hwN⟩ (ev i0)
        rw [adapted_ev hf] at h1
        refine ⟨_, hmap (ev i0) (Submodule.mem_span_singleton_self _), ?_⟩
        exact h1
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
        (G := ↥(M ⊓ Subgroup.centralizer
          ((Subgroup.zpowers (a j) ⊔ Subgroup.zpowers (a k) : Subgroup G) : Set G))) p (hC j k hjk)
      have hyM : (y : G) ∈ M := y.2.1
      have hyC := Subgroup.mem_centralizer_iff.mp y.2.2 _ hwa
      have hconj : w⁻¹ * (y : G) * w ∈ Subgroup.centralizer ({a i0} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        calc a i0 * (w⁻¹ * (y : G) * w) = w⁻¹ * ((w * a i0 * w⁻¹) * (y : G)) * w := by
              simp [mul_assoc]
          _ = w⁻¹ * ((y : G) * (w * a i0 * w⁻¹)) * w := by rw [hyC]
          _ = w⁻¹ * (y : G) * w * a i0 := by simp [mul_assoc]
      have hcenter : w⁻¹ * (y : G) * w ∈ Subgroup.normalizer (Subgroup.zpowers (a i0) : Set G) := by
        refine Subgroup.centralizer_le_normalizer (Subgroup.zpowers (a i0) : Set G) ?_
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨n, rfl⟩ := hx
        have := Subgroup.mem_centralizer_iff.mp hconj (a i0) rfl
        exact (Commute.zpow_left (show Commute (a i0) (w⁻¹ * (y : G) * w) from this) n).eq
      have hyM' : w⁻¹ * (y : G) * w ∈ M := hN i0 hcenter
      have hmemw : (y : G) ∈ M.map (MulAut.conj w).toMonoidHom :=
        ⟨w⁻¹ * (y : G) * w, hyM', by simp [MulAut.conj_apply, mul_assoc]⟩
      apply hM w hwM
      have hmem : (y : G) ∈ M ⊓ M.map (MulAut.conj w).toMonoidHom :=
        Subgroup.mem_inf.mpr ⟨hyM, hmemw⟩
      have hord : orderOf (⟨(y : G), hmem⟩ : ↥(M ⊓ M.map (MulAut.conj w).toMonoidHom)) = p := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy]
      rw [← hord]
      exact orderOf_dvd_natCard _
  ·
    have hSN : S ≤ Subgroup.normalizer (A : Set G) :=
      hSA.trans (Subgroup.centralizer_le_normalizer (A : Set G))
    have hSK : S.subgroupOf (Subgroup.normalizer (A : Set G)) ≤ (psi f).ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply gl_eq_of_mulVec_ev
      intro j
      rw [Units.val_one, Matrix.one_mulVec]
      refine psi_mulVec_ev f x j (ev j) ?_
      have hxS : (x : G) ∈ S := hx
      have hc := Subgroup.mem_centralizer_iff.mp (hSA hxS)
        ((f (Multiplicative.ofAdd (ev j)) : A) : G) (f (Multiplicative.ofAdd (ev j))).2
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    letI : MulDistribMulAction (Subgroup.normalizer (A : Set G)) A :=
      MulDistribMulAction.compHom A A.normalizerMonoidHom
    have hact : ∀ (g : Subgroup.normalizer (A : Set G)) (x : A),
        ((g • x : A) : G) = (g : G) * (x : G) * (g : G)⁻¹ := fun _ _ => rfl
    set a0 : A := ⟨a 0, haA 0⟩ with ha0
    have hev0 : ((f (Multiplicative.ofAdd (ev 0)) : A) : G) = a 0 := adapted_ev hf 0
    have horb : MulAction.orbit (Subgroup.normalizer (A : Set G)) a0 = ({1}ᶜ : Set A) := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩ hx1
        have hx1' : (g • a0 : A) = 1 := hx1
        have h1 : ((g • a0 : A) : G) = 1 := by rw [hx1']; rfl
        rw [hact] at h1
        have h2 : a 0 = 1 := by
          calc a 0 = (g : G)⁻¹ * ((g : G) * a 0 * (g : G)⁻¹) * (g : G) := by group
            _ = 1 := by rw [show (a0 : G) = a 0 from rfl] at h1; rw [h1]; group
        have h3 : f (Multiplicative.ofAdd (ev 0)) = f (Multiplicative.ofAdd 0) := by
          apply Subtype.ext
          rw [hev0, h2]
          simp
        have h4 := Multiplicative.ofAdd.injective (f.injective h3)
        have := congrFun h4 0
        simp [ev] at this
      · intro hx
        have hx1 : x ≠ 1 := hx
        have hv : Multiplicative.toAdd (f.symm x) ≠ 0 := by
          intro h0
          apply hx1
          have : f.symm x = 1 := by
            have := congrArg Multiplicative.ofAdd h0
            simpa using this
          simpa using congrArg f this
        obtain ⟨g', ⟨n, rfl⟩, hn⟩ := htrans _ hv
        refine ⟨n, ?_⟩
        apply Subtype.ext
        rw [hact]
        have := psi_conj f n (ev 0)
        rw [hn, hev0] at this
        rw [show (a0 : G) = a 0 from rfl, ← this]
        simp
    have hcard_orb : Nat.card (MulAction.orbit (Subgroup.normalizer (A : Set G)) a0) = 26 := by
      rw [horb, Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton, h27]
    have hos : Nat.card (MulAction.orbit (Subgroup.normalizer (A : Set G)) a0) =
        (MulAction.stabilizer (Subgroup.normalizer (A : Set G)) a0).index :=
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ a0)
    have hN2 : Nat.card ↥(MulAction.stabilizer (Subgroup.normalizer (A : Set G)) a0) * 26 =
        Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
      rw [← hcard_orb, hos]
      exact Subgroup.card_mul_index _
    have hN1 : Nat.card ↥(psi f).ker * Nat.card ↥(psi f).range =
        Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
      rw [← Subgroup.index_ker (psi f)]
      exact Subgroup.card_mul_index _
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hSdvdK : Nat.card S ∣ Nat.card ↥(psi f).ker := by
      have h := Subgroup.card_dvd_of_le hSK
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv] at h
    obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hS3
    have hdvd1 : Nat.card S * 27 ∣ Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
      rw [← hN1]
      exact Nat.mul_dvd_mul hSdvdK h27H
    have hcop : Nat.Coprime (Nat.card S * 27) 26 := by
      rw [hs]
      exact Nat.Coprime.mul_left (Nat.Coprime.pow_left s (by norm_num)) (by norm_num)
    have hdvd2 : Nat.card S * 27 ∣
        Nat.card ↥(MulAction.stabilizer (Subgroup.normalizer (A : Set G)) a0) := by
      rw [← hN2] at hdvd1
      exact hcop.dvd_of_dvd_mul_right hdvd1
    have hstabM : (MulAction.stabilizer (Subgroup.normalizer (A : Set G)) a0).map
        (Subgroup.normalizer (A : Set G)).subtype ≤ M := by
      rintro _ ⟨g, hg, rfl⟩
      have h1 : ((g • a0 : A) : G) = (a0 : G) := by
        rw [show g • a0 = a0 from hg]
      rw [hact] at h1
      have hcent : (g : G) ∈ Subgroup.centralizer (Subgroup.zpowers (a 0) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨n, rfl⟩ := hx
        have hc : (g : G) * a 0 = a 0 * (g : G) := by
          have := h1
          rw [show (a0 : G) = a 0 from rfl] at this
          calc (g : G) * a 0 = (g : G) * a 0 * (g : G)⁻¹ * (g : G) := by group
            _ = a 0 * (g : G) := by rw [this]
        exact (Commute.zpow_left (show Commute (a 0) (g : G) from hc.symm) n).eq
      exact hN 0 (Subgroup.centralizer_le_normalizer _ hcent)
    have hdvd3 : Nat.card ↥(MulAction.stabilizer (Subgroup.normalizer (A : Set G)) a0) ∣
        Nat.card M := by
      have h := Subgroup.card_dvd_of_le hstabM
      rwa [Subgroup.card_map_of_injective (Subgroup.normalizer (A : Set G)).subtype_injective] at h
    have hMcard : S.relIndex M * Nat.card S = Nat.card M := by
      have := Subgroup.relIndex_mul_card (H := S) (K := M)
      rwa [inf_of_le_left hSM] at this
    have hfin : Nat.card S * 27 ∣ Nat.card S * S.relIndex M := by
      rw [mul_comm (Nat.card S) (S.relIndex M), hMcard]
      exact hdvd2.trans hdvd3
    have h27idx : 27 ∣ S.relIndex M := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hfin
    exact hSidx (dvd_trans (by norm_num : 3 ∣ 27) h27idx)

end CFSG.LocalAnalysis.RankThreeUC.S15.P812
