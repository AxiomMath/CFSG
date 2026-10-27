module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDEvenForm
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.BCDEven

open CFSG.Open Subgroup Polynomial Module Submodule CFSG.LocalAnalysis.RankFourTheoremC
open LinearMap (BilinForm)

section Prelim

instance instFiniteLinearEquivSelf {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] : Finite (V ≃ₗ[K] V) := by
  haveI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective

theorem card_subgroup_prod {A B : Type*} [Group A] [Group B] (E : Subgroup A) (F : Subgroup B) :
    Nat.card (E.prod F) = Nat.card E * Nat.card F := by
  have h : Nat.card ((E : Set A) ×ˢ (F : Set B) : Set (A × B)) =
      Nat.card (E : Set A) * Nat.card (F : Set B) := by
    rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  exact h

theorem pRank_top_prod_ge {p : ℕ} (hp : 1 < p) {A A' : Type*} [Group A] [Finite A] [Group A']
    [Finite A'] :
    CFSG.Open.pRank p (⊤ : Subgroup A) + CFSG.Open.pRank p (⊤ : Subgroup A') ≤
      CFSG.Open.pRank p (⊤ : Subgroup (A × A')) := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup A)
  obtain ⟨F, -, hF, hFc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup A')
  have hEF : IsElemAbelian p (E.prod F) := by
    have h1 := hE.1
    have h2 := hF.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have e1 := congrArg Subtype.val (mul_comm' (⟨a.1.1, a.2.1⟩ : E) ⟨b.1.1, b.2.1⟩)
      have e2 := congrArg Subtype.val (mul_comm' (⟨a.1.2, a.2.2⟩ : F) ⟨b.1.2, b.2.2⟩)
      exact Prod.ext e1 e2
    · exact Prod.ext (hE.2 x.1 hx.1) (hF.2 x.2 hx.2)
  have hcard : Nat.card (E.prod F) =
      p ^ (CFSG.Open.pRank p (⊤ : Subgroup A) + CFSG.Open.pRank p (⊤ : Subgroup A')) := by
    rw [card_subgroup_prod, hEc, hFc, pow_add]
  exact CFSG.SectionRank.le_pRank hp le_top hEF hcard

theorem one_le_pRank_of_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p) {g : G}
    (hg : orderOf g = p) : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have hpow : ∀ s : Subgroup.zpowers g, s ^ p = 1 := by
    rintro ⟨s, k, rfl⟩
    refine Subtype.ext ?_
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
      one_zpow]
  have hcomm : ∀ s t : Subgroup.zpowers g, s * t = t * s := by
    rintro ⟨s, k, rfl⟩ ⟨t, l, rfl⟩
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← zpow_add, ← zpow_add, add_comm]
  have hcard : Nat.card (Subgroup.zpowers g) = p ^ 1 := by
    rw [Nat.card_zpowers, hg, pow_one]
  exact CFSG.SectionRank.le_pRank_of_injective hp hcomm hpow hcard (Subgroup.zpowers g).subtype
    (Subgroup.subtype_injective _) le_top

end Prelim

section Block

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

@[expose] noncomputable def blockLE {D C : Submodule K V} (hDC : IsCompl D C) (g : D ≃ₗ[K] D)
    (g' : C ≃ₗ[K] C) : V ≃ₗ[K] V :=
  (LinearEquiv.autCongr (Submodule.prodEquivOfIsCompl D C hDC)) (g.prodCongr g')

theorem blockLE_apply {D C : Submodule K V} (hDC : IsCompl D C) (g : D ≃ₗ[K] D)
    (g' : C ≃ₗ[K] C) (d : D) (c : C) :
    blockLE hDC g g' ((d : V) + (c : V)) = (g d : V) + (g' c : V) := by
  have h : ((d : V) + (c : V)) = Submodule.prodEquivOfIsCompl D C hDC (d, c) := by
    simp [Submodule.coe_prodEquivOfIsCompl']
  rw [h]
  simp [blockLE, Submodule.coe_prodEquivOfIsCompl']

theorem blockLE_mul {D C : Submodule K V} (hDC : IsCompl D C) (g₁ g₂ : D ≃ₗ[K] D)
    (g₁' g₂' : C ≃ₗ[K] C) :
    blockLE hDC (g₁ * g₂) (g₁' * g₂') = blockLE hDC g₁ g₁' * blockLE hDC g₂ g₂' := by
  ext v
  obtain ⟨⟨d, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective v
  simp only [Submodule.coe_prodEquivOfIsCompl', LinearEquiv.mul_apply]
  rw [blockLE_apply, blockLE_apply, blockLE_apply]
  rfl

theorem blockLE_one {D C : Submodule K V} (hDC : IsCompl D C) :
    blockLE hDC (1 : D ≃ₗ[K] D) (1 : C ≃ₗ[K] C) = 1 := by
  ext v
  obtain ⟨⟨d, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective v
  simp only [Submodule.coe_prodEquivOfIsCompl']
  rw [blockLE_apply]
  rfl

theorem blockLE_injective {D C : Submodule K V} (hDC : IsCompl D C) {g h : D ≃ₗ[K] D}
    {g' h' : C ≃ₗ[K] C} (hgh : blockLE hDC g g' = blockLE hDC h h') : g = h ∧ g' = h' := by
  constructor
  · ext d
    have := congrArg (fun F : V ≃ₗ[K] V => F ((d : V) + ((0 : C) : V))) hgh
    rw [blockLE_apply, blockLE_apply] at this
    simpa using this
  · ext c
    have := congrArg (fun F : V ≃ₗ[K] V => F (((0 : D) : V) + (c : V))) hgh
    rw [blockLE_apply, blockLE_apply] at this
    simpa using this

theorem blockLE_mem {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, B d c = 0) (hperp' : ∀ c ∈ C, ∀ d ∈ D, B c d = 0)
    {g : D ≃ₗ[K] D} (hg : g ∈ TauCeti.BilinForm.isometryGroup (B.restrict D))
    {g' : C ≃ₗ[K] C} (hg' : g' ∈ TauCeti.BilinForm.isometryGroup (B.restrict C)) :
    blockLE hDC g g' ∈ TauCeti.BilinForm.isometryGroup B := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff] at hg hg' ⊢
  intro u v
  obtain ⟨⟨d₁, c₁⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective u
  obtain ⟨⟨d₂, c₂⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective v
  simp only [Submodule.coe_prodEquivOfIsCompl']
  rw [blockLE_apply, blockLE_apply]
  have h1 := hg d₁ d₂
  have h2 := hg' c₁ c₂
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h1 h2
  simp only [map_add, LinearMap.add_apply]
  rw [hperp _ (g d₁).2 _ (g' c₂).2, hperp' _ (g' c₁).2 _ (g d₂).2, hperp _ d₁.2 _ c₂.2,
    hperp' _ c₁.2 _ d₂.2, h1, h2]

@[expose] noncomputable def blockHom {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, B d c = 0) (hperp' : ∀ c ∈ C, ∀ d ∈ D, B c d = 0) :
    TauCeti.BilinForm.isometryGroup (B.restrict D) ×
      TauCeti.BilinForm.isometryGroup (B.restrict C) →* TauCeti.BilinForm.isometryGroup B where
  toFun gg := ⟨blockLE hDC gg.1 gg.2, blockLE_mem hDC hperp hperp' gg.1.2 gg.2.2⟩
  map_one' := Subtype.ext (blockLE_one hDC)
  map_mul' a b := Subtype.ext (blockLE_mul hDC _ _ _ _)

theorem blockHom_coe {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, B d c = 0) (hperp' : ∀ c ∈ C, ∀ d ∈ D, B c d = 0)
    (gg : TauCeti.BilinForm.isometryGroup (B.restrict D) ×
      TauCeti.BilinForm.isometryGroup (B.restrict C)) :
    ((blockHom hDC hperp hperp' gg : TauCeti.BilinForm.isometryGroup B) : V ≃ₗ[K] V) =
      blockLE hDC gg.1 gg.2 := rfl

theorem blockHom_injective {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, B d c = 0) (hperp' : ∀ c ∈ C, ∀ d ∈ D, B c d = 0) :
    Function.Injective (blockHom hDC hperp hperp') := by
  intro a b h
  have h1 := congrArg (fun x : TauCeti.BilinForm.isometryGroup B => (x : V ≃ₗ[K] V)) h
  obtain ⟨e1, e2⟩ := blockLE_injective hDC h1
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

theorem inv_apply_mem_of_pow_eq_one (y : V ≃ₗ[K] V) {p : ℕ} (hp : 0 < p) (hyp : y ^ p = 1)
    {W : Submodule K V} (hW : ∀ x ∈ W, y x ∈ W) : ∀ x ∈ W, y⁻¹ x ∈ W := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hinv : y⁻¹ = y ^ n := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', hyp]
  have hpow : ∀ m : ℕ, ∀ x ∈ W, (y ^ m) x ∈ W := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hW _ (ih x hx)
  intro x hx
  rw [hinv]
  exact hpow n x hx

@[expose] noncomputable def restrictIso (y : TauCeti.BilinForm.isometryGroup B) (W : Submodule K V)
    (hW : ∀ x ∈ W, (y : V ≃ₗ[K] V) x ∈ W) (hW' : ∀ x ∈ W, (y : V ≃ₗ[K] V)⁻¹ x ∈ W) :
    TauCeti.BilinForm.isometryGroup (B.restrict W) :=
  ⟨LinearEquiv.ofSubmodules (y : V ≃ₗ[K] V) W W
      (le_antisymm (Submodule.map_le_iff_le_comap.2 hW)
        (fun x hx => ⟨(y : V ≃ₗ[K] V)⁻¹ x, hW' x hx, (y : V ≃ₗ[K] V).apply_symm_apply x⟩)),
    by
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      intro u v
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearEquiv.ofSubmodules_apply]
      exact TauCeti.BilinForm.mem_isometryGroup_iff.1 y.2 u v⟩

theorem restrictIso_apply (y : TauCeti.BilinForm.isometryGroup B) (W : Submodule K V)
    (hW : ∀ x ∈ W, (y : V ≃ₗ[K] V) x ∈ W) (hW' : ∀ x ∈ W, (y : V ≃ₗ[K] V)⁻¹ x ∈ W) (x : W) :
    (((restrictIso y W hW hW' : TauCeti.BilinForm.isometryGroup (B.restrict W)) :
      W ≃ₗ[K] W) x : V) = (y : V ≃ₗ[K] V) x := rfl

theorem blockHom_restrictIso {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, B d c = 0) (hperp' : ∀ c ∈ C, ∀ d ∈ D, B c d = 0)
    (y : TauCeti.BilinForm.isometryGroup B) (hD : ∀ x ∈ D, (y : V ≃ₗ[K] V) x ∈ D)
    (hD' : ∀ x ∈ D, (y : V ≃ₗ[K] V)⁻¹ x ∈ D) (hC : ∀ x ∈ C, (y : V ≃ₗ[K] V) x ∈ C)
    (hC' : ∀ x ∈ C, (y : V ≃ₗ[K] V)⁻¹ x ∈ C) :
    blockHom hDC hperp hperp' (restrictIso y D hD hD', restrictIso y C hC hC') = y := by
  refine Subtype.ext ?_
  rw [blockHom_coe]
  ext v
  obtain ⟨⟨d, c⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl D C hDC).surjective v
  simp only [Submodule.coe_prodEquivOfIsCompl']
  rw [blockLE_apply, map_add]
  rfl

end Block

section Rank

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
  {B : BilinForm K V} {p : ℕ} [hp : Fact p.Prime]

theorem pRank_centralizer_le_block {D C : Submodule K V} (hDC : IsCompl D C)
    (hperp : ∀ d ∈ D, ∀ c ∈ C, B d c = 0) (hperp' : ∀ c ∈ C, ∀ d ∈ D, B c d = 0)
    (y : TauCeti.BilinForm.isometryGroup B) (yD : TauCeti.BilinForm.isometryGroup (B.restrict D))
    (yC : TauCeti.BilinForm.isometryGroup (B.restrict C))
    (hy : blockHom hDC hperp hperp' (yD, yC) = y) :
    CFSG.Open.pRank p (centralizer ({yD} : Set (TauCeti.BilinForm.isometryGroup (B.restrict D)))) ≤
      CFSG.Open.pRank p (centralizer ({y} : Set (TauCeti.BilinForm.isometryGroup B))) := by
  let ι := (blockHom hDC hperp hperp').comp
    (MonoidHom.inl (TauCeti.BilinForm.isometryGroup (B.restrict D))
      (TauCeti.BilinForm.isometryGroup (B.restrict C)))
  have hι : Function.Injective ι :=
    (blockHom_injective hDC hperp hperp').comp (fun a b h => (Prod.ext_iff.1 h).1)
  refine (CFSG.SectionRank.pRank_le_map hp.out.one_lt ι hι _).trans
    (CFSG.SectionRank.pRank_mono hp.out.one_lt ?_)
  rintro _ ⟨g, hg, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
  rw [Subgroup.mem_centralizer_singleton_iff, ← hy]
  simp only [ι, MonoidHom.comp_apply, MonoidHom.inl_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext hg (by simp)

theorem exists_nondeg_subspace_alt (hB : B.IsAlt) (hnd : B.Nondegenerate) {m : ℕ}
    (hm : 2 * m ≤ Module.finrank K V) :
    ∃ D : Submodule K V, Disjoint D (B.orthogonal D) ∧ Module.finrank K D = 2 * m := by
  have hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ 1 - 1 → f.natDegree ≤ 1 := by
    intro f hf hdvd
    have h1 : (X ^ 1 - 1 : K[X]) = X - C 1 := by simp
    rw [h1] at hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd (X_sub_C_ne_zero (1 : K))
    rwa [natDegree_X_sub_C] at this
  obtain ⟨W, -, hWd, hW1, hW2⟩ := exists_nondeg_window (y := (1 : Module.End K V)) (p := 1)
    (e := 1) (c := 2 * m) (by simp) (by simp) one_pos one_pos hdeg hB.isRefl hnd
    (fun u v => rfl) (by simpa using hm)
  have hWalt : (B.restrict W).IsAlt := fun z => hB.self_eq_zero z
  have hWnd : (B.restrict W).Nondegenerate :=
    B.nondegenerate_restrict_of_disjoint_orthogonal hB.isRefl hWd
  obtain ⟨t, ht⟩ := LinearMap.BilinForm.IsAlt.even_finrank hWalt hWnd
  refine ⟨W, hWd, ?_⟩
  omega

theorem exists_orderOf_isometry {e : ℕ} (he : 0 < e) (hee : Even e)
    (hpe : p ∣ Nat.card K ^ e - 1) {D : Type} [AddCommGroup D] [Module K D] [Module.Finite K D]
    (BD : BilinForm K D) (hB : BD.IsAlt) (hnd : BD.Nondegenerate) (hD : Module.finrank K D = e) :
    ∃ g : TauCeti.BilinForm.isometryGroup BD, orderOf g = p := by
  obtain ⟨m, hm⟩ := hee
  have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup m BD hB hnd
    (by omega)
  have hdvd : p ∣ Nat.card (TauCeti.BilinForm.isometryGroup BD) := by
    rw [hcard]
    refine Dvd.dvd.mul_left ?_ _
    have hm0 : 1 ≤ m := by omega
    have h2 : p ∣ Nat.card K ^ (2 * m) - 1 := by
      rw [show 2 * m = e by omega]
      exact hpe
    exact h2.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ (2 * j) - 1)
      (Finset.mem_Icc.2 ⟨hm0, le_rfl⟩))
  exact exists_prime_orderOf_dvd_card' p hdvd

end Rank

section Main

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem le_pRank_isometryGroup {e : ℕ} (he : 0 < e) (hee : Even e)
    (hpe : p ∣ Nat.card K ^ e - 1) :
    ∀ (k : ℕ) {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V] (B : BilinForm K V),
      B.IsAlt → B.Nondegenerate → k * e ≤ Module.finrank K V →
      k ≤ CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.BilinForm.isometryGroup B)) := by
  intro k
  induction k with
  | zero => intros; exact Nat.zero_le _
  | succ k ih =>
    intro V _ _ _ B hB hnd hk
    have hk' : (k + 1) * e = k * e + e := by ring
    obtain ⟨m, hm⟩ := hee
    obtain ⟨D, hDd, hDdim⟩ := exists_nondeg_subspace_alt hB hnd (m := m) (by omega)
    have hrefl := hB.isRefl
    have hDC : IsCompl D (B.orthogonal D) :=
      (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 hDd
    have hperp : ∀ d ∈ D, ∀ c ∈ B.orthogonal D, B d c = 0 := fun d hd c hc =>
      LinearMap.BilinForm.mem_orthogonal_iff.1 hc d hd
    have hperp' : ∀ c ∈ B.orthogonal D, ∀ d ∈ D, B c d = 0 := fun c hc d hd =>
      hrefl _ _ (hperp d hd c hc)
    have hDalt : (B.restrict D).IsAlt := fun z => hB.self_eq_zero z
    have hDnd : (B.restrict D).Nondegenerate :=
      B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hDd
    have hCd : Disjoint (B.orthogonal D) (B.orthogonal (B.orthogonal D)) := by
      rw [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
      exact hDd.symm
    have hCalt : (B.restrict (B.orthogonal D)).IsAlt := fun z => hB.self_eq_zero z
    have hCnd : (B.restrict (B.orthogonal D)).Nondegenerate :=
      B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hCd
    have hdimC := LinearMap.BilinForm.finrank_orthogonal hnd D
    have hCrank := ih (B.restrict (B.orthogonal D)) hCalt hCnd (by omega)
    obtain ⟨g, hg⟩ := exists_orderOf_isometry he ⟨m, hm⟩ hpe (B.restrict D) hDalt hDnd (by omega)
    have hDrank := one_le_pRank_of_orderOf hp.out.one_lt hg
    have hprod := pRank_top_prod_ge hp.out.one_lt
      (A := TauCeti.BilinForm.isometryGroup (B.restrict D))
      (A' := TauCeti.BilinForm.isometryGroup (B.restrict (B.orthogonal D)))
    have hinj := CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt
      (blockHom hDC hperp hperp') (blockHom_injective hDC hperp hperp')
    omega

theorem isMulCommutative_of_isPGroup_isometry (hp2 : Odd p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) {W : Type} [AddCommGroup W]
    [Module K W] [Module.Finite K W] (BW : BilinForm K W) (hne : Module.finrank K W / e < p)
    {P : Subgroup (TauCeti.BilinForm.isometryGroup BW)} (hP : IsPGroup p P) :
    IsMulCommutative P := by
  let ψ : TauCeti.BilinForm.isometryGroup BW →* (Module.End K W)ˣ :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.toMonoidHom).comp
      (Subgroup.subtype _)
  have hψ : Function.Injective ψ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.injective.comp
      (Subgroup.subtype_injective _)
  exact isMulCommutative_of_map_injective ψ hψ
    (isMulCommutative_of_isPGroup_GL hp2 hpK he hpe hne (hP.map ψ))

theorem three_le_pRank_centralizer_isometry (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hee : Even e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V] (B : BilinForm K V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (h3 : 3 * e ≤ Module.finrank K V)
    (y : TauCeti.BilinForm.isometryGroup B) (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (TauCeti.BilinForm.isometryGroup B))) := by
  have hp2 : Odd p := hp.out.odd_of_ne_two (by omega)
  have hp0 := natCast_ne_zero_of_not_dvd_card hp.out hpK
  have hrefl := hB.isRefl
  set yL : V ≃ₗ[K] V := (y : V ≃ₗ[K] V) with hyL
  have hyLp : yL ^ p = 1 := by
    have := congrArg (fun x : TauCeti.BilinForm.isometryGroup B => (x : V ≃ₗ[K] V)) hy
    simpa using this
  let yE : Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom yL
  have hyEp : yE ^ p = 1 := by
    rw [← map_pow, hyLp, map_one]
  have hyB : ∀ u v, B (yE u) (yE v) = B u v := fun u v =>
    TauCeti.BilinForm.mem_isometryGroup_iff.1 y.2 u v
  have hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e :=
    fun f hf hfP => natDegree_le_of_dvd_X_pow_sub_one he ((hpe e).2 dvd_rfl) hf hfP
  obtain ⟨W, hWinv, hWd, hW3, hW5⟩ :=
    exists_nondeg_window (c := 3) hyEp hp0 hp.out.pos he hdeg hrefl hnd hyB h3
  have hCinv : ∀ x ∈ B.orthogonal W, yE x ∈ B.orthogonal W :=
    orthogonal_invt hp.out.pos hyEp hyB hWinv
  have hWinv' : ∀ x ∈ W, yL⁻¹ x ∈ W := inv_apply_mem_of_pow_eq_one yL hp.out.pos hyLp hWinv
  have hCinv' : ∀ x ∈ B.orthogonal W, yL⁻¹ x ∈ B.orthogonal W :=
    inv_apply_mem_of_pow_eq_one yL hp.out.pos hyLp hCinv
  have hWC : IsCompl W (B.orthogonal W) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 hWd
  have hperp : ∀ d ∈ W, ∀ c ∈ B.orthogonal W, B d c = 0 := fun d hd c hc =>
    LinearMap.BilinForm.mem_orthogonal_iff.1 hc d hd
  have hperp' : ∀ c ∈ B.orthogonal W, ∀ d ∈ W, B c d = 0 := fun c hc d hd =>
    hrefl _ _ (hperp d hd c hc)
  let yW := restrictIso y W hWinv hWinv'
  let yC := restrictIso y (B.orthogonal W) hCinv hCinv'
  have hblock := blockHom_restrictIso hWC hperp hperp' y hWinv hWinv' hCinv hCinv'
  have hyWp : yW ^ p = 1 := by
    have h1 : blockHom hWC hperp hperp' ((yW, yC) ^ p) = 1 := by rw [map_pow, hblock, hy]
    have h2 := blockHom_injective hWC hperp hperp' (h1.trans (map_one _).symm)
    simpa using congrArg Prod.fst h2
  have hWalt : (B.restrict W).IsAlt := fun z => hB.self_eq_zero z
  have hWnd : (B.restrict W).Nondegenerate :=
    B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hWd
  have hne : Module.finrank K W / e < p := by
    refine lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul he).2 ?_) hp5
    have h5 : (3 + 2) * e = 5 * e := by ring
    omega
  have hab : ∀ P : Sylow p (TauCeti.BilinForm.isometryGroup (B.restrict W)),
      IsMulCommutative (P : Subgroup _) := fun P =>
    isMulCommutative_of_isPGroup_isometry hp2 hpK he hpe (B.restrict W) hne P.isPGroup'
  have hrank := le_pRank_isometryGroup he hee ((hpe e).2 dvd_rfl) 3 (B.restrict W) hWalt hWnd hW3
  exact (le_pRank_centralizer_of_sylow_abelian hab hrank hyWp).trans
    (pRank_centralizer_le_block hWC hperp hperp' y yW yC hblock)

end Main



end CFSG.LocalAnalysis.RankFourTheoremC.BCDEven
