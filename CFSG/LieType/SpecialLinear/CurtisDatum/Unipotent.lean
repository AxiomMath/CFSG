module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.LieType.Steinberg.PartBHalfSpace
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
open CFSG.LieType.Universal.SpecialLinear
open CFSG.StandardType.GGRootSL

variable {m : ℕ}

abbrev UpperPair (m : ℕ) := {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}

abbrev LowerPair (m : ℕ) := {p : Fin (m + 1) × Fin (m + 1) // p.2 < p.1}

theorem exists_pos_root_pair (m : ℕ) {i j : Fin (m + 1)} (hij : i < j) :
    ∃ γ : Fin m → ℤ, γ ∈ roots (isFiniteType_A m) ∅ ∧
      toStd m γ = Pi.single i 1 - Pi.single j 1 ∧ 0 < ht γ := by
  have hm : 0 < m := by omega
  let z : Fin (m + 1) := 0
  let o : Fin (m + 1) := ⟨1, by omega⟩
  let σ : Equiv.Perm (Fin (m + 1)) := (Equiv.swap i z).trans (Equiv.swap j o)
  have hzj : z ≠ j := by
    intro h
    have h' : (j : ℕ) = 0 := by rw [← h]; rfl
    omega
  have hzo : z ≠ o := by
    intro h
    have h' : (o : ℕ) = 0 := by rw [← congrArg Fin.val h]; rfl
    simp [o] at h'
  have hσi : σ i = z := by
    simp only [σ, Equiv.trans_apply, z]
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hzj hzo
  have hσj : σ j = o := by
    simp only [σ, Equiv.trans_apply]
    have h1 : j ≠ i := hij.ne'
    have h2 : j ≠ z := by simp [z]; omega
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_left]
  let k0 : Fin m := ⟨0, hm⟩
  let w : (coxeterMatrix (isFiniteType_A m)).Group := CFSG.StandardType.typeAWeylEquiv m σ
  have hreal : CFSG.StandardType.TypeARealizes m w σ :=
    CFSG.StandardType.typeAWeylOf_spec m σ
  let γ : Fin m → ℤ := weylAction (isFiniteType_A m) w⁻¹ (Pi.single k0 1)
  have hkc : k0.castSucc = (0 : Fin (m + 1)) := Fin.ext (by simp [k0])
  have hks : k0.succ = o := Fin.ext (by simp [k0, o])
  have hstd : toStd m γ = Pi.single i 1 - Pi.single j 1 := by
    funext b
    have hb := congrFun (hreal γ) (σ b)
    dsimp only [γ] at hb
    rw [weylAction_apply_inv_apply, Equiv.symm_apply_apply] at hb
    rw [← hb]
    by_cases hbi : b = i
    · subst hbi
      rw [hσi, toStd_single, hkc, hks]
      simp [z, o, hij.ne]
    · by_cases hbj : b = j
      · subst hbj
        rw [hσj, toStd_single, hkc, hks]
        simp [o, hij.ne', ]
      · have hσ0 : σ b ≠ z := by
          intro h
          apply hbi
          apply σ.injective
          rw [h, hσi]
        have hσ1 : σ b ≠ o := by
          intro h
          apply hbj
          apply σ.injective
          rw [h, hσj]
        rw [toStd_single, hkc, hks]
        simp only [Pi.sub_apply, Pi.single_apply]
        have h1 : σ b ≠ (0 : Fin (m + 1)) := hσ0
        have h2 : σ b ≠ (⟨1, by omega⟩ : Fin (m + 1)) := hσ1
        rw [if_neg h1, if_neg h2]
        simp [hbi, hbj]
  refine ⟨γ, ?_, hstd, ?_⟩
  · rw [roots_eq]
    exact ⟨i, j, hij.ne, hstd⟩
  · rw [ht_eq m hstd]
    exact sub_pos.mpr (by exact_mod_cast hij)

theorem exists_neg_root_pair (m : ℕ) {i j : Fin (m + 1)} (hji : j < i) :
    ∃ γ : Fin m → ℤ, γ ∈ roots (isFiniteType_A m) ∅ ∧
      toStd m γ = Pi.single i 1 - Pi.single j 1 ∧ ht γ < 0 := by
  obtain ⟨γ, hγ, hstd, hpos⟩ := exists_pos_root_pair m hji
  refine ⟨-γ, (RootSystem.ofCartan (isFiniteType_A m) ∅).neg_mem γ hγ, ?_, ?_⟩
  · rw [toStd_neg, hstd, neg_sub]
  · rw [ht_neg]
    omega

theorem exists_root_pair (m : ℕ) {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ γ : Fin m → ℤ, γ ∈ roots (isFiniteType_A m) ∅ ∧
      toStd m γ = Pi.single i 1 - Pi.single j 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (exists_pos_root_pair m h).imp (fun γ h => ⟨h.1, h.2.1⟩)
  · exact (exists_neg_root_pair m h).imp (fun γ h => ⟨h.1, h.2.1⟩)

noncomputable def posRootEquiv (m : ℕ) (S : Set (Fin m → ℤ))
    (hmem : ∀ γ, γ ∈ S ↔ γ ∈ roots (isFiniteType_A m) ∅ ∧ 0 < ht γ) :
    ↥S ≃ UpperPair m :=
  Equiv.ofBijective
    (fun γ => ⟨((idx m γ.1).1, (idx m γ.1).2), by
      have hγ := (hmem γ.1).1 γ.2
      have hh := hγ.2
      rw [ht_eq_idx m hγ.1] at hh
      exact_mod_cast (by omega : ((idx m γ.1).1 : ℤ) < (idx m γ.1).2)⟩)
    ⟨fun a b hab => by
      apply Subtype.ext
      have ha := (hmem a.1).1 a.2
      have hb := (hmem b.1).1 b.2
      have hidx : ((idx m a.1).1, (idx m a.1).2) = ((idx m b.1).1, (idx m b.1).2) :=
        congrArg Subtype.val hab
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hidx
      exact idx_injective m ha.1 hb.1 h1 h2,
     fun p => by
      obtain ⟨γ, hγ, hstd⟩ := exists_root_pair m p.2.ne
      have hpos : γ ∈ S := (hmem γ).2 ⟨hγ, by
        rw [ht_eq m hstd]
        have : ((p.1.1 : ℕ) : ℤ) < ((p.1.2 : ℕ) : ℤ) := by exact_mod_cast p.2
        omega⟩
      refine ⟨⟨γ, hpos⟩, ?_⟩
      have hidx := idx_spec m hγ
      have heq : (Pi.single (idx m γ).1 1 - Pi.single (idx m γ).2 1 : Fin (m + 1) → ℤ) =
          Pi.single p.1.1 1 - Pi.single p.1.2 1 := by
        rw [← hidx.2]
        simpa using hstd
      have h := CFSG.LieType.Steinberg.SL.single_sub_single_inj (i := (idx m γ).1)
        (j := (idx m γ).2) (i' := p.1.1) (j' := p.1.2) hidx.1 heq
      exact Subtype.ext (Prod.ext h.1 h.2)⟩


theorem card_le_posUnipotent (F : Type) [Field F] [Finite F] :
    Nat.card F ^ Nat.card (UpperPair m) ≤
      Nat.card (posUnipotent (rootDatum m F)) := by
  classical
  let S : Set (Fin m → ℤ) := {γ | γ ∈ roots (isFiniteType_A m) ∅ ∧ 0 < ht γ}
  have hSfin : S.Finite :=
    ((RootSystem.ofCartan (isFiniteType_A m) ∅).finite_roots).subset (fun x h => h.1)
  obtain ⟨L, hL, hmem, hsort⟩ := exists_sorted_list hSfin (fun γ => ht γ)
  have hroot : ∀ γ ∈ L, γ ∈ roots (isFiniteType_A m) ∅ := fun γ h => ((hmem γ).1 h).1
  have hpos : ∀ γ ∈ L, 0 < ht γ := fun γ h => ((hmem γ).1 h).2
  have hlev : ∀ γ ∈ L, (1 : ℤ) ≤ ((idx m γ).2 : ℤ) - ((idx m γ).1 : ℤ) := by
    intro γ hγ
    have hh := hpos γ hγ
    rw [ht_eq_idx m (hroot γ hγ)] at hh
    omega
  have hsort' : L.Pairwise (fun γ δ =>
      ((idx m γ).2 : ℤ) - ((idx m γ).1 : ℤ) ≤
        ((idx m δ).2 : ℤ) - ((idx m δ).1 : ℤ)) :=
    hsort.imp_of_mem (fun {γ δ} hγ hδ hle => by
      rw [← ht_eq_idx m (hroot γ hγ), ← ht_eq_idx m (hroot δ hδ)]
      exact hle)
  let e₁ : {γ // γ ∈ L} ≃ ↥S := Equiv.subtypeEquiv (Equiv.refl _) (fun γ => hmem γ)
  let e₂ : ↥S ≃ UpperPair m := posRootEquiv m S (fun γ => Iff.rfl)
  let e : {γ // γ ∈ L} ≃ UpperPair m := e₁.trans e₂
  let toU : ({γ // γ ∈ L} → F) → posUnipotent (rootDatum m F) := fun c =>
    ⟨(L.map fun γ => if h : γ ∈ L then
        SpecialLinearGroup.transvection (idx_spec m (hroot γ h)).1 (c ⟨γ, h⟩) else 1).prod, by
      apply Subgroup.list_prod_mem
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨γ, hγ, rfl⟩ := hx
      rw [dif_pos hγ]
      have hmemroot : SpecialLinearGroup.transvection (idx_spec m (hroot γ hγ)).1
          (c ⟨γ, hγ⟩) ∈ rootGroup m F γ := by
        rw [rootGroup_eq_idx m F (hroot γ hγ)]
        exact transvection_mem_rootSubgroup (idx_spec m (hroot γ hγ)).1 _
      exact rootGroup_le_posUnipotent (hroot γ hγ) (hpos γ hγ) hmemroot⟩
  have hinj : Function.Injective toU := by
    intro c d hcd
    have hE := prodInjective_of (m := m) (F := F) (fun a : Fin (m + 1) => (a : ℤ))
      L hL hroot hlev hsort'
    let f : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F := fun γ =>
      if h : γ ∈ L then SpecialLinearGroup.transvection (idx_spec m (hroot γ h)).1 (c ⟨γ, h⟩) else 1
    let g : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F := fun γ =>
      if h : γ ∈ L then SpecialLinearGroup.transvection (idx_spec m (hroot γ h)).1 (d ⟨γ, h⟩) else 1
    have hf : ∀ γ ∈ L, f γ ∈ rootGroup m F γ := by
      intro γ hγ
      rw [show f γ = SpecialLinearGroup.transvection (idx_spec m (hroot γ hγ)).1 (c ⟨γ, hγ⟩) from by
        simp only [f, dif_pos hγ]]
      rw [rootGroup_eq_idx m F (hroot γ hγ)]
      exact transvection_mem_rootSubgroup (idx_spec m (hroot γ hγ)).1 _
    have hg : ∀ γ ∈ L, g γ ∈ rootGroup m F γ := by
      intro γ hγ
      rw [show g γ = SpecialLinearGroup.transvection (idx_spec m (hroot γ hγ)).1 (d ⟨γ, hγ⟩) from by
        simp only [g, dif_pos hγ]]
      rw [rootGroup_eq_idx m F (hroot γ hγ)]
      exact transvection_mem_rootSubgroup (idx_spec m (hroot γ hγ)).1 _
    have hprod : (L.map f).prod = (L.map g).prod := by
      have := congrArg Subtype.val hcd
      simpa only [toU, f, g] using this
    have hfg := hE f g hf hg hprod
    funext γ
    have hγ := hfg γ.1 γ.2
    have hc : c γ = d γ := by
      apply SpecialLinearGroup.transvection_injective (idx_spec m (hroot γ.1 γ.2)).1
      simpa only [f, g, dif_pos γ.2] using hγ
    exact hc
  have hcard := Nat.card_le_card_of_injective toU hinj
  rwa [Nat.card_fun, Nat.card_congr e] at hcard


theorem card_posUnipotent_le (F : Type) [Field F] [Finite F] :
    Nat.card (posUnipotent (rootDatum m F)) ≤
      Nat.card F ^ Nat.card (UpperPair m) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let entry : posUnipotent (rootDatum m F) → (UpperPair m → F) := fun u p =>
    (u.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2
  have hinj : Function.Injective entry := by
    intro u v huv
    apply Subtype.ext
    ext a b
    have hu := upperUni_of_mem_posUnipotent u.2
    have hv := upperUni_of_mem_posUnipotent v.2
    rcases lt_trichotomy a b with h | h | h
    · have hc := congrFun huv ⟨(a, b), h⟩
      simpa [entry] using hc
    · subst h
      rw [hu.2 a, hv.2 a]
    · rw [hu.1 a b h, hv.1 a b h]
  have hcard := Nat.card_le_card_of_injective entry hinj
  rwa [Nat.card_fun] at hcard

theorem card_posUnipotent (F : Type) [Field F] [Finite F] :
    Nat.card (posUnipotent (rootDatum m F)) = Nat.card F ^ Nat.card (UpperPair m) :=
  le_antisymm (card_posUnipotent_le (m := m) F) (card_le_posUnipotent (m := m) F)

theorem card_upperUnitriangular_le (F : Type) [Field F] [Finite F] :
    Nat.card {x : SpecialLinearGroup (Fin (m + 1)) F //
        UpperT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
          ∀ i, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1} ≤
      Nat.card F ^ Nat.card (UpperPair m) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let entry : {x : SpecialLinearGroup (Fin (m + 1)) F //
      UpperT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1} →
      (UpperPair m → F) := fun x p =>
    (x.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2
  have hinj : Function.Injective entry := by
    intro x y hxy
    apply Subtype.ext
    ext a b
    rcases lt_trichotomy a b with h | h | h
    · have hc := congrFun hxy ⟨(a, b), h⟩
      simpa [entry] using hc
    · subst h
      rw [x.2.2 a, y.2.2 a]
    · rw [x.2.1 a b h, y.2.1 a b h]
  have hcard := Nat.card_le_card_of_injective entry hinj
  rwa [Nat.card_fun] at hcard

theorem mem_posUnipotent_iff (F : Type) [Field F] [Finite F]
    {x : SpecialLinearGroup (Fin (m + 1)) F} :
    x ∈ posUnipotent (rootDatum m F) ↔
      UpperT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1 := by
  constructor
  · exact upperUni_of_mem_posUnipotent
  · intro hx
    let S : Set (SpecialLinearGroup (Fin (m + 1)) F) :=
      {y | UpperT (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1}
    have hsub : (↑(posUnipotent (rootDatum m F)) : Set (SpecialLinearGroup (Fin (m + 1)) F)) ⊆ S :=
      fun y hy => upperUni_of_mem_posUnipotent hy
    have hle : Nat.card S ≤ Nat.card (posUnipotent (rootDatum m F)) := by
      rw [card_posUnipotent (m := m) F]
      exact card_upperUnitriangular_le (m := m) F
    have hset : (↑(posUnipotent (rootDatum m F)) : Set (SpecialLinearGroup (Fin (m + 1)) F)) = S := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [← Nat.card_coe_set_eq S, ← Nat.card_coe_set_eq (↑(posUnipotent (rootDatum m F)) : Set (SpecialLinearGroup (Fin (m + 1)) F))]
      exact hle
    change x ∈ S at hx
    rw [← hset] at hx
    exact hx



noncomputable def negRootEquiv (S : Set (Fin m → ℤ))
    (hmem : ∀ γ, γ ∈ S ↔ γ ∈ roots (isFiniteType_A m) ∅ ∧ ht γ < 0) :
    ↥S ≃ LowerPair m :=
  Equiv.ofBijective
    (fun γ => ⟨((idx m γ.1).1, (idx m γ.1).2), by
      have hγ := (hmem γ.1).1 γ.2
      have hh := hγ.2
      rw [ht_eq_idx m hγ.1] at hh
      exact_mod_cast (by omega : ((idx m γ.1).2 : ℤ) < (idx m γ.1).1)⟩)
    ⟨fun a b hab => by
      apply Subtype.ext
      have ha := (hmem a.1).1 a.2
      have hb := (hmem b.1).1 b.2
      have hidx : ((idx m a.1).1, (idx m a.1).2) = ((idx m b.1).1, (idx m b.1).2) :=
        congrArg Subtype.val hab
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hidx
      exact idx_injective m ha.1 hb.1 h1 h2,
     fun p => by
      obtain ⟨γ, hγ, hstd, hlt⟩ := exists_neg_root_pair m p.2
      have hneg : γ ∈ S := (hmem γ).2 ⟨hγ, by
        rw [ht_eq m hstd]
        have : ((p.1.2 : ℕ) : ℤ) < ((p.1.1 : ℕ) : ℤ) := by exact_mod_cast p.2
        omega⟩
      refine ⟨⟨γ, hneg⟩, ?_⟩
      have hidx := idx_spec m hγ
      have heq : (Pi.single (idx m γ).1 1 - Pi.single (idx m γ).2 1 : Fin (m + 1) → ℤ) =
          Pi.single p.1.1 1 - Pi.single p.1.2 1 := by
        rw [← hidx.2]
        simpa using hstd
      have h := CFSG.LieType.Steinberg.SL.single_sub_single_inj (i := (idx m γ).1)
        (j := (idx m γ).2) (i' := p.1.1) (j' := p.1.2) hidx.1 heq
      exact Subtype.ext (Prod.ext h.1 h.2)⟩

theorem card_le_negUnipotent (F : Type) [Field F] [Finite F] :
    Nat.card F ^ Nat.card (LowerPair m) ≤
      Nat.card (negUnipotent (rootDatum m F)) := by
  classical
  let S : Set (Fin m → ℤ) := {γ | γ ∈ roots (isFiniteType_A m) ∅ ∧ ht γ < 0}
  have hSfin : S.Finite :=
    ((RootSystem.ofCartan (isFiniteType_A m) ∅).finite_roots).subset (fun x h => h.1)
  obtain ⟨L, hL, hmem, hsort⟩ := exists_sorted_list hSfin (fun γ => -ht γ)
  have hroot : ∀ γ ∈ L, γ ∈ roots (isFiniteType_A m) ∅ := fun γ h => ((hmem γ).1 h).1
  have hneg : ∀ γ ∈ L, ht γ < 0 := fun γ h => ((hmem γ).1 h).2
  let s : Fin (m + 1) → ℤ := fun a => -((a : ℤ))
  have hlev : ∀ γ ∈ L, (1 : ℤ) ≤ s (idx m γ).2 - s (idx m γ).1 := by
    intro γ hγ
    have hh := hneg γ hγ
    rw [ht_eq_idx m (hroot γ hγ)] at hh
    simp only [s]
    omega
  have hsort' : L.Pairwise (fun γ δ =>
      s (idx m γ).2 - s (idx m γ).1 ≤ s (idx m δ).2 - s (idx m δ).1) :=
    hsort.imp_of_mem (fun {γ δ} hγ hδ hle => by
      have hle' : ((idx m γ).1 : ℤ) - ((idx m γ).2 : ℤ) ≤
          ((idx m δ).1 : ℤ) - ((idx m δ).2 : ℤ) := by
        simpa only [ht_eq_idx m (hroot γ hγ), ht_eq_idx m (hroot δ hδ), neg_sub] using hle
      simp only [s]
      omega)
  let e₁ : {γ // γ ∈ L} ≃ ↥S := Equiv.subtypeEquiv (Equiv.refl _) (fun γ => hmem γ)
  let e₂ : ↥S ≃ LowerPair m := negRootEquiv (m := m) S (fun γ => Iff.rfl)
  let e : {γ // γ ∈ L} ≃ LowerPair m := e₁.trans e₂
  let toU : ({γ // γ ∈ L} → F) → negUnipotent (rootDatum m F) := fun c =>
    ⟨(L.map fun γ => if h : γ ∈ L then
        SpecialLinearGroup.transvection (idx_spec m (hroot γ h)).1 (c ⟨γ, h⟩) else 1).prod, by
      apply Subgroup.list_prod_mem
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨γ, hγ, rfl⟩ := hx
      rw [dif_pos hγ]
      have hmemroot : SpecialLinearGroup.transvection (idx_spec m (hroot γ hγ)).1
          (c ⟨γ, hγ⟩) ∈ rootGroup m F γ := by
        rw [rootGroup_eq_idx m F (hroot γ hγ)]
        exact transvection_mem_rootSubgroup (idx_spec m (hroot γ hγ)).1 _
      exact rootGroup_le_negUnipotent (hroot γ hγ) (hneg γ hγ) hmemroot⟩
  have hinj : Function.Injective toU := by
    intro c d hcd
    have hE := prodInjective_of (m := m) (F := F) s
      L hL hroot hlev hsort'
    let f : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F := fun γ =>
      if h : γ ∈ L then SpecialLinearGroup.transvection (idx_spec m (hroot γ h)).1 (c ⟨γ, h⟩) else 1
    let g : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F := fun γ =>
      if h : γ ∈ L then SpecialLinearGroup.transvection (idx_spec m (hroot γ h)).1 (d ⟨γ, h⟩) else 1
    have hf : ∀ γ ∈ L, f γ ∈ rootGroup m F γ := by
      intro γ hγ
      rw [show f γ = SpecialLinearGroup.transvection (idx_spec m (hroot γ hγ)).1 (c ⟨γ, hγ⟩) from by
        simp only [f, dif_pos hγ]]
      rw [rootGroup_eq_idx m F (hroot γ hγ)]
      exact transvection_mem_rootSubgroup (idx_spec m (hroot γ hγ)).1 _
    have hg : ∀ γ ∈ L, g γ ∈ rootGroup m F γ := by
      intro γ hγ
      rw [show g γ = SpecialLinearGroup.transvection (idx_spec m (hroot γ hγ)).1 (d ⟨γ, hγ⟩) from by
        simp only [g, dif_pos hγ]]
      rw [rootGroup_eq_idx m F (hroot γ hγ)]
      exact transvection_mem_rootSubgroup (idx_spec m (hroot γ hγ)).1 _
    have hprod : (L.map f).prod = (L.map g).prod := by
      have := congrArg Subtype.val hcd
      simpa only [toU, f, g] using this
    have hfg := hE f g hf hg hprod
    funext γ
    have hγ := hfg γ.1 γ.2
    have hc : c γ = d γ := by
      apply SpecialLinearGroup.transvection_injective (idx_spec m (hroot γ.1 γ.2)).1
      simpa only [f, g, dif_pos γ.2] using hγ
    exact hc
  have hcard := Nat.card_le_card_of_injective toU hinj
  rwa [Nat.card_fun, Nat.card_congr e] at hcard

theorem card_negUnipotent_le (F : Type) [Field F] [Finite F] :
    Nat.card (negUnipotent (rootDatum m F)) ≤
      Nat.card F ^ Nat.card (LowerPair m) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let entry : negUnipotent (rootDatum m F) → (LowerPair m → F) := fun u p =>
    (u.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2
  have hinj : Function.Injective entry := by
    intro u v huv
    apply Subtype.ext
    ext a b
    have hu := lowerUni_of_mem_negUnipotent u.2
    have hv := lowerUni_of_mem_negUnipotent v.2
    rcases lt_trichotomy a b with h | h | h
    · rw [hu.1 a b h, hv.1 a b h]
    · subst h
      rw [hu.2 a, hv.2 a]
    · have hc := congrFun huv ⟨(a, b), h⟩
      simpa [entry] using hc
  have hcard := Nat.card_le_card_of_injective entry hinj
  rwa [Nat.card_fun] at hcard

theorem card_negUnipotent (F : Type) [Field F] [Finite F] :
    Nat.card (negUnipotent (rootDatum m F)) = Nat.card F ^ Nat.card (LowerPair m) :=
  le_antisymm (card_negUnipotent_le (m := m) F) (card_le_negUnipotent (m := m) F)

theorem card_lowerUnitriangular_le (F : Type) [Field F] [Finite F] :
    Nat.card {x : SpecialLinearGroup (Fin (m + 1)) F //
        LowerT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
          ∀ i, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1} ≤
      Nat.card F ^ Nat.card (LowerPair m) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let entry : {x : SpecialLinearGroup (Fin (m + 1)) F //
      LowerT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1} →
      (LowerPair m → F) := fun x p =>
    (x.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p.1.1 p.1.2
  have hinj : Function.Injective entry := by
    intro x y hxy
    apply Subtype.ext
    ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [x.2.1 a b h, y.2.1 a b h]
    · subst h
      rw [x.2.2 a, y.2.2 a]
    · have hc := congrFun hxy ⟨(a, b), h⟩
      simpa [entry] using hc
  have hcard := Nat.card_le_card_of_injective entry hinj
  rwa [Nat.card_fun] at hcard

theorem mem_negUnipotent_iff (F : Type) [Field F] [Finite F]
    {x : SpecialLinearGroup (Fin (m + 1)) F} :
    x ∈ negUnipotent (rootDatum m F) ↔
      LowerT (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1 := by
  constructor
  · exact lowerUni_of_mem_negUnipotent
  · intro hx
    let S : Set (SpecialLinearGroup (Fin (m + 1)) F) :=
      {y | LowerT (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
        ∀ i, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1}
    have hsub : (↑(negUnipotent (rootDatum m F)) : Set (SpecialLinearGroup (Fin (m + 1)) F)) ⊆ S :=
      fun y hy => lowerUni_of_mem_negUnipotent hy
    have hle : Nat.card S ≤ Nat.card (negUnipotent (rootDatum m F)) := by
      rw [card_negUnipotent (m := m) F]
      exact card_lowerUnitriangular_le (m := m) F
    have hset : (↑(negUnipotent (rootDatum m F)) : Set (SpecialLinearGroup (Fin (m + 1)) F)) = S := by
      apply Set.eq_of_subset_of_ncard_le hsub
      rw [← Nat.card_coe_set_eq S, ← Nat.card_coe_set_eq (↑(negUnipotent (rootDatum m F)) : Set (SpecialLinearGroup (Fin (m + 1)) F))]
      exact hle
    change x ∈ S at hx
    rw [← hset] at hx
    exact hx


end CFSG.LieType.SpecialLinear

