module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdTheta
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdDiag

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.ClassicalInvolution.ModelFacts.ChevAut CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg

section Tdir

variable {K : Type*} [Group K] {F : Type} [Field F] {r : ℕ} {x : (Fin r → ℤ) → F → K}

@[expose] def tdir (x : (Fin r → ℤ) → F → K) (c : Fin r → ℤ) (s : Fˣ) : K :=
  ((List.finRange r).map fun j => torusGen x j (s ^ c j)).prod

@[expose] def cpair (A : Matrix (Fin r) (Fin r) ℤ) (c γ : Fin r → ℤ) : ℤ :=
  ∑ j, c j * pair A γ j

theorem cpair_single (A : Matrix (Fin r) (Fin r) ℤ) (j : Fin r) (γ : Fin r → ℤ) :
    cpair A (Pi.single j 1) γ = pair A γ j := by
  simp [cpair, Pi.single_apply]

end Tdir

section Act

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem tact_tdir (hE : ChevalleyExtras D F x C O) (c : Fin D.rank → ℤ) (s : Fˣ)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    TAct x (tdir x c s) γ (s ^ cpair D.cartan c γ) := by
  have h := tact_list_prod hE (List.finRange D.rank) (List.nodup_finRange D.rank)
    (fun j => s ^ c j) hγ
  unfold tdir cpair
  convert h using 2
  rw [List.toFinset_finRange, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_mul]

theorem tdir_mem (hS : TorusSetup D x n H) (c : Fin D.rank → ℤ) (s : Fˣ) :
    tdir x c s ∈ ⨆ i, H i :=
  Subgroup.list_prod_mem _ fun t ht => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
    exact hS.torusGen_mem j _

theorem tdir_mem_Zfix (hS : TorusSetup D x n H) {α : K ≃* K} {t : K}
    (ht : t ∈ Zfix α.toMonoidHom) (c : Fin D.rank → ℤ) (s : Fˣ)
    (hact : ∀ γ ∈ D.roots, TAct x t γ (s ^ cpair D.cartan c γ)) :
    tdir x c s ∈ Zfix α.toMonoidHom := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hcen := mem_center_of_tact_eq hS (t₁ := t) (t₂ := tdir x c s)
    (fun γ hγ => ⟨_, hact γ hγ, tact_tdir hE c s hγ⟩)
  have e : tdir x c s = t * (t⁻¹ * tdir x c s) := by group
  rw [e]
  exact mul_mem ht (center_le_Zfix α hcen)

theorem tdir_single_mem_Zfix (hS : TorusSetup D x n H) {α : K ≃* K} (j : Fin D.rank) (s : Fˣ)
    (ht : torusGen x j s ∈ Zfix α.toMonoidHom) :
    tdir x (Pi.single j 1) s ∈ Zfix α.toMonoidHom := by
  obtain ⟨C, O, hE⟩ := hS.chev
  exact tdir_mem_Zfix hS ht _ s fun γ hγ => by
    rw [cpair_single]
    exact torusGen_act hE hγ j s

theorem tdir_theta_mem_Zfix (hS : TorusSetup D x n H)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1)) {θ : Fin D.rank → ℤ}
    (hθr : θ ∈ D.roots) (α : K ≃* K)
    (H1 : ∀ y ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), y ∈ Zfix α.toMonoidHom) (s : Fˣ) :
    tdir x θ s ∈ Zfix α.toMonoidHom := by
  have hθ0 : θ ∈ roots D.isFiniteType D.divisible := hθr
  obtain ⟨w₀, i₀, hw₀⟩ : ∃ (w₀ : (coxeterMatrix D.isFiniteType).Group) (i₀ : Fin D.rank),
      θ = weylAction D.isFiniteType w₀ (Pi.single i₀ 1) := by
    rcases hθ0 with ⟨w, i, h⟩ | ⟨w, i, hi, -⟩
    · exact ⟨w, i, h⟩
    · rw [hS.div] at hi
      exact absurd hi (Set.notMem_empty _)
  refine tdir_mem_Zfix hS (H1 _ (thetaTorus_mem_rankOne hS w₀ i₀ s hw₀)) θ s fun γ hγ => ?_
  have h1 := tact_thetaTorus hS w₀ i₀ s hγ
  rw [pair_weylAction_inv_eq D.isFiniteType hlong θ w₀ i₀ hw₀] at h1
  exact h1

end Act

section Alpha

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {α : K →* K} {g : K} {a : Fin D.rank → Fˣ} {φ : F ≃+* F}

theorem alpha_tdir (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ 1)
    (c : Fin D.rank → ℤ) (s : Fˣ) :
    α (tdir x c s) = g * tdir x c (Units.map (φ : F →+* F) s) * g⁻¹ := by
  have h1 : ∀ j, α (torusGen x j (s ^ c j)) =
      (MulAut.conj g).toMonoidHom (torusGen x j (Units.map (φ : F →+* F) s ^ c j)) := by
    intro j
    rw [alpha_torusGen hS.hom hN.pos hN.neg j (s ^ c j), map_zpow]
    simp [MulAut.conj_apply]
  have e : List.map α ((List.finRange D.rank).map fun j => torusGen x j (s ^ c j)) =
      List.map (MulAut.conj g).toMonoidHom
        ((List.finRange D.rank).map fun j =>
          torusGen x j (Units.map (φ : F →+* F) s ^ c j)) := by
    simp only [List.map_map]
    exact List.map_congr_left fun j _ => h1 j
  unfold tdir
  rw [map_list_prod, e, ← map_list_prod]
  simp [MulAut.conj_apply]

end Alpha

section Family

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {ι : Type*} (c : ι → Fin D.rank → ℤ)

variable (x) in
@[expose] def cosub : Subgroup K :=
  Subgroup.closure {t | ∃ (i : ι) (s : Fˣ), t = tdir x (c i) s}

theorem cosub_le (hS : TorusSetup D x n H) : cosub x c ≤ ⨆ i, H i := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, s, rfl⟩
  exact tdir_mem hS (c i) s

variable {α : K →* K} {g : K} {a : Fin D.rank → Fˣ} {φ : F ≃+* F}

theorem conj_mem_of_alpha_fam (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ 1)
    (hfix : ∀ i s, α (tdir x (c i) s) * (tdir x (c i) s)⁻¹ ∈ Subgroup.center K) :
    ∀ t ∈ cosub x c, g * t * g⁻¹ ∈ ⨆ i, H i := by
  have hgen : ∀ i s', g * tdir x (c i) s' * g⁻¹ ∈ ⨆ i, H i := by
    intro i s'
    have h2 : Units.map (φ : F →+* F) (Units.map (φ.symm : F →+* F) s' : Fˣ) = s' := by
      ext; simp
    have h0 := alpha_tdir hS hN (c i) (Units.map (φ.symm : F →+* F) s')
    rw [h2] at h0
    rw [← h0]
    have h3 := mul_mem (hS.center_le (hfix i (Units.map (φ.symm : F →+* F) s')))
      (tdir_mem hS (c i) (Units.map (φ.symm : F →+* F) s'))
    rwa [inv_mul_cancel_right] at h3
  intro t ht
  have hle : cosub x c ≤ (⨆ i, H i).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, s, rfl⟩
    exact hgen i s
  exact hle ht

theorem char_eq_fam (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ 1)
    (hfix : ∀ i s, α (tdir x (c i) s) * (tdir x (c i) s)⁻¹ ∈ Subgroup.center K)
    {h : K} (hh : h ∈ ⨆ i, H i) {w : (coxeterMatrix D.isFiniteType).Group}
    (hg : g = h * nrep hS.ct w) (i : ι) (s : Fˣ) {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) :
    Units.map (φ : F →+* F) s ^ cpair D.cartan (c i) δ =
      s ^ cpair D.cartan (c i) (weylAction D.isFiniteType w δ) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hδ' : weylAction D.isFiniteType w δ ∈ D.roots := weylAction_mem_roots D.isFiniteType w hδ
  have h1 := tact_tdir hE (c i) (Units.map (φ : F →+* F) s) hδ
  obtain ⟨ε, hε, hεc⟩ := signConj_nrep hE hS.ct hS.n_eq w δ hδ
  have h2 := TAct.conj_of_sign hε hεc h1
  obtain ⟨lam, hlam⟩ := exists_tact_of_mem_iSup hE hS.H_iff hh
  have h3 := TAct.conj (hlam _ hδ') h2
  have h4 : g * tdir x (c i) (Units.map (φ : F →+* F) s) * g⁻¹ =
      h * (nrep hS.ct w * tdir x (c i) (Units.map (φ : F →+* F) s) * (nrep hS.ct w)⁻¹) * h⁻¹ := by
    rw [hg]; group
  have h5 := alpha_tdir hS hN (c i) s
  have h6 : α (tdir x (c i) s) =
      (α (tdir x (c i) s) * (tdir x (c i) s)⁻¹) * tdir x (c i) s := by group
  have h7 : TAct x (α (tdir x (c i) s)) (weylAction D.isFiniteType w δ)
      (s ^ cpair D.cartan (c i) (weylAction D.isFiniteType w δ)) := by
    rw [h6]
    exact TAct.central_mul (hfix i s) (tact_tdir hE (c i) s hδ')
  rw [h5, h4] at h7
  exact TAct.unique (hE.param _ hδ').2.2 h3 h7

theorem hno_fam [Finite F] (hS : TorusSetup D x n H) (hq : 5 ≤ Nat.card F)
    (hc : ∀ γ ∈ D.roots, ∃ i, cpair D.cartan (c i) γ ≠ 0 ∧ |cpair D.cartan (c i) γ| ≤ 2) :
    ∀ γ ∈ D.roots, ∃ t ∈ cosub x c, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
  obtain ⟨C, O, hE⟩ := hS.chev
  intro γ hγ
  obtain ⟨i, hne, hbd⟩ := hc γ hγ
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  refine ⟨tdir x (c i) ζ, Subgroup.subset_closure ⟨i, ζ, rfl⟩, fun y hy hfix => ?_⟩
  obtain ⟨u, rfl⟩ := ((hE.param γ hγ).1 y).1 hy
  have hact := tact_tdir hE (c i) ζ hγ u
  have h3 := (hE.param γ hγ).2.2 (hact.symm.trans hfix)
  have hne' : ζ ^ cpair D.cartan (c i) γ ≠ 1 := by
    intro h1
    have h2 : ((Nat.card F - 1 : ℕ) : ℤ) ∣ cpair D.cartan (c i) γ := by
      rw [← hord]
      exact orderOf_dvd_iff_zpow_eq_one.2 h1
    have hq4 : (4 : ℤ) ≤ ((Nat.card F - 1 : ℕ) : ℤ) := by omega
    exact hne (Int.eq_zero_of_abs_lt_dvd h2 (by omega))
  have h4 : ((ζ ^ cpair D.cartan (c i) γ : Fˣ) : F) * u = u := h3
  have h5 : (((ζ ^ cpair D.cartan (c i) γ : Fˣ) : F) - 1) * u = 0 := by
    linear_combination h4
  have h6 : u = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (Units.ext (by simpa [sub_eq_zero] using h)) hne'
    · exact h
  rw [h6]
  have h7 := (hE.param γ hγ).2.1 0 0
  rw [add_zero] at h7
  exact (mul_left_cancel (a := x γ 0) (by rw [mul_one]; exact h7)).symm

theorem exists_diag_of_fixes_fam [Finite F] (hS : TorusSetup D x n H) (hq : 5 ≤ Nat.card F)
    (hc : ∀ γ ∈ D.roots, ∃ i, cpair D.cartan (c i) γ ≠ 0 ∧ |cpair D.cartan (c i) γ| ≤ 2)
    (hnum : ∀ (φ : F ≃+* F) (w : (coxeterMatrix D.isFiniteType).Group),
      (∀ (i : ι) (s : Fˣ) (δ : Fin D.rank → ℤ), δ ∈ D.roots →
        Units.map (φ : F →+* F) s ^ cpair D.cartan (c i) δ =
          s ^ cpair D.cartan (c i) (weylAction D.isFiniteType w δ)) → φ = 1 ∧ w = 1)
    (hN : NormalForm x α g a φ 1)
    (hfix : ∀ i s, α (tdir x (c i) s) * (tdir x (c i) s)⁻¹ ∈ Subgroup.center K) :
    ∃ b : Fin D.rank → Fˣ, ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c) := by
  have hno := hno_fam c hS hq hc
  obtain ⟨h, hh, w, hg⟩ := exists_mem_mul_nrep_of_forall_conj_mem_of_le hS.ct hS.ext hS.bru
    (cosub_le c hS) hno (conj_mem_of_alpha_fam c hS hN hfix)
  obtain ⟨hφ, hw⟩ := hnum φ w (fun i s δ hδ => char_eq_fam c hS hN hfix hh hg i s hδ)
  subst hw hφ
  rw [nrep_one, mul_one] at hg
  subst hg
  exact diag_of_normalForm_trivial hS hN hh

end Family

section Diagonal

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {α : K →* K} {b : Fin D.rank → Fˣ}

theorem alpha_weylElement_of_diag
    (hb : ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c)) (i : Fin D.rank)
    (t : Fˣ) : α (weylElement x i t) = weylElement x i (b i * t) := by
  have hpos : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hpos
  unfold weylElement
  rw [map_mul, map_mul, hb _ hpos, hb _ hneg, diagChar_neg, diagChar_single]
  have e1 : ((b i : Fˣ) : F) * (t : F) = ((b i * t : Fˣ) : F) := by simp
  have e2 : (((b i)⁻¹ : Fˣ) : F) * (-((t⁻¹ : Fˣ) : F)) = -(((b i * t)⁻¹ : Fˣ) : F) := by
    simp only [mul_inv_rev, Units.val_mul, mul_neg]
    rw [mul_comm]
  rw [e1, e2]

theorem alpha_torusGen_eq_of_diag (hS : TorusSetup D x n H)
    (hb : ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c)) (j : Fin D.rank)
    (s : Fˣ) : α (torusGen x j s) = torusGen x j s := by
  have hw : ∀ t, weylElement x j t = torusGen x j t * weylElement x j 1 := fun t => by
    simp [torusGen]
  have hcomm : torusGen x j s * torusGen x j (b j) = torusGen x j (b j) * torusGen x j s := by
    rw [← hS.hom, ← hS.hom, mul_comm]
  have e : α (torusGen x j s) = torusGen x j (b j * s) * (torusGen x j (b j))⁻¹ := by
    unfold torusGen
    rw [map_mul, map_inv, alpha_weylElement_of_diag hb j s, alpha_weylElement_of_diag hb j 1,
      mul_one, hw (b j * s), hw (b j)]
    group
  rw [e, hS.hom, mul_inv_eq_iff_eq_mul, ← hcomm]

end Diagonal

end CFSG.ClassicalInvolution.ModelFacts.E7Model
