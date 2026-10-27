module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.HardMathSupport.Foote.E27.Uni

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {E : Type} [Field E] {n : ℕ}

theorem card_units_three (hU : UnitaryFieldData 2 1 E) : Nat.card Eˣ = 3 := by
  have := hU.finite
  have h := Nat.card_units E
  rw [hU.card] at h
  simpa using h

theorem unit_cube (hU : UnitaryFieldData 2 1 E) (c : Eˣ) : c ^ 3 = 1 := by
  rw [← card_units_three hU]
  exact pow_card_eq_one'

theorem bar_eq (hU : UnitaryFieldData 2 1 E) (x : E) : hU.bar x = x ^ 2 := by
  rw [hU.bar_apply]; norm_num

@[expose] def dgHom (n : ℕ) (E : Type) [Field E] : (Fin n → Eˣ) →* GL (Fin n) E where
  toFun c := ⟨diagonal fun i => (c i : E), diagonal fun i => ((c i)⁻¹ : Eˣ), by
    rw [diagonal_mul_diagonal]; simp, by
    rw [diagonal_mul_diagonal]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    change diagonal (fun i => ((a i * b i : Eˣ) : E)) =
      diagonal (fun i => (a i : E)) * diagonal (fun i => (b i : E))
    rw [diagonal_mul_diagonal]; simp)

theorem dgHom_val (c : Fin n → Eˣ) : ((dgHom n E c : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
    diagonal fun i => (c i : E) := rfl

theorem dgHom_injective : Function.Injective (dgHom n E) := by
  intro a b hab
  funext i
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) hab
  simp only [dgHom_val, diagonal_apply_eq] at this
  exact Units.ext this

@[expose] def pmHom (n : ℕ) (E : Type) [Field E] : Equiv.Perm (Fin n) →* GL (Fin n) E :=
  (Matrix.permMatrixHom (n := Fin n) (R := E)).toHomUnits

theorem pmHom_val (σ : Equiv.Perm (Fin n)) :
    ((pmHom n E σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (σ⁻¹).permMatrix E := rfl

theorem pmHom_injective : Function.Injective (pmHom n E) := by
  intro σ τ h
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) h
  simp only [pmHom_val] at h1
  have h2 := PEquiv.toMatrix_injective h1
  have h3 : σ⁻¹ = τ⁻¹ := by
    refine Equiv.ext fun x => ?_
    have := congrArg (fun p : Fin n ≃. Fin n => p x) h2
    simp only [Equiv.toPEquiv_apply, Option.some.injEq] at this
    exact this
  exact inv_injective h3

theorem pm_conj_dg (σ : Equiv.Perm (Fin n)) (c : Fin n → Eˣ) :
    pmHom n E σ * dgHom n E c * (pmHom n E σ)⁻¹ = dgHom n E (c ∘ σ.symm) := by
  apply Units.ext
  rw [← map_inv]
  change (σ⁻¹).permMatrix E * diagonal (fun i => (c i : E)) * ((σ⁻¹)⁻¹).permMatrix E =
    diagonal fun i => ((c ∘ σ.symm) i : E)
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  ext i j
  simp [diagonal_apply, Equiv.Perm.inv_def]

theorem eq_one_of_dg_eq_pm {c : Fin n → Eˣ} {σ : Equiv.Perm (Fin n)}
    (h : dgHom n E c = pmHom n E σ) : σ = 1 := by
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) h
  simp only [pmHom_val, dgHom_val] at h1
  have : σ⁻¹ = 1 := by
    refine Equiv.ext fun i => ?_
    by_contra hne
    have hne' : i ≠ σ⁻¹ i := fun e => hne (by rw [Equiv.Perm.one_apply]; exact e.symm)
    have h2 := congrFun (congrFun h1 i) (σ⁻¹ i)
    rw [diagonal_apply_ne _ hne'] at h2
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply] at h2
  exact inv_eq_one.mp this

variable (hU : UnitaryFieldData 2 1 E)

include hU in
theorem dg_mem (c : Fin n → Eˣ) (hc : ∏ i, c i = 1) :
    dgHom n E c ∈ gramSU hU (1 : Matrix (Fin n) (Fin n) E) := by
  rw [mem_gramSU]
  constructor
  · rw [dgHom_val, Matrix.diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
      diagonal_mul_diagonal]
    have : ∀ i, hU.bar (c i : E) * (c i : E) = 1 := fun i => by
      rw [bar_eq hU]
      have := unit_cube hU (c i)
      have h3 := congrArg (fun u : Eˣ => (u : E)) this
      simpa [pow_succ] using h3
    simp only [this]
    exact diagonal_one
  · rw [dgHom_val, det_diagonal]
    have := congrArg (fun u : Eˣ => (u : E)) hc
    simpa [Units.coe_prod] using this

include hU in
theorem pm_mem (σ : Equiv.Perm (Fin n)) :
    pmHom n E σ ∈ gramSU hU (1 : Matrix (Fin n) (Fin n) E) := by
  rw [mem_gramSU]
  have hchar := hU.charP
  constructor
  · have hmap : ((σ⁻¹).permMatrix E).map hU.bar = (σ⁻¹).permMatrix E := by
      ext i j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, apply_ite]
    rw [pmHom_val, hmap, transpose_permMatrix, Matrix.mul_one, inv_inv, ← permMatrix_mul]
    simp
  · rw [pmHom_val, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
    · simp [h]
    · simp [h, CharTwo.neg_eq]

@[expose] def prodHom (n : ℕ) (E : Type) [Field E] : (Fin n → Eˣ) →* Eˣ :=
  MonoidHom.mk' (fun c => ∏ i, c i) fun a b => by simp [Finset.prod_mul_distrib]

@[expose] def prodKer (n : ℕ) (E : Type) [Field E] : Subgroup (Fin n → Eˣ) := (prodHom n E).ker

theorem prodHom_surjective (hn : 1 ≤ n) : Function.Surjective (prodHom n E) := by
  intro u
  refine ⟨Pi.mulSingle ⟨0, hn⟩ u, ?_⟩
  simp [prodHom]

theorem card_prodKer (hU : UnitaryFieldData 2 1 E) (hn : 1 ≤ n) :
    Nat.card (prodKer n E) = 3 ^ (n - 1) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (prodHom_surjective (E := E) hn)
  rw [card_units_three hU] at h
  have hc : Nat.card (Fin n → Eˣ) = 3 ^ n := by
    simp [Nat.card_pi, card_units_three hU]
  rw [hc] at h
  change Nat.card (prodKer n E) * 3 = 3 ^ n at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ] at h
  simpa using Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem prod_eq_one_of_mem {c : Fin n → Eˣ} (h : c ∈ prodKer n E) : ∏ i, c i = 1 := by
  simpa [prodKer, prodHom] using h

variable (hU : UnitaryFieldData 2 1 E)

@[expose] def dgG (n : ℕ) : ↥(prodKer n E) →* ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) :=
  ((dgHom n E).comp (prodKer n E).subtype).codRestrict _
    (fun c => dg_mem hU c.1 (prod_eq_one_of_mem c.2))

@[expose] def pmG (n : ℕ) : Equiv.Perm (Fin n) →* ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) :=
  (pmHom n E).codRestrict _ (pm_mem hU)

theorem dgG_val (c : ↥(prodKer n E)) :
    ((dgG hU n c : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) : GL (Fin n) E) =
      dgHom n E c.1 := rfl

theorem pmG_val (σ : Equiv.Perm (Fin n)) :
    ((pmG hU n σ : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) : GL (Fin n) E) =
      pmHom n E σ := rfl

theorem dgG_injective : Function.Injective (dgG hU n) := by
  intro a b h
  have h1 := congrArg (fun g : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) =>
    (g : GL (Fin n) E)) h
  exact Subtype.ext (dgHom_injective h1)

theorem pmG_injective : Function.Injective (pmG hU n) := by
  intro a b h
  have h1 := congrArg (fun g : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) =>
    (g : GL (Fin n) E)) h
  exact pmHom_injective h1

theorem dgG_range_inf_pmG_range {g : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))}
    (h1 : g ∈ (dgG hU n).range) (h2 : g ∈ (pmG hU n).range) : g = 1 := by
  obtain ⟨c, rfl⟩ := h1
  obtain ⟨σ, hσ⟩ := h2
  have h3 := congrArg (fun g : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) =>
    (g : GL (Fin n) E)) hσ
  have h4 : dgHom n E c.1 = pmHom n E σ := h3.symm
  have := eq_one_of_dg_eq_pm h4
  subst this
  rw [map_one] at hσ
  exact hσ.symm

theorem pm_conj_mem (σ : Equiv.Perm (Fin n)) {a : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))}
    (ha : a ∈ (dgG hU n).range) : pmG hU n σ * a * (pmG hU n σ)⁻¹ ∈ (dgG hU n).range := by
  obtain ⟨c, rfl⟩ := ha
  refine ⟨⟨c.1 ∘ σ.symm, ?_⟩, ?_⟩
  · have := prod_eq_one_of_mem c.2
    change ∏ i, c.1 (σ.symm i) = 1
    rw [Equiv.prod_comp σ.symm c.1]
    exact this
  · apply Subtype.ext
    change dgHom n E (c.1 ∘ σ.symm) = (pmHom n E σ) * dgHom n E c.1 * (pmHom n E σ)⁻¹
    exact (pm_conj_dg σ c.1).symm

theorem dgHom_const (c : Eˣ) : dgHom n E (fun _ => c) = Matrix.GeneralLinearGroup.scalar (Fin n) c :=
  Units.ext (by
    rw [dgHom_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply])

abbrev Zsc (n : ℕ) : Subgroup ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) :=
  normOneScalars hU (gramSU hU (1 : Matrix (Fin n) (Fin n) E)) n

theorem Zsc_le_range : Zsc hU n ≤ (dgG hU n).range := by
  intro z hz
  obtain ⟨c, -, hcn, hc⟩ := hz
  have hprod : (fun _ : Fin n => c) ∈ prodKer n E := by
    change ∏ _i : Fin n, c = 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hcn
  refine ⟨⟨fun _ => c, hprod⟩, Subtype.ext ?_⟩
  rw [dgG_val]
  exact (dgHom_const c).trans hc.symm

theorem card_Zsc_le_three (hU : UnitaryFieldData 2 1 E) : Nat.card (Zsc hU n) ≤ 3 := by
  have := hU.finite
  rw [← card_units_three hU]
  refine Nat.card_le_card_of_injective
    (fun z : Zsc hU n => (Classical.choose z.2 : Eˣ)) ?_
  intro z z' h
  apply Subtype.ext
  apply Subtype.ext
  have h1 := (Classical.choose_spec z.2).2.2
  have h2 := (Classical.choose_spec z'.2).2.2
  change (z.1 : GL (Fin n) E) = _ at h1
  change (z'.1 : GL (Fin n) E) = _ at h2
  rw [h1, h2]
  simp only [h]

theorem Zsc_eq_bot_of_coprime (hU : UnitaryFieldData 2 1 E) (hn : Nat.Coprime n 3) :
    Zsc hU n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨c, -, hcn, hc⟩ := hz
  have h1 : c = 1 := by
    have := (pow_gcd_eq_one (a := c) (m := n) (n := 3)).mpr ⟨hcn, unit_cube hU c⟩
    rwa [hn, pow_one] at this
  apply Subtype.ext
  change (z : GL (Fin n) E) = 1
  rw [hc, h1, map_one]

theorem card_le_card_map_mul {G Q : Type*} [Group G] [Group Q] [Finite G] (π : G →* Q)
    (H : Subgroup G) : Nat.card H ≤ Nat.card (H.map π) * Nat.card π.ker := by
  have h := Subgroup.card_ker_mul_card_range (π.comp H.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hk : Nat.card (π.comp H.subtype).ker ≤ Nat.card π.ker := by
    refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : G), x.2⟩) ?_
    intro x y hxy
    have h' : ((x : H) : G) = ((y : H) : G) := by simpa using congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h')
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_left _ hk

abbrev piU (n : ℕ) : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) →*
    primeFormP hU (1 : Matrix (Fin n) (Fin n) E) :=
  QuotientGroup.mk' (Zsc hU n)

@[expose] def AtS (n : ℕ) : Subgroup ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) := (dgG hU n).range

@[expose] def PtS (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) :
    Subgroup ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) := P.map (pmG hU n)

@[expose] def MS (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) :
    Subgroup ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) := AtS hU n ⊔ PtS hU n P

@[expose] def Smono (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) :
    Subgroup (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) := (MS hU n P).map (piU hU n)

@[expose] def Amono (n : ℕ) : Subgroup (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)) :=
  (AtS hU n).map (piU hU n)

theorem Amono_comm (n : ℕ) : ∀ a ∈ Amono hU n, ∀ b ∈ Amono hU n, a * b = b * a := by
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩ _ ⟨_, ⟨d, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg (piU hU n) (congrArg (dgG hU n) (Subtype.ext (mul_comm c.1 d.1)))

theorem PtS_le_normalizer (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) :
    PtS hU n P ≤ Subgroup.normalizer (AtS hU n : Set _) := by
  rintro _ ⟨σ, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact fun ha => pm_conj_mem hU σ ha
  · intro h
    have := pm_conj_mem hU σ⁻¹ h
    rw [map_inv] at this
    have e : (pmG hU n σ)⁻¹ * (pmG hU n σ * a * (pmG hU n σ)⁻¹) * ((pmG hU n σ)⁻¹)⁻¹ = a := by
      group
    rw [e] at this
    exact this

theorem monomial_data_of_pgroup (hn : 1 ≤ n) (P : Subgroup (Equiv.Perm (Fin n)))
    (hP : IsPGroup 3 P) (zb : ℕ) (hZ : Nat.card (Zsc hU n) ≤ zb) :
    IsPGroup 3 (Smono hU n P) ∧ 3 ^ (n - 1) * Nat.card P ≤ Nat.card (Smono hU n P) * zb ∧
      Amono hU n ≤ Smono hU n P ∧
      (∀ s ∈ Smono hU n P, ∀ a ∈ Amono hU n, s * a * s⁻¹ ∈ Amono hU n) ∧
      (∀ a ∈ Amono hU n, ∀ b ∈ Amono hU n, a * b = b * a) ∧
      (∀ a ∈ Amono hU n, a ^ 3 = 1) ∧ 3 ^ (n - 1) ≤ Nat.card (Amono hU n) * zb := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin := hU.finite
  let π : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) →* primeFormP hU (1 : Matrix (Fin n) (Fin n) E) :=
    QuotientGroup.mk' (Zsc hU n)
  have hker : π.ker = Zsc hU n := QuotientGroup.ker_mk' _
  set At : Subgroup ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) := (dgG hU n).range with hAt
  set Pt : Subgroup ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) :=
    (P : Subgroup (Equiv.Perm (Fin n))).map (pmG hU n) with hPt
  have hAtcard : Nat.card At = 3 ^ (n - 1) := by
    rw [hAt]
    have := Nat.card_range_of_injective (dgG_injective (n := n) hU)
    exact this.trans (card_prodKer hU hn)
  have hPtcard : Nat.card Pt = Nat.card P := Subgroup.card_map_of_injective (pmG_injective hU)
  have hAtp : IsPGroup 3 At := IsPGroup.of_card hAtcard
  have hPtp : IsPGroup 3 Pt := hP.map (pmG hU n)
  have hnormAt : Pt ≤ Subgroup.normalizer (At : Set _) := by
    rintro _ ⟨σ, -, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact fun ha => pm_conj_mem hU σ ha
    · intro h
      have := pm_conj_mem hU σ⁻¹ h
      rw [map_inv] at this
      have e : (pmG hU n σ)⁻¹ * (pmG hU n σ * a * (pmG hU n σ)⁻¹) * ((pmG hU n σ)⁻¹)⁻¹ = a := by
        group
      rw [e] at this
      exact this
  have hMp : IsPGroup 3 (At ⊔ Pt : Subgroup _) := hAtp.to_sup_of_normal_left' hPtp hnormAt
  have hMnorm : (At ⊔ Pt : Subgroup _) ≤ Subgroup.normalizer (At : Set _) :=
    sup_le Subgroup.le_normalizer hnormAt
  have hMcard : 3 ^ (n - 1) * Nat.card P ≤ Nat.card (At ⊔ Pt : Subgroup _) := by
    rw [← hAtcard, ← hPtcard, ← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun x : At × Pt => (⟨(x.1 : _) * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
        (Subgroup.mem_sup_right x.2.2)⟩ : ↥(At ⊔ Pt : Subgroup _))) ?_
    rintro ⟨a, p⟩ ⟨a', p'⟩ h
    have h1 : (a : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) * p = a' * p' :=
      congrArg Subtype.val h
    have hg : ((a' : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)))⁻¹ * (a : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)))) =
        (p' : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) * (p : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1]
      group
    have hpP : ∀ q : Pt, (q : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) ∈ (pmG hU n).range :=
      fun q => by
        obtain ⟨σ, -, hσ⟩ := q.2
        exact ⟨σ, hσ⟩
    have hone := dgG_range_inf_pmG_range hU
      (g := (a' : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)))⁻¹ * (a : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))))
      (mul_mem (inv_mem a'.2) a.2)
      (by rw [hg]; exact mul_mem (hpP p') (inv_mem (hpP p)))
    have haa : (a : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) = a' := by
      rw [inv_mul_eq_one] at hone
      exact hone.symm
    have hpp : (p : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) = p' := by
      rw [haa] at h1
      exact mul_left_cancel h1
    have : a = a' := Subtype.ext haa
    have : p = p' := Subtype.ext hpp
    subst_vars
    rfl
  have hcommAt : ∀ a ∈ At, ∀ b ∈ At, a * b = b * a := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (dgG hU n) (Subtype.ext (mul_comm c.1 d.1))
  have hexpAt : ∀ a ∈ At, a ^ 3 = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [← map_pow]
    have : c ^ 3 = 1 := Subtype.ext (funext fun i => unit_cube hU _)
    rw [this, map_one]
  refine ⟨hMp.map π, ?_, Subgroup.map_mono le_sup_left, ?_, ?_, ?_, ?_⟩
  · have h1 := card_le_card_map_mul π (At ⊔ Pt)
    rw [hker] at h1
    calc 3 ^ (n - 1) * Nat.card P ≤ Nat.card (At ⊔ Pt : Subgroup _) := hMcard
      _ ≤ _ := h1
      _ ≤ _ := Nat.mul_le_mul_left _ hZ
  · rintro _ ⟨m, hm, rfl⟩ _ ⟨a, ha, rfl⟩
    refine ⟨m * a * m⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMnorm hm) a).mp ha
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcommAt a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexpAt a ha, map_one]
  · have h2 := card_le_card_map_mul π At
    rw [hker] at h2
    calc 3 ^ (n - 1) = Nat.card At := hAtcard.symm
      _ ≤ _ := h2
      _ ≤ _ := Nat.mul_le_mul_left _ hZ

theorem monomial_data (hn : 1 ≤ n) (P : Sylow 3 (Equiv.Perm (Fin n))) (zb : ℕ)
    (hZ : Nat.card (Zsc hU n) ≤ zb) :
    IsPGroup 3 (Smono hU n (P : Subgroup (Equiv.Perm (Fin n)))) ∧
      3 ^ (n - 1) * Nat.card (P : Subgroup (Equiv.Perm (Fin n))) ≤
        Nat.card (Smono hU n (P : Subgroup (Equiv.Perm (Fin n)))) * zb ∧
      Amono hU n ≤ Smono hU n (P : Subgroup (Equiv.Perm (Fin n))) ∧
      (∀ s ∈ Smono hU n (P : Subgroup (Equiv.Perm (Fin n))), ∀ a ∈ Amono hU n,
        s * a * s⁻¹ ∈ Amono hU n) ∧
      (∀ a ∈ Amono hU n, ∀ b ∈ Amono hU n, a * b = b * a) ∧
      (∀ a ∈ Amono hU n, a ^ 3 = 1) ∧ 3 ^ (n - 1) ≤ Nat.card (Amono hU n) * zb :=
  by
    have := monomial_data_of_pgroup hU hn (P : Subgroup _) P.isPGroup' zb hZ
    exact this

end CFSG.HardMathSupport.Foote.E27.Uni

end
