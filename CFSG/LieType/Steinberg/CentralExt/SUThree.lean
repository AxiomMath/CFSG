module

public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

section Glue

variable {E G : Type*} [Group E] [Group G] {π : E →* G}

@[expose] def conjRestrict (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    L →* L where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjRestrict (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (x : L) : (conjRestrict L hg x : G) = g * x * g⁻¹ :=
  rfl

theorem conj_section_eq {L : Subgroup G} {β : L →* E} (hβ : ∀ x, π (β x) = x)
    (huniq : ∀ β₁ β₂ : L →* E, π.comp β₁ = π.comp β₂ → β₁ = β₂) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) {g' : E} (hg' : π g' = g) (x : L) :
    g' * β x * g'⁻¹ = β (conjRestrict L hg x) := by
  have h := huniq ((MulAut.conj g').toMonoidHom.comp β) (β.comp (conjRestrict L hg)) (by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hβ, hg', coe_conjRestrict])
  exact DFunLike.congr_fun h x

theorem exists_section_sup_zpowers {L : Subgroup G} {β : L →* E} (hβ : ∀ x, π (β x) = x)
    (huniq : ∀ β₁ β₂ : L →* E, π.comp β₁ = π.comp β₂ → β₁ = β₂) {δ : G}
    (hδ : δ ∈ Subgroup.normalizer (L : Set G)) (hdisj : ∀ k : ℤ, δ ^ k ∈ L → δ ^ k = 1)
    {δ' : E} (hδ' : π δ' = δ) (hord : δ' ^ orderOf δ = 1) :
    ∃ s : ↥(L ⊔ Subgroup.zpowers δ) →* E, ∀ x, π (s x) = x := by
  set L' := β.range
  have hconj : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {g' : E}, π g' = g →
      ∀ y ∈ L', g' * y * g'⁻¹ ∈ L' := by
    rintro g hg g' hg' _ ⟨x, rfl⟩
    rw [conj_section_eq hβ huniq hg hg' x]
    exact ⟨_, rfl⟩
  have hnorm : Subgroup.zpowers δ' ≤ Subgroup.normalizer (L' : Set E) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj hδ hδ' y, fun hy => ?_⟩
    have h := hconj (inv_mem hδ) (by rw [map_inv, hδ']) _ hy
    have e : δ'⁻¹ * (δ' * y * δ'⁻¹) * δ'⁻¹⁻¹ = y := by group
    rwa [e] at h
  set M' := L' ⊔ Subgroup.zpowers δ'
  have hmem : ∀ z ∈ M', ∃ x : L, ∃ k : ℤ, z = β x * δ' ^ k := by
    intro z hz
    have hz' : z ∈ ((M' : Subgroup E) : Set E) := hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hz'
    obtain ⟨_, ⟨x, rfl⟩, _, ⟨k, rfl⟩, rfl⟩ := hz'
    exact ⟨x, k, rfl⟩
  have hinj : ∀ z ∈ M', π z = 1 → z = 1 := by
    intro z hz h1
    obtain ⟨x, k, rfl⟩ := hmem z hz
    rw [map_mul, map_zpow, hβ, hδ'] at h1
    have hk : δ ^ k = 1 := by
      refine hdisj k ?_
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem x.2
    have hx : (x : G) = 1 := by rwa [hk, mul_one] at h1
    have hk' : δ' ^ k = 1 := by
      obtain ⟨m, hm⟩ := (orderOf_dvd_iff_zpow_eq_one).2 hk
      rw [hm, _root_.zpow_mul, zpow_natCast, hord, _root_.one_zpow]
    rw [hk', mul_one, show x = 1 from Subtype.ext hx, map_one]
  have hrange : M'.map π = L ⊔ Subgroup.zpowers δ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hδ', MonoidHom.map_range]
    congr 1
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      rw [MonoidHom.comp_apply, hβ]
      exact x.2
    · intro hg
      exact ⟨⟨g, hg⟩, by rw [MonoidHom.comp_apply, hβ]⟩
  have hmap : ∀ z : M', π z ∈ L ⊔ Subgroup.zpowers δ := fun z => by
    rw [← hrange]
    exact ⟨z, z.2, rfl⟩
  let ψ : M' →* ↥(L ⊔ Subgroup.zpowers δ) := (π.comp M'.subtype).codRestrict _ hmap
  have hψ : Function.Bijective ψ := by
    refine ⟨(injective_iff_map_eq_one ψ).2 fun z hz => Subtype.ext (hinj z z.2 ?_), fun g => ?_⟩
    · exact congrArg Subtype.val hz
    · obtain ⟨z, hz, hzg⟩ : (g : G) ∈ M'.map π := by
        rw [hrange]
        exact g.2
      exact ⟨⟨z, hz⟩, Subtype.ext hzg⟩
  refine ⟨M'.subtype.comp (MulEquiv.ofBijective ψ hψ).symm.toMonoidHom, fun g => ?_⟩
  exact congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply g)

theorem card_sup_zpowers [Finite G] {L : Subgroup G} {δ : G}
    (hδ : δ ∈ Subgroup.normalizer (L : Set G)) (hdisj : ∀ k : ℤ, δ ^ k ∈ L → δ ^ k = 1) :
    Nat.card ↥(L ⊔ Subgroup.zpowers δ) = Nat.card L * orderOf δ := by
  have hnorm : Subgroup.zpowers δ ≤ Subgroup.normalizer (L : Set G) := by
    rwa [Subgroup.zpowers_le]
  have hpos : 0 < orderOf δ := orderOf_pos δ
  let φ : L × Fin (orderOf δ) → ↥(L ⊔ Subgroup.zpowers δ) := fun x =>
    ⟨x.1 * δ ^ (x.2 : ℕ), Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers _ _))⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h : (x.1 : G) * δ ^ (x.2 : ℕ) = y.1 * δ ^ (y.2 : ℕ) := congrArg Subtype.val hxy
      have h' : δ ^ ((x.2 : ℕ) : ℤ) * (δ ^ ((y.2 : ℕ) : ℤ))⁻¹ = (x.1 : G)⁻¹ * y.1 := by
        rw [zpow_natCast, zpow_natCast]
        calc δ ^ (x.2 : ℕ) * (δ ^ (y.2 : ℕ))⁻¹
            = (x.1 : G)⁻¹ * (x.1 * δ ^ (x.2 : ℕ)) * (δ ^ (y.2 : ℕ))⁻¹ := by group
          _ = (x.1 : G)⁻¹ * y.1 := by rw [h]; group
      rw [← _root_.zpow_sub] at h'
      have h1 : δ ^ (((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)) = 1 :=
        hdisj _ (by rw [h']; exact mul_mem (inv_mem x.1.2) y.1.2)
      have hdvd := (orderOf_dvd_iff_zpow_eq_one).2 h1
      have h2 : x.2 = y.2 := by
        have hx := x.2.isLt
        have hy := y.2.isLt
        obtain ⟨c, hc⟩ := hdvd
        apply Fin.ext
        have : c = 0 := by
          rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
          · nlinarith
          · exact hc0
          · nlinarith
        rw [this, mul_zero, sub_eq_zero] at hc
        exact_mod_cast hc
      rw [h2, mul_left_inj] at h
      exact Prod.ext (Subtype.ext h) h2
    · have hz : (z : G) ∈ ((L ⊔ Subgroup.zpowers δ : Subgroup G) : Set G) := z.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hz
      obtain ⟨x, hx, _, ⟨k, rfl⟩, hz⟩ := hz
      refine ⟨(⟨x, hx⟩, ⟨(k % (orderOf δ : ℤ)).toNat, ?_⟩), Subtype.ext ?_⟩
      · have h1 : k % (orderOf δ : ℤ) < orderOf δ := Int.emod_lt_of_pos k (by exact_mod_cast hpos)
        omega
      · change x * δ ^ (k % (orderOf δ : ℤ)).toNat = z
        rw [← hz, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by exact_mod_cast
          hpos.ne')), zpow_mod_orderOf]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_fin]

end Glue

section Embed

variable {F : Type*} [Field F]

@[expose] def embPair (c : Fin 3) (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  if c = 0 then !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]
  else if c = 1 then !![A 0 0, 0, A 0 1; 0, 1, 0; A 1 0, 0, A 1 1]
  else !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem embPair_mul (c : Fin 3) (A B : Matrix (Fin 2) (Fin 2) F) :
    embPair c (A * B) = embPair c A * embPair c B := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem embPair_one (c : Fin 3) : embPair c (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [embPair]

theorem det_embPair (c : Fin 3) (A : Matrix (Fin 2) (Fin 2) F) : (embPair c A).det = A.det := by
  fin_cases c <;> simp [embPair, Matrix.det_fin_three, Matrix.det_fin_two]

theorem conjTr_embPair (σ : F ≃+* F) (c : Fin 3) (A : Matrix (Fin 2) (Fin 2) F) :
    conjTr σ (embPair c A) = embPair c (conjTr σ A) := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [embPair, conjTr]

theorem embPair_injective (c : Fin 3) :
    Function.Injective (embPair c : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 3) (Fin 3) F) := by
  intro A B h
  ext i j
  fin_cases c <;> fin_cases i <;> fin_cases j
  all_goals first
    | simpa [embPair] using congrFun (congrFun h 0) 0
    | simpa [embPair] using congrFun (congrFun h 0) 1
    | simpa [embPair] using congrFun (congrFun h 0) 2
    | simpa [embPair] using congrFun (congrFun h 1) 0
    | simpa [embPair] using congrFun (congrFun h 1) 1
    | simpa [embPair] using congrFun (congrFun h 1) 2
    | simpa [embPair] using congrFun (congrFun h 2) 0
    | simpa [embPair] using congrFun (congrFun h 2) 1
    | simpa [embPair] using congrFun (congrFun h 2) 2

variable (σ : F ≃+* F)

@[expose] def embSUidElt (c : Fin 3) (A : SUid σ 2) : SUid σ 3 :=
  ⟨⟨embPair c ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
      embPair c (((A : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
      by rw [← embPair_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, embPair_one],
      by rw [← embPair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, embPair_one]⟩,
    by rw [Units.val_mk, det_embPair, A.2.1],
    by rw [Units.val_mk, conjTr_embPair, ← embPair_mul, A.2.2, embPair_one]⟩

theorem coe_embSUidElt (c : Fin 3) (A : SUid σ 2) :
    ((embSUidElt σ c A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      embPair c ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] def embSUid (c : Fin 3) : SUid σ 2 →* SUid σ 3 :=
  MonoidHom.mk' (embSUidElt σ c) fun A B => Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_embSUidElt, coe_embSUidElt, coe_embSUidElt,
      Subgroup.coe_mul, Units.val_mul, embPair_mul]))

theorem coe_embSUid (c : Fin 3) (A : SUid σ 2) :
    ((embSUid σ c A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      embPair c ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem embSUid_injective (c : Fin 3) : Function.Injective (embSUid σ c) := by
  intro A B h
  have h' := congrArg (fun g : SUid σ 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_embSUid] at h'
  exact Subtype.ext (Units.ext (embPair_injective c h'))

end Embed

section Torus

variable {F : Type*} [Field F] (σ : F ≃+* F)

@[expose] def diagGL {n : ℕ} (d : Fin n → Fˣ) : GL (Fin n) F :=
  ⟨Matrix.diagonal fun i => (d i : F), Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

theorem coe_diagGL {n : ℕ} (d : Fin n → Fˣ) :
    ((diagGL d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal fun i => (d i : F) :=
  rfl

theorem coe_diagGL_inv {n : ℕ} (d : Fin n → Fˣ) :
    (((diagGL d)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) :=
  rfl

theorem conjTr_diagonal {n : ℕ} (v : Fin n → F) :
    conjTr σ (Matrix.diagonal v) = Matrix.diagonal fun i => σ (v i) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [conjTr]
  · simp [conjTr, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

@[expose] def normOne : Subgroup Fˣ where
  carrier := {u | σ (u : F) * u = 1}
  mul_mem' {a b} ha hb := by
    change σ ((a * b : Fˣ) : F) * ((a * b : Fˣ) : F) = 1
    rw [Units.val_mul, map_mul]
    calc σ a * σ b * (a * b) = (σ a * a) * (σ b * b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' {a} ha := by
    change σ ((a⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, ha, inv_one]

theorem mem_normOne {u : Fˣ} : u ∈ normOne σ ↔ σ (u : F) * u = 1 :=
  Iff.rfl

@[expose] def torusTwoElt (u : normOne σ) : SUid σ 2 :=
  ⟨diagGL ![(u : Fˣ), (u : Fˣ)⁻¹], by
    rw [coe_diagGL, Matrix.det_diagonal, Fin.prod_univ_two]
    simp, by
    have hu := u.2
    rw [mem_normOne] at hu
    rw [coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hu
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Units.val_inv_eq_inv_val, map_inv₀]
      rw [← mul_inv, hu, inv_one]⟩

@[expose] def torusTwo : normOne σ →* SUid σ 2 :=
  MonoidHom.mk' (torusTwoElt σ) fun u v => Subtype.ext (Units.ext (by
    simp only [torusTwoElt, Subgroup.coe_mul, Units.val_mul, coe_diagGL,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]))

theorem coe_torusTwo (u : normOne σ) :
    ((torusTwo σ u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal fun i => (![(u : Fˣ), (u : Fˣ)⁻¹] i : F) :=
  rfl

theorem torusTwo_injective : Function.Injective (torusTwo σ) := by
  intro u v h
  have h' := congrFun (congrFun (congrArg (fun g : SUid σ 2 =>
    ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h) 0) 0
  simp only [coe_torusTwo, Matrix.diagonal_apply_eq, Matrix.cons_val_zero] at h'
  exact Subtype.ext (Units.ext h')

theorem orderOf_torusTwo (u : normOne σ) : orderOf (torusTwo σ u) = orderOf (u : Fˣ) := by
  rw [orderOf_injective _ (torusTwo_injective σ), Subgroup.orderOf_coe]

variable {σ}

theorem conj_mem_SUid (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {D A : GL (Fin n) F}
    (hD : conjTr σ (D : Matrix (Fin n) (Fin n) F) * (D : Matrix (Fin n) (Fin n) F) = 1)
    (hA : A ∈ SUid σ n) : D * A * D⁻¹ ∈ SUid σ n := by
  set Dm := (D : Matrix (Fin n) (Fin n) F)
  set Di := ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Am := (A : Matrix (Fin n) (Fin n) F)
  have hDDi : Dm * Di = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDiD : Di * Dm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDi : Di = conjTr σ Dm := by
    calc Di = conjTr σ Dm * Dm * Di := by rw [hD, Matrix.one_mul]
      _ = conjTr σ Dm := by rw [Matrix.mul_assoc, hDDi, Matrix.mul_one]
  have hcc : conjTr σ (conjTr σ Dm) = Dm := by
    ext i j
    simp [conjTr, hσ]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hA.1, mul_one, ← det_mul, hDDi, det_one]
  · rw [Units.val_mul, Units.val_mul]
    calc conjTr σ (Dm * Am * Di) * (Dm * Am * Di)
        = conjTr σ Di * conjTr σ Am * (conjTr σ Dm * Dm) * Am * Di := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = Dm * (conjTr σ Am * Am) * Di := by
          rw [hD, hDi, hcc]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hA.2, Matrix.mul_one, hDDi]

theorem embSUid_one_mul_embSUid_two (hσ : ∀ c, σ (σ c) = c) (v : normOne σ) (A : SUid σ 2) :
    ∃ B : SUid σ 2,
      embSUid σ 1 (torusTwo σ v) * embSUid σ 2 A = embSUid σ 2 B * embSUid σ 1 (torusTwo σ v) := by
  set D : GL (Fin 2) F := diagGL ![(v : Fˣ), 1]
  have hv := v.2
  rw [mem_normOne] at hv
  have hv0 : ((v : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hD : conjTr σ (D : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hv
    · simp
  refine ⟨⟨D * A * D⁻¹, conj_mem_SUid hσ hD A.2⟩, Subtype.ext (Units.ext ?_)⟩
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo, D, coe_diagGL,
    coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

end Torus

section Split

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

theorem ringChar_fixedSubfield : ringChar (fixedSubfield F p f) = p :=
  ringChar.eq _ p

theorem exists_section_SUid_three (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {E : Type*} [Group E] [Finite E] {π : E →* SUid (unitaryInvolution F p f) 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : SUid (unitaryInvolution F p f) 3 →* E, ∀ x, π (s x) = x := by
  have hσ : ∀ c, σ₀ (σ₀ c) = c := unitaryInvolution_involutive hF
  have hk : ringChar (fixedSubfield F p f) ≠ 2 := by
    rw [ringChar_fixedSubfield]
    exact hp2
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  let e : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f) ≃* SUid σ₀ 2 :=
    (hypEquiv hζ0 hζ).trans (conjEquiv P hP)
  let α₂ := (embSUid σ₀ 2).comp e.toMonoidHom
  have hα₂ : Function.Injective α₂ := (embSUid_injective σ₀ 2).comp e.injective
  set L := α₂.range
  have hL : ∀ x, x ∈ L ↔ ∃ A, embSUid σ₀ 2 A = x := by
    intro x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨A, rfl⟩
      exact ⟨e.symm A, by simp [α₂]⟩
  let ψ := MonoidHom.ofInjective hα₂
  obtain ⟨β₀, hβ₀⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hcen h2 α₂
  let β : L →* E := β₀.comp ψ.symm.toMonoidHom
  have hβ : ∀ x, π (β x) = x := by
    intro x
    have h1 := DFunLike.congr_fun hβ₀ (ψ.symm x)
    have h2' := MonoidHom.ofInjective_apply hα₂ (x := ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at h2'
    rw [MonoidHom.comp_apply] at h1
    change π (β₀ (ψ.symm x)) = x
    rw [h1, ← h2']
  have huniq : ∀ β₁ β₂ : L →* E, π.comp β₁ = π.comp β₂ → β₁ = β₂ := by
    intro β₁ β₂ h
    have h' := CFSG.LieType.CentralExt.lift_unique hk hcen h2
      (β₁ := β₁.comp ψ.toMonoidHom) (β₂ := β₂.comp ψ.toMonoidHom)
      (by rw [← MonoidHom.comp_assoc, h, MonoidHom.comp_assoc])
    ext x
    have := DFunLike.congr_fun h' (ψ.symm x)
    simpa using this
  obtain ⟨l, hl, hlo⟩ := exists_norm_one_orderOf_eq hF
  let u : normOne σ₀ := ⟨l, hl⟩
  set δ := embSUid σ₀ 1 (torusTwo σ₀ u)
  have hδo : orderOf δ = orderOf (torusTwo σ₀ u) :=
    orderOf_injective _ (embSUid_injective σ₀ 1) _
  have hδq : orderOf δ = p ^ f + 1 := by
    rw [hδo, orderOf_torusTwo]
    exact hlo
  obtain ⟨β₁, hβ₁⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hcen h2
    ((embSUid σ₀ 1).comp e.toMonoidHom)
  set δ' := β₁ (e.symm (torusTwo σ₀ u))
  have hδ' : π δ' = δ := by
    have := DFunLike.congr_fun hβ₁ (e.symm (torusTwo σ₀ u))
    simpa using this
  have hord : δ' ^ orderOf δ = 1 := by
    rw [← map_pow, ← map_pow, hδo, pow_orderOf_eq_one, map_one, map_one]
  have hconj : ∀ (v : normOne σ₀) (x : SUid σ₀ 3), x ∈ L →
      embSUid σ₀ 1 (torusTwo σ₀ v) * x * (embSUid σ₀ 1 (torusTwo σ₀ v))⁻¹ ∈ L := by
    intro v x hx
    obtain ⟨A, rfl⟩ := (hL x).1 hx
    obtain ⟨B, hB⟩ := embSUid_one_mul_embSUid_two hσ v A
    rw [hB, mul_inv_cancel_right]
    exact (hL _).2 ⟨B, rfl⟩
  have hδn : δ ∈ Subgroup.normalizer (L : Set (SUid σ₀ 3)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj u x, fun hx => ?_⟩
    have h := hconj u⁻¹ _ hx
    have hinv : embSUid σ₀ 1 (torusTwo σ₀ u⁻¹) = δ⁻¹ := by rw [map_inv, map_inv]
    rwa [hinv, show δ⁻¹ * (δ * x * δ⁻¹) * δ⁻¹⁻¹ = x by group] at h
  have hdisj : ∀ k : ℤ, δ ^ k ∈ L → δ ^ k = 1 := by
    intro k hk'
    obtain ⟨A, hA⟩ := (hL _).1 hk'
    rw [← map_zpow, ← map_zpow] at hA ⊢
    have h22 := congrFun (congrFun (congrArg (fun g : SUid σ₀ 3 =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hA) 2) 2
    simp only [coe_embSUid, coe_torusTwo] at h22
    simp [embPair] at h22
    have hu1 : u ^ k = 1 := Subtype.ext (Units.ext (by
      simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, Subgroup.coe_one, Units.val_one]
      exact h22))
    rw [hu1, map_one, map_one]
  obtain ⟨s, hs⟩ := exists_section_sup_zpowers hβ huniq hδn hdisj hδ' hord
  set q := p ^ f
  have hq2 : 2 ≤ q := (CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF)
  have hqodd : Odd q := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hcardG : Nat.card (SUid σ₀ 3) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    obtain ⟨P₃, hP₃⟩ := exists_wittMatrix hF 3
    rw [← Nat.card_congr (conjEquiv P₃ hP₃).toEquiv, card_SU_three hF]
  have hcardL : Nat.card L = q * (q ^ 2 - 1) := by
    rw [← Nat.card_congr ψ.toEquiv, card_specialLinearGroup_fin_two, card_fixedSubfield hF]
  have hcardM := card_sup_zpowers hδn hdisj
  rw [hcardL, hδq] at hcardM
  have hidx : (L ⊔ Subgroup.zpowers δ).index = q ^ 2 * (q ^ 2 - q + 1) := by
    have h := Subgroup.card_mul_index (L ⊔ Subgroup.zpowers δ)
    rw [hcardM, hcardG] at h
    have hq1 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    have hq3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have key : q * (q ^ 2 - 1) * (q + 1) * (q ^ 2 * (q ^ 2 - q + 1)) =
        q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
      zify [hq1, hq3]
      ring
    rw [← key] at h
    have hq4 : 0 < q ^ 2 - 1 := by
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.mul_pos (by omega) hq4) (by omega)) h
  have hodd : Nat.Coprime 2 (L ⊔ Subgroup.zpowers δ).index := by
    rw [Nat.coprime_two_left, hidx]
    refine Odd.mul hqodd.pow ?_
    obtain ⟨t, ht⟩ := hqodd
    refine ⟨2 * t ^ 2 + t, ?_⟩
    have hq1 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    zify [hq1] at ht ⊢
    rw [ht]
    ring
  exact CFSG.Semidihedral.CentralTransferSplitting.exists_section_of_coprime_index 2 π hπ hcen
    h2 _ hodd s hs

theorem exists_section_SU_three (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : SU σ₀ 3 →* E, ∀ x, π (s x) = x := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
  set e := conjEquiv P hP
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  obtain ⟨s, hs⟩ := exists_section_SUid_three hF hp2 (π := e.toMonoidHom.comp π)
    (e.surjective.comp hπ) (hker ▸ hcen) (hker ▸ h2)
  refine ⟨s.comp e.toMonoidHom, fun x => e.injective ?_⟩
  exact hs (e x)

theorem su_three_central_two_extension_splitting (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ s : SU σ₀ 3 →* E, (∀ x, π (s x) = x) ∧ (∀ τ : SU σ₀ 3 →* E, (∀ x, π (τ x) = x) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  obtain ⟨s, hs⟩ := exists_section_SU_three hF hp2 hπ hcen h2
  have hC : ¬ p ∣ Nat.card π.ker :=
    CFSG.LieType.CentralExt.not_dvd_card_of_isPGroup_two h2 Fact.out hp2
  have : Nonempty (Fin 3) := ⟨0⟩
  refine exists_section_mulEquiv_of_existsUnique hcen (existsUnique_section_of_rankOne_lift
    (D := rootDatum hF 3) (isCTGroupDatum hF 3 (by norm_num) ζ hζ)
    (steinbergExtras hF 3 (by norm_num) ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC fun i => ⟨s.comp (Subgroup.subtype _),
      fun x => hs x⟩)

end Split

end CFSG.LieType.Steinberg
