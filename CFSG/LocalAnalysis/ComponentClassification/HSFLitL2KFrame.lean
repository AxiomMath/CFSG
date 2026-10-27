module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KAct
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldClass

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Glauberman.Dickson (h826_pglMap h826_pglMap_mk h826_pglMap_injective)

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem eq_one_of_lang {σ : F ≃+* F} (hσσ : ∀ x, σ (σ x) = x) (h2 : (2 : F) ≠ 0)
    {K₀ : Subfield F} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) {x y : PSL2 F}
    (hy : y ∈ (psl2Sub K₀).range) (hxy : x * (psl2FieldAut F σ x)⁻¹ = y) : y = 1 := by
  obtain ⟨w, rfl⟩ := hy
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨W, rfl⟩ := QuotientGroup.mk_surjective w
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hxy
  rw [map_mul, map_inv, psl2FieldAut_toPGL, toPGL_psl2Sub,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
    h826_pglMap_mk, pgl2FieldAut_mk, mul_inv_eq_iff_eq_mul, ← map_mul] at h1
  have hB := pgl_eq_one_of_lang hσσ h2 (Matrix.SpecialLinearGroup.toGL X)
    (Matrix.GeneralLinearGroup.map K₀.subtype (Matrix.SpecialLinearGroup.toGL W))
    (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact X.2)
    (by
      change (K₀.subtype.mapMatrix (W : Matrix (Fin 2) (Fin 2) K₀)).det = 1
      rw [← RingHom.map_det, W.2, map_one])
    (fun i j => (hK₀ _).mp (Subtype.mem _)) h1
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [map_one, toPGL_psl2Sub, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, h826_pglMap_mk, hB]

theorem conj_inr_eq {σ : F ≃+* F} {x : PGammaL2 F} {h : PSL2 F}
    (hx : x.left = Matrix.ProjectiveSpecialLinearGroup.toPGL h) :
    x * SemidirectProduct.inr σ * x⁻¹ =
      incl F (h * (psl2FieldAut F σ h)⁻¹) * SemidirectProduct.inr σ := by
  have hσincl : ∀ w : PSL2 F, (SemidirectProduct.inr σ : PGammaL2 F) * incl F w =
      incl F (psl2FieldAut F σ w) * SemidirectProduct.inr σ := by
    intro w
    have := conj_incl (SemidirectProduct.inr σ) w
    rw [semilinearAction_inr] at this
    rw [← this]
    group
  have hx' : x = incl F h * SemidirectProduct.inr x.right := by
    rw [incl_apply, ← hx]
    exact (SemidirectProduct.inl_left_mul_inr_right x).symm
  rw [hx', mul_inv_rev, ← map_inv, ← map_inv (incl F) h]
  have hcomm : (SemidirectProduct.inr x.right : PGammaL2 F) * SemidirectProduct.inr σ *
      SemidirectProduct.inr x.right⁻¹ = SemidirectProduct.inr σ := by
    rw [← map_mul, ← map_mul, ringAut_comm x.right σ, mul_assoc, mul_inv_cancel, mul_one]
  calc incl F h * SemidirectProduct.inr x.right * SemidirectProduct.inr σ *
        (SemidirectProduct.inr x.right⁻¹ * incl F h⁻¹)
      = incl F h * (SemidirectProduct.inr x.right * SemidirectProduct.inr σ *
          SemidirectProduct.inr x.right⁻¹) * incl F h⁻¹ := by group
    _ = incl F h * (SemidirectProduct.inr σ * incl F h⁻¹) := by rw [hcomm, mul_assoc]
    _ = incl F (h * (psl2FieldAut F σ h)⁻¹) * SemidirectProduct.inr σ := by
      rw [hσincl, map_inv, ← mul_assoc, map_mul, map_inv]

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}

structure Frame (A : L2Data t L) (F : Type) [Field F] [Finite F] (κ : X) where
  κ_mem : κ ∈ A.T
  κ_sq : κ ^ 2 = 1
  κ_comm : ∀ r ∈ A.R, κ * r = r * κ
  ψ_κ : ψX A κ ∉ R8
  e : L ⧸ pPrimeCore 2 L ≃* PSL2 F
  σ : F ≃+* F
  orderOf_σ : orderOf σ = 2
  act_κ : act A e κ = SemidirectProduct.inr σ
  odd : IsOddPrimePower (Nat.card F)
  K₀ : Subfield F
  mem_K₀ : ∀ x, x ∈ K₀ ↔ σ x = x
  card_F : Nat.card F = Nat.card K₀ ^ 2
  h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c

theorem nonempty_frame (e₀ : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (S : Gens A) {κ : X}
    (hκ : κ ∈ A.T) (hκ2 : κ ^ 2 = 1) (hκR : ∀ r ∈ A.R, κ * r = r * κ) (hψκ : ψX A κ ∉ R8) :
    Nonempty (Frame A F κ) := by
  obtain ⟨e, σ, hσ, hact⟩ := exists_frame e₀ S hκ hκ2 hκR hψκ
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  exact ⟨⟨hκ, hκ2, hκR, hψκ, e, σ, hσ, hact, isOddPrimePower_card e₀ S, K₀, hK₀, hcard, h90⟩⟩

namespace Frame

variable {κ : X} (Fr : Frame A F κ)

theorem σσ (x : F) : Fr.σ (Fr.σ x) = x := by
  have h1 : Fr.σ * Fr.σ = 1 := by rw [← pow_two, ← Fr.orderOf_σ, pow_orderOf_eq_one]
  have := congrArg (fun τ : F ≃+* F => τ x) h1
  simpa using this

include Fr in
theorem two_ne_zero : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower Fr.odd

theorem K₀_odd : IsOddPrimePower (Nat.card Fr.K₀) := by
  apply isOddPrimePower_of_odd_card
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := Fr.odd
    rw [hc]
    exact hpodd.pow
  rw [Fr.card_F] at hFodd
  exact Nat.Odd.of_mul_left (by rwa [← pow_two])

include Fr in
theorem κ_C : κ ∈ centralizer ({t} : Set X) := A.T_le_centralizer Fr.κ_mem

theorem rho_mem_fieldCent {r : X} (hr : r ∈ A.R) : rho Fr.e r ∈ fieldCent Fr.σ := by
  have h := act_comm_incl Fr.e Fr.κ_C hr (Fr.κ_comm r hr)
  rw [Fr.act_κ, commute_incl_iff, semilinearAction_inr] at h
  exact h

theorem card_fieldCent : Nat.card (fieldCent Fr.σ) = 2 * Nat.card (PSL2 Fr.K₀) := by
  rw [card_fieldCent_eq Fr.mem_K₀ Fr.h90 Fr.σσ Fr.card_F Fr.odd, pgl2_card_eq_two_mul Fr.K₀_odd]

theorem index_range_psl2Sub :
    ((psl2Sub Fr.K₀).range.subgroupOf (fieldCent Fr.σ)).index = 2 := by
  have hle : (psl2Sub Fr.K₀).range ≤ fieldCent Fr.σ := by
    rintro _ ⟨x, rfl⟩
    exact psl2Sub_mem_fieldCent Fr.mem_K₀ x
  have h1 := ((psl2Sub Fr.K₀).range.subgroupOf (fieldCent Fr.σ)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (psl2Sub_injective Fr.K₀)).toEquiv,
    Fr.card_fieldCent] at h1
  have hpos : 0 < Nat.card (PSL2 Fr.K₀) := Nat.card_pos
  have h2 : Nat.card (PSL2 Fr.K₀) * ((psl2Sub Fr.K₀).range.subgroupOf (fieldCent Fr.σ)).index =
      Nat.card (PSL2 Fr.K₀) * 2 := by rw [h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem mul_mem_range_iff {a b : PSL2 F} (ha : a ∈ fieldCent Fr.σ) (hb : b ∈ fieldCent Fr.σ) :
    a * b ∈ (psl2Sub Fr.K₀).range ↔
      (a ∈ (psl2Sub Fr.K₀).range ↔ b ∈ (psl2Sub Fr.K₀).range) := by
  have h := Subgroup.mul_mem_iff_of_index_two Fr.index_range_psl2Sub (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa only [mem_subgroupOf, Subgroup.coe_mul] using h

omit [Finite F] in
include A in
theorem factorization_card_psl2 (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) :
    (Nat.card (PSL2 F)).factorization 2 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := A.config.exists_sylow
  have h := Sylow.card_eq_multiplicity P
  rw [hP] at h
  rw [← Nat.card_congr e.toEquiv]
  have h8 : (2 : ℕ) ^ 3 = 2 ^ (Nat.card (L ⧸ pPrimeCore 2 L)).factorization 2 := by
    rw [← h]
    norm_num
  exact (Nat.pow_right_injective le_rfl h8).symm

theorem factorization_card_psl2_K₀ : (Nat.card (PSL2 Fr.K₀)).factorization 2 ≤ 2 := by
  have hdvd : 2 * Nat.card (PSL2 Fr.K₀) ∣ Nat.card (PSL2 F) := by
    rw [← Fr.card_fieldCent]
    exact Subgroup.card_subgroup_dvd_card _
  have hpos : Nat.card (PSL2 Fr.K₀) ≠ 0 := Nat.card_pos.ne'
  have h := (Nat.factorization_le_iff_dvd (by positivity) Nat.card_pos.ne').mpr hdvd 2
  rw [Nat.factorization_mul (by norm_num) hpos, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, factorization_card_psl2 (A := A) Fr.e] at h
  omega

theorem card_le_four {Q : Subgroup (PSL2 Fr.K₀)} (hQ : IsPGroup 2 Q) : Nat.card Q ≤ 4 := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ n ∣ Nat.card (PSL2 Fr.K₀) := hn ▸ Subgroup.card_subgroup_dvd_card Q
  have hn2 : n ≤ 2 := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
    have := Fr.factorization_card_psl2_K₀
    omega
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

theorem sq_eq_one_dihedralTwo : ∀ g : DihedralGroup 2, g ^ 2 = 1 := by decide

theorem orderOf_ne_four (w : PSL2 Fr.K₀) : orderOf w ≠ 4 := by
  intro hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw2 : IsPGroup 2 (zpowers w) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hw]; norm_num)
  obtain ⟨S, hS⟩ := hw2.exists_le_sylow
  obtain ⟨m, hm, ⟨φ⟩⟩ := psl2_odd_hasDihedralSylowTwo_model Fr.K₀ Fr.K₀_odd S
  have hle := Fr.card_le_four S.isPGroup'
  have hcard : Nat.card S = 2 * 2 ^ m := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hm1 : m = 1 := by
    have : 2 ^ m ≤ 2 := by omega
    have h2 : 2 ^ m ≤ 2 ^ 1 := by simpa using this
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  subst hm1
  have hwS : w ∈ (S : Subgroup (PSL2 Fr.K₀)) := hS (mem_zpowers w)
  have h1 : φ ⟨w, hwS⟩ ^ 2 = 1 := sq_eq_one_dihedralTwo _
  have h2 : (⟨w, hwS⟩ : S) ^ 2 = 1 := by
    rw [← map_pow, ← map_one φ] at h1
    exact φ.injective h1
  have h3 : w ^ 2 = 1 := congrArg Subtype.val h2
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hw] at this
  norm_num at this

@[expose] def V : Subgroup X :=
  ((psl2Sub Fr.K₀).range.comap (rhoL Fr.e)).map L.subtype ⊓ A.R

theorem mem_V {g : X} : g ∈ Fr.V ↔ g ∈ A.R ∧ rho Fr.e g ∈ (psl2Sub Fr.K₀).range := by
  constructor
  · rintro ⟨⟨l, hl, rfl⟩, hR⟩
    refine ⟨hR, ?_⟩
    have hl' : rhoL Fr.e l ∈ (psl2Sub Fr.K₀).range := hl
    rw [rhoL_apply] at hl'
    exact hl'
  · rintro ⟨hR, hm⟩
    refine ⟨⟨⟨g, hR.2⟩, ?_, rfl⟩, hR⟩
    show rhoL Fr.e ⟨g, hR.2⟩ ∈ (psl2Sub Fr.K₀).range
    rw [rhoL_apply]
    exact hm

theorem V_le_R : Fr.V ≤ A.R := inf_le_right

theorem mul_mem_V_iff {r s : X} (hr : r ∈ A.R) (hs : s ∈ A.R) :
    r * s ∈ Fr.V ↔ (r ∈ Fr.V ↔ s ∈ Fr.V) := by
  rw [Fr.mem_V, Fr.mem_V, Fr.mem_V, rho_mul Fr.e hr.2 hs.2,
    Fr.mul_mem_range_iff (Fr.rho_mem_fieldCent hr) (Fr.rho_mem_fieldCent hs)]
  simp only [mul_mem hr hs, hr, hs, true_and]

theorem orderOf_rho_x₀ (S : Gens A) : orderOf (rho Fr.e S.x₀) = 4 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, ← rho_pow Fr.e S.x₀_mem.2]
    intro h
    exact S.z_ne_one (rho_eq_one Fr.e S.z_mem h)
  · rw [show (2 : ℕ) ^ (1 + 1) = 4 by rfl, ← rho_pow Fr.e S.x₀_mem.2, S.x₀_pow_four, rho_one]

theorem x₀_not_mem_V (S : Gens A) : S.x₀ ∉ Fr.V := by
  intro h
  obtain ⟨w, hw⟩ := (Fr.mem_V.mp h).2
  apply Fr.orderOf_ne_four w
  rw [← orderOf_injective (psl2Sub Fr.K₀) (psl2Sub_injective Fr.K₀), hw, Fr.orderOf_rho_x₀ S]

theorem z_mem_V (S : Gens A) : S.z ∈ Fr.V := by
  rw [Gens.z, pow_two, Fr.mul_mem_V_iff S.x₀_mem S.x₀_mem]

theorem card_V_le : Nat.card Fr.V ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup (PSL2 Fr.K₀) := ((Fr.V.subgroupOf L).map (rhoL Fr.e)).comap (psl2Sub Fr.K₀)
    with hQ
  have hVL : Fr.V ≤ L := Fr.V_le_R.trans inf_le_right
  have hV2 : IsPGroup 2 Fr.V := A.isPGroup_T.to_le (Fr.V_le_R.trans inf_le_left)
  have hQ2 : IsPGroup 2 Q :=
    ((hV2.comap_of_injective L.subtype (subtype_injective L)).map _).comap_of_injective _
      (psl2Sub_injective Fr.K₀)
  have hcard : Nat.card Fr.V ≤ Nat.card Q := by
    refine Nat.card_le_card_of_injective (fun v => ⟨Classical.choose (Fr.mem_V.mp v.2).2, ?_⟩)
      (fun v₁ v₂ h => ?_)
    · rw [hQ, mem_comap, Classical.choose_spec (Fr.mem_V.mp v.2).2]
      exact ⟨⟨v, hVL v.2⟩, v.2, rhoL_apply _ _⟩
    · have h' := congrArg (psl2Sub Fr.K₀) (congrArg Subtype.val h)
      simp only [Classical.choose_spec (Fr.mem_V.mp v₁.2).2,
        Classical.choose_spec (Fr.mem_V.mp v₂.2).2] at h'
      exact Subtype.ext (rho_injective Fr.e (Fr.V_le_R v₁.2) (Fr.V_le_R v₂.2) h')
  exact hcard.trans (Fr.card_le_four hQ2)

theorem V_eq (S : Gens A) : ∃ w : X, (w = S.y₀ ∨ w = S.x₀ * S.y₀) ∧ w ∈ Fr.V ∧
    Nat.card Fr.V = 4 ∧ ∀ v, v ∈ Fr.V ↔ v = 1 ∨ v = S.z ∨ v = w ∨ v = S.z * w := by
  have hx := Fr.x₀_not_mem_V S
  have hz := Fr.z_mem_V S
  obtain ⟨w, hw, hwV⟩ : ∃ w : X, (w = S.y₀ ∨ w = S.x₀ * S.y₀) ∧ w ∈ Fr.V := by
    by_cases hy : S.y₀ ∈ Fr.V
    · exact ⟨S.y₀, Or.inl rfl, hy⟩
    · refine ⟨S.x₀ * S.y₀, Or.inr rfl, ?_⟩
      rw [Fr.mul_mem_V_iff S.x₀_mem S.y₀_mem]
      exact iff_of_false hx hy
  have hwR : w ∈ A.R := Fr.V_le_R hwV
  have hw2 : w ^ 2 = 1 := by
    rcases hw with rfl | rfl
    exacts [S.y₀_sq, S.xy_sq]
  have hψw : ψX A w = y8 ∨ ψX A w = x8 * y8 := by
    rcases hw with rfl | rfl
    · exact Or.inl S.ψ_y₀
    · exact Or.inr S.ψ_xy
  have hw1 : w ≠ 1 := fun h => by
    rcases hψw with h' | h' <;> rw [h, ψX_one] at h'
    exacts [y8_ne_one h'.symm, x8_mul_y8_ne_one h'.symm]
  have hwz : w ≠ S.z := fun h => by
    rcases hψw with h' | h' <;> rw [h, S.ψ_z] at h'
    exacts [y8_ne_z8 h'.symm, x8_mul_y8_ne_z8 h'.symm]
  have hzE : ElemAbelianTwo (zpowers S.z) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rcases eq_one_or_eq_of_mem_zpowers S.z_sq ha with rfl | rfl <;>
        rcases eq_one_or_eq_of_mem_zpowers S.z_sq hb with rfl | rfl <;> simp
    · rcases eq_one_or_eq_of_mem_zpowers S.z_sq ha with rfl | rfl
      · exact one_pow 2
      · exact S.z_sq
  have hwnot : w ∉ zpowers S.z := fun h =>
    (eq_one_or_eq_of_mem_zpowers S.z_sq h).elim hw1 hwz
  obtain ⟨-, hmem, hcard⟩ := hzE.sup_zpowers hw2 hwnot (fun a ha => by
    rcases eq_one_or_eq_of_mem_zpowers S.z_sq ha with rfl | rfl
    · simp
    · exact (S.z_comm_R hwR).symm)
  rw [Nat.card_zpowers, orderOf_eq_prime S.z_sq S.z_ne_one] at hcard
  have hle : zpowers S.z ⊔ zpowers w ≤ Fr.V := sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hwV)
  have heq : zpowers S.z ⊔ zpowers w = Fr.V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact Fr.card_V_le)
  have hwinv : w⁻¹ = w := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hw2]
  refine ⟨w, hw, hwV, heq ▸ hcard, fun v => ?_⟩
  rw [← heq]
  constructor
  · intro hv
    rcases hmem v hv with h | h
    · rcases eq_one_or_eq_of_mem_zpowers S.z_sq h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases eq_one_or_eq_of_mem_zpowers S.z_sq h with h' | h'
      · refine Or.inr (Or.inr (Or.inl ?_))
        calc v = v * w * w⁻¹ := by group
          _ = w := by rw [h', one_mul, hwinv]
      · refine Or.inr (Or.inr (Or.inr ?_))
        calc v = v * w * w⁻¹ := by group
          _ = S.z * w := by rw [h', hwinv]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem eq_one_of_conj (C : A.CaseK) (S : Gens A) {n v : X}
    (hn : n ∈ centralizer ({t} : Set X)) (hv : v ∈ Fr.V) (c : ℕ)
    (h : n * κ * n⁻¹ = v * t ^ c * κ) : v = 1 := by
  have hvR := Fr.V_le_R hv
  have hvC := L_le_C (A := A) hvR.2
  have h1 := congrArg (act A Fr.e) h
  rw [act_conj Fr.e hn Fr.κ_C, act_mul Fr.e (mul_mem hvC (pow_mem t_mem_C c)) Fr.κ_C,
    act_mul Fr.e hvC (pow_mem t_mem_C c), act_pow Fr.e t_mem_C, act_t, one_pow, mul_one,
    Fr.act_κ, act_of_mem_L Fr.e hvR.2] at h1
  obtain ⟨y, hy⟩ := sqLeft_act Fr.e C S hn
  rw [conj_inr_eq hy.symm, mul_left_inj] at h1
  have h2 := incl_injective F h1
  have h3 := eq_one_of_lang Fr.σσ Fr.two_ne_zero Fr.mem_K₀ (Fr.mem_V.mp hv).2 h2
  exact rho_eq_one Fr.e hvR h3

end Frame

end CFSG.ComponentClassification.HSFLit.L2K
