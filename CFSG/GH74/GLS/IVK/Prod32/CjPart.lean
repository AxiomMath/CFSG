module

public import CFSG.GH74.GLS.IVK.Prod32.Out

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.GH74.GLS.IVK.Lifted (slFieldAut gammaOf exists_rep slFieldAut_apply mem_fixedSubgroup_slFieldAut
  fixedEquivSL isQuasisimple_sl2' sl2_no_central_sylow)
open CFSG.GH74.GLS.IVK (fixedField odd_card_fixedField fixedField_card_pow)

namespace CjAux

section PureAut

variable {F : Type} [Field F]

theorem uSL_one_fixed (σ : F ≃+* F) : ∀ i j, σ ((uSL (1 : F) : SpecialLinearGroup (Fin 2) F) i j) =
    (uSL (1 : F) : SpecialLinearGroup (Fin 2) F) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem vSL_one_fixed (σ : F ≃+* F) : ∀ i j, σ ((vSL (1 : F) : SpecialLinearGroup (Fin 2) F) i j) =
    (vSL (1 : F) : SpecialLinearGroup (Fin 2) F) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [vSL]

def wSL (t : F) : SpecialLinearGroup (Fin 2) F := ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem wSL_fixed {σ : F ≃+* F} {t : F} (ht : σ t = t) :
    ∀ i j, σ ((wSL t : SpecialLinearGroup (Fin 2) F) i j) = (wSL t : SpecialLinearGroup (Fin 2) F) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [wSL, ht]

theorem eq_one_or_eq_of_forall (τ σ : F ≃+* F) (h : ∀ x, τ x = x ∨ τ x = σ x) :
    τ = 1 ∨ τ = σ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, τ x₀ ≠ x₀ := by
    by_contra hh
    push Not at hh
    exact h1 (RingEquiv.ext hh)
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, τ x₁ ≠ σ x₁ := by
    by_contra hh
    push Not at hh
    exact h2 (RingEquiv.ext hh)
  have hx₀' : τ x₀ = σ x₀ := (h x₀).resolve_left hx₀
  have hx₁' : τ x₁ = x₁ := (h x₁).resolve_right hx₁
  rcases h (x₀ + x₁) with hy | hy
  · rw [map_add, hx₀', hx₁'] at hy
    have : σ x₀ = x₀ := add_right_cancel hy
    exact hx₀ (hx₀'.trans this)
  · rw [map_add, map_add, hx₀', hx₁'] at hy
    have : x₁ = σ x₁ := add_left_cancel hy
    exact hx₁ (hx₁'.trans this)

end PureAut

section MainAut

variable {F : Type} [Field F] [Finite F]

theorem aut_eq_one_or_field (hF : GoodF F) {σ : F ≃+* F} (hσ : ∀ x, σ (σ x) = x)
    (ψ : MulAut (SpecialLinearGroup (Fin 2) F))
    (hψ : ∀ b : SpecialLinearGroup (Fin 2) F, (∀ i j, σ (b i j) = b i j) → ψ b = b) :
    ψ = 1 ∨ ψ = slFieldAut σ := by
  obtain ⟨G, hG⟩ := exists_rep hF.odd hF.gt3 ψ
  set τ : F ≃+* F := (gammaOf hF.odd hF.gt3 ψ).right with hτ
  have hu' := hG (uSL 1)
  rw [hψ _ (uSL_one_fixed σ)] at hu'
  have hv' := hG (vSL 1)
  rw [hψ _ (vSL_one_fixed σ)] at hv'
  have hmapu : GeneralLinearGroup.map (τ : F →+* F) (SpecialLinearGroup.toGL (uSL (1 : F))) =
      SpecialLinearGroup.toGL (uSL (1 : F)) := by
    apply Units.ext
    rw [map_toGL_uSL, map_one]
    rfl
  have hmapv : GeneralLinearGroup.map (τ : F →+* F) (SpecialLinearGroup.toGL (vSL (1 : F))) =
      SpecialLinearGroup.toGL (vSL (1 : F)) := by
    apply Units.ext
    rw [map_toGL_vSL, map_one]
    rfl
  rw [hmapu] at hu'
  rw [hmapv] at hv'
  have hcu : SpecialLinearGroup.toGL (uSL (1 : F)) * G = G * SpecialLinearGroup.toGL (uSL (1 : F)) := by
    calc SpecialLinearGroup.toGL (uSL (1 : F)) * G
        = (G * SpecialLinearGroup.toGL (uSL (1 : F)) * G⁻¹) * G := by rw [← hu']
      _ = G * SpecialLinearGroup.toGL (uSL (1 : F)) := by group
  have hcv : SpecialLinearGroup.toGL (vSL (1 : F)) * G = G * SpecialLinearGroup.toGL (vSL (1 : F)) := by
    calc SpecialLinearGroup.toGL (vSL (1 : F)) * G
        = (G * SpecialLinearGroup.toGL (vSL (1 : F)) * G⁻¹) * G := by rw [← hv']
      _ = G * SpecialLinearGroup.toGL (vSL (1 : F)) := by group
  have eu : ((SpecialLinearGroup.toGL (uSL (1 : F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 0, 1] := rfl
  have ev : ((SpecialLinearGroup.toGL (vSL (1 : F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; 1, 1] := rfl
  obtain ⟨μ, hμ⟩ := scalar_of_commute_two (G : Matrix (Fin 2) (Fin 2) F)
    (by
      have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hcu
      simp only [Units.val_mul, eu] at this
      exact this.symm)
    (by
      have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hcv
      simp only [Units.val_mul, ev] at this
      exact this.symm)
  have hGc : ∀ X : GL (Fin 2) F, G * X = X * G := by
    intro X
    apply Units.ext
    simp only [Units.val_mul]
    rw [hμ]
    simp
  have hψτ : ∀ b, ψ b = slFieldAut τ b := by
    intro b
    apply SpecialLinearGroup.toGL_injective
    rw [hG b, slFieldAut_apply, CFSG.Semidihedral.MatrixCoverData.toGL_field_map, hGc, mul_assoc,
      mul_inv_cancel, mul_one]
    rfl
  have hτfix : ∀ t : F, σ t = t → τ t = t := by
    intro t ht
    have h1 : ψ (wSL t) = wSL t := hψ _ (wSL_fixed ht)
    rw [hψτ, slFieldAut_apply] at h1
    have h2 := congrArg (fun S : SpecialLinearGroup (Fin 2) F => (S : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    exact h2
  have hxx : ∀ x : F, τ x = x ∨ τ x = σ x := by
    intro x
    have hs : σ (x + σ x) = x + σ x := by rw [map_add, hσ, add_comm]
    have hp : σ (x * σ x) = x * σ x := by rw [map_mul, hσ, mul_comm]
    have ht1 := hτfix _ hs
    have ht2 := hτfix _ hp
    have h0 : x * x - (x + σ x) * x + x * σ x = 0 := by ring
    have e : τ (x * x - (x + σ x) * x + x * σ x) = τ x * τ x - (x + σ x) * τ x + x * σ x := by
      rw [map_add, map_sub, ht2, map_mul, map_mul, ht1]
    rw [h0, map_zero] at e
    have : (τ x - x) * (τ x - σ x) = 0 := by linear_combination -e
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  rcases eq_one_or_eq_of_forall τ σ hxx with h | h
  · left
    ext b : 1
    rw [hψτ, h]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  · right
    ext b : 1
    rw [hψτ, h]

end MainAut

section Factor

variable {H : Type} [Group H] {K : Subgroup H} {a : H} {F : Type} [Field F] [Finite F]
  {ê : ↥K ≃* SpecialLinearGroup (Fin 2) F} {σ : F ≃+* F}

theorem map_cen_eq (hact : SLAct K a ê σ) :
    ((K ⊓ centralizer ({a} : Set H)).subgroupOf K).map ê.toMonoidHom =
      CFSG.GH74.GLS.fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slFieldAut σ) := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxa : (x : H) * a = a * (x : H) := Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2
    have hxn := hact.norm x x.2
    have h1 := hact.act x hxn
    have h2 : a * (x : H) * a⁻¹ = x := by rw [← hxa]; group
    have h3 : (⟨a * (x : H) * a⁻¹, hxn⟩ : ↥K) = x := Subtype.ext h2
    rw [h3] at h1
    exact h1.symm
  · intro hb
    refine ⟨ê.symm b, ?_, by simp⟩
    have hb' : slFieldAut σ b = b := hb
    have hxn := hact.norm (ê.symm b : ↥K) (ê.symm b).2
    have h1 := hact.act (ê.symm b) hxn
    rw [MulEquiv.apply_symm_apply, hb'] at h1
    have h3 : (⟨a * ((ê.symm b : ↥K) : H) * a⁻¹, hxn⟩ : ↥K) = ê.symm b := by
      apply ê.injective
      rw [h1, MulEquiv.apply_symm_apply]
    have h4 : a * ((ê.symm b : ↥K) : H) * a⁻¹ = (ê.symm b : ↥K) := congrArg Subtype.val h3
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(ê.symm b).2, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((ê.symm b : ↥K) : H) * a = (a * ((ê.symm b : ↥K) : H) * a⁻¹) * a := by rw [h4]
      _ = a * ((ê.symm b : ↥K) : H) := by group

theorem nonempty_cen_equiv (hact : SLAct K a ê σ) :
    Nonempty (↥(K ⊓ centralizer ({a} : Set H)) ≃* SpecialLinearGroup (Fin 2) ↥(fixedField σ)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
    ((MulEquiv.subgroupMap ê _).trans ((MulEquiv.subgroupCongr (map_cen_eq hact)).trans
      (fixedEquivSL σ)))⟩

end Factor

section CenConj

variable {H : Type} [Group H]

theorem conj_mem_cen {K : Subgroup H} {a m : H} (hm : ∀ y ∈ K, m * y * m⁻¹ ∈ K)
    (hma : m * a = a * m) {x : H} (hx : x ∈ K ⊓ centralizer ({a} : Set H)) :
    m * x * m⁻¹ ∈ K ⊓ centralizer ({a} : Set H) := by
  refine Subgroup.mem_inf.2 ⟨hm x (Subgroup.mem_inf.1 hx).1, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hwa' : m * a * m⁻¹ = a := by rw [hma]; group
  have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
  calc m * x * m⁻¹ * a = m * x * m⁻¹ * (m * a * m⁻¹) := by rw [hwa']
    _ = m * (x * a) * m⁻¹ := by group
    _ = m * (a * x) * m⁻¹ := by rw [hxa]
    _ = (m * a * m⁻¹) * (m * x * m⁻¹) := by group
    _ = a * (m * x * m⁻¹) := by rw [hwa']

end CenConj

section FactorMain

variable {H : Type} [Group H] [Finite H] {K : Subgroup H} {a w : H} {F : Type} [Field F] [Finite F]
  {ê : ↥K ≃* SpecialLinearGroup (Fin 2) F} {σ : F ≃+* F}

theorem factor_dichotomy (hF : GoodF F) (hact : SLAct K a ê σ) (hσ : σ * σ = 1)
    (hF0 : 3 < Nat.card ↥(fixedField σ)) (hwK : ∀ y ∈ K, w * y * w⁻¹ ∈ K) (hwa : w * a = a * w)
    (hw2 : ∃ m : ℕ, w ^ 2 ^ m = 1) {Q : Subgroup H}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (K ⊓ centralizer ({a} : Set H)))
    (hwQ : ∀ q ∈ Q, w * q = q * w) :
    (∀ y ∈ K, w * y * w⁻¹ = y) ∨ (∀ y ∈ K, w * y * w⁻¹ = a * y * a⁻¹) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup H := K ⊓ centralizer ({a} : Set H) with hXdef
  have hwN : w ∈ normalizer (K : Set H) := mem_normalizer_of_conj_le hwK
  have hσ' : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun e : F ≃+* F => e x) hσ
    simpa using this
  have hwX' : ∀ x ∈ X, w * x * w⁻¹ ∈ X := fun x hx => conj_mem_cen hwK hwa hx
  have hwX : w ∈ normalizer (X : Set H) := mem_normalizer_of_conj_le hwX'
  set φ : MulAut ↥X := X.normalizerMonoidHom ⟨w, hwX⟩ with hφdef
  have hφc : ∀ x : ↥X, ((φ x : ↥X) : H) = w * x * w⁻¹ := fun x => rfl
  obtain ⟨m, hm⟩ := hw2
  have hφm : φ ^ 2 ^ m = 1 := by
    ext x
    have hpow : ∀ n : ℕ, (((φ ^ n) x : ↥X) : H) = w ^ n * x * (w ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, hφc, ih, pow_succ']
        group
    rw [hpow, hm]
    simp
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hφm)
  obtain ⟨P, hP⟩ := hQ.exists_sylow_eq_subgroupOf
  have hfix : ∀ p ∈ (P : Subgroup ↥X), φ p = p := by
    intro p hp
    rw [hP] at hp
    apply Subtype.ext
    rw [hφc]
    have := hwQ (p : H) (Subgroup.mem_subgroupOf.1 hp)
    calc w * (p : H) * w⁻¹ = (p : H) * w * w⁻¹ := by rw [this]
      _ = p := by group
  obtain ⟨eX⟩ := nonempty_cen_equiv hact
  have hodd0 : Odd (Nat.card ↥(fixedField σ)) := odd_card_fixedField σ hF.odd
  have hq : CFSG.IsQuasisimple ↥X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm (isQuasisimple_sl2' (by omega))
  have hno : ∀ u v : ↥X, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v := by
    intro u v hu hv _
    have h2 : (2 : ↥(fixedField σ)) ≠ 0 :=
      CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hodd0
    have h1 : eX u = eX v := by
      have hu' := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff _ h2 (eX u)).1
        (by rw [MulEquiv.orderOf_eq]; exact hu)
      have hv' := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff _ h2 (eX v)).1
        (by rw [MulEquiv.orderOf_eq]; exact hv)
      rw [hu', hv']
    exact eX.injective h1
  have hφ1 : φ = 1 := sl2_no_central_sylow hodd0 hF0 eX hq hno φ hk P hfix
  have hwcX : ∀ x ∈ X, w * x * w⁻¹ = x := by
    intro x hx
    have := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : H)) hφ1
    simpa [hφc] using this
  set ψ : MulAut (SpecialLinearGroup (Fin 2) F) :=
    MulAut.congr ê (K.normalizerMonoidHom ⟨w, hwN⟩) with hψdef
  have hψc : ∀ y : ↥K, ψ (ê y) = ê ⟨w * (y : H) * w⁻¹, hwK y y.2⟩ := by
    intro y
    rw [hψdef, congr_apply_eq, MulEquiv.symm_apply_apply]
    rfl
  have hψfix : ∀ b : SpecialLinearGroup (Fin 2) F, (∀ i j, σ (b i j) = b i j) → ψ b = b := by
    intro b hb
    have hb' : slFieldAut σ b = b := (mem_fixedSubgroup_slFieldAut σ b).2 hb
    set x : ↥K := ê.symm b with hx
    have hxn := hact.norm x x.2
    have h1 := hact.act x hxn
    have h2 : ê x = b := by rw [hx, MulEquiv.apply_symm_apply]
    rw [h2, hb'] at h1
    have h3 : (⟨a * (x : H) * a⁻¹, hxn⟩ : ↥K) = x := by
      apply ê.injective
      rw [h1, h2]
    have h4 : a * (x : H) * a⁻¹ = x := congrArg Subtype.val h3
    have hxX : (x : H) ∈ X := Subgroup.mem_inf.2 ⟨x.2, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : H) * a = (a * (x : H) * a⁻¹) * a := by rw [h4]
        _ = a * (x : H) := by group⟩
    have h5 := hwcX (x : H) hxX
    rw [← h2, hψc]
    congr 1
    exact Subtype.ext h5
  rcases aut_eq_one_or_field hF hσ' ψ hψfix with h1 | h1
  · left
    intro y hy
    have h2 := congrArg (fun f : MulAut (SpecialLinearGroup (Fin 2) F) => f (ê ⟨y, hy⟩)) h1
    simp only [MulAut.one_apply] at h2
    rw [hψc] at h2
    exact congrArg Subtype.val (ê.injective h2)
  · right
    intro y hy
    have h2 : ψ (ê ⟨y, hy⟩) = slFieldAut σ (ê ⟨y, hy⟩) := by rw [h1]
    rw [hψc, ← hact.act ⟨y, hy⟩ (hact.norm y hy)] at h2
    exact congrArg Subtype.val (ê.injective h2)

end FactorMain

section Final

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}

theorem hyp_a_mul_a (h : Hyp H K₁ K₂ z T a) : a * a = 1 := by
  have := pow_orderOf_eq_one a
  rwa [h.a_ord, sq] at this

theorem sigma_facts {K : Subgroup H} {F : Type} [Field F] [Finite F]
    {ê : ↥K ≃* SpecialLinearGroup (Fin 2) F} {σ : F ≃+* F} (haa : a * a = 1) (hF : GoodF F)
    (hact : SLAct K a ê σ) (hnt : ¬ ∀ x ∈ K, a * x * a⁻¹ = x) : σ * σ = 1 ∧ σ ≠ 1 := by
  have ha : a ∈ normalizer (K : Set H) := mem_normalizer_of_conj_le hact.norm
  have h1 := coordHom_slAct hF hact ha
  constructor
  · have h2 : coordHom K ê hF (⟨a, ha⟩ * ⟨a, ha⟩) = 1 := by
      have : (⟨a, ha⟩ * ⟨a, ha⟩ : ↥(normalizer (K : Set H))) = 1 := Subtype.ext haa
      rw [this, map_one]
    rw [map_mul, h1] at h2
    exact (Prod.ext_iff.1 h2).2
  · intro hσ1
    apply hnt
    subst hσ1
    intro y hy
    have h3 := hact.act ⟨y, hy⟩ (hact.norm y hy)
    have : slFieldAut (1 : F ≃+* F) (ê ⟨y, hy⟩) = ê ⟨y, hy⟩ := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rfl
    rw [this] at h3
    exact congrArg Subtype.val (ê.injective h3)

omit [Finite H] in
theorem card_eq_of_model {K : Subgroup H} {F : Type} [Field F] [Finite F]
    (ê : ↥K ≃* SpecialLinearGroup (Fin 2) F) {m : ℕ} (h : HasSL2Model ↥K (fun q => q = m)) :
    Nat.card F = m := by
  obtain ⟨F', _, _, hq, ⟨e'⟩⟩ := h
  have := card_eq_of_sl2_equiv ((ê.trans (specialLinearGroupEquivStatedSL 2 F)).symm.trans e')
  rw [this]
  exact hq

theorem inf_centralizer_eq {K K' : Subgroup H} (hT : IsPGroup 2 T)
    (hcomm : ∀ u ∈ K, ∀ y ∈ K', u * y = y * u)
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K') (centralizer (K : Set H))) :
    T ⊓ centralizer (K : Set H) = T ⊓ K' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hP.eq_of_le (P := T ⊓ K') (Q := T ⊓ centralizer (K : Set H)) (K := centralizer (K : Set H))
    (fun y hy => ⟨hy.1, fun u hu => hcomm u hu y hy.2⟩) inf_le_right hT.to_inf_left

theorem mem_zpowers_of_cent (hS : Setting H K₁ K₂ z) {u : H} (h1 : ∀ y ∈ K₁, u * y * u⁻¹ = y)
    (h2 : ∀ y ∈ K₂, u * y * u⁻¹ = y) : u ∈ zpowers z := by
  have hcomm1 : ∀ y ∈ K₁, y * u = u * y := fun y hy => (mul_inv_eq_iff_eq_mul.1 (h1 y hy)).symm
  have hcomm2 : ∀ y ∈ K₂, y * u = u * y := fun y hy => (mul_inv_eq_iff_eq_mul.1 (h2 y hy)).symm
  have hcent : u ∈ centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := (mem_sup_of_comm hS.comm m).mp hm
    calc m₁ * m₂ * u = m₁ * (m₂ * u) := by group
      _ = m₁ * (u * m₂) := by rw [hcomm2 m₂ hm₂]
      _ = (m₁ * u) * m₂ := by group
      _ = (u * m₁) * m₂ := by rw [hcomm1 m₁ hm₁]
      _ = u * (m₁ * m₂) := by group
  have huK : u ∈ K₁ ⊔ K₂ := hS.centralizer_le hcent
  have hmem : u ∈ (Subgroup.center ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype := by
    refine Subgroup.mem_map.2 ⟨⟨u, huK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hcent g g.2)
  rw [hS.zK] at hmem
  exact hmem

theorem sylow_cen (h : Hyp H K₁ K₂ z T a) {K : Subgroup H} (hKle : K ≤ K₁ ⊔ K₂)
    (hKN : K₁ ⊔ K₂ ⊔ T1 T K₁ ≤ normalizer (K : Set H)) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((T1 T K₁ ⊓ centralizer ({a} : Set H)) ⊓ (K ⊓ centralizer ({a} : Set H)))
      (K ⊓ centralizer ({a} : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine h.extr.inf_of_le_normalizer (fun x hx => ⟨hx.2, Subgroup.mem_sup_left (hKle hx.1)⟩) ?_
  intro m hm
  have hmN := hKN hm.2
  have hma : m * a = a * m := Subgroup.mem_centralizer_singleton_iff.1 hm.1
  exact mem_normalizer_of_conj_le (fun x hx =>
    conj_mem_cen (fun y hy => (Subgroup.mem_normalizer_iff.1 hmN y).1 hy) hma hx)

end Final

end CjAux

section Cj

open CjAux

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}

theorem prod3_Cj_of_Cb (h : Hyp H K₁ K₂ z T a)
    (hP₁ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₁) (centralizer (K₂ : Set H)))
    (hP₂ : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K₂) (centralizer (K₁ : Set H)))
    (hnt₁ : ¬ ∀ x ∈ K₁, a * x * a⁻¹ = x) (hnt₂ : ¬ ∀ x ∈ K₂, a * x * a⁻¹ = x)
    {r : ℕ} (hCb : Cb K₁ K₂ r) : Cj T K₁ z a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.setting
  have haa : a * a = 1 := hyp_a_mul_a h
  have hzc : ∀ g : H, z * g = g * z := fun g => (mul_inv_eq_iff_eq_mul.1 (h.z_central g)).symm
  obtain ⟨hpp, hrodd, hM₁, hM₂⟩ := hCb
  have hr3 : 3 ≤ r := by
    have h1 := hpp.one_lt
    obtain ⟨k, hk⟩ := hrodd
    omega
  have hr4 : 3 ^ 4 ≤ r ^ 4 := Nat.pow_le_pow_left hr3 4
  have htype : ∀ {K : Subgroup H}, HasSL2Model ↥K (fun q => q = r ^ 4) →
      HasSL2Model ↥K (fun q => Odd q ∧ 5 ≤ q) := by
    rintro K ⟨F, _, _, hq, e⟩
    exact ⟨F, inferInstance, inferInstance, ⟨by rw [hq]; exact hrodd.pow, by rw [hq]; omega⟩, e⟩
  apply le_antisymm
  · rintro w ⟨c, hc, rfl⟩
    have hwW : (c : H) ∈ T1 T K₁ ⊓ centralizer ({a} : Set H) := c.2
    have hwcen : ∀ y ∈ T1 T K₁ ⊓ centralizer ({a} : Set H), y * (c : H) = (c : H) * y := by
      intro y hy
      have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
      exact congrArg Subtype.val this
    show (c : H) ∈ zpowers a ⊔ zpowers z
    generalize (c : H) = w at hwW hwcen
    have hwT1 : w ∈ T1 T K₁ := (Subgroup.mem_inf.1 hwW).1
    have hwa : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hwW).2
    have hwT : w ∈ T := (Subgroup.mem_inf.1 hwT1).1
    have hwN₁ : w ∈ normalizer (K₁ : Set H) := (Subgroup.mem_inf.1 hwT1).2
    have hwK₁ : ∀ y ∈ K₁, w * y * w⁻¹ ∈ K₁ := fun y hy => (Subgroup.mem_normalizer_iff.1 hwN₁ y).1 hy
    have hwK₂ : ∀ y ∈ K₂, w * y * w⁻¹ ∈ K₂ := fun y hy => hS.conj_mem₂ hwN₁ hy
    have hw2 : ∃ m : ℕ, w ^ 2 ^ m = 1 := by
      obtain ⟨m, hm⟩ := h.sylow.isPGroup ⟨w, hwT⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hsupN₁ : K₁ ⊔ K₂ ⊔ T1 T K₁ ≤ normalizer (K₁ : Set H) :=
      sup_le (sup_le Subgroup.le_normalizer hS.le_normalizer₁) inf_le_right
    have hsupN₂ : K₁ ⊔ K₂ ⊔ T1 T K₁ ≤ normalizer (K₂ : Set H) :=
      sup_le (sup_le hS.symm.le_normalizer₁ Subgroup.le_normalizer) (fun x hx => hS.normalizer₁₂ hx.2)
    have hwQ₁ : ∀ q ∈ (T1 T K₁ ⊓ centralizer ({a} : Set H)) ⊓ (K₁ ⊓ centralizer ({a} : Set H)),
        w * q = q * w := fun q hq => (hwcen q hq.1).symm
    have hwQ₂ : ∀ q ∈ (T1 T K₁ ⊓ centralizer ({a} : Set H)) ⊓ (K₂ ⊓ centralizer ({a} : Set H)),
        w * q = q * w := fun q hq => (hwcen q hq.1).symm
    have D₁ : (∀ y ∈ K₁, w * y * w⁻¹ = y) ∨ (∀ y ∈ K₁, w * y * w⁻¹ = a * y * a⁻¹) := by
      obtain ⟨F, _, _, ê, σ, hF, hact⟩ := h.f₁.exists_slAct (htype hM₁)
      have hcard : Nat.card F = r ^ 4 := card_eq_of_model ê hM₁
      obtain ⟨hσσ, hσ1⟩ := sigma_facts haa hF hact hnt₁
      have hord : orderOf σ = 2 := orderOf_eq_prime (by rwa [pow_two]) hσ1
      have hfix : 3 < Nat.card ↥(fixedField σ) := by
        have h0 := fixedField_card_pow σ
        rw [hord, hcard] at h0
        by_contra hc3
        push Not at hc3
        have := Nat.pow_le_pow_left hc3 2
        omega
      exact factor_dichotomy hF hact hσσ hfix hwK₁ hwa hw2
        (sylow_cen h le_sup_left hsupN₁) hwQ₁
    have D₂ : (∀ y ∈ K₂, w * y * w⁻¹ = y) ∨ (∀ y ∈ K₂, w * y * w⁻¹ = a * y * a⁻¹) := by
      obtain ⟨F, _, _, ê, σ, hF, hact⟩ := h.f₂.exists_slAct (htype hM₂)
      have hcard : Nat.card F = r ^ 4 := card_eq_of_model ê hM₂
      obtain ⟨hσσ, hσ1⟩ := sigma_facts haa hF hact hnt₂
      have hord : orderOf σ = 2 := orderOf_eq_prime (by rwa [pow_two]) hσ1
      have hfix : 3 < Nat.card ↥(fixedField σ) := by
        have h0 := fixedField_card_pow σ
        rw [hord, hcard] at h0
        by_contra hc3
        push Not at hc3
        have := Nat.pow_le_pow_left hc3 2
        omega
      exact factor_dichotomy hF hact hσσ hfix hwK₂ hwa hw2
        (sylow_cen h le_sup_right hsupN₂) hwQ₂
    have hzmem : zpowers z ≤ zpowers a ⊔ zpowers z := le_sup_right
    have hamem : zpowers a ≤ zpowers a ⊔ zpowers z := le_sup_left
    rcases D₁ with t₁ | s₁ <;> rcases D₂ with t₂ | s₂
    ·
      exact hzmem (mem_zpowers_of_cent hS t₁ t₂)
    ·
      exfalso
      have hwC : w ∈ T ⊓ centralizer (K₁ : Set H) := by
        refine Subgroup.mem_inf.2 ⟨hwT, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
        exact (mul_inv_eq_iff_eq_mul.1 (t₁ u hu)).symm
      rw [inf_centralizer_eq h.sylow.isPGroup hS.comm hP₂] at hwC
      exact hnt₂ (h.f₂.inner_trivial hS.type₂ ⟨w, hwC.2, fun y hy => (s₂ y hy).symm⟩)
    ·
      exfalso
      have hwC : w ∈ T ⊓ centralizer (K₂ : Set H) := by
        refine Subgroup.mem_inf.2 ⟨hwT, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
        exact (mul_inv_eq_iff_eq_mul.1 (t₂ u hu)).symm
      rw [inf_centralizer_eq h.sylow.isPGroup hS.symm.comm hP₁] at hwC
      exact hnt₁ (h.f₁.inner_trivial hS.type₁ ⟨w, hwC.2, fun y hy => (s₁ y hy).symm⟩)
    ·
      have hu₁ : ∀ y ∈ K₁, (a * w) * y * (a * w)⁻¹ = y := fun y hy => by
        calc (a * w) * y * (a * w)⁻¹ = a * (w * y * w⁻¹) * a⁻¹ := by group
          _ = a * (a * y * a⁻¹) * a⁻¹ := by rw [s₁ y hy]
          _ = (a * a) * y * (a * a)⁻¹ := by group
          _ = y := by rw [haa]; group
      have hu₂ : ∀ y ∈ K₂, (a * w) * y * (a * w)⁻¹ = y := fun y hy => by
        calc (a * w) * y * (a * w)⁻¹ = a * (w * y * w⁻¹) * a⁻¹ := by group
          _ = a * (a * y * a⁻¹) * a⁻¹ := by rw [s₂ y hy]
          _ = (a * a) * y * (a * a)⁻¹ := by group
          _ = y := by rw [haa]; group
      have hw : w = a * (a * w) := by rw [← mul_assoc, haa, one_mul]
      rw [hw]
      exact mul_mem (hamem (mem_zpowers a)) (hzmem (mem_zpowers_of_cent hS hu₁ hu₂))
  · have haW : a ∈ T1 T K₁ ⊓ centralizer ({a} : Set H) :=
      Subgroup.mem_inf.2 ⟨h.a_mem, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    have hzN : z ∈ normalizer (K₁ : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have : z * y * z⁻¹ = y := by rw [hzc y]; group
      rw [this]
    have hzW : z ∈ T1 T K₁ ⊓ centralizer ({a} : Set H) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨h.z_mem, hzN⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (hzc a)⟩
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨a, haW⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z, hzW⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
      intro g
      apply Subtype.ext
      exact (hzc g).symm

end Cj

end CFSG.GH74.GLS.IVK.Prod3
