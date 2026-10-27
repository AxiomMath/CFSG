module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Inner
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Five
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Z7

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.GLS.Stage4.Hex
open scoped MatrixGroups commutatorElement

section Helpers

theorem normalizer_inf_of_normal_fu3 {G : Type*} [Group G] {X C : Subgroup G} [hC : C.Normal] {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((X ⊓ C : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (X : Set G) → ∀ t ∈ X ⊓ C, g * t * g⁻¹ ∈ X ⊓ C := fun g hg t ht =>
    ⟨(Subgroup.mem_normalizer_iff.mp hg t).mp ht.1, hC.conj_mem t ht.2 g⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key g hg t, fun ht => ?_⟩
  have := key g⁻¹ ((normalizer (X : Set G)).inv_mem hg) _ ht
  simpa [mul_assoc] using this

end Helpers

section Data

structure OuterData {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F) {K : Type} [Group K]
    (θ : ↥(unitarySU ℓ f F 3) →* K) (σ : MulAut K) where
  Ψ : SL(2, ↥h.fixedField) →* ↥(unitarySU ℓ f F 3)
  fixed : ∀ S, σ (θ (Ψ S)) = θ (Ψ S)
  irr : ∀ W : Submodule F (Fin 3 → F),
    (∀ S, ∀ v ∈ W, ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  comm : ∀ T : Matrix (Fin 3) (Fin 3) F,
    (∀ S, T * ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * T) → ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F)
  tr : ∀ τ : F ≃+* F, (∀ S, τ (Matrix.trace ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
    Matrix.trace ((Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) → τ = 1 ∨ ∀ c, τ c = h.bar c
  centOK : CentOK ℓ f Ψ.range
  card : Nat.card ↥h.fixedField = ℓ ^ f
  ker : ∀ S, θ (Ψ S) = 1 → S = 1 ∨ S = -1
  negone : Ψ (-1) = 1

end Data

section Lift

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem exists_gl3_lift [Finite F] (h : UnitaryFieldData ℓ f F) {K : Type} [Group K]
    {θ : ↥(unitarySU ℓ f F 3) →* K} (hθ : IsCover h θ) [Fact ℓ.Prime] (Y : Subgroup K)
    (hY : IsPGroup ℓ ↥Y) :
    ∃ Xt : Subgroup (GL (Fin 3) F), Xt ≤ unitarySU ℓ f F 3 ∧ IsPGroup ℓ ↥Xt ∧ (Xt = ⊥ → Y = ⊥) ∧
      ∀ g : ↥(unitarySU ℓ f F 3), θ g ∈ normalizer (Y : Set K) →
        (g : GL (Fin 3) F) ∈ normalizer (Xt : Set (GL (Fin 3) F)) := by
  classical
  have : Finite ↥(unitarySU ℓ f F 3) := inferInstance
  obtain ⟨Yt, hYt, hmap, hnormYt⟩ := exists_pgroup_lift θ
    (by rw [hθ.ker]; exact unitaryScalars_le_center h 3) Y hY
    (by rw [MonoidHom.range_eq_top.mpr hθ.surj]; exact le_top)
  refine ⟨Yt.map (unitarySU ℓ f F 3).subtype, ?_, hYt.map _, ?_, fun g hg => ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro hbot
    have hYt1 : Yt = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : ((y : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) ∈ Yt.map (unitarySU ℓ f F 3).subtype :=
        ⟨y, hy, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    rw [← hmap, hYt1, Subgroup.map_bot]
  · exact Subgroup.le_normalizer_map (unitarySU ℓ f F 3).subtype
      (Subgroup.mem_map_of_mem _ (hnormYt g hg))

end Lift

section Schur

variable {ℓ f : ℕ} {F : Type} [Field F]

theorem outer_centralizer_bot {h : UnitaryFieldData ℓ f F} {K : Type} [Group K]
    {θ : ↥(unitarySU ℓ f F 3) →* K} (hθ : IsCover h θ) {σ : MulAut K} (D : OuterData h θ σ) {a : K}
    (ha : ∀ S, θ (D.Ψ S) * a = a * θ (D.Ψ S)) : a = 1 := by
  classical
  obtain ⟨g, rfl⟩ := hθ.surj a
  have h1 : ∀ x ∈ D.Ψ.range, ∃ c : Fˣ,
      (g : GL (Fin 3) F) * glAut (1 : F ≃+* F) (x : GL (Fin 3) F) * (g : GL (Fin 3) F)⁻¹ =
        (x : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
    rintro x ⟨S, rfl⟩
    have h2 : θ (D.Ψ S * g) = θ (g * D.Ψ S) := by rw [map_mul, map_mul]; exact ha S
    obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 h2
    refine ⟨c, ?_⟩
    have hGL : ((g * D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) =
        ((D.Ψ S * g : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact hc
    have hscal : (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c * (g : GL (Fin 3) F)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) c := by
      rw [(commute_scalar c (g : GL (Fin 3) F)).eq, mul_inv_cancel_right]
    rw [map_one, MulAut.one_apply]
    have hGL' : (g : GL (Fin 3) F) * ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) =
        ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) * (g : GL (Fin 3) F) *
          GeneralLinearGroup.scalar (Fin 3) c := by
      simpa only [Subgroup.coe_mul] using hGL
    calc (g : GL (Fin 3) F) * ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) * (g : GL (Fin 3) F)⁻¹
        = ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) * (g : GL (Fin 3) F) *
            GeneralLinearGroup.scalar (Fin 3) c * (g : GL (Fin 3) F)⁻¹ := by rw [hGL']
      _ = ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) *
          ((g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c * (g : GL (Fin 3) F)⁻¹) := by group
      _ = _ := by rw [hscal]
  have h3 := D.centOK (g : GL (Fin 3) F) 1 h1
  have hcomm : ∀ S, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((D.Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((D.Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro S
    have h4 := h3 (D.Ψ S) ⟨S, rfl⟩
    rw [map_one, MulAut.one_apply] at h4
    have h5 : (g : GL (Fin 3) F) * ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) =
        ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) * (g : GL (Fin 3) F) := by
      calc (g : GL (Fin 3) F) * ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F)
          = ((g : GL (Fin 3) F) * ((D.Ψ S : ↥(unitarySU ℓ f F 3)) : GL (Fin 3) F) * (g : GL (Fin 3) F)⁻¹) *
              (g : GL (Fin 3) F) := by group
        _ = _ := by rw [h4]
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h5
    simpa using this
  obtain ⟨c0, hc0⟩ := D.comm _ hcomm
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    apply matU_ne_zero g
    simp at hc0
  have hgs : g ∈ unitaryScalars h 3 := by
    refine mem_unitaryScalars_of_scalar h (c := Units.mk0 c0 hc0ne) ?_
    apply Units.ext
    rw [hc0, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0, Matrix.smul_one_eq_diagonal]
  have : g ∈ θ.ker := by rw [hθ.ker]; exact hgs
  exact this

end Schur


section X0

theorem outer_X0_bot_char {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] {ℓ f : ℕ}
    [Fact ℓ.Prime] {F : Type} [Field F] [Finite F] [CharP F ℓ] {h : UnitaryFieldData ℓ f F}
    {θ : ↥(unitarySU ℓ f F 3) →* ↥K} (hθ : IsCover h θ) {σ : MulAut ↥K} (D : OuterData h θ σ)
    {X : Subgroup A} (hX : IsPGroup ℓ ↥X)
    (hnorm : ∀ S, ((θ (D.Ψ S) : ↥K) : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A)) :
    X ⊓ K = ⊥ := by
  classical
  have hX0p : IsPGroup ℓ ↥(X ⊓ K) := hX.to_le inf_le_left
  set Y : Subgroup ↥K := (X ⊓ K).subgroupOf K with hY
  have hYp : IsPGroup ℓ ↥Y := hX0p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨Xt, hXtU, hXtp, hXt1, hXtn⟩ := exists_gl3_lift h hθ Y hYp
  have hYn : ∀ S, θ (D.Ψ S) ∈ normalizer (Y : Set ↥K) := by
    intro S
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hnorm S) (y : A)
    rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h1
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector Xt hXtp
  have hWinv : ∀ S, ∀ w ∈ fixedSpace Xt,
      ((D.Ψ S : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ fixedSpace Xt :=
    fun S w hw => fixedSpace_invariant (hXtn (D.Ψ S) (hYn S)) hw
  rcases D.irr (fixedSpace Xt) hWinv with hW | hW
  · exfalso
    have hvW : v ∈ fixedSpace Xt := hv
    rw [hW] at hvW
    exact hv0 ((Submodule.mem_bot F).1 hvW)
  · have hXt1' : Xt = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      have hall : ∀ w : Fin 3 → F, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
        intro w
        have : w ∈ fixedSpace Xt := by rw [hW]; trivial
        exact this x hx
      apply Units.ext
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    have hYbot : Y = ⊥ := hXt1 hXt1'
    refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    have : (⟨a, ha.2⟩ : ↥K) ∈ Y := Subgroup.mem_subgroupOf.2 ha
    rw [hYbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this


theorem outer_X0_bot_cross {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] {ℓ f : ℕ}
    (hℓ2 : ℓ ≠ 2) {F : Type} [Field F] [Finite F] {h : UnitaryFieldData ℓ f F}
    {θ : ↥(unitarySU ℓ f F 3) →* ↥K} (hθ : IsCover h θ) {σ : MulAut ↥K} (D : OuterData h θ σ)
    (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) (h5 : 5 ≤ ℓ ^ f) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) {X : Subgroup A} (hX : IsPGroup p ↥X)
    (hnorm : ∀ S, ((θ (D.Ψ S) : ↥K) : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A)) : X ⊓ K = ⊥ := by
  classical
  have hq : Odd (ℓ ^ f) := (h.prime.odd_of_ne_two hℓ2).pow
  have hodd : Odd (Nat.card ↥h.fixedField) := by rw [D.card]; exact hq
  have h5k : 5 ≤ Nat.card ↥h.fixedField := by rw [D.card]; exact h5
  have hpk : ¬ p ∣ Nat.card ↥h.fixedField := by
    rw [D.card]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) h.prime).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd))
  let ι : SL(2, ↥h.fixedField) →* A := K.subtype.comp (θ.comp D.Ψ)
  have hnormι : ∀ S, ι S ∈ normalizer ((X ⊓ K : Subgroup A) : Set A) := hnorm
  have hX0p : IsPGroup p ↥(X ⊓ K) := hX.to_le inf_le_left
  have hK : Nat.card ↥K = psu3Order (Nat.card ↥h.fixedField) := by
    rw [D.card]
    exact (Nat.card_congr e.toEquiv).trans (card_statedProj_su3 h)
  have hdvd : Nat.card ↥(X ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
  have hle : padicValNat p (Nat.card ↥(X ⊓ K)) ≤ padicValNat p (psu3Order (Nat.card ↥h.fixedField)) := by
    rw [← hK]
    exact (padicValNat_dvd_iff_le Nat.card_pos.ne').1
      ((pow_padicValNat_dvd (p := p) (n := Nat.card ↥(X ⊓ K))).trans hdvd)
  have hcen : ∀ S, ∀ x ∈ X ⊓ K, ι S * x = x * ι S := by
    by_cases hexc : Nat.card ↥h.fixedField = 5 ∧ p = 3
    · obtain ⟨hk5, hp3⟩ := hexc
      subst hp3
      refine sl2_centralizes_five_three hk5 ι hX0p hnormι ?_
      rw [hk5, padicValNat_psu3Order_five_three] at hle
      exact hle
    · rcases sl2_centralizes_or_large hp2 hodd h5k hpk ι hX0p hnormι with hc | hlarge
      · exact hc
      · exfalso
        rcases padicValNat_psu3Order_lt hodd h5k hp2 hpk with hlt | hexc'
        · have := hlarge.trans hle
          omega
        · exact hexc hexc'
  refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : (⟨a, ha.2⟩ : ↥K) = 1 :=
    outer_centralizer_bot hθ D (fun S => Subtype.ext (hcen S a ha))
  exact congrArg Subtype.val ha'

theorem outer_X0_bot_three {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] {ℓ f : ℕ}
    (hℓ2 : ℓ ≠ 2) {F : Type} [Field F] [Finite F] {h : UnitaryFieldData ℓ f F}
    {θ : ↥(unitarySU ℓ f F 3) →* ↥K} {σ : MulAut ↥K} (D : OuterData h θ σ)
    (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) (hq3 : ℓ ^ f = 3) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {X : Subgroup A} (hX : IsPGroup p ↥X)
    (hnorm : ∀ S, ((θ (D.Ψ S) : ↥K) : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A)) : X ⊓ K = ⊥ := by
  classical
  by_contra hne
  have hK : Nat.card ↥K = 6048 := by
    have h1 : Nat.card ↥K = psu3Order (ℓ ^ f) := (Nat.card_congr e.toEquiv).trans (card_statedProj_su3 h)
    rw [h1, hq3]
    norm_num [psu3Order]
  have hℓ3 : ℓ = 3 := by
    have : ℓ ∣ 3 := hq3 ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp this
  have hX0p : IsPGroup p ↥(X ⊓ K) := hX.to_le inf_le_left
  obtain ⟨a, ha⟩ := hX0p.exists_card_eq
  have hXdvd : Nat.card ↥(X ⊓ K) ∣ 6048 := hK ▸ Subgroup.card_dvd_of_le inf_le_right
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hne
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using ha)
  have hpp : p ∣ 6048 := (dvd_pow_self p ha0).trans (ha ▸ hXdvd)
  have hp7 : p = 7 := by
    have h6048 : (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 := by norm_num
    rw [h6048] at hpp
    rcases (Fact.out : p.Prime).dvd_mul.mp hpp with h' | h'
    · rcases (Fact.out : p.Prime).dvd_mul.mp h' with h'' | h''
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h'')) hp2
      · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h'')
        exact absurd (hp3.trans hℓ3.symm) hpℓ
    · exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp h'
  have ha1 : a = 1 := by
    by_contra hne1
    have h2 : 2 ≤ a := by omega
    have h49 : 7 ^ 2 ∣ 6048 := by
      have := pow_dvd_pow 7 h2
      rw [hp7] at ha
      exact this.trans (ha ▸ hXdvd)
    norm_num at h49
  have hcardX : Nat.card ↥(X ⊓ K) = p := by rw [ha, ha1, pow_one]
  have hcyc : IsCyclic ↥(X ⊓ K) := isCyclic_of_prime_card hcardX
  have h3k : (3 : ↥h.fixedField) = 0 := by
    have : Fintype ↥h.fixedField := Fintype.ofFinite _
    have h' := Nat.cast_card_eq_zero ↥h.fixedField
    rw [← Nat.card_eq_fintype_card, D.card, hq3] at h'
    exact_mod_cast h'
  have hu := hnorm (uElt : SL(2, ↥h.fixedField))
  have hv := hnorm (vElt : SL(2, ↥h.fixedField))
  have hcc := commutator_mem_centralizer_of_cyclic hcyc hu hv
  set c : SL(2, ↥h.fixedField) := ⁅(uElt : SL(2, ↥h.fixedField)), (vElt : SL(2, ↥h.fixedField))⁆ with hc
  have hcsq : c * c = -1 := comm_uv_sq h3k
  have hmapc : ((θ (D.Ψ c) : ↥K) : A) = ⁅((θ (D.Ψ (uElt : SL(2, ↥h.fixedField))) : ↥K) : A),
      ((θ (D.Ψ (vElt : SL(2, ↥h.fixedField))) : ↥K) : A)⁆ := by
    rw [hc, map_commutatorElement, map_commutatorElement]
    rfl
  have ht2 : θ (D.Ψ c) * θ (D.Ψ c) = 1 := by
    rw [← map_mul, ← map_mul, hcsq, D.negone, map_one]
  have ht1 : θ (D.Ψ c) ≠ 1 := by
    intro h1
    rcases D.ker c h1 with h2 | h2
    · rw [h2, one_mul] at hcsq
      have h2' : (2 : ↥h.fixedField) ≠ 0 := by
        intro h2''
        have : Fintype ↥h.fixedField := Fintype.ofFinite _
        have hodd : Odd (Nat.card ↥h.fixedField) := by rw [D.card, hq3]; decide
        exact two_ne_zero_of_odd_card hodd h2''
      have := congrArg (fun x : SL(2, ↥h.fixedField) => (x : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 0 0) hcsq
      simp at this
      exact h2' (by linear_combination this)
    · rw [h2] at hcsq
      have h2' : (2 : ↥h.fixedField) ≠ 0 := by
        intro h2''
        have : Fintype ↥h.fixedField := Fintype.ofFinite _
        have hodd : Odd (Nat.card ↥h.fixedField) := by rw [D.card, hq3]; decide
        exact two_ne_zero_of_odd_card hodd h2''
      have := congrArg (fun x : SL(2, ↥h.fixedField) => (x : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 0 0) hcsq
      simp at this
      exact h2' (by linear_combination this)
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ X ⊓ K, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hy7 : (⟨y, hy.2⟩ : ↥K) ^ 7 = 1 := by
    have h1 : (⟨y, hy⟩ : ↥(X ⊓ K)) ^ Nat.card ↥(X ⊓ K) = 1 := pow_card_eq_one'
    rw [hcardX, hp7] at h1
    apply Subtype.ext
    have := congrArg Subtype.val h1
    simpa using this
  have hcomm : (⟨y, hy.2⟩ : ↥K) * θ (D.Ψ c) = θ (D.Ψ c) * ⟨y, hy.2⟩ := by
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (hmapc ▸ hcc) y hy
    exact this
  have := no_seven_centralizes_involution h (by exact hℓ2) hq3 e hy7 ht2 ht1 hcomm
  exact hy1 (congrArg Subtype.val this)

end X0


section Main

theorem fu3_outer_of_data {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal] {ℓ f : ℕ}
    (hℓ2 : ℓ ≠ 2) {F : Type} [Field F] [Finite F] {h : UnitaryFieldData ℓ f F} (h3 : 3 ≤ ℓ ^ f)
    {θ : ↥(unitarySU ℓ f F 3) →* ↥K} (hθ : IsCover h θ) {σ : MulAut ↥K} (D : OuterData h θ σ)
    (e : ↥K ≃* StatedProj (StatedSU 3 (ℓ ^ f) F)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup A} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hfaith : X ⊓ centralizer (K : Set A) = ⊥)
    (hJ : ∀ j : ↥K, σ j = j → (j : A) ∈ normalizer (X : Set A))
    (hAut : ∀ {ψ : MulAut ↥K} {n : ℕ}, Odd n → ψ ^ n = 1 →
      (∀ g ∈ D.Ψ.range, ψ (θ g) = θ g) → ψ = 1) : False := by
  classical
  have hq : Odd (ℓ ^ f) := (h.prime.odd_of_ne_two hℓ2).pow
  have hnorm : ∀ S, ((θ (D.Ψ S) : ↥K) : A) ∈ normalizer ((X ⊓ K : Subgroup A) : Set A) := fun S =>
    normalizer_inf_of_normal_fu3 (hJ _ (D.fixed S))
  have hX0 : X ⊓ K = ⊥ := by
    by_cases hpℓ : p = ℓ
    · have : Fact ℓ.Prime := ⟨h.prime⟩
      have : CharP F ℓ := h.charP
      exact outer_X0_bot_char hθ D (by rw [← hpℓ]; exact hX) hnorm
    · by_cases h5 : 5 ≤ ℓ ^ f
      · exact outer_X0_bot_cross hℓ2 hθ D e h5 hp2 hpℓ hX hnorm
      · have hq3 : ℓ ^ f = 3 := by
          obtain ⟨m, hm⟩ := hq
          omega
        exact outer_X0_bot_three hℓ2 D e hq3 hp2 hpℓ hX hnorm
  apply hX1
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hcomm : ∀ S, (x : A) * ((θ (D.Ψ S) : ↥K) : A) * (x : A)⁻¹ = ((θ (D.Ψ S) : ↥K) : A) := by
    intro S
    have hjn := hJ _ (D.fixed S)
    have hc1 : ((θ (D.Ψ S) : ↥K) : A) * x * ((θ (D.Ψ S) : ↥K) : A)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 hjn x).1 hx
    have hcX : ⁅((θ (D.Ψ S) : ↥K) : A), (x : A)⁆ ∈ X := by
      rw [commutatorElement_def]
      have := Subgroup.mul_mem X hc1 (Subgroup.inv_mem X hx)
      simpa [mul_assoc] using this
    have hcK : ⁅((θ (D.Ψ S) : ↥K) : A), (x : A)⁆ ∈ K := by
      rw [commutatorElement_def]
      have h1 : (x : A) * ((θ (D.Ψ S) : ↥K) : A)⁻¹ * (x : A)⁻¹ ∈ K := by
        have := (inferInstance : K.Normal).conj_mem (((θ (D.Ψ S) : ↥K) : A)⁻¹)
          (K.inv_mem (θ (D.Ψ S)).2) x
        simpa [mul_assoc] using this
      have := K.mul_mem (θ (D.Ψ S)).2 h1
      simpa [mul_assoc] using this
    have h1 : ⁅((θ (D.Ψ S) : ↥K) : A), (x : A)⁆ = 1 := by
      have : ⁅((θ (D.Ψ S) : ↥K) : A), (x : A)⁆ ∈ X ⊓ K := ⟨hcX, hcK⟩
      rw [hX0, Subgroup.mem_bot] at this
      exact this
    have h2 : ((θ (D.Ψ S) : ↥K) : A) * x = x * ((θ (D.Ψ S) : ↥K) : A) :=
      commutatorElement_eq_one_iff_mul_comm.1 h1
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  let ψ : MulAut ↥K := MulAut.conjNormal (H := K) x
  have hfix : ∀ g ∈ D.Ψ.range, ψ (θ g) = θ g := by
    rintro g ⟨S, rfl⟩
    exact Subtype.ext (by rw [show ψ = MulAut.conjNormal (H := K) x from rfl, MulAut.conjNormal_apply]; exact hcomm S)
  obtain ⟨a, ha⟩ := hX ⟨x, hx⟩
  have hxa : x ^ (p ^ a) = 1 := congrArg Subtype.val ha
  have hψpow : ψ ^ (p ^ a) = 1 := by
    rw [show ψ = MulAut.conjNormal (H := K) x from rfl, ← map_pow, hxa, map_one]
  have hodd : Odd (p ^ a) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hψ1 : ψ = 1 := hAut hodd hψpow hfix
  have hxc : x ∈ centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := congrArg (fun τ : MulAut ↥K => (τ ⟨k, hk⟩ : A)) hψ1
    simp only [show ψ = MulAut.conjNormal (H := K) x from rfl, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc k * x = (x * k * x⁻¹) * x := by rw [this]
      _ = x * k := by group
  have : x ∈ X ⊓ centralizer (K : Set A) := ⟨hx, hxc⟩
  rw [hfaith, Subgroup.mem_bot] at this
  exact this

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
