module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsGroup
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsTransport
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
open scoped commutatorElement

variable {G : Type} [Group G]

structure IsWModel (σ : Setting G) {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ}
    {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
    {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
    (φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma) : Prop where
  model : TIFacts.IsModelMap σ φ (ModelSignalizers.modelLayer b m hm heven Sigma hSigma)
    (ModelSignalizers.modelY b m hm heven Sigma hSigma)
  p_prime : σ.p.Prime
  p_odd : Odd σ.p
  one_le_f : 1 ≤ σ.f
  card : Nat.card F = σ.p ^ σ.f
  two_part : m = 2 ^ padicValInt 2 ((σ.p ^ σ.f : ℕ) -
    (if σ.p ^ σ.f % 4 = 1 then (1 : ℤ) else -1))
  sigma_odd : Odd (Nat.card Sigma)
  sigma_cyclic : IsCyclic Sigma
  sigma_dvd : Nat.card Sigma ∣ σ.f
  nonsquare : ¬ IsSquare b
  x_mem : σ.x ∈ σ.N
  map_x : φ ⟨σ.x, x_mem⟩ = ModelSignalizers.modelX b m hm heven Sigma hSigma
  L_le_N : σ.L ≤ σ.N
  mem_L_iff : ∀ g : σ.N,
    (g : G) ∈ σ.L ↔ φ g ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma
  D_le_N : σ.D ≤ σ.N
  x_mem_D : σ.x ∈ σ.D
  x₂_mem_D : σ.x₂ ∈ σ.D
  exists_swap : ∃ d ∈ σ.D, d ∈ σ.L₀ ∧ d * σ.x₂ * d⁻¹ = σ.x * σ.x₂

namespace IsWModel

variable {σ : Setting G} {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ}
  {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
  {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
  {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}

theorem two_ne_zero (hW : IsWModel σ φ) : (2 : F) ≠ 0 :=
  CFSG.Wreathed.CentralSL2.two_ne_zero_of_not_isSquare hW.nonsquare

theorem mem_ON_iff (hW : IsWModel σ φ) (g : σ.N) : (g : G) ∈ σ.ON ↔ φ g = 1 := by
  rw [← MonoidHom.mem_ker, hW.model.ker_eq, Subgroup.mem_subgroupOf]

theorem map_eq_map_iff (hW : IsWModel σ φ) (g h : σ.N) :
    φ g = φ h ↔ ((g⁻¹ * h : σ.N) : G) ∈ σ.ON := by
  rw [hW.mem_ON_iff, map_mul, map_inv, inv_mul_eq_one]

theorem map_mem_modelC (hW : IsWModel σ φ) (g : σ.N) (hg : (g : G) ∈ σ.C) :
    φ g ∈ ModelSignalizers.modelC b m hm heven Sigma hSigma := by
  rw [ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff, ← hW.model.map_x₂,
    ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext ((TIFacts.mem_C_iff σ g.2).mp hg)

theorem map_mem_modelLayer (hW : IsWModel σ φ) (g : σ.N) (hg : (g : G) ∈ σ.L₀) :
    φ g ∈ ModelSignalizers.modelLayer b m hm heven Sigma hSigma := by
  rw [← hW.model.map_L₀]
  exact ⟨g, hg, rfl⟩

theorem exists_mem_L₀ (hW : IsWModel σ φ) {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hh : h ∈ ModelSignalizers.modelLayer b m hm heven Sigma hSigma) :
    ∃ g : σ.N, (g : G) ∈ σ.L₀ ∧ φ g = h := by
  rw [← hW.model.map_L₀] at hh
  obtain ⟨g, hg, rfl⟩ := hh
  exact ⟨g, hg, rfl⟩

omit [Fintype F] in
theorem modelBase_normal :
    (ModelSignalizers.modelBase b m hm heven Sigma hSigma).Normal := by
  rw [ModelSignalizers.modelBase, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem commutator_mem_ON (hW : IsWModel σ φ) {a c : G} (ha : a ∈ σ.C ⊓ σ.L)
    (hc : c ∈ σ.C ⊓ σ.L) : a * c * a⁻¹ * c⁻¹ ∈ σ.ON := by
  have haN : a ∈ σ.N := TIFacts.C_le_N σ ha.1
  have hcN : c ∈ σ.N := TIFacts.C_le_N σ hc.1
  have key : ∀ {g : G} (hg : g ∈ σ.C ⊓ σ.L) (hgN : g ∈ σ.N), ∃ v ∈ Subgroup.centralizer
      {yV b m hm heven}, φ ⟨g, hgN⟩ = SemidirectProduct.inl v := by
    intro g hg hgN
    obtain ⟨v, hv⟩ := (hW.mem_L_iff ⟨g, hgN⟩).mp hg.2
    refine ⟨v, ?_, hv.symm⟩
    have hC := hW.map_mem_modelC ⟨g, hgN⟩ hg.1
    rw [← hv, ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff, modelY_eq_inl_yV,
      ← map_mul, ← map_mul] at hC
    exact Subgroup.mem_centralizer_singleton_iff.mpr (SemidirectProduct.inl_injective hC)
  obtain ⟨v, hv, hav⟩ := key ha haN
  obtain ⟨w, hw, hcw⟩ := key hc hcN
  have hcomm := centralizer_comm hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven hW.two_part
    hW.sigma_odd hSigma hW.nonsquare hv hw
  have h := (hW.mem_ON_iff (⟨a, haN⟩ * ⟨c, hcN⟩ * (⟨a, haN⟩ : σ.N)⁻¹ * (⟨c, hcN⟩ : σ.N)⁻¹)).mpr
    (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hav, hcw, ← map_mul, hcomm, map_mul]
        group)
  simpa using h

theorem exists_torus_of_mem (hW : IsWModel σ φ) (g : σ.N) (hg : (g : G) ∈ σ.C ⊓ σ.L₀) :
    ∃ Z ∈ torus F, φ g = iota b m hm heven Sigma hSigma Z := by
  have hmem : φ g ∈ ModelSignalizers.modelLayer b m hm heven Sigma hSigma ⊓
      ModelSignalizers.modelC b m hm heven Sigma hSigma :=
    ⟨hW.map_mem_modelLayer g hg.2, hW.map_mem_modelC g hg.1⟩
  rw [modelLayer_inf_modelC hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven hW.two_part
    hW.sigma_odd hSigma hW.nonsquare] at hmem
  obtain ⟨Z, hZ, hZg⟩ := hmem
  exact ⟨Z, hZ, hZg.symm⟩

theorem exists_swap_iota (hW : IsWModel σ φ) :
    ∃ d ∈ σ.D, ∃ hdN : d ∈ σ.N, d ∈ σ.L₀ ∧ d * σ.x₂ * d⁻¹ = σ.x * σ.x₂ ∧
      ∃ X : Matrix.SpecialLinearGroup (Fin 2) F, φ ⟨d, hdN⟩ = iota b m hm heven Sigma hSigma X ∧
        X * weyl F * X⁻¹ = minusIdentity F * weyl F := by
  obtain ⟨d, hdD, hdL₀, hdx⟩ := hW.exists_swap
  have hdN : d ∈ σ.N := hW.D_le_N hdD
  have hM := hW.map_mem_modelLayer ⟨d, hdN⟩ hdL₀
  rw [modelLayer_eq_range] at hM
  obtain ⟨X, hX⟩ := hM
  refine ⟨d, hdD, hdN, hdL₀, hdx, X, hX.symm, ?_⟩
  apply conj_weyl_of_conj_modelY b m hm heven Sigma hSigma
  have hx₂N : σ.x₂ ∈ σ.N := hW.model.x₂_mem
  have key : (⟨d, hdN⟩ : σ.N) * ⟨σ.x₂, hx₂N⟩ * (⟨d, hdN⟩ : σ.N)⁻¹ =
      ⟨σ.x, hW.x_mem⟩ * ⟨σ.x₂, hx₂N⟩ := Subtype.ext hdx
  have h := congrArg φ key
  rw [map_mul, map_mul, map_inv, map_mul, ← hX, hW.model.map_x₂, hW.map_x] at h
  exact h

theorem L_normal (hW : IsWModel σ φ) : σ.N ≤ Subgroup.normalizer (σ.L : Set G) := by
  have key : ∀ n ∈ σ.N, ∀ l ∈ σ.L, n * l * n⁻¹ ∈ σ.L := by
    intro n hn l hl
    have hlN := hW.L_le_N hl
    have hmem := (hW.mem_L_iff ⟨l, hlN⟩).mp hl
    have hconj := (modelBase_normal (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
      (hSigma := hSigma)).conj_mem _ hmem (φ ⟨n, hn⟩)
    rw [← map_inv, ← map_mul, ← map_mul] at hconj
    exact (hW.mem_L_iff _).mpr hconj
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · exact key n hn l
  · intro h
    have h1 := key n⁻¹ (σ.N.inv_mem hn) _ h
    simpa [mul_assoc] using h1

theorem N_mod_L_cyclic (hW : IsWModel σ φ) :
    ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L := by
  have := hW.sigma_cyclic
  obtain ⟨τ₀, hτ₀⟩ := IsCyclic.exists_generator (α := Sigma)
  obtain ⟨g, hg⟩ := hW.model.surjective (SemidirectProduct.inr τ₀)
  refine ⟨g, g.2, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hτ₀ (SemidirectProduct.rightHom (φ ⟨n, hn⟩)))
  refine ⟨k, ?_⟩
  have hmem := (hW.mem_L_iff (⟨n, hn⟩ * (g ^ k)⁻¹)).mpr (by
    rw [ModelSignalizers.modelBase, SemidirectProduct.range_inl_eq_ker_rightHom,
      MonoidHom.mem_ker]
    simp only [map_mul, map_inv, map_zpow, hg, SemidirectProduct.rightHom_inr, hk,
      mul_inv_cancel])
  simpa using hmem

theorem ON_le_solvRadIn_L [Finite G] (hW : IsWModel σ φ) : σ.ON ≤ solvRadIn σ.L := by
  have hON : σ.ON ≤ σ.L := hW.model.ON_le.trans le_sup_left
  set K : Subgroup σ.L := σ.ON.subgroupOf σ.L with hK
  have hKn : K.Normal := by
    constructor
    intro k hk l
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    have hlN : (l : G) ∈ σ.N := hW.L_le_N l.2
    have h := (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON hlN) k).mp hk
    simpa using h
  have hKodd : Odd (Nat.card K) := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv]
    exact odd_card_oddCoreIn σ.N
  have hKs : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
  have hle : K ≤ CFSG.solvableRadical σ.L := le_sSup ⟨hKn, hKs⟩
  intro g hg
  exact ⟨⟨g, hON hg⟩, hle (Subgroup.mem_subgroupOf.mpr hg), rfl⟩

theorem C_inf_L_commutator [Finite G] (hW : IsWModel σ φ) :
    ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L := by
  refine le_trans ?_ hW.ON_le_solvRadIn_L
  rw [Subgroup.commutator_le]
  intro a ha c hc
  rw [commutatorElement_def]
  exact hW.commutator_mem_ON ha hc

theorem C_inf_L₀_commutator (hW : IsWModel σ φ) : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON := by
  rw [Subgroup.commutator_le]
  intro a ha c hc
  rw [commutatorElement_def]
  exact hW.commutator_mem_ON ⟨ha.1, le_sup_left (a := σ.L₀) ha.2⟩
    ⟨hc.1, le_sup_left (a := σ.L₀) hc.2⟩

theorem inverts_C_inf_L₀ (hW : IsWModel σ φ) :
    ∃ d ∈ σ.D, d ∈ σ.L₀ ∧ d * σ.x₂ * d⁻¹ = σ.x * σ.x₂ ∧
      ∀ c ∈ σ.C ⊓ σ.L₀, d * c * d⁻¹ * c ∈ σ.ON := by
  obtain ⟨d, hdD, hdN, hdL₀, hdx, X, hdX, hX⟩ := hW.exists_swap_iota
  refine ⟨d, hdD, hdL₀, hdx, fun c hc => ?_⟩
  have hcN : c ∈ σ.N := TIFacts.C_le_N σ hc.1
  obtain ⟨Z, hZ, hcZ⟩ := hW.exists_torus_of_mem ⟨c, hcN⟩ hc
  have h := (hW.mem_ON_iff (⟨d, hdN⟩ * ⟨c, hcN⟩ * (⟨d, hdN⟩ : σ.N)⁻¹ * ⟨c, hcN⟩)).mpr (by
    rw [map_mul, map_mul, map_mul, map_inv, hdX, hcZ, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, conj_eq_inv_of_mem_torus hX hZ, inv_mul_cancel, map_one])
  simpa using h

theorem exists_inverting_D_L₀ (hW : IsWModel σ φ) :
    ∃ d ∈ σ.D, d ∈ σ.L₀ ∧ ∀ c ∈ σ.C ⊓ σ.L₀, Odd (orderOf c) → d * c * d⁻¹ * c ∈ σ.ON := by
  obtain ⟨d, hdD, hdL₀, -, hinv⟩ := hW.inverts_C_inf_L₀
  exact ⟨d, hdD, hdL₀, fun c hc _ => hinv c hc⟩

theorem L_centralizer_D_odd_le (hW : IsWModel σ φ) :
    ∀ y ∈ σ.L, y ∈ Subgroup.centralizer (σ.D : Set G) → Odd (orderOf y) → y ∈ σ.ON := by
  intro y hyL hyD hodd
  have hyN : y ∈ σ.N := hW.L_le_N hyL
  obtain ⟨v, hv⟩ := (hW.mem_L_iff ⟨y, hyN⟩).mp hyL
  have hyC : y ∈ σ.C := (TIFacts.mem_C_iff σ hyN).mpr
    ((Subgroup.mem_centralizer_iff.mp hyD σ.x₂ hW.x₂_mem_D).symm)
  have hvC : v ∈ Subgroup.centralizer {yV b m hm heven} := by
    have hC := hW.map_mem_modelC ⟨y, hyN⟩ hyC
    rw [← hv, ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff, modelY_eq_inl_yV,
      ← map_mul, ← map_mul] at hC
    exact Subgroup.mem_centralizer_singleton_iff.mpr (SemidirectProduct.inl_injective hC)
  have hvodd : Odd (orderOf v) := by
    have h1 : orderOf (φ ⟨y, hyN⟩) ∣ orderOf (⟨y, hyN⟩ : σ.N) := orderOf_map_dvd φ _
    rw [← hv, orderOf_injective _ SemidirectProduct.inl_injective, Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  obtain ⟨W, hW'⟩ := exists_oddTorus F
  obtain ⟨w, hwW, hwv⟩ := exists_eq_iF_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hW' hvC hvodd
  have hwT : w ∈ torus F := ((hW' w).mp hwW).1
  have hwodd : Odd (orderOf w) := ((hW' w).mp hwW).2
  obtain ⟨d, hdD, hdN, -, -, X, hdX, hX⟩ := hW.exists_swap_iota
  have hyv : φ ⟨y, hyN⟩ = iota b m hm heven Sigma hSigma w := by
    rw [← hv, iota_apply, hwv]
  have hcomm : w * X = X * w := by
    have h1 : (⟨y, hyN⟩ : σ.N) * ⟨d, hdN⟩ = ⟨d, hdN⟩ * ⟨y, hyN⟩ :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hyD d hdD).symm)
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, hyv, hdX, ← map_mul, ← map_mul] at h2
    exact iota_injective b m hm heven Sigma hSigma h2
  have hinv := conj_eq_inv_of_mem_torus hX hwT
  rw [← hcomm, mul_inv_cancel_right] at hinv
  have hw1 : w = 1 := by
    have h2 : w ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel w
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hwodd
      exact absurd hwodd (by decide)
  have h := (hW.mem_ON_iff ⟨y, hyN⟩).mpr (by rw [hyv, hw1, map_one])
  exact h

theorem oddCore_C_inf_L₀_cyclic (hW : IsWModel σ φ) :
    ∃ g ∈ σ.N, oddCoreIn σ.C ⊓ σ.L₀ ≤ Subgroup.zpowers g ⊔ σ.ON := by
  have : IsCyclic (torus F) := torus_isCyclic hW.two_ne_zero
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := torus F)
  have hM : iota b m hm heven Sigma hSigma t₀ ∈ ModelSignalizers.modelLayer b m hm heven Sigma
      hSigma := by
    rw [modelLayer_eq_range]
    exact ⟨t₀, rfl⟩
  obtain ⟨g, -, hg⟩ := hW.exists_mem_L₀ hM
  refine ⟨g, g.2, fun k hk => ?_⟩
  have hkC : k ∈ σ.C := oddCoreIn_le σ.C hk.1
  have hkN : k ∈ σ.N := TIFacts.C_le_N σ hkC
  obtain ⟨Z, hZ, hkZ⟩ := hW.exists_torus_of_mem ⟨k, hkN⟩ ⟨hkC, hk.2⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (ht₀ ⟨Z, hZ⟩)
  have hZj : Z = (t₀ : Matrix.SpecialLinearGroup (Fin 2) F) ^ j := by
    rw [← Subgroup.coe_zpow, hj]
  have heq : φ (g ^ j) = φ ⟨k, hkN⟩ := by rw [map_zpow, hg, hkZ, hZj, map_zpow]
  have hON := (hW.map_eq_map_iff _ _).mp heq
  have hk' : k = ((g ^ j : σ.N) : G) * (((g ^ j)⁻¹ * ⟨k, hkN⟩ : σ.N) : G) := by simp
  rw [hk']
  exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨j, by simp⟩) hON

theorem oddCore_C_inf_L₀_coprime (hW : IsWModel σ φ) :
    ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀) := by
  set X : Subgroup G := oddCoreIn σ.C ⊓ σ.L₀ with hXdef
  have hXN : X ≤ σ.N := fun k hk => TIFacts.C_le_N σ (oddCoreIn_le σ.C hk.1)
  set ψ : X →* SemilinearExtension F b m hm heven Sigma hSigma :=
    φ.comp (Subgroup.inclusion hXN) with hψ
  have hker : ψ.ker = σ.ON.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ, MonoidHom.comp_apply,
      ← hW.mem_ON_iff]
    rfl
  have hrange : ψ.range ≤ (torus F).map (iota b m hm heven Sigma hSigma) := by
    rintro _ ⟨x, rfl⟩
    have hx := x.2
    obtain ⟨Z, hZ, hxZ⟩ := hW.exists_torus_of_mem (Subgroup.inclusion hXN x)
      ⟨oddCoreIn_le σ.C hx.1, hx.2⟩
    exact ⟨Z, hZ, hxZ.symm⟩
  have hidx : σ.ON.relIndex X = Nat.card ψ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hcard : Nat.card ((torus F).map (iota b m hm heven Sigma hSigma)) = Nat.card (torus F) :=
    Nat.card_congr ((torus F).equivMapOfInjective _
      (iota_injective b m hm heven Sigma hSigma)).toEquiv.symm
  have hdvd : (σ.ON.relIndex X : ℤ) ∣ (Nat.card F : ℤ) -
      (if Nat.card F % 4 = 1 then 1 else -1) := by
    rw [← torus_card hW.two_ne_zero, hidx, ← hcard]
    exact Int.natCast_dvd_natCast.mpr (Subgroup.card_dvd_of_le hrange)
  intro hp
  have hp' : (σ.p : ℤ) ∣ (Nat.card F : ℤ) - (if Nat.card F % 4 = 1 then 1 else -1) :=
    (Int.natCast_dvd_natCast.mpr hp).trans hdvd
  have hpq : (σ.p : ℤ) ∣ (Nat.card F : ℤ) := by
    rw [hW.card]
    exact Int.natCast_dvd_natCast.mpr (dvd_pow_self _ (by have := hW.one_le_f; omega))
  have h1 := dvd_sub hpq hp'
  rw [sub_sub_cancel] at h1
  have hp1 : (σ.p : ℤ) ∣ 1 := by
    split_ifs at h1
    · exact h1
    · exact (dvd_neg.mp h1)
  have := Int.eq_one_of_dvd_one (by positivity) hp1
  exact hW.p_prime.one_lt.ne' (by exact_mod_cast this)

theorem oddCore_C_inf_L₀_centralized (hW : IsWModel σ φ) :
    ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, c * k * c⁻¹ * k⁻¹ ∈ σ.ON := by
  intro c hc k hk
  have hcL : c ∈ σ.L := le_sup_right (a := σ.L₀) hc.1.1
  exact hW.commutator_mem_ON ⟨hc.2, hcL⟩ ⟨oddCoreIn_le σ.C hk.1, le_sup_left (a := σ.L₀) hk.2⟩

theorem oddCore_C_inf_L₀_inverted (hW : IsWModel σ φ) :
    ∃ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) ∧
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, d * k * d⁻¹ * k ∈ σ.ON := by
  obtain ⟨d, hdD, -, hdx, hinv⟩ := hW.inverts_C_inf_L₀
  refine ⟨d, hdD, fun hdC => ?_, fun k hk => hinv k ⟨oddCoreIn_le σ.C hk.1, hk.2⟩⟩
  have hx₂T : σ.x₂ ∈ σ.T := Subgroup.subset_closure (by simp)
  have hcomm : d * σ.x₂ = σ.x₂ * d := (Subgroup.mem_centralizer_iff.mp hdC σ.x₂ hx₂T).symm
  rw [hcomm, mul_inv_cancel_right] at hdx
  have hx1 : σ.x = 1 := by
    have h := congrArg (· * σ.x₂⁻¹) hdx
    simpa using h.symm
  have h1 : φ ⟨σ.x, hW.x_mem⟩ = 1 := by
    rw [show (⟨σ.x, hW.x_mem⟩ : σ.N) = 1 from Subtype.ext hx1, map_one]
  rw [hW.map_x, modelX_eq, ← map_one (iota b m hm heven Sigma hSigma)] at h1
  have h2 := iota_injective b m hm heven Sigma hSigma h1
  have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) 0 0) h2
  simp only [minusIdentity_coe] at h3
  have h4 : (-1 : F) = 1 := by simpa using h3
  have h5 : (2 : F) = 0 := by linear_combination -h4
  exact hW.two_ne_zero h5

end IsWModel

end CFSG.Wreathed.OriginalAllPrime.IVFacts
