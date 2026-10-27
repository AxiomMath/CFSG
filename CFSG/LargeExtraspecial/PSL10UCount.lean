module

public import CFSG.LargeExtraspecial.PSL10UStab
public import CFSG.LargeExtraspecial.PSL10USimple
public import CFSG.LieType.SteinbergBRUnitaryExtraspecialWidth
public import CFSG.LargeExtraspecial.PSL10UAxis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup CFSG.Open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons CFSG.LocalAnalysis.GorensteinLyons.FourUnitary

variable {F : Type} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

@[expose] noncomputable def centGL (t : sesqSpecialUnitaryGroup B) :
    centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) →* LinearMap.GeneralLinearGroup F W :=
  (sesqSpecialUnitaryGroup B).subtype.comp (centralizer _).subtype

theorem centGL_injective (t : sesqSpecialUnitaryGroup B) : Function.Injective (centGL t) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem apply_eq_of_mem_of_perfect {t : sesqSpecialUnitaryGroup B} {e f : W} (he0 : e ≠ 0)
    (hef : B e f = 1) (ht : suEnd B t = hermTransvection B e 1)
    {K : Subgroup (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))} (hperf : ⁅K, K⁆ = K) :
    ∀ k ∈ K, ((centGL t k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) e = e := by
  have hc : ∀ c : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)),
      ((centGL t c : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) e =
        B e (((centGL t c : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) • e := by
    intro c
    have h1 : suEnd B c * suEnd B t = suEnd B t * suEnd B c := by
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp c.2]
    have h2 := LinearMap.congr_fun h1 f
    rw [ht, Module.End.mul_apply, Module.End.mul_apply, hermTransvection_apply,
      hermTransvection_apply, hef, one_mul, one_smul, map_add, one_mul] at h2
    exact add_left_cancel h2
  let lam : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) →* F :=
    { toFun := fun c => B e (((centGL t c : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f)
      map_one' := by rw [map_one, Units.val_one, Module.End.one_apply, hef]
      map_mul' := fun c d => by
        refine smul_left_injective F he0 ?_
        change B e (((centGL t (c * d) : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) • e =
          (B e (((centGL t c : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) *
            B e (((centGL t d : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f)) • e
        rw [← hc, map_mul, Units.val_mul, Module.End.mul_apply, hc d, map_smul, hc c, smul_smul,
          mul_comm] }
  have hK : K ≤ (lam.toHomUnits).ker := by
    rw [← hperf]
    refine commutator_le.mpr fun a _ b _ => MonoidHom.mem_ker.mpr ?_
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  intro k hk
  have h1 : lam k = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp (hK hk))
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  rw [hc k]
  change lam k • e = e
  rw [h1, one_smul]

theorem conclusion_hermTransvection [FiniteDimensional F W] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hd : finrank F W = 10) {t : sesqSpecialUnitaryGroup B}
    (ht2 : orderOf t = 2) {e : W} (he0 : e ≠ 0) (he : B e e = 0)
    (ht : suEnd B t = hermTransvection B e 1) : Conclusion (sesqSpecialUnitaryGroup B) t := by
  intro hext hcard K hK hperf hN
  have : Finite F := hF.finite
  have : Finite W := Module.finite_of_finite F
  have : Finite (W →ₗ[F] W) := Finite.of_injective _ DFunLike.coe_injective
  have hd3 : 3 ≤ finrank F W := by omega
  have hψ := centGL_injective t
  obtain ⟨⟨f, hef, hff⟩, hsplit⟩ := hermitian_hyperbolic_splitting hF hB hBl he0 he
  obtain ⟨-, -, hc, hPl, hPdim⟩ := hsplit f hef hff
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hRle, hreg⟩ :=
    four_element_unitary_axis_flag_kernel_and_regular_orbit hF hB hBl hd3 he0 he
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := hreg f hff hef
  set tC : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) :=
    ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have htZ : tC ∈ center (centralizer ({t} : Set (sesqSpecialUnitaryGroup B))) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have htN : tC ∈ timmesfeldFStar (centralizer ({t} : Set (sesqSpecialUnitaryGroup B))) :=
    le_timmesfeldFStar_of_normal (center _).normal_of_characteristic
      (fun a _ b hb => mem_center_iff.mp hb a) htZ
  have hψt : centGL t tC = hermTransvectionGL B he 1 := Units.ext ht
  have hTmem : hermTransvectionGL B he 1 ∈ (timmesfeldFStar _).map (centGL t) :=
    ⟨tC, htN, hψt⟩
  have hP : IsExtraspecialPGroup 2 ((timmesfeldFStar
      (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))).map (centGL t)) :=
    (Bridge.timmesfeldIsExtraspecial_iff _).mp (Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      ((timmesfeldFStar _).equivMapOfInjective _ hψ) hext)
  have hPcard : Nat.card ((timmesfeldFStar
      (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))).map (centGL t)) = 2 ^ (1 + 2 * 8) := by
    rw [card_map_of_injective hψ, hcard]
  have hPU : (timmesfeldFStar (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))).map
      (centGL t) ≤ sesqUnitaryGroup B := by
    rintro _ ⟨x, -, rfl⟩
    exact sesqSpecialUnitaryGroup_le B ((x : centralizer _) : sesqSpecialUnitaryGroup B).2
  have hZ : center ((timmesfeldFStar (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))).map
      (centGL t)) = zpowers ⟨_, hTmem⟩ := by
    have hle : zpowers (⟨_, hTmem⟩ : (timmesfeldFStar _).map (centGL t)) ≤ center _ := by
      rw [zpowers_le]
      refine mem_center_iff.mpr fun g => ?_
      obtain ⟨_, ⟨x, -, rfl⟩⟩ := g
      apply Subtype.ext
      change centGL t x * hermTransvectionGL B he 1 = hermTransvectionGL B he 1 * centGL t x
      rw [← hψt, ← map_mul, ← map_mul, mem_center_iff.mp htZ x]
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [hP.2.2.2, Nat.card_zpowers, ← Subgroup.orderOf_coe]
    change 2 ≤ orderOf (hermTransvectionGL B he 1)
    rw [← hψt, orderOf_injective _ hψ, ← Subgroup.orderOf_coe, ht2]
  obtain ⟨-, _, -, -, -, hEq⟩ :=
    CFSG.LieType.unitary_extraspecial_central_transvection_width_and_equality
      hF hB hBl hd3 _ hPU (n := 8) (by norm_num) hP hPcard he0 he hTmem hZ hff hef
  have hNR := (hEq (by omega)).2.2.2
  have hKe := apply_eq_of_mem_of_perfect he0 hef ht hperf
  have hRK : axisKernel B e ≤ K.map (centGL t) := hNR ▸ map_mono hN
  have hKSU : K.map (centGL t) ≤ sesqSpecialUnitaryGroup B := by
    rintro _ ⟨x, -, rfl⟩
    exact ((x : centralizer _) : sesqSpecialUnitaryGroup B).2
  have hKe' : ∀ k ∈ K.map (centGL t),
      ((k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) e = e := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKe x hx
  have hcardK := card_eq_mul_card_inf_stabEF hB hff hef hc huniq hRle hRK hKSU hKe'
  have hPs : (B.domRestrict₁₂ (partnerPerp B e f) (partnerPerp B e f)).IsSymm :=
    ⟨fun x y => hB.eq x y⟩
  have hPdim' : finrank F (partnerPerp B e f) = 8 := by
    change finrank F ((Submodule.span F {e, f}).orthogonalBilin B) = 8
    omega
  have : IsSimpleGroup (sesqSpecialUnitaryGroup
      (B.domRestrict₁₂ (partnerPerp B e f) (partnerPerp B e f))) :=
    isSimpleGroup_sesqSpecialUnitaryGroup hF hPs hPl hPdim' (by norm_num) (by norm_num)
  set φ := (extGL hc).comp (sesqSpecialUnitaryGroup
    (B.domRestrict₁₂ (partnerPerp B e f) (partnerPerp B e f))).subtype with hφdef
  have hφ : Function.Injective φ := (extGL_injective hc).comp Subtype.val_injective
  have hφS : ∀ σ, φ σ ∈ stabEF hc := fun σ => ⟨σ, σ.2, rfl⟩
  have hL₀ : ((K.map (centGL t) ⊓ stabEF hc).comap φ).Normal := by
    refine ⟨fun σ hσ τ => ⟨?_, hφS _⟩⟩
    obtain ⟨k, hk, hkσ⟩ := hσ.1
    obtain ⟨hτSU, hτe, -⟩ := (mem_stabEF hB hc).mp (hφS τ)
    have hτt : (⟨φ τ, hτSU⟩ : sesqSpecialUnitaryGroup B) ∈
        centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) := by
      refine mem_centralizer_singleton_iff.mpr (suEnd_injective ?_)
      rw [map_mul, map_mul, ht]
      exact commute_hermTransvection_of_apply_eq (sesqSpecialUnitaryGroup_le B hτSU) hτe
    refine ⟨⟨⟨φ τ, hτSU⟩, hτt⟩ * k * ⟨⟨φ τ, hτSU⟩, hτt⟩⁻¹, hK.conj_mem k hk _, ?_⟩
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hkσ]
    rfl
  have hLdvd : 2 ^ 28 ∣ Nat.card ↥(K.map (centGL t) ⊓ stabEF hc) := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ((K.map (centGL t) ⊓ stabEF hc).comap φ) with h | h
    · exfalso
      have hL1 : Nat.card ↥(K.map (centGL t) ⊓ stabEF hc) = 1 := by
        rw [Subgroup.card_eq_one, eq_bot_iff]
        intro l hl
        obtain ⟨σ, hσ, hσl⟩ := hl.2
        have hmem : (⟨σ, hσ⟩ : sesqSpecialUnitaryGroup _) ∈
            (K.map (centGL t) ⊓ stabEF hc).comap φ := by
          change φ ⟨σ, hσ⟩ ∈ K.map (centGL t) ⊓ stabEF hc
          rw [show φ ⟨σ, hσ⟩ = l from hσl]
          exact hl
        rw [h, mem_bot] at hmem
        rw [mem_bot, ← hσl]
        have hσ1 : σ = 1 := congrArg Subtype.val hmem
        rw [hσ1, map_one]
      have hKN : Nat.card K ≤ Nat.card (timmesfeldFStar
          (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))) := by
        rw [← card_map_of_injective (K := K) hψ, hcardK, hL1, mul_one, ← hNR,
          card_map_of_injective hψ]
      have hNK := eq_of_le_of_card_ge hN hKN
      rw [← hNK] at hperf
      rw [eq_bot_of_isPGroup_of_perfect hext.1 hperf, card_bot] at hcard
      norm_num at hcard
    · have hle : φ.range ≤ K.map (centGL t) ⊓ stabEF hc := by
        rintro _ ⟨σ, rfl⟩
        have hσ : σ ∈ (K.map (centGL t) ⊓ stabEF hc).comap φ := h ▸ mem_top σ
        exact hσ
      have h1 : Nat.card φ.range = Nat.card (sesqSpecialUnitaryGroup
          (B.domRestrict₁₂ (partnerPerp B e f) (partnerPerp B e f))) :=
        Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
      have h2 := two_pow_dvd_card_sesqSpecialUnitaryGroup hF hPs hPl hPdim' (by norm_num)
      norm_num at h2
      exact h2.trans (h1 ▸ card_dvd_of_le hle)
  rw [← card_map_of_injective (K := K) hψ, hcardK, ← hNR, card_map_of_injective hψ, hcard,
    show (2 : ℕ) ^ 45 = 2 ^ 17 * 2 ^ 28 by norm_num]
  exact Nat.mul_dvd_mul_left _ hLdvd

theorem conclusion_unitary [FiniteDimensional F W] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : finrank F W = 10) {t : sesqSpecialUnitaryGroup B} (ht : orderOf t = 2) :
    Conclusion (sesqSpecialUnitaryGroup B) t := by
  intro hext
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, sq] at h
  have ht1 : t ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨e, he0, he, hte⟩ := exists_eq_hermTransvection hB hBl htt ht1 hext.1 hext.2.2.2
  exact conclusion_hermTransvection hB hBl hd ht he0 he hte hext

end CFSG.LargeExtraspecial.S14.PSLPSU10
