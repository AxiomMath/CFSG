module

public import CFSG.GF2Type.Smith1979.IdxFourIdent
public import CFSG.GF2Type.Smith1979.IdxFourFpf
public import CFSG.GF2Type.Smith1979.GammaU.Dict2
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Assembly.GL83LieDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module CFSG.LargeExtraspecial
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.Dict
open CFSG.LieType.Multipliers.U43 (X₀)

theorem eq_or_eq_inv_of_mem_zpowers {H : Type*} [Group H] {θ y : H} (hθ3 : θ ^ 3 = 1)
    (hy : y ∈ zpowers θ) (hy1 : y ≠ 1) : y = θ ∨ y = θ⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h3 : θ ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hθ3
  have hk : θ ^ k = θ ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h
  · exact absurd (by rw [hk, h, zpow_zero]) hy1
  · left
    rw [hk, h, zpow_one]
  · right
    rw [hk, h]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← zpow_add_one]
    exact h3

theorem center_map_map_subtype {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (H : Subgroup A) :
    (center (H.map f)).map (H.map f).subtype = ((center H).map H.subtype).map f := by
  rw [← Subgroup.map_center_eq (H.equivMapOfInjective f hf), Subgroup.map_map, Subgroup.map_map]
  rfl

theorem exists_proj_of_map {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (H : Subgroup A) {P : Type*} [Group P] (π : H →* P)
    (hπ : Function.Surjective π) (hk : π.ker = center H) :
    ∃ π' : H.map f →* P, Function.Surjective π' ∧ π'.ker = center (H.map f) := by
  refine ⟨π.comp ((H.equivMapOfInjective f hf).symm : H.map f →* H),
    hπ.comp (H.equivMapOfInjective f hf).symm.surjective, ?_⟩
  rw [MonoidHom.ker_comp_mulEquiv, hk, MulEquiv.symm_symm, Subgroup.map_center_eq]

theorem conj_mem_map_of_normal {A B : Type*} [Group A] [Group B] (f : A →* B) {E : Subgroup A}
    (hE : E.Normal) : ∀ x ∈ (⊤ : Subgroup A).map f, ∀ e ∈ E.map f, x * e * x⁻¹ ∈ E.map f := by
  rintro _ ⟨m, -, rfl⟩ _ ⟨e, he, rfl⟩
  exact ⟨m * e * m⁻¹, hE.conj_mem e he m, by rw [map_mul, map_mul, map_inv]⟩

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def kappa (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V12) :
    S.Mbar →* (V12 ≃ₗ[ZMod 2] V12) :=
  (trEquiv φ).toMonoidHom.comp (S.O.subtype.comp S.Mbar.subtype)

theorem kappa_apply (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V12) (m : S.Mbar) :
    kappa S φ m = trEquiv φ ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl

theorem kappa_injective (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V12) :
    Function.Injective (kappa S φ) :=
  (trEquiv φ).injective.comp (S.O.subtype_injective.comp S.Mbar.subtype_injective)

theorem layer_data {E : Type} [Group E] {θ : E} (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1)
    (hcen : center E = zpowers θ)
    (hmodel : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1) :
    ∃ π : E →* X₀, Function.Surjective π ∧ π.ker = center E ∧ Nat.card E = 9797760 := by
  obtain ⟨e⟩ := Case25.U43Weights.nonempty_mulEquiv_X₀_of_stated hmodel
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center E)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · have hX := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three hmodel
    have hZ : Nat.card (center E) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [hcen, Nat.card_zpowers, orderOf_eq_prime hθ3 hθ1]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center E), hX, hZ]

theorem fixedPointFree_of_layer (S : Setting G) (hw : S.width = 6) (E : Subgroup S.Mbar)
    {θ : S.Mbar} (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1) (hZ : (center E).map E.subtype = zpowers θ)
    (hmodel : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1) :
    ∀ v : S.Qt, (((θ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 := by
  have hθE : θ ∈ E := by
    obtain ⟨c, -, hc⟩ := (hZ ▸ mem_zpowers θ : θ ∈ (center E).map E.subtype)
    exact hc ▸ c.2
  set θE : E := ⟨θ, hθE⟩ with hθEdef
  have hcen : center E = zpowers θE := by
    apply Subgroup.map_injective E.subtype_injective
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  have hθE3 : θE ^ 3 = 1 := Subtype.ext (by simpa using hθ3)
  have hθE1 : θE ≠ 1 := fun h => hθ1 (by simpa [hθEdef] using congrArg Subtype.val h)
  obtain ⟨π, hπ, hker, hcard⟩ := layer_data hθE3 hθE1 hcen hmodel
  let ι : E →* (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.O.subtype.comp (S.Mbar.subtype.comp E.subtype)
  have hι : Function.Injective ι :=
    S.O.subtype_injective.comp (S.Mbar.subtype_injective.comp E.subtype_injective)
  have hθc : ∀ e : E, e * θE = θE * e :=
    Subgroup.mem_center_iff.mp (hcen ▸ mem_zpowers θE)
  intro v hv
  exact fixedPointFree_of_center ι hι (by rw [S.finrank_Qt_eq_two_mul_width, hw]) hθE3 hθc π hπ
    (hker.trans hcen) (by rw [hcard]; norm_num) v hv

theorem map_trEquiv_trans {S : Setting G} (φ : S.Qt ≃ₗ[ZMod 2] V12) (t : V12 ≃ₗ[ZMod 2] V12) :
    (S.Mbar.map S.O.subtype).map (trEquiv (φ.trans t)).toMonoidHom =
      conjSub ((⊤ : Subgroup S.Mbar).map (kappa S φ)) t := by
  ext y
  rw [mem_conjSub]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨⟨m, hm⟩, mem_top _, ?_⟩
    rw [kappa_apply]
    show trEquiv φ m = t⁻¹ * trEquiv (φ.trans t) m * t
    rw [trEquiv_trans]
    group
  · rintro ⟨m, -, hm⟩
    refine ⟨_, ⟨(m : S.O), m.2, rfl⟩, ?_⟩
    show trEquiv (φ.trans t) ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = y
    rw [trEquiv_trans, ← kappa_apply, hm]
    group

theorem exists_isometry_map_eq_M0 (S : Setting G) (hw : S.width = 6) (E : Subgroup S.Mbar)
    (hEn : E.Normal) (hidx : E.index = 4) {θ : S.Mbar} (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1)
    (hZ : (center E).map E.subtype = zpowers θ) (hZn : (zpowers θ).Normal)
    (hmodel : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1)
    (hM0card : Nat.card M0 = 39191040) :
    ∃ ψ : S.Qt ≃ₗ[ZMod 2] V12, (∀ v, q0 (ψ v) = S.q v) ∧ ThetaCompat ψ (θ : S.O) ∧
      (S.Mbar.map S.O.subtype).map (trEquiv ψ).toMonoidHom = M0 := by
  classical
  have hfix := fixedPointFree_of_layer S hw E hθ3 hθ1 hZ hmodel
  have hθO3 : ((θ : S.O)) ^ 3 = 1 := by simpa using congrArg (fun x : S.Mbar => (x : S.O)) hθ3
  obtain ⟨φ₀, hq0, hθ0⟩ := exists_isometry_theta0_of_setting S hw hθO3 hfix
  have hθc : ThetaCompat φ₀ (θ : S.O) := Or.inl hθ0
  have hθE : θ ∈ E := by
    obtain ⟨c, -, hc⟩ := (hZ ▸ mem_zpowers θ : θ ∈ (center E).map E.subtype)
    exact hc ▸ c.2
  set θE : E := ⟨θ, hθE⟩ with hθEdef
  have hcen : center E = zpowers θE := by
    apply Subgroup.map_injective E.subtype_injective
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  have hθE3 : θE ^ 3 = 1 := Subtype.ext (by simpa using hθ3)
  have hθE1 : θE ≠ 1 := fun h => hθ1 (by simpa [hθEdef] using congrArg Subtype.val h)
  obtain ⟨π, hπ, hker, hcardE⟩ := layer_data hθE3 hθE1 hcen hmodel
  have hκ := kappa_injective S φ₀
  have hκθ : kappa S φ₀ θ = theta0e := LinearEquiv.ext fun v => by
    rw [kappa_apply, trEquiv_apply, hθ0, LinearEquiv.apply_symm_apply]
    rfl
  have hcardM : Nat.card S.Mbar = 39191040 := by
    rw [← Subgroup.card_mul_index E, hidx, hcardE]
  have hM : ∀ m : S.Mbar, (m : S.O) * (θ : S.O) * (m : S.O)⁻¹ = θ ∨
      (m : S.O) * (θ : S.O) * (m : S.O)⁻¹ = (θ : S.O)⁻¹ := by
    intro m
    have hmem : m * θ * m⁻¹ ∈ zpowers θ := hZn.conj_mem θ (mem_zpowers θ) m
    have hne : m * θ * m⁻¹ ≠ 1 := by
      intro h
      apply hθ1
      rw [mul_inv_eq_one, mul_eq_left] at h
      exact h
    rcases eq_or_eq_inv_of_mem_zpowers hθ3 hmem hne with h | h
    · exact Or.inl (by simpa using congrArg (fun x : S.Mbar => (x : S.O)) h)
    · exact Or.inr (by simpa using congrArg (fun x : S.Mbar => (x : S.O)) h)
  have hXg : (⊤ : Subgroup S.Mbar).map (kappa S φ₀) ≤ gammaU := by
    rintro _ ⟨m, -, rfl⟩
    refine mem_gammaU_of_conj (fun v => ?_) (conj_thetaU_tr hθc (hM m))
    rw [kappa_apply, trEquiv_apply, hq0,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (m : S.O).2, ← hq0,
      LinearEquiv.apply_symm_apply]
  have hXcard : Nat.card ((⊤ : Subgroup S.Mbar).map (kappa S φ₀)) = 39191040 := by
    rw [Subgroup.card_map_of_injective hκ, Subgroup.card_top, hcardM]
  obtain ⟨π', hπ', hk'⟩ := exists_proj_of_map hκ E π hπ hker
  have hZ' : (center (E.map (kappa S φ₀))).map (E.map (kappa S φ₀)).subtype =
      zpowers theta0e := by
    rw [center_map_map_subtype hκ, hZ, MonoidHom.map_zpowers, hκθ]
  let C : Ctx :=
    { X := (⊤ : Subgroup S.Mbar).map (kappa S φ₀)
      E := E.map (kappa S φ₀)
      hXg := hXg
      hEX := Subgroup.map_mono le_top
      hEnorm := conj_mem_map_of_normal (kappa S φ₀) hEn
      hX4 := by
        rw [hXcard, Subgroup.card_map_of_injective hκ, hcardE]
      hXcard := hXcard
      π := π'
      hπs := hπ'
      hπk := hk'
      hZ := hZ' }
  obtain ⟨t, htg, ht⟩ := exists_conj_eq_M0 C hM0card
  refine ⟨φ₀.trans t, fun v => ?_, ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, htg.1, hq0]
  · rcases htg.2 with h | h
    · exact Or.inl fun v => by rw [LinearEquiv.trans_apply, hθ0, h]; rfl
    · exact Or.inr fun v => by rw [LinearEquiv.trans_apply, hθ0, h]; rfl
  · rw [← ht]
    exact map_trEquiv_trans φ₀ t

end CFSG.GF2Type.Smith1979.IdxFour
