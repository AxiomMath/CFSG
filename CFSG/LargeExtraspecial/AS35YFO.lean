module

public import CFSG.LargeExtraspecial.AS35YFHub
public import CFSG.LargeExtraspecial.S12InspFamDO

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap Matrix
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Recognition.SymO
  CFSG.ClassicalGroups.Orthogonal

namespace Setting

theorem asc_exists_orth_mulEquiv {X : Type*} [Group X] {D : Set X} {m : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hmod : CFSG.Open.fischerLinearModel D
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) {d : X} (hd : d ∈ D) :
    ∃ ψ : X ≃* TauCeti.QuadraticMap.orthogonalGroup Q, ∃ v, Q v = 1 ∧
      ∀ x, ((ψ d : TauCeti.QuadraticMap.orthogonalGroup Q) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x = x + polar Q x v • v := by
  obtain ⟨φ, hφ⟩ := hmod
  obtain ⟨v, hv, hφt⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ _).mp hd)
  have hmap : (CFSG.Open.fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x, Q (A *ᵥ x) = Q x).map (toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap,
      Subgroup.map_comap_eq_self_of_surjective (toLinEquiv (Fin (2 * m)) (ZMod 2)).surjective]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X ≃* TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ x, ((ψ x : TauCeti.QuadraticMap.orthogonalGroup Q) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) =
        toLinEquiv (Fin (2 * m)) (ZMod 2) (φ x : GL (Fin (2 * m)) (ZMod 2)) :=
    ⟨φ.trans (((toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap _).trans
      (MulEquiv.subgroupCongr hmap)), fun x => rfl⟩
  exact ⟨ψ, v, hv, fun x => by
    rw [hψ, hφt, toLinEquiv_orthTransvectionGL, reflect_apply_of_map_eq_one hv]⟩

section Generic

variable {Xh : Type*} [Group Xh] {τ : Xh} {𝒜 : Set (MulAut Xh)}

theorem asc_false_of_orth_ge_four_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ) {m : ℕ} (hm : 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (ψ : Xh ≃* TauCeti.QuadraticMap.orthogonalGroup Q)
    {v : Fin (2 * m) → ZMod 2} (hv : Q v = 1)
    (ht' : ∀ x, ((ψ τ : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x = x + polar Q x v • v) :
    False := by
  have hQ := polarBilin_nondegenerate hnd
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hQ hv
  have hB' : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  have hnd' : ((bil Q).restrict (perp Q v y)).Nondegenerate :=
    (bil_isAlt Q).restrict_nondegenerate_orthogonal_span_pair (bil_eq_one hyv) hQ
  have hdim := finrank_perp hQ hyv
  have hSimp := isSimpleGroup_isometryGroup _ hB' hnd' hdim (by omega)
  have : Nontrivial (perp Q v y) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hsurj := rho_surjective hQ hv hyv _ ht' hSimp (exists_ne 0)
  have : Finite (perp Q v y ≃ₗ[ZMod 2] perp Q v y) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hns : ¬ Group.IsSolvable
      (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) := by
    refine s12_not_isSolvable_of_simple ?_
    rw [card_isometryGroup_two _ hB' hnd' hdim]
    exact S12InspO.not_prime_card_sp (by omega)
  have hker : ∀ k ∈ (rho hQ hv hyv _ ht').ker, ∀ x, k * x = x * k := fun k hk =>
    S12InspO.mul_comm_of_eq_one_or_eq (S12InspO.rho_ker_eq hQ hv hyv _ ht' hk)
  exact asc_false_of_centralizer_hom_simple_equiv hub h𝒜 ψ hns (rho hQ hv hyv _ ht') hsurj hker

theorem asc_false_of_orth_six_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ) {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (ψ : Xh ≃* TauCeti.QuadraticMap.orthogonalGroup Q)
    {v : Fin (2 * 3) → ZMod 2} (hv : Q v = 1)
    (ht' : ∀ x, ((ψ τ : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin (2 * 3) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 3) → ZMod 2)) x = x + polar Q x v • v) :
    False := by
  have hQ := polarBilin_nondegenerate hnd
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hQ hv
  have hB' : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  have hnd' : ((bil Q).restrict (perp Q v y)).Nondegenerate :=
    (bil_isAlt Q).restrict_nondegenerate_orthogonal_span_pair (bil_eq_one hyv) hQ
  have hdim := finrank_perp hQ hyv
  have : Nontrivial (perp Q v y) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨φ₆⟩ := S12InspO.nonempty_isometryGroup_mulEquiv_perm_six _ hB' hnd' (by omega)
  obtain ⟨N, hNn, hN1, hNle⟩ := S12InspO.exists_normal_le_range_rho hQ hv hyv _ ht' (exists_ne 0)
  set σ : centralizer ({ψ τ} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) →*
    Equiv.Perm (Fin 6) := φ₆.toMonoidHom.comp (rho hQ hv hyv _ ht') with hσdef
  have hA6 : alternatingGroup (Fin 6) ≤ σ.range := by
    have hNn' : (N.map φ₆.toMonoidHom).Normal := hNn.map _ φ₆.surjective
    have hnt : Nontrivial (N.map φ₆.toMonoidHom) := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro h
      exact hN1 ((Subgroup.map_eq_bot_iff_of_injective _ φ₆.injective).mp h)
    refine (Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hnt).trans ?_
    rw [hσdef, MonoidHom.range_comp]
    exact Subgroup.map_mono hNle
  have hcomm6 : (commutator (centralizer ({ψ τ} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)))).map σ = alternatingGroup (Fin 6) := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    exact S12InspO.commutator_eq_alternatingGroup_six hA6
  have hker : ∀ k ∈ σ.ker, ∀ x, k * x = x * k := fun k hk => by
    rw [hσdef, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at hk
    exact S12InspO.mul_comm_of_eq_one_or_eq
      (S12InspO.rho_ker_eq hQ hv hyv _ ht' (MonoidHom.mem_ker.mpr hk))
  obtain ⟨σ', hσ', hker'⟩ := S12InspO.exists_commutator_hom σ hcomm6 hker
  have := S12InspO.isSimpleGroup_alternatingGroup_six
  exact asc_false_of_centralizer_commutator_hom_simple_equiv hub h𝒜 ψ
    S12InspO.not_isSolvable_alternatingGroup_six σ' hσ' hker'

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem asc_mem_Ehat [Finite G] {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) :
    (QuotientGroup.mk (ascTL htD htM) : S.LbarAsc ⧸ center S.LbarAsc) ∈ S.EhatAsc :=
  ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩

variable (hst : S.Asc512Standing)
include hst

theorem asc_false_of_orth (h58 : S14.Asc512FiveEightStmt) (hP : S14.Asc512PbarStmt)
    (hS : S.SixHyp) {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {m : ℕ}
    (hm : 3 ≤ m) {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : CFSG.Open.fischerLinearModel S.EhatAsc
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨ψ, v, hv, ht'⟩ := asc_exists_orth_mulEquiv hmod (asc_mem_Ehat htD htM)
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · obtain rfl : m = 3 := by omega
    exact asc_false_of_orth_six_gen (asc_hub hst h58 hS htD htM)
      (asc_hub_fix hst hP hS htD htM) hnd ψ hv ht'
  · exact asc_false_of_orth_ge_four_gen (asc_hub hst h58 hS htD htM)
      (asc_hub_fix hst hP hS htD htM) hm4 hnd ψ hv ht'

end Setting

end CFSG.LargeExtraspecial
