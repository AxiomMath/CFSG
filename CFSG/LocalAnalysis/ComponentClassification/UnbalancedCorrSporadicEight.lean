module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSporadicDihedral
public import CFSG.Sporadic.GLQ.J4TwoRank
public import CFSG.Sporadic.GLQ.HNTwoRank
public import CFSG.Sporadic.GLQ.BTwoRank
public import CFSG.Sporadic.GLQ.MonsterTwoRank
public import CFSG.Sporadic.Schreier.LySylow
public import CFSG.Sporadic.Schreier.ONLocalOrders
public import CFSG.Sporadic.Bridge.MonsterModels

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Blueprint Blueprint.NativeSporadic

@[expose] def ONSylowCharacteristicElementaryEight : Prop :=
  Nat.card (Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x}) = 64 ∧
    IsElementaryAbelian 2 (Subgroup.closure
      {x | x ∈ Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} ∧ x ^ 2 = 1}) ∧
    Nat.card (Subgroup.closure
      {x | x ∈ Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} ∧ x ^ 2 = 1}) = 8 ∧
    ((Subgroup.closure
      {x | x ∈ Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} ∧ x ^ 2 = 1}).subgroupOf
        ONSchreier.onT).Characteristic

theorem exists_elementary_eight_of_injective {X T : Type*} [Group X] [Group T] [Finite X]
    (f : X →* T) (hf : Function.Injective f) {E : Subgroup X} (hE : IsElementaryAbelian 2 E)
    {k : ℕ} (hk : 3 ≤ k) (hcard : Nat.card E = 2 ^ k) :
    ∃ A : Subgroup T, IsElementaryAbelian 2 A ∧ Nat.card A = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3) (G := E)
    (by rw [hcard]; exact pow_dvd_pow 2 hk)
  have hFe : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
        (hE.toIsMulCommutative.is_comm.comm (a : E) (b : E))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) (x : E)) }
  have hinj : Function.Injective (f.comp E.subtype) := fun x y h =>
    E.subtype_injective (hf h)
  refine ⟨F.map (f.comp E.subtype), IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, hF]
  norm_num

theorem six_sporadic_models_have_elementary_eight_of_ON
    (hON : ONSylowCharacteristicElementaryEight) : SixSporadicElementaryEight := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T _ _ _ hT
  rcases hT with h | h | h | h | h | h
  ·
    obtain ⟨e⟩ : Nonempty (T ≃* Carrier .ONan) := h
    obtain ⟨-, hA, hcard, -⟩ := hON
    set D := Subgroup.closure {x | ∃ t ∈ ONSchreier.onT, t ^ 2 = x} with hD
    set A := Subgroup.closure {x | x ∈ D ∧ x ^ 2 = 1} with hAdef
    have hDT : D ≤ ONSchreier.onT := by
      rw [hD, Subgroup.closure_le]
      rintro _ ⟨t, ht, rfl⟩
      exact pow_mem ht 2
    have hAP : A ≤ ONSchreier.Pv := by
      have hAD : A ≤ D := by
        rw [hAdef, Subgroup.closure_le]
        exact fun x hx => hx.1
      exact hAD.trans (hDT.trans ONSchreier.onT_le)
    have hA' : IsElementaryAbelian 2 (A.subgroupOf ONSchreier.Pv) :=
      IsElementaryAbelian.subgroupOf hAP
    have hcard' : Nat.card (A.subgroupOf ONSchreier.Pv) = 2 ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hcard]
      norm_num
    let φ : ↥ONSchreier.Pv ≃* T := ONSchreier.onEquivPv.symm.trans e.symm
    exact exists_elementary_eight_of_injective φ.toMonoidHom φ.injective hA' le_rfl hcard'
  ·
    obtain ⟨e⟩ : Nonempty (T ≃* Carrier .Ly) := h
    obtain ⟨-, -, -, -, -, -, -, ⟨E₁, E₂, -, hiff, -⟩, -⟩ :=
      Sporadic.LySchreier.sylow_structure_automorphisms
    obtain ⟨hE, hcard⟩ := (hiff E₁).mpr (Or.inl rfl)
    let φ : ↥Sporadic.Ly.J ≃* T := Sporadic.Ly.lyEquivJ.symm.trans e.symm
    let ψ : ↥Sporadic.Ly.J →* T := (φ : ↥Sporadic.Ly.J →* T)
    have hψ : Function.Injective ψ := fun x y hxy => φ.injective hxy
    have hE' : IsElementaryAbelian 2 ((E₁.map Sporadic.LySchreier.lyS.subtype).map ψ) := by
      have : IsElementaryAbelian 2 E₁ := hE
      have : IsElementaryAbelian 2 (E₁.map Sporadic.LySchreier.lyS.subtype) :=
        IsElementaryAbelian.map_subtype
      exact IsElementaryAbelian.map _
    have hcard' : Nat.card ((E₁.map Sporadic.LySchreier.lyS.subtype).map ψ) = 2 ^ 4 := by
      rw [Subgroup.card_map_of_injective hψ,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]
      norm_num
    exact exists_elementary_eight_of_injective (MonoidHom.id T) Function.injective_id hE'
      (by norm_num) hcard'
  ·
    obtain ⟨⟨E, hE, hcard⟩, -⟩ := Sporadic.GLQ.j4_two_rank_at_least_eleven T h
    exact exists_elementary_eight_of_injective (MonoidHom.id T) Function.injective_id hE
      (by norm_num) hcard
  ·
    obtain ⟨⟨E, hE, hcard⟩, -⟩ := Sporadic.GLQ.hn_two_rank_at_least_five.2.2.2.2.2 T h
    exact exists_elementary_eight_of_injective (MonoidHom.id T) Function.injective_id hE
      (k := 5) (by norm_num) (by rw [hcard]; norm_num)
  ·
    obtain ⟨⟨E, hE, hcard⟩, -⟩ := Sporadic.GLQ.b_two_rank_at_least_five T h
    exact exists_elementary_eight_of_injective (MonoidHom.id T) Function.injective_id hE
      (k := 5) (by norm_num) (by rw [hcard]; norm_num)
  ·
    obtain ⟨e⟩ : Nonempty (T ≃* Carrier .M) := h
    let e' : T ≃* CFSG.Open.MonsterY443Derived :=
      e.trans CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen
    have : Finite CFSG.Open.MonsterY443Derived := Finite.of_surjective e' e'.surjective
    have hne : CFSG.Open.MonsterY443Derived ≠ ⊥ := by
      have : Nontrivial CFSG.Open.MonsterY443Derived := e'.injective.nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this
    obtain ⟨E, hE, hcard⟩ := Sporadic.GLQ.monster_nontrivial_two_rank_at_least_six.{0}.1 hne
    exact exists_elementary_eight_of_injective e'.symm.toMonoidHom e'.symm.injective hE
      (k := 6) (by norm_num) (by rw [hcard]; norm_num)

theorem dihedralSylowSporadicExclusion_of_inputs_ON (hQ8 : FourSporadicQuaternionEight)
    (hBin : SixBinarySporadicDihedralExclusion)
    (hPerm : EightPermutationSporadicDihedralExclusion)
    (hON : ONSylowCharacteristicElementaryEight) : DihedralSylowSporadicExclusion :=
  dihedralSylowSporadicExclusion_of_inputs hQ8 hBin hPerm
    (six_sporadic_models_have_elementary_eight_of_ON hON)

end CFSG.ComponentClassification.UnbalancedCorr
