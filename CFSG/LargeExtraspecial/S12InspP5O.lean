module

public import CFSG.LargeExtraspecial.S12InspP5Hyp
public import CFSG.LargeExtraspecial.S12InspP4Ord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix QuadraticMap CFSG.Open CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal

namespace S12InspP5

theorem orthTransvection_not_mem_commutator {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)} (hQ : (polarBilin Q).Nondegenerate)
    {v : ι → ZMod 2} (hv : Q v = 1) {h : S12Tri.OG Q}
    (hh : (h : GL ι (ZMod 2)) = orthTransvectionGL Q v) : h ∉ commutator (S12Tri.OG Q) := by
  have hmem : ∀ x : S12Tri.OG Q, toLinEquiv ι (ZMod 2) (x : GL ι (ZMod 2)) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun x => by
    have hx : (x : GL ι (ZMod 2)) ∈
        (fischerMatrixGroup fun A : Matrix ι ι (ZMod 2) => ∀ y, Q (A *ᵥ y) = Q y) := x.2
    rw [fischerMatrixGroup_isometry_eq_comap] at hx
    exact hx
  let ψ : S12Tri.OG Q →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    ((toLinEquiv ι (ZMod 2)).toMonoidHom.comp (S12Tri.OG Q).subtype).codRestrict _ hmem
  intro hc
  have hk := Abelianization.commutator_subset_ker ((dicksonHom Q hQ).comp ψ) hc
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, dicksonHom_apply] at hk
  have hψ : ((ψ h : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) = reflect Q v := by
    show toLinEquiv ι (ZMod 2) (h : GL ι (ZMod 2)) = reflect Q v
    rw [hh, toLinEquiv_orthTransvectionGL]
  have : Invertible (Q v) := by rw [hv]; exact invertibleOne
  have h1 : finrank (ZMod 2) (commSpace (reflect Q v)) = 1 := by
    rw [reflect_eq_reflection]
    exact finrank_commSpace_reflection hQ v
  rw [hψ, h1] at hk
  exact absurd hk (by decide)

end S12InspP5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem not_mem_commutator_of_orth {g : G} {t : S.O} (htE : t ∈ S.Ebar12 g) {m : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1)) :
    (⟨t, subset_Xbar12 htE⟩ : S.Xbar12 g) ∉ commutator (S.Xbar12 g) := by
  obtain ⟨φ, hφ⟩ := hmod
  have hQ : (polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [polar_comm]; simpa using hy x⟩
  obtain ⟨v, hv, hgv⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections
    ((hφ ⟨t, subset_Xbar12 htE⟩).mp htE)
  intro hmem
  exact S12InspP5.orthTransvection_not_mem_commutator hQ hv hgv
    ((S12Tri.apply_mem_commutator_iff φ).mpr hmem)

theorem false_of_orth_minus_four_insp4 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hdeg : ¬ S.IsNondeg12 g) (hM : 25920 ∣ Nat.card S.Mbar)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : fischerLinearModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨hH, hna⟩ := hyp_Xbar12 haQ hne hn ht htA hS hdeg
  have htE := mem_Ebar12_of_mem_Lbar ht htA
  have h2 := S12Tri.index_commutator_eq_two hH.pair (not_mem_commutator_of_orth htE hnd hmod)
  have hcX : Nat.card (S.Xbar12 g) = 120 := by
    rw [S12Insp4P.card_eq_card_orthogonalGroup_of_model hmod,
      S12Insp4P.card_orthogonalGroup_minus_four hnd hmin]
  have h60 : Nat.card (commutator (S.Xbar12 g)) = 60 := by
    have := (commutator (S.Xbar12 g)).card_mul_index
    rw [h2, hcX] at this
    omega
  have hNM : ⁅S.Xbar12 g, S.Xbar12 g⁆ ≤ S.Mbar := (commutator_le_self _).trans Xbar12_le_Mbar
  set N : Subgroup S.Mbar := (⁅S.Xbar12 g, S.Xbar12 g⁆ : Subgroup S.O).subgroupOf S.Mbar with hN
  have hNn : N.Normal := ⟨fun n hn m => by
    rw [hN, mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using conj_mem_commutator_Xbar12 m.2 hn⟩
  let e : N ≃* commutator (S.Xbar12 g) :=
    (subgroupOfEquivOfLe hNM).trans ((MulEquiv.subgroupCongr
      (map_subtype_commutator (S.Xbar12 g)).symm).trans
        ((commutator (S.Xbar12 g)).equivMapOfInjective _ (subtype_injective _)).symm)
  have := hH.simple
  have hs : IsSimpleGroup N := e.isSimpleGroup
  have hN60 : Nat.card N = 60 := (Nat.card_congr e.toEquiv).trans h60
  have hC : ∀ y : S.Mbar, (∀ q ∈ N, y * q = q * y) → y = 1 := fun y hy =>
    Subtype.ext (eq_one_of_commute_commutator_Xbar12 hS hH.center hH.simple hna y.2
      fun n hn => congrArg Subtype.val (hy ⟨n, hNM hn⟩ (mem_subgroupOf.mpr hn)))
  have h6 : 6 * Nat.card N ≤ Nat.card S.Mbar := by
    rw [hN60]
    have := Nat.le_of_dvd Nat.card_pos hM
    omega
  exact S12Tri.false_of_card_sixty hs hN60 hC h6

end Setting

end CFSG.LargeExtraspecial
