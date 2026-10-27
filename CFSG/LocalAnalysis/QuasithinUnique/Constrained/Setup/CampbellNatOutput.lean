module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNormalHull
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellOutput

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

section Aimg

variable {H : Type*} [Group H]

theorem characteristic_map_subtype_of_aimg_invariant {Gb S : Subgroup H} (hSG : S ≤ Gb)
    {N : Subgroup Gb}
    (hinv : ∀ γ : (S.subgroupOf Gb) ≃* (S.subgroupOf Gb), aimg (S.subgroupOf Gb) γ N = N) :
    ((N.map Gb.subtype).subgroupOf S).Characteristic := by
  let e : (S.subgroupOf Gb) ≃* S :=
    { toFun := fun x => ⟨((x : Gb) : H), x.2⟩
      invFun := fun s => ⟨⟨(s : H), hSG s.2⟩, s.2⟩
      left_inv := fun x => rfl
      right_inv := fun s => rfl
      map_mul' := fun x y => rfl }
  refine ⟨fun φ => ?_⟩
  ext s
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  let γ : (S.subgroupOf Gb) ≃* (S.subgroupOf Gb) := e.trans (φ.trans e.symm)
  have hmemN : ∀ x : S.subgroupOf Gb, ((x : Gb) : H) ∈ N.map Gb.subtype ↔ (x : Gb) ∈ N := by
    intro x
    exact Subgroup.mem_map_iff_mem Gb.subtype_injective
  have hγ : ∀ x : S.subgroupOf Gb, (γ x : Gb) ∈ N ↔ (x : Gb) ∈ N := by
    intro x
    have hN := hinv γ
    constructor
    · intro hx
      have : (γ x : Gb) ∈ aimg (S.subgroupOf Gb) γ N := by rw [hN]; exact hx
      obtain ⟨y, hy, hyx⟩ := mem_aimg.mp this
      have : y = x := γ.injective (Subtype.ext hyx)
      exact this ▸ hy
    · intro hx
      have : (γ x : Gb) ∈ aimg (S.subgroupOf Gb) γ N := mem_aimg.mpr ⟨x, hx, rfl⟩
      rw [hN] at this
      exact this
  obtain ⟨x, rfl⟩ := e.surjective s
  have h1 : (φ (e x) : H) = (((γ x : S.subgroupOf Gb) : Gb) : H) := rfl
  rw [h1, hmemN (γ x), hγ x]
  exact (hmemN x).symm

end Aimg

section Output

variable {H : Type*} [Group H] [Finite H] {k : Type*} [Field k] [Finite k] [CharP k 2]

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem actual_Campbell_natural_minimal_parabolic_output (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H)) (hnc : NoCharNormal R ⊤)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowTwoOf (elemBaumannIn 2 R) (baumannOvergroup R) ∧ CharTwo (baumannOvergroup R) ∧
      (baumannOvergroup R).map ρ = slGamma k ∧
      Vmod (baumannOvergroup R) =
        ⁅V.subgroupOf (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ ∧
      (∃ α : (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) ≃*
            (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R),
        aimg ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)) α (Vmod (baumannOvergroup R)) ⊓
            CFSG.pCore 2 (baumannOvergroup R) =
          aimg ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)) α
            (Vmod (baumannOvergroup R) ⊓ Subgroup.centralizer
              (((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) :
                Subgroup (baumannOvergroup R)) : Set (baumannOvergroup R))) ∧
        (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) =
          CFSG.pCore 2 (baumannOvergroup R) ⊔
            aimg ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)) α
              (Vmod (baumannOvergroup R))) ∧
      ⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ =
        Vmod (baumannOvergroup R) ∧
      Vmod (baumannOvergroup R) ≤ Ecore (baumannOvergroup R) ∧
      ∃ β : (⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
            Subgroup (baumannOvergroup R)) →* Multiplicative (Fin 2 → k),
        Function.Surjective β ∧
        β.ker = ((⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
              Subgroup (baumannOvergroup R)) ⊓ Subgroup.center (baumannOvergroup R)).subgroupOf
            (⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
              Subgroup (baumannOvergroup R)) ∧
        ∀ (g : baumannOvergroup R)
          (u u' : (⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
            Subgroup (baumannOvergroup R))),
          (u' : baumannOvergroup R) = g * u * g⁻¹ →
            Multiplicative.toAdd (β u') =
              (h.actualRho hJ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (β u)) := by
  classical
  obtain ⟨h1, h3, h10, hρ, hfrat, hJeq, hseed, hEeq, hψE, hKodd, hVmod⟩ :=
    h.actual_Baumann_whole_center_natural_module hchar hnc hJ
  obtain ⟨ψE, hE, hext⟩ := hseed.toEcore
  have hSG : elemBaumannIn 2 R ≤ baumannOvergroup R := le_sup_right
  have hcharG : ∀ N : Subgroup (baumannOvergroup R),
      N ≤ ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)) →
      (∀ γ : ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)) ≃*
          ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)),
        aimg ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R))
          γ N = N) → N.Normal → N = ⊥ := by
    intro N hNS hinv hNn
    by_contra hN0
    have hCchar := characteristic_map_subtype_of_aimg_invariant hSG
      (N := N) (by exact hinv)
    have hCS : N.map (baumannOvergroup R).subtype ≤ elemBaumannIn 2 R := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hNS hx)
    have hC0 : N.map (baumannOvergroup R).subtype ≠ ⊥ := fun hb =>
      hN0 ((Subgroup.map_eq_bot_iff_of_injective N (baumannOvergroup R).subtype_injective).mp hb)
    have key : ∀ g ∈ baumannOvergroup R, ∀ c ∈ N.map (baumannOvergroup R).subtype,
        g * c * g⁻¹ ∈ N.map (baumannOvergroup R).subtype := by
      rintro g hg _ ⟨y, hy, rfl⟩
      exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hNn.conj_mem y hy ⟨g, hg⟩, rfl⟩
    refine h10 _ hCS hC0 hCchar ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key g hg x, fun hx => by simpa [mul_assoc] using key g⁻¹ ((baumannOvergroup R).inv_mem hg) _ hx⟩
  obtain ⟨α, hα1, hα2⟩ := hE.characteristic_obstruction_produces_Sylow_supplement hcharG
  obtain ⟨hQK, hVE, β, hβs, hβk, hβe⟩ :=
    natural_center_Sylow_translate_produces_output hE.toIsNatBase α hα2
  refine ⟨h1, h3, hρ, hVmod, ⟨α, hα1, hα2⟩, hQK, hVE, β, hβs, hβk, ?_⟩
  intro g u u' hu
  exact hβe g u u' hu

end IsNatQuotSetting

end Output

end CFSG.QuasithinUnique.Setup.Campbell
