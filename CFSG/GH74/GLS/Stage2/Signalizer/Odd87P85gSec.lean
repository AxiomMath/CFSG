module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gGraph

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem section_sylCfg
    {G : Type} [Group G] [Finite G] {z : G} (hz2 : orderOf z = 2) {H₀ : Subgroup G}
    (H₁ : Subgroup ↥H₀) [H₁.Normal] (hz : z ∈ H₀) (hodd : Odd (Nat.card H₁))
    (hL : LieModel (↥(layer (Sec H₀ H₁)) ⧸ center ↥(layer (Sec H₀ H₁))) .PSL 3 2 2)
    (hc : center ↥(layer (Sec H₀ H₁)) = ⊥)
    (hL2 : IVK.IsL2 ↥(layer (Sec H₀ H₁) ⊓ centralizer ({zSec z H₀ hz H₁} : Set (Sec H₀ H₁)))
      (fun q => q = 4)) :
    orderOf (zSec z H₀ hz H₁) = 2 ∧ zSec z H₀ hz H₁ ∉ layer (Sec H₀ H₁) ∧
      ∃ P E F : Subgroup (Sec H₀ H₁),
        SylCfg (fun y => zSec z H₀ hz H₁ * y * (zSec z H₀ hz H₁)⁻¹) P E F ∧
          P ≤ layer (Sec H₀ H₁) := by
  classical
  set t : Sec H₀ H₁ := zSec z H₀ hz H₁ with ht
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hKn : K.Normal := by
    rw [hK]
    exact @Subgroup.normal_of_characteristic _ _ _ CFSG.LocalCores.layer_characteristic
  have hz2' : (⟨z, hz⟩ : ↥H₀) * ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rw [hz2] at this
    simpa [sq] using this
  have ht2 : t * t = 1 := by
    rw [ht, zSec, ← QuotientGroup.mk_mul, hz2']
    rfl
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : (⟨z, hz⟩ : ↥H₀) ∈ H₁ := (QuotientGroup.eq_one_iff _).mp h
    have h2 : orderOf (⟨z, hz⟩ : ↥H₀) ∣ Nat.card H₁ := Subgroup.orderOf_dvd_natCard H₁ h1
    have h3 : orderOf (⟨z, hz⟩ : ↥H₀) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact hz2
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hord : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]; exact ht2
    · exact ht1
  have hJc := center_eq_bot_of_isL2_four hL2
  have htK : t ∉ K := by
    intro htK
    have hmem : (⟨t, htK, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(K ⊓ centralizer ({t} : Set (Sec H₀ H₁)))) ∈ center ↥(K ⊓ centralizer ({t} : Set (Sec H₀ H₁))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp g.2.2
    rw [hJc, Subgroup.mem_bot] at hmem
    exact ht1 (congrArg Subtype.val hmem)
  refine ⟨hord, htK, ?_⟩
  let e₁ : ↥K ⧸ center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨e₂⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL
  let ψ : ↥K ≃* ↥CFSG.ComponentClassification.PSL3Four.S := e₁.symm.trans e₂
  let g : ↥(normalizer (K : Set (Sec H₀ H₁))) := ⟨t, by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hKn.conj_mem x hx t
    · intro hx
      have := hKn.conj_mem _ hx t⁻¹
      simpa [mul_assoc] using this⟩
  let αK : MulAut ↥K := K.normalizerMonoidHom g
  have hαK : ∀ y : ↥K, ((αK y : ↥K) : Sec H₀ H₁) = t * (y : Sec H₀ H₁) * t⁻¹ := fun y => rfl
  have h2 : αK * αK = 1 := by
    ext y
    have h1 : ((αK (αK y) : ↥K) : Sec H₀ H₁) = t * (t * (y : Sec H₀ H₁) * t⁻¹) * t⁻¹ := by
      rw [hαK, hαK]
    show ((αK (αK y) : ↥K) : Sec H₀ H₁) = (y : Sec H₀ H₁)
    rw [h1]
    calc t * (t * (y : Sec H₀ H₁) * t⁻¹) * t⁻¹ = (t * t) * (y : Sec H₀ H₁) * (t * t)⁻¹ := by group
      _ = (y : Sec H₀ H₁) := by rw [ht2]; simp
  have h60 : Nat.card (fixSub αK) = 60 := by
    have hmap : (fixSub αK).map K.subtype = K ⊓ centralizer ({t} : Set (Sec H₀ H₁)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have := congrArg Subtype.val (mem_fixSub.mp hy)
        rw [hαK] at this
        have h3 : t * (y : Sec H₀ H₁) * t⁻¹ * t = (y : Sec H₀ H₁) * t := by rw [this]
        simpa [mul_assoc] using h3.symm
      · rintro ⟨hxK, hxc⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_fixSub]
        apply Subtype.ext
        rw [hαK]
        have := Subgroup.mem_centralizer_singleton_iff.mp hxc
        simp [mul_assoc, ← this]
    rw [← card_isL2_four hL2, ← hmap]
    exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  obtain ⟨P, E, F, hcfg⟩ := exists_sylCfg_of_graph ψ αK h2 h60
  exact ⟨P.map K.subtype, E.map K.subtype, F.map K.subtype,
    hcfg.map K.subtype K.subtype_injective (α := fun y => αK y) (α' := fun y => t * y * t⁻¹)
      (fun y => (hαK y).symm),
    Subgroup.map_subtype_le _⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
