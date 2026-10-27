module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFrameData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BTClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5_oddCore_trivial (h34a : Asc82Lemma34a) (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a)
    (l58d : Asc82Lemma58d) (f59 : Asc82Fact59) (f510 : Asc82Fact510)
    (hP : Asc82FactPockets6) (hQ : Asc82FactQCent6) (hF : Asc82FactFrame6)
    (hZ : Asc82FactOutZeta6) {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z r : G} {B A : Subgroup G} (hR : Sec5RCtx G t L S z r B A) : oddCoreIn L = ⊥ := by
  classical
  have hset : Sec5Setting G t L := hR.toSec5Ctx.toSec5Setting
  have hΩ : IsOm6Z2 L := hset.isOm6Z2
  obtain ⟨φ, hm⟩ := sec5b_model58_of l58d hR
  have ht := sec5b_tM_eq hy f510 hR hm
  obtain ⟨g, a, b, c, hab, hg, hrL, hcL, hct, hcρ⟩ := sec5o_frame_data f59 hm ht
  let y₁ : G := φ (Pi.single a 1)
  have hy₁A : y₁ ∈ A := hm.perm.mem (Pi.single a 1)
  have hy₁ρ : ∀ i : Fin 6, y₁ * φ (Pi.single i 1) * y₁⁻¹ = φ (Pi.single i 1) := by
    intro i
    have h := (sec5b_A_elemAb hR).1 y₁ hy₁A (φ (Pi.single i 1))
      (hm.perm.mem (Pi.single i 1))
    rw [h]
    group
  have hcomm := sec5_oddCore_comm_conj h34a hy.h36 h52a hy.h52b hP hQ hR.toSec5Ctx g hg
  have hOU : oddCoreIn L ≤ oddCoreIn (centralizer ({t} : Set G)) :=
    (sec5_oddCore_comm_L hy.h36 hset).2
  have hconj_le : CFSG.conjugate L g ≤
      Subgroup.centralizer (oddCoreIn (centralizer ({t} : Set G)) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcent_of : ∀ w ∈ CFSG.conjugate L g, ∀ x ∈ oddCoreIn L, w * x = x * w := by
    intro w hw x hx
    have hw' := hconj_le hw
    have hxU := hOU hx
    exact ((Subgroup.mem_centralizer_iff.mp hw') x hxU).symm
  have hy₁type : ∃ α : ℤˣ, InducesTypeSome L y₁ 6 (-1) 1 α :=
    hm.type_one (Pi.single a 1) (Or.inl (sec5b6_vecWeight_single a))
  have hy₁N : y₁ ∈ normalizer (L : Set G) := by
    obtain ⟨α, hα⟩ := hy₁type
    exact sec5o_mem_normalizer_of_type hα
  have hct' : c * t = t * c := mul_inv_eq_iff_eq_mul.mp hct
  have hc_cent : c ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hct'
  have hcN : c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer hy.h36 hset.toSec3SettingLB c hc_cent
  have hframe_ne : ∀ x : G, x ∈ L ⊔ centralizer (L : Set G) →
      (∀ i : Fin 6, x⁻¹ * φ (Pi.single i 1) * x *
        (φ (Pi.single (Equiv.swap a b i) 1))⁻¹ ∈ centralizer (L : Set G)) → False := by
    intro x hx hσ
    have hsign := sec5o_frame_even hF h52a hy.h52b hR hm (x := x) hx
      (σ := Equiv.swap a b) hσ
    rw [Equiv.Perm.sign_swap hab] at hsign
    exact absurd hsign (by decide)
  have hσc : ∀ i : Fin 6, (c⁻¹)⁻¹ * φ (Pi.single i 1) * c⁻¹ *
      (φ (Pi.single (Equiv.swap a b i) 1))⁻¹ ∈ centralizer (L : Set G) := by
    intro i
    have ht' : (c⁻¹)⁻¹ * φ (Pi.single i 1) * c⁻¹ *
        (φ (Pi.single (Equiv.swap a b i) 1))⁻¹ = t := by
      rw [inv_inv, hcρ i]
      group
    rw [ht']
    exact sec5o_t_mem_centralizer hy.h52b hset
  have hc1 : c ∉ L ⊔ centralizer (L : Set G) := fun hc =>
    hframe_ne c⁻¹ (inv_mem hc) hσc
  have hσcy : ∀ i : Fin 6, ((c * y₁)⁻¹)⁻¹ * φ (Pi.single i 1) * (c * y₁)⁻¹ *
      (φ (Pi.single (Equiv.swap a b i) 1))⁻¹ ∈ centralizer (L : Set G) := by
    intro i
    have ht' : ((c * y₁)⁻¹)⁻¹ * φ (Pi.single i 1) * (c * y₁)⁻¹ *
        (φ (Pi.single (Equiv.swap a b i) 1))⁻¹ = t := by
      rw [inv_inv]
      rw [show c * y₁ * φ (Pi.single i 1) * (c * y₁)⁻¹ =
        c * (y₁ * φ (Pi.single i 1) * y₁⁻¹) * c⁻¹ by group]
      rw [hy₁ρ i, hcρ i]
      group
    rw [ht']
    exact sec5o_t_mem_centralizer hy.h52b hset
  have hc2 : c * y₁ ∉ L ⊔ centralizer (L : Set G) := fun hc =>
    hframe_ne (c * y₁)⁻¹ (inv_mem hc) hσcy
  have hcentral : ∀ x ∈ oddCoreIn L, y₁ * x = x * y₁ ∧ c * x = x * c :=
    fun x hx => ⟨hcent_of y₁ hrL x hx, hcent_of c hcL x hx⟩
  exact hZ G L hΩ y₁ c hy₁N hcN hy₁type hc1 hc2 hcentral

end CFSG.OddStandard.SmallF3.Omega
