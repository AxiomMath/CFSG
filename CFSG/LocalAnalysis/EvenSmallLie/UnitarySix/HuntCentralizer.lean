module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntOuter
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntAction

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit CFSG.EvenSmallLie.UnitarySix.MathieuExt
  CFSG.ComponentClassification.WittDesign
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)}

theorem card_eq_card_ker_mul_card_map {A B : Type*} [Group A] [Group B] [Finite A] (ρ : A →* B)
    {K : Subgroup A} (hK : ρ.ker ≤ K) : Nat.card K = Nat.card ρ.ker * Nat.card (K.map ρ) := by
  set ψ := ρ.comp K.subtype
  have hker : Nat.card ψ.ker = Nat.card ρ.ker := by
    have h : ψ.ker.map K.subtype = ρ.ker := by
      rw [← MonoidHom.comap_ker, map_comap_eq, range_subtype, inf_eq_right.2 hK]
    rw [← h, card_map_of_injective K.subtype_injective]
  rw [card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker, mul_comm,
    MonoidHom.range_comp, range_subtype]

section Main

variable
    (hR : ToddRankBounds) (H : Hyp t L E p)
include hR H

theorem Hyp.exists_M22 :
    ∃ f : orb E t ≃ Fin 22, (rhoF f).range = M22 ∧
      Nat.card (((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map
        (rhoF f)) = 20160 ∧
      Nonempty ((((centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G))).map
        (rhoF f)) ≃* PSL(3, F4)) := by
  obtain ⟨f, hf | hf⟩ := H.mathieu_dichotomy
  · exact ⟨f, hf⟩
  · exact absurd hf (H.rhoF_range_ne_hexadAut hR f)

omit hR in
theorem Hyp.card_ker_rhoF
    (f : orb E t ≃ Fin 22) (hM : M22 ≤ (rhoF f).range) :
    Nat.card (rhoF f).ker = 2 ^ 10 := by
  rw [H.ker_rhoF f hM, ← card_subtype, subgroupOf_map_subtype,
    inf_eq_left.2 le_normalizer, H.todd.card_E]

theorem Hyp.card_normalizer
    : Nat.card (normalizer (E : Set G)) = 2 ^ 10 * 443520 := by
  obtain ⟨f, hf, -⟩ := H.exists_M22 hR
  have h := card_eq_card_ker_mul_card_map (rhoF f) (le_top : (rhoF f).ker ≤ ⊤)
  rw [card_top, ← MonoidHom.range_eq_map, hf, H.card_ker_rhoF f hf.ge, card_M22'] at h
  exact h

theorem Hyp.nonempty_quotient_equiv_M22 :
    Nonempty (normalizer (E : Set G) ⧸ E.subgroupOf (normalizer (E : Set G)) ≃* M22) := by
  obtain ⟨f, hf, -⟩ := H.exists_M22 hR
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (H.ker_rhoF f hf.ge).symm).trans
    ((QuotientGroup.quotientKerEquivRange (rhoF f)).trans (MulEquiv.subgroupCongr hf))⟩

omit [Finite G] hR in
theorem Hyp.lift_mem_normalizer_of_uP
    {x : Equiv.Perm (Fin 693)} (hx : x ∈ uP) {ℓ : G}
    (hℓL : ℓ ∈ L) (hpℓ : pe p ℓ = x) : ℓ ∈ normalizer (E : Set G) := by
  have hxN := uP_le_normalizer hx
  rw [mem_normalizer_iff]
  intro e
  constructor
  · intro he
    obtain ⟨heL, heA⟩ := H.todd.mem_E_iff.1 he
    refine H.todd.mem_E_iff.2 ⟨L.mul_mem (L.mul_mem hℓL heL) (L.inv_mem hℓL), ?_⟩
    rw [pe_conj p hℓL heL, hpℓ]
    exact (mem_normalizer_iff.1 hxN _).1 heA
  · intro he
    obtain ⟨heL, heA⟩ := H.todd.mem_E_iff.1 he
    have heL' : e ∈ L := by
      have := L.mul_mem (L.mul_mem (L.inv_mem hℓL) heL) hℓL
      rwa [show ℓ⁻¹ * (ℓ * e * ℓ⁻¹) * ℓ = e by group] at this
    refine H.todd.mem_E_iff.2 ⟨heL', ?_⟩
    rw [pe_conj p hℓL heL', hpℓ] at heA
    exact (mem_normalizer_iff.1 hxN _).2 heA

omit hR in
theorem Hyp.le_card_normalizer_inf :
    2 ^ 10 * 20160 ≤ Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) := by
  set ψ : (normalizer (E : Set G) ⊓ L : Subgroup G) →* Equiv.Perm (Fin 693) :=
    p.comp (inclusion inf_le_right)
  have hrange : uP ≤ ψ.range := by
    intro x hx
    obtain ⟨ℓ, hℓL, hℓ⟩ := H.todd.exists_lift (uP_le_T46 hx)
    refine ⟨⟨ℓ, mem_inf.2 ⟨H.lift_mem_normalizer_of_uP hx hℓL hℓ, hℓL⟩⟩, ?_⟩
    change p ⟨ℓ, hℓL⟩ = x
    rw [← pe_of_mem p hℓL, hℓ]
  have hker : ψ.ker ≠ ⊥ := by
    intro h
    have ht : (⟨t, mem_inf.2 ⟨le_normalizer H.todd.t_mem_E, H.todd.t_mem⟩⟩ :
        (normalizer (E : Set G) ⊓ L : Subgroup G)) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      exact (H.todd.ker ⟨t, H.todd.t_mem⟩).2 (Or.inr rfl)
    rw [h, mem_bot] at ht
    exact H.todd.t_ne_one (congrArg Subtype.val ht)
  have h1 : 2 ≤ Nat.card ψ.ker := (one_lt_card_iff_ne_bot _).2 hker
  have h2 : 10321920 ≤ Nat.card ψ.range := card_uP ▸ card_le_of_le hrange
  rw [card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  calc 2 ^ 10 * 20160 = 10321920 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h2 h1

theorem Hyp.normalizer_inf_centralizer :
    normalizer (E : Set G) ⊓ centralizer ({t} : Set G) = normalizer (E : Set G) ⊓ L := by
  obtain ⟨f, hf, h20, -⟩ := H.exists_M22 hR
  have hle : normalizer (E : Set G) ⊓ L ≤ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_left _ H.todd.le_centralizer
  refine (eq_of_le_of_card_ge hle ?_).symm
  have hker : (rhoF f).ker ≤ (centralizer ({t} : Set G)).subgroupOf (normalizer (E : Set G)) := by
    rw [H.ker_rhoF f hf.ge]
    intro n hn
    rw [mem_subgroupOf] at hn ⊢
    exact mem_centralizer_singleton_iff.2 (H.todd.E_comm hn H.todd.t_mem_E)
  have hK := card_eq_card_ker_mul_card_map (rhoF f) hker
  rw [H.card_ker_rhoF f hf.ge, h20, ← card_subtype, subgroupOf_map_subtype, inf_comm] at hK
  rw [hK]
  exact H.le_card_normalizer_inf

theorem Hyp.centralizer_eq
    : centralizer ({t} : Set G) = L := by
  refine le_antisymm (fun h hh => ?_) H.todd.le_centralizer
  obtain ⟨l, hl, n, hn, rfl⟩ := H.ds.exists_eq_mul hh
  have hnC : n ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (H.todd.le_centralizer hl)) hh
    rwa [inv_mul_cancel_left] at this
  have hnL : n ∈ normalizer (E : Set G) ⊓ L := H.normalizer_inf_centralizer hR ▸ ⟨hn, hnC⟩
  exact L.mul_mem hl hnL.2

end Main

end CFSG.EvenSmallLie.UnitarySix.Hunt
