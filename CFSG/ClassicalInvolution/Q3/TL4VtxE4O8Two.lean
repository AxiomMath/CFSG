module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import CFSG.ClassicalInvolution.Q3.TL4LinkE4
public import Certificates.Certificate128
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.EvenSmallLie.OmegaEight

namespace E4O8

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C


theorem root_mem (h : ℕ) : rootP.getD h 1 ∈ omegaT := by
  rw [List.getD_eq_getElem?_getD]
  cases hh : rootP[h]? with
  | none => exact omegaT.one_mem
  | some g =>
    rw [omegaT_eq_closure_root]
    exact Subgroup.subset_closure (List.mem_of_getElem? hh)


theorem two_parts : edgeCheck L0P u0 v0 (rootP.getD 0 1) = true ∧
    edgeCheck L0P u0 v0 (rootP.getD 4 1) = true ∧
    norms L0P u0 v0 ((rootP.getD 0 1)⁻¹ * rootP.getD 4 1) = false := by
  have h : twoCheck () = true := Certificates.certificate128
  unfold twoCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have r0 := rep_getD forall₂_root 0
  have r4 := rep_getD forall₂_root 4
  refine ⟨?_, ?_, ?_⟩
  · rwa [edgeCheckA_eq forall₂_L0 u0_spec.1 v0_spec.1 r0] at h1
  · rwa [edgeCheckA_eq forall₂_L0 u0_spec.1 v0_spec.1 r4] at h2
  · rwa [normsA_eq forall₂_L0 u0_spec.1 v0_spec.1 (rep_compA (rep_inv r0) r4)] at h3

theorem two_nbrs : conjSub (rootP.getD 0 1) K0 ≠ K0 ∧
    conjSub (rootP.getD 0 1) K0 ≤ Subgroup.normalizer (K0 : Set _) ∧
    conjSub (rootP.getD 4 1) K0 ≠ K0 ∧
    conjSub (rootP.getD 4 1) K0 ≤ Subgroup.normalizer (K0 : Set _) ∧
    conjSub (rootP.getD 0 1) K0 ≠ conjSub (rootP.getD 4 1) K0 := by
  obtain ⟨h1, h2, h3⟩ := two_parts
  obtain ⟨a1, a2⟩ := edge_of_edgeCheck mem_K0_iff h1
  obtain ⟨b1, b2⟩ := edge_of_edgeCheck mem_K0_iff h2
  refine ⟨a1, a2, b1, b2, fun e => ?_⟩
  have he : conjSub ((rootP.getD 0 1)⁻¹ * rootP.getD 4 1) K0 = K0 := by
    rw [conjSub_mul, ← e, conjSub_inv_conjSub]
  rw [norms_of_conjSub_eq mem_K0_iff he] at h3
  exact Bool.noConfusion h3


theorem e4QuatTwoNbrs_POmegaPlus {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) {K : Subgroup M} {s : M}
    (hd : QuatTwinDatum K s) :
    ∃ J ∈ omegaNbr (CoreAssembly.conjClass K) K,
      ∃ J' ∈ omegaNbr (CoreAssembly.conjClass K) K, J ≠ J' := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  obtain ⟨φ, hφ, hrange, hKc⟩ := exists_emb e hd
  obtain ⟨eK⟩ := hd.q8
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  obtain ⟨a1, a2, b1, b2, hab⟩ := two_nbrs
  obtain ⟨m, hm⟩ : rootP.getD 0 1 ∈ φ.range := hrange ▸ root_mem 0
  obtain ⟨m', hm'⟩ : rootP.getD 4 1 ∈ φ.range := hrange ▸ root_mem 4
  have hmap : ∀ g : M, (conjSub g K).map φ = conjSub (φ g) K0 := fun g => by
    rw [← conjSub_map, hKc]
  have hnbr : ∀ g : M, conjSub (φ g) K0 ≠ K0 →
      conjSub (φ g) K0 ≤ Subgroup.normalizer (K0 : Set _) →
      conjSub g K ∈ omegaNbr (CoreAssembly.conjClass K) K := by
    intro g hne hle
    refine (Vtx.mem_omegaNbr_conjClass_iff h2).mpr ⟨⟨g, rfl⟩, fun h => hne ?_, ?_⟩
    · rw [← hmap, h, hKc]
    · rw [← hmap, ← hKc] at hle
      exact (Vtx.map_le_normalizer_map_iff φ hφ).mp hle
  refine ⟨conjSub m K, hnbr m (hm ▸ a1) (hm ▸ a2), conjSub m' K, hnbr m' (hm' ▸ b1) (hm' ▸ b2),
    fun h => hab ?_⟩
  rw [← hm, ← hm', ← hmap, ← hmap, h]

end E4O8


theorem secIdE4O8TwoNbrs_proved : SecIdE4O8TwoNbrs := by
  intro Y _ _ R S t hd hc hO2 hZ hM
  have c := Vtx.centQuotGen_e4 hd hc hO2
  obtain ⟨Jb, hJb, Jb', hJb', hne⟩ :=
    E4O8.e4QuatTwoNbrs_POmegaPlus hM (Vtx.quatTwinDatum_quot hd hc hO2 hZ (Or.inr hM))
  rw [← Vtx.quotFamily_e4] at hJb hJb'
  obtain ⟨J, hJ, rfl⟩ := hJb.1
  obtain ⟨J', hJ', rfl⟩ := hJb'.1
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  exact ⟨tightCore R, hK, J, c.omegaNbr_of_map hK hJ hJb, J', c.omegaNbr_of_map hK hJ' hJb',
    fun h => hne (by rw [h])⟩

end CFSG.ClassicalInvolution.Q3.TL4
