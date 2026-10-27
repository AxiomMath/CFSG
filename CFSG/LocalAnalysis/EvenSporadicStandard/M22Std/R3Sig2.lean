module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutX1Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbar

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

theorem commutator_mem_of_index_two {Γ : Type*} [Group Γ] {N : Subgroup Γ} (hN : N.index = 2)
    (g1 g2 : Γ) : g1 * g2 * g1⁻¹ * g2⁻¹ ∈ N := by
  have key : ∀ a b : Γ, a * b ∈ N ↔ (a ∈ N ↔ b ∈ N) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hN
  rw [key (g1 * g2 * g1⁻¹) g2⁻¹, key (g1 * g2) g1⁻¹, key g1 g2]
  simp only [Subgroup.inv_mem_iff]
  tauto

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

theorem OuterSituation.rho_not_mem_sup_commutator
    (hS : OuterSituation G L z t T₁ F tb Q x L1) (hz : z ∈ normalizer (L1 : Set G))
    {A : Subgroup G} (hLA : L ≤ A) (hAH : A ≤ centralizer ({z} : Set G)) (hzA : z ∉ A)
    {a : G} (haA : a ∈ A) (haL : a ∉ L) (haX : a ∈ normalizer (L1 : Set G)) :
    (QuotientGroup.mk ⟨a, haX⟩ : Xbar L1) ∉
      zpowers (QuotientGroup.mk ⟨z, hz⟩ : Xbar L1) ⊔
        (commutator ↥(centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1)))).map
          (centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1))).subtype := by
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  have hz2 : z * z = 1 := Sup.one.z_mul_self
  have hzL : ∀ l ∈ L, z * l = l * z := fun l hl =>
    (mem_centralizer_singleton_iff.1 (hAH (hLA hl))).symm
  have hzNL : ∀ l, l ∈ L ↔ z * l * z⁻¹ ∈ L := normalizes_of_centralizes hzL
  have hCeq : centralizer ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1)) =
      ((centralizer ({z} : Set G)).subgroupOf (normalizer (L1 : Set G))).map
        (QuotientGroup.mk' _) := Sup.centralizer_zbar_eq
  have hker := Sup.one.centralizer_X_z_inf_C Sup.L1_normE Sup.L1_cz Sup.F_le Sup.L1_comm
    Sup.L1_card Sup.K_eq Sup.z_norm
  set zb : Xbar L1 := QuotientGroup.mk ⟨z, hz⟩ with hzb
  set C : Subgroup (Xbar L1) := centralizer ({zb} : Set (Xbar L1)) with hC
  let K1 : Subgroup ↥(normalizer (L1 : Set G)) :=
    ((L ⊔ zpowers z) ⊓ centralizer ({z} : Set G)).subgroupOf (normalizer (L1 : Set G))
  let H1 : Subgroup (Xbar L1) := K1.map (QuotientGroup.mk' _)
  have hzH1 : zb ∈ H1 := ⟨⟨z, hz⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
    ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers z), mem_centralizer_singleton_iff.2 rfl⟩), rfl⟩
  have hC'H1 : (commutator ↥C).map C.subtype ≤ H1 := by
    rw [Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _
    rw [Subgroup.mem_comap]
    show ((g1 * g2 * g1⁻¹ * g2⁻¹ : ↥C) : Xbar L1) ∈ H1
    obtain ⟨h1, hh1, hρ1⟩ := (SetLike.ext_iff.1 hCeq (g1 : Xbar L1)).1 g1.2
    obtain ⟨h2, hh2, hρ2⟩ := (SetLike.ext_iff.1 hCeq (g2 : Xbar L1)).1 g2.2
    have hcomm : ((g1 * g2 * g1⁻¹ * g2⁻¹ : ↥C) : Xbar L1) =
        QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))
          (h1 * h2 * h1⁻¹ * h2⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ1, hρ2]
      rfl
    rw [hcomm]
    refine ⟨h1 * h2 * h1⁻¹ * h2⁻¹, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.2 ?_
    have hh1' : (h1 : G) ∈ centralizer ({z} : Set G) := Subgroup.mem_subgroupOf.1 hh1
    have hh2' : (h2 : G) ∈ centralizer ({z} : Set G) := Subgroup.mem_subgroupOf.1 hh2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hN : ((L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 := hS.rel
      have := commutator_mem_of_index_two hN ⟨(h1 : G), hh1'⟩ ⟨(h2 : G), hh2'⟩
      exact Subgroup.mem_subgroupOf.1 this
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hh1' hh2')
        (Subgroup.inv_mem _ hh1')) (Subgroup.inv_mem _ hh2')
  have haH1 : (QuotientGroup.mk ⟨a, haX⟩ : Xbar L1) ∉ H1 := by
    rintro ⟨k, hk, hρk⟩
    have hk' : (k : G) ∈ (L ⊔ zpowers z) ⊓ centralizer ({z} : Set G) := hk
    have hker' : (⟨a, haX⟩ : ↥(normalizer (L1 : Set G)))⁻¹ * k ∈
        (centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)) := by
      rw [← QuotientGroup.eq]
      exact hρk.symm
    have hmemF : a⁻¹ * (k : G) ∈ liftSub F := by
      rw [← hker]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mem_subgroupOf.1 hker'⟩
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haX) k.2
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAH haA)) hk'.2
    have hmemL : a⁻¹ * (k : G) ∈ L := liftSub_le F hmemF
    rcases mem_sup_zpowers_invol hz2 hzNL hk'.1 with hkL | ⟨l, hl, hkl⟩
    · apply haL
      have : a = (k : G) * (a⁻¹ * (k : G))⁻¹ := by group
      rw [this]
      exact L.mul_mem hkL (L.inv_mem hmemL)
    · apply hzA
      have : z = a * (a⁻¹ * (k : G)) * l⁻¹ := by rw [hkl]; group
      rw [this]
      exact A.mul_mem (A.mul_mem haA (hLA hmemL)) (A.inv_mem (hLA hl))
  intro hmem
  have hle : zpowers zb ⊔ (commutator ↥C).map C.subtype ≤ H1 :=
    sup_le (Subgroup.zpowers_le.2 hzH1) hC'H1
  exact haH1 (hle hmem)

end CFSG.EvenSporadicStandard.M22Std
