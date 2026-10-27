module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCGoldC
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Closure

variable {G : Type} [Group G]

theorem mul_comm_of_mem_closure_pair {z u : G} (hzu : z * u = u * z) {a b : G}
    (ha : a ∈ Subgroup.closure ({z, u} : Set G)) (hb : b ∈ Subgroup.closure ({z, u} : Set G)) :
    a * b = b * a := by
  have hcomm : ({z, u} : Set G).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hzu
    · exact hzu.symm
    · exact Commute.refl _
  have := Subgroup.isMulCommutative_closure hcomm
  exact setLike_mul_comm ha hb

end Closure

section Gold


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem false_of_matching (GS : Hat2A7.GoldschmidtStronglyClosedExponent) (hs : Pre2A7 Ω K₀)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) (hnoI : ¬ Hat2A7S8.IndepTri Ω K z) {J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ∈ omegaNbr Ω K) (hJ₂ : J₂ ∈ omegaNbr Ω K)
    (hne : T8.layerImg Ω z J₁ ≠ T8.layerImg Ω z J₂) : False := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := hz.ne_one
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzCsq : (⟨z, hzC⟩ : ↥C) * ⟨z, hzC⟩ = 1 := Subtype.ext hz.sq
  obtain ⟨S₀, hS₀⟩ : ∃ S : Sylow 2 ↥C, Subgroup.zpowers (⟨z, hzC⟩ : ↥C) ≤ (S : Subgroup ↥C) :=
    IsPGroup.exists_le_sylow (T8.isPGroup_zpowers_of_sq hzCsq)
  set P : Subgroup G := (S₀ : Subgroup ↥C).map C.subtype with hPdef
  have hP2 : IsPGroup 2 P := S₀.isPGroup'.map C.subtype
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hzP : z ∈ P := ⟨⟨z, hzC⟩, hS₀ (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨T, hPT⟩ := hP2.exists_le_sylow
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hCT : ∀ x ∈ (T : Subgroup G), x ∈ C → x ∈ P := by
    intro x hxT hxC
    have hQ2 : IsPGroup 2 (((T : Subgroup G) ⊓ C).subgroupOf C) :=
      (hT2.to_le (inf_le_left : (T : Subgroup G) ⊓ C ≤ T)).comap_subtype (K := C)
    have hle : (S₀ : Subgroup ↥C) ≤ ((T : Subgroup G) ⊓ C).subgroupOf C := by
      intro s hs'
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hPT ⟨s, hs', rfl⟩, s.2⟩
    have heq := S₀.is_maximal' hQ2 hle
    have hxQ : (⟨x, hxC⟩ : ↥C) ∈ ((T : Subgroup G) ⊓ C).subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr ⟨hxT, hxC⟩
    rw [heq] at hxQ
    exact ⟨⟨x, hxC⟩, hxQ, rfl⟩
  have hmax : ∀ H : Subgroup G, IsPGroup 2 H → H ≤ C → Nat.card H ≤ Nat.card P := by
    intro H hH hHC
    obtain ⟨S', hS'⟩ := (hH.comap_subtype (K := C)).exists_le_sylow
    have h1 : Nat.card (H.subgroupOf C) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv
    have h2 : Nat.card (H.subgroupOf C) ≤ Nat.card S' := Subgroup.card_le_of_le hS'
    have h3 : Nat.card S' = Nat.card S₀ := by
      rw [Sylow.card_eq_multiplicity S', Sylow.card_eq_multiplicity S₀]
    have h4 : Nat.card P = Nat.card S₀ := Subgroup.card_map_of_injective C.subtype_injective
    omega
  have hTP : P = (T : Subgroup G) :=
    eq_sylow_of_matching hs hnt hK hz hnoI hJ₁ hJ₂ hne hP2 hPC hzP hT2 hPT hCT hmax
  obtain ⟨u, hu, hu2, hcomm, hzu1, hall⟩ :=
    exists_pair hs hnt hK hz hnoI hJ₁ hJ₂ hne hP2 hPC hzP
  have hzin : z ∈ invIn Ω P := ⟨hzP, K, hK, hz⟩
  set A : Subgroup G := Subgroup.closure ({z, u} : Set G) with hAdef
  have hzA : z ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have huA : u ∈ A := Subgroup.subset_closure (by simp)
  have hAP : A ≤ P := by
    rw [hAdef, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hzP
    · exact hu.1
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    mul_comm_of_mem_closure_pair hcomm.symm ha hb
  have hA1 : A ≠ ⊥ := fun h => hz1 (by
    have : z ∈ A := hzA
    rw [h] at this
    simpa using this)
  have hsubA : ∀ x ∈ invIn Ω P, x ∈ A := by
    intro x hx
    rcases hall x hx with h | h | h
    · rw [h]
      exact hzA
    · rw [h]
      exact huA
    · rw [h]
      exact A.mul_mem hzA huA
  have hAcls : ∀ a ∈ A, a = 1 ∨ a ∈ invIn Ω P := by
    intro a ha
    rcases T8.mem_closure_pair_involutions hz.sq hu2 hcomm.symm ha with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ hzin)
    · exact Or.inr (h ▸ hu)
    · rcases hzu1 with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (h ▸ h')
  have hAsc : ∀ a ∈ A, ∀ g : G, g * a * g⁻¹ ∈ (T : Subgroup G) → g * a * g⁻¹ ∈ A := by
    intro a ha g hg
    rcases hAcls a ha with h | h
    · rw [h]
      simp
    · have hgP : g * a * g⁻¹ ∈ P := by
        rw [hTP]
        exact hg
      exact hsubA _ (invIn_conj hΩ h hgP)
  have hGS := GS G hs.nonabelian T A hA1 (hAP.trans hPT) hAab hAsc
  obtain ⟨zK, hzK⟩ := hs.classical K hK
  obtain ⟨QK⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨x8, -, hx8⟩ := Hat2A7.exists_orderOf_eight_of_witness hzK.witness QK
  have hx8G : orderOf (x8 : G) = 8 := by
    rw [Subgroup.orderOf_coe]
    exact hx8
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers (x8 : G)) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, hx8G]; norm_num)
  obtain ⟨T', hT'⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T T'
  have hx8T' : (x8 : G) ∈ ((g • T : Sylow 2 G) : Subgroup G) := by
    rw [hg]
    exact hT' (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul] at hx8T'
  obtain ⟨s, hsT, hs'⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx8T'
  have hs4 : s ^ 4 = 1 := hGS s hsT
  have hx84 : (x8 : G) ^ 4 = 1 := by
    rw [← hs']
    rw [MulAut.smul_def, ← map_pow, hs4, map_one]
  have hord : orderOf (x8 : G) ∣ 4 := orderOf_dvd_of_pow_eq_one hx84
  rw [hx8G] at hord
  omega

theorem a7TCMatch_of_gs (GS : Hat2A7.GoldschmidtStronglyClosedExponent) : A7TCMatch := by
  intro G _ _ _ Ω K hs hnt hnoI L hL z hz J₁ hJ₁ J₂ hJ₂ hne
  exact false_of_matching GS hs.toPre2A7 hnt hL hz (hnoI L hL z hz) hJ₁ hJ₂ hne

end Gold

end CFSG.ClassicalInvolution.Hat2A7S
