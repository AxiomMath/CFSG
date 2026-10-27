module

public import CFSG.GH74.GLS.SP.Model
public import CFSG.GH74.GLS.SP.GlueDefs

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Sp

variable (F : Type) [Field F]

theorem spT_le_spN : spT F ≤ spN F := by
  intro h hh
  rw [← spB_inf_spN F] at hh
  exact hh.2

theorem spT_conj_mem {m h : StatedSp 2 F} (hm : m ∈ spN F) (hh : h ∈ spT F) :
    m * h * m⁻¹ ∈ spT F := by
  have hcart : (⟨h, spT_le_spN F hh⟩ : spN F) ∈ cartan (spB F) (spN F) := by
    rw [cartan, Subgroup.mem_subgroupOf, spB_inf_spN]
    exact hh
  have := (spCartan_normal F).conj_mem _ hcart ⟨m, hm⟩
  rw [cartan, Subgroup.mem_subgroupOf, spB_inf_spN] at this
  exact this

theorem coxeterM_cartanC_two : (coxeterMatrix (isFiniteType_cartanC 2)).M 0 1 = 4 := by
  have h01 : cartanC 2 0 1 = -2 := by decide
  have h10 : cartanC 2 1 0 = -1 := by decide
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, h01, h10]
  norm_num

theorem spN_pow : (weylRep 2 F 0 * weylRep 2 F 1) ^ 4 ∈ spT F := by
  have hord := (coxeterMatrix (isFiniteType_cartanC 2)).toCoxeterSystem.orderOf_simple_mul_simple 0 1
  rw [coxeterM_cartanC_two] at hord
  have h1 : (((spNRep F 0 * spNRep F 1) ^ 4 : spN F) : WeylGroup (spB F) (spN F)) = 1 := by
    apply (spWeylEquiv F).injective
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, map_pow, map_mul, spWeylEquiv_spNRep,
      spWeylEquiv_spNRep, map_one, ← hord]
    exact pow_orderOf_eq_one _
  rw [QuotientGroup.eq_one_iff] at h1
  rw [cartan, Subgroup.mem_subgroupOf, spB_inf_spN] at h1
  exact h1


theorem negGen_le_spUneg : negGen 4 (octGroup F) ≤ spUneg F :=
  iSup₂_le fun k hk => octGroup_neg_le_spUneg F hk.1 (by exact_mod_cast hk.2)

private theorem single_zero_eq : (Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = octRoot 1 := by
  rw [octRoot_one]
  exact ext_fin_two (by simp) (by simp)

private theorem single_one_eq : (Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = octRoot 4 := by
  rw [octRoot_four]
  exact ext_fin_two (by simp) (by simp)

private theorem neg_single_zero_eq : (-Pi.single (0 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = octRoot (-1) := by
  rw [octRoot_neg_one]
  exact ext_fin_two (by simp) (by simp)

private theorem neg_single_one_eq : (-Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) = octRoot (-4) := by
  rw [octRoot_neg_four]
  exact ext_fin_two (by simp) (by simp)

private theorem rootGroup_single_zero :
    (rootDatum 2 F).rootGroup (Pi.single (0 : Fin 2) (1 : ℤ)) = octGroup F 1 :=
  congrArg (rootDatum 2 F).rootGroup single_zero_eq

private theorem rootGroup_single_one :
    (rootDatum 2 F).rootGroup (Pi.single (1 : Fin 2) (1 : ℤ)) = octGroup F 4 :=
  congrArg (rootDatum 2 F).rootGroup single_one_eq

private theorem rootGroup_neg_single_zero :
    (rootDatum 2 F).rootGroup (-Pi.single (0 : Fin 2) (1 : ℤ)) = octGroup F (-1) :=
  congrArg (rootDatum 2 F).rootGroup neg_single_zero_eq

private theorem rootGroup_neg_single_one :
    (rootDatum 2 F).rootGroup (-Pi.single (1 : Fin 2) (1 : ℤ)) = octGroup F (-4) :=
  congrArg (rootDatum 2 F).rootGroup neg_single_one_eq

theorem actsAs_inv_simple (i : Fin 2) (m : StatedSp 2 F)
    (h : ActsAs (rootDatum 2 F) m
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple i)) :
    ActsAs (rootDatum 2 F) m⁻¹
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple i) := by
  have := h.inv
  have e : ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple i)⁻¹ =
      (coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple i :=
    CoxeterSystem.inv_simple _ _
  rwa [e] at this

theorem spRGD2 : RGD2 4 (spT F) (weylRep 2 F 0) (weylRep 2 F 1) (spU F) (octGroup F) where
  three_le := by norm_num
  comm_H a ha b hb := (commute_of_mem_iSup (steinbergExtras 2 F) ha hb).eq
  nilpotent := isNilpotent_spU F
  conj_H₁ h hh := spT_conj_mem F (n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F)
    (H := torus 2 F) (0 : Fin 2)) hh
  conj_H₂ h hh := spT_conj_mem F (n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F)
    (H := torus 2 F) (1 : Fin 2)) hh
  sq₁ := by
    have h := (isCTGroupDatum 2 F).sq_mem (0 : Fin 2)
    rw [sq] at h
    exact le_iSup (torus 2 F) 0 h
  sq₂ := by
    have h := (isCTGroupDatum 2 F).sq_mem (1 : Fin 2)
    rw [sq] at h
    exact le_iSup (torus 2 F) 1 h
  pow := spN_pow F
  U_inf_H := by
    rw [inf_comm]
    exact (steinbergExtras 2 F).torus_inf_posPart
  ne_bot := (spOctagon F).ne_bot
  invariant := (spOctagon F).invariant
  carrier_eq := (spOctagon F).carrier_eq
  unique := (spOctagon F).unique
  reverse_eq := (spOctagon F).reverse_eq
  subgroup := (spOctagon F).subgroup
  act₁ := by
    obtain ⟨a1, a2, a3⟩ := spAction₁ F
      (actsAs_inv_simple F 0 (weylRep 2 F 0) (spActsAs F 0 (m := spNRep F 0) rfl))
    exact ⟨a1, a2, fun i h2 h4 => a3 i h2 (by exact_mod_cast h4)⟩
  act₂ := spAction₂' F
    (actsAs_inv_simple F 1 (weylRep 2 F 1) (spActsAs F 1 (m := spNRep F 1) rfl))
  meet_one x hx hxneg := by
    have hmem : x ∈ borel (rootDatum 2 F) (torus 2 F) ⊓ negUnipotent (rootDatum 2 F) :=
      ⟨hx, negGen_le_spUneg F hxneg⟩
    rw [(spBruhatExtras F).borel_inf_negUnipotent] at hmem
    exact Subgroup.mem_bot.1 hmem
  rank₁ y hy hy1 := by
    have hyL : y ∈ rankOne (rootDatum 2 F).rootGroup (0 : Fin 2) := by
      exact Subgroup.mem_sup_right ((rootGroup_neg_single_zero F).ge hy)
    have hyU : y ∈ spUneg F := octGroup_neg_le_spUneg F (k := 1) le_rfl (by norm_num) hy
    rcases (steinbergExtras 2 F).rankOne_bruhat (0 : Fin 2) y hyL with
      ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · exfalso
      have hu' : u ∈ spU F := by
        have : u ∈ octGroup F 1 := (rootGroup_single_zero F).le hu
        exact octGroup_le_spU F le_rfl (by norm_num) this
      have hmem : h * u ∈ borel (rootDatum 2 F) (torus 2 F) ⊓ negUnipotent (rootDatum 2 F) :=
        ⟨Subgroup.mul_mem_sup (le_iSup (torus 2 F) (0 : Fin 2) hh) hu', hyU⟩
      rw [(spBruhatExtras F).borel_inf_negUnipotent] at hmem
      exact hy1 (Subgroup.mem_bot.1 hmem)
    · have hu' : u ∈ octGroup F 1 := (rootGroup_single_zero F).le hu
      have hv' : v ∈ octGroup F 1 := (rootGroup_single_zero F).le hv
      have hh' : weylRep 2 F 0 * h * (weylRep 2 F 0)⁻¹ ∈ spT F :=
        spT_conj_mem F (n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (0 : Fin 2))
          (le_iSup (torus 2 F) (0 : Fin 2) hh)
      refine Set.mem_mul.2 ⟨u * (weylRep 2 F 0 * h * (weylRep 2 F 0)⁻¹) * weylRep 2 F 0,
        Set.mem_mul.2 ⟨u * (weylRep 2 F 0 * h * (weylRep 2 F 0)⁻¹),
          Set.mem_mul.2 ⟨u, hu', _, hh', rfl⟩, weylRep 2 F 0, rfl, rfl⟩, v, hv', ?_⟩
      group
  rank₂ y hy hy1 := by
    have hy' : y ∈ octGroup F (-4) := by simpa using hy
    have hyL : y ∈ rankOne (rootDatum 2 F).rootGroup (1 : Fin 2) := by
      exact Subgroup.mem_sup_right ((rootGroup_neg_single_one F).ge hy')
    have hyU : y ∈ spUneg F := octGroup_neg_le_spUneg F (k := 4) (by norm_num) le_rfl hy'
    rcases (steinbergExtras 2 F).rankOne_bruhat (1 : Fin 2) y hyL with
      ⟨h, hh, u, hu, rfl⟩ | ⟨u, hu, h, hh, v, hv, rfl⟩
    · exfalso
      have hu' : u ∈ spU F := by
        have : u ∈ octGroup F 4 := (rootGroup_single_one F).le hu
        exact octGroup_le_spU F (k := 4) (by norm_num) le_rfl this
      have hmem : h * u ∈ borel (rootDatum 2 F) (torus 2 F) ⊓ negUnipotent (rootDatum 2 F) :=
        ⟨Subgroup.mul_mem_sup (le_iSup (torus 2 F) (1 : Fin 2) hh) hu', hyU⟩
      rw [(spBruhatExtras F).borel_inf_negUnipotent] at hmem
      exact hy1 (Subgroup.mem_bot.1 hmem)
    · have hu' : u ∈ octGroup F ((4 : ℕ) : ℤ) := by
        have : u ∈ octGroup F 4 := (rootGroup_single_one F).le hu
        simpa using this
      have hv' : v ∈ octGroup F ((4 : ℕ) : ℤ) := by
        have : v ∈ octGroup F 4 := (rootGroup_single_one F).le hv
        simpa using this
      have hh' : weylRep 2 F 1 * h * (weylRep 2 F 1)⁻¹ ∈ spT F :=
        spT_conj_mem F (n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (1 : Fin 2))
          (le_iSup (torus 2 F) (1 : Fin 2) hh)
      refine Set.mem_mul.2 ⟨u * (weylRep 2 F 1 * h * (weylRep 2 F 1)⁻¹) * weylRep 2 F 1,
        Set.mem_mul.2 ⟨u * (weylRep 2 F 1 * h * (weylRep 2 F 1)⁻¹),
          Set.mem_mul.2 ⟨u, hu', _, hh', rfl⟩, weylRep 2 F 1, rfl, rfl⟩, v, hv', ?_⟩
      group


theorem spRGD2_N : (spRGD2 F).N = spN F := by
  unfold RGD2.N
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 (Set.union_subset (spT_le_spN F) ?_)
    rintro _ (rfl | rfl)
    · exact n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (0 : Fin 2)
    · exact n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (1 : Fin 2)
  · refine sup_le ?_ ?_
    · exact fun x hx => Subgroup.subset_closure (Or.inl hx)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
      · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem spRGD2_gen : (spT F ⊔ spU F) ⊔ (spRGD2 F).N = ⊤ := by
  rw [spRGD2_N]
  obtain ⟨_, hgen, -⟩ := spSplitBN F (isNilpotent_spU F)
  exact hgen

end Sp

end CFSG.GH74.GLS.SP
