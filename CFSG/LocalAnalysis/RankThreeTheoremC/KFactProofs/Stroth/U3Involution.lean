module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.UnitaryThreeRecognition.Model (rootGroup weyl_not_mem_stabilizer)

namespace KFactProofs.Stroth.U3Involution

private theorem closure_union_eq_top_of_isCoatom {G : Type*} [Group G] {C N : Subgroup G}
    (hN : IsCoatom N) (hC : ¬ C ≤ N) :
    Subgroup.closure ((C : Set G) ∪ (N : Set G)) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rcases hN.le_iff.mp (le_sup_right : N ≤ C ⊔ N) with h | h
  · exact h
  · exact (hC (le_sup_left.trans h.le)).elim

private theorem exists_involution_centralizing_center {L : Type} [Group L] [Finite L] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (h : Nonempty (L ≃* CatGroup d)) (U : Sylow p L) :
    ∃ z : L, z ^ 2 = 1 ∧ z ≠ 1 ∧
      (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ≤
        Subgroup.centralizer ({z} : Set L) ∧
      ¬ Subgroup.centralizer ({z} : Set L) ≤ Subgroup.normalizer ((U : Subgroup L) : Set L) := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : CharP K p := UnitaryModel.charP_of_card Fact.out hK
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  refine ⟨e'.symm (UnitaryModel.invol J hJ), ?_, ?_, ?_, ?_⟩
  · apply e'.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply, pow_two]
    exact UnitaryModel.invol_mul_self J hJ
  · intro h1
    apply UnitaryModel.invol_ne_one J hJ h2
    rw [← MulEquiv.apply_symm_apply e' (UnitaryModel.invol J hJ), h1, map_one]
  · intro x hx
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxR : e' x ∈ rootGroup J hJ := by
      rw [← hU]
      exact (UnitaryModel.mem_map_iff e' _ x).2 hxU
    have hxCR : e' x ∈ Subgroup.centralizer (rootGroup J hJ : Set _) := by
      rw [← hU]
      exact (UnitaryModel.mem_centralizer_map_iff e' _ x).2 hxC
    have hmem : e' x ∈ rootGroup J hJ ⊓ Subgroup.centralizer (rootGroup J hJ : Set _) :=
      ⟨hxR, hxCR⟩
    rw [← UnitaryModel.rootGroup_inf_centralizer_invol J hJ hK hfix h2] at hmem
    have hmap : e' x ∈
        (Subgroup.centralizer ({e'.symm (UnitaryModel.invol J hJ)} : Set L)).map
          e'.toMonoidHom := by
      rw [UnitaryModel.map_centralizer_singleton, MulEquiv.apply_symm_apply]
      exact hmem.2
    exact (UnitaryModel.mem_map_iff e' _ x).1 hmap
  · intro hle
    have hle' := Subgroup.map_mono (f := e'.toMonoidHom) hle
    rw [UnitaryModel.map_centralizer_singleton, MulEquiv.apply_symm_apply, hN] at hle'
    have hw := hle' (UnitaryModel.weyl_mem_centralizer_invol J hJ)
    rw [UnitaryModel.normalizer_rootGroup_eq_stabilizer_pinf J hJ hK hfix hq] at hw
    exact weyl_not_mem_stabilizer J hJ hw

end KFactProofs.Stroth.U3Involution

open KFactProofs.Stroth.U3Involution

theorem kFactU3Involution : KFactU3Involution := by
  intro p _ hp5 L _ _ hL U
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨q, hqp, hq1, hv, ⟨e0⟩⟩ := hL
  have hd : IsUnitaryIndex p (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) :=
    ⟨q, hqp, rfl⟩
  have hLd : Nonempty (L ≃* CatGroup (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)) := ⟨e0⟩
  have hfe : (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = 1 := by
    obtain ⟨q', -, hd', hfe, -⟩ := hd.exists_eq
    injection hd' with _ hqq
    subst hqq
    rw [hfe, hq1]
  obtain ⟨hcard, -, hexp, E, hEU, hEel, hEcard⟩ :=
    kFactUnitarySylowStructure L p _ hp2 hd hLd U
  have hmax := kFactUnitaryBorelMaximal L p _ hd hLd U
  obtain ⟨z, hz2, hz1, hzZ, hznc⟩ := exists_involution_centralizing_center hp2 hd hLd U
  rw [hfe] at hcard hEcard
  refine ⟨CFSG.SectionRank.le_pRank hp.one_lt hEU hEel (k := 2) (by simpa using hEcard), ?_⟩
  have hnt : Nontrivial (U : Subgroup L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact one_lt_pow₀ hp.one_lt (by norm_num)
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u₀ ∈ Subgroup.center ↥(U : Subgroup L), u₀ ≠ 1 := by
    have := U.isPGroup'.center_nontrivial
    obtain ⟨⟨u₀, hu₀⟩, h1⟩ := exists_ne (1 : Subgroup.center ↥(U : Subgroup L))
    exact ⟨u₀, hu₀, fun h => h1 (Subtype.ext h)⟩
  have hu1 : (u₀ : L) ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hup : (u₀ : L) ^ p = 1 := hexp u₀ u₀.2
  have hmem : (u₀ : L) ∈ (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) :=
    ⟨u₀.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hu₀ ⟨g, hg⟩)⟩
  exact ⟨u₀, ⟨u₀, hu₀, rfl⟩, orderOf_eq_prime hup hu1, z, hz1, hz2,
    (Subgroup.mem_centralizer_singleton_iff.mp (hzZ hmem)).symm,
    closure_union_eq_top_of_isCoatom hmax hznc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
