module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality.LayerNaturality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerPerfectCoreContainment.LayerPerfectCoreContainment
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerSylowAtLeastTwo

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem map_conj_self {C : Subgroup G} {c : G} (hc : c ∈ C) :
    C.map (MulAut.conj c).toMonoidHom = C := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact C.mul_mem (C.mul_mem hc hy) (C.inv_mem hc)
  · intro hx
    refine ⟨c⁻¹ * x * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hx) hc, ?_⟩
    group

theorem le_normalizer_layer (C : Subgroup G) :
    C ≤ Subgroup.normalizer ((CFSG.Open.rankThreeLayer C : Subgroup G) : Set G) := by
  intro c hc
  have h := LayerNaturality.map_layer (MulAut.conj c) C
  rw [map_conj_self hc] at h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : c * x * c⁻¹ ∈ (CFSG.Open.rankThreeLayer C).map (MulAut.conj c).toMonoidHom :=
      ⟨x, hx, by simp⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      exact mul_left_cancel (mul_right_cancel hyx)
    exact this ▸ hy

theorem isSylow {p : ℕ} (hp : p.Prime) {P P₀ : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤)
    (hPC : P ≤ Subgroup.centralizer (P₀ : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf p
      (P ⊓ CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)))
      (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hC : CFSG.ABGLocalTools.IsSylowOf p P (Subgroup.centralizer (P₀ : Set G)) :=
    hP.of_le hPC le_top
  have hle : CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤
      Subgroup.centralizer (P₀ : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerPerfectCoreContainment.layer_le_perfectCore _).trans
      (CFSG.Quasithin.perfectCore_le _)
  exact hC.inf_of_le_normalizer hle (le_normalizer_layer _)

private theorem elemAbelian_map {K : Type*} [Group K] {p : ℕ} {E : Subgroup K}
    (hE : CFSG.Open.IsElemAbelian p E) (f : K →* G) (hf : Function.Injective f) :
    CFSG.Open.IsElemAbelian p (E.map f) ∧ Nat.card (E.map f) = Nat.card E := by
  haveI := hE.1
  refine ⟨⟨⟨⟨?_⟩⟩, ?_⟩, (Nat.card_congr (E.equivMapOfInjective f hf).toEquiv).symm⟩
  · rintro ⟨x, a, ha, rfl⟩ ⟨y, b, hb, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem one_lt_rank {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) {P P₀ : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤)
    (hPC : P ≤ Subgroup.centralizer (P₀ : Set G))
    (hmodel : ∃ n : ℕ, 1 < n ∧ Nonempty
      (↥(CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ≃*
        PSL(2, GaloisField p n))) :
    1 < CFSG.Open.pRank p
      (P ⊓ CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) := by
  have hp : p.Prime := hpF.out
  obtain ⟨n, hn, ⟨φ⟩⟩ := hmodel
  obtain ⟨E, hE, hcard⟩ :=
    CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup.exists_elemAbelian hp2 n hn
  set H := CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) with hH
  let f : PSL(2, GaloisField p n) →* G := H.subtype.comp φ.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp φ.symm.injective
  obtain ⟨hE', hc'⟩ := elemAbelian_map hE f hf
  have hle : E.map f ≤ H := by
    rintro _ ⟨a, -, rfl⟩
    exact (φ.symm a).2
  have h1 : Nat.card (E.map f) ≤ p ^ CFSG.Open.pRank p H := by
    obtain ⟨rank, hrank⟩ := hE'.isPGroup.exists_card_eq
    rw [hrank]
    exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.le_pRank hp.one_lt hle hE' hrank)
  rw [hc', hcard] at h1
  have h2 : n ≤ CFSG.Open.pRank p H := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have h4 : CFSG.Open.pRank p (P ⊓ H) = CFSG.Open.pRank p H :=
    CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow hp (isSylow hp hP hPC)
  omega

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerSylowAtLeastTwo
