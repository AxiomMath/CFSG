module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralH8
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreMain
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2S3Main

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.FritzL2

open CFSG Subgroup Equiv CFSG.ComponentClassification.HSFLit
open CFSG.ComponentClassification.HSDihedral.H8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

omit [Finite X] in
theorem map_ker (A : L2Data t L) : A.ψ.ker.map A.T.subtype = A.K := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, (A.ψ_eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, MonoidHom.mem_ker.mpr ((A.ψ_eq_one_iff _).mpr hx.2), rfl⟩

@[expose] def datum (A : L2Data t L) : LocalDatum X (Perm (ZMod 8)) where
  t := t
  S := A.T
  D := A.R
  ψ := A.ψ
  orderOf_t := A.orderOf_t
  sylow := ⟨A.syl, rfl⟩
  D_le := inf_le_left
  conj_mem_D := fun s hs d hd => mem_inf.mpr ⟨mul_mem (mul_mem hs hd.1) (inv_mem hs),
    (mem_normalizer_iff.mp (A.config.le_normalizer (A.T_le_centralizer hs)) d).mp hd.2⟩
  eq_one_of_mem_D := fun d hd h1 =>
    A.eq_of_ψ_eq hd (one_mem _) (h1.trans (map_one A.ψ).symm)
  t_mem_ker := fun ht => (A.mem_K_iff ht).mp A.t_mem_K
  t_not_mem_D := fun ht => A.config.not_mem ht.2
  isCyclic_ker :=
    ((A.ψ.ker.equivMapOfInjective A.T.subtype A.T.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_ker A))).isCyclic.mpr A.isCyclic_K
  dihedral := ⟨4, by norm_num, A.config.inf_L_mulEquiv_dihedral A.syl⟩

theorem Dbar_datum (A : L2Data t L) : (datum A).Dbar = R8 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact A.ψ_mem_R8 g hg.2
  · intro σ hσ
    obtain ⟨g, hgL, rfl⟩ := A.exists_ψ_eq σ hσ
    exact ⟨g, ⟨g.2, hgL⟩, rfl⟩

theorem autFacts_datum (A : L2Data t L) : AutFacts (datum A) := by
  refine (datum A).autFacts_of_autPair ?_
  rw [Dbar_datum]
  exact autPair_H8 A.R8_le_range A.range_le_H8

theorem fritzL2Lemma378 :
    FritzL2Lemma378 := by
  intro hH X _ _ _ _ t L A k hk hk2 hψk hK
  by_contra hnot
  obtain ⟨hQ, -⟩ := (datum A).coreOut hH (autFacts_datum A) hnot
  apply hK
  have hKt : A.K = zpowers t := (map_ker A).symm.trans hQ
  rw [hKt, Nat.card_zpowers, A.orderOf_t]

theorem fritzL2Lemma36Final :
    FritzL2Lemma36Final := by
  intro hH X _ _ _ _ t L A _ hinv _ _
  by_contra hnot
  obtain ⟨-, w, hwS, hw2, hwD, hwn⟩ := (datum A).coreOut hH (autFacts_datum A) hnot
  have hα : (datum A).ψe w = A.ψ ⟨w, hwS⟩ := (datum A).ψe_of_mem hwS
  rw [Dbar_datum, hα] at hwD hwn
  have h16 := hinv ⟨w, hwS⟩ hw2
  obtain ⟨u, b, hub⟩ := A.ψ_mem_H8 ⟨w, hwS⟩
  rw [← hub] at hwD hwn h16
  have hP : (datum A).R ≤ H8 := A.range_le_H8
  rcases centralizer_cases hP (hub ▸ ⟨⟨w, hwS⟩, rfl⟩ : aff8 u b ∈ (datum A).R) hwD with h | h
  · exact hwn h
  · obtain ⟨u₂, b₂, hu₂, he⟩ := h16
    have hfb : fbit8 u = 0 := by
      rw [(aff8_injective he).1.symm]
      exact (fbit8_eq_zero_iff u₂).mpr hu₂
    obtain ⟨u₃, c₃, hu₃, he₃⟩ := h
    rw [aff8_mul] at he₃
    have h1 := (aff8_injective he₃).1
    have hf1 := (fbit8_eq_zero_iff u₃).mpr hu₃
    rw [h1, L2Act.fbit8_mul, hfb] at hf1
    exact absurd hf1 (by decide)

end CFSG.ComponentClassification.HSDihedral.FritzL2
