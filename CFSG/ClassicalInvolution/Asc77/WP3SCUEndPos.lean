module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUEnd
public import CFSG.ClassicalInvolution.Asc77.WP3SCUNG
public import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4
public import CFSG.ClassicalInvolution.Asc77.WP3SCUSuGen
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

section EndPos

variable (p f : ℕ) [Fact p.Prime]

theorem chainFrameEndPos_of_psu
    (hU : ∀ n e : ℕ, p ≠ 2 → 5 ≤ p ^ e → RankFourFacts .PSU n p e) : ChainFrameEndPos p f := by
  intro G _ _ _ Ω K J K' z t z' hs C g a b M hrank hd j hmov
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  set B' : Subgroup G := conjSub g (Subgroup.closure ({z, t, z'} : Set G)) with hB'
  have hBel : IsElemAbelian 2 B' := hd.isElemAbelian
  have hB'eq : B' = Subgroup.closure ({a, z, b} : Set G) := hd.closure_eq
  have haB : a ∈ B' := by rw [hB'eq]; exact Subgroup.subset_closure (by simp)
  have hzB : z ∈ B' := by rw [hB'eq]; exact Subgroup.subset_closure (by simp)
  have hbB : b ∈ B' := by rw [hB'eq]; exact Subgroup.subset_closure (by simp)
  have hBC : B' ≤ Subgroup.centralizer ({z} : Set G) := Lemma52Proof.le_centralizer_of_mem hBel hzB
  have haC := hBC haB
  have hbC := hBC hbB
  have hz1 := C.hKz.ne_one
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hz1
  rcases C.eq_i₀_or_i₁ j with rfl | rfl
  · exfalso
    obtain ⟨y, hy, hne⟩ := hmov _ (oddQuotMk_mem_modOdd haB haC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hBel hzB hz1 haB hd.a_ne_one hd.a_ne_z haC)
    exact hne (C.centralizes_K hd.tq_K haC y hy)
  · have hQ : CFSG.IsComponent (C.psi C.i₁).range := C.isComponent_range C.i₁
    have hBN := FrameVertex.modOdd_le_normalizer C.hp C.hq C.hΩ.conjInvariant C.hΩ.classical
      hs.below C.hc2 hnc hBel hzB hz1 haB hd.a_ne_one hd.a_ne_z hd.mem hd.cls hQ hmov
    obtain ⟨k, R, hR, hmod⟩ := C.exists_fund_of_mem hd.mem
    have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
    rcases C.eq_i₀_or_i₁ k with rfl | rfl
    · exfalso
      have hR' := C.fund_eq_top₀ hR
      have hmod' : modOdd z (exactCore z M) = modOdd z (exactCore z C.K) := by
        rw [← hmod, hR', Subgroup.map_top, C.modOdd_K_eq_range]
      have hU1 := C.isUniqueInvolution_modOdd hd.mem hd.cls
      have hU2 := C.isUniqueInvolution_modOdd ⟨C.hK, C.hKtq⟩ hKcl
      rw [hmod'] at hU1
      have heq := hU1.eq hU2
      apply Lemma52Proof.oddQuotMk_not_mem_zpowers hBel hzB hz1 haB hd.a_ne_one hd.a_ne_z haC
      rw [heq]
      exact oddQuotMk_mem_modOdd (Subgroup.mem_zpowers z) ChainLift.hzC
    · obtain ⟨r, hrR, hrc, hr1, hrbar⟩ :=
        C.exists_central_lift hd.mem hd.cls C.i₁ C.tag₁ hR hmod.symm
      have hquasi : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z M)) := by
        rw [← hmod]
        exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₁)
          (fundQuasisimple_core C.hp (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
            (C.four_le C.i₁ C.tag₁) R hR)
      have hcen := oddQuotMk_centralizes_modOdd_exactCore hd.cls C.hc2 hd.mem.2 hd.tq_M hbC hquasi
      have hbR : ∀ s ∈ R, oddQuotMk z ⟨b, hbC⟩ * C.psi C.i₁ s =
          C.psi C.i₁ s * oddQuotMk z ⟨b, hbC⟩ := by
        intro s hs
        apply hcen
        rw [← hmod]
        exact ⟨s, hs, rfl⟩
      have hb2 : oddQuotMk z ⟨b, hbC⟩ * oddQuotMk z ⟨b, hbC⟩ = 1 := by
        rw [← map_mul]
        have : (⟨b, hbC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨b, hbC⟩ = 1 :=
          Subtype.ext (by simpa [pow_two] using hBel.2 b hbB)
        rw [this, map_one]
      have hF : RankFourFacts (C.D.tag C.i₁) (C.D.rank C.i₁) p (C.D.exp C.i₁) := by
        have he : C.D.exp C.i₁ = f := C.exp_eq C.i₁ C.tag₁
        rcases C.tag₁ with h | h
        · rw [h]; exact rankFourFacts_psl _ hp (by rw [he]; exact hq)
        · rw [h]; exact hU _ _ hp (by rw [he]; exact hq)
      obtain ⟨hgeom, hdich⟩ := hF hrank
      refine ⟨C.tag₁, ?_⟩
      rcases hdich (C.psi C.i₁) (C.psi_ker C.i₁) hR (hBN (oddQuotMk_mem_modOdd hbB hbC)) hb2 hbR
        with ⟨R'', hR'', hcomm, hv''⟩ | hpos
      · exact (false_of_graph_type hs C hd hgeom hR hmod.symm hrR hr1 hR'' hcomm hbC hv'').elim
      · apply hpos r hrR hrc
        set T : Subgroup (OddQuot z) := Subgroup.closure
          (({C.psi C.i₁ r, oddQuotMk z ⟨b, hbC⟩} : Set (OddQuot z)) ∪
            (Subgroup.center (OddQuot z) : Set (OddQuot z))) with hT
        have haT : oddQuotMk z ⟨a, haC⟩ ∈ T := by
          rw [hrbar]
          exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
        have hzbar : oddQuotMk z ⟨z, ChainLift.hzC⟩ ∈ T :=
          Subgroup.subset_closure (Or.inr (Subgroup.mem_center_iff.mpr fun y =>
            (oddQuotMk_central ChainLift.hzC y).symm))
        have hbbar : oddQuotMk z ⟨b, hbC⟩ ∈ T :=
          Subgroup.subset_closure (Or.inl (Or.inr rfl))
        have hTg : B' ≤
            (T.comap (oddQuotMk z)).map (Subgroup.centralizer ({z} : Set G)).subtype := by
          rw [hB'eq, Subgroup.closure_le]
          intro u hu
          rcases hu with rfl | rfl | rfl
          · exact ⟨⟨u, haC⟩, haT, rfl⟩
          · exact ⟨⟨u, ChainLift.hzC⟩, hzbar, rfl⟩
          · exact ⟨⟨u, hbC⟩, hbbar, rfl⟩
        rintro y ⟨k, hk, rfl⟩
        obtain ⟨u, hu, huk⟩ := hTg hk
        have : u = k := Subtype.ext huk
        rw [← this]
        exact hu

theorem chainFrameHyp51t_of_psu
    (hU : ∀ n e : ℕ, p ≠ 2 → 5 ≤ p ^ e → RankFourFacts .PSU n p e) : ChainFrameHyp51t p f :=
  chainFrameHyp51t_of_endPos (chainFrameEndPos_of_psu p f hU)

theorem chainFrameGenT_of_psu
    (hU : ∀ n e : ℕ, p ≠ 2 → 5 ≤ p ^ e → RankFourFacts .PSU n p e) : ChainFrameGenT p f :=
  chainFrameGenT_of_endPos (chainFrameEndPos_of_psu p f hU) suPairGen

end EndPos

end CFSG.ClassicalInvolution.Asc77
