module

public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QTrans
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcComm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

theorem uexc_std_map {p : ℕ} (hp : p.Prime) {Ω Ω' : Type} [Group Ω] [Finite Ω] [Group Ω']
    (π : Ω →* Ω') (hN : ¬ p ∣ Nat.card π.ker) {S B D K : Subgroup Ω} {x : Ω} (hS : S.Normal)
    (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) (hstd : GLAStdSubPre p B x S D K) :
    GLAStdSubPre p (B.map π) (π x) (S.map π) (D.map π) (K.map π) := by
  obtain ⟨hDB, hDel, hDcard, hxD, hKlay, hKcomp, hDK⟩ := hstd
  have hDp : IsPGroup p D := isPGroup_of_isElemAbelian hDel
  have hDN : D ≤ Subgroup.normalizer (S : Set Ω) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 hS]
    exact Subgroup.mem_top g
  have hKq : CFSG.Open.IsQuasisimple ↥K := hKcomp.2.2
  have hKY : K ≤ S ⊓ Subgroup.centralizer (D : Set Ω) := hKcomp.1
  have hKS : K ≤ S := hKY.trans inf_le_left
  have hZ : ∀ n ∈ π.ker, ∀ s ∈ S, s * n = n * s := fun n hn s hs =>
    Subgroup.mem_centralizer_iff.1 (hkc hn) s hs
  have hYmap : (S ⊓ Subgroup.centralizer (D : Set Ω)).map π =
      S.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup Ω') : Set Ω') :=
    S267.map_inf_centralizer hp π hN hDp hDN
  have hKnot : ¬ K ≤ π.ker := fun hle =>
    S265.not_le_of_isQuasisimple_central hKq hle (fun z hz k hk => hZ z hz k (hKS hk))
  have hcompK : IsComponentOf (K.map π)
      (S.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup Ω') : Set Ω')) := by
    rw [← hYmap]
    exact S12.isComponentOf_map_of_not_le_ker π hKcomp hKnot
  refine ⟨Subgroup.map_mono hDB, CFSG.Open.IsElemAbelian.map hDel π, ?_,
    Subgroup.mem_map_of_mem π hxD, ?_, hcompK, ?_⟩
  · rw [S267.card_map_of_isPGroup hp π hN hDp, hDcard]
  · apply le_antisymm
    · exact I142N.le_GLALayer hcompK
    · have h := S265.glaLayer_map_le_central π (Y := S ⊓ Subgroup.centralizer (D : Set Ω))
        (fun n hn hn1 y hy => hZ n (MonoidHom.mem_ker.2 hn1) y hy.1)
      rw [hYmap, ← hKlay] at h
      exact h
  · apply le_antisymm
    · intro y hy
      have hyD : y ∈ D.map π := hy
      rw [hDK] at hyD
      obtain ⟨d, hd, rfl⟩ := hyD
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem π hd.1,
        Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hd.2 k hk]
    · rintro _ ⟨hc₂, hc₂K⟩
      obtain ⟨c, hcB, rfl⟩ := Subgroup.mem_map.1 hc₂
      have hKker : π.ker ≤ Subgroup.centralizer (K : Set Ω) :=
        hkc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hKS))
      have hcK : c ∈ Subgroup.centralizer (K : Set Ω) :=
        uexc_centralizer_of_map π (uexc_commutator_self hKq.1) hKker hc₂K
      have hcD : c ∈ D := by
        rw [hDK]
        exact ⟨hcB, hcK⟩
      exact Subgroup.mem_map_of_mem π hcD

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
