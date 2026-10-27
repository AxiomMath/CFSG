module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveCen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveOut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_23_five_of (E : Lin2Hyp) (hexam : Lemma2_4_23_five_exam)
    (hout : Sp4OutCyclic) : Lemma2_4_23_five := by
  intro G _ _ T M H S L D n hcfg s hs hsR hs2 hc h4 x hx hxS
  obtain ⟨F, _, _, hF, φ, hφ⟩ := hexam G T M H S L D n hcfg s hs hsR hs2 hc h4 x hx hxS
  have hn3 : 3 ≤ n := Five.three_le_of_four_lt_two_pow h4
  obtain ⟨f₀, -, -, -, hev, -⟩ := E.exists_f₀ hcfg
  obtain ⟨k, hk⟩ := hev
  have he : 0 < n / 2 := by omega
  have hxT : x ∈ T := (Subgroup.mem_inf.mp hx).1
  have hxs : x * s = s * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hb := Five.centralizer_Ks E hcfg hs hsR hs2 hc h4 hx hxS
  have hTsN : T ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) : Set G) := fun t ht =>
    Five.mem_normalizer_Ks E hcfg hxT hxS hxs (Subgroup.mem_inf.mp ht).1
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ht).2)
  have hTs2 : IsPGroup 2 (T ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :=
    hcfg.sylowT.isPGroup.to_le inf_le_left
  have hRsLs : thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤
      L ⊓ Subgroup.centralizer ({s} : Set G) := inf_le_inf_right _ (E.Rsyl hcfg).1
  have hRsKs : thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤
      L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
        conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x := hRsLs.trans le_sup_left
  have hRsTs : thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) ≤
      T ⊓ Subgroup.centralizer ({s} : Set G) :=
    inf_le_inf_right _ ((thompsonJ_le_self S).trans hcfg.S_le_T)
  have hRs2 : IsPGroup 2 (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :=
    hcfg.S_isPGroup.to_le (inf_le_left.trans (thompsonJ_le_self S))
  have hRscard : Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
      2 ^ (4 * (n / 2)) := by
    rw [(E.card_R_inf_centralizer hcfg hs hsR hs2).2 hc]
    congr 1
    omega
  obtain ⟨⟨t, htT, hTt⟩, hrel⟩ := Five.outer_two_part hF he hout φ hTsN hTs2 hRsKs hRsTs hRs2
    hRscard hx hφ
  rw [hb] at hTt hrel
  have hn2 : 2 * (n / 2) = n := by omega
  refine ⟨⟨F, ‹Field F›, ‹Fintype F›, hF, ?_⟩, hb, ⟨t, htT, ?_⟩, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hCharP : CharP F 2 := charP_of_card_eq_prime_pow hF
    exact ⟨φ.trans (Five.projEquivSymplectic F)⟩
  · rw [sup_comm (Subgroup.zpowers s)]
    exact hTt
  · rw [sup_comm (Subgroup.zpowers s), hrel, hn2]

end CFSG.QuasithinUnique.Lin2
