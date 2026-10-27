module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD3Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ResidueDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Fix
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open Equiv Equiv.Perm

theorem card_alternatingGroup_inf_centralizer_eight {σ : Perm (Fin 8)} (hσ : σ ^ 2 = 1) :
    Nat.card (alternatingGroup (Fin 8) ⊓ centralizer {σ} : Subgroup (Perm (Fin 8))) ∈
      ({20160, 720, 96, 48, 192} : Finset ℕ) := by
  obtain ⟨k, -, hk, hc, -⟩ := exists_cycleType_eq_replicate_two hσ
  have h2 := card_alternatingGroup_inf_centralizer_mul_two hσ (by simp)
  rw [hc, Fintype.card_fin] at h2
  rw [Fintype.card_fin] at hk
  have hk4 : k ≤ 4 := by omega
  interval_cases k <;> simp [Nat.factorial] at h2 ⊢ <;> omega

theorem not_hasElemAbThree81_of_layer_alt8 {X : Type} [Group X] [Finite X] {z : X}
    {H : Subgroup X} (hz : orderOf z = 2) (hH : Nonempty (H ≃* alternatingGroup (Fin 8)))
    (hC : centralizer ({z} : Set X) = H ⊔ zpowers z) (hz' : z ∈ centralizer (H : Set X))
    (hE : Nonempty (egaLayer (X ⧸ fusionOddCore X) ≃* alternatingGroup (Fin 8))) :
    ¬ HasElemAbThree81 (X ⧸ fusionOddCore X) := by
  rintro ⟨S, hS81, -, -⟩
  obtain ⟨e⟩ := hE
  obtain ⟨eA⟩ := hH
  obtain ⟨hs, hnab⟩ := isSimpleGroup_and_not_comm_of_mulEquiv_alt8 eA
  obtain ⟨-, -, hHcard, ho, ht', hC'⟩ := quotient_facts_of_centralizer_eq hnab hz hC hz'
  have hA8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hHcard' : Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) = 20160 := by
    rw [hHcard, Nat.card_congr eA.toEquiv, hA8]
  have hEcard : Nat.card (egaLayer (X ⧸ fusionOddCore X)) = 20160 := by
    rw [Nat.card_congr e.toEquiv, hA8]
  have ht : QuotientGroup.mk' (fusionOddCore X) z ^ 2 = 1 := by rw [← ho, pow_orderOf_eq_one]
  obtain ⟨f, hf, hfix, -⟩ := exists_mulAut_of_normal e ht
  obtain ⟨σ, hσ2, hσ⟩ :=
    exists_perm_sq_eq_one_of_mulAut_alternatingGroup (Or.inr (by norm_num)) f hf
  have hmem := card_alternatingGroup_inf_centralizer_eight hσ2
  rw [← card_fixed_mulAut_alternatingGroup hσ, hfix] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hHE := map_le_of_two_lt_card_inf_centralizer hnab hz hC hz' (egaLayer_normal _)
    (by omega)
  have hKE : egaLayer (X ⧸ fusionOddCore X) ⊓
      centralizer ({QuotientGroup.mk' (fusionOddCore X) z} : Set (X ⧸ fusionOddCore X)) =
        egaLayer (X ⧸ fusionOddCore X) := by
    refine eq_of_le_of_card_ge inf_le_left ?_
    rcases card_inf_centralizer_mk_le_two_or hnab hz hC hz' (egaLayer_normal _) with h | h
    · omega
    · omega
  have htQ : QuotientGroup.mk' (fusionOddCore X) z ∈
      centralizer (egaLayer (X ⧸ fusionOddCore X) : Set (X ⧸ fusionOddCore X)) := by
    rw [mem_centralizer_iff]
    intro x hx
    rw [← hKE] at hx
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have hQ := eq_zpowers_of_inf_centralizer_le_zpowers
    (standardComponentOddCore_quotient_fusionOddCore_eq_bot X) inferInstance ho htQ
    (centralizer_inf_centralizer_mk_le_zpowers hnab hz hC hz' hHE)
  have htop : centralizer ({QuotientGroup.mk' (fusionOddCore X) z} :
      Set (X ⧸ fusionOddCore X)) = ⊤ := by
    refine eq_top_iff.2 fun y _ => mem_centralizer_singleton_iff.2 ?_
    have hy : y * QuotientGroup.mk' (fusionOddCore X) z * y⁻¹ ∈
        zpowers (QuotientGroup.mk' (fusionOddCore X) z) := by
      rw [← hQ]
      exact (normal_centralizer (H := egaLayer (X ⧸ fusionOddCore X))).conj_mem _ htQ y
    rcases eq_one_or_eq_of_mem_zpowers ho hy with h | h
    · rw [conj_eq_one_iff] at h
      rw [h, orderOf_one] at ho
      exact absurd ho (by norm_num)
    · calc y * QuotientGroup.mk' (fusionOddCore X) z
          = y * QuotientGroup.mk' (fusionOddCore X) z * y⁻¹ * y := by group
        _ = QuotientGroup.mk' (fusionOddCore X) z * y := by rw [h]
  have hcard : Nat.card (X ⧸ fusionOddCore X) ≤ 40320 := by
    rw [← card_top (G := X ⧸ fusionOddCore X), ← htop, hC']
    calc Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X)) ⊔
          zpowers (QuotientGroup.mk' (fusionOddCore X) z) : Subgroup _)
        ≤ Nat.card (H.map (QuotientGroup.mk' (fusionOddCore X))) *
            Nat.card (zpowers (QuotientGroup.mk' (fusionOddCore X) z)) :=
          card_sup_zpowers_le (centralizer_le_normalizer _ ht')
      _ = 40320 := by rw [hHcard', Nat.card_zpowers, ho]
  have h81 : 81 ∣ Nat.card (X ⧸ fusionOddCore X) := hS81 ▸ card_subgroup_dvd_card S
  have h20160 : 20160 ∣ Nat.card (X ⧸ fusionOddCore X) :=
    hHcard' ▸ card_subgroup_dvd_card (H.map (QuotientGroup.mk' (fusionOddCore X)))
  have hpos : 0 < Nat.card (X ⧸ fusionOddCore X) := Nat.card_pos
  omega

end CFSG.EvenSporadicStandard.M24Std
