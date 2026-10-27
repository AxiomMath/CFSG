module

public import CFSG.ClassicalInvolution.Q3.TL4SecClqE2T
public import CFSG.ClassicalInvolution.Q3.TL4SecClqE2W
public import CFSG.ClassicalInvolution.Q3.TL4SecClqE8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent AEIdentOn)

namespace SecClq

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_of_label_eq' (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    {m : ℕ} (hm : 5 ≤ m) (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    {K J : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {α : Finset (Fin m)} {h : α.card = 4}
    {b : Bool}
    (hlabK : (K.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlabJ : (J.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b) : K = J := by
  obtain ⟨a, haK, ha2⟩ := SecIdE2.exists_mul_self_ne_one_mem hd hc K hK
  refine SecIdE2.eq_of_phi_mem φ hd hc hO2 hm hker hlabel hK hJ haK ha2 ?_
  rw [hlabJ, ← hlabK]
  exact ⟨⟨a, le_pSpan hK haK⟩, Subgroup.mem_subgroupOf.mpr haK, rfl⟩

theorem card_le_four_of_clique (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≤ 8)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    {k : ℕ} (B : Fin k → Subgroup Y) (hB : ∀ i, B i ∈ CoreAssembly.conjClass (tightCore R))
    (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) :
    k ≤ 4 := by
  choose α h b hlab using fun i => hlabel (B i) (hB i)
  have hED : ∀ i j, i ≠ j → α i = α j ∨ Disjoint (α i) (α j) := fun i j hij => by
    obtain ⟨u, hu⟩ := AlphaFr.E2A.exists_isUniqueInvolution hd (hB i)
    exact AlphaFr.E2A.eq_or_disjoint_of_commutes hd hc hO2 hm φ (hB i)
      (AlphaFr.E2A.commutes_of_mem_omegaNbr hd hc hO2 (hB i) (hadj i j hij)) (hlab i) (hlab j) hu
  have hlinj : ∀ i j, α i = α j → b i = b j → i = j := fun i j hα hb => by
    apply hinj
    refine eq_of_label_eq' hd hc hO2 hm φ hker hlabel (hB i) (hB j) (hlab i) ?_
    rw [hlab j, ← hb]
    exact memBar_congr (h j) (h i) hα.symm (b i)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  set i0 : Fin k := ⟨0, hk⟩
  by_cases h8 : m = 8
  · subst h8
    have hcases : ∀ i, α i = α i0 ∨ α i = (α i0)ᶜ := fun i => by
      by_cases hi : i = i0
      · exact Or.inl (by rw [hi])
      · rcases hED i0 i (Ne.symm hi) with e | hdisj
        · exact Or.inl e.symm
        · exact Or.inr (AlphaFr.E2A.eq_compl_of_disjoint (h i0) (h i) hdisj)
    have hf : Function.Injective (fun i => (decide (α i = α i0), b i)) := by
      intro i j hij
      simp only [Prod.mk.injEq] at hij
      obtain ⟨h1, h2⟩ := hij
      have hiff : α i = α i0 ↔ α j = α i0 := by simpa using h1
      refine hlinj i j ?_ h2
      by_cases hi : α i = α i0
      · exact hi.trans (hiff.mp hi).symm
      · exact ((hcases i).resolve_left hi).trans
          ((hcases j).resolve_left fun hj => hi (hiff.mpr hj)).symm
    have := Fintype.card_le_of_injective _ hf
    simpa using this
  · have hall : ∀ i, α i = α i0 := fun i => by
      by_cases hi : i = i0
      · rw [hi]
      · rcases hED i0 i (Ne.symm hi) with e | hdisj
        · exact e.symm
        · exact absurd (AlphaFr.E2A.eight_le_of_disjoint (h i0) (h i) hdisj) (by omega)
    have hf : Function.Injective b := fun i j hb => hlinj i j ((hall i).trans (hall j).symm) hb
    have := Fintype.card_le_of_injective b hf
    simp only [Fintype.card_fin, Fintype.card_bool] at this
    omega

end SecClq

section Cit3


theorem secIdE2Clique5_proved : SecIdE2Clique5 := by
  intro n _ hP Y _ _ hn R S t hd hc hO2 B hB hinj hadj
  rcases SecIdE2.thmDConcl_of hP hn hd hc hO2 with
    h1 | ⟨W, hW1⟩ | ⟨E, hE⟩ | h64 | ⟨m, hm, ⟨I⟩⟩ | h29
  · exact absurd (h1 _ (hB 0) _ (hB 1)) (hinj.ne (by decide))
  · exact SecClq.dConnected_of_wSet_clique5 hd hc hO2 hW1 B hB hinj hadj
  · obtain ⟨g, hg⟩ := hB 0
    have h1 := omegaNbr_conj hd.hypOmegaGen.conjInvariant (hadj 0 1 (by decide)) g⁻¹
    rw [← hg, conjSub_inv_conjSub] at h1
    exact SecClq.dConnected_of_e8_edge hd hO2 hE h1
  · obtain ⟨I⟩ := h64
    refine absurd (SecClq.card_le_four_of_clique hd hc hO2 (by norm_num) (by norm_num) I.φ
      I.ker_le (fun L hL => ?_) B hB hinj hadj) (by norm_num)
    obtain ⟨α, -, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, hlab⟩
  · by_cases hm9 : 9 ≤ m
    · exact AlphaFr.E2A.dConnected_of_aeIdent hd hc hO2 hm9 I
    · exact absurd (SecClq.card_le_four_of_clique hd hc hO2 hm (by omega) I.φ I.ker_le I.label B
        hB hinj hadj) (by norm_num)
  · obtain ⟨I⟩ := h29
    refine absurd (SecClq.card_le_four_of_clique hd hc hO2 (by norm_num) le_rfl I.φ I.ker_le
      (fun L hL => ?_) B hB hinj hadj) (by norm_num)
    obtain ⟨α, -, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, hlab⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
