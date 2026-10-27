module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Gen
public import CFSG.LocalAnalysis.GL83PartI.I_22_6.Center
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.GeneratedCore

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ} {B : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem IsFam.layer_le_centralizer_cen (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    {c : G} (hc : c ∈ cen B K₀) : layer 𝒦 ≤ Subgroup.centralizer ({c} : Set G) := by
  refine iSup₂_le fun K hK y hy => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw]
  exact hF.cen_comm hK₀ hc hK y hy

theorem IsFam.cen_le_centralizer_of_le_layer (hF : IsFam p B 𝒦) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ 𝒦) {M : Subgroup G} (hM : M ≤ layer 𝒦) :
    cen B K₀ ≤ Subgroup.centralizer (M : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact (Subgroup.mem_centralizer_iff.1 (hF.layer_le_centralizer_cen hK₀ hc (hM hm)) c rfl).symm

section Norm

variable [Fact p.Prime] {K₀ : Subgroup G}

theorem IsFam.le_centralizer_normSub (hF : IsFam p B 𝒦) (hK₀ : K₀ ∈ 𝒦) {K : Subgroup G}
    (hK : K ∈ 𝒦) {b : G} (hb : b ∈ B) (hbA : b ∉ stab B K) :
    cen B K₀ ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer (normSub (hF.normComm hK hb hbA) : Set G) := by
  refine sup_le (hF.cen_le_centralizer_of_le_layer hK₀ (normSub_le_layer hF hK hb _))
    ((Subgroup.zpowers_le).2 ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact (mem_normSub_comm _ (hF.elem.2 b hb) hm).symm

variable [Finite G]

theorem IsFam.normSub_le_gamma (hF : IsFam p B 𝒦) (hK₀ : K₀ ∈ 𝒦)
    (hC : p ∣ Nat.card (cen B K₀)) {K : Subgroup G} (hK : K ∈ 𝒦) {b : G} (hb : b ∈ B)
    (hbA : b ∉ stab B K) : normSub (hF.normComm hK hb hbA) ≤ GLBCore p 2 B := by
  have hp := (Fact.out : p.Prime)
  have hCB : cen B K₀ ≤ B := inf_le_left
  have hbC : b ∉ cen B K₀ := fun h => hbA (by
    rw [hF.stab_eq hK hK₀]
    exact cen_le_stab B K₀ h)
  have hQB : cen B K₀ ⊔ Subgroup.zpowers b ≤ B := sup_le hCB ((Subgroup.zpowers_le).2 hb)
  have hcard : Nat.card (cen B K₀ ⊔ Subgroup.zpowers b : Subgroup G) =
      p * Nat.card (cen B K₀) := card_sup_zpowers hF.elem hCB hb hbC
  obtain ⟨i, hi⟩ := exists_card_eq_pow (elem_mono hF.elem hCB)
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [pow_zero] at hi
      rw [hi] at hC
      exact absurd (Nat.le_of_dvd one_pos hC) (by have := hp.two_le; omega)
    · exact h0
  have hrank : 2 ≤ pRank p (cen B K₀ ⊔ Subgroup.zpowers b) := by
    have h := CFSG.SectionRank.le_pRank hp.one_lt (le_refl (cen B K₀ ⊔ Subgroup.zpowers b))
      (elem_mono hF.elem hQB) (k := i + 1) (by rw [hcard, hi, pow_succ'])
    omega
  have h1 : normSub (hF.normComm hK hb hbA) ≤
      Subgroup.centralizer ((cen B K₀ ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 (hF.le_centralizer_normSub hK₀ hK hb hbA)
  exact h1.trans ((Subgroup.centralizer_le_normalizer _).trans
    (le_sSup ⟨cen B K₀ ⊔ Subgroup.zpowers b, hQB, hrank, rfl⟩))

theorem IsFam.false_of_stab_le_cen (hodd : p ≠ 2) (hF : IsFam p B 𝒦)
    (hSC : ∀ y ∈ Subgroup.centralizer (B : Set G), y ^ p = 1 → y ∈ B)
    (hK₀ : K₀ ∈ 𝒦) (hdvd : p ∣ Nat.card K₀)
    (hB : Nat.card B = p * Nat.card (stab B K₀)) (hC : stab B K₀ ≤ cen B K₀) : False := by
  have hp := (Fact.out : p.Prime)
  have hAB : stab B K₀ ≤ B := inf_le_left
  have hApos : 0 < Nat.card (stab B K₀) := Nat.card_pos
  have hlt : Nat.card (stab B K₀) < Nat.card B := by
    rw [hB]
    have := hp.two_le
    nlinarith
  obtain ⟨b, hb, hbA⟩ := exists_not_mem_of_card_lt hlt
  have hsup : B ≤ stab B K₀ ⊔ Subgroup.zpowers b := by
    have hle : stab B K₀ ⊔ Subgroup.zpowers b ≤ B := sup_le hAB ((Subgroup.zpowers_le).2 hb)
    have hc := card_sup_zpowers hF.elem hAB hb hbA
    have heq : stab B K₀ ⊔ Subgroup.zpowers b = B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hB])
    rw [heq]
  have hc := hF.normComm hK₀ hb hbA
  have hQ : IsQuasisimple K₀ := hF.quasi K₀ hK₀
  have hBM : B ≤ Subgroup.centralizer (normSub hc : Set G) := by
    refine hsup.trans (sup_le (fun a ha => ?_) ((Subgroup.zpowers_le).2 ?_))
    · exact hF.cen_le_centralizer_of_le_layer hK₀ (normSub_le_layer hF hK₀ hb hc) (hC ha)
    · rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (mem_normSub_comm hc (hF.elem.2 b hb) hm).symm
  obtain ⟨x₀, hx₀ord, hx₀Z⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center hQ hp
      hodd hdvd
  have hx₀p : x₀ ^ p = 1 := by
    rw [← hx₀ord]
    exact pow_orderOf_eq_one _
  have hy1 : normHom hc x₀ ≠ 1 := fun h =>
    hx₀Z (normHom_ker_le_center hc (MonoidHom.mem_ker.2 h))
  have hyp : normHom hc x₀ ^ p = 1 := by rw [← map_pow, hx₀p, map_one]
  have hyord : orderOf (normHom hc x₀) = p := orderOf_eq_prime hyp hy1
  have hyM : normHom hc x₀ ∈ normSub hc := ⟨x₀, rfl⟩
  have hdvdM : p ∣ Nat.card (normSub hc) := by
    have h := orderOf_dvd_natCard (⟨_, hyM⟩ : normSub hc)
    rwa [Subgroup.orderOf_mk, hyord] at h
  obtain ⟨x, hxord, hxZ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      (isQuasisimple_normSub hc hQ) hp hodd hdvdM
  have hxp : (x : G) ^ p = 1 := by
    have h : x ^ p = 1 := by
      have h' := pow_orderOf_eq_one x
      rwa [hxord] at h'
    exact congrArg Subtype.val h
  have hxB : (x : G) ∈ B := by
    refine hSC x (Subgroup.mem_centralizer_iff.2 fun c hcB => ?_) hxp
    exact (Subgroup.mem_centralizer_iff.1 (hBM hcB) x x.2).symm
  refine hxZ (Subgroup.mem_center_iff.2 fun m => Subtype.ext ?_)
  exact Subgroup.mem_centralizer_iff.1 (hBM hxB) m m.2

theorem IsFam.layer_le_gamma (hodd : p ≠ 2) (hF : IsFam p B 𝒦)
    (hSC : ∀ y ∈ Subgroup.centralizer (B : Set G), y ^ p = 1 → y ∈ B) (hK₀ : K₀ ∈ 𝒦)
    (hKB : ¬ B ≤ Subgroup.normalizer (K₀ : Set G))
    (hZ : p ∣ Nat.card (Subgroup.center K₀)) : layer 𝒦 ≤ GLBCore p 2 B := by
  have hp := (Fact.out : p.Prime)
  have hC : p ∣ Nat.card (cen B K₀) := hF.dvd_card_cen hSC hK₀ hZ
  have hdvdK : p ∣ Nat.card K₀ := hZ.trans (Subgroup.card_subgroup_dvd_card _)
  have hAB : stab B K₀ ≤ B := inf_le_left
  obtain ⟨i, hi⟩ := exists_card_eq_pow (elem_mono hF.elem hAB)
  obtain ⟨j, hj⟩ := exists_card_eq_pow hF.elem
  have hij : i < j := by
    have hle : i ≤ j := by
      have h := Subgroup.card_le_of_le hAB
      rw [hi, hj] at h
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
    refine lt_of_le_of_ne hle fun h => hKB ?_
    have hAeq : stab B K₀ = B := Subgroup.eq_of_le_of_card_ge hAB (by rw [hi, hj, h])
    exact (le_of_eq hAeq.symm).trans inf_le_right
  have hnorm : layer 𝒦 ≤ normJoin hF K₀ := by
    by_cases h2 : i + 2 ≤ j
    · refine hF.layer_le_normJoin_two hK₀ ?_
      rw [hi, hj]
      calc p ^ 2 * p ^ i = p ^ (2 + i) := (pow_add p 2 i).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
    · have hj' : j = i + 1 := by omega
      have hB1 : Nat.card B = p * Nat.card (stab B K₀) := by
        rw [hi, hj, hj', pow_succ']
      by_cases hAC : stab B K₀ ≤ cen B K₀
      · exact (hF.false_of_stab_le_cen hodd hSC hK₀ hdvdK hB1 hAC).elim
      · exact hF.layer_le_normJoin_one hK₀ hB1 hAC
  refine hnorm.trans (iSup₂_le fun M hM => ?_)
  obtain ⟨b, hb, hbA, K, hK, hbA', rfl⟩ := hM
  exact hF.normSub_le_gamma hK₀ hC hK hb hbA'

end Norm

end GL83.CompFam
