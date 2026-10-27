module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSylow

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem le_normalizer_of_normal {Lb : Subgroup Q} [hLn : Lb.Normal] (E : Subgroup Q) :
    E ≤ Subgroup.normalizer (Lb : Set Q) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hLn.conj_mem h hh x, fun hh => ?_⟩
  have := hLn.conj_mem _ hh x⁻¹
  simpa [mul_assoc] using this

omit [Finite Q] in
theorem inf_sup_eq_of_inf_eq_bot {Lb B C : Subgroup Q} [C.Normal] (hLC : Lb ⊓ C = ⊥) :
    Lb ⊓ ((Lb ⊓ B) ⊔ C) = Lb ⊓ B := by
  refine le_antisymm (fun x hx => ?_) (le_inf inf_le_left le_sup_left)
  obtain ⟨hxL, hx⟩ := hx
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hcL : c ∈ Lb := by
    have : c = a⁻¹ * (a * c) := by group
    rw [this]
    exact Lb.mul_mem (Lb.inv_mem ha.1) hxL
  have hc1 : c = 1 := by
    have : c ∈ Lb ⊓ C := ⟨hcL, hc⟩
    rw [hLC] at this
    exact Subgroup.mem_bot.mp this
  rw [hc1, mul_one]
  exact ha

theorem isSylowTwoOf_top_of_even {Lb B Tb : Subgroup Q} [hLn : Lb.Normal]
    (hD6 : (Lb ⊔ Subgroup.centralizer (Lb : Set Q)).index ∣ 6)
    (hCB : Subgroup.centralizer (Lb : Set Q) ≤ B)
    (hLC : Lb ⊓ Subgroup.centralizer (Lb : Set Q) = ⊥)
    (hodd : ¬ 2 ∣ (Lb ⊓ B).relIndex Lb)
    (heven : 2 ∣ (B ⊓ (Lb ⊔ Subgroup.centralizer (Lb : Set Q))).relIndex B)
    (hT : IsSylowTwoOf Tb B) : IsSylowTwoOf Tb ⊤ := by
  set C := Subgroup.centralizer (Lb : Set Q) with hCdef
  set D := Lb ⊔ C with hD
  set B' := B ⊓ D with hB'
  set E := (Lb ⊓ B) ⊔ C with hE
  have hCn : C.Normal := inferInstance
  have hEB' : E ≤ B' :=
    sup_le (le_inf inf_le_right (inf_le_left.trans le_sup_left)) (le_inf hCB le_sup_right)
  have hLE : Lb ⊔ E = D := by
    refine le_antisymm (sup_le le_sup_left (sup_le (inf_le_left.trans le_sup_left) le_sup_right))
      (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have hEnorm : E ≤ Subgroup.normalizer (Lb : Set Q) := le_normalizer_of_normal E
  have hErel : E.relIndex D = (Lb ⊓ B).relIndex Lb := by
    rw [← hLE, relIndex_sup_eq hEnorm, hE, inf_sup_eq_of_inf_eq_bot hLC]
  have hB'D : ¬ 2 ∣ B'.relIndex D := fun h =>
    hodd (hErel ▸ h.trans (Subgroup.relIndex_dvd_of_le_left D hEB'))
  have h1 := Subgroup.relIndex_mul_index (inf_le_right : B' ≤ D)
  have h2 := Subgroup.relIndex_mul_index (inf_le_left : B' ≤ B)
  have hBodd : ¬ 2 ∣ B.index := by
    intro hB2
    have h4 : 4 ∣ B'.relIndex D * D.index := by
      rw [h1, ← h2]
      obtain ⟨a, ha⟩ := heven
      obtain ⟨b, hb⟩ := hB2
      exact ⟨a * b, by rw [ha, hb]; ring⟩
    have hcop : Nat.Coprime 4 (B'.relIndex D) := by
      have : Nat.Coprime 2 (B'.relIndex D) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hB'D
      exact Nat.Coprime.pow_left 2 this
    have h4D : 4 ∣ D.index := hcop.dvd_of_dvd_mul_left h4
    have := h4D.trans hD6
    omega
  refine ⟨le_top, hT.2.1, ?_⟩
  have hTB := hT.2.2
  change ¬ 2 ∣ Tb.relIndex ⊤
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hT.1]
  intro h2'
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2' with h | h
  · exact hTB h
  · exact hBodd h

theorem isSylowTwoOf_top_of_sup_eq_top {Lb B Tb : Subgroup Q} [hLn : Lb.Normal]
    (hLB : Lb ⊔ B = ⊤) (hodd : ¬ 2 ∣ (Lb ⊓ B).relIndex Lb) (hT : IsSylowTwoOf Tb B) :
    IsSylowTwoOf Tb ⊤ := by
  have hBnorm : B ≤ Subgroup.normalizer (Lb : Set Q) := le_normalizer_of_normal B
  have hBidx : B.index = (Lb ⊓ B).relIndex Lb := by
    rw [← relIndex_sup_eq hBnorm, hLB, Subgroup.relIndex_top_right]
  refine ⟨le_top, hT.2.1, ?_⟩
  have hTB := hT.2.2
  change ¬ 2 ∣ Tb.relIndex ⊤
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hT.1, hBidx]
  intro h2'
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2' with h | h
  · exact hTB h
  · exact hodd h

end CFSG.AGLEmbeddingD2.McLaughlin
