module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44DataComp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44DataModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup U44Data
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

theorem u44_u2_aux {K : Type} [Group K] [Finite K] {Q : Subgroup K} (M : TorusModel K Q) {x : K}
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) {Ja Jb : Subgroup K} (hne : Ja ≠ Jb)
    (hJa : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) Ja)
    (hJb : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) Jb)
    (hAa : Nonempty (↥Ja ⧸ primeComplementCore (G := ↥Ja) 5 ≃* alternatingGroup (Fin 5)))
    (hAb : Nonempty (↥Jb ⧸ primeComplementCore (G := ↥Jb) 5 ≃* alternatingGroup (Fin 5)))
    (h9 : 9 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set K))) {a : K} (haQ : a ∈ Q) (haJ : a ∈ Ja)
    (ha1 : a ≠ 1) (φ : MulAut K) (hφ : φ x ∈ Subgroup.zpowers a) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ha5 : a ^ 5 = 1 := M.pow_five_of_mem haQ
  have hx5 : x ^ 5 = 1 := M.pow_five_of_mem hxQ
  have hzx : Subgroup.zpowers x ≠ Subgroup.zpowers a := by
    intro h
    exact not_mem_zpowers_of_mem_component hJa hAa haJ ha1 ha5 (h ▸ Subgroup.mem_zpowers a)
  have hox : orderOf (φ x) = 5 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hx5 hx1
  have hoa : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  have hzz : Subgroup.zpowers (φ x) = Subgroup.zpowers a := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hφ) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoa]
  have ha_mem : a ∈ Subgroup.zpowers (φ x) := hzz ▸ Subgroup.mem_zpowers a
  have hCa : Subgroup.centralizer ({a} : Set K) = Subgroup.centralizer ({φ x} : Set K) := by
    ext g
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hφ
      rw [← hl]
      exact ((Commute.zpow_right (show Commute g a from h) l).eq)
    · intro h
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp ha_mem
      rw [← hl]
      exact ((Commute.zpow_right (show Commute g (φ x) from h) l).eq)
  have h9a : 9 ∣ Nat.card ↥(Subgroup.centralizer ({a} : Set K)) := by
    rw [hCa, card_centralizer_singleton_mulEquiv φ x]
    exact h9
  have hle := M.inf_centralizer_le hxQ haQ hx1 ha1 h9 h9a hzx
  have h125 : Nat.card ↥(Subgroup.centralizer ({x} : Set K) ⊓ Subgroup.centralizer ({a} : Set K)) ∣
      5 ^ 3 := M.card_Q ▸ Subgroup.card_dvd_of_le hle
  have h60 := sixty_dvd_card_inf_centralizer hJa hJb hne hAb haJ ha5
  have := h60.trans h125
  norm_num at this

theorem kFactU44Data_holds : KFactU44Data := by
  intro K _ _ ⟨e⟩ Q x hxQ hx1 hx5 J₁ J₂ hne hJ₁ hJ₂ _ hA₁ hA₂
  obtain ⟨M⟩ := exists_torusModel e Q
  have h9 : 9 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set K)) :=
    nine_dvd_card_of_two_components hJ₁ hJ₂ hne hA₁ hA₂
  refine ⟨M.ncard_conj_lines hxQ hx1 h9, ?_⟩
  intro J hJ a ha ha1 φ hφ
  obtain ⟨haQ, haJ⟩ := Subgroup.mem_inf.mp ha
  rcases hJ with rfl | rfl
  · exact u44_u2_aux M hxQ hx1 hne hJ₁ hJ₂ hA₁ hA₂ h9 haQ haJ ha1 φ hφ
  · exact u44_u2_aux M hxQ hx1 hne.symm hJ₂ hJ₁ hA₂ hA₁ h9 haQ haJ ha1 φ hφ

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
