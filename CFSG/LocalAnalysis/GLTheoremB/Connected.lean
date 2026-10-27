module

public import CFSG.LocalAnalysis.GLTheoremB.PlaneAction

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_elemAbelian_above_plane {p : ℕ} [Fact p.Prime] [Finite G] {P U F : Subgroup G}
    (hP : IsPGroup p P) (hU : IsPPlane p U) (hUP : U ≤ P)
    (hN : P ≤ Subgroup.normalizer (U : Set G)) (hF : IsElemAbelian p F) (hFP : F ≤ P)
    (hF3 : p ^ 3 ≤ Nat.card F) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian p E ∧ U ≤ E ∧ p ^ 3 ≤ Nat.card E := by
  have hp : p.Prime := Fact.out
  have hcard := card_le_mul_card_inf_centralizer hP hU hUP hN hFP
  set F0 : Subgroup G := F ⊓ Subgroup.centralizer (U : Set G) with hF0
  have hF0card : p ^ 2 ≤ Nat.card F0 := by
    have h1 : p * p ^ 2 ≤ p * Nat.card F0 := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card F := hF3
        _ ≤ p * Nat.card F0 := hcard
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hnle : ¬ F0 ≤ U := by
    intro h
    have hUF0 : F0 = U := Subgroup.eq_of_le_of_card_ge h (by rw [hU.2]; exact hF0card)
    have hUF : U ≤ F := hUF0 ▸ inf_le_left
    have hFC : F ≤ Subgroup.centralizer (U : Set G) := fun f hf =>
      Subgroup.mem_centralizer_iff.2 fun u hu => elemAbelian_comm hF (hUF hu) hf
    have hFF0 : F0 = F := inf_eq_left.2 hFC
    have : Nat.card F = p ^ 2 := by rw [← hFF0, hUF0, hU.2]
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨c, hcF0, hcU⟩ : ∃ c ∈ F0, c ∉ U := by
    by_contra h
    exact hnle fun x hx => by_contra fun hx' => h ⟨x, hx, hx'⟩
  have hcF : c ∈ F := (inf_le_left : F0 ≤ F) hcF0
  have hcC : c ∈ Subgroup.centralizer (U : Set G) := (inf_le_right : F0 ≤ _) hcF0
  have hzF : Subgroup.zpowers c ≤ F := (Subgroup.zpowers_le).2 hcF
  have hzC : Subgroup.zpowers c ≤ Subgroup.centralizer (U : Set G) := (Subgroup.zpowers_le).2 hcC
  refine ⟨U ⊔ Subgroup.zpowers c, sup_le hUP (hzF.trans hFP), ?_, le_sup_left, ?_⟩
  · exact isElemAbelian_sup_of_commute hU.1 (isElemAbelian_mono hF hzF)
      (Subgroup.le_centralizer_iff.1 hzC)
  · have hEP : U ⊔ Subgroup.zpowers c ≤ P := sup_le hUP (hzF.trans hFP)
    obtain ⟨k, hk⟩ := exists_card_eq_pow (hP.to_le hEP)
    have hdvd : p ^ 2 ∣ p ^ k := hk ▸ hU.2 ▸ Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ _)
    have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
    have hne : k ≠ 2 := by
      rintro rfl
      have := Subgroup.eq_of_le_of_card_ge (le_sup_left : U ≤ U ⊔ Subgroup.zpowers c)
        (by rw [hk, hU.2])
      exact hcU (this ▸ (le_sup_right : Subgroup.zpowers c ≤ U ⊔ _) (Subgroup.mem_zpowers c))
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)

theorem isTwoConnectedIn_of_rank_three {p : ℕ} [Fact p.Prime] [Finite G] {P U E : Subgroup G}
    (hP : IsPGroup p P) (hU : IsPPlane p U) (hUP : U ≤ P)
    (hN : P ≤ Subgroup.normalizer (U : Set G)) (hE : IsElemAbelian p E) (hEP : E ≤ P)
    (hE3 : p ^ 3 ≤ Nat.card E) : IsTwoConnectedIn p P E U := by
  have hp : p.Prime := Fact.out
  have hcard := card_le_mul_card_inf_centralizer hP hU hUP hN hEP
  set F0 : Subgroup G := E ⊓ Subgroup.centralizer (U : Set G) with hF0
  have hF0card : p ^ 2 ≤ Nat.card F0 := by
    have h1 : p * p ^ 2 ≤ p * Nat.card F0 := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card E := hE3
        _ ≤ p * Nat.card F0 := hcard
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hF0el : IsElemAbelian p F0 := isElemAbelian_mono hE inf_le_left
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card F0 = p ^ k :=
    exists_card_eq_pow (hP.to_le (inf_le_left.trans hEP : F0 ≤ P))
  have hk2 : 2 ≤ k := by
    by_contra h
    have : p ^ k < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  obtain ⟨D, hDF0, hDel, hDcard⟩ := exists_le_isElemAbelian_card hF0el (n := 2)
    (hk ▸ pow_dvd_pow p hk2)
  have hDE : D ≤ E := hDF0.trans inf_le_left
  have hDC : D ≤ Subgroup.centralizer (U : Set G) := hDF0.trans inf_le_right
  have hEnc : IsNoncyclicElemAbelianIn p P E :=
    ⟨hEP, hE, not_isCyclic_of_isElemAbelian hE (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num))
      hE3)⟩
  have hDnc : IsNoncyclicElemAbelianIn p P D :=
    ⟨hDE.trans hEP, hDel, not_isCyclic_of_isElemAbelian hDel (hDcard ▸ le_rfl)⟩
  have hUnc : IsNoncyclicElemAbelianIn p P U :=
    ⟨hUP, hU.1, not_isCyclic_of_isElemAbelian hU.1 (hU.2 ▸ le_rfl)⟩
  refine ⟨hEnc, hUnc, Relation.ReflTransGen.tail (Relation.ReflTransGen.single
    ⟨hEnc, hDnc, fun e he => Subgroup.mem_centralizer_iff.2 fun d hd =>
      elemAbelian_comm hE (hDE hd) he⟩) ⟨hDnc, hUnc, hDC⟩⟩

theorem isTwoConnectedIn_of_rank_three' {p : ℕ} [Fact p.Prime] [Finite G] {P U E E' : Subgroup G}
    (hP : IsPGroup p P) (hU : IsPPlane p U) (hUP : U ≤ P)
    (hN : P ≤ Subgroup.normalizer (U : Set G)) (hE : IsElemAbelian p E) (hEP : E ≤ P)
    (hE3 : p ^ 3 ≤ Nat.card E) (hE' : IsElemAbelian p E') (hEP' : E' ≤ P)
    (hE3' : p ^ 3 ≤ Nat.card E') : IsTwoConnectedIn p P E E' :=
  (isTwoConnectedIn_of_rank_three hP hU hUP hN hE hEP hE3).trans'
    (isTwoConnectedIn_of_rank_three hP hU hUP hN hE' hEP' hE3').symm'

end CFSG.LocalAnalysis.GLTheoremB
