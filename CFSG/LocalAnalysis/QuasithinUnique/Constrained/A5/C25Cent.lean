module

public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem eq_bot_of_exponent_three_of_not_dvd {Y : Type*} [Group Y] {F E : Subgroup Y}
    (hF : ¬ 3 ∣ Nat.card F) (hEF : E ≤ F) (hE : ∀ e ∈ E, e ^ 3 = 1) : E = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro e he
  by_contra h1
  have h1' : e ≠ 1 := fun h => h1 ((Subgroup.mem_bot).2 h)
  have hord : orderOf e = 3 := orderOf_eq_prime (hE e he) h1'
  have := Subgroup.orderOf_dvd_natCard F (hEF he)
  rw [hord] at this
  exact hF this

theorem false_of_center_eq_top_of_perfect {Y : Type*} [Group Y] [Nontrivial Y] [Group.IsPerfect Y]
    (h : Subgroup.center Y = ⊤) : False := by
  have h1 : commutator Y = ⊥ := (commutator_eq_bot_iff_center_eq_top Y).2 h
  have h2 : commutator Y = ⊤ := Group.isPerfect_def.1 inferInstance
  obtain ⟨a, ha⟩ := exists_ne (1 : Y)
  have : a ∈ commutator Y := by rw [h2]; exact Subgroup.mem_top a
  rw [h1, Subgroup.mem_bot] at this
  exact ha this

theorem card_multiplicative_fin_zmod (p n : ℕ) [Fact p.Prime] :
    Nat.card (Multiplicative (Fin n → ZMod p)) = p ^ n := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_multiplicative, ZMod.card]

theorem card_le_three_of_central_elemAbelian (h36 : A36ForSQTKCat) {Q : Type} [Group Q]
    (hQ : SQTKHypCat Q) {K : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q)) {E : Subgroup Q}
    (hEK : E ≤ K) (hcen : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 := by
  have : Finite Q := hQ.finite
  obtain ⟨hconc, -, -⟩ := h36 Q hQ K hK
  have hcard : Nat.card (E.subgroupOf K) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hEc : E.subgroupOf K ≤ Subgroup.center ↥K := fun e he =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcen (e : Q) he g g.2).symm
  have hE3 : ∀ e ∈ E.subgroupOf K, e ^ 3 = 1 := fun e he => Subtype.ext (hE.2 (e : Q) he)
  rw [← hcard]
  have hbot : ¬ 3 ∣ Nat.card (CFSG.fittingSubgroup ↥K) → Nat.card (E.subgroupOf K) ≤ 3 := fun hF => by
    have hb : E.subgroupOf K = ⊥ :=
      eq_bot_of_exponent_three_of_not_dvd hF (hEc.trans A36A.center_le_fittingSubgroup) hE3
    rw [hb, Subgroup.card_bot]
    norm_num
  rcases hconc with ⟨-, hsimple, -⟩ | ⟨-, hZ3, -⟩ | h3 | h4
  ·
    have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · have hb : E.subgroupOf K = ⊥ := le_bot_iff.1 (h ▸ hEc)
      rw [hb, Subgroup.card_bot]
      norm_num
    · exact (false_of_center_eq_top_of_perfect h).elim
  ·
    calc Nat.card (E.subgroupOf K) ≤ Nat.card (Subgroup.center ↥K) := Subgroup.card_le_of_le hEc
      _ = 3 := hZ3
  ·
    obtain ⟨p, hp, hp3, -, ⟨ψ⟩, -⟩ := h3
    have : Fact p.Prime := ⟨hp⟩
    refine hbot fun hdvd => ?_
    have hF : Nat.card (CFSG.fittingSubgroup ↥K) = p ^ 2 :=
      (Nat.card_congr ψ.toEquiv).trans (card_multiplicative_fin_zmod p 2)
    rw [hF] at hdvd
    have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p
    omega
  ·
    obtain ⟨-, -, -, hF⟩ := h4
    refine hbot fun hdvd => ?_
    have := (hF 3 Nat.prime_three hdvd).1
    omega

end CFSG.QuasithinUnique.A5.C25
