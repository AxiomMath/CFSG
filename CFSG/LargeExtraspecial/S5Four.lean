module

public import CFSG.LargeExtraspecial.S5Eight
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem centralizer_eq_bot_or_card_eq_three (H : S4.Hyp4 S g) (hNo : S4.NoA2 S g)
    (C : S4.Cons311 S g) (hn : 4 < S.width) {F : Subgroup S.O} (hFM : F ≤ S.Mbar)
    (hodd : Odd (Nat.card F)) (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    F ⊓ centralizer ({t} : Set S.O) = ⊥ ∨ Nat.card (F ⊓ centralizer ({t} : Set S.O) : _) = 3 := by
  by_cases hbot : F ⊓ centralizer ({t} : Set S.O) = ⊥
  · exact Or.inl hbot
  right
  have hodd' : Odd (Nat.card (F ⊓ centralizer ({t} : Set S.O) : Subgroup S.O)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  rcases timmesfeld_4_8_M H hNo C ht ht1 (inf_le_left.trans hFM) hodd' hbot
      (fun x hx => mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2)
      (fun s hs x hx => conj_mem_inf_centralizer H hnorm ht hs hx)
      (fun x hx hc => eq_one_of_mem_of_commute H hodd' hx hc) with h3 | ⟨-, h8, -⟩
  · exact h3
  · have := sixteen_le_card_Lbar C hn
    omega

theorem conj_eq_self_or_inv_of_card_eq_three (H : S4.Hyp4 S g) {P : Subgroup S.O}
    (hP : Nat.card P = 3) (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ P, s * x * s⁻¹ ∈ P) {c : S.O}
    (hc : c ∈ P) {s : S.O} (hs : s ∈ S.Lbar g) : s * c * s⁻¹ = c ∨ s * c * s⁻¹ = c⁻¹ := by
  by_cases hc1 : c = 1
  · left
    rw [hc1, mul_one, mul_inv_cancel]
  have hord : orderOf c = 3 := by
    have h3 : c ^ 3 = 1 := by
      have := pow_card_eq_one' (G := P) (x := ⟨c, hc⟩)
      rw [hP] at this
      exact congrArg Subtype.val this
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hzP : zpowers c = P := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hc)
    (by rw [Nat.card_zpowers, hord, hP])
  refine conj_eq_self_or_inv (p := 3) (j := 1) Nat.prime_three (by norm_num) (by rw [hord]; rfl)
    (S4.mul_self_of_mem_Lbar S H.conj_mem hs) ?_
  rw [hzP]
  exact hnorm s hs c hc

theorem timmesfeld_5_4 (H : S4.Hyp4 S g) (hNo : S4.NoA2 S g) (C : S4.Cons311 S g)
    (hn : 4 < S.width) {F : Subgroup S.O} (hFM : F ≤ S.Mbar) (hodd : Odd (Nat.card F))
    (hF : F ≠ ⊥) (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ F, s * x * s⁻¹ ∈ F) : Nat.card F = 3 := by
  classical
  have hA2 : ∀ s ∈ S.Lbar g, s * s = 1 := fun s hs => S4.mul_self_of_mem_Lbar S H.conj_mem hs
  have h16 := sixteen_le_card_Lbar C hn
  have hCen : ∀ a ∈ S.Lbar g, a ≠ 1 → F ⊓ centralizer ({a} : Set S.O) = ⊥ ∨
      Nat.card (F ⊓ centralizer ({a} : Set S.O) : Subgroup S.O) = 3 := fun a ha ha1 =>
    centralizer_eq_bot_or_card_eq_three H hNo C hn hFM hodd hnorm ha ha1
  have hinv : ∀ a ∈ S.Lbar g, ∀ s ∈ S.Lbar g, ∀ x ∈ F ⊓ centralizer ({a} : Set S.O),
      s * x * s⁻¹ ∈ F ⊓ centralizer ({a} : Set S.O) := fun a ha s hs x hx =>
    conj_mem_inf_centralizer H hnorm ha hs hx
  have huniq : ∀ a ∈ S.Lbar g, ∀ b ∈ S.Lbar g, a ≠ 1 → b ≠ 1 →
      F ⊓ centralizer ({a} : Set S.O) ≠ ⊥ → F ⊓ centralizer ({b} : Set S.O) ≠ ⊥ →
      F ⊓ centralizer ({a} : Set S.O) = F ⊓ centralizer ({b} : Set S.O) := by
    intro a ha b hb ha1 hb1 haC hbC
    have ha3 := (hCen a ha ha1).resolve_left haC
    have hb3 := (hCen b hb hb1).resolve_left hbC
    obtain ⟨ca, hca1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp haC
    obtain ⟨cb, hcb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbC
    obtain ⟨c, hc, hc1, hcca, hccb⟩ := exists_ne_one_commute_two_of_four_lt hA2 (by omega)
      (fun s hs => conj_eq_self_or_inv_of_card_eq_three H ha3 (hinv a ha) ca.2 hs)
      (fun s hs => conj_eq_self_or_inv_of_card_eq_three H hb3 (hinv b hb) cb.2 hs)
    have hle : ∀ (d : S.O) (P : Subgroup S.O), Nat.card P = 3 → P ≤ F → d ∈ P → d ≠ 1 →
        c * d = d * c → P ≤ F ⊓ centralizer ({c} : Set S.O) := by
      intro d P hP hPF hd hd1 hcd
      have hord : orderOf d = 3 := by
        have h3 : d ^ 3 = 1 := by
          have := pow_card_eq_one' (G := P) (x := ⟨d, hd⟩)
          rw [hP] at this
          exact congrArg Subtype.val this
        rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hd1
        · exact h
      have hzP : zpowers d = P := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hd)
        (by rw [Nat.card_zpowers, hord, hP])
      rw [← hzP]
      refine zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hPF hd, ?_⟩)
      exact mem_centralizer_singleton_iff.mpr hcd.symm
    have hca' : (ca : S.O) ≠ 1 := fun h => hca1 (Subtype.ext h)
    have hcb' : (cb : S.O) ≠ 1 := fun h => hcb1 (Subtype.ext h)
    have hac := hle ca _ ha3 inf_le_left ca.2 hca' hcca
    have hbc := hle cb _ hb3 inf_le_left cb.2 hcb' hccb
    have hcC : F ⊓ centralizer ({c} : Set S.O) ≠ ⊥ := by
      intro h0
      rw [h0] at hac
      exact haC (le_bot_iff.mp hac)
    have hc3 := (hCen c hc hc1).resolve_left hcC
    rw [Subgroup.eq_of_le_of_card_ge hac (by rw [ha3, hc3]),
      Subgroup.eq_of_le_of_card_ge hbc (by rw [hb3, hc3])]
  have hnormF : ∀ s ∈ S.Lbar g, s ∈ normalizer (F : Set S.O) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact hnorm s hs x
    · intro hx
      have := hnorm s⁻¹ (inv_mem hs) _ hx
      simpa [mul_assoc] using this
  have hgen : ∀ u ∈ S.Lbar g, ∀ t ∈ S.Lbar g, u ≠ 1 → t ≠ 1 → u ≠ t →
      F = (F ⊓ centralizer ({u} : Set S.O)) ⊔ (F ⊓ centralizer ({t} : Set S.O)) ⊔
        (F ⊓ centralizer ({u * t} : Set S.O)) := by
    intro u hu t ht hu1 ht1 hut
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine four_group_odd_centralizer_generation F u t
      (orderOf_eq_prime (by rw [pow_two]; exact hA2 u hu) hu1)
      (orderOf_eq_prime (by rw [pow_two]; exact hA2 t ht) ht1)
      (S4.Lbar_comm S H.conj_mem hu ht) hut hodd ?_
    rw [denominatorFourGroup_eq]
    exact sup_le (zpowers_le.mpr (hnormF u hu)) (zpowers_le.mpr (hnormF t ht))
  have hut1 : ∀ u ∈ S.Lbar g, ∀ t ∈ S.Lbar g, u ≠ t → u * t ≠ 1 := by
    intro u hu t ht hut h
    apply hut
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (hA2 t ht)]
  by_cases hex : ∃ a ∈ S.Lbar g, a ≠ 1 ∧ F ⊓ centralizer ({a} : Set S.O) ≠ ⊥
  · obtain ⟨a, ha, ha1, haC⟩ := hex
    have ha3 := (hCen a ha ha1).resolve_left haC
    have hoddC : Odd (Nat.card (F ⊓ centralizer ({a} : Set S.O) : Subgroup S.O)) := by
      rw [ha3]
      decide
    obtain ⟨t, ht, x, hx, htx⟩ : ∃ t ∈ S.Lbar g, ∃ x ∈ F ⊓ centralizer ({a} : Set S.O),
        t * x ≠ x * t := by
      by_contra h
      push Not at h
      apply haC
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (eq_one_of_mem_of_commute H hoddC hx fun s hs => h s hs x hx)
    have hxa : x * a = a * x := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact htx (by rw [one_mul, mul_one])
    have hat : a ≠ t := by
      rintro rfl
      exact htx hxa.symm
    have htC : F ⊓ centralizer ({t} : Set S.O) = ⊥ := by
      by_contra htC
      have heq := huniq t ht a ha ht1 ha1 htC haC
      rw [← heq] at hx
      exact htx (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2).symm
    have hatC : F ⊓ centralizer ({a * t} : Set S.O) = ⊥ := by
      by_contra hatC
      have heq := huniq (a * t) (mul_mem ha ht) a ha (hut1 a ha t ht hat) ha1 hatC haC
      rw [← heq] at hx
      have hxat := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
      apply htx
      calc t * x = a⁻¹ * ((a * t) * x) := by group
        _ = a⁻¹ * (x * (a * t)) := by rw [hxat]
        _ = a⁻¹ * (x * a) * t := by group
        _ = a⁻¹ * (a * x) * t := by rw [hxa]
        _ = x * t := by group
    have hFeq := hgen a ha t ht ha1 ht1 hat
    rw [htC, hatC, sup_bot_eq, sup_bot_eq] at hFeq
    rw [hFeq, ha3]
  · push Not at hex
    exfalso
    obtain ⟨u, hu, t, ht, hu1, ht1, hut⟩ := exists_ne_one_ne_one_ne (A := S.Lbar g) (by omega)
    have hFeq := hgen u hu t ht hu1 ht1 hut
    rw [hex u hu hu1, hex t ht ht1, hex (u * t) (mul_mem hu ht) (hut1 u hu t ht hut),
      sup_bot_eq, sup_bot_eq] at hFeq
    exact hF hFeq

end CFSG.LargeExtraspecial.S5
