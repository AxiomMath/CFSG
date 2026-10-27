module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Setup

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

theorem card_centralizer_L1 (S : Setup L z t F L1 N) (hR : RankFour L)
    (hnc : ∀ x ∈ L1, ¬ IsConj z x) {y : G} (hyX : y ∈ normalizer (L1 : Set G))
    (hy2 : y * y = 1) (hconj : IsConj z y) :
    ∃ Cy : Subgroup G, (∀ c, c ∈ Cy ↔ c ∈ L1 ∧ y * c * y⁻¹ = c) ∧ Nat.card Cy = 16 ∧
      ∀ m ∈ L1, y * m * y⁻¹ = m → ∃ l ∈ L1, m = l * (y * l * y⁻¹) := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyn : ∀ l ∈ L1, y * l * y⁻¹ ∈ L1 := fun l hl =>
    (Subgroup.mem_normalizer_iff.1 hyX l).1 hl
  have hcomm := S.L1_comm
  have hsq := S.L1_sq
  have hδmem : ∀ l ∈ L1, l * (y * l * y⁻¹) ∈ L1 := fun l hl =>
    Subgroup.mul_mem _ hl (hyn l hl)
  let δ : ↥L1 →* ↥L1 := MonoidHom.mk' (fun l => ⟨l * (y * l * y⁻¹), hδmem l l.2⟩) (by
    intro a b
    apply Subtype.ext
    have h1 : (y * (a : G) * y⁻¹) * (b : G) = (b : G) * (y * (a : G) * y⁻¹) :=
      hcomm _ (hyn a a.2) _ b.2
    show (a : G) * (b : G) * (y * ((a : G) * (b : G)) * y⁻¹) =
      (a : G) * (y * (a : G) * y⁻¹) * ((b : G) * (y * (b : G) * y⁻¹))
    calc (a : G) * (b : G) * (y * ((a : G) * (b : G)) * y⁻¹)
        = (a : G) * ((b : G) * (y * (a : G) * y⁻¹)) * (y * (b : G) * y⁻¹) := by group
      _ = (a : G) * ((y * (a : G) * y⁻¹) * (b : G)) * (y * (b : G) * y⁻¹) := by rw [← h1]
      _ = _ := by group)
  have hδ : ∀ l : ↥L1, ((δ l : ↥L1) : G) = (l : G) * (y * (l : G) * y⁻¹) := fun l => rfl
  have hker : ∀ l : ↥L1, l ∈ δ.ker ↔ y * (l : G) * y⁻¹ = (l : G) := by
    intro l
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (l : G) * (y * (l : G) * y⁻¹) = 1 := by
        have := congrArg Subtype.val h
        rwa [hδ] at this
      have h2 : y * (l : G) * y⁻¹ = (l : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (hsq l l.2)
    · intro h
      apply Subtype.ext
      rw [hδ, h]
      exact hsq l l.2
  have hrange : δ.range ≤ δ.ker := by
    rintro _ ⟨l, rfl⟩
    rw [hker]
    rw [hδ]
    have h1 : (y * (l : G) * y⁻¹) * (l : G) = (l : G) * (y * (l : G) * y⁻¹) :=
      hcomm _ (hyn l l.2) _ l.2
    have hyy' : y⁻¹ * y⁻¹ = 1 := by rw [hyi, hy2]
    calc y * ((l : G) * (y * (l : G) * y⁻¹)) * y⁻¹
        = (y * (l : G) * y⁻¹) * ((y * y) * (l : G) * (y⁻¹ * y⁻¹)) := by group
      _ = (y * (l : G) * y⁻¹) * (l : G) := by rw [hy2, hyy']; group
      _ = _ := h1
  set Cy : Subgroup G := δ.ker.map L1.subtype with hCy
  have hCymem : ∀ c, c ∈ Cy ↔ c ∈ L1 ∧ y * c * y⁻¹ = c := by
    intro c
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.2, (hker l).1 hl⟩
    · rintro ⟨hc, hyc⟩
      exact ⟨⟨c, hc⟩, (hker ⟨c, hc⟩).2 hyc, rfl⟩
  have hCycard : Nat.card Cy = Nat.card δ.ker :=
    Subgroup.card_map_of_injective L1.subtype_injective
  have hyL1 : y ∉ L1 := fun h => hnc y h hconj
  have hy1 : y ≠ 1 := fun h => hyL1 (h ▸ L1.one_mem)
  have hyC : ∀ c ∈ Cy, y * c = c * y := fun c hc => by
    have := ((hCymem c).1 hc).2
    calc y * c = (y * c * y⁻¹) * y := by group
      _ = c * y := by rw [this]
  have hCyL : Cy ≤ L1 := fun c hc => ((hCymem c).1 hc).1
  have hzc : zpowers y ≤ centralizer (Cy : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_centralizer_iff.2 fun c hc => (hyC c hc).symm
  have hbb : ∀ b ∈ zpowers y, b = 1 ∨ b = y := fun b hb => mem_zpowers_involution hy2 hb
  have hCyc : ∀ a ∈ Cy, ∀ a' ∈ Cy, a * a' = a' * a := fun a ha a' ha' =>
    hcomm a (hCyL ha) a' (hCyL ha')
  have hCys : ∀ a ∈ Cy, a * a = 1 := fun a ha => hsq a (hCyL ha)
  have hbc : ∀ b ∈ zpowers y, ∀ a ∈ Cy, a * b = b * a := fun b hb a ha =>
    mem_centralizer_iff.1 (hzc hb) a ha
  have hbcom : ∀ b ∈ zpowers y, ∀ b' ∈ zpowers y, b * b' = b' * b := fun b hb b' hb' => by
    rcases hbb b hb with rfl | rfl <;> rcases hbb b' hb' with rfl | rfl <;> simp
  have hbsq : ∀ b ∈ zpowers y, b * b = 1 := fun b hb => by
    rcases hbb b hb with rfl | rfl
    · simp
    · exact hy2
  have hAc : ∀ x ∈ Cy ⊔ zpowers y, ∀ x' ∈ Cy ⊔ zpowers y, x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc hx
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc hx'
    calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
      _ = a * (a' * b) * b' := by rw [hbc b hb a' ha']
      _ = (a * a') * (b * b') := by simp only [mul_assoc]
      _ = (a' * a) * (b' * b) := by rw [hCyc a ha a' ha', hbcom b hb b' hb']
      _ = a' * (a * b') * b := by simp only [mul_assoc]
      _ = a' * (b' * a) * b := by rw [hbc b' hb' a ha]
      _ = a' * b' * (a * b) := by simp only [mul_assoc]
  have hAs : ∀ x ∈ Cy ⊔ zpowers y, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzc hx
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hbc b hb a ha]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [hCys a ha, hbsq b hb, mul_one]
  have hdisj : Disjoint Cy (zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro x hxC hxy
    rcases hbb x hxy with rfl | rfl
    · rfl
    · exact absurd (hCyL hxC) hyL1
  have hzy : Nat.card (zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hAcard : Nat.card (Cy ⊔ zpowers y : Subgroup G) = Nat.card Cy * 2 := by
    rw [← Nat.card_congr (mulEquivProdSup hzc hdisj).toEquiv, Nat.card_prod, hzy]
  have hyA : y ∈ Cy ⊔ zpowers y := Subgroup.mem_sup_right (mem_zpowers y)
  have hCyle : Nat.card Cy ≤ 16 := by
    by_contra hcon
    push Not at hcon
    exact not_isConj_of_elemAb S.one hR hAc hAs (by rw [hAcard]; omega) hyA hconj
  have hLcard : Nat.card ↥L1 = 256 := S.L1_card
  have hprod := Subgroup.card_ker_mul_card_range δ
  rw [hLcard] at hprod
  have hrk : Nat.card δ.range ≤ Nat.card δ.ker := Subgroup.card_le_of_le hrange
  have hkerC : Nat.card δ.ker = Nat.card Cy := hCycard.symm
  have hk16 : Nat.card δ.ker = 16 := by
    have h1 : Nat.card δ.ker ≤ 16 := hkerC ▸ hCyle
    nlinarith
  have hrng : δ.range = δ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hrange ?_
    have : Nat.card δ.range = 16 := by rw [hk16] at hprod; omega
    omega
  refine ⟨Cy, hCymem, hkerC ▸ hk16, fun m hm hym => ?_⟩
  have hmk : (⟨m, hm⟩ : ↥L1) ∈ δ.ker := (hker ⟨m, hm⟩).2 hym
  rw [← hrng] at hmk
  obtain ⟨l, hl⟩ := hmk
  refine ⟨l, l.2, ?_⟩
  have := congrArg Subtype.val hl
  rw [hδ] at this
  exact this.symm

end CFSG.EvenSporadicStandard.M22Std
