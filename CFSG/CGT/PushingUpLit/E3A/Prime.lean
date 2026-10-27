module

public import CFSG.CGT.PushingUpLit.E3A.Alt

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.RankThree.PartOne

theorem card_ne_one {G : Type} [Group G] [Finite G] (R : Subgroup G) :
    Nat.card {y : G | y ∈ R ∧ y ≠ 1} = Nat.card R - 1 := by
  classical
  have e : {y : G | y ∈ R ∧ y ≠ 1} ≃ {y : R // y ≠ 1} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
      invFun := fun z => ⟨z.1.1, z.1.2, fun h => z.2 (Subtype.ext h)⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  have hfin : Fintype {y : R // y ≠ 1} := Fintype.ofFinite _
  have h2 : Nat.card R = Nat.card {y : R // y ≠ 1} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe (1 : R)), Nat.card_eq_fintype_card,
      Fintype.card_option, ← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e]
  omega

theorem false_of_trans_dvd {G : Type} [Group G] [Finite G] {R X : Subgroup G} {p : ℕ}
    (hR : 1 < Nat.card R)
    (htrans : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (R : Set G), g * x * g⁻¹ = y)
    (hp : p ∣ Nat.card R - 1) (hXp : p ∣ Nat.card X) (hG : ¬ p * p ∣ Nat.card G)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) : False := by
  classical
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hN
  have hXN : X ≤ N := hXC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra h
    push Not at h
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 h
    rw [this, Subgroup.card_bot] at hR
    omega
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have horb : MulAction.orbit N r = {y | y ∈ R ∧ y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      show n • r ∈ {y | y ∈ R ∧ y ≠ 1}
      rw [hsmul]
      refine ⟨(Subgroup.mem_normalizer_iff.1 n.2 r).1 hrR, fun h => hr1 ?_⟩
      have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h
      simpa [mul_assoc] using this
    · rintro ⟨hyR, hy1⟩
      obtain ⟨g, hg, hgy⟩ := htrans r hrR hr1 y hyR hy1
      exact ⟨⟨g, hg⟩, by show (⟨g, hg⟩ : N) • r = y; rw [hsmul]; exact hgy⟩
  have hcard_orb : Nat.card (MulAction.orbit N r) = Nat.card R - 1 := by
    rw [horb]
    exact card_ne_one R
  have hX : X.subgroupOf N ≤ MulAction.stabilizer N r := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff, hsmul]
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
    have hc := Subgroup.mem_centralizer_iff.1 (hXC hxX) r hrR
    rw [← hc]
    group
  have hprod := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N r)
  rw [Nat.card_prod] at hprod
  have hdvd1 : p ∣ Nat.card (MulAction.orbit N r) := hcard_orb ▸ hp
  have hdvd2 : p ∣ Nat.card (MulAction.stabilizer N r) := by
    have h1 : Nat.card (X.subgroupOf N) ∣ Nat.card (MulAction.stabilizer N r) :=
      Subgroup.card_dvd_of_le hX
    have h2 : Nat.card (X.subgroupOf N) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv
    rw [h2] at h1
    exact hXp.trans h1
  have hNdvd : p * p ∣ Nat.card N := by
    rw [← hprod]
    exact mul_dvd_mul hdvd1 hdvd2
  exact hG (hNdvd.trans (Subgroup.card_subgroup_dvd_card N))

theorem false_of_order_sixteen {G : Type} [Group G] [Finite G] {R X : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hR : Nat.card R = 16)
    (htrans : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (R : Set G), g * x * g⁻¹ = y)
    (hG : ¬ 25 ∣ Nat.card G) (hnat : IsNaturalAltModule ↥X n)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) : False :=
  false_of_trans_dvd (p := 5) (by omega) htrans (by rw [hR]; norm_num)
    (five_dvd_card_block hn hnat) (by simpa using hG) hXC

end CFSG.CGT.PushingUpLit.E3A
