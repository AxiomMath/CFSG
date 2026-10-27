module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentF
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
  CFSG.GH74.GLS.Stage2.Final.Thm4.L193
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (Op_le Op_Fm_eq Fm_le_of_forall)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L20 (Fm_isNilpotent odd_orderOf_of_mem_pPrimeCoreOf Op_conj_mem)

section Z

variable {G : Type} [Group G] [Finite G]

theorem odd_card_F20 (z : G) : Odd (Nat.card ↥(F20 z)) := by
  have h1 : Nat.card ↥(F20 z) ∣ Nat.card ↥(OddCore z) :=
    Subgroup.card_dvd_of_le (F20_le_OddCore z)
  have h2 : Nat.Coprime 2 (Nat.card ↥(OddCore z)) :=
    CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 2 (Cen z)
  exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right h1 h2)

theorem exists_Z20 (z : G) {r : ℕ} (hr : r.Prime) (hrF : r ∣ Nat.card ↥(F20 z)) (hz2 : orderOf z = 2)
    (hM : IsCoatom (Cen z)) (hGs : IsSimpleGroup G) :
    ∃ Z : Subgroup G, IsPGroup r ↥Z ∧ Z ≠ ⊥ ∧ Z ≤ F20 z ∧ (∀ f ∈ F20 z, ∀ w ∈ Z, f * w = w * f) ∧
      (∀ c ∈ Cen z, ∀ w ∈ Z, c * w * c⁻¹ ∈ Z) ∧ (∀ g ∈ normalizer (Z : Set G), g ∈ Cen z) := by
  classical
  have hfact : Fact r.Prime := ⟨hr⟩
  have hFnil : Group.IsNilpotent ↥(F20 z) := Fm_isNilpotent (OddCore z)
  have hFodd : Odd (Nat.card ↥(F20 z)) := odd_card_F20 z
  have hrodd : Odd r := Odd.of_dvd_nat hFodd hrF
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd hrodd (by decide)
  have hFnorm : ∀ c ∈ Cen z, ∀ b ∈ F20 z, c * b * c⁻¹ ∈ F20 z := fun c hc b hb => F20_conj_mem z hc hb
  set P : Subgroup G := Op r (F20 z) with hP
  have hPp : IsPGroup r ↥P := L20.isPGroup_Op r (F20 z)
  obtain ⟨e', he'⟩ : ∃ e : ↥(F20 z), orderOf e = r := by
    have : Fintype ↥(F20 z) := Fintype.ofFinite _
    exact exists_prime_orderOf_dvd_card r (by rwa [← Nat.card_eq_fintype_card])
  have heP : (e' : G) ∈ P :=
    L20.mem_Op_of_orderOf_prime hFnil e'.2 (by rw [Subgroup.orderOf_coe]; exact he')
  have hPnt : Nontrivial ↥P := by
    refine ⟨⟨⟨e', heP⟩, 1, fun h => ?_⟩⟩
    have h2 : (e' : G) = 1 := congrArg Subtype.val h
    have : e' = 1 := Subtype.ext h2
    rw [this, orderOf_one] at he'
    exact hr.one_lt.ne he'
  have hcn : Nontrivial ↥(center ↥P) := hPp.center_nontrivial
  set Z : Subgroup G := (center ↥P).map P.subtype with hZ
  have hZP : ∀ w ∈ Z, w ∈ P := fun w hw => by
    obtain ⟨p, -, rfl⟩ := hw; exact p.2
  have hZc : ∀ w ∈ Z, ∀ x ∈ P, w * x = x * w := by
    intro w hw x hx
    obtain ⟨p, hp, rfl⟩ := hw
    have := Subgroup.mem_center_iff.1 hp ⟨x, hx⟩
    exact congrArg Subtype.val this.symm
  have hZmem : ∀ w ∈ P, (∀ x ∈ P, w * x = x * w) → w ∈ Z := by
    intro w hw hc
    refine ⟨⟨w, hw⟩, Subgroup.mem_center_iff.2 fun x => ?_, rfl⟩
    exact Subtype.ext (hc x x.2).symm
  have hZnorm : ∀ c ∈ Cen z, ∀ w ∈ Z, c * w * c⁻¹ ∈ Z := by
    intro c hc w hw
    have hcw : c * w * c⁻¹ ∈ P := Op_conj_mem r hFnorm hc (hZP w hw)
    refine hZmem _ hcw fun x hx => ?_
    have hx' : c⁻¹ * x * c⁻¹⁻¹ ∈ P := Op_conj_mem r hFnorm ((Cen z).inv_mem hc) hx
    have h1 := hZc w hw _ hx'
    calc c * w * c⁻¹ * x = c * (w * (c⁻¹ * x * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * x * c) * w) * c⁻¹ := by
          have e : c⁻¹ * x * c = c⁻¹ * x * c⁻¹⁻¹ := by group
          rw [e, h1]
      _ = x * (c * w * c⁻¹) := by group
  have hZle : Z ≤ P := fun w hw => hZP w hw
  have hZne : Z ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨p, hp⟩, hp1⟩ := exists_ne (1 : ↥(center ↥P))
    have hpZ : (p : G) ∈ Z := ⟨p, hp, rfl⟩
    rw [hbot] at hpZ
    apply hp1
    have : (p : G) = 1 := (Subgroup.mem_bot).1 hpZ
    exact Subtype.ext (Subtype.ext this)
  have hZF : ∀ f ∈ F20 z, ∀ w ∈ Z, f * w = w * f := by
    intro f hf w hw
    have := commute_of_part hFnil (le_refl (F20 z)) (q := r) (d := w) (hZP w hw)
      (fun x hx => hZc w hw x hx.2) f hf
    exact this.symm
  have hCN : Cen z ≤ normalizer (Z : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact fun hm => hZnorm c hc m hm
    · intro hm
      have h1 := hZnorm c⁻¹ ((Cen z).inv_mem hc) _ hm
      have e : c⁻¹ * (c * m * c⁻¹) * c⁻¹⁻¹ = m := by group
      rwa [e] at h1
  have hNne : normalizer (Z : Set G) ≠ ⊤ := by
    intro htop
    have hnormal : Z.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases hGs.eq_bot_or_eq_top_of_normal Z with h0 | h1
    · exact hZne h0
    ·
      have hGp : IsPGroup r G := by
        intro g
        have hg : g ∈ Z := by rw [h1]; trivial
        obtain ⟨k, hk⟩ := IsPGroup.to_le hPp hZle ⟨g, hg⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      obtain ⟨k, hk⟩ := hGp z
      have hdvd : orderOf z ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
      rw [hz2] at hdvd
      have : 2 ∣ r ^ k := hdvd
      have h2 : 2 ∣ r := (Nat.prime_two.dvd_of_dvd_pow this)
      exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h2).symm
  refine ⟨Z, IsPGroup.to_le hPp hZle, hZne, hZle.trans (Op_le r _), hZF, hZnorm, ?_⟩
  intro g hg
  have hle : Cen z ≤ normalizer (Z : Set G) := hCN
  rcases hM.le_iff.1 hle with h | h
  · exact absurd h hNne
  · rw [← h]; exact hg

end Z

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
