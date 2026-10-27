module

public import CFSG.LargeExtraspecial.S10EightK
public import CFSG.LargeExtraspecial.S10EightI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem index_le_ncard {X : Type*} [Group X] (C : Subgroup X) (y d : X)
    {T : Set (X × X)} (hTfin : T.Finite)
    (hT : ∀ c ∈ C, (c * y * c⁻¹, c * d * c⁻¹) ∈ T) :
    ((centralizer {y} ⊓ centralizer {d} : Subgroup X).subgroupOf C).index ≤ T.ncard := by
  set H := (centralizer {y} ⊓ centralizer {d} : Subgroup X).subgroupOf C with hH
  have hf : ∀ a b : C, ((a : X) * y * (a : X)⁻¹, (a : X) * d * (a : X)⁻¹) =
      ((b : X) * y * (b : X)⁻¹, (b : X) * d * (b : X)⁻¹) ↔ a⁻¹ * b ∈ H := by
    intro a b
    rw [hH, mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff, Prod.mk.injEq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · exact (calc y * ((a : X)⁻¹ * b) = (a : X)⁻¹ * ((a : X) * y * (a : X)⁻¹) * b := by group
          _ = (a : X)⁻¹ * ((b : X) * y * (b : X)⁻¹) * b := by rw [h1]
          _ = (a : X)⁻¹ * b * y := by group).symm
      · exact (calc d * ((a : X)⁻¹ * b) = (a : X)⁻¹ * ((a : X) * d * (a : X)⁻¹) * b := by group
          _ = (a : X)⁻¹ * ((b : X) * d * (b : X)⁻¹) * b := by rw [h2]
          _ = (a : X)⁻¹ * b * d := by group).symm
    · rintro ⟨h1, h2⟩
      constructor
      · calc (a : X) * y * (a : X)⁻¹ = (a : X) * (y * ((a : X)⁻¹ * b)) * (b : X)⁻¹ := by group
          _ = (a : X) * ((a : X)⁻¹ * b * y) * (b : X)⁻¹ := by rw [← h1]
          _ = (b : X) * y * (b : X)⁻¹ := by group
      · calc (a : X) * d * (a : X)⁻¹ = (a : X) * (d * ((a : X)⁻¹ * b)) * (b : X)⁻¹ := by group
          _ = (a : X) * ((a : X)⁻¹ * b * d) * (b : X)⁻¹ := by rw [← h2]
          _ = (b : X) * d * (b : X)⁻¹ := by group
  let f : C → T := fun c => ⟨((c : X) * y * (c : X)⁻¹, (c : X) * d * (c : X)⁻¹), hT c c.2⟩
  let φ : C ⧸ H → T := Quotient.lift f fun a b hab => by
    have := (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
    exact Subtype.ext this
  have hφ : Function.Injective φ := by
    intro x z
    induction x using QuotientGroup.induction_on
    induction z using QuotientGroup.induction_on
    intro h
    exact QuotientGroup.eq.mpr ((hf _ _).mp (congrArg Subtype.val h))
  have : Finite T := hTfin.to_subtype
  calc H.index = Nat.card (C ⧸ H) := rfl
    _ ≤ Nat.card T := Nat.card_le_card_of_injective φ hφ
    _ = T.ncard := Nat.card_coe_set_eq T

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem false_of_inf_eq_bot (hCE : CentralExtInput.{u}) (h7 : 7 ≤ S.width) {k : S.M}
    (hcomm : ∀ c ∈ (S.Lbar g ⊓ Xb).map (cK S k), ∀ e ∈ S.Lbar g ⊓ Xb, c * e = e * c)
    (hinf : (S.Lbar g ⊓ Xb).map (cK S k) ⊓ (S.Lbar g ⊓ Xb) = ⊥) : False := by
  set E := S.Lbar g ⊓ Xb with hE
  set C := E.map (cK S k) with hC
  obtain ⟨F, hFY, hFX, y, hyY, hyL, hπy⟩ := D.exists_frame hCE
  obtain ⟨⟨d, hdY'⟩, hd1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hd1 : d ≠ 1 := fun h => hd1' (Subtype.ext h)
  have hCρ : ∀ c ∈ C, ∃ kc : S.M, S.ρ kc = c := fun c hc =>
    MonoidHom.mem_range.mp (S.Lbar_le_Mbar _ (map_le_Lbar_mul (g := g) (Xb := Xb) k hc))
  have hCt : ∀ c ∈ C, c * t = t * c := fun c hc => hcomm c hc t (D.t_mem_Ebar hCE)
  have hCX : ∀ c ∈ C, ∀ x ∈ Xb, c * x * c⁻¹ ∈ Xb := by
    intro c hc x hx
    obtain ⟨kc, rfl⟩ := hCρ c hc
    exact D.conj_mem_Xb hCE (hCt _ hc) (hcomm _ hc) hx
  have hCd : ∀ c ∈ C, c * d * c⁻¹ = d ∨ c * d * c⁻¹ = d * d := by
    intro c hc
    obtain ⟨kc, rfl⟩ := hCρ c hc
    rcases D.dec.eq_of_mem_commutator hdY' hd1
      (D.conj_mem_commutator_of_commute hCE (hCt _ hc) hdY') with h | h | h
    · exfalso
      apply hd1
      calc d = (S.ρ kc)⁻¹ * (S.ρ kc * d * (S.ρ kc)⁻¹) * S.ρ kc := by group
        _ = 1 := by rw [h]; group
    · exact Or.inl h
    · exact Or.inr h
  have hCy : ∀ c ∈ C, c * y * c⁻¹ ∈ zpowers t ⊔ Yb := by
    intro c hc
    obtain ⟨kc, rfl⟩ := hCρ c hc
    refine D.conj_y_mem hCE hdY' hd1 (hCt _ hc) (hcomm _ hc) (fun x hx => ?_) hyY hyL
    have := hCX _ (inv_mem hc) x hx
    simpa using this
  set T : Set (S.O × S.O) := ((zpowers t ⊔ Yb : Subgroup S.O) : Set S.O) ×ˢ
    ({d, d * d} : Set S.O) with hT
  have hTmem : ∀ c ∈ C, (c * y * c⁻¹, c * d * c⁻¹) ∈ T := fun c hc => by
    refine ⟨hCy c hc, ?_⟩
    rcases hCd c hc with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hncard : T.ncard ≤ 24 := by
    rw [hT, Set.ncard_prod]
    have h1 : ((zpowers t ⊔ Yb : Subgroup S.O) : Set S.O).ncard ≤ 12 := by
      rw [← Nat.card_coe_set_eq]
      exact D.card_zpowers_sup_Yb_le hCE
    have h2 : ({d, d * d} : Set S.O).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    nlinarith
  set H := (centralizer {y} ⊓ centralizer {d} : Subgroup S.O).subgroupOf C with hH
  have hidx : H.index ≤ T.ncard := index_le_ncard C y d (Set.toFinite _) hTmem
  have hcard : Nat.card C = 2 ^ (S.width - 2) := by
    rw [hC, Subgroup.card_map_of_injective (cK_injective k)]
    exact D.card_Ebar hCE h7
  have hmul := Subgroup.card_mul_index H
  rw [hcard] at hmul
  have hdvd : H.index ∣ 2 ^ (S.width - 2) := Dvd.intro_left _ hmul
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj4 : j ≤ 4 := by
    by_contra hcon
    have : 2 ^ 5 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hstab : 1 < Nat.card H := by
    by_contra hcon
    push Not at hcon
    rw [hjeq] at hmul
    have h1 : Nat.card H * 2 ^ j ≤ 1 * 2 ^ 4 :=
      Nat.mul_le_mul hcon (Nat.pow_le_pow_right (by norm_num) hj4)
    have h2 : 2 ^ 5 ≤ 2 ^ (S.width - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp hstab)
  rw [hH, mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff] at hc
  have hcy' : (c : S.O) * y = y * c := hc.1
  have hcd' : (c : S.O) * d = d * c := hc.2
  have hcL : ∀ l ∈ S.Lbar g, (c : S.O) * l = l * c := by
    intro l hl
    have hlR := Lbar_le_Rbar X.ht hl
    have hyR := Lbar_le_Rbar X.ht hyL
    rcases stab_mem_Γ₁_or _ (F.π_mem_stabA hl) with h | h
    · have hlX : l ∈ Xb := by
        rw [hFX]
        exact (F.mem_pre).mpr ⟨hlR, mem_Γ₁.mpr h⟩
      exact hcomm _ c.2 l ⟨hl, hlX⟩
    · have hlyX : l * y ∈ Xb := by
        rw [hFX]
        refine (F.mem_pre).mpr ⟨mul_mem hlR hyR, ?_⟩
        have e : F.π ⟨l * y, mul_mem hlR hyR⟩ = F.π ⟨l, hlR⟩ * τ₂ := by
          rw [← hπy, ← map_mul]
          rfl
        rw [mem_Γ₁, e]
        exact h
      have h1 := hcomm _ c.2 (l * y) ⟨mul_mem hl hyL, hlyX⟩
      calc (c : S.O) * l = (c : S.O) * (l * y) * y⁻¹ := by group
        _ = (l * y) * c * y⁻¹ := by rw [h1]
        _ = l * (y * c) * y⁻¹ := by group
        _ = l * (c * y) * y⁻¹ := by rw [hcy']
        _ = l * c := by group
  have hcC : (c : S.O) ∈ E.map (cK S k) := c.2
  rw [mem_map_cK_iff] at hcC
  have hcL' : S.ρ k * ((S.ρ k)⁻¹ * c * S.ρ k) * (S.ρ k)⁻¹ ∈ S.Lbar g := by
    refine X.conj_mem_Lbar_of_commute hcC.1 (MonoidHom.mem_range.mpr ⟨k, rfl⟩) fun x hx => ?_
    rw [show S.ρ k * ((S.ρ k)⁻¹ * c * S.ρ k) * (S.ρ k)⁻¹ = c by group]
    exact hcL x hx
  rw [show S.ρ k * ((S.ρ k)⁻¹ * c * S.ρ k) * (S.ρ k)⁻¹ = c by group] at hcL'
  have hcX := D.mem_Xb_of_commute hCE hdY' hd1 hcL' hcd'
  have hcinf : (c : S.O) ∈ C ⊓ E := ⟨c.2, hcL', hcX⟩
  rw [hinf] at hcinf
  exact hc1 (Subtype.ext (Subtype.ext ((Subgroup.mem_bot).mp hcinf)))

theorem timmesfeld_10_8_three (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (h7 : 7 ≤ S.width) {m : S.O} (hm : m ∈ S.Mbar)
    (hN : ∀ e ∈ S.Lbar g ⊓ Xb,
      m * e * m⁻¹ ∈ normalizer ((S.Lbar g ⊓ Xb : Subgroup S.O) : Set S.O)) :
    ∀ e ∈ S.Lbar g ⊓ Xb, m * e * m⁻¹ ∈ S.Lbar g ⊓ Xb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := S.Lbar g ⊓ Xb with hE
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, _root_.sq]
    exact S4.mul_self_of_mem_Lbar S X.haQ (Subgroup.mem_inf.mp x.2).1)⟩
  have hEM : E ≤ S.Mbar := inf_le_left.trans (S.Lbar_le_Mbar g)
  have hle : E.map (MulAut.conj m).toMonoidHom ≤ normalizer (E : Set S.O) := by
    rintro _ ⟨e, he, rfl⟩
    exact hN e he
  by_contra hcon
  push Not at hcon
  obtain ⟨e₀, he₀, he₀m⟩ := hcon
  have hne : E.map (MulAut.conj m).toMonoidHom ≠ E := fun h =>
    he₀m (by rw [← h]; exact ⟨e₀, he₀, rfl⟩)
  obtain ⟨m', hm', hne', hle', hge'⟩ := exists_conj_mutual hEp hEM hm hle hne
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hm'
  by_cases hinf : E.map (cK S k) ⊓ E = ⊥
  · refine D.false_of_inf_eq_bot hCE h7 (k := k) (fun c hc e he => ?_) hinf
    have h1 : c * e * c⁻¹ * e⁻¹ ∈ E := mul_mem ((mem_normalizer_iff.mp (hle' hc) e).mp he)
      (inv_mem he)
    have h2 : c * e * c⁻¹ * e⁻¹ ∈ E.map (cK S k) := by
      have h3 := (mem_normalizer_iff.mp (hge' he) c⁻¹).mp (inv_mem hc)
      have e1 : c * e * c⁻¹ * e⁻¹ = c * (e * c⁻¹ * e⁻¹) := by group
      rw [e1]
      exact mul_mem hc h3
    have h4 : c * e * c⁻¹ * e⁻¹ ∈ E.map (cK S k) ⊓ E := ⟨h2, h1⟩
    rw [hinf, Subgroup.mem_bot] at h4
    calc c * e = c * e * c⁻¹ * e⁻¹ * (e * c) := by group
      _ = e * c := by rw [h4, one_mul]
  · obtain ⟨⟨τ, hτ⟩, hτ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hinf
    have hτ1 : τ ≠ 1 := fun h => hτ1' (Subtype.ext h)
    exact hne' (D.eq_of_mem_inf hCE hP hle' hτ.2 hτ1 hτ.1)

end Dec108

end CFSG.LargeExtraspecial.S10
