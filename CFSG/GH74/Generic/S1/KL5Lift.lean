module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvQuasi
public import CFSG.GH74.KGroups.L3EpsFour
public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CFSG.GH74.Generic.S1

theorem kl5_commute_of_perfect_of_commutator_mem_center {G : Type*} [Group G] {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) {x : G} (hx : ∀ y ∈ P, ⁅x, y⁆ ∈ Subgroup.center G) :
    ∀ y ∈ P, x * y = y * x := by
  classical
  set N := Subgroup.center G with hN
  set X := Subgroup.zpowers x with hX
  have hXP : ⁅X, P⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
    have h1 : ⁅QuotientGroup.mk' N x, QuotientGroup.mk' N g₂⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 (hx g₂ hg₂)
    have h2 : Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N g₂) :=
      commutatorElement_eq_one_iff_commute.1 h1
    have h3 : ⁅QuotientGroup.mk' N (x ^ k), QuotientGroup.mk' N g₂⁆ = 1 := by
      rw [map_zpow]
      exact commutatorElement_eq_one_iff_commute.2 (h2.zpow_left k)
    rw [← map_commutatorElement] at h3
    exact (QuotientGroup.eq_one_iff _).1 h3
  have h2 : ⁅⁅X, P⁆, P⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅⁅X, P⁆, P⁆ ≤ ⁅N, P⁆ := Subgroup.commutator_mono hXP le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.center_le_centralizer _)
      _ ≤ ⊥ := le_rfl
  have h3 : ⁅⁅P, X⁆, P⁆ = ⊥ := by rw [Subgroup.commutator_comm P X]; exact h2
  have h4 : ⁅⁅P, P⁆, X⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h3 h2
  rw [hP] at h4
  intro y hy
  have h5 : y ∈ Subgroup.centralizer (X : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h4 hy
  exact Subgroup.mem_centralizer_iff.1 h5 x (Subgroup.mem_zpowers x)

theorem kl5_exists_perfect_lift {H S : Type*} [Group H] [Finite H] [Group S] (π : H →* S)
    (hπ : Function.Surjective π) (A : Subgroup S) (hA : ⁅A, A⁆ = A) :
    ∃ Ã : Subgroup H, ⁅Ã, Ã⁆ = Ã ∧ Ã.map π = A := by
  classical
  let T : Set (Subgroup H) := {R | R.map π = A}
  have hT : T.Nonempty := ⟨A.comap π, Subgroup.map_comap_eq_self_of_surjective hπ A⟩
  obtain ⟨R, hR, hmin⟩ := (wellFounded_lt (α := Subgroup H)).has_min T hT
  refine ⟨R, ?_, hR⟩
  have hle : ⁅R, R⁆ ≤ R := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  have hmem : ⁅R, R⁆ ∈ T := by
    show ⁅R, R⁆.map π = A
    rw [Subgroup.map_commutator]
    have : R.map π = A := hR
    rw [this, hA]
  by_contra hne
  exact hmin _ hmem (lt_of_le_of_ne hle hne)


theorem kl5_odd_center_of_model_three (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {p f : ℕ} (hp2 : p ≠ 2)
    (hmod : StatedClassicalModel (K ⧸ center K) .PSL 3 p f ∨
      StatedClassicalModel (K ⧸ center K) .PSU 3 p f) : Odd (Nat.card (center K)) := by
  rcases hmod with hm | hm
  · have h := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hK hm
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := rfl
    rw [hexc, hgen] at h
    simp only [mul_one] at h
    exact Odd.of_dvd_nat (by decide : Odd 3) (h.trans (Nat.gcd_dvd_left 3 _))
  · have h := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hK hm
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := rfl
    rw [hexc, hgen] at h
    simp only [mul_one] at h
    exact Odd.of_dvd_nat (by decide : Odd 3) (h.trans (Nat.gcd_dvd_left 3 _))


theorem kl5_exists_involution_lift {Ã : Type*} [Group Ã] [Finite Ã]
    (hodd : Odd (Nat.card (Subgroup.center Ã))) (x : Ã ⧸ Subgroup.center Ã) (hx : x * x = 1) :
    ∃ h : Ã, h * h = 1 ∧ (h : Ã ⧸ Subgroup.center Ã) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set m := Nat.card (Subgroup.center Ã) with hm
  obtain ⟨k, hk⟩ := hodd
  have hg2 : g * g ∈ Subgroup.center Ã := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]; exact hx
  have hz : (g * g) ^ m = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center Ã) (x := (⟨g * g, hg2⟩ : Subgroup.center Ã))
    exact congrArg Subtype.val this
  refine ⟨g ^ m, ?_, ?_⟩
  · calc g ^ m * g ^ m = (g * g) ^ m := by
          rw [← pow_add, ← two_mul, pow_mul, sq]
      _ = 1 := hz
  · rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, sq, hx, one_pow, one_mul]


theorem kl5_liftA (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {H S Q : Type} [Group H] [Finite H] [Group S] [Group Q] (π : H →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H) (α : Q →* S)
    (hα : Function.Injective α) (hQ : CFSG.IsQuasisimple Q) {p f : ℕ} (hp2 : p ≠ 2)
    (hmodel : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 p f ∨
      StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 p f) :
    ∃ Ã : Subgroup H, ⁅Ã, Ã⁆ = Ã ∧ Ã.map π = α.range ∧
      ∃ h₁ ∈ Ã, ∃ h₂ ∈ Ã, h₁ * h₁ = 1 ∧ h₂ * h₂ = 1 ∧ h₁ * h₂ = h₂ * h₁ ∧ h₁ ≠ h₂ ∧
        (∃ a ∈ Ã, h₁ * a ≠ a * h₁) ∧ (∃ a ∈ Ã, h₂ * a ≠ a * h₂) ∧
        (∃ a ∈ Ã, h₁ * h₂ * a ≠ a * (h₁ * h₂)) := by
  classical
  have hQperf : Group.IsPerfect Q := hQ.1
  have hAperf : ⁅α.range, α.range⁆ = α.range :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective α.rangeRestrict_surjective)
  obtain ⟨Ã, hÃp, hÃm⟩ := kl5_exists_perfect_lift π hπ α.range hAperf
  have hmemrange : ∀ a : Ã, π a ∈ α.range := fun a => hÃm ▸ Subgroup.mem_map_of_mem π a.2
  let ρ₁ : ↥Ã →* ↥α.range := (π.comp Ã.subtype).codRestrict α.range hmemrange
  let ρ₀ : ↥Ã →* Q := (MonoidHom.ofInjective hα).symm.toMonoidHom.comp ρ₁
  have hρ₀α : ∀ a : Ã, α (ρ₀ a) = π a := fun a => by
    have := (MonoidHom.ofInjective hα).apply_symm_apply (ρ₁ a)
    exact congrArg Subtype.val this
  have hρ₀s : Function.Surjective ρ₀ := by
    intro q
    have hq : α q ∈ (Ã.map π) := by rw [hÃm]; exact ⟨q, rfl⟩
    obtain ⟨a, ha, hπa⟩ := Subgroup.mem_map.1 hq
    refine ⟨⟨a, ha⟩, hα ?_⟩
    rw [hρ₀α]; exact hπa
  have hker₀ : ρ₀.ker ≤ Subgroup.center ↥Ã := by
    intro a ha
    have h1 : π a = 1 := by rw [← hρ₀α, MonoidHom.mem_ker.1 ha, map_one]
    have h2 : (a : H) ∈ Subgroup.center H := hker (MonoidHom.mem_ker.2 h1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 h2 (g : H)))
  have hÃperfT : Group.IsPerfect ↥Ã := Subgroup.isPerfect_iff.2 hÃp
  let ρ : ↥Ã →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp ρ₀
  have hρ : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hρ₀s
  have hkerρ : ρ.ker ≤ Subgroup.center ↥Ã := by
    intro a ha
    have haZ : ρ₀ a ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 ha
    have hcomm := kl5_commute_of_perfect_of_commutator_mem_center (G := H) (P := Ã) hÃp (x := (a : H))
      (fun y hy => by
        apply hker
        rw [MonoidHom.mem_ker]
        have h1 : π ⁅(a : H), y⁆ = ⁅π a, π y⁆ := map_commutatorElement π _ _
        rw [h1, ← hρ₀α a, ← hρ₀α ⟨y, hy⟩, ← map_commutatorElement α]
        have : ⁅ρ₀ a, ρ₀ ⟨y, hy⟩⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 haZ _).symm
        rw [this, map_one])
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2).symm
  have hÃq : CFSG.IsQuasisimple ↥Ã :=
    CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_of_perfect_cover hÃperfT ρ hρ hQ.2.1 hQ.2.2 hkerρ
  have hFinÃ : Finite ↥Ã := inferInstance
  let e : ↥Ã ⧸ Subgroup.center ↥Ã ≃* Q ⧸ Subgroup.center Q :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hÃq hρ₀s hker₀
  have hmodelÃ : StatedClassicalModel (↥Ã ⧸ Subgroup.center ↥Ã) .PSL 3 p f ∨
      StatedClassicalModel (↥Ã ⧸ Subgroup.center ↥Ã) .PSU 3 p f := by
    rcases hmodel with h | h
    · exact Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm h)
    · exact Or.inr (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm h)
  have hodd : Odd (Nat.card (Subgroup.center ↥Ã)) := kl5_odd_center_of_model_three hGA hÃq hp2 hmodelÃ
  have hfour : ∃ a b : ↥Ã ⧸ Subgroup.center ↥Ã, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧
      b ≠ 1 ∧ a ≠ b := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (↥Ã ⧸ Subgroup.center ↥Ã)) := inferInstance
    have hS : IsPGroup 2 (P : Subgroup (↥Ã ⧸ Subgroup.center ↥Ã)) := P.isPGroup'
    have hmax : ∀ T : Subgroup (↥Ã ⧸ Subgroup.center ↥Ã), IsPGroup 2 T → (P : Subgroup _) ≤ T →
        T ≤ P := fun T hT hle => (P.3 hT hle).le
    rcases hmodelÃ with hm | hm
    · obtain ⟨a, -, b, -, h⟩ :=
        CFSG.GH74.KGroups.L3Eps.l3eps_sylow_four (Or.inl rfl) hp2 hm hS hmax
      exact ⟨a, b, h⟩
    · obtain ⟨a, -, b, -, h⟩ :=
        CFSG.GH74.KGroups.L3Eps.l3eps_sylow_four (Or.inr rfl) hp2 hm hS hmax
      exact ⟨a, b, h⟩
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := hfour
  obtain ⟨h₁, hh₁, hh₁x⟩ := kl5_exists_involution_lift hodd a ha
  obtain ⟨h₂, hh₂, hh₂x⟩ := kl5_exists_involution_lift hodd b hb
  have hinv₁ : h₁⁻¹ = h₁ := inv_eq_of_mul_eq_one_right hh₁
  have hinv₂ : h₂⁻¹ = h₂ := inv_eq_of_mul_eq_one_right hh₂
  set c := h₁ * h₂ * h₁⁻¹ * h₂⁻¹ with hc
  have hcZ : c ∈ Subgroup.center ↥Ã := by
    rw [hc, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hh₁x, hh₂x]
    rw [hab, mul_assoc, mul_assoc]
    simp
  have hcentral : ∀ g : ↥Ã, c * g = g * c := fun g => (Subgroup.mem_center_iff.1 hcZ g).symm
  have hcc : c * c = 1 := by
    have e1 : h₁ * h₂ * h₁ = c * h₂ := by
      rw [hc, hinv₁, hinv₂]
      calc h₁ * h₂ * h₁ = h₁ * h₂ * h₁ * (h₂ * h₂) := by rw [hh₂, mul_one]
        _ = h₁ * h₂ * h₁ * h₂ * h₂ := by group
    have e2 : (h₁ * h₂ * h₁) * (h₁ * h₂ * h₁) = 1 := by
      calc (h₁ * h₂ * h₁) * (h₁ * h₂ * h₁) = h₁ * h₂ * (h₁ * h₁) * h₂ * h₁ := by group
        _ = h₁ * (h₂ * h₂) * h₁ := by rw [hh₁, mul_one]; group
        _ = 1 := by rw [hh₂, mul_one, hh₁]
    rw [e1] at e2
    calc c * c = c * c * (h₂ * h₂) := by rw [hh₂, mul_one]
      _ = c * (c * h₂) * h₂ := by group
      _ = c * (h₂ * c) * h₂ := by rw [hcentral h₂]
      _ = (c * h₂) * (c * h₂) := by group
      _ = 1 := e2
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hcc)
    have h2 : orderOf c ∣ Nat.card (Subgroup.center ↥Ã) := Subgroup.orderOf_dvd_natCard _ hcZ
    have h3 : orderOf c ∣ Nat.gcd 2 (Nat.card (Subgroup.center ↥Ã)) := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 2 (Nat.card (Subgroup.center ↥Ã)) = 1 :=
      Nat.coprime_two_left.mpr hodd
    rw [h4] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hcomm : h₁ * h₂ = h₂ * h₁ := by
    have h1 : h₁ * h₂ * (h₁ * h₂) = 1 := by
      calc h₁ * h₂ * (h₁ * h₂) = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by rw [hinv₁, hinv₂]; group
        _ = 1 := hc1
    calc h₁ * h₂ = (h₁ * h₂)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = h₂ * h₁ := by rw [mul_inv_rev, hinv₁, hinv₂]
  have hne12 : h₁ ≠ h₂ := fun h => hne (by rw [← hh₁x, ← hh₂x, h])
  have hnc : ∀ (g : ↥Ã), (g : ↥Ã ⧸ Subgroup.center ↥Ã) ≠ 1 →
      ∃ a ∈ Ã, ((g : H) * a ≠ a * (g : H)) := by
    intro g hg
    by_contra hcon
    push Not at hcon
    apply hg
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcon y y.2).symm
  have hab1 : (↑(h₁ * h₂) : ↥Ã ⧸ Subgroup.center ↥Ã) ≠ 1 := by
    rw [QuotientGroup.mk_mul, hh₁x, hh₂x]
    intro h
    exact hne (by
      calc a = a * (b * b) := by rw [hb, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b := by rw [h, one_mul])
  refine ⟨Ã, hÃp, hÃm, (h₁ : H), h₁.2, (h₂ : H), h₂.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hh₁
  · exact congrArg Subtype.val hh₂
  · exact congrArg Subtype.val hcomm
  · exact fun h => hne12 (Subtype.ext h)
  · exact hnc h₁ (by rw [hh₁x]; exact ha1)
  · exact hnc h₂ (by rw [hh₂x]; exact hb1)
  · have := hnc (h₁ * h₂) hab1
    exact this

end CFSG.GH74.Generic.S1
