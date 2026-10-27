module

public import CFSG.GH74.GLS.Stage1.Main.BrG2AsmT
public import CFSG.GH74.GLS.Stage1.Main.BrG2AbelQ
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutB

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Asm4

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.exists_g (hcen : Cen2 G z S) (hn : 3 ≤ C.n)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1)) :
    ∃ g ∈ barOf z S, g ∉ C.K₁ ⊔ C.K₂ ∧ (∃ c ∈ C.P₁, orderOf c = 2 ^ C.n ∧ g * c = c * g) ∧
      ∃ c ∈ C.P₂, orderOf c = 2 ^ C.n ∧ g * c = c * g := by
  obtain ⟨A, hAT, hAc, hAcard⟩ := C.exists_AT hcen
  have hBle : A ⊓ (C.K₁ ⊔ C.K₂) ≤ C.P₁ ⊔ C.P₂ := by
    rw [C.P_sup hcen]
    exact le_inf (inf_le_left.trans hAT) inf_le_right
  have hBc : ∀ a ∈ A ⊓ (C.K₁ ⊔ C.K₂), ∀ b ∈ A ⊓ (C.K₁ ⊔ C.K₂), a * b = b * a :=
    fun a ha b hb => hAc a ha.1 b hb.1
  obtain ⟨hle, hcc⟩ := abelian_in_quaternion_product hn hq₁ hq₂ C.P_comm (C.card_P_inf hcen) hBle hBc
  obtain ⟨-, hrel⟩ := C.sylow_inf hcen
  have hrelA : (C.K₁ ⊔ C.K₂).relIndex A ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right hAT (H := C.K₁ ⊔ C.K₂) (by
      rw [hrel]; norm_num)
    omega
  have hmul := Subgroup.relIndex_mul_card (C.K₁ ⊔ C.K₂) A
  rw [inf_comm] at hmul
  have h2n : 2 ^ (2 * C.n) = 2 * 2 ^ (2 * C.n - 1) := by
    have : 2 * C.n = (2 * C.n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ]; ring
  have hge : 2 ^ (2 * C.n - 1) ≤ Nat.card ↥(A ⊓ (C.K₁ ⊔ C.K₂)) := by
    rw [hAcard] at hmul
    have hpos : 0 < Nat.card ↥(A ⊓ (C.K₁ ⊔ C.K₂)) := Nat.card_pos
    nlinarith
  have heq : Nat.card ↥(A ⊓ (C.K₁ ⊔ C.K₂)) = 2 ^ (2 * C.n - 1) := le_antisymm hle hge
  obtain ⟨⟨c₁, hc₁P, hc₁B, hc₁o⟩, ⟨c₂, hc₂P, hc₂B, hc₂o⟩⟩ := hcc heq
  have hAnot : ¬ A ≤ C.K₁ ⊔ C.K₂ := by
    intro hAK
    have hBA : A ⊓ (C.K₁ ⊔ C.K₂) = A := inf_eq_left.2 hAK
    rw [hBA, hAcard] at heq
    have hpos : 0 < 2 ^ (2 * C.n - 1) := by positivity
    omega
  obtain ⟨g, hgA, hgK⟩ := Set.not_subset.1 hAnot
  exact ⟨g, hAT hgA, hgK, ⟨c₁, hc₁P, hc₁o, hAc g hgA c₁ hc₁B.1⟩, ⟨c₂, hc₂P, hc₂o,
    hAc g hgA c₂ hc₂B.1⟩⟩

end Asm4

section Asm8

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.induced₁ (hcen : Cen2 G z S)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1))
    (hnorm : ∀ x ∈ barOf z S, x ∈ normalizer (C.K₁ : Set (CentralizerBar z)))
    (hinv : ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) :
    InducedPGL2 C.K₁ (barOf z S) (Nat.card C.F₁) := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, -⟩ := C.exists_zeta hcen
  obtain ⟨u, huT, hu2, huK⟩ := C.exists_invol hcen hinv
  have h3 : 3 < Nat.card C.F₁ := by have := C.five; omega
  have huN : u ∈ normalizer (C.K₁ : Set (CentralizerBar z)) := hnorm u huT
  have hPK : C.P₁ ≤ C.K₁ := inf_le_right
  have hPs : IsSylowOf 2 C.P₁ C.K₁ := C.sylow_P₁ hcen
  have huP' := C.P₁_normalizes hcen huT huN hu2
  have huP : ∀ p ∈ C.P₁, u * p * u⁻¹ ∈ C.P₁ := fun p hp => (Subgroup.mem_normalizer_iff.1 huP' p).1 hp
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hout : ∀ p ∈ C.P₁, ∃ x ∈ C.K₁, (u * p⁻¹) * x ≠ x * (u * p⁻¹) := by
    intro p hp
    have hpT : p ∈ barOf z S := hp.1.1
    have hg : u * p⁻¹ ∈ barOf z S := (barOf z S).mul_mem huT ((barOf z S).inv_mem hpT)
    have hgK : u * p⁻¹ ∉ C.K₁ ⊔ C.K₂ := by
      intro h
      apply huK
      have e : u = (u * p⁻¹) * p := by group
      rw [e]
      exact mul_mem h (Subgroup.mem_sup_left hp.2)
    have := (C.no_outside hcen hq₁ hq₂ hg hgK).1
    push Not at this
    obtain ⟨p', hp', hne⟩ := this
    exact ⟨p', hp'.2, hne⟩
  have hKζ : C.K₁ ≤ centralizer ({ζ} : Set (CentralizerBar z)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact C.comm a ha ζ hζ₂
  have hg2 : ∀ g ∈ barOf z S, ∃ m : ℕ, g ^ (2 ^ m) = 1 := fun g hg => by
    obtain ⟨m, hm⟩ := (C.sylow_bar hcen).1 ⟨g, hg⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hdata : ∃ g : CentralizerBar z, g ∈ normalizer (C.K₁ : Set (CentralizerBar z)) ∧
      (∃ m : ℕ, g ^ (2 ^ m) = 1) ∧ (∃ k ∈ C.K₁, ∀ x ∈ C.K₁, u * x * u⁻¹ = k * (g * x * g⁻¹) * k⁻¹) ∧
      ((∃ n : ℕ, 2 ≤ n ∧ (Nat.card ↥(StatedSL 2 C.F₁)).factorization 2 = n + 1 ∧
        ∃ c ∈ C.K₁, orderOf c = 2 ^ n ∧ g * c = c * g) ∨
        (Nat.card C.F₁ % 8 = 3 ∨ Nat.card C.F₁ % 8 = 5)) := by
    by_cases hn3 : 3 ≤ C.n
    · obtain ⟨g, hgT, hgK, ⟨c, hcP, hco, hgc⟩, -⟩ := C.exists_g hcen hn3 hq₁ hq₂
      have hgN := hnorm g hgT
      refine ⟨g, hgN, hg2 g hgT, ?_, Or.inl ⟨C.n, C.two_le, C.v₁, c, hcP.2, hco, hgc⟩⟩
      have hr : u * g⁻¹ ∈ C.K₁ ⊔ C.K₂ :=
        (C.mul_mem_K_iff hcen huT ((barOf z S).inv_mem hgT)).2 (by
          constructor
          · intro h; exact absurd h huK
          · intro h
            exact absurd (by simpa using (C.K₁ ⊔ C.K₂).inv_mem h) hgK)
      obtain ⟨p, hp, p', hp', hrp⟩ := y_mem_sup_of_commute C.comm hr
      refine ⟨p, hp, fun x hx => ?_⟩
      have hgx : g * x * g⁻¹ ∈ C.K₁ := (Subgroup.mem_normalizer_iff.1 hgN x).1 hx
      have hcomm := C.comm _ hgx p' hp'
      have hu : u = (p * p') * g := by rw [← hrp]; group
      calc u * x * u⁻¹ = (p * p') * (g * x * g⁻¹) * (p * p')⁻¹ := by rw [hu]; group
        _ = p * (p' * (g * x * g⁻¹)) * p'⁻¹ * p⁻¹ := by group
        _ = p * ((g * x * g⁻¹) * p') * p'⁻¹ * p⁻¹ := by rw [← hcomm]
        _ = p * (g * x * g⁻¹) * p⁻¹ := by group
    · have hn2 : C.n = 2 := by have := C.two_le; omega
      refine ⟨u, huN, hg2 u huT, ⟨1, one_mem _, fun x _ => by simp⟩, Or.inr ?_⟩
      refine mod8_of_factorization C.odd₁ ?_
      have hv := C.v₁
      rw [hn2] at hv
      exact hv
  obtain ⟨g, hgN, hg2', hug, hfix⟩ := hdata
  have hpgl := pglQuot_of_outer C.odd₁ h3 C.e₁ hζ₁ hKζ hζo huN hu2 hPK hPs huP hout hgN hg2' hug hfix
  refine inducedPGL2_of_pglQuot_abs C.odd₁ h3 C.e₁ hu2 huN hpgl (fun x hx => hnorm x hx) huT ?_
  intro x hx
  have hK₂c : C.K₂ ≤ centralizer (C.K₁ : Set (CentralizerBar z)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact C.comm a ha b hb
  by_cases hxK : x ∈ C.K₁ ⊔ C.K₂
  · obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hxK
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_right (hK₂c hb))
  · have hxu : x * u ∈ C.K₁ ⊔ C.K₂ :=
      (C.mul_mem_K_iff hcen hx huT).2 ⟨fun h => absurd h hxK, fun h => absurd h huK⟩
    obtain ⟨a, ha, b, hb, hab⟩ := y_mem_sup_of_commute C.comm hxu
    have e : x = a * b * u := by
      calc x = (x * u) * u⁻¹ := by group
        _ = a * b * u := by rw [hab, hui]
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_right (hK₂c hb))) (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers u)))

end Asm8

section Asm9

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.induced₂ (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1))
    (hnorm : ∀ x ∈ barOf z S, x ∈ normalizer (C.K₂ : Set (CentralizerBar z)))
    (hinv : ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) :
    InducedPGL2 C.K₂ (barOf z S) (Nat.card C.F₂) := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, -⟩ := C.exists_zeta hcen
  obtain ⟨u, huT, hu2, huK⟩ := C.exists_invol hcen hinv
  have h3 : 3 < Nat.card C.F₂ := by omega
  have huN : u ∈ normalizer (C.K₂ : Set (CentralizerBar z)) := hnorm u huT
  have hPK : C.P₂ ≤ C.K₂ := inf_le_right
  have hPs : IsSylowOf 2 C.P₂ C.K₂ := C.sylow_P₂ hcen
  have huP' := C.P₂_normalizes hcen huT huN hu2
  have huP : ∀ p ∈ C.P₂, u * p * u⁻¹ ∈ C.P₂ := fun p hp => (Subgroup.mem_normalizer_iff.1 huP' p).1 hp
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hout : ∀ p ∈ C.P₂, ∃ x ∈ C.K₂, (u * p⁻¹) * x ≠ x * (u * p⁻¹) := by
    intro p hp
    have hpT : p ∈ barOf z S := hp.1.1
    have hg : u * p⁻¹ ∈ barOf z S := (barOf z S).mul_mem huT ((barOf z S).inv_mem hpT)
    have hgK : u * p⁻¹ ∉ C.K₁ ⊔ C.K₂ := by
      intro h
      apply huK
      have e : u = (u * p⁻¹) * p := by group
      rw [e]
      exact mul_mem h (Subgroup.mem_sup_right hp.2)
    have := (C.no_outside hcen hq₁ hq₂ hg hgK).2
    push Not at this
    obtain ⟨p', hp', hne⟩ := this
    exact ⟨p', hp'.2, hne⟩
  have hKζ : C.K₂ ≤ centralizer ({ζ} : Set (CentralizerBar z)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (C.comm ζ hζ₁ a ha).symm
  have hg2 : ∀ g ∈ barOf z S, ∃ m : ℕ, g ^ (2 ^ m) = 1 := fun g hg => by
    obtain ⟨m, hm⟩ := (C.sylow_bar hcen).1 ⟨g, hg⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hdata : ∃ g : CentralizerBar z, g ∈ normalizer (C.K₂ : Set (CentralizerBar z)) ∧
      (∃ m : ℕ, g ^ (2 ^ m) = 1) ∧ (∃ k ∈ C.K₂, ∀ x ∈ C.K₂, u * x * u⁻¹ = k * (g * x * g⁻¹) * k⁻¹) ∧
      ((∃ n : ℕ, 2 ≤ n ∧ (Nat.card ↥(StatedSL 2 C.F₂)).factorization 2 = n + 1 ∧
        ∃ c ∈ C.K₂, orderOf c = 2 ^ n ∧ g * c = c * g) ∨
        (Nat.card C.F₂ % 8 = 3 ∨ Nat.card C.F₂ % 8 = 5)) := by
    by_cases hn3 : 3 ≤ C.n
    · obtain ⟨g, hgT, hgK, -, ⟨c, hcP, hco, hgc⟩⟩ := C.exists_g hcen hn3 hq₁ hq₂
      have hgN := hnorm g hgT
      refine ⟨g, hgN, hg2 g hgT, ?_, Or.inl ⟨C.n, C.two_le, C.v₂, c, hcP.2, hco, hgc⟩⟩
      have hr : u * g⁻¹ ∈ C.K₁ ⊔ C.K₂ :=
        (C.mul_mem_K_iff hcen huT ((barOf z S).inv_mem hgT)).2 (by
          constructor
          · intro h; exact absurd h huK
          · intro h
            exact absurd (by simpa using (C.K₁ ⊔ C.K₂).inv_mem h) hgK)
      obtain ⟨p, hp, p', hp', hrp⟩ := y_mem_sup_of_commute C.comm hr
      refine ⟨p', hp', fun x hx => ?_⟩
      have hgx : g * x * g⁻¹ ∈ C.K₂ := (Subgroup.mem_normalizer_iff.1 hgN x).1 hx
      have hconj : p' * (g * x * g⁻¹) * p'⁻¹ ∈ C.K₂ :=
        mul_mem (mul_mem hp' hgx) (inv_mem hp')
      have hcomm := C.comm p hp _ hconj
      have hu : u = (p * p') * g := by rw [← hrp]; group
      calc u * x * u⁻¹ = p * (p' * (g * x * g⁻¹) * p'⁻¹) * p⁻¹ := by rw [hu]; group
        _ = (p' * (g * x * g⁻¹) * p'⁻¹) * p * p⁻¹ := by rw [hcomm]
        _ = p' * (g * x * g⁻¹) * p'⁻¹ := by group
    · have hn2 : C.n = 2 := by have := C.two_le; omega
      refine ⟨u, huN, hg2 u huT, ⟨1, one_mem _, fun x _ => by simp⟩, Or.inr ?_⟩
      refine mod8_of_factorization C.odd₂ ?_
      have hv := C.v₂
      rw [hn2] at hv
      exact hv
  obtain ⟨g, hgN, hg2', hug, hfix⟩ := hdata
  have hpgl := pglQuot_of_outer C.odd₂ h3 C.e₂ hζ₂ hKζ hζo huN hu2 hPK hPs huP hout hgN hg2' hug hfix
  refine inducedPGL2_of_pglQuot_abs C.odd₂ h3 C.e₂ hu2 huN hpgl (fun x hx => hnorm x hx) huT ?_
  intro x hx
  have hK₁c : C.K₁ ≤ centralizer (C.K₂ : Set (CentralizerBar z)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (C.comm a ha b hb).symm
  by_cases hxK : x ∈ C.K₁ ⊔ C.K₂
  · obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hxK
    exact mul_mem (Subgroup.mem_sup_right (hK₁c ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hb))
  · have hxu : x * u ∈ C.K₁ ⊔ C.K₂ :=
      (C.mul_mem_K_iff hcen hx huT).2 ⟨fun h => absurd h hxK, fun h => absurd h huK⟩
    obtain ⟨a, ha, b, hb, hab⟩ := y_mem_sup_of_commute C.comm hxu
    have e : x = a * b * u := by
      calc x = (x * u) * u⁻¹ := by group
        _ = a * b * u := by rw [hab, hui]
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right (hK₁c ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hb)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers u)))

end Asm9

end CFSG.GH74.GLS.Stage1.Main
