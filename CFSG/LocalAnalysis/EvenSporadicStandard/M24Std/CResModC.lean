module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

theorem card_le_sq_of_involution {V : Type} [Group V] [Finite V] (hc : ∀ a b : V, a * b = b * a)
    (h2 : ∀ a : V, a * a = 1) (φ : V →* V) (hφ : ∀ a, φ (φ a) = a) :
    Nat.card V ≤ Nat.card {a : V // φ a = a} * Nat.card {a : V // φ a = a} := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hδ : ∀ a b : V, φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (φ b * b⁻¹) := by
    intro a b
    rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹]
    exact mul_mul_mul_comm _ _ _ _
  let δ : V →* V :=
    { toFun := fun a => φ a * a⁻¹
      map_one' := by simp
      map_mul' := hδ }
  have h1 := Subgroup.card_ker_mul_card_range δ
  have hinv : ∀ a : V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (h2 a)
  have hker : Nat.card δ.ker ≤ Nat.card {a : V // φ a = a} := by
    refine Nat.card_le_card_of_injective
      (fun k : δ.ker => (⟨(k : V), ?_⟩ : {a : V // φ a = a})) ?_
    · have := MonoidHom.mem_ker.1 k.2
      change φ k * (k : V)⁻¹ = 1 at this
      exact mul_inv_eq_one.1 this
    · intro k k' hkk'
      simp only [Subtype.mk.injEq] at hkk'
      exact Subtype.ext hkk'
  have hrange : Nat.card δ.range ≤ Nat.card {a : V // φ a = a} := by
    refine Nat.card_le_card_of_injective
      (fun r : δ.range => (⟨(r : V), ?_⟩ : {a : V // φ a = a})) ?_
    · obtain ⟨a, ha⟩ := r.2
      rw [← ha]
      change φ (φ a * a⁻¹) = φ a * a⁻¹
      rw [map_mul, map_inv, hφ, hinv (φ a), hinv a]
      exact mul_comm _ _
    · intro r r' hrr'
      simp only [Subtype.mk.injEq] at hrr'
      exact Subtype.ext hrr'
  calc Nat.card V = Nat.card δ.ker * Nat.card δ.range := h1.symm
    _ ≤ _ := Nat.mul_le_mul hker hrange

theorem rep_of_index_two {X : Type*} [Group X] {H : Subgroup X} (hH : H.index = 2) {n₀ : X}
    (hn₀ : n₀ ∉ H) : n₀ * n₀ ∈ H ∧ ∀ g : X, g ∈ H ∨ g * n₀⁻¹ ∈ H := by
  refine ⟨Subgroup.mul_self_mem_of_index_two hH n₀, fun g => ?_⟩
  by_cases hg : g ∈ H
  · exact Or.inl hg
  · right
    rw [Subgroup.mul_mem_iff_of_index_two hH]
    exact ⟨fun h => absurd h hg, fun h => absurd (inv_mem_iff.1 h) hn₀⟩

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

theorem card_fixfix_le_four (hF : SextetFacts L A) (hQ : SextetFactsQ L A)
    {H : Subgroup (egNL L A)} (hH : H.index = 2) {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) :
    Nat.card {a : G // a ∈ A ∧ ∀ n ∈ H, (n : G) * x * (n : G)⁻¹ = x →
      (n : G) * a * (n : G)⁻¹ = a} ≤ 4 := by
  classical
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
  let W : Subgroup G :=
    { carrier := {a | a ∈ A ∧ ∀ n ∈ H, (n : G) * x * (n : G)⁻¹ = x →
        (n : G) * a * (n : G)⁻¹ = a}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, fun n hn hnx => by
        have h1 := ha.2 n hn hnx
        have h2 := hb.2 n hn hnx
        calc (n : G) * (a * b) * (n : G)⁻¹
            = ((n : G) * a * (n : G)⁻¹) * ((n : G) * b * (n : G)⁻¹) := by group
          _ = a * b := by rw [h1, h2]⟩
      one_mem' := ⟨A.one_mem, fun n _ _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, fun n hn hnx => by
        have h1 := ha.2 n hn hnx
        calc (n : G) * a⁻¹ * (n : G)⁻¹ = ((n : G) * a * (n : G)⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [h1]⟩ }
  show Nat.card W ≤ 4
  have hWA : ∀ a ∈ W, a ∈ A := fun a ha => ha.1
  by_cases hcase : ∀ n : egNL L A, (n : G) * x * (n : G)⁻¹ = x → n ∈ H
  · have hWx : ∀ a ∈ W, a = 1 ∨ a = x := by
      intro a ha
      refine hQ.fix x hxA hx1 a ha.1 ?_
      intro n hn hnx
      exact ha.2 ⟨n, hn⟩ (hcase ⟨n, hn⟩ hnx) hnx
    have hinj : Function.Injective (fun a : W => decide ((a : G) = x)) := by
      intro a b hab
      simp only [decide_eq_decide] at hab
      refine Subtype.ext ?_
      rcases hWx a a.2 with ha | ha <;> rcases hWx b b.2 with hb | hb
      · rw [ha, hb]
      · exact absurd (hab.2 hb) (by rw [ha]; exact fun h => hx1 h.symm)
      · exact absurd (hab.1 ha) (by rw [hb]; exact fun h => hx1 h.symm)
      · rw [ha, hb]
    calc Nat.card W ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
      _ ≤ 4 := by norm_num
  · obtain ⟨n₀, hn₀x, hn₀H⟩ : ∃ n : egNL L A, (n : G) * x * (n : G)⁻¹ = x ∧ n ∉ H := by
      by_contra hne
      exact hcase fun n hnx => by_contra fun hnH => hne ⟨n, hnx, hnH⟩
    obtain ⟨hn₀2, hrep⟩ := rep_of_index_two hH hn₀H
    have hn₀A : ∀ a ∈ A, (n₀ : G) * a * (n₀ : G)⁻¹ ∈ A := fun a ha =>
      (mem_normalizer_iff.1 (mem_inf.1 n₀.2).1 a).1 ha
    have hx' : (n₀ : G)⁻¹ * x * (n₀ : G) = x := by
      calc (n₀ : G)⁻¹ * x * (n₀ : G) = (n₀ : G)⁻¹ * ((n₀ : G) * x * (n₀ : G)⁻¹) * (n₀ : G) := by
            rw [hn₀x]
        _ = x := by group
    have hWinv : ∀ a ∈ W, (n₀ : G) * a * (n₀ : G)⁻¹ ∈ W := by
      intro a ha
      refine ⟨hn₀A a ha.1, fun n hn hnx => ?_⟩
      have hm : n₀⁻¹ * n * n₀⁻¹⁻¹ ∈ H := hHn.conj_mem n hn n₀⁻¹
      have hmG : ((n₀⁻¹ * n * n₀⁻¹⁻¹ : egNL L A) : G) = (n₀ : G)⁻¹ * n * n₀ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      have hmx : ((n₀ : G)⁻¹ * n * n₀) * x * ((n₀ : G)⁻¹ * n * n₀)⁻¹ = x := by
        calc ((n₀ : G)⁻¹ * n * n₀) * x * ((n₀ : G)⁻¹ * n * n₀)⁻¹
            = (n₀ : G)⁻¹ * n * ((n₀ : G) * x * (n₀ : G)⁻¹) * (n : G)⁻¹ * n₀ := by group
          _ = (n₀ : G)⁻¹ * (n * x * (n : G)⁻¹) * n₀ := by rw [hn₀x]; group
          _ = (n₀ : G)⁻¹ * x * n₀ := by rw [hnx]
          _ = x := hx'
      have := ha.2 _ hm (by rw [hmG]; exact hmx)
      rw [hmG] at this
      calc (n : G) * ((n₀ : G) * a * (n₀ : G)⁻¹) * (n : G)⁻¹
          = (n₀ : G) * (((n₀ : G)⁻¹ * n * n₀) * a * ((n₀ : G)⁻¹ * n * n₀)⁻¹) * (n₀ : G)⁻¹ := by
            group
        _ = (n₀ : G) * a * (n₀ : G)⁻¹ := by rw [this]
    have hWsq : ∀ a ∈ W, (n₀ : G) * ((n₀ : G) * a * (n₀ : G)⁻¹) * (n₀ : G)⁻¹ = a := by
      intro a ha
      have hxx : ((n₀ * n₀ : egNL L A) : G) * x * ((n₀ * n₀ : egNL L A) : G)⁻¹ = x := by
        simp only [Subgroup.coe_mul, mul_inv_rev]
        calc (n₀ : G) * n₀ * x * ((n₀ : G)⁻¹ * (n₀ : G)⁻¹)
            = n₀ * (n₀ * x * (n₀ : G)⁻¹) * (n₀ : G)⁻¹ := by group
          _ = x := by rw [hn₀x, hn₀x]
      have := ha.2 _ hn₀2 hxx
      simp only [Subgroup.coe_mul, mul_inv_rev] at this
      calc (n₀ : G) * ((n₀ : G) * a * (n₀ : G)⁻¹) * (n₀ : G)⁻¹
          = (n₀ : G) * n₀ * a * ((n₀ : G)⁻¹ * (n₀ : G)⁻¹) := by group
        _ = a := this
    let φW : W →* W :=
      ((MulAut.conj (n₀ : G)).toMonoidHom.comp W.subtype).codRestrict W
        (fun a => hWinv a.1 a.2)
    have hφW : ∀ a : W, ((φW a : W) : G) = (n₀ : G) * a * (n₀ : G)⁻¹ := fun a => rfl
    have hfix : ∀ a : W, φW a = a → (a : G) = 1 ∨ (a : G) = x := by
      intro a ha
      have ha' : (n₀ : G) * a * (n₀ : G)⁻¹ = a := by
        rw [← hφW a, ha]
      refine hQ.fix x hxA hx1 a a.2.1 ?_
      intro n hn hnx
      rcases hrep ⟨n, hn⟩ with hnH | hnH
      · exact a.2.2 ⟨n, hn⟩ hnH hnx
      · have hnH' : ((⟨n, hn⟩ * n₀⁻¹ : egNL L A) : G) = n * (n₀ : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hhx : (n * (n₀ : G)⁻¹) * x * (n * (n₀ : G)⁻¹)⁻¹ = x := by
          calc (n * (n₀ : G)⁻¹) * x * (n * (n₀ : G)⁻¹)⁻¹
              = n * ((n₀ : G)⁻¹ * x * n₀) * n⁻¹ := by group
            _ = x := by rw [hx', hnx]
        have := a.2.2 _ hnH (by rw [hnH']; exact hhx)
        rw [hnH'] at this
        calc n * (a : G) * n⁻¹ = (n * (n₀ : G)⁻¹) * ((n₀ : G) * a * (n₀ : G)⁻¹) *
              (n * (n₀ : G)⁻¹)⁻¹ := by group
          _ = (n * (n₀ : G)⁻¹) * a * (n * (n₀ : G)⁻¹)⁻¹ := by rw [ha']
          _ = a := this
    have hcomm : ∀ a b : W, a * b = b * a := fun a b => Subtype.ext (hF.elem.1 _ a.2.1 _ b.2.1)
    have hsq : ∀ a : W, a * a = 1 := fun a => Subtype.ext (hF.elem.2 _ a.2.1)
    have hφφ : ∀ a : W, φW (φW a) = a := fun a => Subtype.ext (by
      rw [hφW, hφW]
      exact hWsq a a.2)
    have hfixcard : Nat.card {a : W // φW a = a} ≤ 2 := by
      have hinj : Function.Injective (fun a : {a : W // φW a = a} => decide ((a.1 : G) = x)) := by
        intro a b hab
        simp only [decide_eq_decide] at hab
        refine Subtype.ext (Subtype.ext ?_)
        rcases hfix a.1 a.2 with ha | ha <;> rcases hfix b.1 b.2 with hb | hb
        · rw [ha, hb]
        · exact absurd (hab.2 hb) (by rw [ha]; exact fun h => hx1 h.symm)
        · exact absurd (hab.1 ha) (by rw [hb]; exact fun h => hx1 h.symm)
        · rw [ha, hb]
      calc Nat.card {a : W // φW a = a} ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
        _ = 2 := by simp
    calc Nat.card W ≤ _ := card_le_sq_of_involution hcomm hsq φW hφφ
      _ ≤ 2 * 2 := Nat.mul_le_mul hfixcard hfixcard

end CFSG.EvenSporadicStandard.M24Std
