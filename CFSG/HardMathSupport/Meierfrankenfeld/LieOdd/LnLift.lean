module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Lift

variable {L S : Type*} [Group L] [Group S] {p : ℕ}

theorem commute_of_map_of_pow_eq_one (π : L →* S) (hK : π.ker ≤ Subgroup.center L) [Fact p.Prime]
    (hKp : ¬ p ∣ Nat.card π.ker) {a b : L} (ha : a ^ p = 1) (hab : π a * π b = π b * π a) :
    a * b = b * a := by
  have hconj : (b⁻¹ * a * b) ^ p = 1 := by
    have := conj_pow (a := b⁻¹) (b := a) (i := p)
    rw [inv_inv] at this
    rw [this, ha]
    group
  have h : b⁻¹ * a * b = a := by
    refine eq_of_map_eq_of_pow_eq_one π hK hKp hconj ha ?_
    rw [map_mul, map_mul, map_inv, mul_assoc, hab, inv_mul_cancel_left]
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h]

end Lift

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_lift_orbit (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hKp : ¬ p ∣ Nat.card π.ker) {U₀ T₀ : Subgroup S}
    (hUc : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a) (hUp : ∀ a ∈ U₀, a ^ p = 1) (hU : U₀ ≠ ⊥)
    (hTN : T₀ ≤ Subgroup.normalizer (U₀ : Set S)) {m : ℕ}
    (horb : ∀ D₀ : Subgroup S, D₀ ≤ U₀ → D₀.relIndex U₀ = p →
      m ≤ (T₀ ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex T₀) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  classical
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hcomm : ∀ {a b : ↥L}, a ^ p = 1 → π a * π b = π b * π a → a * b = b * a :=
    fun ha hab => commute_of_map_of_pow_eq_one π hker hKp ha hab
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup ↥L, ∀ x, x ∈ Q ↔ π x ∈ U₀ ∧ x ^ p = 1 := by
    refine ⟨{ carrier := {x | π x ∈ U₀ ∧ x ^ p = 1}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun _ => Iff.rfl⟩
    · rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
      refine ⟨by rw [map_mul]; exact U₀.mul_mem ha hb, ?_⟩
      have hc : Commute a b := hcomm hap (hUc _ ha _ hb)
      rw [hc.mul_pow, hap, hbp, one_mul]
    · exact ⟨by rw [map_one]; exact U₀.one_mem, one_pow p⟩
    · rintro a ⟨ha, hap⟩
      exact ⟨by rw [map_inv]; exact U₀.inv_mem ha, by rw [inv_pow, hap, inv_one]⟩
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    hcomm ((hQ a).1 ha).2 (hUc _ ((hQ a).1 ha).1 _ ((hQ b).1 hb).1)
  have hQp : ∀ a ∈ Q, a ^ p = 1 := fun a ha => ((hQ a).1 ha).2
  have hQinj : ∀ a ∈ Q, ∀ b ∈ Q, π a = π b → a = b := fun a ha b hb hab =>
    eq_of_map_eq_of_pow_eq_one π hker hKp ((hQ a).1 ha).2 ((hQ b).1 hb).2 hab
  have hQsurj : ∀ u ∈ U₀, ∃ x ∈ Q, π x = u := by
    intro u hu
    obtain ⟨l, hl, hlp⟩ := exists_map_eq_pow_eq_one π hπ hKp (hUp u hu)
    exact ⟨l, (hQ l).2 ⟨hl ▸ hu, hlp⟩, hl⟩
  have hQ1 : Q ≠ ⊥ := by
    intro h
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU
    obtain ⟨x, hx, hxu⟩ := hQsurj u hu
    rw [h, Subgroup.mem_bot] at hx
    apply hu1
    apply Subtype.ext
    show u = 1
    rw [← hxu, hx, map_one]
  let T' : Subgroup ↥L := T₀.comap π
  have hT'Q : ∀ t ∈ T', ∀ h ∈ Q, t * h * t⁻¹ ∈ Q := by
    intro t ht h hh
    obtain ⟨hhU, hhp⟩ := (hQ h).1 hh
    rw [hQ]
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_set_normalizer_iff.1 (hTN (Subgroup.mem_comap.1 ht)) (π h)).1 hhU
      simpa [map_mul, map_inv] using this
    · have := conj_pow (a := t) (b := h) (i := p)
      rw [this, hhp]
      group
  let U : Subgroup (MulAut W) := Q.map L.subtype
  let T : Subgroup (MulAut W) := T'.map L.subtype
  have hUc' : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (hQc x hx y hy)
  have hUp' : ∀ a ∈ U, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hQp x hx, map_one]
  have hU' : U ≠ ⊥ := by
    intro h
    apply hQ1
    rw [eq_bot_iff]
    intro x hx
    have hxU : L.subtype x ∈ U := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hxU
    exact Subgroup.mem_bot.2 (L.subtype_injective (by rw [hxU, map_one]))
  have hTU : T ≤ Subgroup.normalizer (U : Set (MulAut W)) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨t * y * t⁻¹, hT'Q t ht y hy, by simp [map_mul, map_inv]⟩
    · rintro ⟨z, hz, hzeq⟩
      have hz' := hT'Q t⁻¹ (T'.inv_mem ht) z hz
      rw [inv_inv] at hz'
      refine ⟨t⁻¹ * z * t, hz', ?_⟩
      have : (L.subtype t)⁻¹ * (L.subtype z) * (L.subtype t) = h := by
        have hzeq' : L.subtype z = L.subtype t * h * (L.subtype t)⁻¹ := hzeq
        rw [hzeq']
        group
      simpa [map_mul, map_inv] using this
  have hfin : Finite (MulAut W) :=
    Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective
  have horb' : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T := by
    intro D hDU hrel
    let DQ : Subgroup ↥L := D.comap L.subtype
    have hDQD : DQ.map L.subtype = D :=
      Subgroup.map_comap_eq_self (hDU.trans (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩))
    have hDQQ : DQ ≤ Q := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hDU hx
      rwa [← L.subtype_injective hyx]
    have hrelQ : DQ.relIndex Q = p := by
      rw [← Subgroup.relIndex_map_map_of_injective DQ Q L.subtype_injective, hDQD]
      exact hrel
    let πQ : ↥Q →* S := π.comp Q.subtype
    have hπQ : Function.Injective πQ := fun a b h => Subtype.ext (hQinj a a.2 b b.2 h)
    have hrangeQ : πQ.range = U₀ := by
      ext u
      constructor
      · rintro ⟨x, rfl⟩
        exact ((hQ x).1 x.2).1
      · intro hu
        obtain ⟨x, hx, hxu⟩ := hQsurj u hu
        exact ⟨⟨x, hx⟩, hxu⟩
    let D₀ : Subgroup S := (DQ.subgroupOf Q).map πQ
    have hD₀U : D₀ ≤ U₀ := by
      rw [← hrangeQ]
      exact Subgroup.map_le_range _ _
    have hD₀rel : D₀.relIndex U₀ = p := by
      have h1 := Subgroup.relIndex_map_map_of_injective (DQ.subgroupOf Q) ⊤ hπQ
      rw [← MonoidHom.range_eq_map, hrangeQ, Subgroup.relIndex_top_right] at h1
      exact h1.trans hrelQ
    have hm := horb D₀ hD₀U hD₀rel
    refine hm.trans ?_
    let H₀ : Subgroup S := T₀ ⊓ Subgroup.normalizer (D₀ : Set S)
    let H₂ : Subgroup (MulAut W) := (H₀.comap π).map L.subtype
    have hsub : T ⊓ Subgroup.normalizer (D : Set (MulAut W)) ≤ H₂ := by
      rintro _ ⟨⟨t, ht, rfl⟩, hgN⟩
      refine ⟨t, ?_, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.1 ht, ?_⟩
      have hgN' := Subgroup.mem_set_normalizer_iff.1 hgN
      have hgNi := Subgroup.mem_set_normalizer_iff.1
        ((Subgroup.normalizer (D : Set (MulAut W))).inv_mem hgN)
      have hconj : ∀ x ∈ DQ, t * x * t⁻¹ ∈ DQ := by
        intro x hx
        have h' := (hgN' (L.subtype x)).1 hx
        show L.subtype (t * x * t⁻¹) ∈ D
        rw [map_mul, map_mul, map_inv]
        exact h'
      have hconj' : ∀ x ∈ DQ, t⁻¹ * x * t ∈ DQ := by
        intro x hx
        have h' := (hgNi (L.subtype x)).1 hx
        show L.subtype (t⁻¹ * x * t) ∈ D
        rw [map_mul, map_mul, map_inv] at *
        simpa using h'
      rw [Subgroup.mem_set_normalizer_iff]
      intro s
      constructor
      · rintro ⟨⟨x, hxQ⟩, hxD, rfl⟩
        have hxD' : x ∈ DQ := hxD
        have hy := hconj x hxD'
        refine ⟨⟨t * x * t⁻¹, hDQQ hy⟩, hy, ?_⟩
        show π (t * x * t⁻¹) = π t * π x * (π t)⁻¹
        simp [map_mul, map_inv]
      · rintro ⟨⟨y, hyQ⟩, hyD, hyeq⟩
        have hyD' : y ∈ DQ := hyD
        have hy := hconj' y hyD'
        refine ⟨⟨t⁻¹ * y * t, hDQQ hy⟩, hy, ?_⟩
        have hyeq' : π y = π t * s * (π t)⁻¹ := hyeq
        show π (t⁻¹ * y * t) = s
        rw [map_mul, map_mul, map_inv, hyeq']
        group
    have hH₂ : H₂.relIndex T = H₀.relIndex T₀ := by
      rw [Subgroup.relIndex_map_map_of_injective _ _ L.subtype_injective, Subgroup.relIndex_comap,
        Subgroup.map_comap_eq_self_of_surjective hπ]
    have hne : (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (T ⊓ Subgroup.normalizer (D : Set (MulAut W))) T
      rw [h0, zero_mul] at this
      exact (Nat.card_pos (α := T)).ne' this.symm
    calc H₀.relIndex T₀ = H₂.relIndex T := hH₂.symm
      _ ≤ _ := Subgroup.relIndex_le_of_le_left hsub hne
  have hker' := two_pow_le_card_ker_of_hyperplane_orbit hW hp2 hUc' hUp' hU' hTU horb'
  exact hker'.trans (Subgroup.card_le_card_group _)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
