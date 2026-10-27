module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnLift

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

section Main

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

open scoped Classical in
theorem two_pow_le_card_ker_of_hyperplane_orbit_rel (hW : ∀ w : W, w * w = 1) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {U T Z : Subgroup (MulAut W)}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUp : ∀ a ∈ U, a ^ p = 1)
    (hZU : Z ≤ U) (hZ : Z ≠ ⊥)
    (hTU : T ≤ Subgroup.normalizer (U : Set (MulAut W))) {m : ℕ}
    (horb : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p → ¬ Z ≤ D →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card (normHom U).ker := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hUodd : Odd (Nat.card U) := odd_card_of_pow_eq_one hodd hUp
  set K : Subgroup W := (normHom U).ker with hK
  have hKU : ∀ a ∈ U, ∀ k ∈ K, a k ∈ K := fun a ha k hk =>
    map_ker_normHom (Subgroup.le_normalizer ha) hk
  have hKT : ∀ t ∈ T, ∀ k ∈ K, t k ∈ K := fun t ht k hk => map_ker_normHom (hTU ht) hk
  have hfix : fixV U ⊓ K = ⊥ := fixV_inf_ker_normHom hW hUodd
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    Finset.univ.filter (fun D => D ≤ U ∧ D.relIndex U = p)
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ U ∧ D.relIndex U = p := fun D => by simp [𝒟]
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
  have hzU : z ∈ U := hZU hzZ
  obtain ⟨w, hw⟩ : ∃ w : W, z w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hz1
    apply Subtype.ext
    apply DFunLike.ext
    intro w
    exact hcon w
  obtain ⟨f, hfdef⟩ : ∃ f : W, f = normHom U w := ⟨_, rfl⟩
  have hfU : f ∈ fixV U := hfdef ▸ normHom_mem_fixV U w
  have hnf : normHom U f = f := normHom_of_mem_fixV hW hUodd hfU
  obtain ⟨k, hk⟩ : ∃ k : W, k = w * f⁻¹ := ⟨_, rfl⟩
  have hkK : k ∈ K := by
    rw [hK, MonoidHom.mem_ker, hk, map_mul, map_inv, hnf, ← hfdef, mul_inv_cancel]
  have hzf : z f = f := mem_fixV.1 hfU z hzU
  have hzk : z k ≠ k := by
    intro h
    apply hw
    have e1 : z k = z w * f⁻¹ := by rw [hk, map_mul, map_inv, hzf]
    rw [e1, hk] at h
    exact mul_right_cancel h
  obtain ⟨D₀, hD₀𝒟, hD₀ne, hD₀Z⟩ : ∃ D ∈ 𝒟, fixV D ⊓ K ≠ ⊥ ∧ ¬ Z ≤ D := by
    by_contra hcon
    push Not at hcon
    apply hzk
    obtain ⟨x, hx⟩ := hyperplaneHom_surjective hW hp2 hUc hUp hKU hfix 𝒟 h𝒟 hkK
    rw [← hx, hyperplaneHom_apply, map_prod]
    refine Finset.prod_congr rfl fun D _ => ?_
    by_cases hD : fixV (D : Subgroup (MulAut W)) ⊓ K = ⊥
    · have hall : ∀ y : W, y ∈ fixV (D : Subgroup (MulAut W)) ⊓ K → y = 1 := fun y hy => by
        rw [hD] at hy
        exact Subgroup.mem_bot.1 hy
      rw [hall _ (x D).2, map_one]
    · exact mem_fixV.1 (Subgroup.mem_inf.1 (x D).2).1 z (hcon D D.2 hD hzZ)
  have hcardK := card_eq_prod_card_fixV_inf_hyperplanes hW hp2 hUc hUp hKU hfix 𝒟 h𝒟
  obtain ⟨hD₀U, hD₀rel⟩ := (h𝒟 D₀).1 hD₀𝒟
  let 𝒟g : Finset (Subgroup (MulAut W)) := 𝒟.filter (fun D => fixV D ⊓ K ≠ ⊥)
  have hD₀cardpos : 0 < Nat.card D₀ := Nat.card_pos
  have hpD₀ : p * Nat.card D₀ = Nat.card U := by
    have := D₀.relIndex_mul_card U
    rwa [hD₀rel, inf_eq_left.2 hD₀U] at this
  have hconj : ∀ t ∈ T, conjSub t D₀ ∈ 𝒟g := by
    intro t ht
    have htN := hTU ht
    have hle : conjSub t D₀ ≤ U := by
      intro x hx
      rw [mem_conjSub] at hx
      have h1 := hD₀U hx
      have := (Subgroup.mem_set_normalizer_iff.1 htN (t⁻¹ * x * t)).1 h1
      have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [e] at this
    have hrel : (conjSub t D₀).relIndex U = p := by
      have h1 := (conjSub t D₀).relIndex_mul_card U
      rw [inf_eq_left.2 hle, card_conjSub] at h1
      exact Nat.eq_of_mul_eq_mul_right hD₀cardpos (h1.trans hpD₀.symm)
    refine Finset.mem_filter.2 ⟨(h𝒟 _).2 ⟨hle, hrel⟩, ?_⟩
    obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD₀ne
    obtain ⟨hkD, hkK⟩ := Subgroup.mem_inf.1 hk
    apply Subgroup.ne_bot_iff_exists_ne_one.2
    refine ⟨⟨t k, Subgroup.mem_inf.2 ⟨?_, hKT t ht k hkK⟩⟩, ?_⟩
    · rw [mem_fixV]
      intro x hx
      rw [mem_conjSub] at hx
      have hcomm : x * t = t * (t⁻¹ * x * t) := by group
      have hy : (t⁻¹ * x * t) k = k := mem_fixV.1 hkD _ hx
      calc x (t k) = (x * t) k := rfl
        _ = (t * (t⁻¹ * x * t)) k := by rw [hcomm]
        _ = t ((t⁻¹ * x * t) k) := rfl
        _ = t k := by rw [hy]
    · intro h1
      apply hk1
      have h2 : (t : MulAut W) k = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      show k = 1
      have : (t : MulAut W) k = (t : MulAut W) 1 := by rw [h2, map_one]
      exact (t : MulAut W).injective this
  have hm : m ≤ 𝒟g.card :=
    (horb D₀ hD₀U hD₀rel hD₀Z).trans (relIndex_le_card_of_conj hconj)
  have hfac : ∀ D ∈ 𝒟g, 2 ^ orderOf (2 : ZMod p) ≤ Nat.card ↥(fixV D ⊓ K) := by
    intro D hD
    obtain ⟨hD𝒟, hDne⟩ := Finset.mem_filter.1 hD
    obtain ⟨hDU, hDrel⟩ := (h𝒟 D).1 hD𝒟
    exact two_pow_le_card_fixV_inf hW hUc hUp hKU hfix hDU hDrel hDne
  have hpos : ∀ D ∈ 𝒟, 0 < Nat.card ↥(fixV D ⊓ K) := fun D _ => Nat.card_pos
  calc 2 ^ (m * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ m := by
        rw [mul_comm, pow_mul]
    _ ≤ (2 ^ orderOf (2 : ZMod p)) ^ 𝒟g.card :=
        Nat.pow_le_pow_right (Nat.one_le_two_pow) hm
    _ = ∏ _D ∈ 𝒟g, 2 ^ orderOf (2 : ZMod p) := by rw [Finset.prod_const]
    _ ≤ ∏ D ∈ 𝒟g, Nat.card ↥(fixV D ⊓ K) := Finset.prod_le_prod hfac
    _ ≤ (∏ D ∈ 𝒟g, Nat.card ↥(fixV D ⊓ K)) *
          ∏ D ∈ 𝒟.filter (fun D => ¬ (fixV D ⊓ K ≠ ⊥)), Nat.card ↥(fixV D ⊓ K) :=
        Nat.le_mul_of_pos_right _ (Finset.prod_pos fun D hD => hpos D (Finset.mem_filter.1 hD).1)
    _ = ∏ D ∈ 𝒟, Nat.card ↥(fixV D ⊓ K) := Finset.prod_filter_mul_prod_filter_not 𝒟 (fun D => fixV D ⊓ K ≠ ⊥)
        (fun D => Nat.card ↥(fixV D ⊓ K))
    _ = Nat.card K := hcardK.symm

end Main

section Lift

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_lift_orbit_rel (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hKp : ¬ p ∣ Nat.card π.ker) {Z U₀ T₀ : Subgroup S} (hZU : Z ≤ U₀) (hZ : Z ≠ ⊥)
    (hUc : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a) (hUp : ∀ a ∈ U₀, a ^ p = 1)
    (hTN : T₀ ≤ Subgroup.normalizer (U₀ : Set S)) {m : ℕ}
    (horb : ∀ D₀ : Subgroup S, D₀ ≤ U₀ → D₀.relIndex U₀ = p → ¬ Z ≤ D₀ →
      m ≤ (T₀ ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex T₀) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  classical
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hcomm : ∀ {a b : ↥L}, a ^ p = 1 → π a * π b = π b * π a → a * b = b * a :=
    fun ha hab => CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.commute_of_map_of_pow_eq_one π hker hKp ha hab
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
  let ZQ : Subgroup ↥L := Q ⊓ Z.comap π
  let Z' : Subgroup (MulAut W) := ZQ.map L.subtype
  have hZ'U : Z' ≤ U := Subgroup.map_mono inf_le_left
  have hZ' : Z' ≠ ⊥ := by
    intro h
    obtain ⟨⟨u, huZ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ
    obtain ⟨x, hxQ, hxu⟩ := hQsurj u (hZU huZ)
    have hxZ' : L.subtype x ∈ Z' :=
      ⟨x, Subgroup.mem_inf.2 ⟨hxQ, Subgroup.mem_comap.2 (hxu ▸ huZ)⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hxZ'
    apply hu1
    apply Subtype.ext
    show u = 1
    rw [← hxu, L.subtype_injective (hxZ'.trans (map_one L.subtype).symm), map_one]
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
  have horb' : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = p → ¬ Z' ≤ D →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T := by
    intro D hDU hrel hZD
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
    have hD₀Z : ¬ Z ≤ D₀ := by
      intro hZD₀
      apply hZD
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨q', hq'D, hq'⟩ := hZD₀ (Subgroup.mem_comap.1 hxZ)
      have hq'x : (q' : ↥L) = x :=
        hQinj q' q'.2 x hxQ (by simpa [πQ] using hq')
      have : x ∈ DQ := hq'x ▸ hq'D
      exact this
    have hm := horb D₀ hD₀U hD₀rel hD₀Z
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
  have hker' := two_pow_le_card_ker_of_hyperplane_orbit_rel hW hp2 hUc' hUp' hZ'U hZ' hTU horb'
  exact hker'.trans (Subgroup.card_le_card_group _)
end Lift

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
