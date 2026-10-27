module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

section Perfect

variable {L : Type*} [Group L]

theorem commutator_mul_center_right {a b z : L} (hz : z ∈ Subgroup.center L) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have h1 : z * a⁻¹ * z⁻¹ = a⁻¹ := by rw [← hz' a⁻¹]; group
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = ⁅a, b⁆ := by rw [h1, commutatorElement_def]

theorem commutator_mul_center_left {a b z : L} (hz : z ∈ Subgroup.center L) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have h1 : z * b * z⁻¹ = b := by rw [← hz' b]; group
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = ⁅a, b⁆ := by rw [h1, commutatorElement_def]

theorem eq_top_of_sup_center_eq_top (hperf : Group.IsPerfect L) {J : Subgroup L}
    (h : J ⊔ Subgroup.center L = ⊤) : J = ⊤ := by
  have hcomm : commutator L ≤ J := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    have h1 : g₁ ∈ J ⊔ Subgroup.center L := by rw [h]; exact hg₁
    have h2 : g₂ ∈ J ⊔ Subgroup.center L := by rw [h]; exact hg₂
    obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 h1
    obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 h2
    rw [commutator_mul_center_left hz₁, commutator_mul_center_right hz₂, commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
  rw [eq_top_iff, ← hperf.commutator_eq_top]
  exact hcomm

theorem closure_conj_eq_top_of_perfect {S : Type*} [Group S] (hperf : Group.IsPerfect L)
    (π : L →* S) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center L) (t : L)
    (cs : List S) (hgen : Subgroup.closure {x : S | ∃ c ∈ cs, x = c * π t * c⁻¹} = ⊤) :
    ∃ ls : List L, ls.length = cs.length ∧
      Subgroup.closure {x : L | ∃ c ∈ ls, x = c * t * c⁻¹} = ⊤ := by
  obtain ⟨ls, hls⟩ := (List.map_surjective_iff.2 hπ) cs
  refine ⟨ls, by rw [← hls, List.length_map], ?_⟩
  set J := Subgroup.closure {x : L | ∃ c ∈ ls, x = c * t * c⁻¹} with hJ
  have hmap : J.map π = ⊤ := by
    rw [hJ, MonoidHom.map_closure, ← hgen]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨π c, by rw [← hls]; exact List.mem_map_of_mem hc, by simp⟩
    · rintro ⟨_, hc, rfl⟩
      rw [← hls] at hc
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
      exact ⟨c * t * c⁻¹, ⟨c, hc', rfl⟩, by simp⟩
  have hsup : J ⊔ Subgroup.center L = ⊤ := by
    rw [← hker, ← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  exact eq_top_of_sup_center_eq_top hperf hsup

end Perfect

section Gen

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem card_le_index_pow_of_generation {L : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hL : L ≠ ⊥) {S : Type} [Group S] (e : CQ L ≃* S) {b : MulAut W}
    (hb : b ∈ L) (cs : List S)
    (hgen : Subgroup.closure {x : S | ∃ c ∈ cs,
      x = c * e (QuotientGroup.mk ⟨b, hb⟩) * c⁻¹} = ⊤) :
    Nat.card W ≤ (fixV (Subgroup.zpowers b)).index ^ cs.length := by
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    simp [π]
  obtain ⟨ls, hlen, hls⟩ := closure_conj_eq_top_of_perfect hperf π hπ hker ⟨b, hb⟩ cs hgen
  set bs : List (MulAut W) :=
    ls.map (fun c : ↥L => (c : MulAut W) * b * (c : MulAut W)⁻¹) with hbs
  have hcl : Subgroup.closure {x : MulAut W | x ∈ bs} = L := by
    have h1 := congrArg (Subgroup.map L.subtype) hls
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype] at h1
    rw [← h1]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, hbs, List.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c * ⟨b, hb⟩ * c⁻¹, ⟨c, hc, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, rfl⟩
  have hidx : (fixV L).index = Nat.card W := by
    rw [fixV_eq_bot_of_irr hirr hL, Subgroup.index_bot]
  rw [← hidx, ← hcl]
  refine (index_fixV_closure_le bs).trans ?_
  have hrep : bs.map (fun x => (fixV (Subgroup.zpowers x)).index) =
      List.replicate cs.length (fixV (Subgroup.zpowers b)).index := by
    rw [hbs, List.map_map, ← hlen, List.map_eq_replicate_iff]
    intro x hx
    exact index_fixV_conj (x : MulAut W) b
  rw [hrep, List.prod_replicate]

theorem two_pow_le_index_sq_of_dihedral (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    {S : Type} [Group S] (e : CQ L ≃* S) {b : MulAut W} (hb : b ∈ L) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (c : S)
    (hc : orderOf (e (QuotientGroup.mk ⟨b, hb⟩) * (c * e (QuotientGroup.mk ⟨b, hb⟩) * c⁻¹)) = p) :
    2 ^ orderOf (2 : ZMod p) ≤ (fixV (Subgroup.zpowers b)).index ^ 2 := by
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨c', rfl⟩ := hπ c
  set t : ↥L := ⟨b, hb⟩ with ht
  set u : ↥L := t * (c' * t * c'⁻¹) with hu
  have hπu : π u = e (QuotientGroup.mk t) * (π c' * e (QuotientGroup.mk t) * (π c')⁻¹) := by
    simp [π, hu]
  have hpu : p ∣ orderOf u := by
    have := orderOf_map_dvd π u
    rw [hπu, hc] at this
    exact this
  obtain ⟨j, hj⟩ := hpu
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, mul_zero] at hj
      exact absurd hj (orderOf_pos u).ne'
    · exact h0
  have hord : orderOf (u ^ j) = p := by
    rw [orderOf_pow_of_dvd hjpos.ne' ⟨p, by rw [hj, mul_comm]⟩, hj, Nat.mul_div_cancel _ hjpos]
  have hordW : orderOf (((u ^ j : ↥L)) : MulAut W) = p := by
    rw [Subgroup.orderOf_coe, hord]
  have h1 := two_pow_orderOf_le_index_fixV hW hp2 hordW
  have h2 : (fixV (Subgroup.zpowers (((u ^ j : ↥L)) : MulAut W))).index ≤
      (fixV (Subgroup.zpowers (u : MulAut W))).index := by
    have := index_fixV_pow_le (u : MulAut W) j
    simpa using this
  have h3 : (fixV (Subgroup.zpowers (u : MulAut W))).index ≤
      (fixV (Subgroup.zpowers b)).index * (fixV (Subgroup.zpowers b)).index := by
    have := index_fixV_mul_le b ((c' : MulAut W) * b * (c' : MulAut W)⁻¹)
    rw [index_fixV_conj] at this
    simpa [hu, ht] using this
  rw [sq]
  exact h1.trans (h2.trans h3)

theorem two_pow_le_card_of_dvd (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} {S : Type}
    [Group S] (e : CQ L ≃* S) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpS : p ∣ Nat.card S) : 2 ^ orderOf (2 : ZMod p) ≤ Nat.card W := by
  have h1 : p ∣ Nat.card (CQ L) := by rw [Nat.card_congr e.toEquiv]; exact hpS
  have h2 : Nat.card (CQ L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (h1.trans h2)
  have hxW : orderOf (x : MulAut W) = p := by rw [Subgroup.orderOf_coe, hx]
  exact (two_pow_orderOf_le_index_fixV hW hp2 hxW).trans (index_fixV_le_card _)

theorem two_pow_le_of_pow_le {idx k δ ρ : ℕ} (hidx : ∃ m, idx = 2 ^ m)
    (h : 2 ^ δ ≤ idx ^ k) (hρ : k * ρ < δ + k) : 2 ^ ρ ≤ idx := by
  obtain ⟨m, rfl⟩ := hidx
  rw [← pow_mul] at h
  have h1 : δ ≤ m * k := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have h2 : ρ ≤ m := by
    by_contra hcon
    push Not at hcon
    nlinarith
  exact Nat.pow_le_pow_right (by norm_num) h2

theorem rank_of_generation (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥) {S : Type} [Group S]
    (e : CQ L ≃* S) {k ρ p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S)
    (hρ : k * ρ < orderOf (2 : ZMod p) + k)
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ cs : List S, cs.length = k ∧
      Subgroup.closure {x : S | ∃ c ∈ cs, x = c * t * c⁻¹} = ⊤) :
    ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index := by
  intro b hb hb1 hb2
  have ht2 : e (QuotientGroup.mk ⟨b, hb⟩) * e (QuotientGroup.mk ⟨b, hb⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← map_one e, ← QuotientGroup.mk_one]
    congr 2
    exact Subtype.ext hb2
  have ht1 : e (QuotientGroup.mk ⟨b, hb⟩) ≠ 1 := by
    intro h
    apply hb1
    have h1 : (QuotientGroup.mk (⟨b, hb⟩ : ↥L) : CQ L) = 1 := e.injective (by rw [h, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    refine eq_one_of_commutes_of_sq_eq_one hW hirr (fun l hl => ?_) hb2
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨l, hl⟩)
  obtain ⟨cs, hcs, hgen'⟩ := hgen _ ht2 ht1
  have hk : 2 ^ orderOf (2 : ZMod p) ≤ Nat.card W := two_pow_le_card_of_dvd hW e hp2 hpS
  have h1 := card_le_index_pow_of_generation hperf hirr hL e hb cs hgen'
  rw [hcs] at h1
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) (hk.trans h1) hρ

theorem rank_of_dihedral (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {S : Type} [Group S]
    (e : CQ L ≃* S) {ρ p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hρ : 2 * ρ < orderOf (2 : ZMod p) + 2)
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ c : S, orderOf (t * (c * t * c⁻¹)) = p) :
    ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index := by
  intro b hb hb1 hb2
  have ht2 : e (QuotientGroup.mk ⟨b, hb⟩) * e (QuotientGroup.mk ⟨b, hb⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← map_one e, ← QuotientGroup.mk_one]
    congr 2
    exact Subtype.ext hb2
  have ht1 : e (QuotientGroup.mk ⟨b, hb⟩) ≠ 1 := by
    intro h
    apply hb1
    have h1 : (QuotientGroup.mk (⟨b, hb⟩ : ↥L) : CQ L) = 1 := e.injective (by rw [h, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    refine eq_one_of_commutes_of_sq_eq_one hW hirr (fun l hl => ?_) hb2
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨l, hl⟩)
  obtain ⟨c, hc⟩ := hgen _ ht2 ht1
  have h1 := two_pow_le_index_sq_of_dihedral hW e hb hp2 c hc
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h1 hρ

theorem exclusion_of_autInner_le (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) {r ρ : ℕ} (hρ : r ≤ ρ)
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hrank : ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index) :
    2 ^ (ρ - r) * (Nat.card E * Nat.card (fixV E)) ≤ Nat.card W := by
  have hEL : E ≤ L := le_of_autInner hW hperf hirr hE hEel e hAut
  have hcard := card_le_two_pow_of_le hW hirr hEL hEel e hr
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : b * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  have h2 := hrank b (hEL hbE) hb1' hb2
  have h3 : (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index := by
    apply Subgroup.index_antitone
    apply fixV_anti
    rw [Subgroup.zpowers_le]
    exact hbE
  have h4 : 2 ^ (ρ - r) * Nat.card E ≤ (fixV E).index := by
    calc 2 ^ (ρ - r) * Nat.card E ≤ 2 ^ (ρ - r) * 2 ^ r := Nat.mul_le_mul_left _ hcard
      _ = 2 ^ ρ := by rw [← pow_add]; congr 1; omega
      _ ≤ (fixV E).index := h2.trans h3
  calc 2 ^ (ρ - r) * (Nat.card E * Nat.card (fixV E))
      = (2 ^ (ρ - r) * Nat.card E) * Nat.card (fixV E) := by ring
    _ ≤ (fixV E).index * Nat.card (fixV E) := Nat.mul_le_mul_right _ h4
    _ = Nat.card W := by rw [mul_comm, Subgroup.card_mul_index]

theorem exclusion_of_autInner (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S)
    (hAut : ∀ φ : S ≃* S, ∃ s : S, ∀ x, φ x = s * x * s⁻¹) {r ρ : ℕ} (hρ : r < ρ)
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hrank : ∀ b : MulAut W, b ∈ L → b ≠ 1 → b * b = 1 →
      2 ^ ρ ≤ (fixV (Subgroup.zpowers b)).index) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have h := exclusion_of_autInner_le hW hperf hirr hE hEne hEel e hAut hρ.le hr hrank
  have h2 : 2 ≤ 2 ^ (ρ - r) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (ρ - r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < Nat.card E * Nat.card (fixV E) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  nlinarith

end Gen

end CFSG.QuasithinUnique.Setup.X1
