module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDichotomy

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)

section Comm

variable {G : Type} [Group G] {A : Subgroup G}

theorem commute_of_sq_eq_one'
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {d b : G} (hd : d ∈ A) (hb : b ∈ A) (hb2 : b ^ 2 = 1)
    (hc : d * b * d⁻¹ * b⁻¹ ∈ centralizer (A : Set G)) : d * b = b * d := by
  set c := d * b * d⁻¹ * b⁻¹ with hcdef
  have hcA : c ∈ A := mul_mem (mul_mem (mul_mem hd hb) (inv_mem hd)) (inv_mem hb)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb2])
  have hcb : Commute c b := (mem_centralizer_iff.1 hc b hb).symm
  have h1 : d * b * d⁻¹ = c * b := by
    rw [hcdef, hbi, mul_assoc _ b b, ← sq, hb2, mul_one]
  have hsq : c ^ 2 = 1 := by
    have h2 : (c * b) ^ 2 = 1 := by rw [← h1, conj_pow, hb2, mul_one, mul_inv_cancel]
    rwa [hcb.mul_pow, hb2, mul_one] at h2
  have h3 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨hcA, hc⟩)) (k := 1)
    (by rw [pow_one]; exact hsq)
  calc d * b = c * (b * d) := by rw [hcdef]; group
    _ = b * d := by rw [h3, one_mul]

variable {C : Type} [Group C] {ψ : normalizer (A : Set G) →* MulAut C}

theorem commute_of_conj_commute (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {d b : G} (hd : d ∈ A) (hb : b ∈ A) (hb2 : b ^ 2 = 1) {x y : C}
    (hdx : ψ ⟨d, le_normalizer hd⟩ = MulAut.conj x) (hby : ψ ⟨b, le_normalizer hb⟩ = MulAut.conj y)
    (hxy : x * y = y * x) : d * b = b * d := by
  have hN : d * b * d⁻¹ * b⁻¹ ∈ normalizer (A : Set G) :=
    le_normalizer (mul_mem (mul_mem (mul_mem hd hb) (inv_mem hd)) (inv_mem hb))
  refine commute_of_sq_eq_one' hZ hd hb hb2 ((hψ.eq_one_iff ⟨_, hN⟩).1 ?_)
  have e : (⟨d * b * d⁻¹ * b⁻¹, hN⟩ : normalizer (A : Set G)) =
      ⟨d, le_normalizer hd⟩ * ⟨b, le_normalizer hb⟩ * ⟨d, le_normalizer hd⟩⁻¹ *
        ⟨b, le_normalizer hb⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hdx, hby, ← map_mul, ← map_inv, ← map_mul,
    ← map_inv, ← map_mul, show x * y * x⁻¹ * y⁻¹ = 1 by rw [hxy]; group, map_one]

end Comm

section Lift2

variable {G : Type} [Group G] {A : Subgroup G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}

@[expose] def lift2 (ψ : normalizer (A : Set G) →* MulAut C) (U : Subgroup C) : Subgroup G :=
  closure {a | ∃ ha : a ∈ A, a ^ 2 = 1 ∧ ∃ y ∈ U, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y}

theorem lift2_le {U : Subgroup C} : lift2 ψ U ≤ A :=
  (closure_le A).2 fun _ ⟨ha, _⟩ => ha

theorem mem_lift2_of {U : Subgroup C} {a : G} (ha : a ∈ A) (h2 : a ^ 2 = 1) {y : C} (hy : y ∈ U)
    (hay : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y) : a ∈ lift2 ψ U :=
  subset_closure ⟨ha, h2, y, hy, hay⟩

variable (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
  (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
  {U : Subgroup C} (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
include hψ hZ hUc

theorem mem_lift2 {a : G} :
    a ∈ lift2 ψ U ↔ ∃ ha : a ∈ A, a ^ 2 = 1 ∧ ∃ y ∈ U, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y := by
  refine ⟨fun h => ?_, fun ⟨ha, h2, y, hy, hay⟩ => mem_lift2_of ha h2 hy hay⟩
  induction h using closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem A, one_pow 2, 1, one_mem U, by rw [map_one]; exact map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hxA, hx2, u, huU, hu⟩ := hx
    obtain ⟨hyA, hy2, v, hvU, hv⟩ := hy
    have hcomm : x * y = y * x := commute_of_conj_commute hψ hZ hxA hyA hy2 hu hv (hUc u huU v hvU)
    refine ⟨mul_mem hxA hyA, ?_, u * v, mul_mem huU hvU, ?_⟩
    · rw [(Commute.mul_pow hcomm 2 : (x * y) ^ 2 = x ^ 2 * y ^ 2), hx2, hy2, one_mul]
    · have e : (⟨x * y, le_normalizer (mul_mem hxA hyA)⟩ : normalizer (A : Set G)) =
          ⟨x, le_normalizer hxA⟩ * ⟨y, le_normalizer hyA⟩ := rfl
      rw [e, map_mul, hu, hv, map_mul]
  | inv x _ hx =>
    obtain ⟨hxA, hx2, u, huU, hu⟩ := hx
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
    rw [hxi]
    exact ⟨hxA, hx2, u, huU, hu⟩

theorem sq_eq_one_of_mem_lift2 {a : G} (ha : a ∈ lift2 ψ U) : a ^ 2 = 1 :=
  ((mem_lift2 hψ hZ hUc).1 ha).2.1

theorem exists_of_mem_lift2 {a : G} (ha : a ∈ lift2 ψ U) :
    ∃ y ∈ U, ψ ⟨a, le_normalizer (lift2_le ha)⟩ = MulAut.conj y := by
  obtain ⟨haA, -, y, hy, hay⟩ := (mem_lift2 hψ hZ hUc).1 ha
  exact ⟨y, hy, hay⟩

omit hUc in
theorem eq_of_sq_eq_one' {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (h : ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩) : a = b :=
  eq_of_psi_eq hψ hZ ha hb (k := 1) (by rw [pow_one]; exact ha2) (by rw [pow_one]; exact hb2) h

theorem eq_of_mem_lift2 {a b : G} (ha : a ∈ lift2 ψ U) (hb : b ∈ lift2 ψ U)
    (h : ψ ⟨a, le_normalizer (lift2_le ha)⟩ = ψ ⟨b, le_normalizer (lift2_le hb)⟩) : a = b :=
  eq_of_sq_eq_one' hψ hZ (lift2_le ha) (lift2_le hb) (sq_eq_one_of_mem_lift2 hψ hZ hUc ha)
    (sq_eq_one_of_mem_lift2 hψ hZ hUc hb) h

omit hUc in
theorem exists_sq_eq_one_of_sq' (y : C) (hy2 : y ^ 2 = 1) :
    ∃ a : G, ∃ ha : a ∈ A, a ^ 2 = 1 ∧ ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y := by
  obtain ⟨a₀, ha₀, h₀⟩ := hψ.exists_eq (MulAut.conj y) ⟨y, rfl⟩
  set m := Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) with hm
  obtain ⟨k, hk⟩ := hZ
  have ha₀N := le_normalizer ha₀
  have hsqN : a₀ ^ 2 ∈ normalizer (A : Set G) := pow_mem ha₀N 2
  have hsqZ : a₀ ^ 2 ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨pow_mem ha₀ 2, (hψ.eq_one_iff ⟨_, hsqN⟩).1 ?_⟩
    have e : (⟨a₀ ^ 2, hsqN⟩ : normalizer (A : Set G)) = ⟨a₀, ha₀N⟩ ^ 2 := rfl
    rw [e, map_pow, h₀, ← map_pow, hy2, map_one]
  have hpow : (a₀ ^ 2) ^ m = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hsqZ)
  refine ⟨a₀ ^ m, pow_mem ha₀ m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hpow]
  · have e : (⟨a₀ ^ m, le_normalizer (pow_mem ha₀ m)⟩ : normalizer (A : Set G)) =
        ⟨a₀, ha₀N⟩ ^ m := rfl
    rw [e, map_pow, h₀, ← map_pow, hk, pow_succ, pow_mul, hy2, one_pow, one_mul]

omit hUc in
theorem exists_mem_lift2 (hU2 : ∀ u ∈ U, u ^ 2 = 1) {y : C} (hy : y ∈ U) :
    ∃ a, ∃ ha : a ∈ lift2 ψ U, ψ ⟨a, le_normalizer (lift2_le ha)⟩ = MulAut.conj y := by
  obtain ⟨a, haA, ha2, hay⟩ := exists_sq_eq_one_of_sq' hψ hZ y (hU2 y hy)
  exact ⟨a, mem_lift2_of haA ha2 hy hay, hay⟩

theorem mem_normalizer_lift2 {n : G} (hn : n ∈ normalizer (A : Set G))
    (h : ∀ y : C, y ∈ U ↔ ψ ⟨n, hn⟩ y ∈ U) : n ∈ normalizer (lift2 ψ U : Set G) := by
  have key : ∀ (m : G) (hm : m ∈ normalizer (A : Set G)),
      (∀ y : C, y ∈ U → ψ ⟨m, hm⟩ y ∈ U) → ∀ a ∈ lift2 ψ U, m * a * m⁻¹ ∈ lift2 ψ U := by
    intro m hm hmU a ha
    obtain ⟨haA, ha2, y, hy, hay⟩ := (mem_lift2 hψ hZ hUc).1 ha
    have hmaA : m * a * m⁻¹ ∈ A := (mem_normalizer_iff.1 hm a).1 haA
    refine mem_lift2_of hmaA ?_ (hmU y hy) ?_
    · rw [conj_pow, ha2, mul_one, mul_inv_cancel]
    · have e : (⟨m * a * m⁻¹, le_normalizer hmaA⟩ : normalizer (A : Set G)) =
          ⟨m, hm⟩ * ⟨a, le_normalizer haA⟩ * ⟨m, hm⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hay, RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv]
  refine mem_normalizer_iff.2 fun a => ⟨key n hn (fun y hy => (h y).1 hy) a, fun ha => ?_⟩
  have hn' : n⁻¹ ∈ normalizer (A : Set G) := inv_mem hn
  have hU' : ∀ y : C, y ∈ U → ψ ⟨n⁻¹, hn'⟩ y ∈ U := by
    intro y hy
    have e : (⟨n⁻¹, hn'⟩ : normalizer (A : Set G)) = (⟨n, hn⟩ : normalizer (A : Set G))⁻¹ := rfl
    rw [e, map_inv]
    refine (h _).2 ?_
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    exact hy
  have := key n⁻¹ hn' hU' _ ha
  rwa [inv_inv, show n⁻¹ * (n * a * n⁻¹) * n = a by group] at this

end Lift2

section ConjData

variable {C : Type*} [Group C]

theorem mem_map_conj_iff {Z : Subgroup C} {c w : C} :
    w ∈ Z.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * w * c ∈ Z := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_normalizer_map_conj_iff {Z : Subgroup C} {c a : C} :
    a ∈ normalizer (Z.map (MulAut.conj c).toMonoidHom : Set C) ↔
      c⁻¹ * a * c ∈ normalizer (Z : Set C) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h w
    have h1 := h (c * w * c⁻¹)
    rw [mem_map_conj_iff, mem_map_conj_iff] at h1
    simpa [mul_assoc] using h1
  · intro h w
    have h1 := h (c⁻¹ * w * c)
    rw [mem_map_conj_iff, mem_map_conj_iff]
    simpa [mul_assoc] using h1

theorem mem_centralizer_map_conj_iff {Z : Subgroup C} {c a : C} :
    a ∈ centralizer (Z.map (MulAut.conj c).toMonoidHom : Set C) ↔
      c⁻¹ * a * c ∈ centralizer (Z : Set C) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h w hw
    have hw' : c * w * c⁻¹ ∈ Z.map (MulAut.conj c).toMonoidHom := by
      rw [mem_map_conj_iff]
      simpa [mul_assoc] using hw
    have h1 := h _ hw'
    calc w * (c⁻¹ * a * c) = c⁻¹ * (c * w * c⁻¹ * a) * c := by group
      _ = c⁻¹ * (a * (c * w * c⁻¹)) * c := by rw [h1]
      _ = c⁻¹ * a * c * w := by group
  · intro h w hw
    have hw' : c⁻¹ * w * c ∈ Z := mem_map_conj_iff.1 hw
    have h1 := h _ hw'
    calc w * a = c * ((c⁻¹ * w * c) * (c⁻¹ * a * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * a * c) * (c⁻¹ * w * c)) * c⁻¹ := by rw [h1]
      _ = a * w := by group

theorem CentreData.conj {x : C} {Z : Subgroup C} (h : CentreData x Z) (c : C) :
    CentreData (c * x * c⁻¹) (Z.map (MulAut.conj c).toMonoidHom) := by
  have hZ := zx_eq_of_centreData h
  have hx2 : x * x = 1 := by rw [← sq]; exact h.elem.2 x h.mem
  have h1 : zx (c * x * c⁻¹) = Z.map (MulAut.conj c).toMonoidHom := by rw [zx_conj, hZ]
  have hx2' : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  rw [← h1]
  refine ⟨mem_zx hx2', fun h0 => h.ne_one ?_, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun w hw => ?_⟩,
    fun w hw => hw.1, fun w hw d hd => hw.2.1 d hd, fun w hw hwc hw2 => ⟨hw, hwc, hw2⟩⟩
  · calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h0]; group
  · exact a.2.2.1 b b.2.1
  · rw [sq]
    exact hw.2.2

theorem Regular.conj {Z : Subgroup C} {u : C} (h : Regular Z u) (c : C) :
    Regular (Z.map (MulAut.conj c).toMonoidHom) (c * u * c⁻¹) := by
  refine ⟨?_, ?_, fun j hj hj1 j' hj' hj'1 => ?_, fun a ha j hj hj1 haj => ?_, fun a ha => ?_⟩
  · rw [mem_normalizer_map_conj_iff, show c⁻¹ * (c * u * c⁻¹) * c = u by group]
    exact h.y_mem
  · rw [show c * u * c⁻¹ = MulAut.conj c u from rfl, MulEquiv.orderOf_eq]
    exact h.odd
  · rw [mem_map_conj_iff] at hj hj'
    obtain ⟨a, ha, hak⟩ := h.trans _ hj (fun h0 => hj1 (by
      calc j = c * (c⁻¹ * j * c) * c⁻¹ := by group
        _ = 1 := by rw [h0]; group)) _ hj' (fun h0 => hj'1 (by
      calc j' = c * (c⁻¹ * j' * c) * c⁻¹ := by group
        _ = 1 := by rw [h0]; group))
    refine ⟨c * a * c⁻¹, ?_, ?_⟩
    · rw [mem_normalizer_map_conj_iff, show c⁻¹ * (c * a * c⁻¹) * c = a by group]
      exact ha
    · calc c * a * c⁻¹ * j * (c * a * c⁻¹)⁻¹ = c * (a * (c⁻¹ * j * c) * a⁻¹) * c⁻¹ := by group
        _ = c * (c⁻¹ * j' * c) * c⁻¹ := by rw [hak]
        _ = j' := by group
  · rw [mem_normalizer_map_conj_iff] at ha
    rw [mem_map_conj_iff] at hj
    rw [mem_centralizer_map_conj_iff]
    refine h.free _ ha _ hj (fun h0 => hj1 (by
      calc j = c * (c⁻¹ * j * c) * c⁻¹ := by group
        _ = 1 := by rw [h0]; group)) ?_
    calc c⁻¹ * a * c * (c⁻¹ * j * c) * (c⁻¹ * a * c)⁻¹ = c⁻¹ * (a * j * a⁻¹) * c := by group
      _ = c⁻¹ * j * c := by rw [haj]
  · rw [mem_normalizer_map_conj_iff] at ha
    obtain ⟨k, hk⟩ := h.cyclic _ ha
    refine ⟨k, ?_⟩
    rw [mem_centralizer_map_conj_iff]
    have e : c⁻¹ * (((c * u * c⁻¹) ^ k)⁻¹ * a) * c = (u ^ k)⁻¹ * (c⁻¹ * a * c) := by
      rw [conj_pow]
      group
    rw [e]
    exact hk

theorem SylowData.conj {x : C} {Z : Subgroup C} (h : SylowData x Z) (c : C) :
    SylowData (c * x * c⁻¹) (Z.map (MulAut.conj c).toMonoidHom) := by
  intro w hw hwc hw2
  rw [mem_map_conj_iff]
  refine h _ ?_ (fun b hb => ?_) ?_
  · rw [cent_conj, mem_map_equiv, MulAut.conj_symm_apply] at hw
    exact hw
  · have hb' : (c * b * c⁻¹) * (c * x * c⁻¹) * (c * b * c⁻¹)⁻¹ ∈ cent (c * x * c⁻¹) := by
      rw [cent_conj, mem_map_equiv, MulAut.conj_symm_apply]
      simpa [mul_assoc] using hb
    have h1 := hwc _ hb'
    rw [show (c * b * c⁻¹) * (c * x * c⁻¹) * (c * b * c⁻¹)⁻¹ = c * (b * x * b⁻¹) * c⁻¹ by group,
      cent_conj, mem_map_equiv, MulAut.conj_symm_apply] at h1
    exact h1
  · obtain ⟨k, hk⟩ := hw2
    refine ⟨k, ?_⟩
    have e : c⁻¹ * w * c = c⁻¹ * w * c⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hk]
    group

end ConjData

section JData

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit [Finite G] hZC in
theorem mem_centralizer_lift2 (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {U : Subgroup C} (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {a : G} (ha : a ∈ A) {d : C}
    (hd : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj d) (hdU : d ∈ centralizer (U : Set C)) :
    a ∈ centralizer (lift2 ψ U : Set G) := by
  rw [mem_centralizer_iff]
  intro b hb
  obtain ⟨hbA, hb2, w, hw, hbw⟩ := (mem_lift2 hψ hZ hUc).1 hb
  exact (commute_of_conj_commute hψ hZ ha hbA hb2 hd hbw
    (mem_centralizer_iff.1 hdU w hw).symm).symm

theorem jData_of_class (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) {x₀ u : C} {Z : Subgroup C}
    (hcd : CentreData x₀ Z) (hreg : Regular Z u) (hsyl : SylowData x₀ Z) (hT : ActsIn ψ T Z)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) (ht₀N : t₀ ∈ normalizer (A : Set G))
    (hx₀ : ψ ⟨t₀, ht₀N⟩ = MulAut.conj x₀) :
    ∃ p û : G, JData A R T p (lift2 ψ Z) û := by
  classical
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hUc : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcd.elem.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hU2 : ∀ u ∈ Z, u ^ 2 = 1 := fun u hu => hcd.elem.2 u hu
  have hpart : ∀ t ∈ T, ∀ (htN : t ∈ normalizer (A : Set G)) (p' : G) (hp'A : p' ∈ A),
      t⁻¹ * p' ∈ R → ψ ⟨p', le_normalizer hp'A⟩ = ψ ⟨t, htN⟩ ∧ p' ^ 2 = 1 := by
    intro t ht htN p' hp'A hp'
    refine ⟨?_, ?_⟩
    · have h1 : ψ ⟨t⁻¹ * p', mul_mem (inv_mem htN) (le_normalizer hp'A)⟩ = 1 :=
        (hψ.eq_one_iff _).2 (hc.sylowR.le hp')
      rw [psi_mul (inv_mem htN) (le_normalizer hp'A), psi_inv htN, inv_mul_eq_one] at h1
      exact h1.symm
    · have htr : Commute t (t⁻¹ * p') :=
        (mem_centralizer_iff.1 (hc.le_centralizer ht) (t⁻¹ * p') hp').symm
      have e : p' = t * (t⁻¹ * p') := by group
      rw [e, htr.mul_pow, (hc.elemT h32).2 t ht, (hc.elemR h32).2 _ hp', one_mul]
  obtain ⟨p, hpA, hp⟩ := hc.exists_aPart h32 h4 h34 ht₀
  obtain ⟨hpψ', hp2⟩ := hpart t₀ ht₀ ht₀N p hpA hp
  have hpψ : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj x₀ := hpψ'.trans hx₀
  have hpZ : p ∈ lift2 ψ Z := mem_lift2_of hpA hp2 hcd.mem hpψ
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply ht₀1
    have h1 : t₀⁻¹ ∈ R := by simpa using hp
    have h2 : t₀ ∈ R ⊓ T := mem_inf.2 ⟨by simpa using inv_mem h1, ht₀⟩
    rwa [hc.inf_eq_bot, mem_bot] at h2
  obtain ⟨û, hûA, hûψ⟩ := hψ.exists_eq (MulAut.conj u) ⟨u, rfl⟩
  have hûN := le_normalizer hûA
  have hnorm : ∀ a (haA : a ∈ A) (d : C), ψ ⟨a, le_normalizer haA⟩ = MulAut.conj d →
      d ∈ normalizer (Z : Set C) → a ∈ normalizer (lift2 ψ Z : Set G) := by
    intro a haA d hd hdZ
    refine mem_normalizer_lift2 hψ hZ hUc (le_normalizer haA) fun y => ?_
    rw [hd, MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hdZ y)
  have hnorm' : ∀ a (haA : a ∈ A) (d : C), ψ ⟨a, le_normalizer haA⟩ = MulAut.conj d →
      a ∈ normalizer (lift2 ψ Z : Set G) → d ∈ normalizer (Z : Set C) := by
    have key : ∀ a (haA : a ∈ A) (d : C), ψ ⟨a, le_normalizer haA⟩ = MulAut.conj d →
        a ∈ normalizer (lift2 ψ Z : Set G) → ∀ w ∈ Z, d * w * d⁻¹ ∈ Z := by
      intro a haA d hd ha w hw
      obtain ⟨j, hj, hjw⟩ := exists_mem_lift2 hψ hZ hU2 hw
      have hj' := (mem_normalizer_iff.1 ha j).1 hj
      obtain ⟨w', hw', hjw'⟩ := exists_of_mem_lift2 hψ hZ hUc hj'
      have e : (⟨a * j * a⁻¹, le_normalizer (lift2_le hj')⟩ : normalizer (A : Set G)) =
          ⟨a, le_normalizer haA⟩ * ⟨j, le_normalizer (lift2_le hj)⟩ *
            ⟨a, le_normalizer haA⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hd, hjw, ← map_inv, ← map_mul, ← map_mul] at hjw'
      rw [hinj hjw']
      exact hw'
    intro a haA d hd ha
    refine mem_normalizer_iff.2 fun w => ⟨key a haA d hd ha w, fun hw => ?_⟩
    have hd' : ψ ⟨a⁻¹, le_normalizer (inv_mem haA)⟩ = MulAut.conj d⁻¹ := by
      rw [psi_inv (le_normalizer haA), hd, map_inv]
    have h1 := key a⁻¹ (inv_mem haA) d⁻¹ hd' (inv_mem ha) _ hw
    simpa [mul_assoc] using h1
  have hcentZ : ∀ a (haA : a ∈ A) (d : C), ψ ⟨a, le_normalizer haA⟩ = MulAut.conj d →
      d ∈ centralizer (Z : Set C) → a ∈ centralizer (lift2 ψ Z : Set G) :=
    fun a haA d hd hdZ => mem_centralizer_lift2 hψ hZ hUc haA hd hdZ
  refine ⟨p, û,
    { le := lift2_le
      mem := hpZ
      ne_one := hp1
      aPart_mem := ⟨t₀, ht₀, hp⟩
      aPart_le := ?_
      le_centralizer := ?_
      le_normalizer := ?_
      trans := ?_
      free := ?_
      y_mem := mem_inf.2 ⟨hûA, hnorm û hûA u hûψ hreg.y_mem⟩
      odd := ?_
      cyclic := ?_
      sylow := ?_ }⟩
  · intro t ht p' hp'A hp'
    have htN := hc.le_normalizer ht
    obtain ⟨hp'ψ, hp'2⟩ := hpart t ht htN p' hp'A hp'
    obtain ⟨x, hx⟩ := exists_conj_of_mem hψ hc h32 h4 h34 ht htN
    exact mem_lift2_of hp'A hp'2 ((actsIn_iff.1 hT) t ht htN x hx) (hp'ψ.trans hx)
  · intro b hb hcomm z hz
    obtain ⟨d, hd⟩ := hψ.map_mem b hb
    have hbp : b * p * b⁻¹ ∈ A := mul_mem (mul_mem hb hpA) (inv_mem hb)
    have hψbp : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ = MulAut.conj (d * x₀ * d⁻¹) := by
      have e : (⟨b * p * b⁻¹, le_normalizer hbp⟩ : normalizer (A : Set G)) =
          ⟨b, le_normalizer hb⟩ * ⟨p, le_normalizer hpA⟩ * ⟨b, le_normalizer hb⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, ← hd, hpψ]
      simp only [map_mul, map_inv]
    have hw : d * x₀ * d⁻¹ ∈ cent x₀ := by
      rw [mem_centralizer_singleton_iff]
      have h1 : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ * ψ ⟨p, le_normalizer hpA⟩ =
          ψ ⟨p, le_normalizer hpA⟩ * ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext hcomm.eq)
      rw [hψbp, hpψ, ← map_mul, ← map_mul] at h1
      exact hinj h1
    obtain ⟨hzA, hz2, w, hwZ, hzw⟩ := (mem_lift2 hψ hZ hUc).1 hz
    rw [mem_centralizer_singleton_iff]
    exact commute_of_conj_commute hψ hZ hzA hbp (by rw [conj_pow, hp2, mul_one,
      mul_inv_cancel]) hzw hψbp (hcd.commute w hwZ _ hw)
  · intro a ha
    obtain ⟨haA, hap⟩ := mem_inf.1 ha
    obtain ⟨d, hd⟩ := hψ.map_mem a haA
    have hdy : d ∈ cent x₀ := by
      rw [mem_centralizer_singleton_iff]
      have h1 : ψ ⟨a, le_normalizer haA⟩ * ψ ⟨p, le_normalizer hpA⟩ =
          ψ ⟨p, le_normalizer hpA⟩ * ψ ⟨a, le_normalizer haA⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.1 hap))
      rw [← hd, hpψ, ← map_mul, ← map_mul] at h1
      exact hinj h1
    refine centralizer_le_normalizer _ (hcentZ a haA d hd.symm ?_)
    rw [mem_centralizer_iff]
    intro w hw
    exact (hcd.commute w hw d hdy)
  · intro j hj hj1 j' hj' hj'1
    obtain ⟨w, hw, hjw⟩ := exists_of_mem_lift2 hψ hZ hUc hj
    obtain ⟨w', hw', hjw'⟩ := exists_of_mem_lift2 hψ hZ hUc hj'
    have hw1 : w ≠ 1 := by
      rintro rfl
      apply hj1
      refine eq_of_sq_eq_one' hψ hZ (lift2_le hj) (one_mem A)
        (sq_eq_one_of_mem_lift2 hψ hZ hUc hj) (one_pow 2) ?_
      rw [hjw, map_one]
      exact (map_one ψ).symm
    have hw'1 : w' ≠ 1 := by
      rintro rfl
      apply hj'1
      refine eq_of_sq_eq_one' hψ hZ (lift2_le hj') (one_mem A)
        (sq_eq_one_of_mem_lift2 hψ hZ hUc hj') (one_pow 2) ?_
      rw [hjw', map_one]
      exact (map_one ψ).symm
    obtain ⟨c, hcN, hcw⟩ := hreg.trans w hw hw1 w' hw' hw'1
    obtain ⟨a, haA, haψ⟩ := hψ.exists_eq (MulAut.conj c) ⟨c, rfl⟩
    have haN := hnorm a haA c haψ hcN
    refine ⟨a, mem_inf.2 ⟨haA, haN⟩, ?_⟩
    have hmem : a * j * a⁻¹ ∈ lift2 ψ Z := (mem_normalizer_iff.1 haN j).1 hj
    refine eq_of_mem_lift2 hψ hZ hUc hmem hj' ?_
    have e : (⟨a * j * a⁻¹, le_normalizer (lift2_le hmem)⟩ : normalizer (A : Set G)) =
        ⟨a, le_normalizer haA⟩ * ⟨j, le_normalizer (lift2_le hj)⟩ *
          ⟨a, le_normalizer haA⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, haψ, hjw, hjw', ← hcw]
    simp only [map_mul, map_inv]
  · intro a ha j hj hj1 haj
    obtain ⟨haA, haJ⟩ := mem_inf.1 ha
    obtain ⟨d, hd⟩ := hψ.map_mem a haA
    have hdZ := hnorm' a haA d hd.symm haJ
    obtain ⟨w, hw, hjw⟩ := exists_of_mem_lift2 hψ hZ hUc hj
    have hw1 : w ≠ 1 := by
      rintro rfl
      apply hj1
      refine eq_of_sq_eq_one' hψ hZ (lift2_le hj) (one_mem A)
        (sq_eq_one_of_mem_lift2 hψ hZ hUc hj) (one_pow 2) ?_
      rw [hjw, map_one]
      exact (map_one ψ).symm
    have hfix : d * w * d⁻¹ = w := by
      have hmem : a * j * a⁻¹ ∈ A := mul_mem (mul_mem haA (lift2_le hj)) (inv_mem haA)
      have e : (⟨a * j * a⁻¹, le_normalizer hmem⟩ : normalizer (A : Set G)) =
          ⟨a, le_normalizer haA⟩ * ⟨j, le_normalizer (lift2_le hj)⟩ *
            ⟨a, le_normalizer haA⟩⁻¹ := rfl
      have h1 : ψ ⟨a * j * a⁻¹, le_normalizer hmem⟩ = ψ ⟨j, le_normalizer (lift2_le hj)⟩ := by
        congr 1
        exact Subtype.ext haj
      rw [e, map_mul, map_mul, map_inv, ← hd, hjw, ← map_inv, ← map_mul, ← map_mul] at h1
      exact hinj h1
    exact hcentZ a haA d hd.symm (hreg.free d hdZ w hw hw1 hfix)
  · have hZA' := hZ
    have hu := hreg.odd
    set n := orderOf u
    have hûn : û ^ n ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.2 ⟨pow_mem hûA n, (hψ.eq_one_iff ⟨_, pow_mem hûN n⟩).1 ?_⟩
      have e : (⟨û ^ n, pow_mem hûN n⟩ : normalizer (A : Set G)) = ⟨û, hûN⟩ ^ n := rfl
      rw [e, map_pow, hûψ, ← map_pow, pow_orderOf_eq_one, map_one]
    have hz := RankTwoL3Even.odd_orderOf_of_mem hZA' hûn
    have h1 : û ^ (n * orderOf (û ^ n)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
    exact (hu.mul hz).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · intro a ha
    obtain ⟨haA, haJ⟩ := mem_inf.1 ha
    obtain ⟨d, hd⟩ := hψ.map_mem a haA
    have hdZ := hnorm' a haA d hd.symm haJ
    obtain ⟨k, hk⟩ := hreg.cyclic d hdZ
    refine ⟨k, ?_⟩
    have hkA : (û ^ k)⁻¹ * a ∈ A := mul_mem (inv_mem (pow_mem hûA k)) haA
    refine hcentZ _ hkA ((u ^ k)⁻¹ * d) ?_ hk
    have e : (⟨(û ^ k)⁻¹ * a, le_normalizer hkA⟩ : normalizer (A : Set G)) =
        (⟨û, hûN⟩ ^ k)⁻¹ * ⟨a, le_normalizer haA⟩ := rfl
    rw [e, map_mul, map_inv, map_pow, hûψ, ← hd]
    simp only [map_mul, map_inv, map_pow]
  · intro x hx hxc hx2
    obtain ⟨hxA, hxp⟩ := mem_inf.1 hx
    obtain ⟨c, hc'⟩ := hψ.map_mem x hxA
    have hcx : c ∈ cent x₀ := by
      rw [mem_centralizer_singleton_iff]
      have h1 : ψ ⟨x, le_normalizer hxA⟩ * ψ ⟨p, le_normalizer hpA⟩ =
          ψ ⟨p, le_normalizer hpA⟩ * ψ ⟨x, le_normalizer hxA⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.1 hxp))
      rw [← hc', hpψ, ← map_mul, ← map_mul] at h1
      exact hinj h1
    have hcZ : c ∈ Z := by
      refine hsyl c hcx (fun e he => ?_) ?_
      · obtain ⟨b, hb, hbψ⟩ := hψ.exists_eq (MulAut.conj e) ⟨e, rfl⟩
        have hbp : b * p * b⁻¹ ∈ A := mul_mem (mul_mem hb hpA) (inv_mem hb)
        have hψbp : ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ = MulAut.conj (e * x₀ * e⁻¹) := by
          have e1 : (⟨b * p * b⁻¹, le_normalizer hbp⟩ : normalizer (A : Set G)) =
              ⟨b, le_normalizer hb⟩ * ⟨p, le_normalizer hpA⟩ * ⟨b, le_normalizer hb⟩⁻¹ := rfl
          rw [e1, map_mul, map_mul, map_inv, hbψ, hpψ]
          simp only [map_mul, map_inv]
        have hbp2 : (b * p * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2, mul_one, mul_inv_cancel]
        have hcomm : Commute (b * p * b⁻¹) p :=
          commute_of_conj_commute hψ hZ hbp hpA hp2 hψbp hpψ
            (mem_centralizer_singleton_iff.1 he)
        have h1 := mem_centralizer_singleton_iff.1 (hxc b hb hcomm)
        have h2 : ψ ⟨x, le_normalizer hxA⟩ * ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ =
            ψ ⟨b * p * b⁻¹, le_normalizer hbp⟩ * ψ ⟨x, le_normalizer hxA⟩ := by
          rw [← map_mul, ← map_mul]
          exact congrArg ψ (Subtype.ext h1)
        rw [← hc', hψbp, ← map_mul, ← map_mul] at h2
        rw [mem_centralizer_singleton_iff]
        exact hinj h2
      · obtain ⟨k, hk⟩ := hx2
        refine ⟨k, hinj ?_⟩
        rw [map_pow, hc', ← psi_pow (le_normalizer hxA), map_one]
        have e : (⟨x ^ 2 ^ k, pow_mem (le_normalizer hxA) _⟩ : normalizer (A : Set G)) = 1 :=
          Subtype.ext hk
        rw [e, map_one]
    have hx2' : x ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := hx2
      have hsq : x ^ 2 ∈ A ⊓ centralizer (A : Set G) := by
        refine mem_inf.2 ⟨pow_mem hxA 2, (hψ.eq_one_iff ⟨_, pow_mem (le_normalizer hxA) 2⟩).1 ?_⟩
        have e : (⟨x ^ 2, pow_mem (le_normalizer hxA) 2⟩ : normalizer (A : Set G)) =
            ⟨x, le_normalizer hxA⟩ ^ 2 := rfl
        rw [e, map_pow, ← hc', ← map_pow, hU2 c hcZ, map_one]
      refine RankTwoL3Even.eq_one_of_odd_of_pow_two (RankTwoL3Even.odd_orderOf_of_mem hZ hsq)
        (k := k) ?_
      rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
    exact mem_lift2_of hxA hx2' hcZ hc'.symm

end JData

section Exists

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit [Finite G] hZC hψ in
theorem zx_eq_of_mem {x u : C} {Z : Subgroup C} (hcd : CentreData x Z) (hreg : Regular Z u)
    {z : C} (hz : z ∈ Z) (hz1 : z ≠ 1) : zx z = Z := by
  obtain ⟨c, hcN, hcz⟩ := hreg.trans x hcd.mem hcd.ne_one z hz hz1
  rw [← hcz, zx_conj, zx_eq_of_centreData hcd]
  exact (mem_normalizer_iff_map_conj_eq.1 hcN)

omit [Finite G] hZC hψ in
theorem exists_classData_of_reps {reps : List C} (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z) {x : C}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ u, CentreData x (zx x) ∧ Regular (zx x) u ∧ SylowData x (zx x) := by
  obtain ⟨y, hy, hyx⟩ := hcover x hx2 hx1
  obtain ⟨c, rfl⟩ := isConj_iff.1 hyx
  obtain ⟨Z, u, hcd, hreg, hsyl⟩ := hJ y hy
  have hZ : zx (c * y * c⁻¹) = Z.map (MulAut.conj c).toMonoidHom := by
    rw [zx_conj, zx_eq_of_centreData hcd]
  rw [hZ]
  exact ⟨c * u * c⁻¹, hcd.conj c, hreg.conj c, hsyl.conj c⟩

theorem exists_jData (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) {reps : List C}
    (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) (ht₀N : t₀ ∈ normalizer (A : Set G)) {x₀ : C}
    (hx₀ : ψ ⟨t₀, ht₀N⟩ = MulAut.conj x₀) (hT : ActsIn ψ T (zx x₀)) :
    ∃ p û : G, JData A R T p (lift2 ψ (zx x₀)) û := by
  obtain ⟨hx2, hx1⟩ := involution_of_conj hZC hψ hc h32 ht₀ ht₀N hx₀
  obtain ⟨u, hcd, hreg, hsyl⟩ := exists_classData_of_reps hcover hJ hx2 (hx1 ht₀1)
  exact jData_of_class hZC hψ h4 h32 h34 hc hZA hcd hreg hsyl hT ht₀ ht₀1 ht₀N hx₀

end Exists

end CFSG.ComponentClassification.RankTwoExceptional.Exc
