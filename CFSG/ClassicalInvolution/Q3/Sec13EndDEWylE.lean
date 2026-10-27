module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

@[expose] def dewA {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) : Subgroup G where
  carrier := {q | q ∈ pCore 2 G ∧ ∀ K ∈ Ω, conjSub q K = K ∨ conjSub q K = S.shift b K}
  one_mem' := ⟨(pCore 2 G).one_mem, fun K _ => Or.inl (conjSub_one K)⟩
  mul_mem' := by
    rintro a c ⟨ha, ha'⟩ ⟨hc, hc'⟩
    refine ⟨(pCore 2 G).mul_mem ha hc, fun K hK => ?_⟩
    rw [conjSub_mul]
    rcases hc' K hK with h | h
    · rw [h]
      exact ha' K hK
    · rw [h, ← S.shift_conj b a K hK]
      rcases ha' K hK with h' | h'
      · rw [h']
        exact Or.inr rfl
      · rw [h', S.shift_shift_self b hK]
        exact Or.inl rfl
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(pCore 2 G).inv_mem ha, fun K hK => ?_⟩
    have hK' : conjSub a⁻¹ K ∈ Ω := S.conj_mem a⁻¹ K hK
    have h1 : conjSub a (conjSub a⁻¹ K) = K := conjSub_conjSub_inv a K
    rcases ha' _ hK' with h | h
    · exact Or.inl (by rw [h] at h1; exact h1)
    · refine Or.inr ?_
      rw [h] at h1
      have h2 := S.shift_shift_self b hK'
      rw [h1] at h2
      exact h2.symm

open Classical in
@[expose] noncomputable def dewFun {Ω : Set (Subgroup G)} (S : TwinShift Ω) (a : G) :
    G → ZMod 2 :=
  fun x => if S.lam a x = 0 then 0 else 1

theorem dewA_le_pCore {Ω : Set (Subgroup G)} (S : TwinShift Ω) (b : Lab2) :
    dewA S b ≤ pCore 2 G := fun _ hq => hq.1

private theorem dewe_add_self : ∀ c : Lab2, c + c = 0 := by decide

private theorem dewe_zmod_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem dewe_smul_inj : ∀ b : Lab2, b ≠ 0 → ∀ c c' : ZMod 2, c • b = c' • b → c = c' := by
  decide

private theorem dewe_add_mem {b p q : Lab2} (hp : p = 0 ∨ p = b) (hq : q = 0 ∨ q = b) :
    p + q = 0 ∨ p + q = b := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; exact dewe_add_self _

private theorem dewe_ifadd {b : Lab2} (hb : b ≠ 0) {p q : Lab2} (hp : p = 0 ∨ p = b)
    (hq : q = 0 ∨ q = b) :
    (if p + q = 0 then (0 : ZMod 2) else 1) =
      (if p = 0 then 0 else 1) + (if q = 0 then 0 else 1) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
  · simp
  · simp [hb]
  · simp [hb]
  · simp [hb, dewe_add_self b, h11]

section Shifts

variable {Ω : Set (Subgroup G)} (S : TwinShift Ω)

private theorem dewe_shift_mem {m : Lab2} {K : Subgroup G} (hK : K ∈ Ω) : S.shift m K ∈ Ω :=
  (S.shift_mem m K hK).1

private theorem dewe_shift_invol {m : Lab2} {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) : IsUniqueInvolution (S.shift m K) u := by
  obtain ⟨-, z, hz, hzJ⟩ := S.shift_mem m K hK
  rwa [show z = u from hz.eq hu] at hzJ

private theorem dewe_ne_shift {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} (hK : K ∈ Ω) :
    K ≠ S.shift b K := fun heq => hb (S.shift_free b K hK heq.symm)

private theorem dewe_twins {b : Lab2} (hb : b ≠ 0) {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) : DewTwins Ω K (S.shift b K) u :=
  ⟨hK, dewe_shift_mem S hK, hu, dewe_shift_invol S hK hu, dewe_ne_shift S hb hK⟩

private theorem dewe_twins' {b b' : Lab2} (hbb : b ≠ b') {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) : DewTwins Ω (S.shift b K) (S.shift b' K) u :=
  ⟨dewe_shift_mem S hK, dewe_shift_mem S hK, dewe_shift_invol S hK hu,
    dewe_shift_invol S hK hu, fun heq => hbb (S.shift_injective hK heq)⟩

end Shifts

section Q8

variable {K : Subgroup G} {x i j : G}

private theorem dewe_q8_central (hx : IsUniqueInvolution K x) {k : G} (hk : k ∈ K) :
    x * k = k * x :=
  (mul_inv_eq_iff_eq_mul.mp (conj_of_mem_mem hx hk (Or.inr rfl))).symm

private theorem dewe_q8_inv (hQ : Q8Data K x i j) {a : G} (ha : a ∈ K)
    (ha' : a ∉ Subgroup.zpowers x) : a⁻¹ = a * x := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, det_tw_q8_sq hQ ha ha', hQ.inv.sq]

private theorem dewe_q8_comm (hQ : Q8Data K x i j) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (ha' : a ∉ Subgroup.zpowers x) (hb' : b ∉ Subgroup.zpowers x) (hnc : a * b ≠ b * a) :
    a * b * a⁻¹ * b⁻¹ = x := by
  have hbx := dewe_q8_central hQ.inv hb
  have hc : a * b * a⁻¹ * b⁻¹ = (a * b) * (a * b) := by
    rw [dewe_q8_inv hQ ha ha', dewe_q8_inv hQ hb hb']
    calc a * b * (a * x) * (b * x) = a * b * a * (x * b) * x := by group
      _ = a * b * a * (b * x) * x := by rw [hbx]
      _ = a * b * a * b * (x * x) := by group
      _ = a * b * (a * b) := by rw [hQ.inv.sq]; group
  have hab : a * b ∉ Subgroup.zpowers x := by
    intro hmem
    have hsq : (a * b) * (a * b) = 1 := by
      rcases det_tw_eq_one_or_of_mem_zpowers hQ.inv.sq hQ.inv.ne_one hmem with h1 | h1
      · rw [h1, one_mul]
      · rw [h1, hQ.inv.sq]
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := hc.trans hsq
    have h3 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h2
    exact hnc (mul_inv_eq_iff_eq_mul.mp h3)
  rw [hc]
  exact det_tw_q8_sq hQ (K.mul_mem ha hb) hab

private theorem dewe_q8_dichotomy (hQ : Q8Data K x i j) {k₁ k₂ : G} (hk₁ : k₁ ∈ K)
    (hk₂ : k₂ ∈ K) (h₁ : k₁ ∉ Subgroup.zpowers x) (h₂ : k₂ ∉ Subgroup.zpowers x)
    (hc : k₁ * k₂ = k₂ * k₁) : k₂ = k₁ ∨ k₂ = x * k₁ := by
  have hs1 : k₁ * k₁ = x := det_tw_q8_sq hQ hk₁ h₁
  have hs2 : k₂ * k₂ = x := det_tw_q8_sq hQ hk₂ h₂
  have hsq : (k₁ * k₂) * (k₁ * k₂) = 1 := by
    calc (k₁ * k₂) * (k₁ * k₂) = k₁ * (k₂ * k₁) * k₂ := by group
      _ = k₁ * (k₁ * k₂) * k₂ := by rw [hc]
      _ = (k₁ * k₁) * (k₂ * k₂) := by group
      _ = x * x := by rw [hs1, hs2]
      _ = 1 := hQ.inv.sq
  rcases hQ.inv.unique (k₁ * k₂) (K.mul_mem hk₁ hk₂) hsq with h0 | h0
  · right
    rw [eq_inv_of_mul_eq_one_right h0, dewe_q8_inv hQ hk₁ h₁, dewe_q8_central hQ.inv hk₁]
  · left
    have e1 : k₂ = k₁⁻¹ * x := by rw [← h0, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [dewe_q8_inv hQ hk₁ h₁, mul_assoc, hQ.inv.sq, mul_one] at e1
    exact e1

private theorem dewe_comm_twins {K J₁ J₂ : Subgroup G} (h1 : Commutes K J₁) (h2 : Commutes K J₂)
    (h3 : Commutes J₁ J₂) {k₁ k₂ j₁ j₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (hj₁ : j₁ ∈ J₁)
    (hj₂ : j₂ ∈ J₂) :
    k₁ * j₁⁻¹ * (k₂ * j₂⁻¹) * (k₁ * j₁⁻¹)⁻¹ * (k₂ * j₂⁻¹)⁻¹ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by
  have hA : k₁ * j₁⁻¹ * (k₂ * j₂⁻¹) = k₁ * k₂ * (j₁⁻¹ * j₂⁻¹) := by
    have e1 := h1 k₂ hk₂ j₁⁻¹ (J₁.inv_mem hj₁)
    calc k₁ * j₁⁻¹ * (k₂ * j₂⁻¹) = k₁ * (j₁⁻¹ * k₂) * j₂⁻¹ := by group
      _ = k₁ * (k₂ * j₁⁻¹) * j₂⁻¹ := by rw [← e1]
      _ = k₁ * k₂ * (j₁⁻¹ * j₂⁻¹) := by group
  have hB : k₂ * j₂⁻¹ * (k₁ * j₁⁻¹) = k₂ * k₁ * (j₁⁻¹ * j₂⁻¹) := by
    have e2 := h2 k₁ hk₁ j₂⁻¹ (J₂.inv_mem hj₂)
    have h5 : j₂⁻¹ * j₁⁻¹ = j₁⁻¹ * j₂⁻¹ := by
      have e3 := h3 j₁ hj₁ j₂ hj₂
      calc j₂⁻¹ * j₁⁻¹ = (j₁ * j₂)⁻¹ := (mul_inv_rev j₁ j₂).symm
        _ = (j₂ * j₁)⁻¹ := by rw [e3]
        _ = j₁⁻¹ * j₂⁻¹ := mul_inv_rev j₂ j₁
    calc k₂ * j₂⁻¹ * (k₁ * j₁⁻¹) = k₂ * (j₂⁻¹ * k₁) * j₁⁻¹ := by group
      _ = k₂ * (k₁ * j₂⁻¹) * j₁⁻¹ := by rw [← e2]
      _ = k₂ * k₁ * (j₂⁻¹ * j₁⁻¹) := by group
      _ = k₂ * k₁ * (j₁⁻¹ * j₂⁻¹) := by rw [h5]
  calc k₁ * j₁⁻¹ * (k₂ * j₂⁻¹) * (k₁ * j₁⁻¹)⁻¹ * (k₂ * j₂⁻¹)⁻¹
      = (k₁ * j₁⁻¹ * (k₂ * j₂⁻¹)) * (k₂ * j₂⁻¹ * (k₁ * j₁⁻¹))⁻¹ := by group
    _ = (k₁ * k₂ * (j₁⁻¹ * j₂⁻¹)) * (k₂ * k₁ * (j₁⁻¹ * j₂⁻¹))⁻¹ := by rw [hA, hB]
    _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by group

end Q8

section Coord

variable {Ω : Set (Subgroup G)}

private theorem dewe_coord_add {M : Type*} [AddCommMonoid M] {F : G → M} (hF1 : F 1 = 0)
    (hFadd : ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, F (x * y) = F x + F y) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (v : Fin 3 → ZMod 2) :
    F (TL4.e8Coord e v) = F (e 0 ^ (v 0).val) + F (e 1 ^ (v 1).val) + F (e 2 ^ (v 2).val) := by
  have hp : ∀ k : Fin 3, e k ^ (v k).val ∈ zGroup Ω := fun k => (zGroup Ω).pow_mem (he.mem k) _
  unfold TL4.e8Coord
  rw [hFadd _ ((zGroup Ω).mul_mem (hp 0) (hp 1)) _ (hp 2), hFadd _ (hp 0) _ (hp 1)]

private theorem dewe_pow_zero_or {M : Type*} [AddCommMonoid M] {F : G → M} (hF1 : F 1 = 0)
    (k : G) (c : ZMod 2) : F (k ^ c.val) = 0 ∨ F (k ^ c.val) = F k := by
  rcases dewe_zmod_cases c with rfl | rfl
  · left; simp [hF1]
  · right; rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

private theorem dewe_pow_zmod {F : G → ZMod 2} (hF1 : F 1 = 0) (k : G) (c : ZMod 2) :
    F (k ^ c.val) = c * F k := by
  rcases dewe_zmod_cases c with rfl | rfl
  · simp [hF1]
  · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, one_mul]

private theorem dewe_zmod_coord {F : G → ZMod 2} (hF : F ∈ DE2Hyp.deq2Dual Ω)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) (v : Fin 3 → ZMod 2) :
    F (TL4.e8Coord e v) = v 0 * F (e 0) + v 1 * F (e 1) + v 2 * F (e 2) := by
  obtain ⟨hF1, -, hadd⟩ := hF
  rw [dewe_coord_add hF1 hadd he v, dewe_pow_zmod hF1 (e 0) (v 0),
    dewe_pow_zmod hF1 (e 1) (v 1), dewe_pow_zmod hF1 (e 2) (v 2)]

private theorem dewe_zero_basis {F : G → Lab2} (hF : F ∈ dewDual2 Ω) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (hz : ∀ i, F (e i) = 0) (x : G) : F x = 0 := by
  obtain ⟨hF1, hoff, hadd⟩ := hF
  by_cases hx : x ∈ zGroup Ω
  · obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hx
    rw [dewe_coord_add hF1 hadd he v]
    have hterm : ∀ k : Fin 3, F (e k ^ (v k).val) = 0 := fun k => by
      rcases dewe_pow_zero_or hF1 (e k) (v k) with h1 | h1
      · exact h1
      · rw [h1, hz k]
    rw [hterm 0, hterm 1, hterm 2, add_zero, add_zero]
  · exact hoff x hx

private theorem dewe_mem_basis {F : G → Lab2} (hF : F ∈ dewDual2 Ω) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {b : Lab2} (hb : ∀ i, F (e i) = 0 ∨ F (e i) = b) (x : G) :
    F x = 0 ∨ F x = b := by
  obtain ⟨hF1, hoff, hadd⟩ := hF
  by_cases hx : x ∈ zGroup Ω
  · obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hx
    rw [dewe_coord_add hF1 hadd he v]
    have hterm : ∀ k : Fin 3, F (e k ^ (v k).val) = 0 ∨ F (e k ^ (v k).val) = b := fun k => by
      rcases dewe_pow_zero_or hF1 (e k) (v k) with h1 | h1
      · exact Or.inl h1
      · rw [h1]; exact hb k
    exact dewe_add_mem (dewe_add_mem (hterm 0) (hterm 1)) (hterm 2)
  · exact Or.inl (hoff x hx)

private def dewe_chk (c d v w : Fin 3 → ZMod 2) : Bool :=
  !(c != 0 && d != 0 && c != d && v != 0 && w != 0 &&
      (v 0 * c 0 + v 1 * c 1 + v 2 * c 2 == 0) && (v 0 * d 0 + v 1 * d 1 + v 2 * d 2 == 0) &&
      (w 0 * c 0 + w 1 * c 1 + w 2 * c 2 == 0) && (w 0 * d 0 + w 1 * d 1 + w 2 * d 2 == 0)) ||
    (v == w)

private theorem dewe_chk_all : ∀ c d v w : Fin 3 → ZMod 2, dewe_chk c d v w = true := by
  decide

private theorem dewe_chk_eq {c d v w : Fin 3 → ZMod 2} (h1 : c ≠ 0) (h2 : d ≠ 0) (h3 : c ≠ d)
    (h4 : v ≠ 0) (h5 : w ≠ 0) (h6 : v 0 * c 0 + v 1 * c 1 + v 2 * c 2 = 0)
    (h7 : v 0 * d 0 + v 1 * d 1 + v 2 * d 2 = 0)
    (h8 : w 0 * c 0 + w 1 * c 1 + w 2 * c 2 = 0)
    (h9 : w 0 * d 0 + w 1 * d 1 + w 2 * d 2 = 0) : v = w := by
  have := dewe_chk_all c d v w
  unfold dewe_chk at this
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9] at this
  exact this

private theorem dewe_common_unique {f g : G → ZMod 2} (hf : f ∈ DE2Hyp.deq2Dual Ω)
    (hg : g ∈ DE2Hyp.deq2Dual Ω) (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hfg : f ≠ g) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {x y : G} (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hfx : f x = 0) (hgx : g x = 0) (hfy : f y = 0)
    (hgy : g y = 0) : x = y := by
  obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hx
  obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he hy
  have hv : ¬(v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hx1
    have hv0 : v = 0 := by
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    rw [hv0, TL4.e8Coord_zero]
  have hw : ¬(w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hy1
    have hw0 : w = 0 := by
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    rw [hw0, TL4.e8Coord_zero]
  have ha : ¬(f (e 0) = 0 ∧ f (e 1) = 0 ∧ f (e 2) = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hf0
    funext z
    by_cases hz : z ∈ zGroup Ω
    · obtain ⟨c, rfl⟩ := TL4.exists_e8Coord_eq he hz
      rw [dewe_zmod_coord hf he c, h0, h1, h2]
      simp
    · exact hf.2.1 z hz
  have hb : ¬(g (e 0) = 0 ∧ g (e 1) = 0 ∧ g (e 2) = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hg0
    funext z
    by_cases hz : z ∈ zGroup Ω
    · obtain ⟨c, rfl⟩ := TL4.exists_e8Coord_eq he hz
      rw [dewe_zmod_coord hg he c, h0, h1, h2]
      simp
    · exact hg.2.1 z hz
  have hab : ¬(f (e 0) = g (e 0) ∧ f (e 1) = g (e 1) ∧ f (e 2) = g (e 2)) := by
    rintro ⟨h0, h1, h2⟩
    apply hfg
    funext z
    by_cases hz : z ∈ zGroup Ω
    · obtain ⟨c, rfl⟩ := TL4.exists_e8Coord_eq he hz
      rw [dewe_zmod_coord hf he c, dewe_zmod_coord hg he c, h0, h1, h2]
    · rw [hf.2.1 z hz, hg.2.1 z hz]
  have hc0 : (fun i => f (e i)) ≠ 0 := fun h0 => ha ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
  have hd0 : (fun i => g (e i)) ≠ 0 := fun h0 => hb ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
  have hcd : (fun i => f (e i)) ≠ (fun i => g (e i)) := fun h0 =>
    hab ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
  have hv0 : v ≠ 0 := fun h0 => hv ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
  have hw0 : w ≠ 0 := fun h0 => hw ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
  rw [dewe_zmod_coord hf he v] at hfx
  rw [dewe_zmod_coord hg he v] at hgx
  rw [dewe_zmod_coord hf he w] at hfy
  rw [dewe_zmod_coord hg he w] at hgy
  exact congrArg (TL4.e8Coord e) (dewe_chk_eq hc0 hd0 hcd hv0 hw0 hfx hgx hfy hgy)

end Coord

private def dewe_W (b : Lab2) : Subgroup (Multiplicative (Fin 3 → Lab2)) where
  carrier := {w | ∀ i, Multiplicative.toAdd w i = 0 ∨ Multiplicative.toAdd w i = b}
  one_mem' := fun _ => Or.inl rfl
  mul_mem' := by
    intro p q hp hq i
    exact dewe_add_mem (hp i) (hq i)
  inv_mem' := by
    intro p hp i
    have hneg : ∀ c : Lab2, -c = c := by decide
    have e : Multiplicative.toAdd p⁻¹ i = Multiplicative.toAdd p i := hneg _
    rw [e]
    exact hp i

private theorem dewe_W_card {b : Lab2} (hb : b ≠ 0) : Nat.card (dewe_W b) = 8 := by
  have hmem : ∀ v : Fin 3 → ZMod 2, Multiplicative.ofAdd (fun i => v i • b) ∈ dewe_W b := by
    intro v i
    show Multiplicative.toAdd (Multiplicative.ofAdd (fun i => v i • b)) i = 0 ∨
      Multiplicative.toAdd (Multiplicative.ofAdd (fun i => v i • b)) i = b
    rcases dewe_zmod_cases (v i) with c | c <;> simp [c]
  have hbij : Function.Bijective (fun v : Fin 3 → ZMod 2 =>
      (⟨Multiplicative.ofAdd (fun i => v i • b), hmem v⟩ : dewe_W b)) := by
    constructor
    · intro v w hvw
      funext i
      have h1 : v i • b = w i • b := by
        have := congrArg (fun z : dewe_W b =>
          Multiplicative.toAdd (z : Multiplicative (Fin 3 → Lab2)) i) hvw
        exact this
      exact dewe_smul_inj b hb _ _ h1
    · rintro ⟨w, hw⟩
      refine ⟨fun i => if Multiplicative.toAdd w i = 0 then 0 else 1, ?_⟩
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext i
      have hwi : Multiplicative.toAdd w i = 0 ∨ Multiplicative.toAdd w i = b := hw i
      rcases hwi with h1 | h1 <;> simp [h1, hb]
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private theorem dewe_elation_eq {Ω : Set (Subgroup G)} {x k₁ k₂ : G} {φ₁ φ₂ : G → ZMod 2}
    (hx1 : x ≠ 1) (hφ₁ : φ₁ ∈ DE2Hyp.deq2Dual Ω) (hφ₂ : φ₂ ∈ DE2Hyp.deq2Dual Ω)
    (h1 : IsElationOf Ω x φ₁ k₁) (h2 : IsElationOf Ω x φ₂ k₂)
    (hconj : ∀ y ∈ zGroup Ω, k₂ * y * k₂⁻¹ = k₁ * y * k₁⁻¹) : φ₁ = φ₂ := by
  funext y
  by_cases hy : y ∈ zGroup Ω
  · have e1 := h1 y hy
    have e2 := h2 y hy
    rw [hconj y hy, e1] at e2
    rcases dewe_zmod_cases (φ₁ y) with c1 | c1 <;> rcases dewe_zmod_cases (φ₂ y) with c2 | c2 <;>
      simp [c1, c2, hx1] at e2 ⊢
  · obtain ⟨-, o1, -⟩ := hφ₁
    obtain ⟨-, o2, -⟩ := hφ₂
    rw [o1 y hy, o2 y hy]

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

private theorem dewe_cent {d : G} (hd : d ∈ zGroup Ω) {q : G} (hq : q ∈ pCore 2 G) :
    d * q = q * d :=
  Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup hq) d hd

private theorem dewe_prod_comm {d d' δ δ' : G} (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω)
    (hδ : δ ∈ pCore 2 G) (hδ' : δ' ∈ pCore 2 G) (hδδ : δ * δ' = δ' * δ) :
    d * δ * (d' * δ') = d' * δ' * (d * δ) := by
  have e1 : d' * δ = δ * d' := h.dewe_cent hd' hδ
  have e2 : d * δ' = δ' * d := h.dewe_cent hd hδ'
  have e3 : d * d' = d' * d := h.zGroup_comm d hd d' hd'
  calc d * δ * (d' * δ') = d * (δ * d') * δ' := by group
    _ = d * (d' * δ) * δ' := by rw [← e1]
    _ = (d * d') * (δ * δ') := by group
    _ = (d' * d) * (δ' * δ) := by rw [e3, hδδ]
    _ = d' * (d * δ') * δ := by group
    _ = d' * (δ' * d) * δ := by rw [e2]
    _ = d' * δ' * (d * δ) := by group

private theorem dewe_central_reduce {d₁ d₂ δ₁ δ₂ : G} (hd₁ : d₁ ∈ zGroup Ω)
    (hd₂ : d₂ ∈ zGroup Ω) (hδ₁ : δ₁ ∈ pCore 2 G) (hδ₂ : δ₂ ∈ pCore 2 G) :
    d₁ * δ₁ * (d₂ * δ₂) * (d₁ * δ₁)⁻¹ * (d₂ * δ₂)⁻¹ = δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹ := by
  have e1 : d₁ * δ₂ = δ₂ * d₁ := h.dewe_cent hd₁ hδ₂
  have e2 : d₂ * δ₁ = δ₁ * d₂ := h.dewe_cent hd₂ hδ₁
  have e3 : d₁ * d₂ = d₂ * d₁ := h.zGroup_comm d₁ hd₁ d₂ hd₂
  have hXQ : δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹ ∈ pCore 2 G :=
    (pCore 2 G).mul_mem ((pCore 2 G).mul_mem ((pCore 2 G).mul_mem hδ₁ hδ₂)
      ((pCore 2 G).inv_mem hδ₁)) ((pCore 2 G).inv_mem hδ₂)
  have hXd : d₁ * d₂ * (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) = (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * (d₁ * d₂) :=
    h.dewe_cent ((zGroup Ω).mul_mem hd₁ hd₂) hXQ
  have e4 : d₂ * δ₂ * (d₁ * δ₁) = (d₁ * d₂) * (δ₂ * δ₁) := by
    calc d₂ * δ₂ * (d₁ * δ₁) = d₂ * (δ₂ * d₁) * δ₁ := by group
      _ = d₂ * (d₁ * δ₂) * δ₁ := by rw [← e1]
      _ = (d₂ * d₁) * (δ₂ * δ₁) := by group
      _ = (d₁ * d₂) * (δ₂ * δ₁) := by rw [e3]
  have e5 : d₁ * δ₁ * (d₂ * δ₂) = (d₁ * d₂) * (δ₁ * δ₂) := by
    calc d₁ * δ₁ * (d₂ * δ₂) = d₁ * (δ₁ * d₂) * δ₂ := by group
      _ = d₁ * (d₂ * δ₁) * δ₂ := by rw [← e2]
      _ = (d₁ * d₂) * (δ₁ * δ₂) := by group
  have e6 : (d₁ * d₂) * (δ₁ * δ₂) = (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * ((d₁ * d₂) * (δ₂ * δ₁)) := by
    calc (d₁ * d₂) * (δ₁ * δ₂)
        = (d₁ * d₂) * ((δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * (δ₂ * δ₁)) := by group
      _ = ((d₁ * d₂) * (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹)) * (δ₂ * δ₁) := by group
      _ = ((δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * (d₁ * d₂)) * (δ₂ * δ₁) := by rw [hXd]
      _ = (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * ((d₁ * d₂) * (δ₂ * δ₁)) := by group
  have key : d₁ * δ₁ * (d₂ * δ₂) = (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * (d₂ * δ₂ * (d₁ * δ₁)) := by
    rw [e5, e6, e4]
  calc d₁ * δ₁ * (d₂ * δ₂) * (d₁ * δ₁)⁻¹ * (d₂ * δ₂)⁻¹
      = (d₁ * δ₁ * (d₂ * δ₂)) * (d₂ * δ₂ * (d₁ * δ₁))⁻¹ := by group
    _ = (δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹) * (d₂ * δ₂ * (d₁ * δ₁)) * (d₂ * δ₂ * (d₁ * δ₁))⁻¹ := by
        rw [key]
    _ = δ₁ * δ₂ * δ₁⁻¹ * δ₂⁻¹ := by group

private theorem dewe_not_mem_zpowers {x k : G} (hxD : x ∈ zGroup Ω) (hx1 : x ≠ 1)
    {φ : G → ZMod 2} (hφ : φ ∈ DE2Hyp.deq2Dual Ω) (hφ0 : φ ≠ 0)
    (hel : IsElationOf Ω x φ k) : k ∉ Subgroup.zpowers x := by
  intro hk
  apply hφ0
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
  funext y
  show φ y = 0
  by_cases hy : y ∈ zGroup Ω
  · have hcomm : Commute x y := h.zGroup_comm x hxD y hy
    have hcy : k * y * k⁻¹ = y := by
      rw [← hn]
      exact mul_inv_eq_iff_eq_mul.mpr (hcomm.zpow_left n).eq
    have e := hel y hy
    rw [hcy] at e
    by_cases hφy : φ y = 0
    · exact hφy
    · rw [if_neg hφy] at e
      exact absurd (by simpa using e.symm) hx1
  · obtain ⟨-, o, -⟩ := hφ
    exact o y hy

private theorem dewe_mem_delta (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {K : Subgroup G}
    {u : G} (hK : K ∈ Ω) (hu : IsUniqueInvolution K u) : u ∈ dewDelta K (S.shift b K) :=
  h.zpowers_le_dewDelta (dewe_twins S hb hK hu) (Subgroup.mem_zpowers u)

theorem dewA_normal (S : TwinShift Ω) (b : Lab2) : (dewA S b).Normal := by
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  refine ⟨fun n hn g => ?_⟩
  refine ⟨hQn.conj_mem n hn.1 g, fun K hK => ?_⟩
  have hK' : conjSub g⁻¹ K ∈ Ω := S.conj_mem g⁻¹ K hK
  have key : conjSub (g * n * g⁻¹) K = conjSub g (conjSub n (conjSub g⁻¹ K)) := by
    rw [conjSub_mul, conjSub_mul]
  rw [key]
  rcases hn.2 _ hK' with h1 | h1
  · left
    rw [h1, conjSub_conjSub_inv]
  · right
    rw [h1, ← S.shift_conj b g _ hK', conjSub_conjSub_inv]

theorem zGroup_le_dewA (S : TwinShift Ω) (b : Lab2) : zGroup Ω ≤ dewA S b := by
  intro d hd
  refine ⟨h.zGroup_le_pCore hd, fun K hK => Or.inl ?_⟩
  exact mem_normalizer_iff_conjSub_eq.mp (h.dNorm K hK hd)

theorem mem_dewA_iff (S : TwinShift Ω) (b : Lab2) {q : G} (hq : q ∈ pCore 2 G) :
    q ∈ dewA S b ↔ ∀ x, S.lam q x = 0 ∨ S.lam q x = b := by
  constructor
  · intro hqA x
    by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
    · obtain ⟨M, hM⟩ := h.exists_mem_dew1V hx.1 hx.2
      have hspec := h.lam_spec S hq hM
      rcases hqA.2 M hM.1 with h1 | h1
      · left
        exact S.shift_free _ M hM.1 (hspec.symm.trans h1)
      · right
        exact S.shift_injective hM.1 (hspec.symm.trans h1)
    · exact Or.inl (h.lam_eq_zero_of_not_mem S (not_and_or.mp hx |>.imp id not_not.mp))
  · intro hall
    refine ⟨hq, fun K hK => ?_⟩
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
    have hspec := h.lam_spec S hq (show K ∈ dew1V Ω z from ⟨hK, hz⟩)
    rcases hall z with h0 | h0
    · left
      rw [h0, S.shift_zero K hK] at hspec
      exact hspec
    · right
      rw [h0] at hspec
      exact hspec

theorem dewFun_mem_dual (S : TwinShift Ω) {b : Lab2} {a : G} (ha : a ∈ dewA S b) :
    dewFun S a ∈ DE2Hyp.deq2Dual Ω := by
  have hlam := (h.mem_dewA_iff S b ha.1).mp ha
  by_cases hb : b = 0
  · have h0 : dewFun S a = fun _ => 0 := by
      funext x
      rcases hlam x with h1 | h1
      · simp [dewFun, h1]
      · simp [dewFun, h1, hb]
    rw [h0]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => (add_zero 0).symm⟩
  · have hD := h.lam_mem_dual S ha.1
    refine ⟨?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · simp [dewFun, h.lam_eq_zero_of_not_mem S (Or.inr rfl)]
    · simp [dewFun, h.lam_eq_zero_of_not_mem S (Or.inl hx)]
    · have hxy := hD.2.2 x hx y hy
      show (if S.lam a (x * y) = 0 then (0 : ZMod 2) else 1) =
        (if S.lam a x = 0 then 0 else 1) + (if S.lam a y = 0 then 0 else 1)
      rw [hxy]
      exact dewe_ifadd hb (hlam x) (hlam y)

theorem lam_eq_smul_dewFun (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {a : G}
    (ha : a ∈ dewA S b) (x : G) : S.lam a x = dewFun S a x • b := by
  rcases (h.mem_dewA_iff S b ha.1).mp ha x with h1 | h1
  · simp [dewFun, h1]
  · simp [dewFun, h1, hb]

theorem exists_eq_mul_dewDelta (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {a : G}
    (ha : a ∈ dewA S b) {K : Subgroup G} {u : G} (hK : K ∈ Ω) (hu : IsUniqueInvolution K u)
    (hau : dewFun S a u = 0) : ∃ d ∈ zGroup Ω, ∃ δ ∈ dewDelta K (S.shift b K), a = d * δ := by
  obtain ⟨q, hq, hqlam⟩ := (h.lam_dewDelta_range S hb hK hu).2 (dewFun S a)
    (h.dewFun_mem_dual S ha) hau
  have haQ : a ∈ pCore 2 G := ha.1
  have hqQ : q ∈ pCore 2 G := dewDelta_le_pCore K (S.shift b K) hq
  have hdQ : a * q⁻¹ ∈ pCore 2 G := (pCore 2 G).mul_mem haQ ((pCore 2 G).inv_mem hqQ)
  refine ⟨a * q⁻¹, (h.lam_eq_zero_iff S hdQ).mp (fun x => ?_), q, hq, by group⟩
  rw [h.lam_mul S haQ ((pCore 2 G).inv_mem hqQ) x, h.lam_inv S hqQ x, hqlam x,
    h.lam_eq_smul_dewFun S hb ha x]
  exact dewe_add_self _

theorem dewA_eq_closure (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) :
    dewA S b = Subgroup.closure {x | ∃ K ∈ Ω, x ∈ dewDelta K (S.shift b K)} := by
  have hDle : zGroup Ω ≤ Subgroup.closure {x | ∃ K ∈ Ω, x ∈ dewDelta K (S.shift b K)} := by
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1]
      exact one_mem _
    · obtain ⟨K, hK⟩ := h.exists_mem_dew1V hd hd1
      exact Subgroup.subset_closure ⟨K, hK.1, h.dewe_mem_delta S hb hK.1 hK.2⟩
  apply le_antisymm
  · intro a ha
    obtain ⟨u, hu, hu1, hfu, -⟩ :=
      h.exists_involution_ker (h.dewFun_mem_dual S ha) (h.dewFun_mem_dual S ha)
    obtain ⟨K, hK⟩ := h.exists_mem_dew1V hu hu1
    obtain ⟨d, hd, δ, hδ, rfl⟩ := h.exists_eq_mul_dewDelta S hb ha hK.1 hK.2 hfu
    exact Subgroup.mul_mem _ (hDle hd) (Subgroup.subset_closure ⟨K, hK.1, hδ⟩)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨K, hK, hx⟩
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
    obtain ⟨f, -, -, hfl⟩ := (h.lam_dewDelta_range S hb hK hz).1 x hx
    refine (h.mem_dewA_iff S b (dewDelta_le_pCore K (S.shift b K) hx)).mpr (fun y => ?_)
    rw [hfl y]
    rcases dewe_zmod_cases (f y) with c | c <;> simp [c]

theorem dewA_mul_self (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {a : G} (ha : a ∈ dewA S b) :
    a * a = 1 := by
  obtain ⟨u, hu, hu1, hfu, -⟩ :=
    h.exists_involution_ker (h.dewFun_mem_dual S ha) (h.dewFun_mem_dual S ha)
  obtain ⟨K, hK⟩ := h.exists_mem_dew1V hu hu1
  obtain ⟨d, hd, δ, hδ, rfl⟩ := h.exists_eq_mul_dewDelta S hb ha hK.1 hK.2 hfu
  have hδQ : δ ∈ pCore 2 G := dewDelta_le_pCore K (S.shift b K) hδ
  have hdδ : d * δ = δ * d := h.dewe_cent hd hδQ
  calc d * δ * (d * δ) = d * (δ * d) * δ := by group
    _ = d * (d * δ) * δ := by rw [← hdδ]
    _ = (d * d) * (δ * δ) := by group
    _ = 1 := by
      rw [h.zGroup_mul_self d hd, h.dewDelta_mul_self (dewe_twins S hb hK.1 hK.2) hδ, mul_one]

theorem dewA_comm (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) {a a' : G} (ha : a ∈ dewA S b)
    (ha' : a' ∈ dewA S b) : a * a' = a' * a := by
  obtain ⟨u, hu, hu1, hfu, hgu⟩ :=
    h.exists_involution_ker (h.dewFun_mem_dual S ha) (h.dewFun_mem_dual S ha')
  obtain ⟨K, hK⟩ := h.exists_mem_dew1V hu hu1
  obtain ⟨d, hd, δ, hδ, rfl⟩ := h.exists_eq_mul_dewDelta S hb ha hK.1 hK.2 hfu
  obtain ⟨d', hd', δ', hδ', rfl⟩ := h.exists_eq_mul_dewDelta S hb ha' hK.1 hK.2 hgu
  have hδδ : δ * δ' = δ' * δ := h.dewDelta_comm (dewe_twins S hb hK.1 hK.2) hδ hδ'
  exact h.dewe_prod_comm hd hd' (dewDelta_le_pCore K (S.shift b K) hδ)
    (dewDelta_le_pCore K (S.shift b K) hδ') hδδ

theorem dewA_inf_dewA (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0) (hb' : b' ≠ 0) (hbb : b ≠ b') :
    dewA S b ⊓ dewA S b' = zGroup Ω := by
  apply le_antisymm
  · intro x hx
    refine (h.lam_eq_zero_iff S hx.1.1).mp (fun y => ?_)
    have h1 := (h.mem_dewA_iff S b hx.1.1).mp hx.1 y
    have h2 := (h.mem_dewA_iff S b' hx.1.1).mp hx.2 y
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact h1
    · exact h1
    · exact absurd (h1.symm.trans h2) hb
    · exact absurd (h1.symm.trans h2) hbb
  · exact le_inf (h.zGroup_le_dewA S b) (h.zGroup_le_dewA S b')

private theorem dewe_key {b b' : Lab2} (S : TwinShift Ω) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb : b ≠ b') {a a' : G} (ha : a ∈ dewA S b) (ha' : a' ∈ dewA S b') {K : Subgroup G}
    {x : G} (hK : K ∈ Ω) (hKx : IsUniqueInvolution K x) (hfx : dewFun S a x = 0)
    (hgx : dewFun S a' x = 0) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K, IsElationOf Ω x (dewFun S a) k₁ ∧ IsElationOf Ω x (dewFun S a') k₂ ∧
      a * a' * a⁻¹ * a'⁻¹ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by
  obtain ⟨d₁, hd₁, δ₁, hδ₁, rfl⟩ := h.exists_eq_mul_dewDelta S hb ha hK hKx hfx
  obtain ⟨d₂, hd₂, δ₂, hδ₂, rfl⟩ := h.exists_eq_mul_dewDelta S hb' ha' hK hKx hgx
  obtain ⟨k₁, hk₁, j₁, hj₁, rfl, hδ₁Q⟩ :=
    (h.mem_dewDelta_iff (dewe_twins S hb hK hKx)).mp hδ₁
  obtain ⟨k₂, hk₂, j₂, hj₂, rfl, hδ₂Q⟩ :=
    (h.mem_dewDelta_iff (dewe_twins S hb' hK hKx)).mp hδ₂
  obtain ⟨φ₁, hφ₁, -, hel₁⟩ := h.exists_isElationOf hK hKx hk₁
  obtain ⟨φ₂, hφ₂, -, hel₂⟩ := h.exists_isElationOf hK hKx hk₂
  have hd₁Q : d₁ ∈ pCore 2 G := h.zGroup_le_pCore hd₁
  have hd₂Q : d₂ ∈ pCore 2 G := h.zGroup_le_pCore hd₂
  have hφ₁eq : φ₁ = dewFun S (d₁ * (k₁ * j₁⁻¹)) := by
    funext y
    apply dewe_smul_inj b hb
    have hmul : S.lam (d₁ * (k₁ * j₁⁻¹)) y = S.lam (k₁ * j₁⁻¹) y := by
      rw [h.lam_mul S hd₁Q hδ₁Q y, h.lam_of_mem_zGroup S hd₁ y, zero_add]
    rw [← h.lam_dewDelta S hb hK hKx hφ₁ hk₁ hj₁ hel₁ hδ₁Q y, ← hmul,
      h.lam_eq_smul_dewFun S hb ha y]
  have hφ₂eq : φ₂ = dewFun S (d₂ * (k₂ * j₂⁻¹)) := by
    funext y
    apply dewe_smul_inj b' hb'
    have hmul : S.lam (d₂ * (k₂ * j₂⁻¹)) y = S.lam (k₂ * j₂⁻¹) y := by
      rw [h.lam_mul S hd₂Q hδ₂Q y, h.lam_of_mem_zGroup S hd₂ y, zero_add]
    rw [← h.lam_dewDelta S hb' hK hKx hφ₂ hk₂ hj₂ hel₂ hδ₂Q y, ← hmul,
      h.lam_eq_smul_dewFun S hb' ha' y]
  refine ⟨k₁, hk₁, k₂, hk₂, ?_, ?_, ?_⟩
  · rw [← hφ₁eq]
    exact hel₁
  · rw [← hφ₂eq]
    exact hel₂
  · have hc12 := dewe_comm_twins (h.commutes_of_dewTwins (dewe_twins S hb hK hKx))
      (h.commutes_of_dewTwins (dewe_twins S hb' hK hKx))
      (h.commutes_of_dewTwins (dewe_twins' S hbb hK hKx)) hk₁ hk₂ hj₁ hj₂
    rw [h.dewe_central_reduce hd₁ hd₂ hδ₁Q hδ₂Q, hc12]

theorem card_dewA (S : TwinShift Ω) {b : Lab2} (hb : b ≠ 0) : Nat.card (dewA S b) = 64 := by
  obtain ⟨e, he⟩ := h.exists_basis
  let Ψ : pCore 2 G →* Multiplicative (Fin 3 → Lab2) :=
    MonoidHom.mk' (fun q => Multiplicative.ofAdd (fun i => S.lam (q : G) (e i)))
      (fun p q => by
        show Multiplicative.ofAdd (fun i => S.lam ((p * q : pCore 2 G) : G) (e i)) =
          Multiplicative.ofAdd (fun i => S.lam (p : G) (e i)) *
            Multiplicative.ofAdd (fun i => S.lam (q : G) (e i))
        rw [← ofAdd_add]
        congr 1
        funext i
        exact h.lam_mul S p.2 q.2 (e i))
  have hTc : Nat.card (Multiplicative (Fin 3 → Lab2)) = 64 := by
    show Nat.card (Fin 3 → Lab2) = 64
    rw [Nat.card_fun, Nat.card_prod, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hker : Ψ.ker = (zGroup Ω).subgroupOf (pCore 2 G) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have hz : ∀ i, S.lam (q : G) (e i) = 0 := by
        intro i
        have := congrArg (fun w : Multiplicative (Fin 3 → Lab2) => Multiplicative.toAdd w i) hq
        exact this
      refine (h.lam_eq_zero_iff S q.2).mp (fun x => ?_)
      by_cases hx : x ∈ zGroup Ω
      · obtain ⟨c, rfl⟩ := TL4.exists_e8Coord_eq he hx
        exact dewe_zero_basis (h.lam_mem_dual S q.2) he hz _
      · exact h.lam_eq_zero_of_not_mem S (Or.inl hx)
    · intro hq
      show Multiplicative.ofAdd (fun i => S.lam (q : G) (e i)) = 1
      have hfun : (fun i => S.lam (q : G) (e i)) = 0 :=
        funext fun i => h.lam_of_mem_zGroup S hq (e i)
      rw [hfun]
      rfl
  have hkc : Nat.card Ψ.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.zGroup_le_pCore).toEquiv,
      h.card_zGroup]
  have hrc := Subgroup.card_ker_mul_card_range Ψ
  have hrange : Nat.card Ψ.range = 64 := by
    rw [hkc, h.card_pCore_eq] at hrc
    omega
  have hΨsurj : Ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hTc])
  have hWi : (dewe_W b).index = 8 := by
    have := Subgroup.card_mul_index (dewe_W b)
    rw [dewe_W_card hb, hTc] at this
    omega
  have hsub : (dewA S b).subgroupOf (pCore 2 G) = (dewe_W b).comap Ψ := by
    ext q
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    constructor
    · intro hq i
      exact (h.mem_dewA_iff S b q.2).mp hq (e i)
    · intro hi
      have hi' : ∀ i, Multiplicative.toAdd (Ψ q) i = 0 ∨ Multiplicative.toAdd (Ψ q) i = b := hi
      refine (h.mem_dewA_iff S b q.2).mpr (fun x => ?_)
      exact dewe_mem_basis (h.lam_mem_dual S q.2) he (fun i => hi' i) x
  have hidx : ((dewA S b).subgroupOf (pCore 2 G)).index = 8 := by
    rw [hsub, Subgroup.index_comap, hΨsurj, Subgroup.relIndex_top_right, hWi]
  have hm := Subgroup.relIndex_mul_card (H := dewA S b) (K := pCore 2 G)
  rw [inf_eq_left.mpr (dewA_le_pCore S b), h.card_pCore_eq] at hm
  have hrel : (dewA S b).relIndex (pCore 2 G) = 8 := hidx
  rw [hrel] at hm
  omega

theorem commutator_dewA_of_independent (S : TwinShift Ω) {b b' : Lab2} (hb : b ≠ 0)
    (hb' : b' ≠ 0) (hbb : b ≠ b') {a a' : G} (ha : a ∈ dewA S b) (ha' : a' ∈ dewA S b')
    (hf : dewFun S a ≠ 0) (hg : dewFun S a' ≠ 0) (hfg : dewFun S a ≠ dewFun S a') :
    ∃ x ∈ zGroup Ω, x ≠ 1 ∧ dewFun S a x = 0 ∧ dewFun S a' x = 0 ∧
      (∀ y ∈ zGroup Ω, y ≠ 1 → dewFun S a y = 0 → dewFun S a' y = 0 → y = x) ∧
      a * a' * a⁻¹ * a'⁻¹ = x := by
  have hF := h.dewFun_mem_dual S ha
  have hG := h.dewFun_mem_dual S ha'
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨x, hxD, hx1, hfx, hgx⟩ := h.exists_involution_ker hF hG
  refine ⟨x, hxD, hx1, hfx, hgx, fun y hy hy1 hfy hgy =>
    dewe_common_unique hF hG hf hg hfg he hy hxD hy1 hx1 hfy hgy hfx hgx, ?_⟩
  obtain ⟨K, hK⟩ := h.exists_mem_dew1V hxD hx1
  obtain ⟨k₁, hk₁, k₂, hk₂, hel₁, hel₂, hcomm⟩ :=
    h.dewe_key S hb hb' hbb ha ha' hK.1 hK.2 hfx hgx
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hK.2 (h.isQuatSub_of_mem hK.1) (h.card K hK.1)
  have hQ : Q8Data K x i j := ⟨hK.2, hi, hj, hii, hjj, hji, hNF⟩
  have hk₁z := h.dewe_not_mem_zpowers hxD hx1 hF hf hel₁
  have hk₂z := h.dewe_not_mem_zpowers hxD hx1 hG hg hel₂
  have hnc : k₁ * k₂ ≠ k₂ * k₁ := by
    intro hc
    apply hfg
    rcases dewe_q8_dichotomy hQ hk₁ hk₂ hk₁z hk₂z hc with h2 | h2
    · exact dewe_elation_eq hx1 hF hG hel₁ hel₂ (fun y _ => by rw [h2])
    · refine dewe_elation_eq hx1 hF hG hel₁ hel₂ (fun y hy => ?_)
      rw [h2]
      have hw : k₁ * y * k₁⁻¹ ∈ zGroup Ω := h.zGroup_normal.conj_mem y hy k₁
      calc x * k₁ * y * (x * k₁)⁻¹ = x * (k₁ * y * k₁⁻¹) * x⁻¹ := by group
        _ = k₁ * y * k₁⁻¹ := by rw [h.zGroup_comm x hxD _ hw, mul_inv_cancel_right]
  rw [hcomm]
  exact dewe_q8_comm hQ hk₁ hk₂ hk₁z hk₂z hnc

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
