module

public import CFSG.ClassicalInvolution.Q3.Sec13EndPolar16
import CFSG.ClassicalInvolution.Q3.Sec13EndSp4
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.Polar

variable {V : Type*} [CommGroup V]

private theorem p16b_ovoid_block : ∀ a : Fin 6, ∀ x : Sp4.V4, x ≠ 0 → x ∉ Sp4.ovoid a →
    ∃ y ∈ Sp4.ovoid a, Sp4.symp x y = 0 := by
  unfold Sp4.ovoid Sp4.dv Sp4.cv Sp4.symp; decide +kernel

private theorem p16b_no_six_V4 (T : Finset Sp4.V4) (hT : 6 ≤ T.card) (h0 : (0 : Sp4.V4) ∉ T)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Sp4.symp x y = 1) : False := by
  obtain ⟨O, hOT, hO⟩ := Finset.exists_subset_card_eq (show 5 ≤ T.card by omega)
  have hOmem : O ∈ Finset.powersetCard 5 (Finset.univ.erase (0 : Sp4.V4)) := by
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => h0 (h ▸ hOT hx), Finset.mem_univ _⟩, hO⟩
  obtain ⟨a, rfl⟩ := Sp4.ovoid_classification O hOmem
    (fun x hx y hy hxy => hpair x (hOT hx) y (hOT hy) hxy)
  obtain ⟨x, hxT, hxO⟩ : ∃ x ∈ T, x ∉ Sp4.ovoid a := by
    by_contra hcon
    push Not at hcon
    have hsub : T ⊆ Sp4.ovoid a := fun x hx => hcon x hx
    have := Finset.card_le_card hsub
    rw [Sp4.ovoid_card] at this
    omega
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxT)
  obtain ⟨y, hy, hxy⟩ := p16b_ovoid_block a x hx0 hxO
  have hyT : y ∈ T := hOT hy
  have hne : x ≠ y := fun h => hxO (h ▸ hy)
  have h1 := hpair x hxT y hyT hne
  rw [hxy] at h1
  exact absurd h1 (by decide)

theorem exists_orth_of_card_six [Finite V] {B : V → V → ZMod 2} (hB : SympForm B)
    (hcard : Nat.card V = 16) (T : Finset V) (hT : 6 ≤ T.card) (h1 : (1 : V) ∉ T) :
    ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ B x y = 0 := by
  obtain ⟨θ, hθ⟩ := Sp4.exists_symplectic_iso hB hcard
  by_contra hcon
  push Not at hcon
  refine p16b_no_six_V4 (T.image fun a => Multiplicative.toAdd (θ a)) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _
      (fun a b h => θ.injective (Multiplicative.toAdd.injective h))]
    exact hT
  · intro h0
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp h0
    have hθa : θ a = 1 := toAdd_eq_zero.mp hEq
    have ha1 : a = 1 := θ.injective (by rw [hθa, map_one])
    exact h1 (ha1 ▸ ha)
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hθ a b]
    have hab : a ≠ b := fun h => hxy (by rw [h])
    have hne := hcon a ha b hb hab
    revert hne
    generalize B a b = c
    revert c
    decide

private theorem p16b_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

private theorem p16b_pw_sq {w : V} (hw : w * w = 1) (c : ZMod 2) : Sp4.pw w c * Sp4.pw w c = 1 := by
  rw [← Sp4.pw_add hw, p16b_add_self, Sp4.pw_zero]

private def p16bK {B : V → V → ZMod 2} (hB : SympForm B) (z f : V) : Subgroup V where
  carrier := {v | B z v = 0 ∧ B f v = 0}
  mul_mem' := fun {a b} ha hb => ⟨by rw [hB.mul_right, ha.1, hb.1, add_zero],
    by rw [hB.mul_right, ha.2, hb.2, add_zero]⟩
  one_mem' := ⟨Sp4.B_one_right hB z, Sp4.B_one_right hB f⟩
  inv_mem' := fun {a} ha => by
    rw [Set.mem_setOf_eq, inv_eq_of_mul_eq_one_right (hB.sq_eq_one a)]
    exact ha

private theorem p16b_B_expand {B : V → V → ZMod 2} (hB : SympForm B) (a k z f : V) (β γ : ZMod 2) :
    B a (k * Sp4.pw z β * Sp4.pw f γ) = B a k + β * B a z + γ * B a f := by
  rw [hB.mul_right, hB.mul_right, Sp4.B_pw_right hB, Sp4.B_pw_right hB]

private theorem p16b_decomp {B : V → V → ZMod 2} (hB : SympForm B) {z f : V} (hzf : B z f = 1) (v :
    V) :
    ∃ k : V, B z k = 0 ∧ B f k = 0 ∧ v = k * Sp4.pw z (B f v) * Sp4.pw f (B z v) := by
  have hzf' : B f z = 1 := (hB.symm f z).trans hzf
  refine ⟨v * Sp4.pw z (B f v) * Sp4.pw f (B z v), ?_, ?_, ?_⟩
  · rw [p16b_B_expand hB, hB.alt, hzf, mul_zero, mul_one, add_zero]
    exact p16b_add_self _
  · rw [p16b_B_expand hB, hB.alt, hzf', mul_one, mul_zero, add_zero]
    exact p16b_add_self _
  · calc v = v * (Sp4.pw z (B f v) * Sp4.pw z (B f v)) * (Sp4.pw f (B z v) * Sp4.pw f (B z v)) := by
          rw [p16b_pw_sq (hB.sq_eq_one z), p16b_pw_sq (hB.sq_eq_one f), mul_one, mul_one]
      _ = v * Sp4.pw z (B f v) * Sp4.pw f (B z v) * Sp4.pw z (B f v) * Sp4.pw f (B z v) := by
          ac_rfl

private theorem p16b_natCard_K [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) (hcard : Nat.card
    V = 64)
    {z f : V} (hzf : B z f = 1) : Nat.card (p16bK hB z f) = 16 := by
  let Φ : p16bK hB z f × (ZMod 2 × ZMod 2) → V :=
    fun p => (p.1 : V) * Sp4.pw z p.2.1 * Sp4.pw f p.2.2
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨k, hk⟩, β, γ⟩ ⟨⟨k', hk'⟩, β', γ'⟩ h
    have hk1 : B z k = 0 := hk.1
    have hk2 : B f k = 0 := hk.2
    have hk1' : B z k' = 0 := hk'.1
    have hk2' : B f k' = 0 := hk'.2
    have h1 : B z (k * Sp4.pw z β * Sp4.pw f γ) = B z (k' * Sp4.pw z β' * Sp4.pw f γ') :=
      congrArg (B z) h
    have h2 : B f (k * Sp4.pw z β * Sp4.pw f γ) = B f (k' * Sp4.pw z β' * Sp4.pw f γ') :=
      congrArg (B f) h
    rw [p16b_B_expand hB, p16b_B_expand hB, hk1, hk1', hB.alt, hzf] at h1
    rw [p16b_B_expand hB, p16b_B_expand hB, hk2, hk2', hB.alt,
      (hB.symm f z).trans hzf] at h2
    simp only [zero_add, mul_zero, mul_one, add_zero, zero_add] at h1 h2
    have hγ : γ = γ' := h1
    have hβ : β = β' := h2
    subst hγ
    subst hβ
    have hkk : k * Sp4.pw z β = k' * Sp4.pw z β := mul_right_cancel h
    have hkk' : k = k' := mul_right_cancel hkk
    subst hkk'
    rfl
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨k, hkz, hkf, hv⟩ := p16b_decomp hB hzf v
    exact ⟨(⟨k, ⟨hkz, hkf⟩⟩, B f v, B z v), hv.symm⟩
  have h := Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod, hcard] at h
  omega

private theorem p16b_sympK [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) {z f : V} (hzf : B z f
    = 1) :
    SympForm (fun a b : p16bK hB z f => B (a : V) (b : V)) where
  sq_eq_one a := Subtype.ext (hB.sq_eq_one a)
  mul_left a a' b := hB.mul_left a a' b
  mul_right a b b' := hB.mul_right a b b'
  alt a := hB.alt a
  nondeg a ha := by
    apply Subtype.ext
    apply hB.nondeg
    intro v
    obtain ⟨k, hkz, hkf, hv⟩ := p16b_decomp hB hzf v
    have haz : B z (a : V) = 0 := a.2.1
    have haf : B f (a : V) = 0 := a.2.2
    have hak : B (a : V) k = 0 := ha ⟨k, ⟨hkz, hkf⟩⟩
    rw [hv, p16b_B_expand hB, hak, (hB.symm _ _).trans haz, (hB.symm _ _).trans haf]
    simp

private def p16bRes (B : V → V → ZMod 2) (z f x : V) : V := x * Sp4.pw z (B f x)

private theorem p16b_res_mem {B : V → V → ZMod 2} (hB : SympForm B) {z f x : V} (hzf : B z f = 1)
    (hx : B z x = 0) : p16bRes B z f x ∈ p16bK hB z f := by
  have hzf' : B f z = 1 := (hB.symm f z).trans hzf
  refine ⟨?_, ?_⟩
  · show B z (x * Sp4.pw z (B f x)) = 0
    rw [hB.mul_right, hx, Sp4.B_pw_right hB, hB.alt, mul_zero, zero_add]
  · show B f (x * Sp4.pw z (B f x)) = 0
    rw [hB.mul_right, Sp4.B_pw_right hB, hzf', mul_one]
    exact p16b_add_self _

private theorem p16b_res_ne_one {B : V → V → ZMod 2} (hB : SympForm B) {z f x : V} (hx1 : x ≠ 1)
    (hxz : x ≠ z) : p16bRes B z f x ≠ 1 := by
  intro h
  unfold p16bRes at h
  have hx : x = Sp4.pw z (B f x) := by
    calc x = x * (Sp4.pw z (B f x) * Sp4.pw z (B f x)) := by
          rw [p16b_pw_sq (hB.sq_eq_one z), mul_one]
      _ = (x * Sp4.pw z (B f x)) * Sp4.pw z (B f x) := by ac_rfl
      _ = Sp4.pw z (B f x) := by rw [h, one_mul]
  generalize B f x = c at hx
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · rw [Sp4.pw_zero] at hx
    exact hx1 hx
  · rw [Sp4.pw_one] at hx
    exact hxz hx

private theorem p16b_res_B {B : V → V → ZMod 2} (hB : SympForm B) {z f x y : V} (hzf : B z f = 1)
    (hx : B z x = 0) (hy : B z y = 0) :
    B (p16bRes B z f x) (p16bRes B z f y) = B x y := by
  have hxz : B x z = 0 := (hB.symm x z).trans hx
  unfold p16bRes
  simp only [hB.mul_left, hB.mul_right, Sp4.B_pw_left hB, Sp4.B_pw_right hB, hxz, hy, hB.alt,
    mul_zero, zero_mul, add_zero, zero_add]

private theorem p16b_no_six_residue [Finite V] {B : V → V → ZMod 2} (hB : SympForm B)
    (hcard : Nat.card V = 64) {z f : V} (hzf : B z f = 1) {T : Set V} (hT : 6 ≤ T.ncard)
    (hz : ∀ x ∈ T, B z x = 0 ∧ x ≠ 1 ∧ x ≠ z) (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → B x y = 1) :
    False := by
  classical
  have hTfin : T.Finite := Set.toFinite T
  have hinjT : Set.InjOn (p16bRes B z f) T := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hpair x hx y hy hne
    have h2 := p16b_res_B hB hzf (hz x hx).1 (hz y hy).1
    rw [hxy, hB.alt, h1] at h2
    exact absurd h2 (by decide)
  set F : Finset V := hTfin.toFinset with hF
  have hFcard : F.card = T.ncard := (Set.ncard_eq_toFinset_card T hTfin).symm
  have hmemF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  have hImg : (F.image (p16bRes B z f)).card = F.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    exact hinjT ((hmemF x).mp hx) ((hmemF y).mp hy) hxy
  have hsub : ∀ x ∈ F, p16bRes B z f x ∈ p16bK hB z f := fun x hx =>
    p16b_res_mem hB hzf ((hz x ((hmemF x).mp hx)).1)
  set G : Finset (p16bK hB z f) :=
    (F.image (p16bRes B z f)).subtype (fun v => v ∈ p16bK hB z f) with hG
  have hGcard : 6 ≤ G.card := by
    rw [hG, Finset.card_subtype, Finset.filter_true_of_mem, hImg, hFcard]
    · exact hT
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact hsub x hx
  have h1mem : (1 : V) ∉ F.image (p16bRes B z f) := by
    intro h
    obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp h
    exact p16b_res_ne_one hB (hz x ((hmemF x).mp hx)).2.1 (hz x ((hmemF x).mp hx)).2.2 hxr
  have h1G : (1 : p16bK hB z f) ∉ G := by
    intro h
    rw [hG, Finset.mem_subtype] at h
    exact h1mem h
  obtain ⟨u, hu, w, hw, huw, hBuw⟩ :=
    exists_orth_of_card_six (p16b_sympK hB hzf) (p16b_natCard_K hB hcard hzf) G hGcard h1G
  rw [hG, Finset.mem_subtype, Finset.mem_image] at hu hw
  obtain ⟨x, hx, hxu⟩ := hu
  obtain ⟨y, hy, hyw⟩ := hw
  have hxy : x ≠ y := by
    intro h
    apply huw
    apply Subtype.ext
    rw [← hxu, ← hyw, h]
  have h1 := hpair x ((hmemF x).mp hx) y ((hmemF y).mp hy) hxy
  have h2 := p16b_res_B hB hzf (hz x ((hmemF x).mp hx)).1 (hz y ((hmemF y).mp hy)).1
  rw [hxu, hyw, h1] at h2
  have hBuw' : B (u : V) (w : V) = 0 := hBuw
  rw [h2] at hBuw'
  exact absurd hBuw' (by decide)

private theorem p16b_exists_pair {B : V → V → ZMod 2} (hB : SympForm B) {z : V} (hz : z ≠ 1) :
    ∃ f : V, B z f = 1 := by
  by_contra h
  push Not at h
  apply hz
  apply hB.nondeg
  intro b
  have hb := h b
  generalize B z b = c at hb ⊢
  revert hb
  revert c
  decide

private theorem p16b_half [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) {z f : V} (hzf : B z f
    = 1)
    {N : Set V} (hN : ∀ x ∈ N, z * x ∈ N) : 2 * {x ∈ N | B f x = 0}.ncard = N.ncard := by
  have hzf' : B f z = 1 := (hB.symm f z).trans hzf
  have key : ∀ x, B f (z * x) = B f x + 1 := fun x => by
    rw [hB.mul_right, hzf', add_comm]
  have hzz : ∀ x, z * (z * x) = x := fun x => by
    rw [← mul_assoc, hB.sq_eq_one z, one_mul]
  have hA' : {x ∈ N | ¬ B f x = 0} = (fun x => z * x) '' {x ∈ N | B f x = 0} := by
    ext x
    constructor
    · rintro ⟨hxN, hx⟩
      have hx1 : B f x = 1 := by
        generalize B f x = c at hx ⊢
        revert hx
        revert c
        decide
      refine ⟨z * x, ⟨hN x hxN, ?_⟩, hzz x⟩
      rw [key, hx1]
      decide
    · rintro ⟨y, ⟨hyN, hy⟩, rfl⟩
      show z * y ∈ N ∧ ¬ B f (z * y) = 0
      refine ⟨hN y hyN, ?_⟩
      rw [key, hy]
      decide
  have hdisj : Disjoint {x ∈ N | B f x = 0} {x ∈ N | ¬ B f x = 0} := by
    rw [Set.disjoint_left]
    rintro x ⟨_, h1⟩ ⟨_, h2⟩
    exact h2 h1
  have hunion : {x ∈ N | B f x = 0} ∪ {x ∈ N | ¬ B f x = 0} = N := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · exact h
    · intro hx
      by_cases h : B f x = 0
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hnc := Set.ncard_union_eq hdisj
  rw [hunion, hA', Set.ncard_image_of_injective _ (mul_right_injective z)] at hnc
  omega

theorem false_of_two_sections [Finite V] {B : V → V → ZMod 2} (hB : SympForm B) {S : Set V}
    {a : ℕ} (hS : PointSet B S a) (hcard : Nat.card V = 64) {t e : V} (ht : t ∈ S)
    (hte : B e t = 0) {A₁ A₂ : Set V} (hA₁ : A₁ ⊆ nbr B S t) (hA₂ : A₂ ⊆ nbr B S t)
    (hc₁ : A₁.ncard = 6) (hc₂ : A₂.ncard = 6) (hd : Disjoint A₁ A₂)
    (hl₁ : ∀ j ∈ A₁, t * j ∈ A₁) (hl₂ : ∀ j ∈ A₂, t * j ∈ A₂)
    (hp₁ : ∀ j ∈ A₁, ∀ y ∈ A₁, y ≠ j → y ≠ t * j → B j y = 1)
    (hp₂ : ∀ j ∈ A₂, ∀ y ∈ A₂, y ≠ j → y ≠ t * j → B j y = 1)
    (hzero : ∀ j ∈ nbr B S t, B e j = 0 ↔ j ∈ A₁ ∪ A₂) : False := by
  classical
  have ht1 : t ≠ 1 := fun h => hS.one_notMem (h ▸ ht)
  obtain ⟨f, hf⟩ := p16b_exists_pair hB ht1
  have hf' : B f t = 1 := (hB.symm f t).trans hf
  set N : Set V := A₁ ∪ A₂ with hN
  have hNcard : N.ncard = 12 := by rw [hN, Set.ncard_union_eq hd, hc₁, hc₂]
  have hNcl : ∀ x ∈ N, t * x ∈ N := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hl₁ x hx)
    · exact Or.inr (hl₂ x hx)
  have hhalf := p16b_half hB hf hNcl
  have hNnbr : ∀ x ∈ N, x ∈ nbr B S t := by
    intro x hx
    rcases hx with hx | hx
    · exact hA₁ hx
    · exact hA₂ hx
  have claim : ∀ j ∈ N, ∀ y ∈ N, y ≠ j → y ≠ t * j → B j y = 1 := by
    intro j hj y hy hyj hyt
    by_contra hne
    have hB0 : B j y = 0 := by
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (B j y) with h | h
      · exact h
      · exact absurd h hne
    have hjnbr := hNnbr j hj
    have hynbr := hNnbr y hy
    have hjS : j ∈ S := hjnbr.1
    have hyS : y ∈ S := hynbr.1
    have hj1 : j ≠ 1 := fun h => hS.one_notMem (h ▸ hjS)
    have hy1 : y ≠ 1 := fun h => hS.one_notMem (h ▸ hyS)
    have hjt : j ≠ t := hjnbr.2.1
    have hyt' : y ≠ t := hynbr.2.1
    have hBtj : B t j = 0 := hjnbr.2.2
    have hBty : B t y = 0 := hynbr.2.2
    have hjy : j ≠ y := Ne.symm hyj
    have hw_S : j * y ∈ S := hS.mul_mem_of_orth j hjS y hyS hjy hB0
    have hw_nbr : j * y ∈ nbr B S t := by
      refine ⟨hw_S, ?_, ?_⟩
      · intro h
        apply hyt
        calc y = j * (j * y) := by rw [← mul_assoc, hB.sq_eq_one j, one_mul]
          _ = j * t := by rw [h]
          _ = t * j := mul_comm _ _
      · rw [hB.mul_right, hBtj, hBty, add_zero]
    have hBe_j : B e j = 0 := (hzero j hjnbr).mpr hj
    have hBe_y : B e y = 0 := (hzero y hynbr).mpr hy
    have hw_N : j * y ∈ N :=
      (hzero (j * y) hw_nbr).mp (by rw [hB.mul_right, hBe_j, hBe_y, add_zero])
    have hByj : B y j = 0 := (hB.symm y j).trans hB0
    have hBjw : B j (j * y) = 0 := by rw [hB.mul_right, hB.alt, hB0, zero_add]
    have hBwj : B (j * y) j = 0 := (hB.symm _ _).trans hBjw
    have hByw : B y (j * y) = 0 := by rw [hB.mul_right, hB.alt, hByj, add_zero]
    have hBwy : B (j * y) y = 0 := (hB.symm _ _).trans hByw
    have hwj : j * y ≠ j := by
      intro h
      apply hy1
      calc y = j * (j * y) := by rw [← mul_assoc, hB.sq_eq_one j, one_mul]
        _ = j * j := by rw [h]
        _ = 1 := hB.sq_eq_one j
    have hwy : j * y ≠ y := by
      intro h
      apply hj1
      calc j = (j * y) * y := by rw [mul_assoc, hB.sq_eq_one y, mul_one]
        _ = y * y := by rw [h]
        _ = 1 := hB.sq_eq_one y
    have hwt_j : j * y ≠ t * j := by
      intro h
      apply hyt'
      calc y = j * (j * y) := by rw [← mul_assoc, hB.sq_eq_one j, one_mul]
        _ = j * (t * j) := by rw [h]
        _ = t * (j * j) := by ac_rfl
        _ = t := by rw [hB.sq_eq_one j, mul_one]
    have hwty : j * y ≠ t * y := by
      intro h
      apply hjt
      calc j = (j * y) * y := by rw [mul_assoc, hB.sq_eq_one y, mul_one]
        _ = (t * y) * y := by rw [h]
        _ = t := by rw [mul_assoc, hB.sq_eq_one y, mul_one]
    have hjwt : j ≠ t * y := by
      intro h
      apply hyt
      calc y = t * (t * y) := by rw [← mul_assoc, hB.sq_eq_one t, one_mul]
        _ = t * j := by rw [← h]
    have hjwt'' : j ≠ t * (j * y) := by
      intro h
      have hty : t * y = 1 := by
        calc t * y = t * ((j * j) * y) := by rw [hB.sq_eq_one j, one_mul]
          _ = t * (j * (j * y)) := by rw [mul_assoc]
          _ = j * (t * (j * y)) := by ac_rfl
          _ = j * j := by rw [← h]
          _ = 1 := hB.sq_eq_one j
      apply hyt'
      calc y = t * (t * y) := by rw [← mul_assoc, hB.sq_eq_one t, one_mul]
        _ = t * 1 := by rw [hty]
        _ = t := mul_one t
    have hyw_t : y ≠ t * (j * y) := by
      intro h
      have htyj : t * y = j * y := by
        calc t * y = t * (t * (j * y)) := by rw [← h]
          _ = (t * t) * (j * y) := by rw [mul_assoc]
          _ = j * y := by rw [hB.sq_eq_one t, one_mul]
      exact hjt (mul_right_cancel htyj).symm
    rcases hj with hj | hj <;> rcases hy with hy | hy <;> rcases hw_N with hw | hw
    all_goals first
      | exact one_ne_zero ((hp₁ j hj y hy hyj hyt).symm.trans hB0)
      | exact one_ne_zero ((hp₂ j hj y hy hyj hyt).symm.trans hB0)
      | exact one_ne_zero ((hp₁ y hy j hj hjy hjwt).symm.trans hByj)
      | exact one_ne_zero ((hp₂ y hy j hj hjy hjwt).symm.trans hByj)
      | exact one_ne_zero ((hp₁ j hj (j * y) hw hwj hwt_j).symm.trans hBjw)
      | exact one_ne_zero ((hp₂ j hj (j * y) hw hwj hwt_j).symm.trans hBjw)
      | exact one_ne_zero ((hp₁ (j * y) hw j hj (Ne.symm hwj) hjwt'').symm.trans hBwj)
      | exact one_ne_zero ((hp₂ (j * y) hw j hj (Ne.symm hwj) hjwt'').symm.trans hBwj)
      | exact one_ne_zero ((hp₁ y hy (j * y) hw hwy hwty).symm.trans hByw)
      | exact one_ne_zero ((hp₂ y hy (j * y) hw hwy hwty).symm.trans hByw)
      | exact one_ne_zero ((hp₁ (j * y) hw y hy (Ne.symm hwy) hyw_t).symm.trans hBwy)
      | exact one_ne_zero ((hp₂ (j * y) hw y hy (Ne.symm hwy) hyw_t).symm.trans hBwy)
  set R : Set V := {x ∈ N | B f x = 0} with hR
  have hRcard : R.ncard = 6 := by omega
  apply p16b_no_six_residue hB hcard hf (le_of_eq hRcard.symm)
  · intro x hx
    have hxN : x ∈ N := hx.1
    exact ⟨(hNnbr x hxN).2.2, fun h => hS.one_notMem (h ▸ (hNnbr x hxN).1),
      (hNnbr x hxN).2.1⟩
  · intro x hx y hy hxy
    apply claim x hx.1 y hy.1 (Ne.symm hxy)
    intro hyt
    have h := hy.2
    rw [hyt, hB.mul_right, hf', hx.2, add_zero] at h
    exact one_ne_zero h

structure Sections (B : V → V → ZMod 2) (S : Set V) (𝓔 : Set V) : Prop where
  ne_one : ∀ e ∈ 𝓔, e ≠ 1
  card_sigma : ∀ e ∈ 𝓔, (sigma B S e).ncard = 15
  card_nbr_sigma : ∀ e ∈ 𝓔, ∀ p ∈ sigma B S e, (nbr B S p ∩ sigma B S e).ncard = 6
  noplane : ∀ e ∈ 𝓔, ∀ p ∈ sigma B S e, ∀ x ∈ nbr B S p ∩ sigma B S e,
    ∀ y ∈ nbr B S p ∩ sigma B S e, y ≠ x → y ≠ p * x → B x y = 1
  unique : ∀ p ∈ S, ∀ x ∈ nbr B S p, ∃! e, e ∈ 𝓔 ∧ p ∈ sigma B S e ∧ x ∈ sigma B S e

private theorem p16b_S_part {B : V → V → ZMod 2} {S : Set V} {a : ℕ} (hS : PointSet B S a) {z : V}
    (hz : z ∈ S) : S = insert z (nbr B S z ∪ far B S z) := by
  ext q
  constructor
  · intro hq
    by_cases hqz : q = z
    · rw [hqz]
      exact Set.mem_insert _ _
    · apply Set.mem_insert_of_mem
      by_cases hb : B z q = 0
      · exact Or.inl ⟨hq, hqz, hb⟩
      · refine Or.inr ⟨hq, ?_⟩
        generalize B z q = c at hb ⊢
        revert hb
        revert c
        decide
  · intro hq
    rcases hq with rfl | hq
    · exact hz
    · rcases hq with hq | hq
      · exact hq.1
      · exact hq.1

private theorem p16b_nbr_mul {B : V → V → ZMod 2} {S : Set V} {a : ℕ} (hB : SympForm B)
    (hS : PointSet B S a) {z x : V} (hz : z ∈ S) (hx : x ∈ nbr B S z) : z * x ∈ nbr B S z := by
  have hx1 : x ≠ 1 := fun h => hS.one_notMem (h ▸ hx.1)
  refine ⟨hS.mul_mem_of_orth z hz x hx.1 (Ne.symm hx.2.1) hx.2.2, ?_, ?_⟩
  · intro h
    apply hx1
    calc x = z * (z * x) := by rw [← mul_assoc, hB.sq_eq_one z, one_mul]
      _ = z * z := by rw [h]
      _ = 1 := hB.sq_eq_one z
  · rw [hB.mul_right, hB.alt, hx.2.2, zero_add]

private theorem p16b_filter_card [Finite V] (T : Set V) (P : V → Prop) [DecidablePred P] :
    ((T.toFinite.toFinset).filter P).card = {q | q ∈ T ∧ P q}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext q
  simp [Set.Finite.mem_toFinset]

private theorem p16b_dc [Finite V] (E G : Set V) (r : V → V → Prop) [DecidableRel r] :
    ∑ e ∈ E.toFinite.toFinset, {q | q ∈ G ∧ r e q}.ncard =
      ∑ q ∈ G.toFinite.toFinset, {e | e ∈ E ∧ r e q}.ncard := by
  have h1 : ∀ e, {q | q ∈ G ∧ r e q}.ncard =
      ∑ q ∈ G.toFinite.toFinset, if r e q then 1 else 0 := by
    intro e
    rw [← p16b_filter_card G (r e), Finset.card_filter]
  have h2 : ∀ q, {e | e ∈ E ∧ r e q}.ncard =
      ∑ e ∈ E.toFinite.toFinset, if r e q then 1 else 0 := by
    intro q
    rw [← p16b_filter_card E (fun e => r e q), Finset.card_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

private theorem p16b_sum_zmod {ι : Type*} [DecidableEq ι] (T : Finset ι) (g : ι → ZMod 2) :
    ∑ i ∈ T, g i = ((T.filter (fun i => g i ≠ 0)).card : ZMod 2) := by
  have hg : ∀ c : ZMod 2, c = if c ≠ 0 then 1 else 0 := by decide
  rw [Finset.sum_congr rfl (fun i _ => hg (g i)), Finset.sum_boole]

private theorem p16b_B_prod_right {ι : Type*} [DecidableEq ι] {B : V → V → ZMod 2} (hB : SympForm B)
    (b : V) (f : ι → V) (T : Finset ι) : B b (∏ i ∈ T, f i) = ∑ i ∈ T, B b (f i) := by
  induction T using Finset.induction_on with
  | empty => simp [Sp4.B_one_right hB b]
  | insert x T hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, hB.mul_right, ih]

private theorem p16b_count [Finite V] {B : V → V → ZMod 2} {S : Set V} {𝓔 : Set V} (hB : SympForm B)
    (hS : PointSet B S 9) (hSec : Sections B S 𝓔) {z : V} (hz : z ∈ S)
    (hE : ∀ q ∈ S, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard = 3) :
    𝓔.ncard = 7 ∧ S.ncard = 35 := by
  classical
  have hzz : B z z = 0 := hB.alt z
  have hSpart := p16b_S_part hS hz
  have hdisj_nf : Disjoint (nbr B S z) (far B S z) := by
    rw [Set.disjoint_left]
    intro q hq hq'
    have h1 : B z q = 0 := hq.2.2
    have h2 : B z q = 1 := hq'.2
    rw [h1] at h2
    exact zero_ne_one h2
  have hz_notin : z ∉ nbr B S z ∪ far B S z := by
    rintro (h | h)
    · exact h.2.1 rfl
    · have h2 : B z z = 1 := h.2
      rw [hzz] at h2
      exact zero_ne_one h2
  have hcardS : S.ncard = (far B S z).ncard + 19 := by
    have h := congrArg Set.ncard hSpart
    rw [Set.ncard_insert_of_notMem hz_notin, Set.ncard_union_eq hdisj_nf, hS.card_nbr z hz] at h
    omega
  have hEz : ∀ e ∈ 𝓔, z ∈ sigma B S e → (far B S z ∩ sigma B S e).ncard = 8 := by
    intro e he hze
    have hpart : sigma B S e = insert z ((nbr B S z ∩ sigma B S e) ∪ (far B S z ∩ sigma B S e)) :=
    by
      ext q
      constructor
      · intro hq
        have hqS : q ∈ S := hq.1
        rw [hSpart] at hqS
        rcases hqS with rfl | hqS
        · exact Set.mem_insert _ _
        · apply Set.mem_insert_of_mem
          rcases hqS with h | h
          · exact Or.inl ⟨h, hq⟩
          · exact Or.inr ⟨h, hq⟩
      · rintro (rfl | ⟨_, hq⟩ | ⟨_, hq⟩)
        · exact hze
        · exact hq
        · exact hq
    have hdisj : Disjoint (nbr B S z ∩ sigma B S e) (far B S z ∩ sigma B S e) := by
      rw [Set.disjoint_left]
      rintro q ⟨h1, _⟩ ⟨h2, _⟩
      exact Set.disjoint_left.mp hdisj_nf h1 h2
    have hzn : z ∉ (nbr B S z ∩ sigma B S e) ∪ (far B S z ∩ sigma B S e) := by
      rintro (h | h)
      · exact h.1.2.1 rfl
      · have h2 : B z z = 1 := h.1.2
        rw [hzz] at h2
        exact zero_ne_one h2
    have h := congrArg Set.ncard hpart
    rw [Set.ncard_insert_of_notMem hzn, Set.ncard_union_eq hdisj, hSec.card_nbr_sigma e he z hze,
      hSec.card_sigma e he] at h
    omega
  have hEz' : ∀ e ∈ 𝓔, z ∉ sigma B S e → (far B S z ∩ sigma B S e).ncard = 6 := by
    intro e he hze
    have hzf : B z e = 1 := by
      have h1 : B e z = 1 := by
        have hez : B e z ≠ 0 := fun h => hze ⟨hz, h⟩
        generalize B e z = c at hez ⊢
        revert hez
        revert c
        decide
      exact (hB.symm z e).trans h1
    have hN := p16b_half hB hzf (N := nbr B S z) (fun x hx => p16b_nbr_mul hB hS hz hx)
    rw [hS.card_nbr z hz] at hN
    have hset : {x ∈ nbr B S z | B e x = 0} = nbr B S z ∩ sigma B S e := by
      ext x
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, hx.1, h⟩
      · rintro ⟨hx, _, h⟩
        exact ⟨hx, h⟩
    rw [hset] at hN
    have hpart : sigma B S e = (nbr B S z ∩ sigma B S e) ∪ (far B S z ∩ sigma B S e) := by
      ext q
      constructor
      · intro hq
        have hqS : q ∈ S := hq.1
        rw [hSpart] at hqS
        rcases hqS with rfl | hqS
        · exact absurd hq hze
        · rcases hqS with h | h
          · exact Or.inl ⟨h, hq⟩
          · exact Or.inr ⟨h, hq⟩
      · rintro (⟨_, hq⟩ | ⟨_, hq⟩)
        · exact hq
        · exact hq
    have hdisj : Disjoint (nbr B S z ∩ sigma B S e) (far B S z ∩ sigma B S e) := by
      rw [Set.disjoint_left]
      rintro q ⟨h1, _⟩ ⟨h2, _⟩
      exact Set.disjoint_left.mp hdisj_nf h1 h2
    have h := congrArg Set.ncard hpart
    rw [Set.ncard_union_eq hdisj, hSec.card_sigma e he] at h
    omega
  have hsig : ∀ e, {q | q ∈ S ∧ q ∈ sigma B S e} = sigma B S e := fun e => by
    ext q
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hDC1 : ∑ e ∈ 𝓔.toFinite.toFinset, {q | q ∈ S ∧ q ∈ sigma B S e}.ncard =
      ∑ q ∈ S.toFinite.toFinset, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard :=
    p16b_dc 𝓔 S (fun e q => q ∈ sigma B S e)
  have hDC2 : ∑ e ∈ 𝓔.toFinite.toFinset, {q | q ∈ far B S z ∧ q ∈ sigma B S e}.ncard =
      ∑ q ∈ (far B S z).toFinite.toFinset, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard :=
    p16b_dc 𝓔 (far B S z) (fun e q => q ∈ sigma B S e)
  have hcE : 𝓔.toFinite.toFinset.card = 𝓔.ncard :=
    (Set.ncard_eq_toFinset_card 𝓔 (Set.toFinite 𝓔)).symm
  have hcS : S.toFinite.toFinset.card = S.ncard :=
    (Set.ncard_eq_toFinset_card S (Set.toFinite S)).symm
  have hcF : (far B S z).toFinite.toFinset.card = (far B S z).ncard :=
    (Set.ncard_eq_toFinset_card (far B S z) (Set.toFinite _)).symm
  have hL1 : ∑ e ∈ 𝓔.toFinite.toFinset, {q | q ∈ S ∧ q ∈ sigma B S e}.ncard =
      15 * 𝓔.ncard := by
    rw [← hcE, Finset.sum_congr rfl (fun e he => by
      rw [hsig e, hSec.card_sigma e ((Set.Finite.mem_toFinset _).mp he)])]
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  have hR1 : ∑ q ∈ S.toFinite.toFinset, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard = 3 * S.ncard := by
    rw [← hcS, Finset.sum_congr rfl (fun q hq => hE q ((Set.Finite.mem_toFinset _).mp hq))]
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  have hR2 : ∑ q ∈ (far B S z).toFinite.toFinset, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard =
      3 * (far B S z).ncard := by
    rw [← hcF, Finset.sum_congr rfl (fun q hq => hE q (((Set.Finite.mem_toFinset _).mp hq).1))]
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  have hmem𝓔 : ∀ e ∈ 𝓔.toFinite.toFinset, e ∈ 𝓔 := fun e he => (Set.Finite.mem_toFinset _).mp he
  have hEz2 : ∀ e ∈ 𝓔, z ∈ sigma B S e → {q | q ∈ far B S z ∧ q ∈ sigma B S e}.ncard = 8 :=
    fun e he hze => hEz e he hze
  have hEz2' : ∀ e ∈ 𝓔, z ∉ sigma B S e → {q | q ∈ far B S z ∧ q ∈ sigma B S e}.ncard = 6 :=
    fun e he hze => hEz' e he hze
  have hfil3 : (𝓔.toFinite.toFinset.filter (fun e => z ∈ sigma B S e)).card = 3 := by
    rw [p16b_filter_card 𝓔 (fun e => z ∈ sigma B S e)]
    exact hE z hz
  have hsplit := Finset.card_filter_add_card_filter_not (s := 𝓔.toFinite.toFinset)
    (p := fun e => z ∈ sigma B S e)
  beta_reduce at hsplit
  have hsplit2 := Finset.sum_filter_add_sum_filter_not 𝓔.toFinite.toFinset
    (fun e => z ∈ sigma B S e) (fun e => {q | q ∈ far B S z ∧ q ∈ sigma B S e}.ncard)
  beta_reduce at hsplit2
  have hA : ∑ e ∈ 𝓔.toFinite.toFinset.filter (fun e => z ∈ sigma B S e),
      {q | q ∈ far B S z ∧ q ∈ sigma B S e}.ncard =
        ∑ e ∈ 𝓔.toFinite.toFinset.filter (fun e => z ∈ sigma B S e), 8 := by
    apply Finset.sum_congr rfl
    intro e he
    exact hEz2 e (hmem𝓔 e (Finset.mem_filter.mp he).1) (Finset.mem_filter.mp he).2
  have hB' : ∑ e ∈ 𝓔.toFinite.toFinset.filter (fun e => ¬ z ∈ sigma B S e),
      {q | q ∈ far B S z ∧ q ∈ sigma B S e}.ncard =
        ∑ e ∈ 𝓔.toFinite.toFinset.filter (fun e => ¬ z ∈ sigma B S e), 6 := by
    apply Finset.sum_congr rfl
    intro e he
    exact hEz2' e (hmem𝓔 e (Finset.mem_filter.mp he).1) (Finset.mem_filter.mp he).2
  rw [Finset.sum_const, smul_eq_mul, hfil3] at hA
  rw [Finset.sum_const, smul_eq_mul] at hB'
  have hfinal1 : 15 * 𝓔.ncard = 3 * S.ncard := by
    rw [← hL1, ← hR1, hDC1]
  have hfinal2 : 3 * (far B S z).ncard = 8 * 3 + 6 * (𝓔.toFinite.toFinset.filter
      (fun e => ¬ z ∈ sigma B S e)).card := by
    rw [← hR2, ← hDC2, ← hsplit2, hA, hB']
    omega
  rw [hcE] at hsplit
  constructor <;> omega

private def p16bPerp {B : V → V → ZMod 2} (hB : SympForm B) (w : V) : Subgroup V where
  carrier := {x | B x w = 0}
  mul_mem' := fun {a b} ha hb => by
    have ha' : B a w = 0 := ha
    have hb' : B b w = 0 := hb
    show B (a * b) w = 0
    rw [hB.mul_left, ha', hb', add_zero]
  one_mem' := Sp4.B_one_left hB w
  inv_mem' := fun {a} ha => by
    have ha' : B a w = 0 := ha
    show B a⁻¹ w = 0
    rw [inv_eq_of_mul_eq_one_right (hB.sq_eq_one a)]
    exact ha'

private theorem p16b_ncard_diff_singleton {s : Set V} {x : V} (h : x ∈ s) (hs : s.Finite) :
    (s \ {x}).ncard + 1 = s.ncard := by
  have hn : x ∉ s \ {x} := fun h' => h'.2 rfl
  rw [← Set.ncard_insert_of_notMem hn (hs.diff), Set.insert_diff_singleton, Set.insert_eq_of_mem h]

private theorem p16b_parity6 : ∀ I J : Finset (Fin 6),
    (∀ j : Fin 6, (I.filter (fun i => i ≠ j)).card % 2 = (J.filter (fun i => i ≠ j)).card % 2) →
      I = J := by
  decide +kernel

private theorem p16b_eq_one_of_perp {B : V → V → ZMod 2} {S : Set V} (hB : SympForm B)
    (hspan : Subgroup.closure S = ⊤) {P : V} (h : ∀ b ∈ S, B b P = 0) : P = 1 := by
  have hle : Subgroup.closure S ≤ p16bPerp hB P :=
    (Subgroup.closure_le (p16bPerp hB P)).mpr (fun b hb => h b hb)
  rw [hspan] at hle
  refine hB.nondeg P (fun b => ?_)
  rw [hB.symm]
  exact hle (Subgroup.mem_top b)

private theorem p16b_span_zero [Finite V] {B : V → V → ZMod 2} (hB : SympForm B)
    (hcard : Nat.card V = 64) {𝓔 : Set V} (h𝓔 : 6 ≤ 𝓔.ncard)
    (h1 : ∀ e ∈ 𝓔, ∀ e' ∈ 𝓔, e ≠ e' → B e e' = 1) {Q : V} (hQ : ∀ e ∈ 𝓔, B Q e = 0) :
    Q = 1 := by
  classical
  obtain ⟨T, hT𝓔, hTcard⟩ := Set.exists_subset_card_eq h𝓔
  have hTfin : T.Finite := Set.toFinite T
  have hTf6 : (hTfin.toFinset).card = 6 := by
    rw [← Set.ncard_eq_toFinset_card T hTfin, hTcard]
  have hTfmem : ∀ e ∈ hTfin.toFinset, e ∈ 𝓔 := fun e he => hT𝓔 ((hTfin.mem_toFinset).mp he)
  have eq6 : hTfin.toFinset ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hTf6])
  let ε : Fin 6 → V := fun i => ((eq6.symm i : hTfin.toFinset) : V)
  have hεmem : ∀ i, ε i ∈ 𝓔 := fun i => hTfmem _ (eq6.symm i).2
  have hεinj : Function.Injective ε := by
    intro i j hij
    exact eq6.symm.injective (Subtype.ext hij)
  have hpar : ∀ (I : Finset (Fin 6)) (j : Fin 6),
      B (ε j) (∏ i ∈ I, ε i) = ((I.filter (fun i => i ≠ j)).card : ZMod 2) := by
    intro I j
    rw [p16b_B_prod_right hB, p16b_sum_zmod]
    rw [Finset.filter_congr (q := fun i => i ≠ j) ?_]
    intro i _
    constructor
    · intro h hij
      apply h
      rw [hij, hB.alt]
    · intro hij
      rw [h1 (ε j) (hεmem j) (ε i) (hεmem i) (fun h => hij (hεinj h).symm)]
      decide
  have hinj : Function.Injective (fun I : Finset (Fin 6) => ∏ i ∈ I, ε i) := by
    intro I J hIJ
    have hIJ' : ∏ i ∈ I, ε i = ∏ i ∈ J, ε i := hIJ
    apply p16b_parity6
    intro j
    have h2 := congrArg (B (ε j)) hIJ'
    rw [hpar, hpar] at h2
    exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mp h2
  have hbij : Function.Bijective (fun I : Finset (Fin 6) => ∏ i ∈ I, ε i) := by
    apply Function.Injective.bijective_of_nat_card_le hinj
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
    norm_num
  refine hB.nondeg Q (fun y => ?_)
  obtain ⟨I, hI⟩ := hbij.2 y
  rw [← hI, p16b_B_prod_right hB]
  exact Finset.sum_eq_zero (fun i _ => hQ (ε i) (hεmem i))

namespace Sections

variable {B : V → V → ZMod 2} {S : Set V} {a : ℕ} {𝓔 : Set V}

theorem card_centres_of_mem [Finite V] (hB : SympForm B) (hS : PointSet B S a)
    (hSec : Sections B S 𝓔) {p : V} (hp : p ∈ S) : a = 3 * {e | e ∈ 𝓔 ∧ p ∈ sigma B S e}.ncard := by
  classical
  have hDC := p16b_dc {e | e ∈ 𝓔 ∧ p ∈ sigma B S e} (nbr B S p) (fun e x => x ∈ sigma B S e)
  beta_reduce at hDC
  have hL : ∑ e ∈ {e | e ∈ 𝓔 ∧ p ∈ sigma B S e}.toFinite.toFinset,
      {q | q ∈ nbr B S p ∧ q ∈ sigma B S e}.ncard =
        ∑ e ∈ {e | e ∈ 𝓔 ∧ p ∈ sigma B S e}.toFinite.toFinset, 6 := by
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨he𝓔, hpe⟩ := (Set.Finite.mem_toFinset _).mp he
    exact hSec.card_nbr_sigma e he𝓔 p hpe
  have hR : ∑ q ∈ (nbr B S p).toFinite.toFinset,
      {e | e ∈ {e | e ∈ 𝓔 ∧ p ∈ sigma B S e} ∧ q ∈ sigma B S e}.ncard =
        ∑ q ∈ (nbr B S p).toFinite.toFinset, 1 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : x ∈ nbr B S p := (Set.Finite.mem_toFinset _).mp hx
    obtain ⟨e0, ⟨he0, hpe0, hxe0⟩, huniq⟩ := hSec.unique p hp x hx'
    rw [Set.ncard_eq_one]
    refine ⟨e0, ?_⟩
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h𝓔, hpe⟩, hxe⟩
      exact huniq e ⟨h𝓔, hpe, hxe⟩
    · rintro rfl
      exact ⟨⟨he0, hpe0⟩, hxe0⟩
  rw [hL, hR] at hDC
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hDC
  have h1 := Set.ncard_eq_toFinset_card {e | e ∈ 𝓔 ∧ p ∈ sigma B S e} (Set.toFinite _)
  have h2 := Set.ncard_eq_toFinset_card (nbr B S p) (Set.toFinite _)
  have h3 := hS.card_nbr p hp
  omega

theorem card_nbr_eq [Finite V] (hB : SympForm B) (hS : PointSet B S a) (hSec : Sections B S 𝓔)
    (hcard : Nat.card V = 64) (hmem : ∃ p ∈ S, ∃ e ∈ 𝓔, ∃ e' ∈ 𝓔, e ≠ e' ∧ p ∈ sigma B S e ∧
      p ∈ sigma B S e') : a = 9 := by
  classical
  obtain ⟨p, hp, e, he, e', he', hee', hpe, hpe'⟩ := hmem
  have hE2 : 2 ≤ {f | f ∈ 𝓔 ∧ p ∈ sigma B S f}.ncard := by
    have hsub : ({e, e'} : Set V) ⊆ {f | f ∈ 𝓔 ∧ p ∈ sigma B S f} := by
      intro f hf
      rcases hf with rfl | hf
      · exact ⟨he, hpe⟩
      · rw [Set.mem_singleton_iff] at hf
        rw [hf]
        exact ⟨he', hpe'⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair hee'] at this
  have ha3 := card_centres_of_mem hB hS hSec hp
  have ha6 : 6 ≤ a := by omega
  have hp1 : p ≠ 1 := fun h => hS.one_notMem (h ▸ hp)
  obtain ⟨f, hf⟩ := p16b_exists_pair hB hp1
  have hN_cl : ∀ x ∈ nbr B S p, p * x ∈ nbr B S p := fun x hx => p16b_nbr_mul hB hS hp hx
  have hplane : ∃ x ∈ nbr B S p, ∃ y ∈ nbr B S p, B x y = 0 ∧ y ≠ x ∧ y ≠ p * x := by
    by_contra hcon
    push Not at hcon
    have hhalf := p16b_half hB hf hN_cl
    rw [hS.card_nbr p hp] at hhalf
    obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_card_eq
      (show 6 ≤ {x ∈ nbr B S p | B f x = 0}.ncard by omega)
    refine p16b_no_six_residue hB hcard hf (le_of_eq hTcard.symm) ?_ ?_
    · intro x hx
      have hxN := (hTsub hx).1
      exact ⟨hxN.2.2, fun h => hS.one_notMem (h ▸ hxN.1), hxN.2.1⟩
    · intro x hx y hy hxy
      by_contra hne
      have h0 : B x y = 0 := by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (B x y) with h | h
        · exact h
        · exact absurd h hne
      have hyp := hcon x (hTsub hx).1 y (hTsub hy).1 h0 (Ne.symm hxy)
      have hyf := (hTsub hy).2
      rw [hyp, hB.mul_right, (hB.symm f p).trans hf, (hTsub hx).2, add_zero] at hyf
      exact one_ne_zero hyf
  obtain ⟨x, hx, y, hy, hxy0, hyx, hypx⟩ := hplane
  have hxS : x ∈ S := hx.1
  have hyS : y ∈ S := hy.1
  have hx1 : x ≠ 1 := fun h => hS.one_notMem (h ▸ hxS)
  have hy1 : y ≠ 1 := fun h => hS.one_notMem (h ▸ hyS)
  have huS : x * y ∈ S := hS.mul_mem_of_orth x hxS y hyS (Ne.symm hyx) hxy0
  have hu_nbr : x * y ∈ nbr B S p := by
    refine ⟨huS, ?_, ?_⟩
    · intro h
      apply hypx
      calc y = x * (x * y) := by rw [← mul_assoc, hB.sq_eq_one x, one_mul]
        _ = x * p := by rw [h]
        _ = p * x := mul_comm _ _
    · rw [hB.mul_right, hx.2.2, hy.2.2, add_zero]
  obtain ⟨sx, ⟨hsx𝓔, hpsx, hxsx⟩, hsx_uniq⟩ := hSec.unique p hp x hx
  obtain ⟨sy, ⟨hsy𝓔, hpsy, hysy⟩, hsy_uniq⟩ := hSec.unique p hp y hy
  obtain ⟨su, ⟨hsu𝓔, hpsu, husu⟩, hsu_uniq⟩ := hSec.unique p hp (x * y) hu_nbr
  have hux : x * y ≠ x := by
    intro h
    apply hy1
    calc y = x * (x * y) := by rw [← mul_assoc, hB.sq_eq_one x, one_mul]
      _ = x * x := by rw [h]
      _ = 1 := hB.sq_eq_one x
  have hupx : x * y ≠ p * x := by
    intro h
    apply hy.2.1
    calc y = x * (x * y) := by rw [← mul_assoc, hB.sq_eq_one x, one_mul]
      _ = x * (p * x) := by rw [h]
      _ = p * (x * x) := by ac_rfl
      _ = p := by rw [hB.sq_eq_one x, mul_one]
  have huy : x * y ≠ y := by
    intro h
    apply hx1
    calc x = (x * y) * y := by rw [mul_assoc, hB.sq_eq_one y, mul_one]
      _ = y * y := by rw [h]
      _ = 1 := hB.sq_eq_one y
  have hupy : x * y ≠ p * y := by
    intro h
    apply hx.2.1
    calc x = (x * y) * y := by rw [mul_assoc, hB.sq_eq_one y, mul_one]
      _ = (p * y) * y := by rw [h]
      _ = p := by rw [mul_assoc, hB.sq_eq_one y, mul_one]
  have hsx_sy : sx ≠ sy := by
    intro h
    have hx' : x ∈ nbr B S p ∩ sigma B S sx := ⟨hx, hxsx⟩
    have hy' : y ∈ nbr B S p ∩ sigma B S sx := ⟨hy, by rw [h]; exact hysy⟩
    have := hSec.noplane sx hsx𝓔 p hpsx x hx' y hy' hyx hypx
    exact one_ne_zero (this.symm.trans hxy0)
  have hsx_su : sx ≠ su := by
    intro h
    have hx' : x ∈ nbr B S p ∩ sigma B S sx := ⟨hx, hxsx⟩
    have hu' : x * y ∈ nbr B S p ∩ sigma B S sx := ⟨hu_nbr, by rw [h]; exact husu⟩
    have := hSec.noplane sx hsx𝓔 p hpsx x hx' (x * y) hu' hux hupx
    have h0 : B x (x * y) = 0 := by rw [hB.mul_right, hB.alt, hxy0, zero_add]
    exact one_ne_zero (this.symm.trans h0)
  have hsy_su : sy ≠ su := by
    intro h
    have hy' : y ∈ nbr B S p ∩ sigma B S sy := ⟨hy, hysy⟩
    have hu' : x * y ∈ nbr B S p ∩ sigma B S sy := ⟨hu_nbr, by rw [h]; exact husu⟩
    have := hSec.noplane sy hsy𝓔 p hpsy y hy' (x * y) hu' huy hupy
    have h0 : B y (x * y) = 0 := by
      rw [hB.mul_right, hB.alt, add_zero, hB.symm y x, hxy0]
    exact one_ne_zero (this.symm.trans h0)
  have hEp : {f | f ∈ 𝓔 ∧ p ∈ sigma B S f} = {sx, sy, su} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hf𝓔, hpf⟩
      rcases (by decide : ∀ c d : ZMod 2, c = 0 ∨ d = 0 ∨ c + d = 0) (B f x) (B f y) with
        h | h | h
      · exact Or.inl (hsx_uniq f ⟨hf𝓔, hpf, hxS, h⟩)
      · exact Or.inr (Or.inl (hsy_uniq f ⟨hf𝓔, hpf, hyS, h⟩))
      · have h' : B f (x * y) = 0 := by rw [hB.mul_right]; exact h
        exact Or.inr (Or.inr (hsu_uniq f ⟨hf𝓔, hpf, huS, h'⟩))
    · rintro (rfl | rfl | rfl)
      · exact ⟨hsx𝓔, hpsx⟩
      · exact ⟨hsy𝓔, hpsy⟩
      · exact ⟨hsu𝓔, hpsu⟩
  have hnot : sx ∉ ({sy, su} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hsx_sy, hsx_su⟩
  have hE3 : {f | f ∈ 𝓔 ∧ p ∈ sigma B S f}.ncard = 3 := by
    rw [hEp, Set.ncard_insert_of_notMem hnot, Set.ncard_pair hsy_su]
  omega

theorem card_points_eq [Finite V] (hB : SympForm B) (hS : PointSet B S a) (hSec : Sections B S 𝓔)
    (hcard : Nat.card V = 64) (hmem : ∃ p ∈ S, ∃ e ∈ 𝓔, ∃ e' ∈ 𝓔, e ≠ e' ∧ p ∈ sigma B S e ∧
      p ∈ sigma B S e') : S.ncard = 35 := by
  have ha := card_nbr_eq hB hS hSec hcard hmem
  subst ha
  obtain ⟨p, hp, -⟩ := hmem
  have hE : ∀ q ∈ S, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard = 3 := fun q hq => by
    have := card_centres_of_mem hB hS hSec hq
    omega
  exact (p16b_count hB hS hSec hp hE).2

theorem closure_nbr_eq [Finite V] (hB : SympForm B) (hS : PointSet B S 9) (hSec : Sections B S 𝓔)
    (hcard : Nat.card V = 64) {z : V} (hz : z ∈ S) :
    (Subgroup.closure (insert z (nbr B S z)) : Set V) = {x : V | B z x = 0} := by
  classical
  have hz1 : z ≠ 1 := fun h => hS.one_notMem (h ▸ hz)
  let χ : V →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (B x z)
      map_one' := by
        show Multiplicative.ofAdd (B 1 z) = 1
        rw [Sp4.B_one_left hB z]
        rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (B (x * y) z) =
          Multiplicative.ofAdd (B x z) * Multiplicative.ofAdd (B y z)
        rw [hB.mul_left, ofAdd_add] }
  have hker : χ.ker = p16bPerp hB z := by
    ext x
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (B x z) = 1 ↔ B x z = 0
    exact ofAdd_eq_one
  obtain ⟨f, hf⟩ := p16b_exists_pair hB hz1
  have hf' : B f z = 1 := (hB.symm f z).trans hf
  have hrange : χ.range = ⊤ := by
    apply MonoidHom.range_eq_top_of_surjective
    intro y
    have hy : y = Multiplicative.ofAdd (Multiplicative.toAdd y) := rfl
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd y) with h | h
    · refine ⟨1, ?_⟩
      rw [hy, h]
      show Multiplicative.ofAdd (B 1 z) = Multiplicative.ofAdd 0
      rw [Sp4.B_one_left hB z]
    · refine ⟨f, ?_⟩
      rw [hy, h]
      show Multiplicative.ofAdd (B f z) = Multiplicative.ofAdd 1
      rw [hf']
  have hcardZ : Nat.card (p16bPerp hB z) = 32 := by
    rw [← hker]
    have h := Subgroup.card_ker_mul_card_range χ
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hrange, Subgroup.card_top, h2, hcard] at h
    omega
  have hsubZ : ∀ x, x ∈ p16bPerp hB z ↔ B z x = 0 := fun x => by
    show B x z = 0 ↔ B z x = 0
    rw [hB.symm]
  set E := Subgroup.closure (insert z (nbr B S z)) with hE
  have hleE : E ≤ p16bPerp hB z := by
    rw [hE, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact (hsubZ x).mpr (hB.alt x)
    · exact (hsubZ x).mpr hx.2.2
  have hcardE : 20 ≤ Nat.card E := by
    have hz_notin : z ∉ nbr B S z := fun h => h.2.1 rfl
    have h1_notin : (1 : V) ∉ insert z (nbr B S z) := by
      rintro (h | h)
      · exact hz1 h.symm
      · exact hS.one_notMem h.1
    have hsub : ((insert 1 (insert z (nbr B S z))) : Set V) ⊆ (E : Set V) := by
      intro x hx
      rcases hx with rfl | hx
      · exact E.one_mem
      · rcases hx with rfl | hx
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (insert 1 (insert z (nbr B S z)) : Set V).ncard = 20 := by
      rw [Set.ncard_insert_of_notMem h1_notin, Set.ncard_insert_of_notMem hz_notin,
        hS.card_nbr z hz]
    have h3 : Nat.card E = (E : Set V).ncard := Nat.card_coe_set_eq _
    omega
  have hdvd : Nat.card E ∣ Nat.card (p16bPerp hB z) := Subgroup.card_dvd_of_le hleE
  rw [hcardZ] at hdvd
  have hEeq : Nat.card E = 32 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k < 2 := by
      by_contra hc
      push Not at hc
      have : 20 * 2 ≤ Nat.card E * k := Nat.mul_le_mul hcardE hc
      omega
    interval_cases k <;> omega
  have hEZ : E = p16bPerp hB z := Subgroup.eq_of_le_of_card_ge hleE (by omega)
  rw [hEZ]
  ext x
  exact hsubZ x

theorem card_centres_eq [Finite V] (hB : SympForm B) (hS : PointSet B S a) (hSec : Sections B S 𝓔)
    (hcard : Nat.card V = 64) (hmem : ∃ p ∈ S, ∃ e ∈ 𝓔, ∃ e' ∈ 𝓔, e ≠ e' ∧ p ∈ sigma B S e ∧
      p ∈ sigma B S e') : 𝓔.ncard = 7 := by
  have ha := card_nbr_eq hB hS hSec hcard hmem
  subst ha
  obtain ⟨p, hp, -⟩ := hmem
  have hE : ∀ q ∈ S, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard = 3 := fun q hq => by
    have := card_centres_of_mem hB hS hSec hq
    omega
  exact (p16b_count hB hS hSec hp hE).1

theorem B_eq_one [Finite V] (hB : SympForm B) (hS : PointSet B S a) (hSec : Sections B S 𝓔)
    (hcard : Nat.card V = 64)
    (hmem : ∃ p ∈ S, ∃ e ∈ 𝓔, ∃ e' ∈ 𝓔, e ≠ e' ∧ p ∈ sigma B S e ∧ p ∈ sigma B S e')
    (hmodel : ∀ e ∈ 𝓔, ∀ e' : V, e' ≠ 1 → e' ≠ e →
      5 ≤ (sigma B S e ∩ {p | B e' p = 0}).ncard ∧
        ((sigma B S e ∩ {p | B e' p = 0}).ncard = 5 → B e e' = 1))
    {e e' : V} (he : e ∈ 𝓔) (he' : e' ∈ 𝓔) (hne : e ≠ e') : B e e' = 1 := by
  classical
  have ha := card_nbr_eq hB hS hSec hcard hmem
  subst ha
  have hE : ∀ q ∈ S, {f | f ∈ 𝓔 ∧ q ∈ sigma B S f}.ncard = 3 := fun q hq => by
    have := card_centres_of_mem hB hS hSec hq
    omega
  obtain ⟨p, hp, -⟩ := hmem
  have h7 : 𝓔.ncard = 7 := (p16b_count hB hS hSec hp hE).1
  have hcard6 : (𝓔 \ {e}).ncard + 1 = 𝓔.ncard := p16b_ncard_diff_singleton he 𝓔.toFinite
  have hdc := p16b_dc (𝓔 \ {e}) (sigma B S e) (fun e'' q => B e'' q = 0)
  beta_reduce at hdc
  have hR : ∀ q ∈ (sigma B S e).toFinite.toFinset,
      {e'' | e'' ∈ 𝓔 \ {e} ∧ B e'' q = 0}.ncard = 2 := by
    intro q hq
    have hq' : q ∈ sigma B S e := (Set.Finite.mem_toFinset _).mp hq
    have hset : {e'' | e'' ∈ 𝓔 \ {e} ∧ B e'' q = 0} =
        {e'' | e'' ∈ 𝓔 ∧ q ∈ sigma B S e''} \ {e} := by
      ext e''
      constructor
      · rintro ⟨⟨h𝓔, hne⟩, hB0⟩
        exact ⟨⟨h𝓔, hq'.1, hB0⟩, hne⟩
      · rintro ⟨⟨h𝓔, _, hB0⟩, hne⟩
        exact ⟨⟨h𝓔, hne⟩, hB0⟩
    have hmem' : e ∈ {e'' | e'' ∈ 𝓔 ∧ q ∈ sigma B S e''} := ⟨he, hq'⟩
    rw [hset]
    have hE3 := hE q hq'.1
    have := p16b_ncard_diff_singleton hmem' (Set.toFinite _)
    omega
  have hsum30 : ∑ e'' ∈ (𝓔 \ {e}).toFinite.toFinset,
      {q | q ∈ sigma B S e ∧ B e'' q = 0}.ncard = 30 := by
    rw [hdc, Finset.sum_congr rfl hR, Finset.sum_const, smul_eq_mul]
    have hc15 : (sigma B S e).toFinite.toFinset.card = 15 := by
      rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      exact hSec.card_sigma e he
    rw [hc15]
  have hlow : ∀ e'' ∈ (𝓔 \ {e}).toFinite.toFinset,
      5 ≤ {q | q ∈ sigma B S e ∧ B e'' q = 0}.ncard := by
    intro e'' he''
    have hm := (Set.Finite.mem_toFinset _).mp he''
    exact (hmodel e he e'' (hSec.ne_one e'' hm.1) hm.2).1
  have hcard6' : (𝓔 \ {e}).toFinite.toFinset.card = 6 := by
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    omega
  have hall : ∀ e'' ∈ (𝓔 \ {e}).toFinite.toFinset,
      {q | q ∈ sigma B S e ∧ B e'' q = 0}.ncard = 5 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e0, he0, hne0⟩ := hcon
    have hlt : ∑ _e'' ∈ (𝓔 \ {e}).toFinite.toFinset, 5 <
        ∑ e'' ∈ (𝓔 \ {e}).toFinite.toFinset, {q | q ∈ sigma B S e ∧ B e'' q = 0}.ncard :=
      Finset.sum_lt_sum (fun e'' he'' => hlow e'' he'')
        ⟨e0, he0, lt_of_le_of_ne (hlow e0 he0) (Ne.symm hne0)⟩
    rw [hsum30, Finset.sum_const, smul_eq_mul, hcard6'] at hlt
    omega
  have he'6 : e' ∈ 𝓔 \ {e} := ⟨he', fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
  have h5 := hall e' ((Set.Finite.mem_toFinset _).mpr he'6)
  exact (hmodel e he e' (hSec.ne_one e' he') (Ne.symm hne)).2 h5

theorem prod_eq_one [Finite V] (hB : SympForm B) (hS : PointSet B S a) (hspan : Subgroup.closure S
= ⊤)
    (hSec : Sections B S 𝓔) (hcard : Nat.card V = 64)
    (hmem : ∃ p ∈ S, ∃ e ∈ 𝓔, ∃ e' ∈ 𝓔, e ≠ e' ∧ p ∈ sigma B S e ∧ p ∈ sigma B S e')
    (h1 : ∀ e ∈ 𝓔, ∀ e' ∈ 𝓔, e ≠ e' → B e e' = 1) (l : List V) (hl : l.Nodup)
    (hl𝓔 : ∀ e, e ∈ l ↔ e ∈ 𝓔) : l.prod = 1 := by
  classical
  have ha := card_nbr_eq hB hS hSec hcard hmem
  subst ha
  obtain ⟨p, hp, -⟩ := hmem
  have hE : ∀ q ∈ S, {e | e ∈ 𝓔 ∧ q ∈ sigma B S e}.ncard = 3 := fun q hq => by
    have := card_centres_of_mem hB hS hSec hq
    omega
  have h7 : 𝓔.ncard = 7 := (p16b_count hB hS hSec hp hE).1
  have hlist : l.toFinset = 𝓔.toFinite.toFinset := by
    ext e
    simp only [List.mem_toFinset, Set.Finite.mem_toFinset, hl𝓔]
  have hprod : l.prod = ∏ e ∈ 𝓔.toFinite.toFinset, e := by
    rw [← hlist, List.prod_toFinset _ hl]
    simp
  refine p16b_eq_one_of_perp hB hspan (fun b hb => ?_)
  rw [hprod, p16b_B_prod_right hB, p16b_sum_zmod]
  have hcnt : (𝓔.toFinite.toFinset.filter (fun e => B b e = 0)).card = 3 := by
    rw [p16b_filter_card 𝓔 (fun e => B b e = 0)]
    have hset : {q | q ∈ 𝓔 ∧ B b q = 0} = {e | e ∈ 𝓔 ∧ b ∈ sigma B S e} := by
      ext q
      constructor
      · rintro ⟨h𝓔, h⟩
        exact ⟨h𝓔, hb, (hB.symm q b).trans h⟩
      · rintro ⟨h𝓔, _, h⟩
        exact ⟨h𝓔, (hB.symm b q).trans h⟩
    rw [hset]
    exact hE b hb
  have hsplit := Finset.card_filter_add_card_filter_not (s := 𝓔.toFinite.toFinset)
    (p := fun e => B b e ≠ 0)
  beta_reduce at hsplit
  have hnot : 𝓔.toFinite.toFinset.filter (fun e => ¬ (B b e ≠ 0)) =
      𝓔.toFinite.toFinset.filter (fun e => B b e = 0) :=
    Finset.filter_congr (fun e _ => not_not)
  rw [hnot, hcnt] at hsplit
  have hcE : 𝓔.toFinite.toFinset.card = 𝓔.ncard :=
    (Set.ncard_eq_toFinset_card 𝓔 (Set.toFinite 𝓔)).symm
  have hpos : (𝓔.toFinite.toFinset.filter (fun e => B b e ≠ 0)).card = 4 := by
    omega
  rw [hpos]
  decide

theorem eq_prod_of_mem [Finite V] (hB : SympForm B) (hS : PointSet B S a)
    (hspan : Subgroup.closure S = ⊤) (hSec : Sections B S 𝓔) (hcard : Nat.card V = 64)
    (hmem : ∃ p ∈ S, ∃ e ∈ 𝓔, ∃ e' ∈ 𝓔, e ≠ e' ∧ p ∈ sigma B S e ∧ p ∈ sigma B S e')
    (h1 : ∀ e ∈ 𝓔, ∀ e' ∈ 𝓔, e ≠ e' → B e e' = 1) {b : V} (hb : b ∈ S)
    (T : Finset V) (hT : ∀ e, e ∈ T ↔ e ∈ 𝓔 ∧ b ∈ sigma B S e) :
    b = ∏ e ∈ T, e := by
  classical
  have ha := card_nbr_eq hB hS hSec hcard hmem
  subst ha
  obtain ⟨z, hz, -⟩ := hmem
  have hE : ∀ q ∈ S, {f | f ∈ 𝓔 ∧ q ∈ sigma B S f}.ncard = 3 := fun q hq => by
    have := card_centres_of_mem hB hS hSec hq
    omega
  have h7 : 𝓔.ncard = 7 := (p16b_count hB hS hSec hz hE).1
  have hTcard : T.card = 3 := by
    have hTset : T = {e | e ∈ 𝓔 ∧ b ∈ sigma B S e}.toFinite.toFinset := by
      ext e
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact hT e
    rw [hTset, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    have := card_centres_of_mem hB hS hSec hb
    omega
  have hT𝓔 : ∀ e ∈ T, e ∈ 𝓔 := fun e he => ((hT e).mp he).1
  have hbS : ∀ e0 ∈ 𝓔, B e0 b = 0 ↔ e0 ∈ T := fun e0 he0 => by
    rw [hT]
    constructor
    · intro h
      exact ⟨he0, hb, h⟩
    · intro h
      exact h.2.2
  have hPP : (∏ e ∈ T, e) * (∏ e ∈ T, e) = 1 := by
    rw [← pow_two, ← Finset.prod_pow]
    exact Finset.prod_eq_one (fun e _ => by rw [pow_two]; exact hB.sq_eq_one e)
  have hQ : ∀ e0 ∈ 𝓔, B (b * ∏ e ∈ T, e) e0 = 0 := by
    intro e0 he0
    rw [hB.mul_left, hB.symm b e0, hB.symm (∏ e ∈ T, e) e0, p16b_B_prod_right hB]
    by_cases h0 : e0 ∈ T
    · have hb0 : B e0 b = 0 := (hbS e0 he0).mpr h0
      have hsum1 : ∑ e ∈ T.erase e0, B e0 e = ∑ e ∈ T.erase e0, (1 : ZMod 2) :=
        Finset.sum_congr rfl (fun e he => h1 e0 he0 e (hT𝓔 e (Finset.mem_of_mem_erase he))
          (Ne.symm (Finset.ne_of_mem_erase he)))
      rw [hb0, zero_add, ← Finset.add_sum_erase T _ h0, hB.alt, zero_add, hsum1, Finset.sum_const,
        Finset.card_erase_of_mem h0, hTcard]
      decide
    · have hb1 : B e0 b = 1 := by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (B e0 b) with h | h
        · exact absurd ((hbS e0 he0).mp h) h0
        · exact h
      have hsum1 : ∑ e ∈ T, B e0 e = ∑ e ∈ T, (1 : ZMod 2) :=
        Finset.sum_congr rfl (fun e he => h1 e0 he0 e (hT𝓔 e he)
          (fun h => h0 (by rw [h]; exact he)))
      rw [hb1, hsum1, Finset.sum_const, hTcard]
      decide
  have hQ1 : b * (∏ e ∈ T, e) = 1 := p16b_span_zero hB hcard (by omega) h1 hQ
  calc b = b * ((∏ e ∈ T, e) * (∏ e ∈ T, e)) := by rw [hPP, mul_one]
    _ = (b * ∏ e ∈ T, e) * ∏ e ∈ T, e := by ac_rfl
    _ = ∏ e ∈ T, e := by rw [hQ1, one_mul]

end Sections

end CFSG.ClassicalInvolution.Q3.Sec13.Polar
