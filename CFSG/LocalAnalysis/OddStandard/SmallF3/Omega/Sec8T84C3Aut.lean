module

public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

private lemma zeta_cube {S : Type} [Group S] (ζ : MulAut S) (hζ3 : ζ ^ 3 = 1) (s : S) :
    ζ (ζ (ζ s)) = s := by
  have h := congrArg (fun f : MulAut S => f s) hζ3
  simpa [pow_succ, MulAut.mul_apply] using h

private lemma zeta_prod {S : Type} [CommGroup S] (ζ : MulAut S) (hζ3 : ζ ^ 3 = 1)
    (hfix : ∀ s : S, ζ s = s → s = 1) (s : S) : s * ζ s * ζ (ζ s) = 1 := by
  apply hfix
  rw [map_mul, map_mul, zeta_cube ζ hζ3 s]
  ac_rfl

private lemma mem_sup_zpowers_iff {S : Type} [CommGroup S] (h2 : ∀ s : S, s * s = 1)
    (T : Subgroup S) (x a : S) : a ∈ T ⊔ Subgroup.zpowers x ↔ a ∈ T ∨ a * x ∈ T := by
  constructor
  · intro ha
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, h2 x, one_zpow, mul_one]
      exact hy
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, h2 x, one_zpow, one_mul, mul_assoc, h2 x, mul_one]
      exact hy
  · rintro (ha | ha)
    · exact Subgroup.mem_sup_left ha
    · have h1 : a * x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_left ha
      have h3 : x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      have := mul_mem h1 h3
      rwa [mul_assoc, h2 x, mul_one] at this

private lemma two_mul_card_le {S : Type} [Group S] [Finite S] {U V : Subgroup S} (hUV : U ≤ V)
    (hne : U ≠ V) : 2 * Nat.card U ≤ Nat.card V := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hUV
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hposV : 0 < Nat.card V := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hUV (le_of_eq (by rw [hk, mul_one])))
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk, mul_comm]
  exact Nat.mul_le_mul_left _ hk2

private lemma zeta_step {S : Type} [CommGroup S] [Finite S] (h2 : ∀ s : S, s * s = 1)
    (ζ : MulAut S) (hζ3 : ζ ^ 3 = 1) (hfix : ∀ s : S, ζ s = s → s = 1)
    (T : Subgroup S) (hT : ∀ t ∈ T, ζ t ∈ T) (x : S) (hx : x ∉ T) :
    ∃ T' : Subgroup S, T ≤ T' ∧ x ∈ T' ∧ ζ x ∈ T' ∧ (∀ t ∈ T', ζ t ∈ T') ∧
      (∀ U : Subgroup S, T ≤ U → x ∈ U → ζ x ∈ U → T' ≤ U) ∧ 4 * Nat.card T ≤ Nat.card T' := by
  have hp := zeta_prod ζ hζ3 hfix x
  have hzz : ζ (ζ x) = (x * ζ x)⁻¹ := eq_inv_of_mul_eq_one_right hp
  have hx2 : ζ x ∉ T := fun h => hx (by simpa [zeta_cube ζ hζ3] using hT _ (hT _ h))
  have hx3 : ζ x * x ∉ T := by
    intro h
    apply hx
    have h' : ζ (ζ x * x) ∈ T := hT _ h
    rw [map_mul] at h'
    have h1 : x * (ζ (ζ x) * ζ x) = 1 := by rw [← hp]; ac_rfl
    have h4 : ζ (ζ x) * ζ x = x := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_eq_of_mul_eq_one_right (h2 x)
    rwa [h4] at h'
  have hT1 : T ≠ T ⊔ Subgroup.zpowers x := fun h =>
    hx (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hx2' : ζ x ∉ T ⊔ Subgroup.zpowers x := by
    rw [mem_sup_zpowers_iff h2]
    exact fun h => h.elim hx2 hx3
  have hT2 : T ⊔ Subgroup.zpowers x ≠ T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x) :=
    fun h => hx2' (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (ζ x)))
  have hxm : x ∈ T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hzxm : ζ x ∈ T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers (ζ x))
  have hmap : (T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x)).map ζ.toMonoidHom ≤
      T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x) := by
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hT t ht))
    · exact Subgroup.zpowers_le.mpr hzxm
    · refine Subgroup.zpowers_le.mpr ?_
      show ζ (ζ x) ∈ _
      rw [hzz]
      exact inv_mem (mul_mem hxm hzxm)
  refine ⟨T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x), le_sup_left.trans le_sup_left, hxm,
    hzxm, fun t ht => hmap ⟨t, ht, rfl⟩, fun U hTU hxU hzxU => ?_, ?_⟩
  · exact sup_le (sup_le hTU (Subgroup.zpowers_le.mpr hxU)) (Subgroup.zpowers_le.mpr hzxU)
  · have h1 := two_mul_card_le (le_sup_left : T ≤ T ⊔ Subgroup.zpowers x) hT1
    have h2' := two_mul_card_le (le_sup_left : T ⊔ Subgroup.zpowers x ≤
      T ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (ζ x)) hT2
    omega

private lemma exists_gen {S : Type} [CommGroup S] [Finite S] (h2 : ∀ s : S, s * s = 1)
    (ζ : MulAut S) (hζ3 : ζ ^ 3 = 1) (hfix : ∀ s : S, ζ s = s → s = 1)
    (hS : Nat.card S ≤ 16) :
    ∃ a b : S, ∀ U : Subgroup S, (∀ u ∈ U, ζ u ∈ U) → a ∈ U → b ∈ U → U = ⊤ := by
  have hbot : ∀ t ∈ (⊥ : Subgroup S), ζ t ∈ (⊥ : Subgroup S) := by
    intro t ht
    rw [Subgroup.mem_bot] at ht ⊢
    rw [ht, map_one]
  by_cases h0 : ∃ x : S, x ∉ (⊥ : Subgroup S)
  · obtain ⟨x₁, hx₁⟩ := h0
    obtain ⟨T₁, -, hx₁T, hzx₁T, hT₁inv, hT₁min, hT₁card⟩ :=
      zeta_step h2 ζ hζ3 hfix ⊥ hbot x₁ hx₁
    by_cases h1 : ∃ x : S, x ∉ T₁
    · obtain ⟨x₂, hx₂⟩ := h1
      obtain ⟨T₂, -, hx₂T, hzx₂T, -, hT₂min, hT₂card⟩ :=
        zeta_step h2 ζ hζ3 hfix T₁ hT₁inv x₂ hx₂
      have hT₂top : T₂ = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        have h3 : Nat.card T₂ ≤ Nat.card S := Subgroup.card_le_card_group T₂
        rw [Subgroup.card_bot] at hT₁card
        omega
      refine ⟨x₁, x₂, fun U hUinv ha hb => ?_⟩
      have hT₁U : T₁ ≤ U := hT₁min U bot_le ha (hUinv _ ha)
      have hT₂U : T₂ ≤ U := hT₂min U hT₁U hb (hUinv _ hb)
      rw [hT₂top] at hT₂U
      exact top_le_iff.mp hT₂U
    · push Not at h1
      refine ⟨x₁, 1, fun U hUinv ha _ => ?_⟩
      have hT₁U : T₁ ≤ U := hT₁min U bot_le ha (hUinv _ ha)
      exact top_le_iff.mp (fun s _ => hT₁U (h1 s))
  · push Not at h0
    refine ⟨1, 1, fun U _ _ _ => ?_⟩
    refine top_le_iff.mp (fun s _ => ?_)
    have := h0 s
    rw [Subgroup.mem_bot] at this
    rw [this]
    exact U.one_mem

theorem card_centralizer_zeta_le {S : Type} [CommGroup S] [Finite S] (h2 : ∀ s : S, s * s = 1)
    (ζ : MulAut S) (hζ3 : ζ ^ 3 = 1) (hfix : ∀ s : S, ζ s = s → s = 1)
    (hS : Nat.card S ≤ 16) :
    Nat.card (Subgroup.centralizer ({ζ} : Set (MulAut S))) ≤ 256 := by
  obtain ⟨a, b, hgen⟩ := exists_gen h2 ζ hζ3 hfix hS
  let ev : ↥(Subgroup.centralizer ({ζ} : Set (MulAut S))) → S × S := fun c =>
    ((c : MulAut S) a, (c : MulAut S) b)
  have hev : Function.Injective ev := by
    intro c d hcd
    have hca : (c : MulAut S) a = (d : MulAut S) a := congrArg Prod.fst hcd
    have hcb : (c : MulAut S) b = (d : MulAut S) b := congrArg Prod.snd hcd
    have hcomm : ∀ (e : ↥(Subgroup.centralizer ({ζ} : Set (MulAut S)))) (s : S),
        (e : MulAut S) (ζ s) = ζ ((e : MulAut S) s) := by
      intro e s
      have h := Subgroup.mem_centralizer_iff.mp e.2 ζ rfl
      have := congrArg (fun f : MulAut S => f s) h
      simpa [MulAut.mul_apply] using this.symm
    let U : Subgroup S :=
      { carrier := {s | (c : MulAut S) s = (d : MulAut S) s}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, map_mul] at hx hy ⊢
          rw [hx, hy]
        one_mem' := by simp
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq, map_inv] at hx ⊢
          rw [hx] }
    have hinv : ∀ u ∈ U, ζ u ∈ U := by
      intro u hu
      change (c : MulAut S) (ζ u) = (d : MulAut S) (ζ u)
      rw [hcomm c, hcomm d]
      exact congrArg ζ hu
    have hUtop : U = ⊤ := hgen U hinv hca hcb
    apply Subtype.ext
    apply MulEquiv.ext
    intro s
    have hs : s ∈ U := hUtop ▸ Subgroup.mem_top s
    exact hs
  calc Nat.card (Subgroup.centralizer ({ζ} : Set (MulAut S)))
      ≤ Nat.card (S × S) := Nat.card_le_card_of_injective ev hev
    _ = Nat.card S * Nat.card S := Nat.card_prod S S
    _ ≤ 16 * 16 := Nat.mul_le_mul hS hS
    _ = 256 := by norm_num

theorem exists_sectionAct {V : Type} [CommGroup V] (Rr Tt : Subgroup V) (_hRT : Rr ≤ Tt)
    (K : Subgroup (MulAut V)) (hT : ∀ k ∈ K, ∀ t ∈ Tt, k t ∈ Tt)
    (hR : ∀ k ∈ K, ∀ r ∈ Rr, k r ∈ Rr) :
    ∃ ρ : ↥K →* MulAut (↥Tt ⧸ Rr.subgroupOf Tt), ∀ (k : ↥K) (t : ↥Tt),
      ρ k (QuotientGroup.mk t) = QuotientGroup.mk ⟨(k : MulAut V) t, hT k k.2 t t.2⟩ := by
  classical
  let N : Subgroup ↥Tt := Rr.subgroupOf Tt
  let restT : ↥K → (↥Tt →* ↥Tt) := fun k =>
    ((k : MulAut V).toMonoidHom.comp Tt.subtype).codRestrict Tt (fun t => hT k k.2 t t.2)
  have hrestT_mul : ∀ k1 k2 : ↥K, restT (k1 * k2) = (restT k1).comp (restT k2) := by
    intro k1 k2
    ext t
    rfl
  have hrestT_one : restT 1 = MonoidHom.id _ := by
    ext t
    rfl
  have hle : ∀ k : ↥K, N ≤ N.comap (restT k) := by
    intro k t ht
    exact hR k k.2 t ht
  let m : ∀ k : ↥K, (↥Tt ⧸ N) →* (↥Tt ⧸ N) := fun k => QuotientGroup.map N N (restT k) (hle k)
  have hm_mk : ∀ k t, m k (QuotientGroup.mk t) = QuotientGroup.mk (restT k t) := fun k t => rfl
  have hm_mul : ∀ k1 k2, m (k1 * k2) = (m k1).comp (m k2) := by
    intro k1 k2
    apply QuotientGroup.monoidHom_ext
    ext t
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hm_mk, hrestT_mul]
  have hm_one : m 1 = MonoidHom.id _ := by
    apply QuotientGroup.monoidHom_ext
    ext t
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hm_mk, hrestT_one]
    rfl
  let act : ↥K → MulAut (↥Tt ⧸ N) := fun k =>
    MonoidHom.toMulEquiv (m k) (m k⁻¹)
      (by rw [← hm_mul, inv_mul_cancel, hm_one])
      (by rw [← hm_mul, mul_inv_cancel, hm_one])
  refine ⟨MonoidHom.mk' act (fun k1 k2 => ?_), fun k t => rfl⟩
  apply MulEquiv.ext
  intro x
  show m (k1 * k2) x = m k1 (m k2 x)
  rw [hm_mul]
  rfl

theorem card_section {V : Type} [CommGroup V] [Finite V] (Rr Tt : Subgroup V) (hRT : Rr ≤ Tt) :
    Nat.card (↥Tt ⧸ Rr.subgroupOf Tt) * Nat.card Rr = Nat.card Tt := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Rr.subgroupOf Tt)
  have h2 : Nat.card ↥(Rr.subgroupOf Tt) = Nat.card ↥Rr :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv
  rw [h2] at h
  exact h.symm

theorem pow_four_eq_one {V : Type} [CommGroup V] (hsq : ∀ v : V, v * v = 1)
    (R T : Subgroup V) (m : MulAut V) (h1 : ∀ r ∈ R, m r = r) (h2 : ∀ t ∈ T, m t * t⁻¹ ∈ R)
    (h3 : ∀ v : V, m v * v⁻¹ ∈ T) : m ^ 4 = 1 := by
  ext v
  set a : V := m v * v⁻¹ with ha
  have haT : a ∈ T := h3 v
  set b : V := m a * a⁻¹ with hb
  have hbR : b ∈ R := h2 a haT
  have hmb : m b = b := h1 b hbR
  have hmv : m v = a * v := by rw [ha]; group
  have hma : m a = b * a := by rw [hb]; group
  have hm4 : (m ^ 4) v = m (m (m (m v))) := by
    simp [pow_succ, MulAut.mul_apply]
  have e2 : m (m v) = b * v := by
    rw [hmv, map_mul, hma, hmv]
    calc b * a * (a * v) = b * (a * a) * v := by ac_rfl
      _ = b * v := by rw [hsq a, mul_one]
  have e3 : m (m (m v)) = a * b * v := by
    rw [e2, map_mul, hmb, hmv]
    ac_rfl
  rw [hm4, e3, map_mul, map_mul, hma, hmb, hmv]
  calc b * a * b * (a * v) = (a * a) * (b * b) * v := by ac_rfl
    _ = v := by rw [hsq a, hsq b, one_mul, one_mul]

end C10

end CFSG.OddStandard.SmallF3.Omega
