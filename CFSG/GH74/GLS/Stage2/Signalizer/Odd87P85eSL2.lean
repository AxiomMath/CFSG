module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eDih
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

theorem exists_proj {Y : Type} [Group Y] (A B : Subgroup Y)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (N : Subgroup ↥A) [N.Normal]
    (hN : ∀ a : ↥A, (a : Y) ∈ B → a ∈ N) (hNB : ∀ a : ↥A, a ∈ N → (a : Y) ∈ B) :
    ∃ φ : ↥(A ⊔ B) →* ↥A ⧸ N, Function.Surjective φ ∧
      (∀ x : ↥(A ⊔ B), φ x = 1 ↔ (x : Y) ∈ B) := by
  classical
  let ν : ↥A × ↥B →* ↥(A ⊔ B) :=
    MonoidHom.noncommCoprod (Subgroup.inclusion le_sup_left) (Subgroup.inclusion le_sup_right)
      (fun a b => Subtype.ext (hcomm a a.2 b b.2))
  have hν : ∀ a : ↥A, ∀ b : ↥B, ((ν (a, b) : ↥(A ⊔ B)) : Y) = (a : Y) * b := by
    intro a b
    rfl
  have hsurj : Function.Surjective ν := by
    intro x
    obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup' hcomm x.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by rw [hν]; exact hx.symm)⟩
  let κ : ↥A × ↥B →* ↥A ⧸ N := (QuotientGroup.mk' N).comp (MonoidHom.fst _ _)
  have hker : ν.ker ≤ κ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have h1 : (p.1 : Y) * p.2 = 1 := by rw [← hν]; exact congrArg Subtype.val hp |>.trans rfl
    have h2 : (p.1 : Y) ∈ B := by
      have : (p.1 : Y) = ((p.2)⁻¹ : ↥B) := by
        rw [Subgroup.coe_inv]; exact eq_inv_of_mul_eq_one_left h1
      rw [this]; exact (p.2⁻¹).2
    simpa [κ, QuotientGroup.eq_one_iff] using hN p.1 h2
  let φ : ↥(A ⊔ B) →* ↥A ⧸ N :=
    MonoidHom.liftOfRightInverse ν (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨κ, hker⟩
  have hφ : ∀ p : ↥A × ↥B, φ (ν p) = κ p := fun p =>
    MonoidHom.liftOfRightInverse_comp_apply ν (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨κ, hker⟩ p
  refine ⟨φ, ?_, fun x => ?_⟩
  · intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N q
    exact ⟨ν (a, 1), by rw [hφ]; rfl⟩
  · obtain ⟨p, rfl⟩ := hsurj x
    rw [hφ, hν]
    constructor
    · intro h
      have h' : p.1 ∈ N := by simpa [κ, QuotientGroup.eq_one_iff] using h
      exact B.mul_mem (hNB p.1 h') p.2.2
    · intro h
      have h2 : (p.1 : Y) ∈ B := by
        have := B.mul_mem h (B.inv_mem p.2.2)
        simpa using this
      simpa [κ, QuotientGroup.eq_one_iff] using hN p.1 h2

theorem quot_center_equiv_psl {A : Type} [Group A] {r : ℕ} (hA : HasSL2Model A (fun q => q = r)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ∧
      Nonempty (A ⧸ Subgroup.center A ≃* CFSG.GorensteinWalter.PSL2 F) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hA
  refine ⟨F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  let e' : SL(2, F) ≃* A := (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  exact (QuotientGroup.congr (Subgroup.center SL(2, F)) (Subgroup.center A) e'
    (Subgroup.map_center_eq e')).symm

theorem proj_generic {Y : Type} [Group Y] (A B : Subgroup Y)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hcard : Nat.card ↥(A ⊓ B) = 2)
    {r : ℕ} (hr : Odd r) (hA : HasSL2Model ↥A (fun q => q = r)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : ↥(A ⊔ B) →* CFSG.GorensteinWalter.PSL2 F),
      Odd (Nat.card F) ∧ Function.Surjective φ ∧ ∀ x : ↥(A ⊔ B), φ x = 1 ↔ (x : Y) ∈ B := by
  classical
  obtain ⟨t, htA, -, hinv, hcen⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr hA
  obtain ⟨x, hxAB, hx1⟩ : ∃ x ∈ A ⊓ B, x ≠ 1 := by
    by_contra h
    push Not at h
    have : A ⊓ B = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hxt : x = t := by
    rcases hcen x hxAB.1 (fun w hw => (hcomm w hw x hxAB.2).symm) with h | h
    · exact absurd h hx1
    · exact h
  have htB : t ∈ B := hxt ▸ hxAB.2
  have hN : ∀ a : ↥A, (a : Y) ∈ B → a ∈ Subgroup.center ↥A := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 a ha)
  have hNB : ∀ a : ↥A, a ∈ Subgroup.center ↥A → (a : Y) ∈ B := by
    intro a ha
    have hac : ∀ w ∈ A, (a : Y) * w = w * (a : Y) := by
      intro w hw
      have := Subgroup.mem_center_iff.mp ha ⟨w, hw⟩
      exact (congrArg Subtype.val this).symm
    rcases hcen (a : Y) a.2 (fun w hw => hac w hw) with h | h
    · rw [h]; exact B.one_mem
    · rw [h]; exact htB
  obtain ⟨φ', hφ's, hφ'⟩ := exists_proj A B hcomm (Subgroup.center ↥A) hN hNB
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := quot_center_equiv_psl hA
  refine ⟨F, inferInstance, inferInstance, e.toMonoidHom.comp φ', hF ▸ hr, e.surjective.comp hφ's, fun y => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact hφ' y

theorem isOddPrimePower_of_odd {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  have := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' F
  have hq : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  refine ⟨p, n, hp, ?_, n.pos, hq⟩
  by_contra hpo
  have h2 : p = 2 := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · exact h2
    · exact absurd h2 hpo
  have hq2 : Even (Nat.card F) := by
    rw [hq, h2]
    exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.mpr h) hq2

theorem hasDihedralSylowTwo_psl2 {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (CFSG.GorensteinWalter.PSL2 F) :=
  CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower_of_odd h)

structure SL2Pair (Y : Type) [Group Y] (L₁ L₂ : Subgroup Y) : Prop where
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  card_inf : Nat.card ↥(L₁ ⊓ L₂) = 2
  sl₁ : ∃ r : ℕ, Odd r ∧ HasSL2Model ↥L₁ (fun q => q = r)
  sl₂ : ∃ r : ℕ, Odd r ∧ HasSL2Model ↥L₂ (fun q => q = r)

theorem SL2Pair.symm {Y : Type} [Group Y] {L₁ L₂ : Subgroup Y} (h : SL2Pair Y L₁ L₂) :
    SL2Pair Y L₂ L₁ :=
  ⟨fun a ha b hb => (h.comm b hb a ha).symm, by rw [inf_comm]; exact h.card_inf, h.sl₂, h.sl₁⟩

theorem SL2Pair.exists_t {Y : Type} [Group Y] {L₁ L₂ : Subgroup Y} (h : SL2Pair Y L₁ L₂) :
    ∃ t : Y, t ∈ L₁ ∧ t ∈ L₂ ∧ orderOf t = 2 ∧ (∀ v ∈ L₁, v * v = 1 → v = 1 ∨ v = t) ∧
      (∀ v ∈ L₂, v * v = 1 → v = 1 ∨ v = t) ∧ (∀ v ∈ L₁ ⊓ L₂, v = 1 ∨ v = t) := by
  obtain ⟨r₁, hr₁, h₁⟩ := h.sl₁
  obtain ⟨r₂, hr₂, h₂⟩ := h.sl₂
  obtain ⟨t₁, ht₁, ht₁o, hu₁, hc₁⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₁ h₁
  obtain ⟨t₂, ht₂, ht₂o, hu₂, hc₂⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₂ h₂
  obtain ⟨x, hxAB, hx1⟩ : ∃ x ∈ L₁ ⊓ L₂, x ≠ 1 := by
    by_contra hh
    push Not at hh
    have : L₁ ⊓ L₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hh
    have hc := h.card_inf
    rw [this, Subgroup.card_bot] at hc
    omega
  have hx₁ : x = t₁ := by
    rcases hc₁ x hxAB.1 (fun w hw => (h.comm w hw x hxAB.2).symm) with e | e
    · exact absurd e hx1
    · exact e
  have hx₂ : x = t₂ := by
    rcases hc₂ x hxAB.2 (fun w hw => h.comm x hxAB.1 w hw) with e | e
    · exact absurd e hx1
    · exact e
  refine ⟨x, hxAB.1, hxAB.2, ?_, ?_, ?_, ?_⟩
  · rw [hx₁]; exact ht₁o
  · intro v hv hv2; rw [hx₁]; exact hu₁ v hv hv2
  · intro v hv hv2; rw [hx₂]; exact hu₂ v hv hv2
  · intro v hv
    rw [hx₁]
    exact hc₁ v hv.1 (fun w hw => (h.comm w hw v hv.2).symm)

theorem coe_normalizerMonoidHom {G : Type} [Group G] (H : Subgroup G) (g : ↥(normalizer (H : Set G)))
    (h : ↥H) : ((H.normalizerMonoidHom g h : ↥H) : G) = (g : G) * (h : G) * (g : G)⁻¹ := rfl

theorem pair_cyc_index {Y : Type} [Group Y] [Finite Y] {L₁ L₂ : Subgroup Y} (h : SL2Pair Y L₁ L₂)
    {t : Y} (htL : t ∈ L₁ ⊓ L₂) (ht2 : orderOf t = 2) {B : Subgroup Y} (hB : B ≤ L₁ ⊔ L₂)
    (hB2 : IsPGroup 2 B) (htB : t ∉ B) : ∃ x ∈ B, Nat.card B ≤ 2 * orderOf x := by
  classical
  obtain ⟨t', ht'₁, ht'₂, -, -, hu₂, hc⟩ := h.exists_t
  have htt : t = t' := by
    rcases hc t htL with h1 | h1
    · exact absurd ht2 (by rw [h1, orderOf_one]; decide)
    · exact h1
  subst htt
  obtain ⟨r₁, hr₁, h₁⟩ := h.sl₁
  obtain ⟨F, _, _, φ, hodd, -, hker⟩ := proj_generic L₁ L₂ h.comm h.card_inf hr₁ h₁
  have hM := hasDihedralSylowTwo_psl2 hodd
  have hBL₂ : ∀ y ∈ B, y ∈ L₂ → y = 1 := by
    intro y hyB hyL
    by_contra hy1
    have hC2 : IsPGroup 2 ↥(B ⊓ L₂) := hB2.to_le inf_le_left
    obtain ⟨n, hn⟩ := hC2.exists_card_eq
    have hn1 : 1 ≤ n := by
      by_contra hn0
      have hn0' : n = 0 := by omega
      rw [hn0', pow_zero] at hn
      have hb : B ⊓ L₂ = ⊥ := Subgroup.card_eq_one.mp hn
      have hy : y ∈ B ⊓ L₂ := ⟨hyB, hyL⟩
      rw [hb, Subgroup.mem_bot] at hy
      exact hy1 hy
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ L₂)) 2
      (by rw [hn]; exact dvd_pow_self 2 (by omega))
    have hv2 : (v : Y) * v = 1 := by
      have := pow_orderOf_eq_one v
      rw [hv, pow_two] at this
      exact congrArg Subtype.val this
    have hv1 : (v : Y) ≠ 1 := by
      intro h1
      have : v = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hv
      omega
    rcases hu₂ (v : Y) v.2.2 hv2 with h1 | h1
    · exact hv1 h1
    · exact htB (h1 ▸ v.2.1)
  let B' : Subgroup ↥(L₁ ⊔ L₂) := B.subgroupOf (L₁ ⊔ L₂)
  let ψ : ↥B' →* CFSG.GorensteinWalter.PSL2 F := φ.comp B'.subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : ↥(L₁ ⊔ L₂)) ∈ φ.ker := hx
    have h2 : ((x : ↥(L₁ ⊔ L₂)) : Y) ∈ L₂ := (hker _).mp h1
    have h3 : ((x : ↥(L₁ ⊔ L₂)) : Y) ∈ B := x.2
    have h4 := hBL₂ _ h3 h2
    exact Subtype.ext (Subtype.ext h4)
  have hB'2 : IsPGroup 2 ↥B' := IsPGroup.of_equiv hB2 (Subgroup.subgroupOfEquivOfLe hB).symm
  let D : Subgroup (CFSG.GorensteinWalter.PSL2 F) := B'.map φ
  have hD2 : IsPGroup 2 ↥D := by
    have := hB'2.map φ
    exact this
  obtain ⟨x₀, hx₀D, hx₀⟩ := dih_cyc_index hM D hD2
  obtain ⟨b', hb'B', hb'⟩ := Subgroup.mem_map.mp hx₀D
  have hrange : ψ.range = D := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardD : Nat.card D = Nat.card B' := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hcardB : Nat.card B = Nat.card B' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).symm.toEquiv
  refine ⟨((b' : ↥(L₁ ⊔ L₂)) : Y), hb'B', ?_⟩
  have hord : orderOf ((b' : ↥(L₁ ⊔ L₂)) : Y) = orderOf x₀ := by
    rw [← hb', Subgroup.orderOf_coe]
    have e1 : orderOf (ψ ⟨b', hb'B'⟩) = orderOf (⟨b', hb'B'⟩ : ↥B') := orderOf_injective ψ hψinj _
    have e2 : orderOf ((⟨b', hb'B'⟩ : ↥B') : ↥(L₁ ⊔ L₂)) = orderOf (⟨b', hb'B'⟩ : ↥B') :=
      Subgroup.orderOf_coe _
    exact e2.trans e1.symm
  rw [hord, hcardB, ← hcardD]
  exact hx₀

theorem proj_comm_mem {Y : Type} [Group Y] [Finite Y] {Lb K B : Subgroup Y} [Lb.Normal] {F : Type}
    [Field F] [Finite F] (hodd : Odd (Nat.card F)) (φ : ↥Lb →* CFSG.GorensteinWalter.PSL2 F)
    (hφs : Function.Surjective φ) (hker : ∀ x : ↥Lb, φ x = 1 ↔ (x : Y) ∈ K) (hB : B ≤ Lb)
    (hB2 : IsPGroup 2 B) {w : Y} (hwK : w ∈ normalizer (K : Set Y)) (hwB : w ∈ normalizer (B : Set Y))
    {a : ℕ} (hwa : w ^ (5 ^ a) = 1) : ∀ b ∈ B, ⁅b, w⁆ ∈ K := by
  classical
  let c : MulAut ↥Lb := MulAut.conjNormal w
  have hcv : ∀ x : ↥Lb, ((c x : ↥Lb) : Y) = w * x * w⁻¹ := fun x => MulAut.conjNormal_apply w x
  have hc : ∀ x : ↥Lb, φ x = 1 → φ (c x) = 1 := by
    intro x hx
    rw [hker] at hx ⊢
    rw [hcv]
    exact (Subgroup.mem_normalizer_iff.mp hwK x).mp hx
  have hca : c ^ (5 ^ a) = 1 := by
    have : c ^ (5 ^ a) = MulAut.conjNormal (w ^ (5 ^ a)) := (map_pow MulAut.conjNormal w _).symm
    rw [this, hwa, map_one]
  obtain ⟨α, hαc, hα5⟩ := exists_equivariant_aut_pow φ hφs c hc a hca
  let D : Subgroup (CFSG.GorensteinWalter.PSL2 F) := (B.subgroupOf Lb).map φ
  have hD2 : IsPGroup 2 ↥D := by
    have h1 : IsPGroup 2 ↥(B.subgroupOf Lb) := IsPGroup.of_equiv hB2 (Subgroup.subgroupOfEquivOfLe hB).symm
    exact h1.map φ
  have hαD : ∀ d ∈ D, α d ∈ D := by
    rintro _ ⟨b', hb', rfl⟩
    rw [← hαc]
    have hb'' : (b' : Y) ∈ B := Subgroup.mem_subgroupOf.mp hb'
    refine ⟨c b', ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hcv]
    exact (Subgroup.mem_normalizer_iff.mp hwB (b' : Y)).mp hb''
  have hfix := aut_trivial_on (hasDihedralSylowTwo_psl2 hodd) D hD2 α hαD a hα5
  intro b hb
  have hbL : b ∈ Lb := hB hb
  let b' : ↥Lb := ⟨b, hbL⟩
  have hb'D : φ b' ∈ D := ⟨b', Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have h1 : φ (c b') = φ b' := by rw [hαc]; exact hfix _ hb'D
  have h2 : φ (c b' * b'⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 : ((c b' * b'⁻¹ : ↥Lb) : Y) ∈ K := (hker _).mp h2
  have h4 : ((c b' * b'⁻¹ : ↥Lb) : Y) = ⁅w, b⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcv]
    simp [commutatorElement_def, b', mul_assoc]
  rw [h4] at h3
  have : ⁅b, w⁆ = ⁅w, b⁆⁻¹ := (commutatorElement_inv w b).symm
  rw [this]
  exact K.inv_mem h3

theorem pair_kl {Y : Type} [Group Y] [Finite Y] {L₁ L₂ : Subgroup Y} (h : SL2Pair Y L₁ L₂)
    (hLn : (L₁ ⊔ L₂).Normal) {P : Subgroup Y} (hP2 : IsPGroup 2 P)
    (hidx : (P ⊓ (L₁ ⊔ L₂)).relIndex P ≤ 4) {W : Subgroup Y} (hW5 : IsPGroup 5 W)
    (hWP : W ≤ normalizer (P : Set Y)) (hW₁ : W ≤ normalizer (L₁ : Set Y))
    (hW₂ : W ≤ normalizer (L₂ : Set Y)) : ⁅P, W⁆ = ⊥ := by
  classical
  have := hLn
  set Lb : Subgroup Y := L₁ ⊔ L₂ with hLb
  set B : Subgroup Y := P ⊓ Lb with hB
  have hB2 : IsPGroup 2 ↥B := hP2.to_le inf_le_left
  have hP5 : ¬ 5 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    intro hd
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hd)
    omega
  have hWLb : ∀ w ∈ W, w ∈ normalizer (Lb : Set Y) := fun w _ =>
    Subgroup.mem_normalizer_iff.mpr (fun x => ⟨fun hx => hLn.conj_mem x hx w, fun hx => by
      have := hLn.conj_mem _ hx w⁻¹
      simpa [mul_assoc] using this⟩)
  have hWB : ∀ w ∈ W, w ∈ normalizer (B : Set Y) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hWP hw) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hWLb w hw) x
    constructor
    · rintro ⟨hxP, hxL⟩; exact ⟨h1.mp hxP, h2.mp hxL⟩
    · rintro ⟨hxP, hxL⟩; exact ⟨h1.mpr hxP, h2.mpr hxL⟩
  have hPB : ∀ x ∈ P, ∀ w ∈ W, ⁅x, w⁆ ∈ B := by
    intro x hx w hw
    let N : Subgroup ↥P := B.subgroupOf P
    have hNn : N.Normal := ⟨fun n hn g => by
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · exact P.mul_mem (P.mul_mem g.2 n.2) (P.inv_mem g.2)
      · have := Subgroup.mem_subgroupOf.mp hn
        have h3 := hLn.conj_mem (n : Y) this.2 (g : Y)
        simpa using h3⟩
    obtain ⟨a, ha⟩ := hW5 ⟨w, hw⟩
    let g : ↥(normalizer (P : Set Y)) := ⟨w, hWP hw⟩
    let c : MulAut ↥P := P.normalizerMonoidHom g
    have hcv : ∀ y : ↥P, ((c y : ↥P) : Y) = w * y * w⁻¹ := fun y => coe_normalizerMonoidHom P g y
    have hc : ∀ y : ↥P, (QuotientGroup.mk' N) y = 1 → (QuotientGroup.mk' N) (c y) = 1 := by
      intro y hy
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy ⊢
      have hy' := Subgroup.mem_subgroupOf.mp hy
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [hcv]
      exact (Subgroup.mem_normalizer_iff.mp (hWB w hw) (y : Y)).mp hy'
    have hca : c ^ (5 ^ a) = 1 := by
      have : c ^ (5 ^ a) = P.normalizerMonoidHom (g ^ (5 ^ a)) := (map_pow _ g _).symm
      have hg : g ^ (5 ^ a) = 1 := Subtype.ext (by simpa [g] using congrArg Subtype.val ha)
      rw [this, hg, map_one]
    obtain ⟨α, hαc, hα5⟩ := exists_equivariant_aut_pow (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) c hc a hca
    have hcardQ : Nat.card (↥P ⧸ N) ≤ 4 := by
      have : Nat.card (↥P ⧸ N) = (P ⊓ Lb).relIndex P := rfl
      exact this.le.trans hidx
    have hα1 : α = 1 := mulAut_eq_one_of_card_le_four hcardQ α a hα5
    have hxx : (QuotientGroup.mk' N) (c ⟨x⁻¹, P.inv_mem hx⟩) = (QuotientGroup.mk' N) ⟨x⁻¹, P.inv_mem hx⟩ := by
      rw [hαc, hα1]; rfl
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxx
    have hmem := Subgroup.mem_subgroupOf.mp hxx
    have hcalc : (((c ⟨x⁻¹, P.inv_mem hx⟩)⁻¹ * ⟨x⁻¹, P.inv_mem hx⟩ : ↥P) : Y) = ⁅w, x⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcv, commutatorElement_def]
      group
    rw [hcalc] at hmem
    rw [← commutatorElement_inv]
    exact B.inv_mem hmem
  have hBL : ∀ b ∈ B, ∀ w ∈ W, ⁅b, w⁆ ∈ L₁ ⊓ L₂ := by
    intro b hb w hw
    obtain ⟨a, ha⟩ := hW5 ⟨w, hw⟩
    have hwa : w ^ (5 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨r₁, hr₁, h₁⟩ := h.sl₁
    obtain ⟨r₂, hr₂, h₂⟩ := h.sl₂
    obtain ⟨F₁, _, _, φ₁, hodd₁, hs₁, hk₁⟩ := proj_generic L₁ L₂ h.comm h.card_inf hr₁ h₁
    obtain ⟨F₂, _, _, φ₂, hodd₂, hs₂, hk₂⟩ := proj_generic L₂ L₁ h.symm.comm h.symm.card_inf hr₂ h₂
    have hLn' : (L₂ ⊔ L₁).Normal := by rw [sup_comm]; exact hLn
    have hBLb' : B ≤ L₂ ⊔ L₁ := by rw [sup_comm]; exact inf_le_right
    refine ⟨?_, ?_⟩
    · exact proj_comm_mem (Lb := L₂ ⊔ L₁) (K := L₁) (B := B) hodd₂ φ₂ hs₂ hk₂ hBLb' hB2 (hW₁ hw)
        (hWB w hw) hwa b hb
    · exact proj_comm_mem (Lb := L₁ ⊔ L₂) (K := L₂) (B := B) hodd₁ φ₁ hs₁ hk₁ inf_le_right hB2 (hW₂ hw)
        (hWB w hw) hwa b hb
  have hUB : ⁅P, W⁆ ≤ B := Subgroup.commutator_le.mpr (fun x hx w hw => hPB x hx w hw)
  have hUL : ⁅⁅P, W⁆, W⁆ ≤ L₁ ⊓ L₂ :=
    Subgroup.commutator_le.mpr (fun u hu w hw => hBL u (hUB hu) w hw)
  have hidem : ⁅⁅P, W⁆, W⁆ = ⁅P, W⁆ :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 5 (by norm_num) W P hW5 hP5 hWP
  obtain ⟨t, ht₁, ht₂, ht2, -, -, htc⟩ := h.exists_t
  have hU1 : ⁅P, W⁆ ≤ L₁ ⊓ L₂ := hidem ▸ hUL
  have hUn : ∀ w ∈ W, ∀ u ∈ ⁅P, W⁆, w * u * w⁻¹ ∈ ⁅P, W⁆ := by
    intro w hw u hu
    have : w ∈ normalizer ((⁅P, W⁆ : Subgroup Y) : Set Y) :=
      Subgroup.normalizer_commutator_ge_right P W hw
    exact (Subgroup.mem_normalizer_iff.mp this u).mp hu
  have hcomm1 : ⁅⁅P, W⁆, W⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu w hw
    rw [Subgroup.mem_bot]
    rcases htc u (hU1 hu) with h1 | h1
    · rw [h1]; simp
    · have h2 := hU1 (hUn w hw u hu)
      have h3 : (w * u * w⁻¹) * (w * u * w⁻¹) = 1 := by
        rw [h1]
        have : t * t = 1 := by
          have := pow_orderOf_eq_one t
          rwa [ht2, pow_two] at this
        calc w * t * w⁻¹ * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
          _ = 1 := by rw [this]; group
      have hwt : w * u * w⁻¹ = u := by
        rcases htc _ h2 with h4 | h4
        · exfalso
          have : u = 1 := by
            have := congrArg (fun y => w⁻¹ * y * w) h4
            simpa [mul_assoc] using this
          rw [h1] at this
          have h5 : orderOf t = 1 := by rw [this]; exact orderOf_one
          omega
        · rw [h4, h1]
      have ht : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rwa [ht2, pow_two] at this
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
      rw [commutatorElement_def]
      calc u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) := by group
        _ = u * (w * u * w⁻¹)⁻¹ := by group
        _ = u * u⁻¹ := by rw [hwt]
        _ = 1 := by group
  rw [← hidem, hcomm1]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
