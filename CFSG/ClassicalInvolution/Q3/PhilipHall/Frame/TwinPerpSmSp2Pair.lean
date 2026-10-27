module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafTwin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Quaternion

variable {G : Type*} [Group G]

theorem mem_of_quaternion {Q : Subgroup G} (ψ : ↥Q ≃* QuaternionGroup 2) {t : G}
    (hu : ∀ y ∈ Q, y * y = 1 → y = 1 ∨ y = t) : t ∈ Q := by
  have hs2 : ((ψ.symm (QuaternionGroup.a 2) : ↥Q) : G) * (ψ.symm (QuaternionGroup.a 2) : ↥Q) = 1 := by
    have h1 : ψ.symm (QuaternionGroup.a 2) * ψ.symm (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, show (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 by
        decide, map_one]
    exact congrArg Subtype.val h1
  have hs1 : ((ψ.symm (QuaternionGroup.a 2) : ↥Q) : G) ≠ 1 := by
    intro h1
    have h2 : ψ.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h1
    have h3 : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
      have := congrArg ψ h2
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd h3 (by decide)
  rcases hu _ (ψ.symm (QuaternionGroup.a 2)).2 hs2 with h | h
  · exact absurd h hs1
  · rw [← h]
    exact (ψ.symm (QuaternionGroup.a 2)).2

theorem exists_q8_gens {Q : Subgroup G} (ψ : ↥Q ≃* QuaternionGroup 2) {t : G} (htQ : t ∈ Q)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ A ∈ Q, ∃ B ∈ Q, A * A = t ∧ B * B = t ∧ (A * B) * (A * B) = t ∧ A * B = t * (B * A) ∧
      A * B ≠ B * A ∧ (A * B) * A ≠ A * (A * B) := by
  let ι : QuaternionGroup 2 →* G := Q.subtype.comp ψ.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp ψ.symm.injective
  have hιt : ι (QuaternionGroup.a 2) = t := by
    have hq : ψ ⟨t, htQ⟩ = QuaternionGroup.a 2 := by
      have h1 : ψ ⟨t, htQ⟩ * ψ ⟨t, htQ⟩ = 1 := by
        rw [← map_mul, show (⟨t, htQ⟩ : ↥Q) * ⟨t, htQ⟩ = 1 from Subtype.ext ht2, map_one]
      have h2 : ψ ⟨t, htQ⟩ ≠ 1 := by
        intro h
        apply ht1
        have h3 : (⟨t, htQ⟩ : ↥Q) = 1 := by
          have := congrArg ψ.symm h
          rwa [MulEquiv.symm_apply_apply, map_one] at this
        exact congrArg Subtype.val h3
      have key : ∀ q : QuaternionGroup 2, q * q = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by
        decide
      exact (key _ h1).resolve_left h2
    show ((ψ.symm (QuaternionGroup.a 2) : ↥Q) : G) = t
    rw [← hq, MulEquiv.symm_apply_apply]
  refine ⟨ι (QuaternionGroup.a 1), (ψ.symm _).2, ι (QuaternionGroup.xa 0), (ψ.symm _).2, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 by decide, hιt]
  · rw [← map_mul, show (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 by decide, hιt]
  · rw [← map_mul, ← map_mul, show ((QuaternionGroup.a 1 : QuaternionGroup 2) *
      QuaternionGroup.xa 0) * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
      QuaternionGroup.a 2 by decide, hιt]
  · rw [← hιt, ← map_mul, ← map_mul, ← map_mul, show (QuaternionGroup.a 1 : QuaternionGroup 2) *
      QuaternionGroup.xa 0 = QuaternionGroup.a 2 * (QuaternionGroup.xa 0 * QuaternionGroup.a 1) by
      decide]
  · intro h
    rw [← map_mul, ← map_mul] at h
    exact absurd (hι h) (by decide)
  · intro h
    simp only [← map_mul] at h
    exact absurd (hι h) (by decide)

theorem isPGroup_sup_of_commute {Q Q' : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hQ' : IsPGroup 2 ↥Q')
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x) : IsPGroup 2 ↥(Q ⊔ Q') := by
  refine hQ.to_sup_of_normal_left' hQ' ?_
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [show y * x * y⁻¹ = x by rw [← hcomm x hx y hy]; group]
    exact hx
  · intro hx
    have h1 := hcomm _ hx y hy
    have h2 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
        _ = y * x * y⁻¹ := by group
    rw [h2]
    exact hx

theorem card_quaternion {Q : Subgroup G} (ψ : ↥Q ≃* QuaternionGroup 2) : Nat.card ↥Q = 8 := by
  rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem isPGroup_quaternion {Q : Subgroup G} (ψ : ↥Q ≃* QuaternionGroup 2) : IsPGroup 2 ↥Q :=
  IsPGroup.of_card (n := 3) (by rw [card_quaternion ψ]; norm_num)

theorem eq_of_mul_self_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  haveI := Fintype.ofFinite C
  by_contra hxy
  have h2 := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [pow_two]; exact hx
    · rw [pow_two]; exact hy
  have hcard : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx1, Ne.symm hy1⟩
  have h3 := Finset.card_le_card hsub
  omega

end Quaternion

section Central

variable {G : Type*} [Group G] [Finite G]

theorem false_of_commuting_q8 {F : Subgroup G} [F.Normal]
    (hcyc : ∀ P : Subgroup (G ⧸ F), IsPGroup 2 P → IsCyclic P)
    (hcen : ∀ H : Subgroup G, H ≤ F → IsPGroup 2 ↥H → ∀ w ∈ H, w * w = 1 → ∀ g ∈ H,
      w * g = g * w)
    {Q Q' : Subgroup G} (ψ : ↥Q ≃* QuaternionGroup 2) (ψ' : ↥Q' ≃* QuaternionGroup 2)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x) {t : G} (htQ : t ∈ Q) (htQ' : t ∈ Q')
    (ht1 : t ≠ 1) (ht2 : t * t = 1) : False := by
  set P : Subgroup G := Q ⊔ Q' with hPdef
  have hP2 : IsPGroup 2 ↥P :=
    isPGroup_sup_of_commute (isPGroup_quaternion ψ) (isPGroup_quaternion ψ') hcomm
  have hQP : Q ≤ P := le_sup_left
  have hQ'P : Q' ≤ P := le_sup_right
  let π : G →* G ⧸ F := QuotientGroup.mk' F
  have hker : ∀ x : G, π x = 1 ↔ x ∈ F := fun x => QuotientGroup.eq_one_iff x
  set Pb : Subgroup (G ⧸ F) := P.map π with hPb
  haveI : IsCyclic ↥Pb := hcyc Pb (hP2.map π)
  have hπP : ∀ x ∈ P, π x ∈ Pb := fun x hx => Subgroup.mem_map_of_mem π hx
  have hpc : ∀ x ∈ P, ∀ y ∈ P, π x * π y = π y * π x := by
    intro x hx y hy
    have := (IsCyclic.isMulCommutative (α := ↥Pb)).is_comm.comm ⟨π x, hπP x hx⟩ ⟨π y, hπP y hy⟩
    exact congrArg Subtype.val this
  have hpu : ∀ x ∈ P, ∀ y ∈ P, π x * π x = 1 → π y * π y = 1 → π x ≠ 1 → π y ≠ 1 →
      π x = π y := by
    intro x hx y hy hx2 hy2 hx1 hy1
    have := eq_of_mul_self_of_isCyclic (C := ↥Pb) (x := ⟨π x, hπP x hx⟩) (y := ⟨π y, hπP y hy⟩)
      (Subtype.ext hx2) (Subtype.ext hy2) (fun h => hx1 (congrArg Subtype.val h))
      (fun h => hy1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  obtain ⟨A, hA, B, hB, hA2, hB2, hC2, hABt, hAB, hCA⟩ := exists_q8_gens ψ htQ ht1 ht2
  obtain ⟨A', hA', B', hB', hA2', hB2', hC2', -, hAB', hCA'⟩ := exists_q8_gens ψ' htQ' ht1 ht2
  have htF : t ∈ F := by
    have h1 := hpc A (hQP hA) B (hQP hB)
    rw [← map_mul, ← map_mul, hABt, map_mul] at h1
    have h2 : π t = 1 := mul_eq_right.mp h1
    exact (hker t).mp h2
  have hsq : ∀ u : G, u * u = t → π u * π u = 1 := fun u hu => by
    rw [← map_mul, hu]
    exact (hker t).mpr htF
  have key : ∀ X : Subgroup G, X ≤ P → ∀ A ∈ X, ∀ B ∈ X, A * A = t → B * B = t →
      (A * B) * (A * B) = t → A * B ≠ B * A → (A * B) * A ≠ A * (A * B) →
      ∃ u ∈ X, ∃ v ∈ X, u ∈ F ∧ u * u = t ∧ v * v = t ∧ u * v ≠ v * u := by
    intro X hXP A hA B hB hA2 hB2 hC2 hAB hCA
    by_cases hAF : A ∈ F
    · exact ⟨A, hA, B, hB, hAF, hA2, hB2, hAB⟩
    by_cases hBF : B ∈ F
    · exact ⟨B, hB, A, hA, hBF, hB2, hA2, fun h => hAB h.symm⟩
    have hπ : π A = π B := hpu A (hXP hA) B (hXP hB) (hsq A hA2) (hsq B hB2)
      (fun h => hAF ((hker A).mp h)) (fun h => hBF ((hker B).mp h))
    have hCF : A * B ∈ F := by
      rw [← hker, map_mul, ← hπ]
      exact hsq A hA2
    exact ⟨A * B, X.mul_mem hA hB, A, hA, hCF, hC2, hA2, hCA⟩
  obtain ⟨u, hu, v, hv, huF, hu2, hv2, huv⟩ := key Q hQP A hA B hB hA2 hB2 hC2 hAB hCA
  obtain ⟨u', hu', v', hv', huF', hu2', hv2', huv'⟩ :=
    key Q' hQ'P A' hA' B' hB' hA2' hB2' hC2' hAB' hCA'
  have hH2 : IsPGroup 2 ↥(P ⊓ F) := hP2.to_inf_left
  have hHF : P ⊓ F ≤ F := inf_le_right
  have hmemH : ∀ x, x ∈ P → x ∈ F → x ∈ P ⊓ F := fun x h1 h2 => Subgroup.mem_inf.mpr ⟨h1, h2⟩
  have hww : ∀ x ∈ Q, ∀ x' ∈ Q', x * x = t → x' * x' = t → (x * x') * (x * x') = 1 := by
    intro x hx x' hx' h1 h2
    calc (x * x') * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm x hx x' hx']
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [h1, h2, ht2]
  by_cases hvF : v ∈ F
  ·
    have hw := hcen _ hHF hH2 (u * u') (hmemH _ (P.mul_mem (hQP hu) (hQ'P hu'))
      (F.mul_mem huF huF')) (hww u hu u' hu' hu2 hu2') v (hmemH v (hQP hv) hvF)
    apply huv
    have e1 : u * u' * v = (u * v) * u' := by
      rw [mul_assoc, ← hcomm v hv u' hu', ← mul_assoc]
    rw [e1, ← mul_assoc] at hw
    exact mul_right_cancel hw
  by_cases hvF' : v' ∈ F
  ·
    have hw := hcen _ hHF hH2 (u * u') (hmemH _ (P.mul_mem (hQP hu) (hQ'P hu'))
      (F.mul_mem huF huF')) (hww u hu u' hu' hu2 hu2') v' (hmemH v' (hQ'P hv') hvF')
    apply huv'
    have e1 : v' * (u * u') = u * (v' * u') := by
      rw [← mul_assoc, ← hcomm u hu v' hv', mul_assoc]
    rw [e1, mul_assoc] at hw
    exact mul_left_cancel hw
  ·
    have hπ : π v = π v' := hpu v (hQP hv) v' (hQ'P hv') (hsq v hv2) (hsq v' hv2')
      (fun h => hvF ((hker v).mp h)) (fun h => hvF' ((hker v').mp h))
    have hwF : v * v' ∈ F := by
      rw [← hker, map_mul, ← hπ]
      exact hsq v hv2
    have hw := hcen _ hHF hH2 (v * v') (hmemH _ (P.mul_mem (hQP hv) (hQ'P hv')) hwF)
      (hww v hv v' hv' hv2 hv2') u (hmemH u (hQP hu) huF)
    apply huv
    have e1 : v * v' * u = (v * u) * v' := by
      rw [mul_assoc, ← hcomm u hu v' hv', ← mul_assoc]
    rw [e1, ← mul_assoc] at hw
    exact (mul_right_cancel hw).symm

theorem sixteen_dvd_card_sup_q8 {Q Q' : Subgroup G} (ψ : ↥Q ≃* QuaternionGroup 2)
    (ψ' : ↥Q' ≃* QuaternionGroup 2) (hcomm : ∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x) {t : G}
    (htQ' : t ∈ Q') (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    IsPGroup 2 ↥(Q ⊔ Q') ∧ 16 ∣ Nat.card ↥(Q ⊔ Q') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(Q ⊔ Q') :=
    isPGroup_sup_of_commute (isPGroup_quaternion ψ) (isPGroup_quaternion ψ') hcomm
  refine ⟨hP2, ?_⟩
  obtain ⟨A', hA', B', hB', -, -, -, -, hAB', -⟩ := exists_q8_gens ψ' htQ' ht1 ht2
  have hA'Q : A' ∉ Q := fun h => hAB' (hcomm A' h B' hB')
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hQcard : Nat.card ↥Q = 8 := card_quaternion ψ
  have h8 : 8 ∣ Nat.card ↥(Q ⊔ Q') := hQcard ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card ↥(Q ⊔ Q') ≠ 8 := by
    intro h8'
    have hQeq : Q = Q ⊔ Q' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h8', hQcard])
    apply hA'Q
    rw [hQeq]
    exact Subgroup.mem_sup_right hA'
  have hk3 : 3 ≤ k := by
    have h1 : 2 ^ 3 ∣ 2 ^ k := by
      rw [← hk]
      exact h8
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : k = 3 := by omega
    exact hne (by rw [hk, this]; norm_num)
  rw [hk]
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ k := pow_dvd_pow 2 hk4

end Central

set_option linter.unusedSectionVars false


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_commuting_q8 (h : PerpHypS n Y R S t) :
    ∃ Q Q' : Subgroup Y, Nonempty (↥Q ≃* QuaternionGroup 2) ∧
      Nonempty (↥Q' ≃* QuaternionGroup 2) ∧ (∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x) ∧
      t ∈ Q ∧ t ∈ Q' := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  obtain ⟨g, -, hne, -, hz'⟩ := exists_twin h
  set K : Subgroup Y := tightCore R with hKdef
  set K' : Subgroup Y := conjSub g K with hK'def
  have h4 := hΩ.omega4 K (CoreAssembly.mem_conjClass_self _) K' ⟨g, rfl⟩ (Ne.symm hne)
  have ht2 : orderOf t = 2 := h.core.datum.order
  have hdvd : 2 ^ 1 ∣ Nat.card ↥(K ⊓ K') := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (Subgroup.mem_inf.mpr ⟨hz.mem, hz'.mem⟩)
    rw [ht2] at this
    simpa using this
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
    (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  have hcomm : ⁅K, K'⁆ ≤ oddCoreOf K ⊓ oddCoreOf K' := h4.2 (le_antisymm h4.1 h1)
  have hKK' : ⁅K, K'⁆ ≤ K' :=
    hcomm.trans (inf_le_right.trans (CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.oddCoreOf_le' K'))
  have hK'K : ⁅K', K⁆ ≤ K := by
    rw [Subgroup.commutator_comm]
    exact hcomm.trans (inf_le_left.trans (CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.oddCoreOf_le' K))
  obtain ⟨R₀, R₀', hR₀, hR₀', hcom⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.exists_commuting_sylow2
    (CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.le_normalizer_of_commutator_le hK'K)
    (CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.le_normalizer_of_commutator_le hKK')
    (CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.card_oddCoreOf_odd K) (hcomm.trans inf_le_left)
  have hP : IsSylow2In ((S : Subgroup R).map R.subtype) K := h.core.datum.sylow_core
  obtain ⟨e⟩ := h.core.q8
  let e₁ : ↥((S : Subgroup R).map R.subtype) ≃* QuaternionGroup 2 :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e
  obtain ⟨φ₀⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.nonempty_mulEquiv_of_isSylow2In hP hR₀
  have hP' : IsSylow2In (conjSub g ((S : Subgroup R).map R.subtype)) K' := hP.conj g
  obtain ⟨φ₀'⟩ := CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.nonempty_mulEquiv_of_isSylow2In hP' hR₀'
  let e₂ : ↥((S : Subgroup R).map R.subtype) ≃* ↥(conjSub g ((S : Subgroup R).map R.subtype)) :=
    Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let ψ : ↥R₀ ≃* QuaternionGroup 2 := φ₀.symm.trans e₁
  let ψ' : ↥R₀' ≃* QuaternionGroup 2 := (e₂.trans φ₀').symm.trans e₁
  exact ⟨R₀, R₀', ⟨ψ⟩, ⟨ψ'⟩, hcom, mem_of_quaternion ψ fun y hy => hz.unique y (hR₀.1 hy),
    mem_of_quaternion ψ' fun y hy => hz'.unique y (hR₀'.1 hy)⟩

theorem false_of_perp_central (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hcyc : ∀ P : Subgroup (Y ⧸ N), IsPGroup 2 P → IsCyclic P)
    (hcen : ∀ H : Subgroup Y, H ≤ N → IsPGroup 2 ↥H → ∀ w ∈ H, w * w = 1 → ∀ g ∈ H,
      w * g = g * w) : False := by
  obtain ⟨Q, Q', ⟨ψ⟩, ⟨ψ'⟩, hcomm, htQ, htQ'⟩ := exists_commuting_q8 h
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  exact false_of_commuting_q8 hcyc hcen ψ ψ' hcomm htQ htQ' hz.ne_one hz.sq

theorem sixteen_dvd_card_of_perp (h : PerpHypS n Y R S t) : 16 ∣ Nat.card Y := by
  obtain ⟨Q, Q', ⟨ψ⟩, ⟨ψ'⟩, hcomm, -, htQ'⟩ := exists_commuting_q8 h
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  exact (sixteen_dvd_card_sup_q8 ψ ψ' hcomm htQ' hz.ne_one hz.sq).2.trans
    (Subgroup.card_subgroup_dvd_card _)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP2
