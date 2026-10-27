module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Out
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open Out
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_kbar_of_equiv {L : Subgroup G} (e : Kbar L ≃* Q8) : IsPGroup 2 (Kbar L) :=
  IsPGroup.of_card (n := 3) (by rw [Nat.card_congr e.toEquiv, card_q8]; norm_num)

theorem nonempty_kbar_conj_equiv {L : Subgroup G} (g : G) (e : Kbar L ≃* Q8) :
    Nonempty (Kbar (conjSub g L) ≃* Q8) := by
  let φ : ↥L ≃* ↥(conjSub g L) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hφ : (classicalInvolutionOddCore ↥L).map φ.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub g L) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant φ
  exact ⟨(QuotientGroup.congr _ _ φ hφ).symm.trans e⟩

theorem not_mem_oddCoreOf_of_invol {L : Subgroup G} {y : G} (h1 : y ≠ 1) (h2 : y * y = 1) :
    y ∉ oddCoreOf L := by
  intro h
  have h3 := TwinExact.odd_orderOf_of_mem_oddCoreOf h
  rw [orderOf_eq_prime (by rw [pow_two]; exact h2) h1] at h3
  exact absurd h3 (by decide)

theorem isPGroup_zpowers_of_mul_self {y : G} (h : y * y = 1) : IsPGroup 2 (Subgroup.zpowers y) := by
  by_cases h1 : y = 1
  · subst h1
    rw [Subgroup.zpowers_one_eq_bot]
    exact IsPGroup.of_bot
  · exact IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact h) h1]
      norm_num)

theorem eq_of_mk_eq_mk {L P : Subgroup G} (hP2 : IsPGroup 2 P) (hPL : P ≤ L) {a x : G}
    (ha : a ∈ P) (hx : x ∈ P)
    (h : (QuotientGroup.mk ⟨a, hPL ha⟩ : Kbar L) = QuotientGroup.mk ⟨x, hPL hx⟩) : a = x := by
  have h1 := QuotientGroup.eq.mp h
  have h2 : a⁻¹ * x ∈ oddCoreOf L := (Out.mem_oddCoreOf_iff L _).mpr h1
  have h4 : a⁻¹ * x ∈ oddCoreOf L ⊓ P := ⟨h2, P.mul_mem (P.inv_mem ha) hx⟩
  rw [TwinExact.inf_oddCoreOf_eq_bot hP2] at h4
  exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp h4)

theorem mk_mul_self_ne_one {L : Subgroup G} {w : G} (hwL : w ∈ L) (hw2 : w * w ∉ oddCoreOf L) :
    (QuotientGroup.mk ⟨w, hwL⟩ : Kbar L) * QuotientGroup.mk ⟨w, hwL⟩ ≠ 1 := by
  intro h
  rw [← QuotientGroup.mk_mul] at h
  exact hw2 ((Out.mem_oddCoreOf_iff L _).mpr ((QuotientGroup.eq_one_iff _).mp h))

theorem mk_comm_of_mem_trivialOnQuot {L : Subgroup G} {u : G} (huL : u ∈ L)
    (hu : u ∈ trivialOnQuot L) (y : Kbar L) :
    (QuotientGroup.mk ⟨u, huL⟩ : Kbar L) * y = y * QuotientGroup.mk ⟨u, huL⟩ := by
  induction y using QuotientGroup.induction_on with
  | H y' =>
    show (QuotientGroup.mk (⟨u, huL⟩ * y') : Kbar L) = QuotientGroup.mk (y' * ⟨u, huL⟩)
    rw [QuotientGroup.eq_iff_div_mem]
    refine (Out.mem_oddCoreOf_iff L _).mp ?_
    have : ⁅u, (y' : G)⁆ ∈ oddCoreOf L := hu.2 y' y'.2
    simpa [commutatorElement_def, div_eq_mul_inv, mul_assoc] using this

theorem eq_one_of_mem_oddCoreOf_of_mem {L P : Subgroup G} (hP2 : IsPGroup 2 P) {y : G}
    (hyL : y ∈ oddCoreOf L) (hyP : y ∈ P) : y = 1 := by
  have h : y ∈ oddCoreOf L ⊓ P := ⟨hyL, hyP⟩
  rw [TwinExact.inf_oddCoreOf_eq_bot hP2] at h
  exact Subgroup.mem_bot.mp h

theorem mem_cases_of_equiv_q8 {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hRK : R ≤ K) (eR : ↥R ≃* Q8) {y : G} (hy : y ∈ R) : y = 1 ∨ y = z ∨ y * y = z := by
  have hq : ∀ p : Q8, p * p * (p * p) = 1 := by decide
  by_cases h1 : y * y = 1
  · rcases hz.unique y (hRK hy) h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right
    right
    have h2 : (y * y) * (y * y) = 1 := by
      have h3 := hq (eR ⟨y, hy⟩)
      rw [← map_mul, ← map_mul] at h3
      have h4 : (⟨y, hy⟩ * ⟨y, hy⟩ * (⟨y, hy⟩ * ⟨y, hy⟩) : ↥R) = 1 :=
        eR.injective (h3.trans (map_one eR).symm)
      exact congrArg Subtype.val h4
    exact (hz.unique _ (K.mul_mem (hRK hy) (hRK hy)) h2).resolve_left h1

theorem exists_conj_of_mul_odd {r o : G} (hr : r * r = 1) (ho : Odd (orderOf o))
    (hc : (r * o) * (r * o) = 1) : ∃ q : G, r * o = q⁻¹ * r * q := by
  obtain ⟨k, hk⟩ := ho
  have hm : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hro : r * o * r⁻¹ = o⁻¹ := by
    rw [hrinv]
    exact eq_inv_of_mul_eq_one_left (by rw [← hc]; group)
  refine ⟨o ^ (k + 1), ?_⟩
  have hconj : r * o ^ (k + 1) * r⁻¹ = (o ^ (k + 1))⁻¹ := by rw [← conj_pow, hro, inv_pow]
  have hsq : (o ^ (k + 1))⁻¹ * (o ^ (k + 1))⁻¹ = o⁻¹ := by
    rw [← mul_inv_rev, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hm,
      one_mul]
  calc r * o = (r * o * r⁻¹) * r := by group
    _ = (o ^ (k + 1))⁻¹ * (o ^ (k + 1))⁻¹ * r := by rw [hro, hsq]
    _ = (o ^ (k + 1))⁻¹ * (r * o ^ (k + 1) * r⁻¹) * r := by rw [hconj]
    _ = (o ^ (k + 1))⁻¹ * r * o ^ (k + 1) := by group

theorem innerOn_of_mem_kerG {L : Subgroup G} (e : Kbar L ≃* Q8) {y : G} (hy : y ∈ kerG L) :
    InnerOn L y := by
  obtain ⟨h, h1⟩ := mem_kerG.mp hy
  exact (psiK_eq_one_iff L e ⟨y, h⟩).mp h1

theorem not_innerOn_mul {L : Subgroup G} (e : Kbar L ≃* Q8) {c c' : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) (hc' : c' ∈ Subgroup.normalizer (L : Set G))
    (h : InnerOn L c) (h' : ¬ InnerOn L c') : ¬ InnerOn L (c * c') := by
  intro h''
  have h1 := (psiK_eq_one_iff L e ⟨c, hc⟩).mpr h
  have h3 := (psiK_eq_one_iff L e ⟨c * c', Subgroup.mul_mem _ hc hc'⟩).mpr h''
  have e1 : (⟨c * c', Subgroup.mul_mem _ hc hc'⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨c, hc⟩ * ⟨c', hc'⟩ := rfl
  rw [e1, map_mul, h1, one_mul] at h3
  exact h' ((psiK_eq_one_iff L e _).mp h3)

theorem not_innerOn_of_outer {L R : Subgroup G} (hQ : IsPGroup 2 (Kbar L)) (hR : IsSylow2In R L)
    (eR : ↥R ≃* Q8) {c : G} (hcR : c ∈ Subgroup.normalizer (R : Set G))
    (hout : TL4.LinkDisc.B2b.Outer R c) : ¬ InnerOn L c := by
  rintro ⟨k, hkL, hk⟩
  obtain ⟨r, hr, o, ho, rfl⟩ := TwinExact.mem_mul_oddCore_of_sylow hQ hR k hkL
  have hbot : oddCoreOf L ⊓ R = ⊥ := TwinExact.inf_oddCoreOf_eq_bot hR.2.1
  have hrL : r ∈ L := hR.1 hr
  have key : ∀ y ∈ R, c * y * c⁻¹ = r * y * r⁻¹ := by
    intro y hy
    have hyL : y ∈ L := hR.1 hy
    have hn : o * y * o⁻¹ * y⁻¹ ∈ oddCoreOf L := by
      have e1 : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
      rw [e1]
      exact (oddCoreOf L).mul_mem ho (mem_normalizer_oddCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer hyL) ((oddCoreOf L).inv_mem ho))
    have hrn : r * (o * y * o⁻¹ * y⁻¹) * r⁻¹ ∈ oddCoreOf L :=
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hrL) hn
    have h2 : (c * y * c⁻¹) * (r * y * r⁻¹)⁻¹ ∈ oddCoreOf L := by
      have e1 : (c * y * c⁻¹) * (r * y * r⁻¹)⁻¹ =
          ((c * y * c⁻¹) * (r * o * y * (r * o)⁻¹)⁻¹) * (r * (o * y * o⁻¹ * y⁻¹) * r⁻¹) := by
        group
      rw [e1]
      exact (oddCoreOf L).mul_mem (hk y hyL) hrn
    have h3 : (c * y * c⁻¹) * (r * y * r⁻¹)⁻¹ ∈ R :=
      R.mul_mem ((Subgroup.mem_normalizer_iff.mp hcR y).mp hy)
        (R.inv_mem (R.mul_mem (R.mul_mem hr hy) (R.inv_mem hr)))
    have h4 : (c * y * c⁻¹) * (r * y * r⁻¹)⁻¹ ∈ oddCoreOf L ⊓ R := ⟨h2, h3⟩
    rw [hbot] at h4
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h4)
  obtain ⟨w', hw'1, hw'r⟩ := q8_comm_order_four (eR ⟨r, hr⟩)
  have hw : eR (eR.symm w') = w' := eR.apply_symm_apply w'
  have hwr : ((eR.symm w' : ↥R) : G) * r = r * (eR.symm w' : ↥R) := by
    have h1 : eR.symm w' * ⟨r, hr⟩ = ⟨r, hr⟩ * eR.symm w' := by
      apply eR.injective
      rw [map_mul, map_mul, hw]
      exact hw'r
    exact congrArg Subtype.val h1
  have hww : ((eR.symm w' : ↥R) : G) * (eR.symm w' : ↥R) ≠ 1 := by
    intro h
    apply hw'1
    have h1 : eR.symm w' * eR.symm w' = 1 := Subtype.ext h
    have h2 : eR (eR.symm w' * eR.symm w') = 1 := by rw [h1, map_one]
    rwa [map_mul, hw] at h2
  have hwc : ((eR.symm w' : ↥R) : G) * c = c * (eR.symm w' : ↥R) := by
    have h1 := key _ (eR.symm w').2
    have h2 : r * ((eR.symm w' : ↥R) : G) * r⁻¹ = (eR.symm w' : ↥R) := by
      rw [← hwr, mul_inv_cancel_right]
    rw [h2] at h1
    calc ((eR.symm w' : ↥R) : G) * c = (c * (eR.symm w' : ↥R) * c⁻¹) * c := by rw [h1]
      _ = c * (eR.symm w' : ↥R) := by group
  exact hww (hout _ (eR.symm w').2 hwc)

theorem innerOn_of_invol_comm {L : Subgroup G} (e : Kbar L ≃* Q8) {c w : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) (hc2 : c * c = 1) (hwL : w ∈ L)
    (hw2 : w * w ∉ oddCoreOf L) (hcw : c * w = w * c) : InnerOn L c := by
  have hαα : ∀ y, rhoK L ⟨c, hc⟩ (rhoK L ⟨c, hc⟩ y) = y := by
    intro y
    have h1 : (⟨c, hc⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨c, hc⟩ = 1 := Subtype.ext hc2
    have h2 : rhoK L ⟨c, hc⟩ * rhoK L ⟨c, hc⟩ = 1 := by rw [← map_mul, h1, map_one]
    exact congrArg (fun φ : MulAut (Kbar L) => φ y) h2
  have hαw : rhoK L ⟨c, hc⟩ (QuotientGroup.mk ⟨w, hwL⟩) = QuotientGroup.mk ⟨w, hwL⟩ := by
    rw [rhoK_mk]
    congr 1
    apply Subtype.ext
    show c * w * c⁻¹ = w
    rw [hcw, mul_inv_cancel_right]
  obtain ⟨g, hg⟩ := aut_inner_of_invol e _ hαα (mk_mul_self_ne_one hwL hw2) hαw
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  have h1 : rhoK L ⟨c, hc⟩ = MulAut.conj (QuotientGroup.mk k : Kbar L) := by
    apply MulEquiv.ext
    intro q
    rw [hg q]
    rfl
  exact ⟨k, k.2, fun y hy => (rhoK_eq_conj_iff L ⟨c, hc⟩ k).mp h1 ⟨y, hy⟩⟩

theorem innerOn_mul_self_of_two_pow {L : Subgroup G} (e : Kbar L ≃* Q8) {w : G}
    (hw : w ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (hk : w ^ (2 ^ k) = 1) :
    InnerOn L (w * w) := by
  have hpow : (⟨w, hw⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ (2 ^ k) = 1 :=
    Subtype.ext (by simpa using hk)
  have h1 := perm_sq_eq_one_of_two_pow (card_idx2_of_equiv_q8 e) (psiK L ⟨w, hw⟩) (k := k)
    (by rw [← map_pow, hpow, map_one])
  have e1 : (⟨w * w, Subgroup.mul_mem _ hw hw⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨w, hw⟩ * ⟨w, hw⟩ := rfl
  exact (psiK_eq_one_iff L e ⟨w * w, Subgroup.mul_mem _ hw hw⟩).mp (by rw [e1, map_mul]; exact h1)

theorem not_mem_omegaStarNbr_of_outer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {A B : Subgroup G} {b : G} (hb : IsUniqueInvolution B b) (eA : Kbar A ≃* Q8)
    (hbout : ¬ InnerOn A b) : B ∉ omegaStarNbr Ω A := by
  rintro ⟨-, -, U, hU, hUB, hUN⟩
  obtain ⟨-, -, -, -, -, -, hUc, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  obtain ⟨w, hwU, hww⟩ := Asc77.T3.exists_sq_eq_of_cyclic hb hUB hUc hU2 hU4
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU2) ⟨w, hwU⟩
  have hk' : w ^ (2 ^ k) = 1 := by
    have := pow_orderOf_eq_one (⟨w, hwU⟩ : ↥U)
    rw [hk] at this
    exact congrArg Subtype.val this
  have h := innerOn_mul_self_of_two_pow eA (hUN hwU) hk'
  rw [hww] at h
  exact hbout h

theorem not_innerOn_of_not_innerOn {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h8 : ∀ P ∈ RSet Ω, Nat.card P = 8) {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω) {a b : G}
    (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b) (hab : a ≠ b)
    (hc : a * b = b * a) (hbout : ¬ InnerOn A b) (haN : a ∈ Subgroup.normalizer (B : Set G))
    (eA : Kbar A ≃* Q8) (eB : Kbar B ≃* Q8) : ¬ InnerOn B a := by
  intro hin
  have hAB : A ≠ B := by
    rintro rfl
    exact hab (ha.eq hb)
  have hnt : A ∉ twinSet Ω B := by
    rintro ⟨-, z', hz'B, hz'A⟩
    exact hab ((ha.eq hz'A).trans (hz'B.eq hb))
  have haC : a ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hc
  obtain ⟨V₀, hV₀, haV₀⟩ := IsSylow2In.exists_ge (isPGroup_zpowers_of_mul_self ha.sq)
    (Subgroup.zpowers_le.mpr (show a ∈ A ⊓ Subgroup.centralizer ({b} : Set G) from ⟨ha.mem, haC⟩))
  have hnotB : B ∉ omegaStarNbr Ω A := not_mem_omegaStarNbr_of_outer hΩ hb eA hbout
  rcases Sec6Gen.l6_2Gen G Ω hΩ B hB b hb A hA hnt a ha V₀ hV₀ (haV₀ (Subgroup.mem_zpowers a)) with
    ⟨-, hne⟩ | ⟨hV1, -, R, hR, hRB, hVR, hsd⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hcomm⟩
  · exact hne (mem_normalizer_iff_conjSub_eq.mp haN)
  · have hRs : IsSylow2In R B := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hB hR hRB
    obtain ⟨eR⟩ := nonempty_equiv_q8' (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR) (h8 R hR)
    have haR : a ∈ Subgroup.normalizer (R : Set G) :=
      hVR (by rw [hV1]; exact Subgroup.mem_zpowers a)
    have hout : TL4.LinkDisc.B2b.Outer R a :=
      TL4.LinkDisc.B2b.outer_of_isSemidihedral (r := 3) (by norm_num) eR ha.sq haR
        (by rw [← hV1]; exact hsd)
    exact not_innerOn_of_outer (isPGroup_kbar_of_equiv eB) hRs eR haR hout hin
  · exact hnotB (Q3T6.Mu.omegaStarNbr_symm hΩ hB hA
      ⟨hA, hAB, V₀, hVU, hV₀.1.trans inf_le_left, hVN⟩)
  · have hVN : V₀ ≤ Subgroup.normalizer (B : Set G) :=
      Asc77.T3.le_normalizer_of_commutator_le' (hcomm.trans (oddCoreOf_le_self B))
    exact hnotB (Q3T6.Mu.omegaStarNbr_symm hΩ hB hA
      (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ B ⟨hA, hAB, V₀, hVR, hV₀.1.trans inf_le_left, hVN⟩))

theorem eq_or_eq_inv_of_mk_comm {L P : Subgroup G} (e : Kbar L ≃* Q8) (hP2 : IsPGroup 2 P)
    (hPL : P ≤ L) {x a : G} (hxP : x ∈ P) (haP : a ∈ P) (hx2 : x * x ∉ oddCoreOf L)
    (ha2 : a * a ∉ oddCoreOf L)
    (hcomm : (QuotientGroup.mk ⟨x, hPL hxP⟩ : Kbar L) * QuotientGroup.mk ⟨a, hPL haP⟩ =
      QuotientGroup.mk ⟨a, hPL haP⟩ * QuotientGroup.mk ⟨x, hPL hxP⟩) : a = x ∨ a = x⁻¹ := by
  have hcomm' : e (QuotientGroup.mk ⟨x, hPL hxP⟩) * e (QuotientGroup.mk ⟨a, hPL haP⟩) =
      e (QuotientGroup.mk ⟨a, hPL haP⟩) * e (QuotientGroup.mk ⟨x, hPL hxP⟩) := by
    rw [← map_mul, ← map_mul, hcomm]
  rcases q8_eq_or_eq_inv_of_comm _ _ (mul_self_ne_one_map e (mk_mul_self_ne_one (hPL hxP) hx2))
    (mul_self_ne_one_map e (mk_mul_self_ne_one (hPL haP) ha2)) hcomm' with h | h
  · exact Or.inl (eq_of_mk_eq_mk hP2 hPL haP hxP (e.injective h))
  · right
    rw [← map_inv] at h
    have h2 : (QuotientGroup.mk ⟨a, hPL haP⟩ : Kbar L) =
        QuotientGroup.mk ⟨x⁻¹, hPL (P.inv_mem hxP)⟩ := e.injective h
    exact eq_of_mk_eq_mk hP2 hPL haP (P.inv_mem hxP) h2

theorem rhoK_mk_eq_or_eq_inv {L L' : Subgroup G} (e : Kbar L ≃* Q8) (hL' : L' ≤ trivialOnQuot L)
    {a a' w : G} (haL : a ∈ L) (ha2 : a * a ∉ oddCoreOf L) (ha' : a' ∈ L')
    (hwN : w ∈ Subgroup.normalizer (L : Set G)) (hwN' : w ∈ Subgroup.normalizer (L' : Set G))
    (hwb : w * (a * a') * w⁻¹ = a * a') :
    rhoK L ⟨w, hwN⟩ (QuotientGroup.mk ⟨a, haL⟩) = QuotientGroup.mk ⟨a, haL⟩ ∨
      rhoK L ⟨w, hwN⟩ (QuotientGroup.mk ⟨a, haL⟩) = (QuotientGroup.mk ⟨a, haL⟩)⁻¹ := by
  obtain ⟨u, hu⟩ : ∃ u : G, u = a⁻¹ * (w * a * w⁻¹) := ⟨_, rfl⟩
  have huL : u ∈ L := by
    rw [hu]
    exact L.mul_mem (L.inv_mem haL) ((Subgroup.mem_normalizer_iff.mp hwN a).mp haL)
  have huL' : u ∈ L' := by
    have e1 : u = a' * (w * a' * w⁻¹)⁻¹ := by
      have h1 : w * a * w⁻¹ = a * a' * (w * a' * w⁻¹)⁻¹ := by
        rw [← hwb]
        group
      rw [hu, h1]
      group
    rw [e1]
    exact L'.mul_mem ha' (L'.inv_mem ((Subgroup.mem_normalizer_iff.mp hwN' a').mp ha'))
  have hrw : rhoK L ⟨w, hwN⟩ (QuotientGroup.mk ⟨a, haL⟩) =
      QuotientGroup.mk ⟨a, haL⟩ * QuotientGroup.mk ⟨u, huL⟩ := by
    rw [rhoK_mk, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show w * a * w⁻¹ = a * u
    rw [hu]
    group
  have hc : e (QuotientGroup.mk ⟨u, huL⟩) = 1 ∨
      e (QuotientGroup.mk ⟨u, huL⟩) = QuaternionGroup.a 2 :=
    q8_center _ (fun y => by
      have := mk_comm_of_mem_trivialOnQuot huL (hL' huL') (e.symm y)
      simpa using congrArg e this)
  rw [hrw]
  rcases q8_mul_central _ _ (mul_self_ne_one_map e (mk_mul_self_ne_one haL ha2)) hc with h | h
  · left
    rw [← map_mul] at h
    exact e.injective h
  · right
    rw [← map_mul, ← map_inv] at h
    exact e.injective h

theorem eq_or_eq_inv_of_psiK_eq {L L' P : Subgroup G} (e : Kbar L ≃* Q8) (hP2 : IsPGroup 2 P)
    (hPL : P ≤ L) (hL' : L' ≤ trivialOnQuot L) {z x a a' w v : G} (hz : z ∉ oddCoreOf L)
    (hxP : x ∈ P) (hx2 : x * x = z) (haP : a ∈ P) (ha2 : a * a = z) (ha' : a' ∈ L')
    (hwN : w ∈ Subgroup.normalizer (L : Set G)) (hwN' : w ∈ Subgroup.normalizer (L' : Set G))
    (hwb : w * (a * a') * w⁻¹ = a * a') (hvN : v ∈ Subgroup.normalizer (L : Set G))
    (hvx : v * x * v⁻¹ = x) (hσ : psiK L ⟨w, hwN⟩ = psiK L ⟨v, hvN⟩)
    (hσ1 : psiK L ⟨v, hvN⟩ ≠ 1) (hσ2 : psiK L ⟨v, hvN⟩ * psiK L ⟨v, hvN⟩ = 1) :
    a = x ∨ a = x⁻¹ := by
  have hx2' : x * x ∉ oddCoreOf L := by rw [hx2]; exact hz
  have ha2' : a * a ∉ oddCoreOf L := by rw [ha2]; exact hz
  let Hx : Idx2 (Kbar L) := ⟨Subgroup.zpowers (QuotientGroup.mk ⟨x, hPL hxP⟩),
    card_eq_two_mul_zpowers e (mk_mul_self_ne_one (hPL hxP) hx2')⟩
  let Ha : Idx2 (Kbar L) := ⟨Subgroup.zpowers (QuotientGroup.mk ⟨a, hPL haP⟩),
    card_eq_two_mul_zpowers e (mk_mul_self_ne_one (hPL haP) ha2')⟩
  have hfx : psiK L ⟨v, hvN⟩ Hx = Hx := by
    rw [psiK_apply]
    refine idx2_act_zpowers _ (Or.inl ?_) Hx rfl
    rw [rhoK_mk]
    congr 1
    exact Subtype.ext hvx
  have hfa : psiK L ⟨v, hvN⟩ Ha = Ha := by
    rw [← hσ, psiK_apply]
    exact idx2_act_zpowers _ (rhoK_mk_eq_or_eq_inv e hL' (hPL haP) ha2' ha' hwN hwN' hwb) Ha rfl
  have hHax : Ha = Hx := eq_of_fixed_of_invol (card_idx2_of_equiv_q8 e) _ hσ1 hσ2 hfa hfx
  have hmem : (QuotientGroup.mk ⟨a, hPL haP⟩ : Kbar L) ∈
      Subgroup.zpowers (QuotientGroup.mk ⟨x, hPL hxP⟩ : Kbar L) := by
    have h1 : (QuotientGroup.mk ⟨a, hPL haP⟩ : Kbar L) ∈ Ha.1 := Subgroup.mem_zpowers _
    rw [hHax] at h1
    exact h1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine eq_or_eq_inv_of_mk_comm e hP2 hPL hxP haP hx2' ha2' ?_
  rw [← hn]
  exact (Commute.self_zpow _ n).eq

theorem conj_eq_inv_of_not_innerOn {L P W : Subgroup G} (e : Kbar L ≃* Q8) (hP2 : IsPGroup 2 P)
    (hPL : P ≤ L) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {s x : G}
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G)) (hs2 : s * s = 1) (hxP : x ∈ P) (hxW : x ∈ W)
    (hx2 : x * x ∉ oddCoreOf L) (hout : ¬ InnerOn L s) : s * x * s⁻¹ = x⁻¹ := by
  have hyP : s * x * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hsP x).mp hxP
  have hyW : s * x * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hsW x).mp hxW
  have hy2 : (s * x * s⁻¹) * (s * x * s⁻¹) ∉ oddCoreOf L := by
    intro h
    apply hx2
    have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hsN) h
    have e1 : s⁻¹ * ((s * x * s⁻¹) * (s * x * s⁻¹)) * s⁻¹⁻¹ = x * x := by group
    rwa [e1] at h1
  have hcomm : (QuotientGroup.mk ⟨x, hPL hxP⟩ : Kbar L) *
      QuotientGroup.mk ⟨s * x * s⁻¹, hPL hyP⟩ =
      QuotientGroup.mk ⟨s * x * s⁻¹, hPL hyP⟩ * QuotientGroup.mk ⟨x, hPL hxP⟩ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg (fun y : ↥L => (QuotientGroup.mk y : Kbar L)) (Subtype.ext (hWc _ hxW _ hyW))
  rcases eq_or_eq_inv_of_mk_comm e hP2 hPL hxP hyP hx2 hy2 hcomm with h | h
  · exfalso
    apply hout
    refine innerOn_of_invol_comm e hsN hs2 (hPL hxP) hx2 ?_
    calc s * x = (s * x * s⁻¹) * s := by group
      _ = x * s := by rw [h]
  · exact h

end Generic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
