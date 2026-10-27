module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement Pointwise

@[expose] def S267Conc268 (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S : Subgroup Ω) : Prop :=
  ∃ B E D : Subgroup Ω, IsElemAbelian p B ∧ Nat.card B = p ^ 4 ∧ E ≤ B ∧ Nat.card E = p ^ 3 ∧
    D ≤ E ∧ Nat.card D = p ^ 2 ∧
    (∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω)) ∧
    (∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ D ≤ Subgroup.normalizer (U : Set Ω) ∧
      GLAPLayer p (S ⊓ Subgroup.centralizer (D : Set Ω)) ≤ Subgroup.normalizer (U : Set Ω)) ∧
    GLAPComponent p (S ⊓ Subgroup.centralizer (D : Set Ω))
      (GLAPLayer p (S ⊓ Subgroup.centralizer (D : Set Ω))) ∧
    B ≤ Subgroup.normalizer
      ((GLAPLayer p (S ⊓ Subgroup.centralizer (D : Set Ω)) : Subgroup Ω) : Set Ω) ∧
    (∀ b ∈ B, CentMod p (GLAPLayer p (S ⊓ Subgroup.centralizer (D : Set Ω))) b ↔ b ∈ D) ∧
    GLAPLayer p (GLAPLayer p (S ⊓ Subgroup.centralizer (D : Set Ω)) ⊓
      Subgroup.centralizer (E : Set Ω)) ≠ ⊥

section Helpers

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem mem_centModSubgroup_of_commute {p : ℕ} {J : Subgroup Ω} {c : Ω}
    (hN : c ∈ Subgroup.normalizer (J : Set Ω)) (h : ∀ l ∈ J, l * c = c * l) :
    c ∈ centModSubgroup p J := by
  refine ⟨hN, fun l hl => ?_⟩
  have : ⁅l, c⁆ = 1 := by
    rw [commutatorElement_def, h l hl]; group
  rw [this]
  exact Subgroup.one_mem _

theorem card_sup_zpowers_of_comm {p : ℕ} (hp : p.Prime) {E : Subgroup Ω} {x : Ω} (hx : x ^ p = 1)
    (hx1 : x ≠ 1) (hxE : x ∉ E) (hc : ∀ e ∈ E, e * x = x * e) :
    Nat.card (E ⊔ Subgroup.zpowers x : Subgroup Ω) = Nat.card E * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.HardMathSupport.Solomon.Coordinator.i1020_card_sup_zpowers hp (orderOf_eq_prime hx hx1) hxE hc

theorem isElemAbelian_sup_zpowers {p : ℕ} {E : Subgroup Ω} {x : Ω} (hE : IsElemAbelian p E)
    (hx : x ^ p = 1) (hc : ∀ e ∈ E, e * x = x * e) : IsElemAbelian p (E ⊔ Subgroup.zpowers x) :=
  CFSG.HardMathSupport.Solomon.Coordinator.i1020_isElemAbelian_sup hE
    (CFSG.HardMathSupport.Solomon.Coordinator.i1020_isElemAbelian_zpowers hx) (by
    intro e he y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (show Commute e x from hc e he) k).eq)


theorem exists_mul_of_comm_sup {H K : Subgroup Ω} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : Ω}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hN : H ≤ Subgroup.normalizer (K : Set Ω) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : h * y * h⁻¹ = y := by rw [hc h hh y hy]; group
      rwa [this]
    · intro hy
      have h1 : h⁻¹ * (h * y * h⁻¹) = (h * y * h⁻¹) * h⁻¹ := hc h⁻¹ (H.inv_mem hh) _ hy
      have h2 : y = h * y * h⁻¹ := by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = (h * y * h⁻¹) * h⁻¹ * h := by rw [h1]
          _ = h * y * h⁻¹ := by group
      rwa [← h2] at hy
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K hN
  have hx' : x ∈ (H : Set Ω) * (K : Set Ω) := by rw [← this]; exact hx
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨h, hh, k, hk, rfl⟩

theorem mem_zpowers_of_mem_zpowers {p : ℕ} (hp : p.Prime) {a y : Ω} (ha : a ^ p = 1) (ha1 : a ≠ 1)
    (hy : y ∈ Subgroup.zpowers a) (hy1 : y ≠ 1) : a ∈ Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hya : y ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hoy : orderOf y = p := orderOf_eq_prime hya hy1
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hy
  have hcard : Nat.card (Subgroup.zpowers a) ≤ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hoy]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm ▸ Subgroup.mem_zpowers a

end Helpers

section Z1

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem mem_normalizer_zpowers_of_comm {d u : Ω} (h : d * u = u * d) :
    d ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup Ω) : Set Ω) := by
  apply Subgroup.centralizer_le_normalizer _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((Commute.zpow_left (show Commute u d from h.symm) k)).eq

theorem conc268_of_Z1 (hZ1 : S267FactZ1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : TauCeti.PrimePower)
    (hQ2 : Q.p ≠ 2) (hQp : Q.p ≠ p) (S A : Subgroup Ω)
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSc : Subgroup.center ↥S = ⊥)
    (hcat : catalogIs ↥S (onLie fun d => d = .A 2 Q) ∨ catalogIs ↥S (onLie fun d => d = .twistedA 2 Q))
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 4) (hcyc : CycModSylow p S) :
    S267Conc268 p S := by
  obtain ⟨hA0, a, haA, haS, R, hRS, hRel, hRc, hRa, r, hrR, hr1, hJc, hJn, hcm, hlay,
    ⟨T, hTS, hT0, hT2, hTn⟩, ⟨u, huS, hu1, hu2, hur, huJ⟩⟩ :=
    hZ1 p Q hp hp2 hQ2 hQp Ω S A hSn hSq hSc hcat hA hAc hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  set CS : Subgroup Ω := Subgroup.centralizer (S : Set Ω) with hCS
  set A0 : Subgroup Ω := A ⊓ CS with hA0def
  set J : Subgroup Ω := GLAPLayer p (S ⊓ Subgroup.centralizer ({r} : Set Ω)) with hJdef
  have hA0A : A0 ≤ A := inf_le_left
  have hA0CS : A0 ≤ CS := inf_le_right
  have hA0S : ∀ c ∈ A0, ∀ s ∈ S, c * s = s * c := fun c hc s hs =>
    (Subgroup.mem_centralizer_iff.1 (hA0CS hc) s hs).symm
  have hA0el : IsElemAbelian p A0 := isElemAbelian_mono hA hA0A
  have ha1 : a ≠ 1 := by
    intro h; apply haS; rw [h]; exact Subgroup.one_mem _
  have hap : a ^ p = 1 := hA.2 a haA
  have haA0 : a ∉ A0 := fun h => haS (Subgroup.mem_sup_right (hA0CS h))
  have hacomm : ∀ c ∈ A0, c * a = a * c := fun c hc => isElemAbelian_commute hA (hA0A hc) haA
  have hrS : r ∈ S := hRS hrR
  have hrp : r ^ p = 1 := hRel.2 r hrR
  have hSbot : ∀ x ∈ A0, x ∈ S → x = 1 := by
    intro x hx hxS
    have : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by
        have := Subgroup.mem_centralizer_iff.1 (hA0CS hx) g g.2
        simpa using this)
    rw [hSc, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hPcard : Nat.card (A0 ⊔ Subgroup.zpowers a : Subgroup Ω) = p ^ 2 := by
    rw [card_sup_zpowers_of_comm hp hap ha1 haA0 hacomm, hA0]; ring
  have hPel : IsElemAbelian p (A0 ⊔ Subgroup.zpowers a) := isElemAbelian_sup_zpowers hA0el hap hacomm
  have hPR : ∀ x ∈ A0 ⊔ Subgroup.zpowers a, ∀ s ∈ R, x * s = s * x := by
    intro x hx s hs
    have hle : A0 ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({s} : Set Ω) := by
      refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hA0S c hc s (hRS hs))
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hRa s hs)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hPRbot : (A0 ⊔ Subgroup.zpowers a) ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxR⟩
    obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_comm_sup (fun c hc y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (show Commute c a from hacomm c hc) k).eq) hxP
    have hyS : y ∈ S ⊔ CS := by
      have h1 : c⁻¹ * (c * y) ∈ S ⊔ CS :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right (CS.inv_mem (hA0CS hc)))
          (Subgroup.mem_sup_left (hRS hxR))
      simpa using h1
    by_cases hy1 : y = 1
    · rw [hy1, mul_one] at hxR ⊢
      exact (Subgroup.mem_bot).2 (hSbot c hc (hRS hxR))
    · exfalso
      exact haS (by
        have := mem_zpowers_of_mem_zpowers hp hap ha1 hy hy1
        exact (Subgroup.zpowers_le.2 hyS) this)
  have hRcP : R ≤ Subgroup.centralizer ((A0 ⊔ Subgroup.zpowers a : Subgroup Ω) : Set Ω) := fun s hs =>
    Subgroup.mem_centralizer_iff.2 fun x hx => hPR x hx s hs
  have hRnP : R ≤ Subgroup.normalizer ((A0 ⊔ Subgroup.zpowers a : Subgroup Ω) : Set Ω) :=
    hRcP.trans (Subgroup.centralizer_le_normalizer _)
  have hBcard : Nat.card ((A0 ⊔ Subgroup.zpowers a) ⊔ R : Subgroup Ω) = p ^ 4 := by
    have := card_sup_mul_card_inf_of_le_normalizer hRnP
    rw [hPRbot, Subgroup.card_bot, mul_one, hPcard, hRc] at this
    rw [this]; ring
  have hBel : IsElemAbelian p ((A0 ⊔ Subgroup.zpowers a) ⊔ R) :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_isElemAbelian_sup hPel hRel hPR
  have hrA0 : r ∉ A0 := fun h => hr1 (hSbot r h hrS)
  have hrcomm : ∀ c ∈ A0, c * r = r * c := fun c hc => hA0S c hc r hrS
  have hDcard : Nat.card (A0 ⊔ Subgroup.zpowers r : Subgroup Ω) = p ^ 2 := by
    rw [card_sup_zpowers_of_comm hp hrp hr1 hrA0 hrcomm, hA0]; ring
  have hDSCS : (A0 ⊔ Subgroup.zpowers r : Subgroup Ω) ≤ S ⊔ CS :=
    sup_le (hA0CS.trans le_sup_right) (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left hrS))
  have haD : a ∉ (A0 ⊔ Subgroup.zpowers r : Subgroup Ω) := fun h => haS (hDSCS h)
  have hDa : ∀ d ∈ (A0 ⊔ Subgroup.zpowers r : Subgroup Ω), d * a = a * d := by
    intro d hd
    have hle : (A0 ⊔ Subgroup.zpowers r : Subgroup Ω) ≤ Subgroup.centralizer ({a} : Set Ω) := by
      refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hacomm c hc)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hRa r hrR).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
  have hEcard : Nat.card ((A0 ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers a : Subgroup Ω) = p ^ 3 := by
    rw [card_sup_zpowers_of_comm hp hap ha1 haD hDa, hDcard]; ring
  have hEB : (A0 ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers a ≤ (A0 ⊔ Subgroup.zpowers a) ⊔ R := by
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) (le_sup_right.trans le_sup_left)
    exact (Subgroup.zpowers_le.2 hrR).trans le_sup_right
  have hSD : S ⊓ Subgroup.centralizer ((A0 ⊔ Subgroup.zpowers r : Subgroup Ω) : Set Ω) =
      S ⊓ Subgroup.centralizer ({r} : Set Ω) := by
    ext x
    constructor
    · rintro ⟨hxS, hxC⟩
      refine ⟨hxS, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hxC r (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))).symm
    · rintro ⟨hxS, hxr⟩
      refine ⟨hxS, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
      have hle : (A0 ⊔ Subgroup.zpowers r : Subgroup Ω) ≤ Subgroup.centralizer ({x} : Set Ω) := by
        refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hA0S c hc x hxS)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxr).symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
  have hJle : J ≤ S ⊓ Subgroup.centralizer ({r} : Set Ω) := by
    have : J ≤ S ⊓ Subgroup.centralizer ({r} : Set Ω) := hJdef ▸ hJc.1
    exact this
  have hJS : ∀ j ∈ J, j ∈ S := fun j hj => (hJle hj).1
  have hJr : ∀ j ∈ J, j * r = r * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJle hj).2
  have hJnorm : ∀ c ∈ A0, c ∈ Subgroup.normalizer (J : Set Ω) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun j hj =>
      (hA0S c hc j (hJS j hj)).symm)
  have hA0M : A0 ≤ centModSubgroup p J := fun c hc =>
    mem_centModSubgroup_of_commute (hJnorm c hc) fun j hj => (hA0S c hc j (hJS j hj)).symm
  have hrM : r ∈ centModSubgroup p J :=
    mem_centModSubgroup_of_commute (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun j hj => (hJr j hj))) fun j hj => hJr j hj
  refine ⟨(A0 ⊔ Subgroup.zpowers a) ⊔ R, (A0 ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers a,
    A0 ⊔ Subgroup.zpowers r, hBel, hBcard, hEB, hEcard, le_sup_left, hDcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨T, hT0, hT2, sup_le (sup_le ?_ ?_) ?_⟩
    · intro c hc
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht =>
        (hA0S c hc t (hTS ht)).symm)
    · exact le_sup_left.trans hTn
    · exact le_sup_right.trans hTn
  ·
    refine ⟨Subgroup.zpowers u, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hu1 (Subgroup.zpowers_eq_bot.1 h)
    · exact isPGroup_of_isElemAbelian (CFSG.HardMathSupport.Solomon.Coordinator.i1020_isElemAbelian_zpowers hu2)
    · refine sup_le (fun c hc => mem_normalizer_zpowers_of_comm (hA0S c hc u huS))
        (Subgroup.zpowers_le.2 (mem_normalizer_zpowers_of_comm hur.symm))
    · rw [hSD]
      exact fun j hj => mem_normalizer_zpowers_of_comm (huJ j hj)
  · rw [hSD]; exact hJc
  · rw [hSD]
    exact sup_le (sup_le (fun c hc => hJnorm c hc) (le_sup_left.trans hJn)) (le_sup_right.trans hJn)
  · rw [hSD]
    intro b hb
    rw [centMod_iff]
    constructor
    · intro hbM
      obtain ⟨x, hx, s, hs, rfl⟩ := exists_mul_of_comm_sup hPR hb
      obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_comm_sup (fun c hc y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact (Commute.zpow_right (show Commute c a from hacomm c hc) k).eq) hx
      have hb₁ : y * s ∈ centModSubgroup p J := by
        have := (centModSubgroup p J).mul_mem ((centModSubgroup p J).inv_mem (hA0M hc)) hbM
        simpa [mul_assoc] using this
      have hb₁' : y * s ∈ Subgroup.zpowers a ⊔ R :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hs)
      have hr' := hcm (y * s) hb₁' (centMod_iff.2 hb₁)
      have e : c * y * s = c * (y * s) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hr')
    · intro hbD
      have : (A0 ⊔ Subgroup.zpowers r : Subgroup Ω) ≤ centModSubgroup p J :=
        sup_le hA0M (Subgroup.zpowers_le.2 hrM)
      exact this hbD
  · rw [hSD]
    have hE : J ⊓ Subgroup.centralizer (((A0 ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers a : Subgroup Ω) :
        Set Ω) = J ⊓ Subgroup.centralizer ({a} : Set Ω) := by
      ext x
      constructor
      · rintro ⟨hxJ, hxC⟩
        refine ⟨hxJ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        exact (Subgroup.mem_centralizer_iff.1 hxC a
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))).symm
      · rintro ⟨hxJ, hxa⟩
        refine ⟨hxJ, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
        have hle : ((A0 ⊔ Subgroup.zpowers r) ⊔ Subgroup.zpowers a : Subgroup Ω) ≤
            Subgroup.centralizer ({x} : Set Ω) := by
          refine sup_le (sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)) (Subgroup.zpowers_le.2 ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hA0S c hc x (hJS x hxJ))
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hJr x hxJ).symm
          · exact Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_singleton_iff.1 hxa).symm
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
    rw [hE]
    exact hlay

end Z1

section Z3

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem conc268_of_Z3 (hZ3 : S267FactZ3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : TauCeti.PrimePower)
    (hQ2 : Q.p ≠ 2) (hQp : Q.p ≠ p) (S A : Subgroup Ω)
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : Subgroup.center ↥S ≠ ⊥)
    (hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) (onLie fun d => d = .A 2 Q) ∨
      catalogIs (↥S ⧸ Subgroup.center ↥S) (onLie fun d => d = .twistedA 2 Q))
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 4) (hcyc : CycModSylow p S) :
    S267Conc268 p S := by
  obtain ⟨hA0, b, hbA, hbC, hJc, hJn, hcm, ⟨a, haA, haD, hlay⟩, ⟨T, hTS, hT0, hT2, hTn⟩,
    ⟨u, huS, hu1, hu2, hub, huJ⟩⟩ :=
    hZ3 p Q hp hp2 hQ2 hQp Ω S A hSn hSq hSp hSc hcat hA hAc hcyc
  haveI : Fact p.Prime := ⟨hp⟩
  set CS : Subgroup Ω := Subgroup.centralizer (S : Set Ω) with hCS
  set A0 : Subgroup Ω := A ⊓ CS with hA0def
  set J : Subgroup Ω := GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) with hJdef
  have hA0A : A0 ≤ A := inf_le_left
  have hA0CS : A0 ≤ CS := inf_le_right
  have hA0S : ∀ c ∈ A0, ∀ s ∈ S, c * s = s * c := fun c hc s hs =>
    (Subgroup.mem_centralizer_iff.1 (hA0CS hc) s hs).symm
  have hA0el : IsElemAbelian p A0 := isElemAbelian_mono hA hA0A
  have hb1 : b ≠ 1 := by
    intro h; apply hbC; rw [h]; exact Subgroup.one_mem _
  have hbp : b ^ p = 1 := hA.2 b hbA
  have hbA0 : b ∉ A0 := fun h => hbC (hA0CS h)
  have hbcomm : ∀ c ∈ A0, c * b = b * c := fun c hc => isElemAbelian_commute hA (hA0A hc) hbA
  have hDcard : Nat.card (A0 ⊔ Subgroup.zpowers b : Subgroup Ω) = p ^ 2 := by
    rw [card_sup_zpowers_of_comm hp hbp hb1 hbA0 hbcomm, hA0]; ring
  have haD' : a ∉ (A0 ⊔ Subgroup.zpowers b : Subgroup Ω) := by rw [sup_comm]; exact haD
  have hDA : (A0 ⊔ Subgroup.zpowers b : Subgroup Ω) ≤ A :=
    sup_le hA0A (Subgroup.zpowers_le.2 hbA)
  have ha1 : a ≠ 1 := by
    intro h; apply haD'; rw [h]; exact Subgroup.one_mem _
  have hap : a ^ p = 1 := hA.2 a haA
  have hDa : ∀ d ∈ (A0 ⊔ Subgroup.zpowers b : Subgroup Ω), d * a = a * d := fun d hd =>
    isElemAbelian_commute hA (hDA hd) haA
  have hEcard : Nat.card ((A0 ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers a : Subgroup Ω) = p ^ 3 := by
    rw [card_sup_zpowers_of_comm hp hap ha1 haD' hDa, hDcard]; ring
  have hEA : (A0 ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers a ≤ A :=
    sup_le hDA (Subgroup.zpowers_le.2 haA)
  have hSD : S ⊓ Subgroup.centralizer ((A0 ⊔ Subgroup.zpowers b : Subgroup Ω) : Set Ω) =
      S ⊓ Subgroup.centralizer ({b} : Set Ω) := by
    ext x
    constructor
    · rintro ⟨hxS, hxC⟩
      refine ⟨hxS, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hxC b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))).symm
    · rintro ⟨hxS, hxb⟩
      refine ⟨hxS, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
      have hle : (A0 ⊔ Subgroup.zpowers b : Subgroup Ω) ≤ Subgroup.centralizer ({x} : Set Ω) := by
        refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hA0S c hc x hxS)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxb).symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
  have hJle : J ≤ S ⊓ Subgroup.centralizer ({b} : Set Ω) := hJdef ▸ hJc.1
  have hJS : ∀ j ∈ J, j ∈ S := fun j hj => (hJle hj).1
  have hJb : ∀ j ∈ J, j * b = b * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJle hj).2
  have hJnorm : ∀ c ∈ A0, c ∈ Subgroup.normalizer (J : Set Ω) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun j hj =>
      (hA0S c hc j (hJS j hj)).symm)
  have hA0M : A0 ≤ centModSubgroup p J := fun c hc =>
    mem_centModSubgroup_of_commute (hJnorm c hc) fun j hj => (hA0S c hc j (hJS j hj)).symm
  have hbM : b ∈ centModSubgroup p J :=
    mem_centModSubgroup_of_commute (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun j hj => (hJb j hj))) fun j hj => hJb j hj
  refine ⟨A, (A0 ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers a, A0 ⊔ Subgroup.zpowers b, hA, hAc, hEA,
    hEcard, le_sup_left, hDcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨T, hT0, hT2, hTn⟩
  · refine ⟨Subgroup.zpowers u, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hu1 (Subgroup.zpowers_eq_bot.1 h)
    · exact isPGroup_of_isElemAbelian (CFSG.HardMathSupport.Solomon.Coordinator.i1020_isElemAbelian_zpowers hu2)
    · exact sup_le (fun c hc => mem_normalizer_zpowers_of_comm (hA0S c hc u huS))
        (Subgroup.zpowers_le.2 (mem_normalizer_zpowers_of_comm hub.symm))
    · rw [hSD]
      exact fun j hj => mem_normalizer_zpowers_of_comm (huJ j hj)
  · rw [hSD]; exact hJc
  · rw [hSD]; exact hJn
  · rw [hSD]
    intro x hx
    rw [centMod_iff]
    constructor
    · intro hxM
      have := hcm x hx (centMod_iff.2 hxM)
      rwa [sup_comm] at this
    · intro hxD
      have : (A0 ⊔ Subgroup.zpowers b : Subgroup Ω) ≤ centModSubgroup p J :=
        sup_le hA0M (Subgroup.zpowers_le.2 hbM)
      exact this hxD
  · rw [hSD]
    have hE : J ⊓ Subgroup.centralizer (((A0 ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers a : Subgroup Ω) :
        Set Ω) = J ⊓ Subgroup.centralizer ({a} : Set Ω) := by
      ext x
      constructor
      · rintro ⟨hxJ, hxC⟩
        refine ⟨hxJ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        exact (Subgroup.mem_centralizer_iff.1 hxC a
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))).symm
      · rintro ⟨hxJ, hxa⟩
        refine ⟨hxJ, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
        have hle : ((A0 ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers a : Subgroup Ω) ≤
            Subgroup.centralizer ({x} : Set Ω) := by
          refine sup_le (sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_)) (Subgroup.zpowers_le.2 ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hA0S c hc x (hJS x hxJ))
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hJb x hxJ).symm
          · exact Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_singleton_iff.1 hxa).symm
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hd)
    rw [hE]
    exact hlay

end Z3

end CFSG.LocalAnalysis.GLTheoremA.S267

end
