module

public import CFSG.ClassicalInvolution.Q3.Q3T6BOddFix
public import CFSG.ClassicalInvolution.Q3.Q3TNGen
public import CFSG.ClassicalInvolution.Q3.Q3T6YOddCl
public import CFSG.ClassicalInvolution.Q3.Q3T6YTwinP
public import CFSG.ClassicalInvolution.Q3.Q3T6BFixSub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

@[expose] def swapFix (X : Subgroup F) (y : F) : Subgroup F :=
  twinProd (Subgroup.zpowers y) X ⊓ Subgroup.centralizer ({y} : Set F)

@[expose] def deltaStar (X : Subgroup F) (y : F) : Subgroup F := oddClosure (swapFix X y)

variable {X : Subgroup F} {x y : F}

theorem isSubnormal_swapFix (h : Swap X x y) :
    IsSubnormal (swapFix X y)
      (Subgroup.centralizer ({x} : Set F) ⊓ Subgroup.centralizer ({y} : Set F)) := by
  have hzK : ∀ k ∈ Subgroup.zpowers y, k * x = x * k := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact Commute.zpow_left (show Commute y x from h.comm) n
  have hEsub : IsSubnormal (twinProd (Subgroup.zpowers y) X)
      (Subgroup.centralizer ({x} : Set F)) :=
    isSubnormal_twinProd h.member.subnormal hzK
  have hyE : y ∈ Subgroup.normalizer ((twinProd (Subgroup.zpowers y) X : Subgroup F) : Set F) :=
    K_le_normalizer_twinProd (Subgroup.mem_zpowers y)
  have hyCx : y ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({x} : Set F) : Subgroup F) : Set F) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr h.comm)
  exact isSubnormal_inf_centralizer_of_normalizes hEsub hyE hyCx

theorem isSubnormal_deltaStar (h : Swap X x y) :
    IsSubnormal (deltaStar X y)
      (Subgroup.centralizer ({x} : Set F) ⊓ Subgroup.centralizer ({y} : Set F)) :=
  isSubnormal_oddClosure (isSubnormal_swapFix h)

theorem exists_diag_eq_mul (h : Swap X x y) {a : F} (ha : a ∈ X) :
    ∃ w ∈ deltaStar X y, ∃ o ∈ oddCoreOf X, a * (y * a * y⁻¹) = w * o := by
  classical
  have hX := h.member
  have hX' : Mem3 (conjSub y X) x := h.twin
  obtain ⟨hX'N, -, hcomm⟩ := hX.twin_facts hX' h.moves.symm
  set O : Subgroup F := oddCoreOf X with hOdef
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hOX : O ≤ X := oddCoreOf_le_self X
  have hXO : ∀ a ∈ X, ∀ n ∈ O, a * n * a⁻¹ ∈ O := fun a ha n hn =>
    (Subgroup.mem_normalizer_iff.mp
      (AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer ha)) n).mp hn
  have hX'O : ∀ a ∈ conjSub y X, a ∈ Subgroup.normalizer (O : Set F) := fun a ha =>
    AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (hX'N ha)
  have hyO : ∀ n ∈ O, y * n * y⁻¹ ∈ O := by
    have hyC : y ∈ Subgroup.centralizer ({x} : Set F) :=
      Subgroup.mem_centralizer_singleton_iff.mpr h.comm
    have hOeq : O = Balance.oddCoreIn (Subgroup.centralizer ({x} : Set F)) :=
      Uniform.oddCoreIn_eq_of_intrinsic hX.member (hX.intrinsic solvableType_three)
    intro n hn
    rw [hOeq] at hn ⊢
    exact Balance.conj_mem_oddCoreIn hyC hn
  have hcO : ∀ a ∈ X, ∀ b ∈ conjSub y X, ⁅a, b⁆ ∈ O := fun a ha b hb =>
    (hcomm (Subgroup.commutator_mem_commutator ha hb)).1
  have hy2 : y * y = 1 := h.sq
  have hyi : y⁻¹ = y := h.inv_eq
  have hyyg : ∀ g : F, y * (y * g * y⁻¹) * y⁻¹ = g := fun g => by
    rw [hyi]
    calc y * (y * g * y) * y = (y * y) * g * (y * y) := by group
      _ = g := by rw [hy2]; group
  set P : Subgroup F := Subgroup.normalizer (O : Set F) with hPdef
  set E : Subgroup F := twinProd (Subgroup.zpowers y) X with hEdef
  have hzK : ∀ k ∈ Subgroup.zpowers y, k * x = x * k := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact Commute.zpow_left (show Commute y x from h.comm) n
  have hEC : E ≤ Subgroup.centralizer ({x} : Set F) := twinProd_le_centralizer' hX hzK
  have hXE : X ≤ E := le_twinProd ⟨1, Subgroup.one_mem _, (conjSub_one X).symm⟩
  have hX'E : conjSub y X ≤ E := le_twinProd ⟨y, Subgroup.mem_zpowers y, rfl⟩
  let M : Set F := {g | g ∈ P ∧ g ∈ E ∧ g * y = y * g ∧ Odd (orderOf g)}
  set W : Subgroup F := Subgroup.closure M with hWdef
  have hWP : W ≤ P := (Subgroup.closure_le _).mpr fun g hg => hg.1
  have hWE : W ≤ E := (Subgroup.closure_le _).mpr fun g hg => hg.2.1
  have hWoddGen : W ≤ deltaStar X y :=
    Subgroup.closure_mono fun g hg =>
      ⟨⟨hg.2.1, Subgroup.mem_centralizer_singleton_iff.mpr hg.2.2.1⟩, hg.2.2.2⟩
  have hWO : ∀ w ∈ W, ∀ n ∈ O, w⁻¹ * n * w ∈ O := fun w hw n hn => by
    have := (Subgroup.mem_normalizer_iff.mp (P.inv_mem (hWP hw)) n).mp hn
    simpa using this
  let H : Subgroup F :=
    { carrier := {a | a ∈ X ∧ ∃ w ∈ W, ∃ o ∈ O, a * (y * a * y⁻¹) = w * o}
      one_mem' := ⟨X.one_mem, 1, W.one_mem, 1, O.one_mem, by group⟩
      mul_mem' := by
        rintro a b ⟨haX, w₁, hw₁, o₁, ho₁, e₁⟩ ⟨hbX, w₂, hw₂, o₂, ho₂, e₂⟩
        have hay : y * a * y⁻¹ ∈ conjSub y X := conj_mem_conjSub haX
        have hc : ⁅b, y * a * y⁻¹⁆ ∈ O := hcO b hbX _ hay
        have hc' : a * ⁅b, y * a * y⁻¹⁆ * a⁻¹ ∈ O := hXO a haX _ hc
        refine ⟨X.mul_mem haX hbX, w₁ * w₂, W.mul_mem hw₁ hw₂,
          (w₂⁻¹ * (w₁⁻¹ * (a * ⁅b, y * a * y⁻¹⁆ * a⁻¹) * w₁ * o₁) * w₂) * o₂, ?_, ?_⟩
        · exact O.mul_mem (hWO w₂ hw₂ _ (O.mul_mem (hWO w₁ hw₁ _ hc') ho₁)) ho₂
        · calc a * b * (y * (a * b) * y⁻¹)
              = (a * ⁅b, y * a * y⁻¹⁆ * a⁻¹) * (a * (y * a * y⁻¹)) * (b * (y * b * y⁻¹)) := by
                simp only [commutatorElement_def]
                group
            _ = (a * ⁅b, y * a * y⁻¹⁆ * a⁻¹) * (w₁ * o₁) * (w₂ * o₂) := by rw [e₁, e₂]
            _ = w₁ * w₂ * ((w₂⁻¹ * (w₁⁻¹ * (a * ⁅b, y * a * y⁻¹⁆ * a⁻¹) * w₁ * o₁) * w₂) * o₂) := by
                group
      inv_mem' := by
        rintro a ⟨haX, w₁, hw₁, o₁, ho₁, e₁⟩
        have hay : y * a * y⁻¹ ∈ conjSub y X := conj_mem_conjSub haX
        have hd : ⁅y * a * y⁻¹, a⁆ ∈ O := by
          rw [← commutatorElement_inv]
          exact O.inv_mem (hcO a haX _ hay)
        have hw₁inv : w₁ * o₁⁻¹ * w₁⁻¹ ∈ O := by
          have := hWO w₁⁻¹ (W.inv_mem hw₁) o₁⁻¹ (O.inv_mem ho₁)
          simpa using this
        refine ⟨X.inv_mem haX, w₁⁻¹, W.inv_mem hw₁, (w₁ * o₁⁻¹ * w₁⁻¹) * ⁅y * a * y⁻¹, a⁆⁻¹,
          O.mul_mem hw₁inv (O.inv_mem hd), ?_⟩
        calc a⁻¹ * (y * a⁻¹ * y⁻¹) = (y * a * y⁻¹ * a)⁻¹ := by group
          _ = (⁅y * a * y⁻¹, a⁆ * (a * (y * a * y⁻¹)))⁻¹ := by
              congr 1
              simp only [commutatorElement_def]
              group
          _ = (⁅y * a * y⁻¹, a⁆ * (w₁ * o₁))⁻¹ := by rw [e₁]
          _ = w₁⁻¹ * ((w₁ * o₁⁻¹ * w₁⁻¹) * ⁅y * a * y⁻¹, a⁆⁻¹) := by group }
  have hodd : ∀ s ∈ X, ∀ p k : ℕ, p.Prime → p ≠ 2 → s ^ p ^ k = 1 → s ∈ H := by
    intro s hsX p k hp hp2 hs
    have hsy : y * s * y⁻¹ ∈ conjSub y X := conj_mem_conjSub hsX
    have hsP : s ∈ P := AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer'
      (Subgroup.le_normalizer hsX)
    have hsyP : y * s * y⁻¹ ∈ P := hX'O _ hsy
    have hx0 : (s * (y * s * y⁻¹))⁻¹ * (y * (s * (y * s * y⁻¹)) * y⁻¹) ∈ O := by
      have h1 : y * (s * (y * s * y⁻¹)) * y⁻¹ = (y * s * y⁻¹) * s := by
        calc y * (s * (y * s * y⁻¹)) * y⁻¹ = (y * s * y⁻¹) * (y * (y * s * y⁻¹) * y⁻¹) := by
              group
          _ = (y * s * y⁻¹) * s := by rw [hyyg s]
      rw [h1]
      have h2 := hcO s⁻¹ (X.inv_mem hsX) (y * s * y⁻¹)⁻¹ ((conjSub y X).inv_mem hsy)
      have h3 : (s * (y * s * y⁻¹))⁻¹ * ((y * s * y⁻¹) * s) =
          ⁅s⁻¹, (y * s * y⁻¹)⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h3]
      exact O.inv_mem h2
    obtain ⟨n, hn, hfix⟩ := exists_fixed_mul_mem hy2 hOodd hyO hx0
    set σ : F := s * (y * s * y⁻¹) * n with hσdef
    have hnP : n ∈ P := Subgroup.le_normalizer hn
    have hσP : σ ∈ P := P.mul_mem (P.mul_mem hsP hsyP) hnP
    have hσy : σ * y = y * σ := by
      have h1 : y * σ * y⁻¹ = σ := hfix
      calc σ * y = (y * σ * y⁻¹) * y := by rw [h1]
        _ = y * σ := by group
    have hxs : s * x = x * s := hX.mul_comm_of_mem hsX
    have hxsy : (y * s * y⁻¹) * x = x * (y * s * y⁻¹) := hX'.mul_comm_of_mem hsy
    have hxn : n * x = x * n := hX.mul_comm_of_mem (hOX hn)
    have hσx : σ * x = x * σ := by
      calc σ * x = s * (y * s * y⁻¹) * (n * x) := by rw [hσdef]; group
        _ = s * (y * s * y⁻¹) * (x * n) := by rw [hxn]
        _ = s * ((y * s * y⁻¹) * x) * n := by group
        _ = s * (x * (y * s * y⁻¹)) * n := by rw [hxsy]
        _ = (s * x) * (y * s * y⁻¹) * n := by group
        _ = x * s * (y * s * y⁻¹) * n := by rw [hxs]
        _ = x * σ := by rw [hσdef]; group
    have hσpow : σ ^ p ^ k ∈ O := by
      have : (O.subgroupOf P).Normal := Subgroup.normal_in_normalizer
      let π : P →* P ⧸ O.subgroupOf P := QuotientGroup.mk' (O.subgroupOf P)
      have hπ : ∀ (g : F) (hg : g ∈ P), π ⟨g, hg⟩ = 1 ↔ g ∈ O := fun g hg => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hπσ : π ⟨σ, hσP⟩ = π ⟨s, hsP⟩ * π ⟨y * s * y⁻¹, hsyP⟩ := by
        have : (⟨σ, hσP⟩ : P) = ⟨s, hsP⟩ * ⟨y * s * y⁻¹, hsyP⟩ * ⟨n, hnP⟩ := rfl
        rw [this, map_mul, map_mul, (hπ n hnP).mpr hn, mul_one]
      have hcomm : Commute (π ⟨s, hsP⟩) (π ⟨y * s * y⁻¹, hsyP⟩) := by
        have h1 : ⁅(⟨s, hsP⟩ : P), (⟨y * s * y⁻¹, hsyP⟩ : P)⁆ ∈ O.subgroupOf P := by
          rw [Subgroup.mem_subgroupOf]
          exact hcO s hsX _ hsy
        have h2 : π ⁅(⟨s, hsP⟩ : P), (⟨y * s * y⁻¹, hsyP⟩ : P)⁆ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr h1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
        exact h2
      have hsm : (⟨s, hsP⟩ : P) ^ p ^ k = 1 := Subtype.ext (by simpa using hs)
      have hsym : (⟨y * s * y⁻¹, hsyP⟩ : P) ^ p ^ k = 1 := by
        refine Subtype.ext ?_
        show (y * s * y⁻¹) ^ p ^ k = 1
        rw [conj_pow, hs]
        group
      have h1 : (π ⟨σ, hσP⟩) ^ p ^ k = 1 := by
        rw [hπσ, hcomm.mul_pow, ← map_pow, ← map_pow, hsm, hsym, map_one, mul_one]
      have h2 : π (⟨σ, hσP⟩ ^ p ^ k) = 1 := by rw [map_pow]; exact h1
      exact (hπ (σ ^ p ^ k) (P.pow_mem hσP _)).mp h2
    have hσodd : Odd (orderOf σ) :=
      odd_orderOf_of_pow_mem hOodd (hp.odd_of_ne_two hp2 |>.pow) hσpow
    have hσE : σ ∈ E :=
      E.mul_mem (E.mul_mem (hXE hsX) (hX'E hsy)) (hXE (hOX hn))
    have hσM : σ ∈ M := ⟨hσP, hσE, hσy, hσodd⟩
    refine ⟨hsX, σ, Subgroup.subset_closure hσM, n⁻¹, O.inv_mem hn, ?_⟩
    rw [hσdef]
    group
  have hXH : X ≤ H :=
    Q3T.le_of_forall_oddPrimePow_mem (hX.member.toQ3 (by norm_num)) hodd
  obtain ⟨-, w, hw, o, ho, hqo⟩ := hXH ha
  exact ⟨w, hWoddGen hw, o, ho, hqo⟩

theorem diag_mem_deltaStar (h : Swap X x y) {q : F} (hq : q ∈ X)
    (hqc : q * (y * q * y⁻¹) = (y * q * y⁻¹) * q) : q * (y * q * y⁻¹) ∈ deltaStar X y := by
  obtain ⟨w, hw, o, ho, hqo⟩ := exists_diag_eq_mul h hq
  have hX := h.member
  have hOodd : Odd (Nat.card (oddCoreOf X)) := oddCoreOf_odd_natCard X
  have hOX : oddCoreOf X ≤ X := oddCoreOf_le_self X
  have hy2 : y * y = 1 := h.sq
  have hXE : X ≤ twinProd (Subgroup.zpowers y) X :=
    le_twinProd ⟨1, Subgroup.one_mem _, (conjSub_one X).symm⟩
  have hwy : w * y = y * w :=
    Subgroup.mem_centralizer_singleton_iff.mp (oddClosure_le _ hw).2
  have hqqy : (q * (y * q * y⁻¹)) * y = y * (q * (y * q * y⁻¹)) :=
    (diag_comm_y hy2 hqc).symm
  have hoeq : o = w⁻¹ * (q * (y * q * y⁻¹)) := by rw [hqo]; group
  have hoy : o * y = y * o := by
    rw [hoeq]
    calc w⁻¹ * (q * (y * q * y⁻¹)) * y = w⁻¹ * (y * (q * (y * q * y⁻¹))) := by
          rw [mul_assoc, hqqy]
      _ = (w⁻¹ * y) * (q * (y * q * y⁻¹)) := by group
      _ = (y * w⁻¹) * (q * (y * q * y⁻¹)) := by
          congr 1
          have := (Commute.inv_left (show Commute w y from hwy)).eq
          exact this
      _ = y * (w⁻¹ * (q * (y * q * y⁻¹))) := by group
  have hoodd : Odd (orderOf o) :=
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreOf X) ho)
  have hoE : o ∈ twinProd (Subgroup.zpowers y) X ⊓ Subgroup.centralizer ({y} : Set F) :=
    ⟨hXE (hOX ho), Subgroup.mem_centralizer_singleton_iff.mpr hoy⟩
  rw [hqo]
  exact (deltaStar X y).mul_mem hw (mem_oddClosure_of_odd hoE hoodd)

end CFSG.ClassicalInvolution.Q3.Q3T6Y
