module

public import Certificates.Data.Kernel.SporSch.RootPairZ
public import CFSG.Certificates.Kernel.SporSch.RootPairSound

public section

namespace CFSG.KS.SporSch.RPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.KS.SporSch.CAll
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
open CFSG.Sporadic.Schreier

theorem q8Out_spec {A B : Nat → Nat} {x y : Nat} (h : q8Out A B x y = true) :
    ∀ k < 8, y ≠ q8W A B k x := by
  unfold q8Out at h
  simp only [CIdx.strictB_eq] at h
  obtain ⟨c0, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨c1, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨c2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨c3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨c4, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨c5, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨c6, c7⟩ := (CIdx.bAnd_iff' _ _).1 h
  rw [bNot_iff, Bool.eq_false_iff] at c0 c1 c2 c3 c4 c5 c6 c7
  intro k hk e
  have e' : Nat.beq y (q8W A B k x) = true := beq_iff.2 e
  interval_cases k
  exacts [c0 e', c1 e', c2 e', c3 e', c4 e', c5 e', c6 e', c7 e']

section Chain

variable {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hQ : ChainCK n w PS PSI LR TR TRI kS kO nb BP S base D)
include hQ

theorem el_eq_of_eqAll {j : Nat} {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (hf : Acts n f g)
    (h : eqAllK n (elF n w (mask w) (n * w) nb LR TR j) f = true) : el n S base nb j = g := by
  unfold eqAllK at h
  refine Equiv.ext fun y => Fin.ext ?_
  rw [← acts_elF hQ j y, ← hf y]
  exact beq_iff.1 ((allN_iff.1 h) y y.isLt)

theorem twin_facts {N mm : Nat} {T QJ : Nat → Nat} {A B : Equiv.Perm (Fin n)}
    (hA : Acts n (pg w (mask w) (T (2 * mm))) A) (hB : Acts n (pg w (mask w) (T (2 * mm + 1))) B)
    (h : twinQK n w (mask w) (n * w) nb N LR TR T QJ mm = true) :
    ∀ k < 8, QJ (8 * mm + k) < N → el n S base nb (QJ (8 * mm + k)) = q8G A B k := by
  intro k hk hj
  unfold twinQK at h
  rw [CIdx.strictB_eq] at h
  have h1 := (allN_iff.1 h) k hk
  rw [CIdx.strictB_eq] at h1
  simp only [show Nat.blt (QJ (Nat.add (Nat.mul 8 mm) k)) N = true from blt_iff.2 hj] at h1
  exact el_eq_of_eqAll hQ (acts_q8W hA hB hk) h1

theorem subA_facts {N nx zj mm : Nat} {X XI QJ QA QW QP : Nat → Nat}
    {Xg : Nat → Equiv.Perm (Fin n)} (hN : ordK LR nb = N)
    (hX : ∀ t < nx, Orb.PRep n w (X t) (Xg t) ∧ Orb.PRep n w (XI t) (Xg t)⁻¹)
    (h : subAK n w (mask w) (n * w) BP nb N nx zj LR TR X XI QJ QA QW QP mm = true) :
    (∀ k < 8, QJ (8 * mm + k) < N) ∧ QJ (8 * mm + 1) = zj ∧
      (∀ k < 8, el n S base nb (QJ (8 * mm + k)) =
        q8G (el n S base nb (QJ (8 * mm + 2))) (el n S base nb (QJ (8 * mm + 4))) k) ∧
      el n S base nb (QJ (8 * mm + 4)) * el n S base nb (QJ (8 * mm + 4)) =
        el n S base nb (QJ (8 * mm + 1)) ∧
      el n S base nb (QJ (8 * mm + 2)) * el n S base nb (QJ (8 * mm + 4)) *
        el n S base nb (QJ (8 * mm + 2)) = el n S base nb (QJ (8 * mm + 4)) ∧
      (∀ a < 5, 1 ≤ QA (5 * mm + a) ∧ QA (5 * mm + a) < nx) ∧
      ∀ a < 5, ∀ b < 5, a < b → ∃ k < 8, ∀ k' < 8,
        (Xg (QA (5 * mm + b)))⁻¹ * Xg (QA (5 * mm + a)) * el n S base nb (QJ (8 * mm + k)) *
          (Xg (QA (5 * mm + a)))⁻¹ * Xg (QA (5 * mm + b)) ≠
            el n S base nb (QJ (8 * mm + k')) := by
  unfold subAK at h
  simp only [CIdx.strictB_eq, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨h2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h4, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h5, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h6, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h7, h8⟩ := (CIdx.bAnd_iff' _ _).1 h
  have hlt : ∀ k < 8, QJ (8 * mm + k) < N := fun k hk => blt_iff.1 ((allN_iff.1 h2) k hk)
  have hM : ∀ k < 8, el n S base nb (QJ (8 * mm + k)) ∈ Gen n S kO := fun k hk =>
    el_mem' hQ hN (hlt k hk)
  have hac := fun k => acts_elF hQ (QJ (8 * mm + k))
  set A := el n S base nb (QJ (8 * mm + 2))
  set B := el n S base nb (QJ (8 * mm + 4))
  have hAM := hM 2 (by norm_num)
  have hBM := hM 4 (by norm_num)
  have hq8M : ∀ k < 8, q8G A B k ∈ Gen n S kO := by
    intro k hk
    have m := fun x y => Subgroup.mul_mem (Gen n S kO) (x := x) (y := y)
    interval_cases k <;> simp only [q8G] <;> norm_num <;>
      first
        | exact Subgroup.one_mem _
        | exact hAM
        | exact hBM
        | exact m _ _ hAM hAM
        | exact m _ _ (m _ _ hAM hAM) hAM
        | exact m _ _ (m _ _ hAM hAM) hBM
        | exact m _ _ hAM hBM
        | exact m _ _ (m _ _ (m _ _ hAM hAM) hAM) hBM
  have hQA : ∀ a < 5, 1 ≤ QA (5 * mm + a) ∧ QA (5 * mm + a) < nx := by
    intro a ha
    obtain ⟨c1, c2⟩ := (CIdx.bAnd_iff' _ _).1 ((allN_iff.1 h7) a ha)
    exact ⟨ble_iff.1 c1, blt_iff.1 c2⟩
  refine ⟨hlt, beq_iff.1 h3, fun k hk => ?_, ?_, ?_, hQA, fun a ha b hb hab => ?_⟩
  · exact (eqB_iff_eq hQ (hac k) (acts_q8W (hac 2) (hac 4) hk) (hM k hk) (hq8M k hk)).1
      ((allN_iff.1 h4) k hk)
  · refine (eqB_iff_eq hQ (fun y => ?_) (hac 1) (Subgroup.mul_mem _ hBM hBM)
      (hM 1 (by norm_num))).1 h5
    rw [Equiv.Perm.mul_apply, hac 4 y, hac 4]
  · refine (eqB_iff_eq hQ (fun y => ?_) (hac 4) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hAM hBM)
      hAM) hBM).1 h6
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hac 2 y, hac 4, hac 2]
  · have g1 := (allN_iff.1 ((allN_iff.1 h8) a ha)) b hb
    simp only [show Nat.blt a b = true from blt_iff.2 hab] at g1
    obtain ⟨k1, k2⟩ := (CIdx.bAnd_iff' _ _).1 g1
    obtain ⟨kx, k2⟩ := (CIdx.bAnd_iff' _ _).1 k2
    have hta := (hQA a ha).2
    have htb := (hQA b hb).2
    generalize QA (5 * mm + a) = ta at k2 hta
    generalize QA (5 * mm + b) = tb at k2 htb
    obtain ⟨hXa, hXa'⟩ := hX ta hta
    obtain ⟨hXb, hXb'⟩ := hX tb htb
    refine ⟨_, blt_iff.1 k1, fun k' hk' e => ?_⟩
    have k3 := (allN_iff.1 k2) k' hk'
    rw [bNot_iff, Bool.eq_false_iff] at k3
    refine k3 (beq_iff.2 ?_)
    obtain ⟨y, hy⟩ : ∃ y : Fin n, (y : Nat) = QP (25 * mm + (5 * a + b)) :=
      ⟨⟨_, blt_iff.1 kx⟩, rfl⟩
    rw [← hy]
    have e' := congrArg (fun g : Equiv.Perm (Fin n) => (g y : Nat)) e
    simp only [Equiv.Perm.mul_apply] at e'
    rw [hXb y, hXa', hac, hXa, hXb', hac]
    exact e'

theorem pairQ_sound {N nr nq : Nat} {RL CT PQ QJ : Nat → Nat} (hN : ordK LR nb = N)
    (hRL : ∀ d < nr, RL d < N)
    (hpk : ∀ d < nr, pairQK n w (mask w) (n * w) BP nb LR TR RL CT PQ QJ nr nq d = true)
    {d e : Nat} (hd : d < nr) (he : e < nr) (hcd : CT d = 0) (hce : CT e = 0)
    (hxy : el n S base nb (RL d) * el n S base nb (RL e) * el n S base nb (RL d) =
      el n S base nb (RL e)) :
    PQ (d * nr + e) < nq ∧ (∃ k < 8, QJ (8 * PQ (d * nr + e) + k) = RL d) ∧
      ∃ k < 8, QJ (8 * PQ (d * nr + e) + k) = RL e := by
  have h := hpk d hd
  unfold pairQK at h
  rw [show Nat.beq (CT d) 0 = true from beq_iff.2 hcd] at h
  simp only [CIdx.strictB_eq] at h
  have h1 := (allN_iff.1 h) e he
  rw [show Nat.beq (CT e) 0 = true from beq_iff.2 hce] at h1
  have hA : Acts n (fun x => elF n w (mask w) (n * w) nb LR TR (RL d)
      (elF n w (mask w) (n * w) nb LR TR (RL e) (elF n w (mask w) (n * w) nb LR TR (RL d) x)))
      (el n S base nb (RL d) * el n S base nb (RL e) * el n S base nb (RL d)) := by
    intro y
    dsimp only
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, acts_elF hQ (RL d) y,
      acts_elF hQ (RL e), acts_elF hQ (RL d)]
  have hdM := el_mem' hQ hN (hRL d hd)
  have heM := el_mem' hQ hN (hRL e he)
  have hb := (eqB_iff_eq hQ hA (acts_elF hQ _) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hdM heM)
    hdM) heM).2 hxy
  simp only [hb, Nat.add_eq] at h1
  obtain ⟨b1, b⟩ := (CIdx.bAnd_iff' _ _).1 h1
  obtain ⟨b2, b3⟩ := (CIdx.bAnd_iff' _ _).1 b
  exact ⟨blt_iff.1 b1, inQ_iff.1 b2, inQ_iff.1 b3⟩

theorem rootT_acts {N nr : Nat} {RL RT CT IV : Nat → Nat} (hN : ordK LR nb = N)
    (hRL : ∀ d < nr, RL d < N)
    (hRT : ∀ d < nr, rootTK n w (mask w) (n * w) BP nb LR TR RL RT CT IV d = true) :
    ∀ d < nr, CT d = 0 → Acts n (pg w (mask w) (RT d)) (el n S base nb (RL d)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcd
  have h := hRT d hd
  unfold rootTK at h
  rw [show Nat.beq (CT d) 0 = true from beq_iff.2 hcd, CIdx.strictB_eq] at h
  cases hlt : Nat.blt (IV d) d
  · rw [hlt] at h
    unfold eqAllK at h
    intro y
    rw [← acts_elF hQ (RL d) y]
    exact (beq_iff.1 ((allN_iff.1 h) y y.isLt)).symm
  · rw [hlt] at h
    have hlt' := blt_iff.1 hlt
    obtain ⟨c1, c⟩ := (CIdx.bAnd_iff' _ _).1 h
    obtain ⟨c2, c3⟩ := (CIdx.bAnd_iff' _ _).1 c
    have hd' : IV d < nr := by omega
    have hg := ih (IV d) hlt' hd' (beq_iff.1 c1)
    set g := el n S base nb (RL (IV d))
    have hdM := el_mem' hQ hN (hRL d hd)
    have hgM := el_mem' hQ hN (hRL (IV d) hd')
    have hA : Acts n (fun x => elF n w (mask w) (n * w) nb LR TR (RL d)
        (pg w (mask w) (RT (IV d)) x)) (el n S base nb (RL d) * g) := by
      intro y
      dsimp only
      rw [Equiv.Perm.mul_apply, hg y, acts_elF hQ (RL d)]
    have e := (eqB_iff_eq hQ hA (g' := 1) (fun _ => rfl) (Subgroup.mul_mem _ hdM hgM)
      (Subgroup.one_mem _)).1 c3
    have e' : el n S base nb (RL d) = g⁻¹ := eq_inv_of_mul_eq_one_left e
    unfold eqAllK at c2
    intro y
    have hy := beq_iff.1 ((allN_iff.1 c2) (g⁻¹ y) (g⁻¹ y).isLt)
    dsimp only at hy
    rw [hg (g⁻¹ y), ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at hy
    rw [hy, e']

theorem pairR_sound {N nr nq w2 : Nat} {RL RT CT IV PR QJ : Nat → Nat} (hN : ordK LR nb = N)
    (hRL : ∀ d < nr, RL d < N)
    (hRT : ∀ d < nr, rootTK n w (mask w) (n * w) BP nb LR TR RL RT CT IV d = true)
    (hpk : ∀ d < nr, pairRK w (mask w) w2 (mask w2) BP nb RL RT CT PR QJ nr nq d = true)
    {d e : Nat} (hde : d < e) (he : e < nr) (hcd : CT d = 0) (hce : CT e = 0)
    (hxy : el n S base nb (RL d) * el n S base nb (RL e) * el n S base nb (RL d) =
      el n S base nb (RL e)) :
    ∃ mm, mm < nq ∧ (∃ k < 8, QJ (8 * mm + k) = RL d) ∧ ∃ k < 8, QJ (8 * mm + k) = RL e := by
  have hd : d < nr := by omega
  have hR := rootT_acts hQ hN hRL hRT
  have h := hpk d hd
  unfold pairRK at h
  rw [show Nat.beq (CT d) 0 = true from beq_iff.2 hcd] at h
  simp only [CIdx.strictB_eq] at h
  have h1 := (allN_iff.1 h) (e - Nat.succ d) (by change e - (d + 1) < nr - (d + 1); omega)
  have ee : Nat.add (Nat.succ d) (e - Nat.succ d) = e := by
    change d + 1 + (e - (d + 1)) = e
    omega
  rw [ee, show Nat.beq (CT e) 0 = true from beq_iff.2 hce] at h1
  have key : ∀ {a b : Bool}, Bool.rec (motive := fun _ => Bool) b true a = true →
      a = true ∨ b = true := by
    intro a b h
    cases a
    · exact Or.inr h
    · exact Or.inl rfl
  rcases key h1 with hc | hc
  · obtain ⟨b1, b⟩ := (CIdx.bAnd_iff' _ _).1 hc
    obtain ⟨b2, b3⟩ := (CIdx.bAnd_iff' _ _).1 b
    generalize pg w2 (mask w2) (PR d) e = c at b1 b2 b3
    refine ⟨c / 64, blt_iff.1 b1, ⟨c / 8 % 8, Nat.mod_lt _ (by norm_num), ?_⟩, c % 8,
      Nat.mod_lt _ (by norm_num), beq_iff.1 b3⟩
    have e8 : 8 * (c / 64) + c / 8 % 8 = c / 8 := by omega
    rw [e8]
    exact beq_iff.1 b2
  · exfalso
    have hA : Acts n (fun x => pg w (mask w) (RT d) (pg w (mask w) (RT e)
        (pg w (mask w) (RT d) x)))
        (el n S base nb (RL d) * el n S base nb (RL e) * el n S base nb (RL d)) := by
      intro y
      dsimp only
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hR d hd hcd y, hR e he hce, hR d hd hcd]
    have hdM := el_mem' hQ hN (hRL d hd)
    have heM := el_mem' hQ hN (hRL e he)
    have hb := (eqB_iff_eq hQ hA (hR e he hce) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hdM heM)
      hdM) heM).2 hxy
    rw [hb] at hc
    exact Bool.false_ne_true hc

theorem subR_facts {N nr nx zj mm : Nat} {RL RT CT IV X XI QJ QR QA QW QP : Nat → Nat}
    {Xg : Nat → Equiv.Perm (Fin n)} (hN : ordK LR nb = N) (hRL : ∀ d < nr, RL d < N)
    (hRT : ∀ d < nr, rootTK n w (mask w) (n * w) BP nb LR TR RL RT CT IV d = true)
    (hX : ∀ t < nx, Orb.PRep n w (X t) (Xg t) ∧ Orb.PRep n w (XI t) (Xg t)⁻¹)
    (h : subRK n w (mask w) (n * w) BP nb N nr nx zj LR TR RL RT CT X XI QJ QR QA QW QP mm =
      true) :
    (∀ k < 8, QJ (8 * mm + k) < N) ∧ QJ (8 * mm + 1) = zj ∧
      (∀ k < 8, el n S base nb (QJ (8 * mm + k)) =
        q8G (el n S base nb (QJ (8 * mm + 2))) (el n S base nb (QJ (8 * mm + 4))) k) ∧
      el n S base nb (QJ (8 * mm + 4)) * el n S base nb (QJ (8 * mm + 4)) =
        el n S base nb (QJ (8 * mm + 1)) ∧
      el n S base nb (QJ (8 * mm + 2)) * el n S base nb (QJ (8 * mm + 4)) *
        el n S base nb (QJ (8 * mm + 2)) = el n S base nb (QJ (8 * mm + 4)) ∧
      (∀ a < 5, 1 ≤ QA (5 * mm + a) ∧ QA (5 * mm + a) < nx) ∧
      ∀ a < 5, ∀ b < 5, a < b → ∃ k < 8, ∀ k' < 8,
        (Xg (QA (5 * mm + b)))⁻¹ * Xg (QA (5 * mm + a)) * el n S base nb (QJ (8 * mm + k)) *
          (Xg (QA (5 * mm + a)))⁻¹ * Xg (QA (5 * mm + b)) ≠
            el n S base nb (QJ (8 * mm + k')) := by
  unfold subRK at h
  simp only [CIdx.strictB_eq, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨h2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨hr, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h01, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h27, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h5, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h6, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h7, h8⟩ := (CIdx.bAnd_iff' _ _).1 h
  have hlt : ∀ k < 8, QJ (8 * mm + k) < N := fun k hk => blt_iff.1 ((allN_iff.1 h2) k hk)
  have hM : ∀ k < 8, el n S base nb (QJ (8 * mm + k)) ∈ Gen n S kO := fun k hk =>
    el_mem' hQ hN (hlt k hk)
  have hR := rootT_acts hQ hN hRL hRT
  have hroot : ∀ i < 6, Acts n (pg w (mask w) (RT (QR (8 * mm + (2 + i)))))
      (el n S base nb (QJ (8 * mm + (2 + i)))) := by
    intro i hi
    obtain ⟨c1, c⟩ := (CIdx.bAnd_iff' _ _).1 ((allN_iff.1 hr) i hi)
    obtain ⟨c2, c3⟩ := (CIdx.bAnd_iff' _ _).1 c
    rw [← beq_iff.1 c3]
    exact hR _ (blt_iff.1 c1) (beq_iff.1 c2)
  set A := el n S base nb (QJ (8 * mm + 2))
  set B := el n S base nb (QJ (8 * mm + 4))
  have hA : Acts n (pg w (mask w) (RT (QR (8 * mm + 2)))) A := hroot 0 (by norm_num)
  have hB : Acts n (pg w (mask w) (RT (QR (8 * mm + 4)))) B := hroot 2 (by norm_num)
  have hAM := hM 2 (by norm_num)
  have hBM := hM 4 (by norm_num)
  have hq8M : ∀ k < 8, q8G A B k ∈ Gen n S kO := by
    intro k hk
    have m := fun x y => Subgroup.mul_mem (Gen n S kO) (x := x) (y := y)
    interval_cases k <;> simp only [q8G] <;> norm_num <;>
      first
        | exact Subgroup.one_mem _
        | exact hAM
        | exact hBM
        | exact m _ _ hAM hAM
        | exact m _ _ (m _ _ hAM hAM) hAM
        | exact m _ _ (m _ _ hAM hAM) hBM
        | exact m _ _ hAM hBM
        | exact m _ _ (m _ _ (m _ _ hAM hAM) hAM) hBM
  have hq8 : ∀ k < 8, el n S base nb (QJ (8 * mm + k)) = q8G A B k := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · exact (eqB_iff_eq hQ (acts_elF hQ _) (acts_q8W hA hB hk) (hM k hk) (hq8M k hk)).1
        ((allN_iff.1 h01) k hk2)
    · obtain ⟨i, rfl⟩ : ∃ i, k = 2 + i := ⟨k - 2, by omega⟩
      exact (eqB_iff_eq hQ (hroot i (by omega)) (acts_q8W hA hB hk) (hM _ hk) (hq8M _ hk)).1
        ((allN_iff.1 h27) i (by omega))
  have hAA : A * A = el n S base nb (QJ (8 * mm + 1)) := by
    rw [hq8 1 (by norm_num)]
    simp [q8G]
  have hQA : ∀ a < 5, 1 ≤ QA (5 * mm + a) ∧ QA (5 * mm + a) < nx := by
    intro a ha
    obtain ⟨c1, c2⟩ := (CIdx.bAnd_iff' _ _).1 ((allN_iff.1 h7) a ha)
    exact ⟨ble_iff.1 c1, blt_iff.1 c2⟩
  refine ⟨hlt, beq_iff.1 h3, hq8, ?_, ?_, hQA, fun a ha b hb hab => ?_⟩
  · rw [← hAA]
    refine (eqB_iff_eq hQ (fun y => ?_) (fun y => ?_) (Subgroup.mul_mem _ hBM hBM)
      (Subgroup.mul_mem _ hAM hAM)).1 h5
    · rw [Equiv.Perm.mul_apply, hB y, hB]
    · rw [Equiv.Perm.mul_apply, hA y, hA]
  · refine (eqB_iff_eq hQ (fun y => ?_) hB (Subgroup.mul_mem _ (Subgroup.mul_mem _ hAM hBM)
      hAM) hBM).1 h6
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hA y, hB, hA]
  · have g1 := (allN_iff.1 ((allN_iff.1 h8) a ha)) b hb
    simp only [show Nat.blt a b = true from blt_iff.2 hab] at g1
    obtain ⟨k1, k2⟩ := (CIdx.bAnd_iff' _ _).1 g1
    obtain ⟨kx, k2⟩ := (CIdx.bAnd_iff' _ _).1 k2
    have hta := (hQA a ha).2
    have htb := (hQA b hb).2
    generalize QA (5 * mm + a) = ta at k2 hta
    generalize QA (5 * mm + b) = tb at k2 htb
    obtain ⟨hXa, hXa'⟩ := hX ta hta
    obtain ⟨hXb, hXb'⟩ := hX tb htb
    have hk := blt_iff.1 k1
    refine ⟨_, hk, fun k' hk' e => ?_⟩
    rw [hq8 _ hk, hq8 k' hk'] at e
    refine q8Out_spec k2 k' hk' ?_
    obtain ⟨y, hy⟩ : ∃ y : Fin n, (y : Nat) = QP (25 * mm + (5 * a + b)) :=
      ⟨⟨_, blt_iff.1 kx⟩, rfl⟩
    rw [← hy]
    have e' := congrArg (fun g : Equiv.Perm (Fin n) => (g y : Nat)) e
    simp only [Equiv.Perm.mul_apply] at e'
    rw [hXb y, hXa', acts_q8W hA hB hk, hXa, hXb', acts_q8W hA hB hk']
    exact e'

theorem cutZ_sound {p : Nat} {RL X XI CT CP : Nat → Nat} {x0 : Equiv.Perm (Fin n)}
    (hX1 : Orb.PRep n w (X 0) x0) (hX2 : Orb.PRep n w (XI 0) x0⁻¹)
    (hct : cutK n w (mask w) (n * w) BP nb LR TR TRI RL (fun _ => 0) (fun i => i) (fun _ => 0)
      X XI CT CP p = true)
    (hCT : CT p ≠ 0) : x0⁻¹ * el n S base nb (RL p) * x0 ∉ Gen n S kO := by
  unfold cutK at hct
  rw [CIdx.strictB_eq, show Nat.beq (CT p) 0 = false from
    Bool.eq_false_iff.2 fun e => hCT (beq_iff.1 e)] at hct
  simp only [CIdx.strictB_eq] at hct
  obtain ⟨-, a⟩ := (CIdx.bAnd_iff' _ _).1 hct
  obtain ⟨a2, a3⟩ := (CIdx.bAnd_iff' _ _).1 a
  intro hm
  obtain ⟨g, hg, hgid⟩ := siftP_complete hQ (f := conjF w (mask w) (XI 0) (X 0)
    (elF n w (mask w) (n * w) nb LR TR (RL p))) (fun y => by
      unfold conjF
      rw [hX1 y, acts_elF hQ, hX2]
      rfl) hm
  rw [hg] at a3
  have e2 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (g (CP p)) (CP p)) = true :=
    a3
  have hgq : g (CP p) = CP p := hgid ⟨CP p, blt_iff.1 a2⟩
  rw [hgq, show Nat.beq (CP p) (CP p) = true from beq_iff.2 rfl] at e2
  exact Bool.false_ne_true e2

end Chain

end CFSG.KS.SporSch.RPair

end
