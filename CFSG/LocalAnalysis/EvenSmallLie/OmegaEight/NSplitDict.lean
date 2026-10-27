module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitSylowCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitFox
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSModel

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SpBranch
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

attribute [local irreducible] sAct sMt sGinv p9List p9Index


theorem dictFacts (ε : Eps) :
    ((∀ x < 128, kapCode ε x < 128 ∧ kapInv ε (kapCode ε x) = x ∧ kapInv ε x < 128 ∧
      kapCode ε (kapInv ε x) = x ∧ ∀ y < 128, kapCode ε (x ^^^ y) = kapCode ε x ^^^ kapCode ε y) ∧
    (∀ i < 512, ∀ v < 64, phiCode ε i v < 64 ∧ qfB ε (phiCode ε i v) = qfB ε v ∧
      phiCode ε (sGinv[i]!) (phiCode ε i v) = v ∧ phiCode ε i (phiCode ε (sGinv[i]!) v) = v ∧
      ∀ w < 64, phiCode ε i (v ^^^ w) = phiCode ε i v ^^^ phiCode ε i w ^^^ phiCode ε i 0) ∧
    (∀ i < 512, ∀ x < 128, kapInv ε (sA i (kapCode ε x)) = actPhi ε i x) ∧
    (∀ i < 512, i = 0 ∨ ∃ e < 128, sA i e ≠ e)) ∧
    ∀ v < 64, qfB ε v = false → (p9Orbit (kapCode ε (v + 64))).length = 4 →
      tCode ε ∈ p9Orbit (kapCode ε (v + 64)) := by
  have h : dictCheck ε = true := by cases ε; exact dictCheck_plus; exact dictCheck_minus
  simp only [dictCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨⟨fun x hx => ?_, fun i hi v hv => ?_, h3, fun i hi => ?_⟩, fun v hv hq hl => ?_⟩
  · obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h1 x hx
    exact ⟨a, b, c, d, e⟩
  · obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h2 i hi v hv
    exact ⟨a, b, c, d, e⟩
  · rcases h4 i hi with h | ⟨e, he, hne⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, he, hne⟩
  · rcases h5 v hv with h | h | h
    · rw [hq] at h; exact absurd h (by decide)
    · exact absurd hl h
    · exact h

@[expose] def kV (ε : Eps) (e : ℕ) : V7 := toVec 7 (kapInv ε e)

theorem kV_xor (ε : Eps) {e e' : ℕ} (he : e < 128) (he' : e' < 128) :
    kV ε (e ^^^ e') = kV ε e + kV ε e' := by
  obtain ⟨h1, -⟩ := (dictFacts ε).1
  obtain ⟨-, -, a, b, -⟩ := h1 e he
  obtain ⟨-, -, a', b', -⟩ := h1 e' he'
  have hx := (h1 (kapInv ε e) a).2.2.2.2 (kapInv ε e') a'
  rw [b, b'] at hx
  have hlt : kapInv ε e ^^^ kapInv ε e' < 128 := Nat.xor_lt_two_pow (n := 7) a a'
  have : kapInv ε (e ^^^ e') = kapInv ε e ^^^ kapInv ε e' := by
    rw [← hx, (h1 _ hlt).2.1]
  rw [kV, this, toVec_xorN]
  rfl

theorem kV_injective (ε : Eps) {e e' : ℕ} (he : e < 128) (he' : e' < 128)
    (h : kV ε e = kV ε e') : e = e' := by
  obtain ⟨h1, -⟩ := (dictFacts ε).1
  have ha := (h1 e he).2.2
  have ha' := (h1 e' he').2.2
  have hi : kapInv ε e = kapInv ε e' := toVec_injective_lt (n := 7) ha.1 ha'.1 h
  rw [← ha.2.1, ← ha'.2.1, hi]

theorem kV_surjective (ε : Eps) (x : V7) : ∃ e < 128, kV ε e = x := by
  obtain ⟨h1, -⟩ := (dictFacts ε).1
  have hb : bitsV 7 x < 128 := bitsV_lt 7 x
  refine ⟨kapCode ε (bitsV 7 x), (h1 _ hb).1, ?_⟩
  rw [kV, (h1 _ hb).2.1, toVec_bitsV]

theorem phi_lt (ε : Eps) {i v : ℕ} (hi : i < 512) (hv : v < 64) : phiCode ε i v < 64 :=
  ((dictFacts ε).1.2.1 i hi v hv).1

@[expose] def phiFun (ε : Eps) (i : ℕ) (v : V6) : V6 := toVec 6 (phiCode ε i (vecBits v))

theorem vecBits_phiFun (ε : Eps) {i : ℕ} (hi : i < 512) (v : V6) :
    vecBits (phiFun ε i v) = phiCode ε i (vecBits v) :=
  vecBits_toVec (phi_lt ε hi (vecBits_lt v))


@[expose] def phiPerm (ε : Eps) (i : Fin 512) : Equiv.Perm V6 where
  toFun := phiFun ε i
  invFun := phiFun ε (sGinv[(i : ℕ)]!)
  left_inv v := by
    rw [phiFun, vecBits_phiFun ε i.2, ((dictFacts ε).1.2.1 i i.2 _ (vecBits_lt v)).2.2.1,
      toVec_vecBits]
  right_inv v := by
    rw [phiFun, vecBits_phiFun ε (sGinv_lt i.2),
      ((dictFacts ε).1.2.1 i i.2 _ (vecBits_lt v)).2.2.2.1,
      toVec_vecBits]

theorem qfV_phiFun (ε : Eps) {i : ℕ} (hi : i < 512) (v : V6) :
    qfV ε (phiFun ε i v) = qfV ε v := by
  rw [phiFun, qfV_toVec ε (phi_lt ε hi (vecBits_lt v)),
    ((dictFacts ε).1.2.1 i hi _ (vecBits_lt v)).2.1, qfV]

theorem phiCode_xor (ε : Eps) {i v w : ℕ} (hi : i < 512) (hv : v < 64) (hw : w < 64) :
    phiCode ε i (v ^^^ w) = phiCode ε i v ^^^ phiCode ε i w ^^^ phiCode ε i 0 :=
  ((dictFacts ε).1.2.1 i hi v hv).2.2.2.2 w hw

theorem phiFun_add (ε : Eps) {i : ℕ} (hi : i < 512) (v w : V6) :
    phiFun ε i (v + w) = phiFun ε i v + phiFun ε i w + phiFun ε i 0 := by
  have h := phiCode_xor ε hi (vecBits_lt v) (vecBits_lt w)
  rw [← vecBits_add] at h
  simp only [phiFun, h, toVec_xor, vecBits_zero]

theorem phiPerm_mem (ε : Eps) (i : Fin 512) : phiPerm ε i ∈ affGroup ε := by
  refine ⟨fun v => qfV_phiFun ε i.2 v, fun a b c => ?_⟩
  change phiFun ε i (a + b + c) = phiFun ε i a + phiFun ε i b + phiFun ε i c
  rw [phiFun_add ε i.2, phiFun_add ε i.2 a]
  have h0 : phiFun ε i 0 + phiFun ε i 0 = 0 := CharTwo.add_self_eq_zero _
  calc phiFun ε i a + phiFun ε i b + phiFun ε i 0 + phiFun ε i c + phiFun ε i 0
      = phiFun ε i a + phiFun ε i b + phiFun ε i c + (phiFun ε i 0 + phiFun ε i 0) := by abel
    _ = phiFun ε i a + phiFun ε i b + phiFun ε i c := by rw [h0, add_zero]

@[expose] def phiG (ε : Eps) (i : Fin 512) : affGroup ε := ⟨phiPerm ε i, phiPerm_mem ε i⟩

theorem toVec_actGen {f : ℕ → ℕ} (hf : ∀ v < 64, f v < 64) {σ : Equiv.Perm V6}
    (hσ : ∀ v, σ v = toVec 6 (f (vecBits v))) (x : ℕ) :
    toVec 7 (if x.testBit 6 then f (x % 64) + 64 else f (x % 64) ^^^ f 0) =
      actV7 σ (toVec 7 x) := by
  have hm : x % 64 < 64 := Nat.mod_lt x (by norm_num)
  have h1 := hf _ hm
  have h2 := hf 0 (by norm_num)
  have hs : ∀ y, y < 64 → σ (toVec 6 y) = toVec 6 (f y) := fun y hy => by
    rw [hσ, vecBits_toVec hy]
  rw [toVec7_eq x, actV7_mk7, hs _ hm]
  by_cases hb : x.testBit 6
  · simp only [hb, ite_true]
    rw [toVec7_eq]
    have e1 : (f (x % 64) + 64) % 64 = f (x % 64) := by omega
    have e2 : (f (x % 64) + 64).testBit 6 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]
      omega
    rw [e1, e2]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp [bz, h11]
  · simp only [hb, Bool.false_eq_true, ite_false]
    have hlt := Nat.xor_lt_two_pow (n := 6) h1 h2
    rw [toVec7_eq]
    rw [Nat.mod_eq_of_lt hlt, Nat.testBit_lt_two_pow hlt, toVec_xor, ← hs 0 (by norm_num)]
    simp [bz, show toVec 6 0 = 0 from toVec_zero 6]

theorem kV_sA (ε : Eps) (i : Fin 512) {e : ℕ} (he : e < 128) :
    kV ε (sA i e) = rhoE ε (phiG ε i) (kV ε e) := by
  obtain ⟨h1, -, h3, -⟩ := (dictFacts ε).1
  obtain ⟨-, -, hx, hkx, -⟩ := h1 e he
  have h := h3 i i.2 _ hx
  rw [hkx] at h
  rw [kV, h, rhoE_apply, kV]
  exact toVec_actGen (fun v hv => phi_lt ε i.2 hv) (fun v => rfl) _

theorem rhoE_injective (ε : Eps) {σ τ : affGroup ε} (h : ∀ x, rhoE ε σ x = rhoE ε τ x) :
    σ = τ := by
  apply Subtype.ext
  apply Equiv.ext
  intro v
  have := congrArg vOf (h (mk7 v 1))
  rw [rhoE_apply, rhoE_apply, actV7_mk7, actV7_mk7, vOf_mk7, vOf_mk7] at this
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  simpa [h11] using this

theorem rhoE_ext_kV (ε : Eps) {σ τ : affGroup ε}
    (h : ∀ e < 128, rhoE ε σ (kV ε e) = rhoE ε τ (kV ε e)) : σ = τ := by
  apply rhoE_injective ε
  intro x
  obtain ⟨e, he, rfl⟩ := kV_surjective ε x
  exact h e he

theorem phiG_sM (ε : Eps) (i j : Fin 512) :
    phiG ε ⟨sM i j, sM_lt i.2 j.2⟩ = phiG ε i * phiG ε j := by
  apply rhoE_ext_kV ε
  intro e he
  rw [← kV_sA ε _ he, map_mul]
  change kV ε (sA (sM i j) e) = rhoE ε (phiG ε i) (rhoE ε (phiG ε j) (kV ε e))
  rw [sA_mul i.2 j.2 he, ← kV_sA ε j he, ← kV_sA ε i (sA_lt j.2 he)]

theorem phiG_zero (ε : Eps) : phiG ε ⟨0, by norm_num⟩ = 1 := by
  apply rhoE_ext_kV ε
  intro e he
  rw [← kV_sA ε _ he, map_one]
  change kV ε (sA 0 e) = kV ε e
  rw [sA_zero he]

theorem phiG_eq_one (ε : Eps) {i : Fin 512} (h : phiG ε i = 1) : (i : ℕ) = 0 := by
  rcases (dictFacts ε).1.2.2.2 i i.2 with h0 | ⟨e, he, hne⟩
  · exact h0
  · exfalso
    apply hne
    apply kV_injective ε (sA_lt i.2 he) he
    rw [kV_sA ε i he, h, map_one]
    rfl

end CFSG.EvenSmallLie.OmegaEight.NSplit
