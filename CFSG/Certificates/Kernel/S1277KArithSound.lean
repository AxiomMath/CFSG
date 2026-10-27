module

public import Certificates.Data.Kernel.S1277KArith
public import CFSG.Certificates.Kernel.S1277KSigSound
public import CFSG.Certificates.Kernel.S1277KFrSound

public section

namespace CFSG.KS.S1277Ar

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Fr
  CFSG.KC.S1277Ar CFSG.KS.S1277Lat CFSG.KS.S1277Mod CFSG.KS.S1277Sig CFSG.KS.S1277Cand
  CFSG.KS.S1277Fr CFSG.Quasithin.H13.I1277 Certificates.Data.S1277Sig CFSG.Open

section XPart

variable {d L u : ℕ}

theorem sig_zero {φ : ℕ → ℕ} {σ : Equiv.Perm (Fin (2 ^ d))} (hσ : σ ∈ Sig d φ)
    (x : Fin (2 ^ d)) (hx : x.1 = 0) : σ x = x := by
  have h := hσ.1 x x x (by rw [hx, Nat.xor_self])
  rw [Nat.xor_self] at h
  exact Fin.ext (h.symm.trans hx.symm)

theorem sig_fix_u {σ : Equiv.Perm (Fin (2 ^ d))} (hσ : σ ∈ Sig d (φL (2 ^ u)))
    (x : Fin (2 ^ d)) (hx : x.1 = u) : σ x = x := by
  have h := φL_eq_iff.1 (hσ.2 x)
  rw [Nat.testBit_two_pow, Nat.testBit_two_pow, hx] at h
  simp only [decide_true, decide_eq_true_eq] at h
  exact Fin.ext (h.symm.trans hx.symm)

noncomputable def Xk (d u : ℕ) : Subgroup (Equiv.Perm (Fin (2 ^ d))) where
  carrier := {σ | σ ∈ Sig d (φL (2 ^ u)) ∧
    ∀ x : Fin (2 ^ d), (σ x).1 ^^^ x.1 = 0 ∨ (σ x).1 ^^^ x.1 = u}
  one_mem' := ⟨(Sig d _).one_mem, fun x => Or.inl (Nat.xor_self _)⟩
  mul_mem' := fun {σ τ} hσ hτ => ⟨(Sig d _).mul_mem hσ.1 hτ.1, fun x => by
    rw [Equiv.Perm.mul_apply]
    have e : (σ (τ x)).1 ^^^ x.1 = ((σ (τ x)).1 ^^^ (τ x).1) ^^^ ((τ x).1 ^^^ x.1) := by
      rw [Nat.xor_assoc, ← Nat.xor_assoc (τ x).1, Nat.xor_self, Nat.zero_xor]
    rw [e]
    rcases hσ.2 (τ x) with h1 | h1 <;> rcases hτ.2 x with h2 | h2 <;> rw [h1, h2] <;> simp⟩
  inv_mem' := fun {σ} hσ => ⟨(Sig d _).inv_mem hσ.1, fun x => by
    have h := hσ.2 (σ⁻¹ x)
    have e : σ (σ⁻¹ x) = x := by simp
    rw [e, Nat.xor_comm] at h
    exact h⟩

theorem Xk_normal {τ σ : Equiv.Perm (Fin (2 ^ d))} (hτ : τ ∈ Sig d (φL (2 ^ u)))
    (hσ : σ ∈ Xk d u) : τ * σ * τ⁻¹ ∈ Xk d u := by
  refine ⟨(Sig d _).mul_mem ((Sig d _).mul_mem hτ hσ.1) ((Sig d _).inv_mem hτ), fun x => ?_⟩
  obtain ⟨y, rfl⟩ := τ.surjective x
  have e : τ⁻¹ (τ y) = y := by simp
  simp only [Equiv.Perm.mul_apply, e]
  have hc : (σ y).1 ^^^ y.1 < 2 ^ d := Nat.xor_lt_two_pow (σ y).2 y.2
  rw [hτ.1 (σ y) y ⟨_, hc⟩ rfl]
  rcases hσ.2 y with h | h
  · rw [sig_zero hτ ⟨_, hc⟩ h]
    exact Or.inl h
  · rw [sig_fix_u hτ ⟨_, hc⟩ h]
    exact Or.inr h

theorem Xk_sq {σ : Equiv.Perm (Fin (2 ^ d))} (hσ : σ ∈ Xk d u) : σ * σ = 1 := by
  refine Equiv.ext fun x => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  have hc : (σ x).1 ^^^ x.1 < 2 ^ d := Nat.xor_lt_two_pow (σ x).2 x.2
  have hfix : σ ⟨_, hc⟩ = ⟨_, hc⟩ := by
    rcases hσ.2 x with h | h
    · exact sig_zero hσ.1 _ h
    · exact sig_fix_u hσ.1 _ h
  have hadd := hσ.1.1 x ⟨_, hc⟩ (σ x) (by
    change x.1 ^^^ ((σ x).1 ^^^ x.1) = (σ x).1
    rw [Nat.xor_comm (σ x).1, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor])
  rw [hfix] at hadd
  rw [← hadd]
  change (σ x).1 ^^^ ((σ x).1 ^^^ x.1) = x.1
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem x_sound {ts : List (List ℕ)} (h : xChk d L u ts = true) :
    ∃ X : Subgroup (Equiv.Perm (Fin (2 ^ d))), X ≤ Sig d (φL L) ∧
      (∀ τ ∈ Sig d (φL L), ∀ x ∈ X, τ * x * τ⁻¹ ∈ X) ∧ IsPGroup 2 ↥X ∧ 8 ≤ Nat.card X := by
  rw [xChk] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, -⟩, -⟩, hall⟩ := h
  obtain rfl : L = 2 ^ u := Nat.eq_of_beq_eq_true hL
  refine ⟨Xk d u, fun σ hσ => hσ.1, fun τ hτ σ hσ => Xk_normal hτ hσ, fun σ => ⟨1, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (σ : Equiv.Perm (Fin (2 ^ d))) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact Xk_sq σ.2
  have hrow : ∀ j < 8, tChk d (2 ^ u) [] 0 (ts.getD j []) = true ∧
      allLt (2 ^ d) (fun x => Nat.beq (apK (ts.getD j []) x ^^^ x) 0 ||
        Nat.beq (apK (ts.getD j []) x ^^^ x) u) = true ∧
      allLt j (fun j' => !eqL (ts.getD j []) (ts.getD j' [])) = true := by
    intro j hj
    have hc := (allL_iff.1 hall) j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2⟩
  have hlen : ∀ j < 8, (ts.getD j []).length = d := by
    intro j hj
    have ht := (hrow j hj).1
    rw [tChk] at ht
    simp only [Bool.and_eq_true] at ht
    exact Nat.eq_of_beq_eq_true ht.1.1.1.1
  have hj : ∀ j < 8, ∃ σ ∈ Xk d u, ∀ x : Fin (2 ^ d), (σ x).1 = applyCols (ts.getD j []) x.1 := by
    intro j hj
    obtain ⟨ht, hmv, -⟩ := hrow j hj
    obtain ⟨σ, hσ, hσt⟩ := perm_of_tChk ht
    rw [Gk_zero] at hσ
    refine ⟨σ, ⟨hσ, fun x => ?_⟩, hσt⟩
    have h1 := (allLt_iff.1 hmv) x.1 x.2
    rw [Bool.or_eq_true] at h1
    rw [hσt, ← apK_eq]
    rcases h1 with h1 | h1
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · exact Or.inr (Nat.eq_of_beq_eq_true h1)
  have heq : ∀ j < 8, ∀ j' < 8, (∀ x : Fin (2 ^ d),
      applyCols (ts.getD j []) x.1 = applyCols (ts.getD j' []) x.1) → j = j' := by
    intro j hj j' hj' hx
    have hts : ts.getD j [] = ts.getD j' [] := by
      apply List.ext_getElem (by rw [hlen j hj, hlen j' hj'])
      intro i h1 h2
      have hi : i < d := by rw [hlen j hj] at h1; exact h1
      rw [← applyCols_pow _ i h1, ← applyCols_pow _ i h2]
      exact hx ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi⟩
    have e : eqL (ts.getD j' []) (ts.getD j' []) = true := eqL_iff.2 rfl
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := (allLt_iff.1 (hrow j' hj').2.2) j hlt
      rw [hts, e] at h1
      exact absurd h1 (by decide)
    · have h1 := (allLt_iff.1 (hrow j hj).2.2) j' hlt
      rw [hts, e] at h1
      exact absurd h1 (by decide)
  choose f hf hfa using hj
  let g : Fin 8 → Xk d u := fun j => ⟨f j.1 j.2, hf _ _⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hab' : f a.1 a.2 = f b.1 b.2 := congrArg Subtype.val hab
    refine Fin.ext (heq a.1 a.2 b.1 b.2 fun x => ?_)
    rw [← hfa a.1 a.2 x, ← hfa b.1 b.2 x, hab']
  have h8 := Nat.card_le_card_of_injective g hg
  have e8 : Nat.card (Fin 8) = 8 := by simp
  rwa [e8] at h8

end XPart

section Branch

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem card_of_node (hκ : MCod K M κ) {kg kt nm nxs : List ℕ} {ngs nts : List (List ℕ)}
    (hgen : genChk M kg kt = true) (hnodes : nodesChk M kg nm ngs nts nxs = true) {i : ℕ}
    (hi : i < nm.length) (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ (nm.getD i 0).testBit n = true) :
    Nat.card Q = 2 ^ nxs.getD i 0 := by
  obtain ⟨O, hOK, -, -, hOm, hOc⟩ := node_subgroupG hκ hgen hnodes hi
  have hQO : Q = O := by
    ext x
    constructor
    · intro hx
      exact (hOm x (hQK hx)).2 ((hQN _).1 ⟨x, hx, rfl⟩)
    · intro hx
      obtain ⟨q, hq, hqx⟩ := (hQN _).2 ((hOm x (hOK hx)).1 hx)
      rw [← hκ.inj q (hQK hq) x (hOK hx) hqx]
      exact hq
  rw [hQO, hOc]

theorem lab_conj {z : G} (hzH : ∀ h ∈ H, h * z * h⁻¹ = z)
    (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) {h : G} (hh : h ∈ H) (x : G) :
    (h * x * h⁻¹ = z ↔ x = z) ∧ (h * x * h⁻¹ * (h * x * h⁻¹) ≠ 1 ↔ x * x ≠ 1) ∧
      ((∀ n ∈ Phi' Q, h * x * h⁻¹ * n = n * (h * x * h⁻¹)) ↔ ∀ n ∈ Phi' Q, x * n = n * x) := by
  refine ⟨⟨fun e => ?_, fun e => by rw [e]; exact hzH h hh⟩, ?_, ?_⟩
  · have e' : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [e', e]
    have := hzH h⁻¹ (H.inv_mem hh)
    simpa using this
  · have e : h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
    rw [e, not_iff_not]
    constructor
    · intro e'
      have : x * x = h⁻¹ * (h * (x * x) * h⁻¹) * h := by group
      rw [this, e']
      group
    · intro e'
      rw [e']
      group
  · constructor
    · intro hc n' hn'
      have := hc _ (Phi'_normal hQn h hh n' hn')
      have e1 : h * x * h⁻¹ * (h * n' * h⁻¹) = h * (x * n') * h⁻¹ := by group
      have e2 : h * n' * h⁻¹ * (h * x * h⁻¹) = h * (n' * x) * h⁻¹ := by group
      rw [e1, e2] at this
      exact mul_left_cancel (mul_right_cancel this)
    · intro hc n hn
      have hn' : h⁻¹ * n * h ∈ Phi' Q := by
        have := Phi'_normal hQn h⁻¹ (H.inv_mem hh) n hn
        simpa using this
      have := hc _ hn'
      have e1 : h * x * h⁻¹ * n = h * (x * (h⁻¹ * n * h)) * h⁻¹ := by group
      have e2 : n * (h * x * h⁻¹) = h * ((h⁻¹ * n * h) * x) * h⁻¹ := by group
      rw [e1, e2, this]

end Branch

theorem cov_sound {n : ℕ} {l₁ l₂ l₃ l₄ : List ℕ} (h : covChk n l₁ l₂ l₃ l₄ = true) :
    ∀ i < n, i ∈ l₁ ∨ i ∈ l₂ ∨ i ∈ l₃ ∨ i ∈ l₄ := by
  intro i hi
  have h1 := (allLt_iff.1 h) i hi
  simp only [Bool.or_eq_true, memL_iff] at h1
  tauto

end CFSG.KS.S1277Ar

end
