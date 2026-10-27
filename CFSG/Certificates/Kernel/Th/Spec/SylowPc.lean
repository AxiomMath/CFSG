module

public import CFSG.Certificates.Kernel.Th.Spec.SylowPcGrp
public import CFSG.Certificates.Kernel.Th.Spec.SylowPcRun
public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Certificates.Kernel.Th.S.BigS
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp

public section

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec

namespace CFSG.KC.Th.Spec.SylowPc

private theorem pc_andB_split {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem pc_natRec_iff (P : ℕ → Bool) (m : ℕ) :
    Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (P k)) m = true ↔
      ∀ k < m, P k = true := by
  induction m with
  | zero =>
    constructor
    · intro _ k hk
      exact absurd hk (Nat.not_lt_zero k)
    · intro _
      rfl
  | succ m ih =>
    show andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (P k)) m) (P m) = true ↔ _
    constructor
    · intro h k hk
      obtain ⟨h1, h2⟩ := pc_andB_split h
      by_cases hkm : k < m
      · exact ih.1 h1 k hkm
      · have hkeq : k = m := by omega
        subst hkeq
        exact h2
    · intro h
      have h1 : Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (P k)) m = true :=
        ih.2 (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have h2 : P m = true := h m (Nat.lt_succ_self m)
      rw [h1, h2]
      rfl

private theorem pc_pwOK_entry {RB PW : ℕ → ℕ} {c rm PR n p : ℕ}
    (h : pwOK RB PW c rm PR n p = true) :
    ∀ k < n, ∀ e < p - 1, Nat.beq (PW (k * (p - 1) + e))
      (Bool.rec (motive := fun _ => Nat) (mulB c rm (PW (k * (p - 1) + e - 1)) (RB (regAt PR k)))
        (RB (regAt PR k)) (Nat.beq e 0)) = true := by
  intro k hk e he
  have h1 := (pc_natRec_iff (fun k' => Nat.rec (motive := fun _ => Bool) true
      (fun e' ih2 => andB ih2 (Nat.beq (PW (k' * (p - 1) + e')) (Bool.rec (motive := fun _ => Nat)
        (mulB c rm (PW (k' * (p - 1) + e' - 1)) (RB (regAt PR k'))) (RB (regAt PR k'))
        (Nat.beq e' 0))))
      (p - 1)) n).1 h k hk
  exact (pc_natRec_iff (fun e' => Nat.beq (PW (k * (p - 1) + e')) (Bool.rec (motive := fun _ => Nat)
      (mulB c rm (PW (k * (p - 1) + e' - 1)) (RB (regAt PR k))) (RB (regAt PR k))
      (Nat.beq e' 0))) (p - 1)).1 h1 e he

private theorem pc_rhsPc_succ_eq (PW : ℕ → ℕ) (c rm ONE p pb x m : ℕ) :
    rhsPc PW c rm ONE (m + 1) p pb x =
      Bool.rec (motive := fun _ => Nat)
        (mulB c rm (rhsPc PW c rm ONE m p pb x) (PW (m * (p - 1) + bitsN x (pb * m) pb - 1)))
        (rhsPc PW c rm ONE m p pb x) (Nat.beq (bitsN x (pb * m) pb) 0) := rfl

private theorem pc_rhsPc_succ_zero (PW : ℕ → ℕ) (c rm ONE p pb x m : ℕ)
    (h0 : bitsN x (pb * m) pb = 0) :
    rhsPc PW c rm ONE (m + 1) p pb x = rhsPc PW c rm ONE m p pb x := by
  have hb : Nat.beq (bitsN x (pb * m) pb) 0 = true := by simp [h0]
  rw [pc_rhsPc_succ_eq, hb]

private theorem pc_rhsPc_succ_ne (PW : ℕ → ℕ) (c rm ONE p pb x m : ℕ)
    (h0 : bitsN x (pb * m) pb ≠ 0) :
    rhsPc PW c rm ONE (m + 1) p pb x =
      mulB c rm (rhsPc PW c rm ONE m p pb x) (PW (m * (p - 1) + bitsN x (pb * m) pb - 1)) := by
  have hb : Nat.beq (bitsN x (pb * m) pb) 0 = false :=
    Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  rw [pc_rhsPc_succ_eq, hb]

section Rel

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {G : Type*} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2))

private theorem pc_rhsPc_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {PW : ℕ → ℕ} {n p pb x i : ℕ} (g : ℕ → G)
    (hpw : ∀ k < n, ∀ e, 1 ≤ e → e < p → pkMat (PW (k * (p - 1) + e - 1)) = φ (g k ^ e))
    (hx : ∀ k < n, bitsN x (pb * k) pb < p)
    (hz : ∀ k < n, k ≤ i → bitsN x (pb * k) pb = 0) :
    ∀ m, m ≤ n → ∃ r ∈ pcSub g n (i + 1), pkMat (rhsPc PW c rm ONE m p pb x) = φ r := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨1, one_mem _, ?_⟩
    have h0 : rhsPc PW c rm ONE 0 p pb x = ONE := rfl
    rw [h0, pkMat_one hk, map_one]
  | succ m ih =>
    intro hm
    obtain ⟨r, hr, hrpk⟩ := ih (Nat.le_of_succ_le hm)
    have hmn : m < n := Nat.lt_of_succ_le hm
    by_cases h0 : bitsN x (pb * m) pb = 0
    · refine ⟨r, hr, ?_⟩
      rw [pc_rhsPc_succ_zero PW c rm ONE p pb x m h0]
      exact hrpk
    · have hmi : i < m := by
        by_contra hcon
        exact h0 (hz m hmn (by omega))
      have hpos : 1 ≤ bitsN x (pb * m) pb := Nat.pos_of_ne_zero h0
      have hgm : g m ∈ pcSub g n (i + 1) := by
        exact Subgroup.subset_closure (Set.mem_image_of_mem g (Set.mem_Ico.mpr ⟨by omega, hmn⟩))
      refine ⟨r * g m ^ bitsN x (pb * m) pb, mul_mem hr (pow_mem hgm _), ?_⟩
      rw [pc_rhsPc_succ_ne PW c rm ONE p pb x m h0, pkMat_mulB hk, hrpk,
        hpw m hmn _ hpos (hx m hmn), map_mul]

theorem pw_spec (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {RB PW : ℕ → ℕ} {PR n p : ℕ} (g : ℕ → G)
    (hg : ∀ k < n, φ (g k) = pkMat (RB (regAt PR k)))
    (h : pwOK RB PW c rm PR n p = true) :
    ∀ k < n, ∀ e, 1 ≤ e → e < p → pkMat (PW (k * (p - 1) + e - 1)) = φ (g k ^ e) := by
  have key : ∀ k < n, ∀ e, e < p - 1 → pkMat (PW (k * (p - 1) + e)) = φ (g k) ^ (e + 1) := by
    intro k hkn e
    induction e with
    | zero =>
      intro he
      have heq : PW (k * (p - 1) + 0) = RB (regAt PR k) :=
        Nat.eq_of_beq_eq_true (pc_pwOK_entry h k hkn 0 he)
      rw [heq, ← hg k hkn, zero_add, pow_one]
    | succ e ih =>
      intro he
      have h2 : k * (p - 1) + (e + 1) - 1 = k * (p - 1) + e := by omega
      have heq : PW (k * (p - 1) + (e + 1)) = mulB c rm (PW (k * (p - 1) + e)) (RB (regAt PR k)) := by
        have h1 := Nat.eq_of_beq_eq_true (pc_pwOK_entry h k hkn (e + 1) he)
        rw [h2] at h1
        exact h1
      rw [heq, pkMat_mulB hk, ih (by omega), ← hg k hkn, ← pow_succ]
  intro k hkn e he1 hep
  have h1 := key k hkn (e - 1) (by omega)
  have h2 : k * (p - 1) + e - 1 = k * (p - 1) + (e - 1) := by omega
  have h3 : e - 1 + 1 = e := by omega
  rw [h2, h1, h3, map_pow]

theorem pcRel_spec (hφ : Function.Injective φ)
    (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {RB PW : ℕ → ℕ} {PR n p pb : ℕ} (hp : 2 ≤ p) (g : ℕ → G)
    (hg : ∀ k < n, φ (g k) = pkMat (RB (regAt PR k)))
    (hpw : pwOK RB PW c rm PR n p = true)
    {i j x : ℕ} (hij : i ≤ j) (hj : j < n)
    (h : pcRelOK RB PW c rm ONE PR n p pb i j x = true) :
    (i = j → g i ^ p ∈ pcSub g n (i + 1)) ∧
      (i < j → (g i)⁻¹ * g j * g i ∈ pcSub g n (i + 1)) := by
  have hpwS := pw_spec φ hk g hg hpw
  unfold pcRelOK at h
  obtain ⟨hL, hR⟩ := pc_andB_split h
  have hL' : ∀ k < n, Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsN x (pb * k) pb) p)
      (Nat.beq (bitsN x (pb * k) pb) 0) (Nat.ble k i) = true :=
    (pc_natRec_iff (fun k => Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsN x (pb * k) pb) p)
      (Nat.beq (bitsN x (pb * k) pb) 0) (Nat.ble k i)) n).1 hL
  have hzero : ∀ k < n, k ≤ i → bitsN x (pb * k) pb = 0 := by
    intro k hkn hki
    have h1 := hL' k hkn
    rw [Nat.ble_eq_true_of_le hki] at h1
    have h2 : Nat.beq (bitsN x (pb * k) pb) 0 = true := h1
    exact Nat.eq_of_beq_eq_true h2
  have hxlt : ∀ k < n, bitsN x (pb * k) pb < p := by
    intro k hkn
    by_cases hki : k ≤ i
    · rw [hzero k hkn hki]
      omega
    · have hb : Nat.ble k i = false :=
        Bool.eq_false_iff.mpr (fun h' => hki (Nat.le_of_ble_eq_true h'))
      have h1 := hL' k hkn
      rw [hb] at h1
      have h2 : Nat.blt (bitsN x (pb * k) pb) p = true := h1
      rw [Nat.blt_eq] at h2
      exact h2
  obtain ⟨r, hr, hrpk⟩ := pc_rhsPc_spec φ hk g hpwS hxlt hzero n le_rfl
  have hi : i < n := lt_of_le_of_lt hij hj
  constructor
  · intro hEq
    have hbeq : Nat.beq i j = true := by
      rw [hEq]
      exact Nat.beq_refl j
    rw [hbeq] at hR
    have hR2 : Nat.beq (mulB c rm (PW (i * (p - 1) + (p - 1) - 1)) (RB (regAt PR i)))
        (rhsPc PW c rm ONE n p pb x) = true := hR
    have e1 := congrArg pkMat (Nat.eq_of_beq_eq_true hR2)
    rw [pkMat_mulB hk, hrpk, hpwS i hi (p - 1) (by omega) (by omega), ← hg i hi] at e1
    have hpe : g i ^ p = g i ^ (p - 1) * g i := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    have hφe : φ (g i ^ p) = φ r := by
      rw [hpe, map_mul]
      exact e1
    have hgr : g i ^ p = r := hφ hφe
    rw [hgr]
    exact hr
  · intro hlt
    have hne : Nat.beq i j = false :=
      Bool.eq_false_iff.mpr (fun h' => ne_of_lt hlt (Nat.eq_of_beq_eq_true h'))
    rw [hne] at hR
    have hR2 : Nat.beq (mulB c rm (RB (regAt PR j)) (RB (regAt PR i)))
        (mulB c rm (RB (regAt PR i)) (rhsPc PW c rm ONE n p pb x)) = true := hR
    have e1 := congrArg pkMat (Nat.eq_of_beq_eq_true hR2)
    rw [pkMat_mulB hk, pkMat_mulB hk, hrpk, ← hg i hi, ← hg j hj] at e1
    have e2 : φ (g j * g i) = φ (g i * r) := by
      rw [map_mul, map_mul]
      exact e1
    have e3 : g j * g i = g i * r := hφ e2
    have e4 : (g i)⁻¹ * g j * g i = r := by
      rw [mul_assoc, e3, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e4]
    exact hr

end Rel

section Regs

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {G : Type*} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem regs_exist (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {RB : ℕ → ℕ} {Cs : List ℕ} (a b : G) (h1 : φ a = pkMat (RB 1)) (h2 : φ b = pkMat (RB 2))
    (hpos : 0 < runSlp RB c rm ONE Cs 3) :
    ∀ k, 0 < k → k < runSlp RB c rm ONE Cs 3 → ∃ g : G, φ g = pkMat (RB k) := by
  have hmul : ∀ r x y : ℕ, (∃ g : G, φ g = pkMat (RB x)) → (∃ g : G, φ g = pkMat (RB y)) →
      RB r = mulB c rm (RB x) (RB y) → ∃ g : G, φ g = pkMat (RB r) := by
    rintro r x y ⟨g, hg⟩ ⟨g', hg'⟩ h
    refine ⟨g * g', ?_⟩
    rw [map_mul, hg, hg', h, pkMat_mulB hk]
  have hpow : ∀ r x e : ℕ, (∃ g : G, φ g = pkMat (RB x)) → 0 < e → e < 16 →
      RB r = powB c rm ONE (RB x) e 4 → ∃ g : G, φ g = pkMat (RB r) := by
    rintro r x e ⟨g, hg⟩ _ he h
    refine ⟨g ^ e, ?_⟩
    rw [map_pow, hg, h, pkMat_powB hk _ e 4 he]
  have hinv : ∀ r x : ℕ, (∃ g : G, φ g = pkMat (RB x)) → mulB c rm (RB x) (RB r) = ONE →
      ∃ g : G, φ g = pkMat (RB r) := by
    rintro r x ⟨g, hg⟩ h
    refine ⟨g⁻¹, ?_⟩
    have hx : pkMat (RB x) * pkMat (RB r) = 1 := by
      rw [← pkMat_mulB hk, h, pkMat_one hk]
    have hgi : φ g⁻¹ * pkMat (RB x) = 1 := by
      rw [← hg, ← map_mul, inv_mul_cancel, map_one]
    calc φ g⁻¹ = φ g⁻¹ * (pkMat (RB x) * pkMat (RB r)) := by rw [hx, Matrix.mul_one]
      _ = (φ g⁻¹ * pkMat (RB x)) * pkMat (RB r) := (Matrix.mul_assoc _ _ _).symm
      _ = pkMat (RB r) := by rw [hgi, Matrix.one_mul]
  have hS : ∀ k, 0 < k → k < 3 → ∃ g : G, φ g = pkMat (RB k) := by
    intro k hk0 hk3
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · exact ⟨a, h1⟩
    · exact ⟨b, h2⟩
  intro k hk0 hk1
  exact CFSG.KC.Th.Spec.FwdSlp.runSlp_induct (fun k => ∃ g : G, φ g = pkMat (RB k))
    hmul hpow hinv Cs 3 hS hpos k hk0 hk1

end Regs


@[expose] def unitsHom (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) :
    Sˣ →* Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  S.subtype.comp (Units.coeHom S)

theorem unitsHom_apply (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) (u : Sˣ) :
    unitsHom S u = ((u : S) : Matrix (Fin 248) (Fin 248) (ZMod 2)) :=
  rfl

theorem unitsHom_injective (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) :
    Function.Injective (unitsHom S) := by
  intro x y hxy
  apply Units.ext
  apply Subtype.ext
  exact hxy

theorem unitsHom_finite (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) : Finite Sˣ := by
  have : Finite (Matrix (Fin 248) (Fin 248) (ZMod 2)) :=
    (inferInstance : Finite (Fin 248 → Fin 248 → ZMod 2))
  exact Finite.of_injective (unitsHom S) (unitsHom_injective S)

theorem seed_units (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2)))
    {A B : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hA : A ∈ S) (hB : B ∈ S) (hAA : A * A = 1)
    (hBBB : B * B * B = 1) : ∃ a b : Sˣ, unitsHom S a = A ∧ unitsHom S b = B := by
  refine ⟨⟨⟨A, hA⟩, ⟨A, hA⟩, Subtype.ext hAA, Subtype.ext hAA⟩,
    ⟨⟨B, hB⟩, ⟨B * B, S.mul_mem hB hB⟩, Subtype.ext ?_, Subtype.ext hBBB⟩, rfl, rfl⟩
  show B * (B * B) = 1
  rw [← mul_assoc]
  exact hBBB

section Main

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {G : Type*} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem pc_card_dvd [Finite G] (hφ : Function.Injective φ)
    (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {RB PW : ℕ → ℕ} {PR n p pb : ℕ} {Cs : List ℕ} (hn : n < 256) (hp : 2 ≤ p) (g : ℕ → G)
    (hg : ∀ k < n, φ (g k) = pkMat (RB (regAt PR k)))
    (hpw : pwOK RB PW c rm PR n p = true)
    (hrun : runPc RB PW c rm ONE PR n p pb Cs 1 = n + 1) :
    Nat.card (pcSub g n 0) ∣ p ^ n := by
  refine card_pcSub_dvd p n g (fun i hi => ?_) (fun i j hij hj => ?_)
  · obtain ⟨x, hx⟩ := runPc_pairs hn hrun i i le_rfl hi
    exact (pcRel_spec φ hφ hk hp g hg hpw le_rfl hi hx).1 rfl
  · obtain ⟨x, hx⟩ := runPc_pairs hn hrun i j hij.le hj
    exact (pcRel_spec φ hφ hk hp g hg hpw hij.le hj hx).2 hij

end Main

end CFSG.KC.Th.Spec.SylowPc

end
