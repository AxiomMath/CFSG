module

public import CFSG.CGT.Stroth77.Section47CoreIC
public import CFSG.CGT.Stroth77.Section47CoreKH

public section

namespace CFSG.CGT.Stroth77

namespace Stroth47

theorem dvd_sub_of_dvd_two_mul {N M a b : ℤ} (hN : N = 2 * M) (hM : M ≠ 0) (ha : N ∣ 2 * a)
    (hb : N ∣ 2 * b) (hab : N ∣ a ↔ N ∣ b) : N ∣ b - a := by
  subst hN
  obtain ⟨t, rfl⟩ := (mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ) ≠ 0)).mp ha
  obtain ⟨t', rfl⟩ := (mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ) ≠ 0)).mp hb
  have key : ∀ s : ℤ, 2 * M ∣ M * s ↔ 2 ∣ s := fun s => by
    rw [mul_comm 2 M]
    exact mul_dvd_mul_iff_left hM
  rw [key, key] at hab
  rw [show M * t' - M * t = M * (t' - t) by ring, key]
  rcases Int.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨r', hr'⟩ := hab.mp ⟨r, by rw [hr]; ring⟩
    exact ⟨r' - r, by rw [hr, hr']; ring⟩
  · rcases Int.even_or_odd t' with ⟨r', hr'⟩ | ⟨r', hr'⟩
    · exfalso
      obtain ⟨q, hq⟩ := hab.mpr ⟨r', by rw [hr']; ring⟩
      omega
    · exact ⟨r' - r, by rw [hr, hr']; ring⟩

variable {G : Type*} [Group G]

theorem relIndex_sup_zpowers_dvd_two {U : Subgroup G} {f : G}
    (hf : f ∈ Subgroup.normalizer (U : Set G)) (hf2 : f * f ∈ U) :
    U.relIndex (U ⊔ Subgroup.zpowers f) ∣ 2 := by
  by_cases hfU : f ∈ U
  · rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hfU), Subgroup.relIndex_self]
    exact one_dvd _
  · rw [relIndex_sup_zpowers_of_mul_self_mem hf hf2 hfU]

end Stroth47

namespace Stroth47Core

open Matrix Stroth42Core Stroth34T200 StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {e f : G} {p : ℕ}

theorem t200k_e_conj_f_mem (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) : e⁻¹ * f * e * f⁻¹ ∈ D := by
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hrel_f.e_sq
  have h1 : e⁻¹ * f * e * f⁻¹ = e⁻¹ * (f⁻¹ * e * f) := by rw [hfinv]; group
  rw [h1, hconj, ← mul_assoc, ← _root_.mul_inv_rev, hrel_e.e_sq, inv_inv]
  exact D.mul_mem dD.c.2 (D.pow_mem dD.c.2 _)

theorem t200k_relIndex_dvd (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    D.relIndex (D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e) ∣ 8 := by
  have hDN : (D ⊔ Subgroup.zpowers dD.u : Subgroup G) ≤ Subgroup.normalizer (D : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr dD.u_mem)
  have hDfN : (D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f : Subgroup G) ≤
      Subgroup.normalizer (D : Set G) :=
    sup_le hDN (Subgroup.zpowers_le.mpr hfN)
  have h1 := Stroth47.relIndex_sup_zpowers_dvd_two (U := D) dD.u_mem
    (by rw [dD.u_sq]; exact D.one_mem)
  have hf2 : f ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers dD.u : Subgroup G) : Set G) := by
    refine Stroth47.mem_normalizer_of_conj_mul_inv_mem le_sup_left
      (by rw [hrel_f.e_sq]; exact one_mem _) ?_
    refine Stroth47.conj_mul_inv_mem hfN hDN (s := {dD.u}) (by rw [Subgroup.zpowers_eq_closure])
      ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hrel_f.u_conj, mul_inv_cancel]
    exact D.one_mem
  have h2 := Stroth47.relIndex_sup_zpowers_dvd_two hf2 (by rw [hrel_f.e_sq]; exact one_mem _)
  have heU : e * e ∈ D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f := by
    rw [hrel_e.e_sq]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (D.inv_mem dD.c.2))
  have he2 : e ∈ Subgroup.normalizer
      ((D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f : Subgroup G) : Set G) := by
    refine Stroth47.mem_normalizer_of_conj_mul_inv_mem (le_sup_left.trans le_sup_left) heU ?_
    refine Stroth47.conj_mul_inv_mem heN hDfN (s := {dD.u, f}) ?_ ?_
    · rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure, sup_assoc]
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [hrel_e.u_conj, mul_inv_cancel]
        exact D.one_mem
      · exact t200k_e_conj_f_mem dD hrel_e hrel_f hconj
  have h3 := Stroth47.relIndex_sup_zpowers_dvd_two he2 heU
  rw [← Subgroup.relIndex_mul_relIndex D (D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f) _
      (le_sup_left.trans le_sup_left) le_sup_left,
    ← Subgroup.relIndex_mul_relIndex D (D ⊔ Subgroup.zpowers dD.u) _ le_sup_left le_sup_left]
  exact mul_dvd_mul (mul_dvd_mul h1 h2) h3

theorem t200k_mem_of_comm_c₁ (hm : 1 ≤ m) (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    ∀ s ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e,
      s * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * s →
      s ∈ D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e := by
  intro s hs hsc
  obtain ⟨w, hw, kk, rfl⟩ := (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem
    (t200k_mem_normalizer dD heN hfN hrel_e hrel_f hconj) (t200k_e_mul_self_mem dD hrel_e)).mp hs
  obtain ⟨v, i, j, l, k', rfl⟩ := (dD.t200fEAction hrel_f).mem_sup_zpowers_iff.mp hw
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hfc : Commute f z := t200k_f_comm_c₁ dD hm hrel_f
  have hec : Commute e z := t200k_e_comm_c₁ dD hrel_e
  have hbf : Commute (bpow f k') z := by cases k' <;> simp [bpow, hfc]
  have hbe : Commute (bpow e kk) z := by cases kk <;> simp [bpow, hec]
  set X := dD.ofTorus v * dD.d8 i j l with hX
  have hsz : Commute (X * bpow f k' * bpow e kk) z := hsc
  have hXz : Commute X z := by
    have h := hsz.mul_left ((hbf.mul_left hbe).inv_left)
    rwa [show X * bpow f k' * bpow e kk * (bpow f k' * bpow e kk)⁻¹ = X by group] at h
  obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hXz.eq
  have hd8 : dD.d8 false false l ∈ Subgroup.zpowers dD.u := by
    cases l
    · rw [d8_fff]; exact one_mem _
    · rw [d8_fft]; exact Subgroup.mem_zpowers _
  have hbf' : bpow f k' ∈ Subgroup.zpowers f := by
    cases k' <;> simp [bpow, Subgroup.mem_zpowers, one_mem]
  have hbe' : bpow e kk ∈ Subgroup.zpowers e := by
    cases kk <;> simp [bpow, Subgroup.mem_zpowers, one_mem]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left (dD.ofTorus_mem v)))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hd8))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hbf')
  · exact Subgroup.mem_sup_right hbe'

theorem t200k_conj_ofTorus_y (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (l : Bool) (w : Torus (StrothTypeIndex.t200 m).k) :
    (dD.ofTorus v₀ * dD.d8 false false l * (f * e))⁻¹ * dD.ofTorus w *
        (dD.ofTorus v₀ * dD.d8 false false l * (f * e)) =
      dD.ofTorus ((dD.t200gEAction hrel_e hrel_f hconj).φe
        (if l then (StrothTypeIndex.t200 m).action.φu w else w)) := by
  have hD : dD.ofTorus (-v₀) * dD.ofTorus w * dD.ofTorus v₀ = dD.ofTorus w := by
    rw [← dD.ofTorus_add, ← dD.ofTorus_add, neg_add_cancel_comm]
  cases l
  · simp only [d8_fff, mul_one, Bool.false_eq_true, ↓reduceIte]
    rw [show (dD.ofTorus v₀ * (f * e))⁻¹ * dD.ofTorus w * (dD.ofTorus v₀ * (f * e)) =
        (f * e)⁻¹ * (dD.ofTorus (-v₀) * dD.ofTorus w * dD.ofTorus v₀) * (f * e) by
          rw [dD.ofTorus_neg]; group, hD, (dD.t200gEAction hrel_e hrel_f hconj).conj_ofTorus]
  · simp only [d8_fft, ↓reduceIte]
    rw [show (dD.ofTorus v₀ * dD.u * (f * e))⁻¹ * dD.ofTorus w * (dD.ofTorus v₀ * dD.u * (f * e)) =
        (f * e)⁻¹ * (dD.u⁻¹ * (dD.ofTorus (-v₀) * dD.ofTorus w * dD.ofTorus v₀) * dD.u) * (f * e) by
          rw [dD.ofTorus_neg]; group, hD, dD.conj_ofTorus dD.u_mem dD.u_conj,
      (dD.t200gEAction hrel_e hrel_f hconj).conj_ofTorus]

theorem t200k_fix_int (hm : 1 ≤ m) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (l : Bool) (x : Fin 3 → ℤ)
    (hw : (dD.t200gEAction hrel_e hrel_f hconj).φe
        (if l then (StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ x) else Torus.ofInt _ x) =
      Torus.ofInt _ x) :
    (2 : ℤ) ^ m ∣ 2 * x 0 ∧ (if l then (2 : ℤ) ^ (m + 2) ∣ x 1 + (1 + 2 ^ (m + 1)) * x 2 else
      (2 : ℤ) ^ (m + 2) ∣ 2 * x 1 ∧ (2 : ℤ) ^ (m + 2) ∣ 2 * x 2) := by
  have hco : IsCoprime ((2 : ℤ) ^ (m + 1)) (1 + 2 ^ m) := by
    refine ⟨2 ^ (m - 1), 1 - 2 ^ m, ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hhalf : ∀ y : ℤ, (2 : ℤ) ^ (m + 2) ∣ (1 + (1 + 2 ^ (m + 1))) * y →
      (2 : ℤ) ^ (m + 2) ∣ 2 * y := by
    intro y hy
    rw [show (1 + (1 + 2 ^ (m + 1)) : ℤ) * y = 2 * ((1 + 2 ^ m) * y) by ring,
      show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by ring] at hy
    have h1 := (mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ) ≠ 0)).mp hy
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by ring]
    exact mul_dvd_mul_left 2 (hco.dvd_of_dvd_mul_left h1)
  cases l
  · simp only [Bool.false_eq_true, ↓reduceIte, t200gEAction_φe_apply, t200_ofInt_eq_iff] at hw
    obtain ⟨h0, h1, h2⟩ := hw
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0 h1 h2
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by rw [show 2 * x 0 = x 0 - -x 0 by ring]; exact h0, hhalf _ ?_, hhalf _ ?_⟩
    · rw [show (1 + (1 + 2 ^ (m + 1)) : ℤ) * x 1 = x 1 - -((1 + 2 ^ (m + 1)) * x 1) by ring]
      exact h1
    · rw [show (1 + (1 + 2 ^ (m + 1)) : ℤ) * x 2 = x 2 - -((1 + 2 ^ (m + 1)) * x 2) by ring]
      exact h2
  · simp only [↓reduceIte, t200_φu, t200gEAction_φe_apply, t200_ofInt_eq_iff] at hw
    obtain ⟨h0, h1, -⟩ := hw
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0 h1
    simp only [↓reduceIte]
    refine ⟨by rw [show 2 * x 0 = x 0 - -x 0 by ring]; exact h0, ?_⟩
    rw [show x 1 + (1 + 2 ^ (m + 1)) * x 2 = x 1 - -((1 + 2 ^ (m + 1)) * x 2) by ring]
    exact h1

theorem t200k_card_centralizer_D_le (hm : 1 ≤ m) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (l : Bool) :
    Nat.card ↥(D ⊓ Subgroup.centralizer {dD.ofTorus v₀ * dD.d8 false false l * (f * e)}) ≤
      2 ^ (m + 4) := by
  classical
  set y := dD.ofTorus v₀ * dD.d8 false false l * (f * e) with hy
  set C := D ⊓ Subgroup.centralizer {y} with hC
  set coord : ↥C → Torus (StrothTypeIndex.t200 m).k :=
    fun d => dD.e (Additive.ofMul ⟨d.1, (Subgroup.mem_inf.mp d.2).1⟩) with hcoord
  have hcoord_eq : ∀ d : ↥C, dD.ofTorus (coord d) = d.1 := fun d => dD.ofTorus_e _
  have hfix : ∀ d : ↥C, (dD.t200gEAction hrel_e hrel_f hconj).φe
      (if l then (StrothTypeIndex.t200 m).action.φu (coord d) else coord d) = coord d := by
    intro d
    apply dD.ofTorus_inj
    rw [← t200k_conj_ofTorus_y dD hrel_e hrel_f hconj v₀ l, hcoord_eq]
    have hdy : y * d.1 = d.1 * y :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp d.2).2 y rfl
    calc y⁻¹ * d.1 * y = y⁻¹ * (d.1 * y) := by group
      _ = y⁻¹ * (y * d.1) := by rw [hdy]
      _ = d.1 := by group
  set F : ↥C → Bool × Bool × ZMod (2 ^ (StrothTypeIndex.t200 m).k 2) :=
    fun d => (decide (coord d 0 = 0), decide (coord d 1 = 0), coord d 2) with hF
  have hk0 : ((2 ^ (StrothTypeIndex.t200 m).k 0 : ℕ) : ℤ) = 2 ^ m := by push_cast; rfl
  have hk1 : ((2 ^ (StrothTypeIndex.t200 m).k 1 : ℕ) : ℤ) = 2 ^ (m + 2) := by push_cast; rfl
  have hk2 : ((2 ^ (StrothTypeIndex.t200 m).k 2 : ℕ) : ℤ) = 2 ^ (m + 2) := by push_cast; rfl
  have hFinj : Function.Injective F := by
    intro d d' hdd'
    simp only [hF, Prod.mk.injEq, decide_eq_decide] at hdd'
    obtain ⟨h0, h1, h2⟩ := hdd'
    have hfd := hfix d
    have hfd' := hfix d'
    obtain ⟨x, hx⟩ := Torus.exists_ofInt (coord d)
    obtain ⟨x', hx'⟩ := Torus.exists_ofInt (coord d')
    rw [← hx] at hfd h0 h1 h2
    rw [← hx'] at hfd' h0 h1 h2
    obtain ⟨c0, c12⟩ := t200k_fix_int dD hm hrel_e hrel_f hconj l x hfd
    obtain ⟨c0', c12'⟩ := t200k_fix_int dD hm hrel_e hrel_f hconj l x' hfd'
    simp only [Torus.ofInt_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, hk0, hk1] at h0 h1
    simp only [Torus.ofInt_apply, ZMod.intCast_eq_intCast_iff_dvd_sub, hk2] at h2
    have hw : Torus.ofInt (StrothTypeIndex.t200 m).k x = Torus.ofInt _ x' := by
      rw [t200_ofInt_eq_iff]
      refine ⟨Stroth47.dvd_sub_of_dvd_two_mul (M := 2 ^ (m - 1)) (by
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring) (by positivity) c0 c0' h0, ?_, h2⟩
      cases l
      · simp only [Bool.false_eq_true, ↓reduceIte] at c12 c12'
        exact Stroth47.dvd_sub_of_dvd_two_mul (M := 2 ^ (m + 1)) (by ring) (by positivity)
          c12.1 c12'.1 h1
      · simp only [↓reduceIte] at c12 c12'
        have := dvd_sub (dvd_sub c12' c12) (dvd_mul_of_dvd_right h2 (1 + 2 ^ (m + 1)))
        rwa [show x' 1 + (1 + 2 ^ (m + 1)) * x' 2 - (x 1 + (1 + 2 ^ (m + 1)) * x 2) -
          (1 + 2 ^ (m + 1)) * (x' 2 - x 2) = x' 1 - x 1 by ring] at this
    apply Subtype.ext
    rw [← hcoord_eq d, ← hcoord_eq d', ← hx, ← hx', hw]
  calc Nat.card ↥C ≤ Nat.card (Bool × Bool × ZMod (2 ^ (StrothTypeIndex.t200 m).k 2)) :=
        Nat.card_le_card_of_injective F hFinj
    _ = 2 ^ (m + 4) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool),
          Fintype.card_bool]
        show 2 * (2 * 2 ^ (m + 2)) = 2 ^ (m + 4)
        ring

variable [Finite G]

theorem t200k_card_centralizer_le (hm : 1 ≤ m) (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (l : Bool)
    (hyy : dD.ofTorus v₀ * dD.d8 false false l * (f * e) *
      (dD.ofTorus v₀ * dD.d8 false false l * (f * e)) = (dD.c : G) ^ 2 ^ (m - 1)) :
    Nat.card ↥((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔
      Subgroup.zpowers e) ⊓
        Subgroup.centralizer {dD.ofTorus v₀ * dD.d8 false false l * (f * e)}) ≤ 2 ^ (m + 7) := by
  set y := dD.ofTorus v₀ * dD.d8 false false l * (f * e) with hy
  set C := (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔
    Subgroup.zpowers e) ⊓ Subgroup.centralizer {y} with hC
  have hCT : C ≤ D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e := by
    intro s hs
    obtain ⟨hsS, hsy⟩ := Subgroup.mem_inf.mp hs
    refine t200k_mem_of_comm_c₁ dD hm heN hfN hrel_e hrel_f hconj s hsS ?_
    have h : y * s = s * y := Subgroup.mem_centralizer_iff.mp hsy y rfl
    rw [← hyy]
    calc s * (y * y) = s * y * y := by group
      _ = y * s * y := by rw [h]
      _ = y * (s * y) := by group
      _ = y * (y * s) := by rw [h]
      _ = y * y * s := by group
  have hidx := t200k_relIndex_dvd dD heN hfN hrel_e hrel_f hconj
  have hidx0 : D.relIndex (D ⊔ Subgroup.zpowers dD.u ⊔ Subgroup.zpowers f ⊔
      Subgroup.zpowers e) ≠ 0 := fun h0 => by
    rw [h0] at hidx
    norm_num at hidx
  have h1 : D.relIndex C ≤ 8 :=
    (Subgroup.relIndex_le_of_le_right hCT hidx0).trans (Nat.le_of_dvd (by norm_num) hidx)
  have h2 : Nat.card ↥(D ⊓ C) ≤ 2 ^ (m + 4) :=
    (Subgroup.card_le_of_le (inf_le_inf_left D inf_le_right)).trans
      (t200k_card_centralizer_D_le dD hm hrel_e hrel_f hconj v₀ l)
  rw [← Subgroup.relIndex_mul_card D C]
  calc D.relIndex C * Nat.card ↥(D ⊓ C) ≤ 8 * 2 ^ (m + 4) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (m + 7) := by ring

theorem t200k_card_sup_e (hm : 1 ≤ m) (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hrel_e : Rel34i dD e (2 ^ (m + 1))) :
    Nat.card ↥(D ⊔ Subgroup.zpowers e) = 2 ^ (3 * m + 5) := by
  have heD : e ∉ D := fun h => t200_i_h2 dD hm hrel_e (Subgroup.mem_sup_left h)
  have hidx := Stroth47.relIndex_sup_zpowers_of_mul_self_mem heN
    (by rw [hrel_e.e_sq]; exact D.inv_mem dD.c.2) heD
  have h := Subgroup.relIndex_mul_card D (D ⊔ Subgroup.zpowers e)
  rw [inf_of_le_left le_sup_left, hidx, dD.card] at h
  rw [← h]
  show 2 * 2 ^ (m + (m + 2) + (m + 2)) = 2 ^ (3 * m + 5)
  ring

theorem t200k_sup_e_le_centralizer (hrel_e : Rel34i dD e (2 ^ (m + 1))) {k : ℕ} (hk : 1 ≤ k) :
    D ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer {e ^ 2 ^ k} := by
  haveI := dD.isMulCommutative
  have hmem : e ^ 2 ^ k ∈ D := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ', pow_mul, sq, hrel_e.e_sq]
    exact D.pow_mem (D.inv_mem dD.c.2) _
  refine sup_le (fun d hd => ?_) (Subgroup.zpowers_le.mpr ?_)
  · rw [Subgroup.mem_centralizer_iff]
    rintro z rfl
    exact Subgroup.mul_comm_of_mem_isMulCommutative D hmem hd
  · rw [Subgroup.mem_centralizer_iff]
    rintro z rfl
    exact ((Commute.refl e).pow_left _).eq

theorem t200k_h8c (hm1 : 1 ≤ m) (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (he1 : e ^ 2 ^ (m + 1) = 1) (hz1 : (dD.c : G) ^ 2 ^ (m - 1) ≠ 1)
    (hSp : IsPGroup 2 ↥(D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔
      Subgroup.zpowers e)) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f →
      y * y = (dD.c : G) ^ 2 ^ (m - 1) → ∀ (g : G) (k : ℕ), 1 ≤ k → y = g⁻¹ * e ^ 2 ^ k * g →
      2 ^ (k + 1) * Nat.card ↥((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔
        Subgroup.zpowers e) ⊓ Subgroup.centralizer {y}) ∣
        Nat.card ↥(Subgroup.centralizer {e ^ 2 ^ k}) := by
  intro y hyS hyU hyy g k hk hyg
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hkm : k + 1 ≤ m := by
    by_contra hkm
    apply hz1
    rw [← hyy, hyg, show g⁻¹ * e ^ 2 ^ k * g * (g⁻¹ * e ^ 2 ^ k * g) =
      g⁻¹ * (e ^ 2 ^ k * e ^ 2 ^ k) * g by group, ← pow_add,
      show 2 ^ k + 2 ^ k = 2 ^ (m + 1) * 2 ^ (k - m) by
        rw [← pow_add, show m + 1 + (k - m) = k + 1 by omega, pow_succ]; ring,
      pow_mul, he1, one_pow]
    group
  obtain ⟨w, hw, kk, rfl⟩ := (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem
    (t200k_mem_normalizer dD heN hfN hrel_e hrel_f hconj) (t200k_e_mul_self_mem dD hrel_e)).mp hyS
  cases kk
  · exact absurd (by simpa [bpow] using hw) hyU
  simp only [bpow, ↓reduceIte] at hyU hyy hyg ⊢
  obtain ⟨v, i, j, l, k', rfl⟩ := (dD.t200fEAction hrel_f).mem_sup_zpowers_iff.mp hw
  cases k'
  ·
    exfalso
    simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyy hyg hyU
    refine t200_i_h8 dD hm1 hrel_e _ ?_ ?_ 1 le_rfl (by rw [pow_one, sq]; exact hyy) ?_
    · exact mul_mem (Subgroup.mem_sup_left (dD.nf_mem v i j l))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    · intro hmem
      apply t200_i_h2 dD hm1 hrel_e
      have := (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).mul_mem
        ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).inv_mem (dD.nf_mem v i j l)) hmem
      rwa [inv_mul_cancel_left] at this
    · rw [hyg, Stroth42.conj_pow', ← pow_mul, ← pow_add,
        show k + m = (m + 1) + (k - 1) by omega, pow_add, pow_mul, he1, one_pow]
      group
  simp only [bpow, ↓reduceIte] at hyy hyg hyU ⊢
  set X := dD.ofTorus v * dD.d8 i j l with hXdef
  have hy' : X * f * e = X * (f * e) := by group
  rw [hy'] at hyy hyg ⊢
  have hfc := t200k_f_comm_c₁ dD hm1 hrel_f
  have hec := t200k_e_comm_c₁ dD hrel_e
  rw [← hz] at hfc hec
  have hgz : f * e * z = z * (f * e) := by
    rw [mul_assoc, hec, ← mul_assoc, hfc, mul_assoc]
  have hyz : X * (f * e) * z = z * (X * (f * e)) := by
    rw [← hyy]
    group
  have hX : X * z = z * X := by
    have h1 : X * z * (f * e) = z * X * (f * e) := by
      rw [mul_assoc X z, ← hgz, ← mul_assoc, hyz, ← mul_assoc]
    exact mul_right_cancel h1
  obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm1 hX
  have hcard := t200k_card_centralizer_le dD hm1 heN hfN hrel_e hrel_f hconj v l hyy
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hSp.to_le (inf_le_left :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {X * (f * e)} ≤ _))
  rw [ha] at hcard ⊢
  have ha' : a ≤ m + 7 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  have hDe := Subgroup.card_dvd_of_le (t200k_sup_e_le_centralizer dD hrel_e hk)
  rw [t200k_card_sup_e dD hm1 heN hrel_e] at hDe
  rw [← pow_add]
  exact (pow_dvd_pow 2 (by omega)).trans hDe

end Stroth47Core

end CFSG.CGT.Stroth77
