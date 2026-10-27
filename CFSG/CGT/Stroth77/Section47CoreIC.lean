module

public import CFSG.CGT.Stroth77.Section47CoreI
public import CFSG.CGT.Stroth77.Section44CoreII

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))

open StrothWeakTypeData

theorem t200_mem_CSc₁ (hm : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l : Bool),
      y = dD.ofTorus v * dD.d8 false false l := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hyS
  rw [Subgroup.mem_centralizer_iff] at hyC
  have hc := hyC _ (Set.mem_singleton _)
  obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hc.symm
  exact ⟨v, l, rfl⟩

theorem t200_mem_CSc₁_of_not_mem (hm : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) (hyD : y ∉ D) :
    ∃ v : Torus (StrothTypeIndex.t200 m).k, y = dD.ofTorus v * dD.d8 false false true := by
  obtain ⟨v, l, rfl⟩ := t200_mem_CSc₁ dD hm hy
  cases l
  · exact absurd (by rw [dD.d8_fff, mul_one]; exact dD.ofTorus_mem v) hyD
  · exact ⟨v, rfl⟩

theorem t200_h7 (hm : 1 ≤ m) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ y ∈ E, y * y = 1) →
        Nat.card E ≠ 16 := by
  intro E hE hinv hcard
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have hD1 : ∀ e ∈ E, e ∈ D → ∃ a b c : Bool,
      e = dD.ofTorus (om200 m ![(a.toNat : ℤ), b.toNat, c.toNat]) := by
    intro e he heD
    obtain ⟨ε, hε, rfl⟩ := dD.t200_eq_om_of_mul_self hm heD (hinv e he)
    refine ⟨decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1), ?_⟩
    congr 2
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by simp [Nat.card_eq_fintype_card]
  by_cases hD : ∃ e₀ ∈ E, e₀ ∉ D
  · obtain ⟨e₀, he₀, he₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := t200_mem_CSc₁_of_not_mem dD hm (hE he₀) he₀D
    have hfix : ∀ d ∈ E, d ∈ D → ∃ a b : Bool,
        d = dD.ofTorus (om200 m ![(a.toNat : ℤ), b.toNat, b.toNat]) := by
      intro d hd hdD
      obtain ⟨a, b, c, rfl⟩ := hD1 d hd hdD
      have hc := hcomm _ hd _ he₀
      rw [hv₀] at hc
      have hω := (dD.nf_commute_iff v₀ _ false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, t200_φu_om, om200_eq_iff hm] at hω
      have h1 := hω 1
      have hbc : c = b := by
        revert h1
        cases a <;> cases b <;> cases c <;> decide
      exact ⟨a, b, by rw [hbc]⟩
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om200 m ![(w.2.1.toNat : ℤ), w.2.2.toNat, w.2.2.toNat]) *
        (if w.1 then e₀ else 1)
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨a, b, hd⟩ := hfix e he heD
        exact ⟨(false, a, b), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := t200_mem_CSc₁_of_not_mem dD hm (hE he) heD
        have hmem : e * e₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        obtain ⟨a, b, hd⟩ := hfix (e * e₀⁻¹) (mul_mem he (inv_mem he₀)) hmem
        refine ⟨(true, a, b), ?_⟩
        simp only [f, if_true]
        rw [← hd, inv_mul_cancel_right]
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om200 m ![(w.1.toNat : ℤ), w.2.1.toNat, w.2.2.toNat])
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      obtain ⟨a, b, c, hd⟩ := hD1 e he (hD e he)
      exact ⟨(a, b, c), hd.symm⟩
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega


section CaseI

variable {e : G} (hE : dD.EAction e)

theorem t200_i_φe (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (x : Fin 3 → ℤ) : hE.φe (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0, (1 + 2 ^ (m + 1)) * x 1, (1 + 2 ^ (m + 1)) * x 2] := by
  rw [hφe, torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200_d8Act_c₁ (hm : 1 ≤ m) {i j l : Bool}
    (h : (StrothTypeIndex.t200 m).action.d8Act i j l (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0]) :
    i = false ∧ j = false := by
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t200_φuv_om hm, t200_φt_om hm, t200_φu_om, om200_eq_iff hm] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t200_i_mem_of_mul_self (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (hve : hE.ve = Torus.ofInt _ ![-1, 0, 0]) {y : G}
    (hy : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hyc : y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y) (hy2 : y * y = 1) :
    y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · simpa [bpow] using dD.nf_mem v i j l
  exfalso
  simp only [bpow, ↓reduceIte] at hyc hy2
  have hc₁ : hE.φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0] := by
    rw [om200_apply, t200_i_φe dD hE hφe]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [dD.t200_c_pow, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
    mul_left_inj] at hyc
  obtain ⟨rfl, rfl⟩ := t200_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
  rw [hE.nfe_e_mul_self, Bool.and_false, dD.d8_fff, mul_one, dD.ofTorus_eq_one_iff] at hy2
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have h0 := congrFun hy2 0
  simp only [EAction.sqE, EAction.twist, hve, Bool.false_eq_true, ↓reduceIte,
    SigmaFourAction.d8Act, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Bool.and_false,
    map_zero, add_zero] at h0
  have hk0 : (StrothTypeIndex.t200 m).k 0 ≠ 0 := by
    simp [StrothTypeIndex.k, Type200.k]
    omega
  have hodd : ∀ z : ℤ, ((2 * z - 1 : ℤ) : ZMod (2 ^ (StrothTypeIndex.t200 m).k 0)) ≠ 0 := by
    intro z hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have h2 : (2 : ℤ) ∣ 2 * z - 1 := dvd_trans (dvd_pow_self 2 hk0) (by exact_mod_cast hz)
    omega
  apply hodd (x 0)
  cases l <;>
    simp only [Bool.false_eq_true, ↓reduceIte, AddMonoidHom.id_apply, map_add, map_sub,
      t200_i_φe dD hE hφe, t200_φu, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Torus.ofInt_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0 <;>
    push_cast <;> linear_combination h0

theorem t200_i_h7 (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (hve : hE.ve = Torus.ofInt _ ![-1, 0, 0]) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ y ∈ E, y * y = 1) →
        Nat.card E ≠ 16 := by
  intro E hES hinv
  refine t200_h7 dD hm E (fun y hy => ?_) hinv
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp (hES hy)
  exact Subgroup.mem_inf.mpr ⟨t200_i_mem_of_mul_self dD hE hm hφe hve hyS
    (Subgroup.mem_centralizer_singleton_iff.mp hyC) (hinv y hy), hyC⟩

theorem t200_i_mem_CSc₁ (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyc := Subgroup.mem_centralizer_singleton_iff.mp hyC
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  have hc₁ : hE.φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0] := by
    rw [om200_apply, t200_i_φe dD hE hφe]
    congr 1
    funext i
    fin_cases i <;> simp
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyc
    obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hyc
    exact ⟨v, l, false, rfl⟩
  · simp only [bpow, ↓reduceIte] at hyc
    rw [dD.t200_c_pow, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
      mul_left_inj] at hyc
    obtain ⟨rfl, rfl⟩ := t200_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
    exact ⟨v, l, true, rfl⟩

theorem t200_e_comm_iff (v₀ w : Torus (StrothTypeIndex.t200 m).k) (l k : Bool) :
    dD.ofTorus w * (dD.ofTorus v₀ * dD.d8 false false l * bpow e k) =
        dD.ofTorus v₀ * dD.d8 false false l * bpow e k * dD.ofTorus w ↔
      (StrothTypeIndex.t200 m).action.d8Act false false l (if k then hE.φe w else w) = w := by
  have hk : bpow e k * dD.ofTorus w = dD.ofTorus (if k then hE.φe w else w) * bpow e k := by
    cases k
    · simp [bpow]
    · simp only [bpow, ↓reduceIte]
      exact hE.e_mul_ofTorus w
  have hL : dD.ofTorus w * (dD.ofTorus v₀ * dD.d8 false false l * bpow e k) =
      dD.ofTorus (v₀ + w) * dD.d8 false false l * bpow e k := by
    rw [← mul_assoc, ← mul_assoc, ← dD.ofTorus_add, add_comm w v₀]
  have hR : dD.ofTorus v₀ * dD.d8 false false l * bpow e k * dD.ofTorus w =
      dD.ofTorus (v₀ + (StrothTypeIndex.t200 m).action.d8Act false false l
        (if k then hE.φe w else w)) * dD.d8 false false l * bpow e k := by
    rw [mul_assoc _ (bpow e k), hk, ← mul_assoc, mul_assoc (dD.ofTorus v₀), dD.d8_mul_ofTorus,
      ← mul_assoc, ← dD.ofTorus_add]
  rw [hL, hR, mul_left_inj, mul_left_inj, dD.ofTorus_inj.eq_iff]
  exact ⟨fun h => (add_left_cancel h).symm, fun h => by rw [h]⟩

theorem nfe_mul_inv_mem (v v' : Torus (StrothTypeIndex.t200 m).k) (l k : Bool) :
    dD.ofTorus v * dD.d8 false false l * bpow e k *
      (dD.ofTorus v' * dD.d8 false false l * bpow e k)⁻¹ ∈ D := by
  have h : dD.ofTorus v * dD.d8 false false l * bpow e k *
      (dD.ofTorus v' * dD.d8 false false l * bpow e k)⁻¹ = dD.ofTorus v * (dD.ofTorus v')⁻¹ := by
    group
  rw [h]
  exact mul_mem (dD.ofTorus_mem _) (inv_mem (dD.ofTorus_mem _))

theorem card_le_of_cover {X : Subgroup G} {ι T : Type*} [Finite ι] [Finite T] (r : ι → G)
    (hr : ∀ j, r j ∈ X) (hcov : ∀ y ∈ X, ∃ j, y * (r j)⁻¹ ∈ D)
    (g : T → Torus (StrothTypeIndex.t200 m).k) (hg : ∀ d ∈ X, d ∈ D → ∃ s, d = dD.ofTorus (g s)) :
    Nat.card X ≤ Nat.card (ι × T) := by
  refine Stroth42Core.natCard_le_of_subset_range (fun w : ι × T => dD.ofTorus (g w.2) * r w.1)
    (fun y hy => ?_)
  obtain ⟨j, hj⟩ := hcov y hy
  obtain ⟨s, hs⟩ := hg _ (mul_mem hy (inv_mem (hr j))) hj
  exact ⟨(j, s), by simp only; rw [← hs, inv_mul_cancel_right]⟩

theorem t200_i_comm_u (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (k : Bool) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus v₀ * dD.d8 false false true * bpow e k) =
      dD.ofTorus v₀ * dD.d8 false false true * bpow e k * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ^ (m + 2) ∣ x 1 - (if k then 1 + 2 ^ (m + 1) else 1) * x 2 := by
  have hc := (t200_e_comm_iff dD hE v₀ _ true k).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  cases k
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [t200_φu, t200_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1
  · simp only [↓reduceIte] at hc ⊢
    rw [t200_i_φe dD hE hφe, t200_φu, t200_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1

theorem t200_i_comm_e (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus v₀ * dD.d8 false false false * bpow e true) =
      dD.ofTorus v₀ * dD.d8 false false false * bpow e true * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ∣ x 1 ∧ (2 : ℤ) ∣ x 2 := by
  have hc := (t200_e_comm_iff dD hE v₀ _ false true).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  rw [t200_i_φe dD hE hφe, t200_ofInt_eq_iff] at hc
  obtain ⟨-, h1, h2⟩ := hc
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2
  have key : ∀ y : ℤ, (2 : ℤ) ^ (m + 2) ∣ y - (1 + 2 ^ (m + 1)) * y → (2 : ℤ) ∣ y := by
    intro y hy
    obtain ⟨c, hc⟩ := hy
    have e : y - (1 + 2 ^ (m + 1)) * y = 2 ^ (m + 1) * (-y) := by ring
    rw [e, pow_succ (2 : ℤ) (m + 1)] at hc
    have hne : (2 : ℤ) ^ (m + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hc' : -y = 2 * c := mul_left_cancel₀ hne (hc.trans (by ring))
    exact ⟨-c, by linarith⟩
  exact ⟨key _ h1, key _ h2⟩

theorem t200_i_h9 (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  classical
  intro X hX hab hcard
  have hDcard : Nat.card D = 2 ^ (m + (m + 2) + (m + 2)) := dD.card
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  have hnf : ∀ y ∈ X, ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k :=
    fun y hy => t200_i_mem_CSc₁ dD hE hm hφe (hX hy)
  let rep : Bool × Bool → G := fun lk =>
    if h : ∃ y ∈ X, ∃ v, y = dD.ofTorus v * dD.d8 false false lk.1 * bpow e lk.2 then h.choose
    else 1
  have hrep : ∀ y ∈ X, ∀ v l k, y = dD.ofTorus v * dD.d8 false false l * bpow e k →
      y * (rep (l, k))⁻¹ ∈ D := by
    intro y hy v l k hyv
    have h : ∃ y ∈ X, ∃ v, y = dD.ofTorus v * dD.d8 false false l * bpow e k := ⟨_, hy, v, hyv⟩
    simp only [rep, h, dite_true]
    obtain ⟨-, v', hv'⟩ := h.choose_spec
    rw [hv', hyv]
    exact nfe_mul_inv_mem dD v v' l k
  have hrepX : ∀ lk, rep lk ∈ X := by
    intro lk
    simp only [rep]
    split_ifs with h
    · exact h.choose_spec.1
    · exact X.one_mem
  by_cases hD : ∀ x ∈ X, x ∈ D
  · haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge hD hcard.ge
  exfalso
  push Not at hD
  obtain ⟨x₁, hx₁, hx₁D⟩ := hD
  have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  by_cases hA : ∃ x₀ ∈ X, ∃ v₀ k₀, x₀ = dD.ofTorus v₀ * dD.d8 false false true * bpow e k₀
  · obtain ⟨x₀, hx₀, v₀, k₀, rfl⟩ := hA
    set γ : ℤ := if k₀ then 1 + 2 ^ (m + 1) else 1 with hγ
    have hle := card_le_of_cover dD rep hrepX
      (fun y hy => by
        obtain ⟨v, l, k, hyv⟩ := hnf y hy
        exact ⟨(l, k), hrep y hy v l k hyv⟩)
      (fun s : ZMod (2 ^ m) × ZMod (2 ^ (m + 2)) =>
        Torus.ofInt _ ![(s.1.val : ℤ), γ * (s.2.val : ℤ), (s.2.val : ℤ)])
      (by
        intro d hd hdD
        obtain ⟨w, rfl⟩ := dD.exists_ofTorus hdD
        obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
        have h1 := t200_i_comm_u dD hE hφe v₀ k₀ x (hcomm _ hd _ hx₀)
        refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((x 2 : ℤ) : ZMod (2 ^ (m + 2)))), ?_⟩
        congr 1
        rw [t200_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        have e0 := Stroth44Core.dvd_sub_val (2 ^ m) (x 0)
        have e2 := Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 2)
        push_cast at e0 e2
        refine ⟨e0, ?_, e2⟩
        have := dvd_sub (Dvd.dvd.mul_left e2 γ) h1
        convert this using 1
        ring)
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
      Nat.card_zmod, h2, show 2 * 2 * (2 ^ m * 2 ^ (m + 2)) = 2 ^ (m + m + 4) by ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  ·
    push Not at hA
    obtain ⟨v₁, l₁, k₁, rfl⟩ := hnf _ hx₁
    have hl₁ : l₁ = false := by
      cases l₁
      · rfl
      · exact absurd rfl (hA _ hx₁ v₁ k₁)
    subst hl₁
    have hk₁ : k₁ = true := by
      cases k₁
      · exact absurd (by simpa [bpow, dD.d8_fff] using dD.ofTorus_mem v₁) hx₁D
      · rfl
    subst hk₁
    have hle := card_le_of_cover dD (fun k : Bool => rep (false, k)) (fun k => hrepX _)
      (fun y hy => by
        obtain ⟨v, l, k, hyv⟩ := hnf y hy
        have hl : l = false := by
          cases l
          · rfl
          · exact absurd hyv (hA y hy v k)
        subst hl
        exact ⟨k, hrep y hy v false k hyv⟩)
      (fun s : ZMod (2 ^ m) × ZMod (2 ^ (m + 1)) × ZMod (2 ^ (m + 1)) =>
        Torus.ofInt _ ![(s.1.val : ℤ), 2 * (s.2.1.val : ℤ), 2 * (s.2.2.val : ℤ)])
      (by
        intro d hd hdD
        obtain ⟨w, rfl⟩ := dD.exists_ofTorus hdD
        obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
        obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩ := t200_i_comm_e dD hE hφe v₁ x (hcomm _ hd _ hx₁)
        refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((y₁ : ℤ) : ZMod (2 ^ (m + 1))),
          ((y₂ : ℤ) : ZMod (2 ^ (m + 1)))), ?_⟩
        congr 1
        rw [t200_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        have e0 := Stroth44Core.dvd_sub_val (2 ^ m) (x 0)
        have e1 := Stroth44Core.dvd_sub_val (2 ^ (m + 1)) y₁
        have e2 := Stroth44Core.dvd_sub_val (2 ^ (m + 1)) y₂
        push_cast at e0 e1 e2
        refine ⟨e0, ?_, ?_⟩
        · obtain ⟨c, hc⟩ := e1
          exact ⟨c, by rw [hy₁, pow_succ (2 : ℤ) (m + 1)]; linear_combination 2 * hc⟩
        · obtain ⟨c, hc⟩ := e2
          exact ⟨c, by rw [hy₂, pow_succ (2 : ℤ) (m + 1)]; linear_combination 2 * hc⟩)
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
      Nat.card_zmod, h2, show 2 * (2 ^ m * (2 ^ (m + 1) * 2 ^ (m + 1))) = 2 ^ (m + m + m + 3) by
        ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega


theorem t200_i_h8 (hm : 1 ≤ m) (hrel : Rel34i dD e (2 ^ (m + 1))) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ m ≠ 1 := by
  intro y hy hyU l hl hyl hy1
  have hyc : y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y := by
    rw [← hyl]; exact ((Commute.refl y).pow_right _).eq
  obtain ⟨v, l', k, rfl⟩ := t200_i_mem_CSc₁ dD (dD.t200iAction hrel) hm (dD.t200iAction_φe hrel)
    (Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyc⟩)
  cases k
  · exact hyU (by simpa [bpow] using dD.nf_mem v false false l')
  · simp only [bpow, ↓reduceIte] at hy1
    rw [pow_two_pow_eq_mul_self _ hm, (dD.t200iAction hrel).nfe_e_mul_self, Bool.and_false,
      d8_fff, mul_one, ← ofTorus_nsmul, ofTorus_eq_one_iff] at hy1
    obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [EAction.sqE, EAction.twist, t200iAction_φe, t200iAction_ve, t200iAction_wuv,
      t200iAction_wt] at hy1
    cases l' <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, Bool.and_false, map_add, map_sub, map_zero, torusDiag_ofInt,
      t200_φu, ← Torus.ofInt_add, ← Torus.ofInt_sub, add_zero, zero_add, ← natCast_zsmul,
      ← Torus.ofInt_zsmul, t200_ofInt_eq_zero_iff, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.add_sub_cancel] at hy1 <;>
    obtain ⟨⟨k0, hk0⟩, -, -⟩ := hy1 <;>
    push_cast at hk0 <;>
    · have h2 : (2 : ℤ) ^ m' * (2 * x0 - 1) = 2 ^ m' * (2 * k0) := by linear_combination hk0
      have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
      omega

end CaseI


end Stroth47Core

end CFSG.CGT.Stroth77
