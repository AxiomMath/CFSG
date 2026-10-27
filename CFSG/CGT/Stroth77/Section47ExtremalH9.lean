module

public import CFSG.CGT.Stroth77.Section47Extremal
public import CFSG.CGT.Stroth77.Section47CoreIC

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core StrothWeakTypeData

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ}

theorem torusDiag_om200_of_odd (hm : 1 ≤ m) {d : Fin 3 → ℤ}
    (h0 : d 0 % 2 = 1) (h1 : d 1 % 2 = 1) (h2 : d 2 % 2 = 1) (ε : Fin 3 → ℤ) :
    torusDiag _ d (om200 m ε) = om200 m ε := by
  rw [om200, torusDiag_ofInt]
  rw [show (fun i => d i * (ε i * 2 ^ ((StrothTypeIndex.t200 m).k i - 1))) =
    fun i => (d i * ε i) * 2 ^ ((StrothTypeIndex.t200 m).k i - 1) by funext i; ring]
  refine (om200_eq_iff hm _ _).mpr fun i => ?_
  have hd : ∀ i, d i % 2 = 1 := by intro i; fin_cases i <;> assumption
  have := hd i
  simp only [Int.ModEq, Int.mul_emod, this, one_mul, Int.emod_emod_of_dvd, Int.emod_emod]

end Stroth47Core

namespace StrothWeakTypeData

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

@[expose] def t200invEAction {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) : dD.EAction e where
  φe := torusDiag _ ![-1, -1 + (2 : ℤ) ^ (m + 1), -1 + (2 : ℤ) ^ (m + 1)]
  wuv := Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]
  wt := Torus.ofInt _ ![0, -(p : ℤ), 0]
  ve := Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0]
  conj_ofTorus := dD.conj_ofTorus_of_gens
    (by rw [hrel.c_conj, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
    (by
      rw [hrel.a_conj, torusDiag_gen, ofTorus_zsmul, ← a_eq,
        show (![-1, -1 + (2 : ℤ) ^ (m + 1), -1 + (2 : ℤ) ^ (m + 1)] : Fin 3 → ℤ) 1 =
          -1 + (2 : ℤ) ^ (m + 1) from rfl,
        _root_.zpow_add, _root_.zpow_neg_one,
        show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl, zpow_natCast])
    (by
      rw [hrel.b_conj, torusDiag_gen, ofTorus_zsmul, ← b_eq,
        show (![-1, -1 + (2 : ℤ) ^ (m + 1), -1 + (2 : ℤ) ^ (m + 1)] : Fin 3 → ℤ) 2 =
          -1 + (2 : ℤ) ^ (m + 1) from rfl,
        _root_.zpow_add, _root_.zpow_neg_one,
        show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl, zpow_natCast])
  conj_uv := by
    rw [hrel.uv_conj, dD.c_eq, dD.a_eq, dD.b_eq, ← dD.ofTorus_add, ← dD.ofTorus_add,
      ← dD.ofTorus_nsmul, c_eq_ofInt, a_eq_ofInt, b_eq_ofInt, t200_add_vec, t200_add_vec,
      ← natCast_zsmul, t200_zsmul_vec]
    congr 1
    congr 1
    funext i
    fin_cases i <;> simp
  conj_t := by
    rw [hrel.t_conj, dD.a_eq, ← dD.ofTorus_nsmul, ← dD.ofTorus_neg, a_eq_ofInt,
      ← natCast_zsmul, t200_zsmul_vec, t200_neg_vec]
    congr 1
    congr 1
    funext i
    fin_cases i <;> simp
  conj_u := hrel.u_conj
  mul_self := by
    rw [hrel.e_sq, dD.t200_c_pow]
    congr 1
    rw [Stroth47Core.om200_apply]
    congr 1
    funext i
    fin_cases i <;> simp

theorem t200inv_φe {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) (x : Fin 3 → ℤ) :
    (dD.t200invEAction hrel).φe (Torus.ofInt _ x) =
      Torus.ofInt _ ![-(x 0), (-1 + (2 : ℤ) ^ (m + 1)) * x 1,
        (-1 + (2 : ℤ) ^ (m + 1)) * x 2] := by
  change torusDiag _ ![-1, -1 + (2 : ℤ) ^ (m + 1), -1 + (2 : ℤ) ^ (m + 1)]
    (Torus.ofInt _ x) = _
  rw [torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

end StrothWeakTypeData

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200inv_φe_om {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) (hm : 1 ≤ m)
    (ε : Fin 3 → ℤ) :
    (dD.t200invEAction hrel).φe (om200 m ε) = om200 m ε := by
  have hγ : (-1 + (2 : ℤ) ^ (m + 1)) % 2 = 1 :=
    StrothWeakTypeData.neg_one_add_two_pow_emod_two (m := m + 1) (by omega)
  change torusDiag _ ![-1, -1 + (2 : ℤ) ^ (m + 1), -1 + (2 : ℤ) ^ (m + 1)] (om200 m ε) =
    om200 m ε
  exact torusDiag_om200_of_odd hm (by norm_num) hγ hγ ε

theorem t200_inv_mem_CSc₁ {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) (hm : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k := by
  let hE := dD.t200invEAction hrel
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyc := Subgroup.mem_centralizer_singleton_iff.mp hyC
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  have hc₁ : hE.φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0] :=
    t200inv_φe_om dD hrel hm _
  cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyc
    obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hyc
    exact ⟨v, l, false, rfl⟩
  · simp only [Stroth42Core.bpow, ↓reduceIte] at hyc
    rw [dD.t200_c_pow, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
      mul_left_inj] at hyc
    obtain ⟨rfl, rfl⟩ := t200_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
    exact ⟨v, l, true, rfl⟩

theorem t200_inv_comm_u {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (k : Bool) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) *
        (dD.ofTorus v₀ * dD.d8 false false true * bpow e k) =
      dD.ofTorus v₀ * dD.d8 false false true * bpow e k * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ^ (m + 2) ∣ x 1 - (if k then -1 + (2 : ℤ) ^ (m + 1) else 1) * x 2 := by
  let hE := dD.t200invEAction hrel
  have hc := (Stroth47Core.t200_e_comm_iff dD hE v₀ _ true k).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  cases k
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [t200_φu, t200_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1
  · simp only [↓reduceIte] at hc ⊢
    rw [t200inv_φe dD hrel, t200_φu, t200_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1

theorem t200_inv_comm_e {p : ℕ} (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) *
        (dD.ofTorus v₀ * dD.d8 false false false * bpow e true) =
      dD.ofTorus v₀ * dD.d8 false false false * bpow e true * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ∣ x 1 ∧ (2 : ℤ) ∣ x 2 := by
  let hE := dD.t200invEAction hrel
  have hc := (Stroth47Core.t200_e_comm_iff dD hE v₀ _ false true).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  rw [t200inv_φe dD hrel, t200_ofInt_eq_iff] at hc
  obtain ⟨-, h1, h2⟩ := hc
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2
  have key : ∀ y : ℤ, (2 : ℤ) ^ (m + 2) ∣ y - (-1 + (2 : ℤ) ^ (m + 1)) * y →
      (2 : ℤ) ∣ y := by
    intro y hy
    have e : y - (-1 + (2 : ℤ) ^ (m + 1)) * y = 2 * ((1 - 2 ^ m) * y) := by ring
    rw [e] at hy
    obtain ⟨c, hc⟩ := hy
    have hc' : (2 : ℤ) ^ (m + 1) * c = (1 - 2 ^ m) * y := by
      have h2 : (2 : ℤ) ^ (m + 2) = (2 : ℤ) ^ (m + 1) * 2 := by rw [pow_succ]
      rw [h2] at hc
      have hc2 : (2 : ℤ) * ((2 : ℤ) ^ (m + 1) * c) = (2 : ℤ) * ((1 - 2 ^ m) * y) := by
        rw [hc]; ring
      exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) hc2
    have h2dvd : (2 : ℤ) ∣ (2 : ℤ) ^ (m + 1) := by
      exact dvd_pow_self 2 (by omega : m + 1 ≠ 0)
    have heven : (2 : ℤ) ∣ (1 - 2 ^ m) * y := by
      rw [← hc']
      exact dvd_mul_of_dvd_left h2dvd c
    have hodd : ¬ (2 : ℤ) ∣ (1 - 2 ^ m) := by
      have h2m_even : Even ((2 : ℤ) ^ m) :=
        (even_two : Even (2 : ℤ)).pow_of_ne_zero (by omega : m ≠ 0)
      have hodd' : Odd (1 - (2 : ℤ) ^ m) := Odd.sub_even odd_one h2m_even
      intro hd
      exact (Int.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hd)
    rcases Int.prime_two.dvd_mul.mp heven with h | h
    · exact absurd h hodd
    · exact h
  exact ⟨key _ h1, key _ h2⟩

end Stroth47Core

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200_inv_h9 {p : ℕ} (hm : 2 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  classical
  intro X hX hab hcard
  let hE := dD.t200invEAction hrel
  have hDcard : Nat.card D = 2 ^ (m + (m + 2) + (m + 2)) := dD.card
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  have hnf : ∀ y ∈ X, ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k :=
    fun y hy => t200_inv_mem_CSc₁ dD hrel (by omega) (hX hy)
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
    set γ : ℤ := if k₀ then -1 + (2 : ℤ) ^ (m + 1) else 1 with hγ
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
        have h1 := t200_inv_comm_u dD hrel v₀ k₀ x (hcomm _ hd _ hx₀)
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
  · push Not at hA
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
        obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩ := t200_inv_comm_e dD (by omega) hrel v₁ x
          (hcomm _ hd _ hx₁)
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

end Stroth47Core

end CFSG.CGT.Stroth77

namespace CFSG.CGT.Stroth77

theorem H47H9_proved : H47H9 := by
  unfold H47H9
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel X hX hab hcard
  rw [hS] at hX
  rcases hrel with hrel | hrel
  · exact Stroth47Core.t200_inv_h9 dD hm hrel X hX hab hcard
  · exact Stroth47Core.t200_inv_h9 dD hm hrel X hX hab hcard

end CFSG.CGT.Stroth77

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core StrothWeakTypeData

variable {G : Type} [Group G] [Finite G]

theorem H47Extremal_of_normalizer (hNorm : H47Normalizer) : H47Extremal :=
  H47Extremal_of_h9_normalizer H47H9_proved hNorm

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem om200_add (ε δ : Fin 3 → ℤ) :
    om200 m ε + om200 m δ = om200 m (ε + δ) := by
  rw [om200, om200, om200, ← Torus.ofInt_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem om200_bool_eq_iff (hm1 : 1 ≤ m) (b₀ b₁ b₂ c₀ c₁ c₂ : Bool) :
    om200 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)] =
        om200 m ![(c₀.toNat : ℤ), (c₁.toNat : ℤ), (c₂.toNat : ℤ)] ↔
      b₀ = c₀ ∧ b₁ = c₁ ∧ b₂ = c₂ := by
  rw [om200_eq_iff hm1]
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases c₀ <;> cases c₁ <;> cases c₂ <;> decide

theorem t200_card_CSz_le (F : StrothFrame G) (hm : 1 ≤ m) {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) :
    Nat.card (↥((F.S : Subgroup G) ⊓
      Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G))) ≤ 4 * Nat.card (↥D) := by
  let f : D × Bool × Bool → G := fun w =>
    (w.1 : G) * dD.d8 false false w.2.1 * Stroth42Core.bpow e w.2.2
  have hcov : ∀ y ∈ (F.S : Subgroup G) ⊓
      Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G), ∃ w, f w = y := by
    intro y hy
    rw [hS] at hy
    obtain ⟨v, l, k, rfl⟩ := t200_inv_mem_CSc₁ dD hrel hm hy
    exact ⟨(⟨dD.ofTorus v, dD.ofTorus_mem v⟩, l, k), rfl⟩
  have hle := Stroth42Core.natCard_le_of_subset_range f hcov
  rw [Nat.card_prod, Nat.card_prod,
    show Nat.card Bool = 2 by simp [Nat.card_eq_fintype_card]] at hle
  calc Nat.card (↥((F.S : Subgroup G) ⊓
        Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G)))
      ≤ Nat.card (↥D) * (2 * 2) := hle
    _ = 4 * Nat.card (↥D) := by ring

theorem t200_rho_c : dD.ρ⁻¹ * (dD.c : G) * dD.ρ = dD.c := by
  rw [dD.c_eq, dD.conj_ofTorus dD.ρ_mem dD.ρ_conj]
  congr 1
  rw [Stroth34T200.c_eq_ofInt, t200_φρ_vec]
  simp

theorem t200_rho_c₂ : dD.ρ⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * dD.ρ =
    (dD.c : G) ^ 2 ^ (m - 2) := by
  have hcomm : Commute dD.ρ (dD.c : G) := by
    have h := t200_rho_c dD
    refine (show dD.c * dD.ρ = dD.ρ * dD.c from ?_).symm
    calc dD.c * dD.ρ = dD.ρ * (dD.ρ⁻¹ * dD.c * dD.ρ) := by group
      _ = dD.ρ * dD.c := by rw [h]
  have hpow := (hcomm.pow_right (2 ^ (m - 2))).eq
  calc dD.ρ⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * dD.ρ
      = dD.ρ⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2) * dD.ρ) := by group
    _ = dD.ρ⁻¹ * (dD.ρ * (dD.c : G) ^ 2 ^ (m - 2)) := by rw [← hpow]
    _ = (dD.c : G) ^ 2 ^ (m - 2) := by group

end Stroth47Core


namespace Stroth47Core

variable {G : Type} [Group G] [Finite G]
variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200_normalizer_conj_c₂ (F : StrothFrame G) (h : F.IsD D dD) (hm : 2 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hez : e ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G))
    (heΩ : e ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    {p : ℕ} (hp : p = 1 ∨ p = 3)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    {n : G} (hn : n ∈ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G)) :
    n⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * n = (dD.c : G) ^ 2 ^ (m - 2) ∨
      n⁻¹ * (dD.c : G) ^ 2 ^ (m - 2) * n = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hm1 : 1 ≤ m := by omega
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set N := Subgroup.normalizer (D : Set G) ⊓ Z with hN
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hc₂sq : c₂ * c₂ = z := by
    rw [hc₂, hz, ← pow_add]
    congr 1
    rw [← two_mul, mul_comm 2 (2 ^ (m - 2)), ← pow_succ]
    congr 1
    omega
  have hz2 : z * z = 1 := by
    rw [hz]
    exact Stroth47Fus.t200_c₁_mul_self dD hm1
  have hz1 : z ≠ 1 := by
    rw [hz]
    exact Stroth47Fus.t200_c₁_ne_one dD hm1
  have hc₂z : c₂ * z = c₂⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hc₂sq]
    calc c₂ * (c₂ * c₂) * c₂ = (c₂ * c₂) * (c₂ * c₂) := by group
      _ = 1 := by rw [hc₂sq, hz2]
  have hzom : z = dD.ofTorus (om200 m ![1, 0, 0]) := dD.t200_c_pow
  have heNz : e ∈ N := Subgroup.mem_inf.2 ⟨heN, hez⟩
  have hρz : dD.ρ ∈ Z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Stroth47Fus.t200_rho_c₁ dD
    have h' : z * dD.ρ = dD.ρ * z := by
      calc z * dD.ρ = dD.ρ * (dD.ρ⁻¹ * z * dD.ρ) := by group
        _ = dD.ρ * z := by rw [h]
    exact h'.symm
  have hρN : dD.ρ ∈ N := Subgroup.mem_inf.2 ⟨dD.ρ_mem, hρz⟩
  set O : Set G := {x | ∃ n' ∈ N, n' * c₂ * n'⁻¹ = x} with hO
  have hO_conj : ∀ x ∈ O, ∀ n' ∈ N, n'⁻¹ * x * n' ∈ O := by
    rintro x ⟨n₀, hn₀, rfl⟩ n' hn'
    exact ⟨n'⁻¹ * n₀, N.mul_mem (N.inv_mem hn') hn₀, by group⟩
  have hc₂O : c₂ ∈ O := ⟨1, N.one_mem, by group⟩
  have he_om : ∀ ε : Fin 3 → ℤ, e⁻¹ * (c₂ * dD.ofTorus (om200 m ε)) * e =
      c₂ * dD.ofTorus (om200 m (![1, 0, 0] + ε)) := by
    intro ε
    let hE := dD.t200invEAction hrel
    have h1 : e⁻¹ * c₂ * e = c₂ * z := by
      rw [hc₂z, hc₂, ← Stroth43Sc.conj_pow_eq, hrel.c_conj, inv_pow]
    have h2 : e⁻¹ * dD.ofTorus (om200 m ε) * e = dD.ofTorus (om200 m ε) := by
      rw [hE.conj_ofTorus, t200inv_φe_om dD hrel hm1]
    calc e⁻¹ * (c₂ * dD.ofTorus (om200 m ε)) * e
        = (e⁻¹ * c₂ * e) * (e⁻¹ * dD.ofTorus (om200 m ε) * e) := by group
      _ = (c₂ * z) * dD.ofTorus (om200 m ε) := by rw [h1, h2]
      _ = c₂ * (z * dD.ofTorus (om200 m ε)) := by group
      _ = c₂ * (dD.ofTorus (om200 m ![1, 0, 0]) * dD.ofTorus (om200 m ε)) := by rw [hzom]
      _ = c₂ * dD.ofTorus (om200 m (![1, 0, 0] + ε)) := by
        rw [← dD.ofTorus_add, om200_add]
  have hρ_om : ∀ ε : Fin 3 → ℤ, dD.ρ⁻¹ * (c₂ * dD.ofTorus (om200 m ε)) * dD.ρ =
      c₂ * dD.ofTorus (om200 m ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2]) := by
    intro ε
    have h1 : dD.ρ⁻¹ * c₂ * dD.ρ = c₂ := by
      rw [hc₂, t200_rho_c₂]
    have h2 : dD.ρ⁻¹ * dD.ofTorus (om200 m ε) * dD.ρ =
        dD.ofTorus (om200 m ![ε 0 - 4 * ε 2, -ε 2, ε 1 - ε 2]) := by
      rw [dD.conj_ofTorus dD.ρ_mem dD.ρ_conj, t200_φρ_om hm1]
    rw [show dD.ρ⁻¹ * (c₂ * dD.ofTorus (om200 m ε)) * dD.ρ =
      (dD.ρ⁻¹ * c₂ * dD.ρ) * (dD.ρ⁻¹ * dD.ofTorus (om200 m ε) * dD.ρ) by group, h1, h2]
  have hQe : ∀ b₀ b₁ b₂ : Bool,
      c₂ * dD.ofTorus (om200 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)]) ∈ O →
      c₂ * dD.ofTorus (om200 m ![((!b₀).toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)]) ∈ O := by
    intro b₀ b₁ b₂ hq
    have h1 := hO_conj _ hq e heNz
    rw [he_om] at h1
    convert h1 using 3
    exact (om200_eq_iff hm1 _ _).mpr (by cases b₀ <;> cases b₁ <;> cases b₂ <;> decide)
  have hQρ : ∀ b₀ b₁ b₂ : Bool,
      c₂ * dD.ofTorus (om200 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)]) ∈ O →
      c₂ * dD.ofTorus (om200 m ![(b₀.toNat : ℤ), (b₂.toNat : ℤ),
        ((xor b₁ b₂).toNat : ℤ)]) ∈ O := by
    intro b₀ b₁ b₂ hq
    have h1 := hO_conj _ hq dD.ρ hρN
    rw [hρ_om] at h1
    convert h1 using 3
    exact (om200_eq_iff hm1 _ _).mpr (by cases b₀ <;> cases b₁ <;> cases b₂ <;> decide)
  have hkey : ∀ b₀ b₁ b₂ : Bool, (b₁ || b₂) = true →
      c₂ * dD.ofTorus (om200 m ![(b₀.toNat : ℤ), (b₁.toNat : ℤ), (b₂.toNat : ℤ)]) ∈ O →
      ∀ d₀ d₁ d₂ : Bool, (d₁ || d₂) = true →
        c₂ * dD.ofTorus (om200 m ![(d₀.toNat : ℤ), (d₁.toNat : ℤ), (d₂.toNat : ℤ)]) ∈ O := by
    intro b₀ b₁ b₂ hb hq d₀ d₁ d₂ hd
    have q1 := hQρ _ _ _ hq
    have q2 := hQρ _ _ _ q1
    have q3 := hQe _ _ _ hq
    have q4 := hQe _ _ _ q1
    have q5 := hQe _ _ _ q2
    cases b₀ <;> cases b₁ <;> cases b₂ <;> cases d₀ <;> cases d₁ <;> cases d₂ <;>
      simp only [Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.xor_false,
        Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_or] at hb hd q1 q2 q3 q4 q5 ⊢ <;>
      first | assumption | exact absurd hb (by decide) | exact absurd hd (by decide)
  have hx₀O : n⁻¹ * c₂ * n ∈ O := ⟨n⁻¹, N.inv_mem hn, by group⟩
  have hx₀D : n⁻¹ * c₂ * n ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp (Subgroup.mem_inf.1 hn).1 c₂).mp hc₂D
  have hx₀sq : n⁻¹ * c₂ * n * (n⁻¹ * c₂ * n) = z := by
    have hnz := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
    calc n⁻¹ * c₂ * n * (n⁻¹ * c₂ * n) = n⁻¹ * (c₂ * c₂) * n := by group
      _ = n⁻¹ * (z * n) := by rw [hc₂sq]; group
      _ = n⁻¹ * (n * z) := by rw [hnz]
      _ = z := by group
  have hs₀D : c₂⁻¹ * (n⁻¹ * c₂ * n) ∈ D := D.mul_mem (D.inv_mem hc₂D) hx₀D
  have hs₀sq : c₂⁻¹ * (n⁻¹ * c₂ * n) * (c₂⁻¹ * (n⁻¹ * c₂ * n)) = 1 := by
    have hc := hcommD _ hx₀D _ (D.inv_mem hc₂D)
    calc c₂⁻¹ * (n⁻¹ * c₂ * n) * (c₂⁻¹ * (n⁻¹ * c₂ * n))
        = c₂⁻¹ * ((n⁻¹ * c₂ * n) * c₂⁻¹) * (n⁻¹ * c₂ * n) := by group
      _ = c₂⁻¹ * (c₂⁻¹ * (n⁻¹ * c₂ * n)) * (n⁻¹ * c₂ * n) := by rw [hc]
      _ = (c₂ * c₂)⁻¹ * (n⁻¹ * c₂ * n * (n⁻¹ * c₂ * n)) := by group
      _ = 1 := by rw [hc₂sq, hx₀sq, inv_mul_cancel]
  obtain ⟨δ, hδ, hδs⟩ := dD.t200_eq_om_of_mul_self hm1 hs₀D hs₀sq
  have hδb : δ = ![((decide (δ 0 = 1)).toNat : ℤ), ((decide (δ 1 = 1)).toNat : ℤ),
      ((decide (δ 2 = 1)).toNat : ℤ)] := by
    funext i
    fin_cases i
    · exact Stroth43Sc.eq_toNat_decide (hδ 0)
    · exact Stroth43Sc.eq_toNat_decide (hδ 1)
    · exact Stroth43Sc.eq_toNat_decide (hδ 2)
  have hx₀ : n⁻¹ * c₂ * n = c₂ * dD.ofTorus (om200 m ![((decide (δ 0 = 1)).toNat : ℤ),
      ((decide (δ 1 = 1)).toNat : ℤ), ((decide (δ 2 = 1)).toNat : ℤ)]) := by
    rw [← hδb, ← hδs]; group
  have hb12 : (decide (δ 1 = 1) || decide (δ 2 = 1)) = true := by
    by_contra hb
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hb
    have hδ1 : δ 1 = 0 := (hδ 1).resolve_right hb.1
    have hδ2 : δ 2 = 0 := (hδ 2).resolve_right hb.2
    rcases hδ 0 with h0 | h0
    · apply hne1
      rw [hx₀, show (![((decide (δ 0 = 1)).toNat : ℤ), ((decide (δ 1 = 1)).toNat : ℤ),
        ((decide (δ 2 = 1)).toNat : ℤ)] : Fin 3 → ℤ) = 0 by
          funext i; fin_cases i <;> simp [h0, hδ1, hδ2], om200_zero,
        dD.ofTorus_zero, mul_one]
    · apply hne2
      rw [hx₀, show (![((decide (δ 0 = 1)).toNat : ℤ), ((decide (δ 1 = 1)).toNat : ℤ),
        ((decide (δ 2 = 1)).toNat : ℤ)] : Fin 3 → ℤ) = ![1, 0, 0] by
          funext i; fin_cases i <;> simp [h0, hδ1, hδ2], ← hzom, hc₂z]
  rw [hx₀] at hx₀O
  have hall := hkey _ _ _ hb12 hx₀O
  set f : Bool × Bool × Bool → G := fun b =>
    c₂ * dD.ofTorus (om200 m ![(b.1.toNat : ℤ), (b.2.1.toNat : ℤ),
      (b.2.2.toNat : ℤ)]) with hf
  have hfO : ∀ b, f b ∈ O := by
    rintro ⟨b₀, b₁, b₂⟩
    by_cases hb : (b₁ || b₂) = true
    · exact hall b₀ b₁ b₂ hb
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hb
      obtain ⟨rfl, rfl⟩ := hb
      cases b₀
      · simp only [hf]
        rw [show (![((false).toNat : ℤ), ((false).toNat : ℤ), ((false).toNat : ℤ)] : Fin 3 → ℤ)
          = 0 by funext i; fin_cases i <;> rfl, om200_zero, dD.ofTorus_zero,
          mul_one]
        exact hc₂O
      · simp only [hf]
        rw [show (![((true).toNat : ℤ), ((false).toNat : ℤ), ((false).toNat : ℤ)] : Fin 3 → ℤ)
          = ![1, 0, 0] by funext i; fin_cases i <;> rfl, ← hzom, hc₂z]
        have := hO_conj _ hc₂O e heNz
        rwa [hc₂, ← Stroth43Sc.conj_pow_eq, hrel.c_conj, inv_pow] at this
  have hfinj : Function.Injective f := by
    rintro ⟨b₀, b₁, b₂⟩ ⟨d₀, d₁, d₂⟩ hbd
    simp only [hf, mul_right_inj] at hbd
    obtain ⟨rfl, rfl, rfl⟩ := (om200_bool_eq_iff hm1 _ _ _ _ _ _).mp (dD.ofTorus_inj hbd)
    rfl
  have hO8 : 8 ≤ Nat.card O := by
    have := Nat.card_le_card_of_injective (fun b => (⟨f b, hfO b⟩ : O))
      (fun b b' hbb' => hfinj (congrArg Subtype.val hbb'))
    simpa [Nat.card_eq_fintype_card] using this
  have hO8' : Nat.card O ≤ 8 := by
    have hΩ : Nat.card (omegaIn 1 D) = 8 := by rw [h.omegaIn_one_eq]; exact F.card_omegaIn_one_A
    rw [← hΩ]
    refine Nat.card_le_card_of_injective (fun x : O => (⟨c₂⁻¹ * x, ?_⟩ : omegaIn 1 D)) ?_
    · obtain ⟨n', hn', hx⟩ := x.2
      have hxD : (x : G) ∈ D := by
        rw [← hx]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.1 hn').1 c₂).mp hc₂D
      have hxsq : (x : G) * x = z := by
        have hnz := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn').2
        rw [← hx]
        calc n' * c₂ * n'⁻¹ * (n' * c₂ * n'⁻¹) = n' * (c₂ * c₂) * n'⁻¹ := by group
          _ = (n' * z) * n'⁻¹ := by rw [hc₂sq]
          _ = (z * n') * n'⁻¹ := by rw [hnz]
          _ = z := by group
      refine mem_omegaIn_one_of_mul_self (D.mul_mem (D.inv_mem hc₂D) hxD) ?_
      have hc := hcommD _ hxD _ (D.inv_mem hc₂D)
      calc c₂⁻¹ * x * (c₂⁻¹ * x) = c₂⁻¹ * ((x : G) * c₂⁻¹) * x := by group
        _ = c₂⁻¹ * (c₂⁻¹ * x) * x := by rw [hc]
        _ = (c₂ * c₂)⁻¹ * ((x : G) * x) := by group
        _ = 1 := by rw [hc₂sq, hxsq, inv_mul_cancel]
    · intro x x' hxx'
      have := congrArg Subtype.val hxx'
      simp only [mul_right_inj] at this
      exact Subtype.ext this
  have hOcard : Nat.card O = 8 := le_antisymm hO8' hO8
  have hOS := Stroth43Sc.card_eq_card_conj_mul N c₂
  rw [show {x : G | ∃ n ∈ N, n * c₂ * n⁻¹ = x} = O from rfl, hOcard] at hOS
  have hDle : D ≤ N ⊓ Subgroup.centralizer {c₂} := fun d hd =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hd,
      Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd c₂ hc₂D)⟩
  have hDcard : Nat.card D = 2 ^ (m + (m + 2) + (m + 2)) := dD.card
  have hdvd : 2 ^ (m + (m + 2) + (m + 2) + 3) ∣ Nat.card N := by
    rw [hOS, pow_add, hDcard.symm, mul_comm (Nat.card D)]
    exact Nat.mul_dvd_mul (by norm_num) (Subgroup.card_dvd_of_le hDle)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 N
  have hPcard : 2 ^ (m + (m + 2) + (m + 2) + 3) ≤ Nat.card P := by
    rw [hP.card_eq]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hrelOr : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3 := by
    rcases hp with rfl | rfl
    · exact Or.inl hrel
    · exact Or.inr hrel
  have hSylow := H47SylowControl_of_h9 H47H9_proved F hm dD h hSN hnc e
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨heS, heN⟩, heΩ⟩) hS hrelOr P hP.isPGroup
    (hP.le.trans inf_le_right)
  obtain ⟨k, hkz, hkP⟩ := hSylow
  have hle : P.map (MulAut.conj k⁻¹).toMonoidHom ≤
      (F.S : Subgroup G) ⊓ Subgroup.centralizer {z} := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact Subgroup.mem_inf.2 ⟨hkP q hq, Z.mul_mem (Z.mul_mem (Z.inv_mem hkz)
      ((hP.le.trans inf_le_right) hq)) hkz⟩
  have h4 := t200_card_CSz_le dD F hm1 hrel hS
  have hPle : Nat.card P ≤ 4 * Nat.card D := by
    have hcm : Nat.card (P.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
    rw [← hcm]
    exact (Subgroup.card_le_of_le hle).trans h4
  rw [hDcard] at hPle
  have : 2 ^ (m + (m + 2) + (m + 2) + 3) ≤ 4 * 2 ^ (m + (m + 2) + (m + 2)) :=
    hPcard.trans hPle
  rw [pow_add] at this
  have hpos : 0 < 2 ^ (m + (m + 2) + (m + 2)) := by positivity
  nlinarith

end Stroth47Core

end CFSG.CGT.Stroth77

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem H47Normalizer_proved : H47Normalizer := by
  unfold H47Normalizer
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel n hn
  have heΩ : e ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp he).2
  have heN : e ∈ Subgroup.normalizer (D : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp he).1).2
  have hzD : (dD.c : G) ^ 2 ^ (m - 1) ∈ D := D.pow_mem dD.c.2 _
  have hz2 : (dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1) = 1 :=
    Stroth47Fus.t200_c₁_mul_self dD (by omega)
  have hzΩ : (dD.c : G) ^ 2 ^ (m - 1) ∈ omegaIn 1 D :=
    mem_omegaIn_one_of_mul_self hzD hz2
  have hez : e ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.mp heΩ _ hzΩ).symm
  rcases hrel with hrel | hrel
  · exact Stroth47Core.t200_normalizer_conj_c₂ dD F h hm hSN hnc heN hez heΩ hS
      (p := 1) (Or.inl rfl) hrel hn
  · exact Stroth47Core.t200_normalizer_conj_c₂ dD F h hm hSN hnc heN hez heΩ hS
      (p := 3) (Or.inr rfl) hrel hn

theorem H47Extremal_proved : H47Extremal :=
  H47Extremal_of_normalizer H47Normalizer_proved

end CFSG.CGT.Stroth77
