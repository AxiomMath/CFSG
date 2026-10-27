module

public import CFSG.CGT.Stroth77.Section47ExtremalH9

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

@[expose] def t200inv1EAction {j p : ℕ} (hrel : Rel34inv dD e j 1 p) : dD.EAction e where
  φe := torusDiag _ ![-1, -1 + (j : ℤ), -1 + (j : ℤ)]
  wuv := Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)]
  wt := Torus.ofInt _ ![0, -(p : ℤ), 0]
  ve := 0
  conj_ofTorus := dD.conj_ofTorus_of_gens
    (by rw [hrel.c_conj, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
    (by
      rw [hrel.a_conj, torusDiag_gen, ofTorus_zsmul, ← a_eq,
        show (![-1, -1 + (j : ℤ), -1 + (j : ℤ)] : Fin 3 → ℤ) 1 = -1 + (j : ℤ) from rfl,
        _root_.zpow_add, _root_.zpow_neg_one,
        show ((j : ℤ)) = ((j : ℕ) : ℤ) from rfl, zpow_natCast])
    (by
      rw [hrel.b_conj, torusDiag_gen, ofTorus_zsmul, ← b_eq,
        show (![-1, -1 + (j : ℤ), -1 + (j : ℤ)] : Fin 3 → ℤ) 2 = -1 + (j : ℤ) from rfl,
        _root_.zpow_add, _root_.zpow_neg_one,
        show ((j : ℤ)) = ((j : ℕ) : ℤ) from rfl, zpow_natCast])
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
    rw [hrel.e_sq, dD.ofTorus_zero]

theorem t200inv1_φe {j p : ℕ} (hrel : Rel34inv dD e j 1 p) (x : Fin 3 → ℤ) :
    (dD.t200inv1EAction hrel).φe (Torus.ofInt _ x) =
      Torus.ofInt _ ![-(x 0), (-1 + (j : ℤ)) * x 1, (-1 + (j : ℤ)) * x 2] := by
  change torusDiag _ ![-1, -1 + (j : ℤ), -1 + (j : ℤ)] (Torus.ofInt _ x) = _
  rw [torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

end StrothWeakTypeData

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem t200inv1_φe_om {j p : ℕ} (hrel : Rel34inv dD e j 1 p) (hm : 1 ≤ m) (hj : Even j)
    (ε : Fin 3 → ℤ) :
    (dD.t200inv1EAction hrel).φe (om200 m ε) = om200 m ε := by
  have hγ : (-1 + (j : ℤ)) % 2 = 1 := by
    obtain ⟨k, rfl⟩ := hj
    push_cast
    omega
  change torusDiag _ ![-1, -1 + (j : ℤ), -1 + (j : ℤ)] (om200 m ε) = om200 m ε
  exact torusDiag_om200_of_odd hm (by norm_num) hγ hγ ε

theorem t200_eAction_mem_CSc₁ (hE : dD.EAction e)
    (hc₁ : hE.φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0]) (hm : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyc := Subgroup.mem_centralizer_singleton_iff.mp hyC
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  cases k
  · simp only [Stroth42Core.bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyc
    obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hyc
    exact ⟨v, l, false, rfl⟩
  · simp only [Stroth42Core.bpow, ↓reduceIte] at hyc
    rw [dD.t200_c_pow, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
      mul_left_inj] at hyc
    obtain ⟨rfl, rfl⟩ := t200_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
    exact ⟨v, l, true, rfl⟩

theorem t200_inv1_comm_u {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (k : Bool) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) *
        (dD.ofTorus v₀ * dD.d8 false false true * bpow e k) =
      dD.ofTorus v₀ * dD.d8 false false true * bpow e k * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ^ (m + 2) ∣ x 1 - (if k then -1 + (j : ℤ) else 1) * x 2 := by
  let hE := dD.t200inv1EAction hrel
  have hc := (Stroth47Core.t200_e_comm_iff dD hE v₀ _ true k).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  cases k
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [t200_φu, t200_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1
  · simp only [↓reduceIte] at hc ⊢
    rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_φu, t200_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1

theorem t200_inv1_comm_e {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p)
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) *
        (dD.ofTorus v₀ * dD.d8 false false false * bpow e true) =
      dD.ofTorus v₀ * dD.d8 false false false * bpow e true * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ∣ x 1 ∧ (2 : ℤ) ∣ x 2 := by
  let hE := dD.t200inv1EAction hrel
  have hc := (Stroth47Core.t200_e_comm_iff dD hE v₀ _ false true).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_ofInt_eq_iff] at hc
  obtain ⟨-, h1, h2⟩ := hc
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2
  have key : ∀ y : ℤ, (2 : ℤ) ^ (m + 2) ∣ y - (-1 + (j : ℤ)) * y → (2 : ℤ) ∣ y := by
    intro y hy
    have hy' : (2 : ℤ) ^ (m + 2) ∣ (2 - (j : ℤ)) * y := by
      convert hy using 1
      ring
    rcases hj with rfl | rfl
    · have hy2 : (2 : ℤ) ^ (m + 2) ∣ 2 * y := by
        convert hy' using 1
        ring
      rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ']] at hy2
      have hy1 : (2 : ℤ) ^ (m + 1) ∣ y :=
        (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hy2
      exact dvd_trans (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) hy1
    · have hy2 : (2 : ℤ) ^ (m + 2) ∣ 2 * ((1 - 2 ^ m) * y) := by
        convert hy' using 1
        push_cast
        rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ']]
        ring
      rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ']] at hy2
      have hy1 : (2 : ℤ) ^ (m + 1) ∣ (1 - 2 ^ m) * y :=
        (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hy2
      have h2dvd : (2 : ℤ) ∣ (1 - 2 ^ m) * y :=
        dvd_trans (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) hy1
      have hodd : ¬ (2 : ℤ) ∣ (1 - 2 ^ m) := by
        have h2m_even : Even ((2 : ℤ) ^ m) :=
          (even_two : Even (2 : ℤ)).pow_of_ne_zero (by omega : m ≠ 0)
        have hodd' : Odd (1 - (2 : ℤ) ^ m) := Odd.sub_even odd_one h2m_even
        intro hd
        exact (Int.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr hd)
      exact (Int.prime_two.dvd_mul.mp h2dvd).resolve_left hodd
  exact ⟨key _ h1, key _ h2⟩

theorem t200_inv1_h9 [Finite G] {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  classical
  intro X hX hab hcard
  let hE := dD.t200inv1EAction hrel
  have hf : Even j := by
    rcases hj with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨2 ^ m, by rw [← two_mul, pow_succ']⟩
  have hc₁ : hE.φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0] :=
    t200inv1_φe_om dD hrel hm hf _
  have hDcard : Nat.card D = 2 ^ (m + (m + 2) + (m + 2)) := dD.card
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 1)) := ⟨by positivity⟩
  haveI : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  have hnf : ∀ y ∈ X, ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k :=
    fun y hy => t200_eAction_mem_CSc₁ dD hE hc₁ hm (hX hy)
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
    set γ : ℤ := if k₀ then -1 + (j : ℤ) else 1 with hγ
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
        have h1 := t200_inv1_comm_u dD hrel v₀ k₀ x (hcomm _ hd _ hx₀)
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
        obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩ := t200_inv1_comm_e dD hm hj hrel v₁ x
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

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.IsD.t200_inv1_conj_le_S {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    {e : G}
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    {j p : ℕ} (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQz : Q ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ k ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := dD.isMulCommutative
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hPS : P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_right.trans le_sup_left
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have h3 := dD.t200_h3 hm
  have hncA : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hnc
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  have hza := h.not_isConj_of_omega hncA h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have hz2 : z * z = 1 := by rw [hz]; exact Stroth47Fus.t200_c₁_mul_self dD hm
  have hz1 : z ≠ 1 := by rw [hz]; exact Stroth47Fus.t200_c₁_ne_one dD hm
  exact Stroth42.exists_conj_le_centralizer F.S dD.isMulCommutative h.le_S hSN hPS hzD h3'
    hz2 hz1 (fun X hX hab hcard => by
      rw [hS] at hX
      exact Stroth47Core.t200_inv1_h9 dD hm hj hrel X hX hab hcard) hQ hQz

end CFSG.CGT.Stroth77
