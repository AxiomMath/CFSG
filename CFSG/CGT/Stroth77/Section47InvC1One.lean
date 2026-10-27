module

public import CFSG.CGT.Stroth77.Section47InvC1Final
public import CFSG.CGT.Stroth77.Section47ScInvOne

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core StrothWeakTypeData

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200inv_sqE_ne_zero_of_eq_one (hm : m = 1) {p : ℕ} (hp : p % 2 = 1)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (x : Fin 3 → ℤ) (i j l : Bool) (hlj : (l && j) = false) :
    (dD.t200invEAction hrel).sqE (Torus.ofInt _ x) i j l ≠ 0 := by
  subst hm
  obtain ⟨q, rfl⟩ := Nat.odd_iff.mpr hp
  intro h0
  have hwuv : (dD.t200invEAction hrel).wuv =
      Torus.ofInt _ ![((2 * q + 1 : ℕ) : ℤ), ((2 * q + 1 : ℕ) : ℤ),
        ((2 * q + 1 : ℕ) : ℤ)] := rfl
  have hwt : (dD.t200invEAction hrel).wt =
      Torus.ofInt _ ![0, -((2 * q + 1 : ℕ) : ℤ), 0] := rfl
  simp only [EAction.sqE, EAction.twist, hwuv, hwt, t200invEAction_ve,
      StrothWeakTypeData.t200inv_φe dD hrel, SigmaFourAction.d8Act,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Bool.false_eq_true, Bool.true_eq_false,
      Bool.and_false, Bool.and_true, ↓reduceIte, map_zero] at h0
  cases i <;> cases j <;> cases l <;>
    simp only [Bool.and_true, Bool.and_false, Bool.false_eq_true, Bool.true_eq_false] at hlj <;>
    (try exact absurd hlj (by decide)) <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, Bool.true_eq_false, Bool.and_false,
      Bool.and_true, ↓reduceIte, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_zero,
      map_add, map_sub, t200_φuv, t200_φt, t200_φu, StrothWeakTypeData.t200inv_φe dD hrel,
      ← Torus.ofInt_add, ← Torus.ofInt_sub, add_zero, zero_add] at h0
  all_goals
    rw [Stroth34T200.t200_ofInt_eq_zero_iff] at h0
    try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0
    obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h0
    norm_num at hk0 hk1 hk2
    push_cast at hk0 hk1 hk2
    omega

theorem t200inv_mem_of_mul_self_of_eq_one (hm : m = 1) {p : ℕ} (hp : p % 2 = 1)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    {y : G}
    (hy : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hyy : y * y = 1) :
    y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  subst hm
  let hE := dD.t200invEAction hrel
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · simpa [bpow] using dD.nf_mem v i j l
  · simp only [bpow, ↓reduceIte] at hyy
    rw [hE.nfe_e_mul_self] at hyy
    by_cases hlj : (l && j) = true
    · exfalso
      rw [hlj, dD.d8_tff] at hyy
      have huvD : dD.uv ∈ D := by
        have h1 : dD.uv = (dD.ofTorus (hE.sqE v i j l))⁻¹ :=
          eq_inv_of_mul_eq_one_right hyy
        rw [h1]
        exact D.inv_mem (dD.ofTorus_mem _)
      exact (dD.d8_not_mem (t200_faithful (m := 1) le_rfl) (i := true) (j := false) (l := false)
        (by decide) (0 : Torus (StrothTypeIndex.t200 1).k))
        (by simpa [dD.d8_tff, dD.ofTorus_zero, one_mul] using huvD)
    · exfalso
      have hlj' : (l && j) = false := by
        cases l <;> cases j <;> simp_all
      rw [hlj', d8_fff, mul_one] at hyy
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      exact absurd (dD.ofTorus_eq_one_iff.mp hyy)
        (t200inv_sqE_ne_zero_of_eq_one dD rfl hp hrel x i j l hlj')

end Stroth47Core

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200_inv_h9_of_one_le {p : ℕ} (hm : 1 ≤ m)
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

theorem exists_conj_mem_centralizer_of_mem_S₁_of_one_le :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g : G, g⁻¹ * e * g ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) →
      ∃ g' ∈ Subgroup.centralizer {((dD.c : G) ^ 2 ^ (m - 1))},
        g'⁻¹ * e * g' ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel
  have go : ∀ {p : ℕ}, Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p →
      ∀ g : G, g⁻¹ * e * g ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) →
        ∃ g' ∈ Subgroup.centralizer {((dD.c : G) ^ 2 ^ (m - 1))},
          g'⁻¹ * e * g' ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) := by
    intro p hrel g hg
    have hm1 : 1 ≤ m := by omega
    set P : Subgroup G := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
    set z : G := (dD.c : G) ^ 2 ^ (m - 1) with hz
    set y : G := g⁻¹ * e * g with hy
    set z' : G := g⁻¹ * z * g with hz'
    have he_sq : e * e = z := hrel.e_sq
    have hz2 : z * z = 1 := Stroth47Fus.t200_c₁_mul_self dD hm1
    have hz1 : z ≠ 1 := Stroth47Fus.t200_c₁_ne_one dD hm1
    have hzD : z ∈ D := D.pow_mem dD.c.2 _
    have hzz' : z' = y * y := by
      rw [hz', hy]
      calc g⁻¹ * z * g = g⁻¹ * (e * e) * g := by rw [← he_sq]
        _ = (g⁻¹ * e * g) * (g⁻¹ * e * g) := by group
    have hz'conj : IsConj z' z :=
      Stroth42.isConj_of_conj_eq (by rw [hz', hz])
    have hz'2 : z' * z' = 1 := Stroth42.mul_self_eq_one_of_isConj hz'conj hz2
    have hz'_ne : z' ≠ 1 := Stroth42.ne_one_of_isConj hz'conj hz1
    have hz'mem : z' ∈ D ∨ z' * dD.uv ∈ D := by
      rw [hzz']
      exact dD.mul_self_mem_or y hg
    have hza : ¬ IsConj z ((dD.a : G) ^ 2 ^ (m + 1)) := by
      have hncA : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
          orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
        obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hnc
        rw [h.omegaIn_one_eq] at hx hy
        exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
      exact h.not_isConj_of_omega hncA (dD.t200_h3 hm1)
    have h3' : ∀ w ∈ D, w * w = 1 → w ≠ 1 → IsConj w z →
        ∃ q ∈ P, q⁻¹ * w * q = z := by
      intro w hwD hw2 hw1 hwz
      rcases dD.t200_h3 hm1 w hwD hw2 hw1 with ⟨q, hqP, hq⟩ | ⟨l, hlL, hl⟩
      · exact ⟨q, hqP, hq⟩
      · exact absurd (hwz.symm.trans (Stroth42.isConj_of_conj_eq hl).symm) hza
    rcases hz'mem with hz'D | hz'uv
    · rcases dD.t200_h3 hm1 z' hz'D hz'2 hz'_ne with ⟨q, hqP, hq⟩ | ⟨l, hlL, hl⟩
      · refine ⟨g * q, ?_, ?_⟩
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hconj : (g * q)⁻¹ * z * (g * q) = z := by
            calc (g * q)⁻¹ * z * (g * q)
                = q⁻¹ * (g⁻¹ * z * g) * q := by group
              _ = q⁻¹ * z' * q := by rw [hz']
              _ = z := hq
          calc (g * q) * z = (g * q) * ((g * q)⁻¹ * z * (g * q)) := by rw [hconj]
            _ = z * (g * q) := by group
        · have hqS : q ∈ D ⊔ P := Subgroup.mem_sup_right hqP
          have hqinvS : q⁻¹ ∈ D ⊔ P := (D ⊔ P).inv_mem hqS
          have heq : (g * q)⁻¹ * e * (g * q) = q⁻¹ * y * q := by
            rw [hy]; group
          rw [heq]
          exact (D ⊔ P).mul_mem ((D ⊔ P).mul_mem hqinvS hg) hqS
      · exact absurd (hz'conj.symm.trans (Stroth42.isConj_of_conj_eq hl).symm) hza
    · have hDS : D ≤ (F.S : Subgroup G) := by
        rw [hS]; exact le_sup_left.trans le_sup_left
      have hPS : P ≤ (F.S : Subgroup G) := by
        rw [hS]; exact le_sup_right.trans le_sup_left
      have h7 : ∀ E : Subgroup G, E ≤ (F.S : Subgroup G) ⊓
          Subgroup.centralizer {z} → (∀ y ∈ E, y * y = 1) → Nat.card E ≠ 16 := by
        intro E hE hE2
        have hE' := hE
        rw [hS] at hE'
        exact t200_inv_h7 dD hm1 hrel E hE' hE2
      have h9 : ∀ X : Subgroup G, X ≤ (F.S : Subgroup G) ⊓
          Subgroup.centralizer {z} → IsMulCommutative X →
            Nat.card X = Nat.card D → X = D := by
        intro X hX hab hcard
        have hX' := hX
        rw [hS] at hX'
        exact t200_inv_h9_of_one_le dD hm hrel X hX' hab hcard
      have hE16 : ∃ E : Subgroup G, E ≤ Subgroup.centralizer {z'} ∧
          (∀ y ∈ E, y * y = 1) ∧ Nat.card E = 16 :=
        dD.t200_h6 hm1 z' hz'uv hz'2
      exact absurd hz'conj (Stroth42.not_isConj_of_e16 F.S dD.isMulCommutative hDS hSN
        hPS hzD h3' hz2 hz1 h7 h9 hE16)
  rcases hrel with hrel | hrel
  · exact go hrel
  · exact go hrel

theorem stroth_4_7_inv_conj_notMem_all_of_one_le :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g : G, g⁻¹ * e * g ∉ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel g hg
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain ⟨g', hg'C, hg'S⟩ :=
      exists_conj_mem_centralizer_of_mem_S₁_of_one_le F hm dD h hSN hnc e he hS hrel g hg
    exact stroth_4_7_inv_conj_notMem_of_one_le F hm dD h hSN hnc e he hS hrel g' hg'C hg'S
  · exact stroth_4_7_inv_conj_notMem_all F hm2 dD h hSN hnc e he hS hrel g hg

theorem stroth_4_7_hinv_c1_one :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧ ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) → False := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : 1 ≤ m := by omega
    have hme : m = 1 := by omega
    haveI := F.simple
    obtain ⟨p, hp, hrelp⟩ : ∃ p : ℕ, p % 2 = 1 ∧
        Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p :=
      hrel.elim (fun h' => ⟨1, by norm_num, h'⟩) (fun h' => ⟨3, by norm_num, h'⟩)
    set U : Subgroup G := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} with hUdef
    have heN : e ∈ Subgroup.normalizer (U : Set G) := by
      rw [hUdef]
      exact (dD.t200invEAction hrelp).mem_normalizer
    have he2U : e * e ∈ U := by
      rw [hrelp.e_sq]
      exact Subgroup.mem_sup_left (D.pow_mem dD.c.2 _)
    have heU : e ∉ U := by
      have h1 := stroth_4_7_inv_conj_notMem_all_of_one_le F hm dD h hSN hnc e he hS hrel 1
      simpa [hUdef] using h1
    have hUidx : U.relIndex (F.S : Subgroup G) = 2 := by
      rw [hS]
      exact Stroth47.relIndex_sup_zpowers_of_mul_self_mem heN he2U heU
    have hc₁ : ∀ g : G, g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g ∈ (F.S : Subgroup G) →
        g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g ∈ U := by
      intro g hg
      have hyy : (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g) *
          (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g) = 1 := by
        rw [show g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g *
            (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g) =
            g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1)) * g by group,
          Stroth47Fus.t200_c₁_mul_self dD hm1]
        group
      have hg' : g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g ∈
          D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
        rw [← hUdef]
        rw [← hS]
        exact hg
      exact Stroth47Core.t200inv_mem_of_mul_self_of_eq_one dD hme hp hrelp hg' hyy
    refine false_of_t200_inv_of_noConj (Stroth42.frame_exists_mul_ne F) F.S ?_ hUidx ?_ heU ?_
      (stroth_4_7_inv_conj_notMem_all_of_one_le F hm dD h hSN hnc e he hS hrel)
    · rw [hS]
      exact le_sup_left
    · rw [hS]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    · intro g k hmem
      have h1 : e ^ (2 * k) = ((dD.c : G) ^ 2 ^ (m - 1)) ^ k := by
        rw [pow_mul, pow_two, hrelp.e_sq]
      rcases H47Inv_c₁_pow dD hm1 k with hk | hk
      · rw [h1, hk]
        simpa using U.one_mem
      · rw [h1, hk] at hmem ⊢
        exact hc₁ g hmem
  · exact stroth_4_7_hinv_c1 F hm2 dD h hSN hnc e he hS hrel

end CFSG.CGT.Stroth77
