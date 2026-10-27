module

public import CFSG.CGT.Stroth77.Section47ScInv

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core StrothWeakTypeData

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G} {p : ℕ}

theorem t200invEAction_ve {p : ℕ}
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    (dD.t200invEAction hrel).ve = Torus.ofInt _ ![(2 : ℤ) ^ (m - 1), 0, 0] := rfl

theorem t200_inv_sqE_c (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (x0 x1 x2 : ℤ) (l : Bool) :
    ∃ s1 s2 : ℤ, (dD.t200invEAction hrel).sqE (Torus.ofInt _ ![x0, x1, x2])
      false false l = Torus.ofInt _ ![2 ^ (m - 1), s1, s2] := by
  have hφ : ∀ y : Fin 3 → ℤ, (dD.t200invEAction hrel).φe (Torus.ofInt _ y) =
      Torus.ofInt _ ![-y 0, (-1 + 2 ^ (m + 1)) * y 1, (-1 + 2 ^ (m + 1)) * y 2] :=
    fun y => StrothWeakTypeData.t200inv_φe dD hrel y
  simp only [EAction.sqE, EAction.twist, t200invEAction_ve]
  cases l <;>
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, Bool.and_false, map_add, map_sub, map_zero, hφ, t200_φu,
    ← Torus.ofInt_add, ← Torus.ofInt_sub, add_zero, zero_add]
  · refine ⟨2 ^ (m + 1) * x1, 2 ^ (m + 1) * x2, ?_⟩
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  · refine ⟨x1 + (-1 + 2 ^ (m + 1)) * x2, x2 + (-1 + 2 ^ (m + 1)) * x1, ?_⟩
    congr 1
    funext i
    fin_cases i <;> simp <;> ring

theorem t200_inv_sqE_ne_zero (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (v : Torus (StrothTypeIndex.t200 m).k) (l : Bool) :
    (dD.t200invEAction hrel).sqE v false false l ≠ 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  obtain ⟨x0, x1, x2, hx⟩ := t200_exists_vec (Torus.ofInt _ x)
  rw [hx]
  obtain ⟨s1, s2, hs⟩ := t200_inv_sqE_c dD hm hrel x0 x1 x2 l
  rw [hs]
  intro h0
  have h1 := congrArg (fun t => t 0) h0
  simp only [Torus.ofInt_apply, Pi.zero_apply, Matrix.cons_val_zero] at h1
  have hmk : (StrothTypeIndex.t200 m).k 0 = m := rfl
  rw [hmk] at h1
  have h2 : ((2 : ZMod (2 ^ m)) ^ (m - 1)) = 0 := by
    simpa using h1
  exact two_pow_pred_ne_zero hm (by simpa using h2)

theorem t200_inv_mul_self_ne_one (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (v : Torus (StrothTypeIndex.t200 m).k) (l : Bool) :
    (dD.ofTorus v * dD.d8 false false l * e) *
      (dD.ofTorus v * dD.d8 false false l * e) ≠ 1 := by
  rw [(dD.t200invEAction hrel).nfe_e_mul_self]
  simp only [Bool.and_false, d8_fff, mul_one]
  intro h
  exact t200_inv_sqE_ne_zero dD hm hrel v l ((dD.ofTorus_eq_one_iff).mp h)

theorem t200_inv_h7 (hm : 1 ≤ m)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
      (∀ y ∈ E, y * y = 1) → Nat.card E ≠ 16 := by
  intro E hE hE2
  have hE' : E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} := by
    intro y hy
    obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp (hE hy)
    obtain ⟨v, l, k, hyv⟩ := t200_inv_mem_CSc₁ dD hrel hm
      (Subgroup.mem_inf.mpr ⟨hyS, hyC⟩)
    cases k
    · refine Subgroup.mem_inf.mpr ⟨?_, hyC⟩
      rw [hyv]
      simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
      exact (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).mul_mem
        (Subgroup.mem_sup_left (dD.ofTorus_mem v))
        (Subgroup.mem_sup_right (dD.d8_mem false false l))
    · exfalso
      have hsq := hE2 y hy
      rw [hyv] at hsq
      simp only [bpow, ↓reduceIte] at hsq
      exact t200_inv_mul_self_ne_one dD hm hrel v l hsq
  exact t200_h7 dD hm E hE' hE2

end Stroth47Core

theorem exists_conj_mem_centralizer_of_mem_S₁ :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
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
        exact t200_inv_h9 dD hm hrel X hX' hab hcard
      have hE16 : ∃ E : Subgroup G, E ≤ Subgroup.centralizer {z'} ∧
          (∀ y ∈ E, y * y = 1) ∧ Nat.card E = 16 :=
        dD.t200_h6 hm1 z' hz'uv hz'2
      exact absurd hz'conj (Stroth42.not_isConj_of_e16 F.S dD.isMulCommutative hDS hSN
        hPS hzD h3' hz2 hz1 h7 h9 hE16)
  rcases hrel with hrel | hrel
  · exact go hrel
  · exact go hrel

theorem stroth_4_7_inv_conj_notMem_all :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
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
  obtain ⟨g', hg'C, hg'S⟩ :=
    exists_conj_mem_centralizer_of_mem_S₁ F hm dD h hSN hnc e he hS hrel g hg
  exact stroth_4_7_inv_conj_notMem F hm dD h hSN hnc e he hS hrel g' hg'C hg'S

end CFSG.CGT.Stroth77
