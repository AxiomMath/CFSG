module

public import CFSG.CGT.Stroth77.Section310CharBC
public import CFSG.CGT.Stroth77.Section44CoreIII
public import CFSG.CGT.Stroth77.Stroth34Defs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Stroth77.Extension22FourC4
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.CGT.Stroth77.TorusCard
public import CFSG.Foundations
public import CFSG.GH74.Defs
public import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.CGT.Stroth77

open Stroth44Core

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t201 m)}

namespace Stroth310T201

theorem two_le_k (hm : 2 ≤ m) (i : Fin 3) : 2 ≤ (StrothTypeIndex.t201 m).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type201.k] <;> omega

theorem card_D (dD : StrothWeakTypeData D (.t201 m)) : Nat.card D = 2 ^ (3 * m + 4) := by
  rw [dD.card]
  change 2 ^ (m + (m + 2) + (m + 2)) = 2 ^ (3 * m + 4)
  ring_nf

theorem om201_add_self (hm : 1 ≤ m) (ε : Fin 3 → ℤ) : om201 m ε + om201 m ε = 0 := by
  rw [om201_add, ← om201_zero, om201_eq_iff hm]
  intro i
  exact Int.modEq_zero_iff_dvd.mpr ⟨ε i, by simp only [Pi.add_apply]; ring⟩

theorem φuv_om_ne (hm : 1 ≤ m) :
    (StrothTypeIndex.t201 m).action.φuv (om201 m ![1, 0, 0]) ≠ om201 m ![1, 0, 0] := by
  rw [t201_φuv_om hm]
  intro h
  have h1 := (om201_eq_iff hm _ _).mp h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
  norm_num [Int.ModEq] at h1

theorem uv_not_mem (dD : StrothWeakTypeData D (.t201 m)) (hm : 1 ≤ m) :
    ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w :=
  dD.not_forall_commute_uv_of_torus (by rw [two_nsmul]; exact om201_add_self hm _) (φuv_om_ne hm)

theorem c_pow_mem (dD : StrothWeakTypeData D (.t201 m)) (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) ∈ omegaIn 1 D := by
  rw [Stroth44Core.c_pow_om dD]
  exact mem_omegaIn_one_of_mul_self (dD.ofTorus_mem _) (om201_mul_self dD hm _)

theorem c_pow_not_commute (dD : StrothWeakTypeData D (.t201 m)) (hm : 1 ≤ m) :
    ¬ (dD.c : G) ^ 2 ^ (m - 1) * dD.uv = dD.uv * (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [Stroth44Core.c_pow_om dD, dD.uv_mul_ofTorus]
  intro h
  exact φuv_om_ne hm (dD.ofTorus_inj (mul_right_cancel h).symm)

theorem a₁_b₁ (dD : StrothWeakTypeData D (.t201 m)) (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) ≠ 1 ∧ (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 ∧
      (dD.a : G) ^ 2 ^ (m + 1) ≠ (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [za_om dD, zb_om dD]
  refine ⟨om201_ne_one dD hm 1 (by norm_num [Int.ModEq]),
    om201_ne_one dD hm 2 (by norm_num [Int.ModEq]), ?_⟩
  rw [Ne, dD.ofTorus_inj.eq_iff, om201_eq_iff hm]
  intro h0
  have h1 := h0 1
  simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
  norm_num [Int.ModEq] at h1

theorem hA (h : F.IsD D dD) (hm : 2 ≤ m) :
    ∀ g ∈ Subgroup.normalizer
        (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G),
      D.map (MulAut.conj g).toMonoidHom ⊓ ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ D →
      ∀ y ∈ D.map (MulAut.conj g).toMonoidHom, ∀ w ∈ omegaIn 1 D, w * y = y * w := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine h.hA_of_torus (two_le_k hm) (uv_not_mem dD hm1) (v₁ := om201 (m' + 1) ![0, 1, 0])
    (v₂ := om201 (m' + 1) ![0, 0, 1]) (z := Torus.ofInt _ ![0, 2 ^ m', 0]) ?_
    (om201_add_self hm1 _) ?_ ?_ ?_ ?_
  · rw [← natCast_zsmul, ← Torus.ofInt_zsmul, om201]
    congr 1
    funext i
    fin_cases i <;> simp [StrothTypeIndex.k, Type201.k] <;> ring
  · intro h0
    have h1 := (om201_eq_iff hm1 _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    norm_num [Int.ModEq] at h1
  · rw [t201_φu_om]
    congr 1
  · rw [t201_φuv_om hm1]
    refine (om201_eq_iff hm1 _ _).mpr fun i => ?_
    fin_cases i <;> simp [Int.ModEq] <;> decide
  · rw [t201_φt_om hm1]
    refine (om201_eq_iff hm1 _ _).mpr fun i => ?_
    fin_cases i <;> simp [Int.ModEq] <;> decide

theorem bound_ii (dD : StrothWeakTypeData D (.t201 m)) (hm : 2 ≤ m) {e : G}
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (hc : e⁻¹ * (dD.c : G) * e = dD.c)
    (ha : e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1))
    (hb : e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxC : x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hA1, hB1, hAB⟩ := a₁_b₁ dD hm1
  have hb4 := dD.bound_comm (card_D dD) (c_pow_not_commute dD hm1) heN hc (pow_mem dD.a.2 _)
    (pow_mem dD.b.2 _) ha hb hA1 hB1 hAB hxN
    (Subgroup.mem_centralizer_iff.mp hxC _ (c_pow_mem dD hm1))
  have hpos : 0 < Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) := Nat.card_pos
  have h4m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : 16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) ≤ Nat.card D :=
    le_trans (by nlinarith) hb4
  omega

theorem card_le_eight_of_inv (dD : StrothWeakTypeData D (.t201 m)) (hm : 1 ≤ m) {e : G}
    {j t : ℕ} (hj : j = 2 ^ (m + 1) * t) (hc : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (ha : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ j)
    (hb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ j) (y : G) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) ≤ 8 := by
  have hle : D ⊓ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      omegaIn 1 D := by
    intro z hz
    exact mem_omegaIn_one_of_mul_self hz.1.1 (dD.mul_self_eq_one_of_inv_shape
      (by change 3 ≤ m + 2; omega) (j := j) (t := t) (by rw [hj]; rfl) hc ha hb hz.1.1
      (Subgroup.mem_centralizer_singleton_iff.mp hz.2))
  have h8 : Nat.card (omegaIn 1 D) = 8 := natCard_omegaIn_one_of_pos dD.e (t201_one_le_k hm)
  exact (Subgroup.card_le_of_le hle).trans h8.le

end Stroth310T201

theorem StrothFrame.IsD.mem_normalizer_omegaIn_t201 (h : F.IsD D dD) (hm : 2 ≤ m)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) →
        (StrothTypeIndex.t201 m).m = (StrothTypeIndex.t201 m).n)
    (h34 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨ Rel34inv dD e 0 1 2 ∨ Rel34inv dD e (2 ^ (m + 1)) 1 2))
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  have hm1 : 1 ≤ m := by omega
  have hDs := Stroth310T201.card_D dD
  have h1024 : 2 ^ 10 ≤ 2 ^ (3 * m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine h.mem_normalizer_omegaIn_of_cases (by change m ≠ m + 2; omega) (t201_one_le_k hm1)
    (Stroth310T201.uv_not_mem dD hm1) h226 (Stroth310T201.hA h hm) ?_ hgN
  rcases h34 with hRD | ⟨e, heR, hRe, he | he | he⟩
  · intro x _ Q hQR hQD _
    exact absurd (hRD ▸ hQR) hQD
  · have heN : e ∈ Subgroup.normalizer (D : Set G) := (Subgroup.mem_inf.mp heR).1.2
    have heC := (Subgroup.mem_inf.mp heR).2
    refine h.hB_of_zpowers hRe heN (he.e_sq ▸ inv_mem dD.c.2) ?_
      (Stroth310T201.bound_ii dD hm heN he.c_conj he.a_conj he.b_conj heN heC)
    simpa using Stroth310T201.bound_ii dD hm heN he.c_conj he.a_conj he.b_conj (x := 1)
      (one_mem _) (one_mem _)
  · have heN : e ∈ Subgroup.normalizer (D : Set G) := (Subgroup.mem_inf.mp heR).1.2
    have h8 := Stroth310T201.card_le_eight_of_inv dD hm1 (t := 0) (by ring) he.c_conj
      he.a_conj he.b_conj
    exact h.hB_of_zpowers hRe heN (by rw [he.e_sq]; exact one_mem D)
      (by have := h8 dD.uv; omega) (by have := h8 (dD.uv * e); omega)
  · have heN : e ∈ Subgroup.normalizer (D : Set G) := (Subgroup.mem_inf.mp heR).1.2
    have h8 := Stroth310T201.card_le_eight_of_inv dD hm1 (t := 1) (by ring) he.c_conj
      he.a_conj he.b_conj
    exact h.hB_of_zpowers hRe heN (by rw [he.e_sq]; exact one_mem D)
      (by have := h8 dD.uv; omega) (by have := h8 (dD.uv * e); omega)

end CFSG.CGT.Stroth77
