module

public import CFSG.CGT.Stroth77.Section310CharBA

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t100 m)}

namespace Stroth310T100

theorem two_le_k (hm : 2 ≤ m) (i : Fin 3) : 2 ≤ (StrothTypeIndex.t100 m).k i := by
  fin_cases i
  · exact hm
  · show 2 ≤ m + 1; omega
  · show 2 ≤ m + 1; omega

theorem card_D (dD : StrothWeakTypeData D (.t100 m)) : Nat.card D = 2 ^ (3 * m + 2) := by
  rw [dD.card]
  change 2 ^ (m + (m + 1) + (m + 1)) = 2 ^ (3 * m + 2)
  ring_nf

theorem φuv_om_ne (hm : 1 ≤ m) :
    (StrothTypeIndex.t100 m).action.φuv (om100 m ![1, 0, 0]) ≠ om100 m ![1, 0, 0] := by
  rw [t100_φuv_om hm]
  intro h
  have h1 := (om100_eq_iff hm _ _).mp h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
  norm_num [Int.ModEq] at h1

theorem uv_not_mem (dD : StrothWeakTypeData D (.t100 m)) (hm : 1 ≤ m) :
    ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w :=
  dD.not_forall_commute_uv_of_torus (by rw [two_nsmul]; exact om100_add_self hm _) (φuv_om_ne hm)

theorem c_pow_mem (dD : StrothWeakTypeData D (.t100 m)) (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) ∈ omegaIn 1 D := by
  rw [dD.t100_c_pow]
  exact mem_omegaIn_one_of_mul_self (dD.ofTorus_mem _)
    (by rw [← dD.ofTorus_add, om100_add_self hm, dD.ofTorus_zero])

theorem c_pow_not_commute (dD : StrothWeakTypeData D (.t100 m)) (hm : 1 ≤ m) :
    ¬ (dD.c : G) ^ 2 ^ (m - 1) * dD.uv = dD.uv * (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [dD.t100_c_pow, dD.uv_mul_ofTorus]
  intro h
  exact φuv_om_ne hm (dD.ofTorus_inj (mul_right_cancel h).symm)

theorem hA (h : F.IsD D dD) (hm : 2 ≤ m) :
    ∀ g ∈ Subgroup.normalizer
        (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G),
      D.map (MulAut.conj g).toMonoidHom ⊓ ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ D →
      ∀ y ∈ D.map (MulAut.conj g).toMonoidHom, ∀ w ∈ omegaIn 1 D, w * y = y * w := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  refine h.hA_of_torus (two_le_k hm) (uv_not_mem dD hm1) (v₁ := om100 (m' + 2) ![0, 1, 0])
    (v₂ := om100 (m' + 2) ![0, 0, 1]) (z := Torus.ofInt _ ![0, 2 ^ m', 0]) ?_
    (om100_add_self hm1 _) ?_ ?_ ?_ ?_
  · rw [← natCast_zsmul, ← Torus.ofInt_zsmul, om100]
    congr 1
    funext i
    fin_cases i <;> simp [StrothTypeIndex.k, Type100.k] <;> ring
  · intro h0
    have h1 := (om100_eq_iff hm1 _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    norm_num [Int.ModEq] at h1
  · rw [t100_φu_om]
    congr 1
  · rw [t100_φuv_om hm1]
    refine (om100_eq_iff hm1 _ _).mpr fun i => ?_
    fin_cases i <;> simp [Int.ModEq] <;> decide
  · rw [t100_φt_om hm1]
    refine (om100_eq_iff hm1 _ _).mpr fun i => ?_
    fin_cases i <;> simp [Int.ModEq] <;> decide

theorem bound_ii (dD : StrothWeakTypeData D (.t100 m)) (hm : 2 ≤ m) {e : G}
    (heN : e ∈ Subgroup.normalizer (D : Set G))
    (heC : e ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hc : e⁻¹ * (dD.c : G) * e = dD.c) (ha : e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m)
    (hb : e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m) {x : G} (hx : x = 1 ∨ x = e) :
    8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D := by
  have hm1 : 1 ≤ m := by omega
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDs := card_D dD
  have hcomm' : ∀ (g : G) (q : ℕ), g * g ^ q * g⁻¹ = g ^ q := fun g q => by
    rw [(Commute.self_pow g q).eq, mul_inv_cancel_right]
  have hae : e⁻¹ * (dD.a : G) * e * (dD.a : G)⁻¹ = (dD.a : G) ^ 2 ^ m := by rw [ha, hcomm']
  have hbe : e⁻¹ * (dD.b : G) * e * (dD.b : G)⁻¹ = (dD.b : G) ^ 2 ^ m := by rw [hb, hcomm']
  have hom1 : om100 m ![0, 1, 0] ≠ 0 := by
    rw [← om100_zero]
    intro h0
    have h1 := (om100_eq_iff hm1 _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
    norm_num [Int.ModEq] at h1
  have hom2 : om100 m ![0, 0, 1] ≠ 0 := by
    rw [← om100_zero]
    intro h0
    have h1 := (om100_eq_iff hm1 _ _).mp h0 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at h1
    norm_num [Int.ModEq] at h1
  have hom12 : om100 m ![0, 1, 0] ≠ om100 m ![0, 0, 1] := by
    intro h0
    have h1 := (om100_eq_iff hm1 _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    norm_num [Int.ModEq] at h1
  have h4 := four_mul_card_inf_centralizer_le hcommD hDs heN dD.a.2 dD.b.2
    (by rw [hae, dD.t100_a_pow, Ne, dD.ofTorus_eq_one_iff]; exact hom1)
    (by rw [hbe, dD.t100_b_pow, Ne, dD.ofTorus_eq_one_iff]; exact hom2)
    (by rw [hae, hbe, dD.t100_a_pow, dD.t100_b_pow, Ne, dD.ofTorus_inj.eq_iff]; exact hom12)
  have hxN : x ∈ Subgroup.normalizer (D : Set G) := by
    rcases hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact heN
  have hbN : dD.uv * x ∈ Subgroup.normalizer (D : Set G) := mul_mem dD.uv_mem hxN
  have hcH : (dD.c : G) ∈ D ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine ⟨dD.c.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (dD.c : G) * e = e * (e⁻¹ * (dD.c : G) * e) := by group
      _ = e * dD.c := by rw [hc]
  have hcb : ¬ (dD.c : G) ^ 2 ^ (m - 1) * (dD.uv * x) = dD.uv * x * (dD.c : G) ^ 2 ^ (m - 1) := by
    refine not_commute_mul_of_commute (c_pow_not_commute dD hm1) ?_
    rcases hx with rfl | rfl
    · rw [mul_one, one_mul]
    · exact Subgroup.mem_centralizer_iff.mp heC _ (c_pow_mem dD hm1)
  have h2m := two_pow_mul_card_inf_centralizer_le hcommD hDs inf_le_left hbN hcH hcb
  have heq : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) =
      D ⊓ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) :=
    inf_right_comm _ _ _
  rw [heq]
  have hpos : 0 < Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
      Subgroup.centralizer ({dD.uv * x} : Set G)) := Nat.card_pos
  have h4m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h16 : 16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
      Subgroup.centralizer ({dD.uv * x} : Set G)) ≤ Nat.card D := by
    calc 16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({dD.uv * x} : Set G))
        = 4 * (4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({dD.uv * x} : Set G))) := by ring
      _ ≤ 4 * (2 ^ m * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({dD.uv * x} : Set G))) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ h4m)
      _ ≤ 4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G)) := Nat.mul_le_mul_left 4 h2m
      _ ≤ Nat.card D := h4
  omega

theorem bound_inv (dD : StrothWeakTypeData D (.t100 m)) (hm : 2 ≤ m) {e : G} {j t : ℕ}
    (hj : j = 2 ^ m * t) (hc : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (ha : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ j)
    (hb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ j) (y : G) :
    8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D := by
  have hle : D ⊓ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      omegaIn 1 D := by
    intro z hz
    have hzD : z ∈ D := hz.1.1
    have hze : z * e = e * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
    exact mem_omegaIn_one_of_mul_self hzD (dD.mul_self_eq_one_of_inv_shape
      (by change 3 ≤ m + 1; omega) (j := j) (t := t) (by rw [hj]; rfl) hc ha hb hzD hze)
  have h8 : Nat.card (omegaIn 1 D) = 8 :=
    natCard_omegaIn_one_of_pos dD.e (t100_one_le_k (by omega))
  have h1 := Subgroup.card_le_of_le hle
  rw [h8] at h1
  rw [card_D dD]
  have h256 : 2 ^ 8 ≤ 2 ^ (3 * m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Stroth310T100

open Stroth310T100

theorem StrothFrame.IsD.mem_normalizer_omegaIn_t100 (h : F.IsD D dD)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) →
        (StrothTypeIndex.t100 m).m = (StrothTypeIndex.t100 m).n)
    (h32 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))))
    {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · refine h.mem_normalizer_omegaIn_of_card_le ?_ hgS
    rw [card_D dD]
    interval_cases m <;> norm_num
  have hm1 : 1 ≤ m := by omega
  refine h.mem_normalizer_omegaIn_of_cases (by change m ≠ m + 1; omega) (t100_one_le_k hm1)
    (Stroth310T100.uv_not_mem dD hm1) h226 (Stroth310T100.hA h hm) ?_ hgN
  rcases h32 with hRD | ⟨e, heR, hRe, -, -, -, hshape⟩
  · intro x _ Q hQR hQD _
    exact absurd (hRD ▸ hQR) hQD
  have heN : e ∈ Subgroup.normalizer (D : Set G) := (Subgroup.mem_inf.mp heR).1.2
  have heC := (Subgroup.mem_inf.mp heR).2
  have hc2 : (dD.c : G) ^ 2 ^ (m - 1) ∈ D := pow_mem dD.c.2 _
  rcases hshape with ⟨hc, ha, hb, he2⟩ | ⟨hc, ha, hb, he2⟩ | ⟨hc, ha, hb, he2⟩
  · refine h.hB_of_zpowers hRe heN (he2 ▸ mul_mem (inv_mem dD.c.2) hc2) ?_
      (Stroth310T100.bound_ii dD hm heN heC hc ha hb (Or.inr rfl))
    simpa using Stroth310T100.bound_ii dD hm heN heC hc ha hb (x := 1) (Or.inl rfl)
  · have ha' : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ (2 ^ m * 0) := by
      rw [ha, mul_zero, pow_zero, mul_one]
    have hb' : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ (2 ^ m * 0) := by
      rw [hb, mul_zero, pow_zero, mul_one]
    exact h.hB_of_zpowers hRe heN (he2 ▸ one_mem D)
      (Stroth310T100.bound_inv dD hm rfl hc ha' hb' _)
      (Stroth310T100.bound_inv dD hm rfl hc ha' hb' _)
  · have ha' : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ (2 ^ m * 1) := by
      rw [ha, mul_one]
    have hb' : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ (2 ^ m * 1) := by
      rw [hb, mul_one]
    exact h.hB_of_zpowers hRe heN (he2 ▸ hc2)
      (Stroth310T100.bound_inv dD hm rfl hc ha' hb' _)
      (Stroth310T100.bound_inv dD hm rfl hc ha' hb' _)

end CFSG.CGT.Stroth77
