module

public import CFSG.CGT.Stroth77.Section44CoreA

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth44Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t201 m)) {e : G}

@[expose] def t201EAction
    (φe : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k)
    (ve : Torus (StrothTypeIndex.t201 m).k)
    (hφe : ∀ v, e⁻¹ * dD.ofTorus v * e = dD.ofTorus (φe v))
    (heuv : e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t) (heu : e⁻¹ * dD.u * e = dD.u)
    (he : e * e = dD.ofTorus ve) : dD.EAction e where
  φe := φe
  wuv := Torus.ofInt _ ![2, 2, 2]
  wt := Torus.ofInt _ ![0, -2, 0]
  ve := ve
  conj_ofTorus := hφe
  conj_uv := by
    rw [heuv, cab_eq, sq, ofTorus_ofInt_mul]
    congr 3
    funext i
    fin_cases i <;> simp <;> norm_num
  conj_t := by
    rw [het, dD.ofTorus_ofInt]
    simp [sq]
  conj_u := heu
  mul_self := he

@[expose] def t201iAction (heuv : e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t) (heu : e⁻¹ * dD.u * e = dD.u)
    (hec : e⁻¹ * (dD.c : G) * e = dD.c)
    (hea : e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1))
    (heb : e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1))
    (he : e * e = (dD.c : G)⁻¹) : dD.EAction e :=
  dD.t201EAction (torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (Torus.ofInt _ ![-1, 0, 0])
    (dD.conj_ofTorus_of_gens
      (by rw [hec, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
      (by
        rw [hea, torusDiag_gen, ofTorus_zsmul, ← a_eq,
          show (![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] : Fin 3 → ℤ) 1 = 1 + 2 ^ (m + 1) from rfl,
          zpow_add, zpow_one, show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast])
      (by
        rw [heb, torusDiag_gen, ofTorus_zsmul, ← b_eq,
          show (![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)] : Fin 3 → ℤ) 2 = 1 + 2 ^ (m + 1) from rfl,
          zpow_add, zpow_one, show ((2 : ℤ) ^ (m + 1)) = ((2 ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl,
          zpow_natCast]))
    heuv het heu
    (by
      rw [he, dD.ofTorus_ofInt]
      simp)

end StrothWeakTypeData

namespace Stroth44Core

section CaseII

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t201 m))
  {e : G} (hE : dD.EAction e)

open StrothWeakTypeData

theorem t201_ii_φe (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (x : Fin 3 → ℤ) : hE.φe (Torus.ofInt _ x) =
      Torus.ofInt _ ![x 0, (1 + 2 ^ (m + 1)) * x 1, (1 + 2 ^ (m + 1)) * x 2] := by
  rw [hφe, torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t201_φuv_z (hm : 1 ≤ m) :
    (StrothTypeIndex.t201 m).action.φuv (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1] := by
  rw [t201_φuv_om hm, om201_eq_iff hm]
  decide

theorem t201_φt_z (hm : 1 ≤ m) :
    (StrothTypeIndex.t201 m).action.φt (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1] := by
  rw [t201_φt_om hm, om201_eq_iff hm]
  decide

theorem t201_φu_z :
    (StrothTypeIndex.t201 m).action.φu (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1] := by
  rw [t201_φu_om]
  rfl

theorem t201_ii_φe_z (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]) :
    hE.φe (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1] := by
  rw [om201_apply, t201_ii_φe dD hE hφe, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨0, by ring⟩, ⟨-2 * 2 ^ k, by ring⟩, ⟨-2 * 2 ^ k, by ring⟩⟩

theorem t201_e_hC2c (hm : 1 ≤ m) (hez : hE.φe (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1]) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y := by
  intro y hy
  rw [z_om]
  suffices hS : D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e ≤
      Subgroup.centralizer {dD.ofTorus (om201 m ![0, 1, 1])} from
    Subgroup.mem_centralizer_singleton_iff.1 (hS hy)
  refine sup_le (sup_le (fun d hd => Subgroup.mem_centralizer_singleton_iff.2
    (mem_comm dD hd (dD.ofTorus_mem _))) ?_) ((Subgroup.zpowers_le).2 ?_)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · rw [dD.uv_mul_ofTorus, t201_φuv_z hm]
    · rw [dD.t_mul_ofTorus, t201_φt_z hm]
    · rw [dD.u_mul_ofTorus, t201_φu_z]
  · rw [Subgroup.mem_centralizer_singleton_iff, hE.e_mul_ofTorus, hez]

theorem ofTorus_conj_nfe {v q w : Torus (StrothTypeIndex.t201 m).k} {i j l : Bool}
    (hq : (StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe q) = q + w)
    (hw : (StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe w) = w) :
    (dD.ofTorus q)⁻¹ * (dD.ofTorus v * dD.d8 i j l * e) * dD.ofTorus q =
      dD.ofTorus v * dD.d8 i j l * e * dD.ofTorus w := by
  have hL : (dD.ofTorus q)⁻¹ * (dD.ofTorus v * dD.d8 i j l * e) * dD.ofTorus q =
      dD.ofTorus (-q + v + (StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe q)) *
        dD.d8 i j l * e := by
    calc (dD.ofTorus q)⁻¹ * (dD.ofTorus v * dD.d8 i j l * e) * dD.ofTorus q
        = (dD.ofTorus q)⁻¹ * dD.ofTorus v * (dD.d8 i j l * (e * dD.ofTorus q)) := by group
      _ = (dD.ofTorus q)⁻¹ * dD.ofTorus v *
          (dD.ofTorus ((StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe q)) * dD.d8 i j l) *
            e := by
          rw [hE.e_mul_ofTorus, ← mul_assoc (dD.d8 i j l), dD.d8_mul_ofTorus]
          group
      _ = _ := by
          rw [← dD.ofTorus_neg, ← mul_assoc, ← dD.ofTorus_add, ← dD.ofTorus_add]
  have hR : dD.ofTorus v * dD.d8 i j l * e * dD.ofTorus w =
      dD.ofTorus (v + (StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe w)) *
        dD.d8 i j l * e := by
    rw [mul_assoc _ e, hE.e_mul_ofTorus, ← mul_assoc, mul_assoc (dD.ofTorus v),
      dD.d8_mul_ofTorus, ← mul_assoc, ← dD.ofTorus_add]
  rw [hL, hR, hq, hw]
  congr 3
  rw [add_comm (-q) v, add_assoc, neg_add_cancel_left]

theorem t201_ii_conj_e (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]) (i j l : Bool) :
    ∃ q : Torus (StrothTypeIndex.t201 m).k,
      (StrothTypeIndex.t201 m).action.d8Act i j l (hE.φe q) = q + om201 m ![0, 1, 1] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [om201_apply]
  cases i <;> cases j <;> cases l
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1) - 1, 2 ^ (k + 1) - 1], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨1 - 2 ^ k, by ring⟩, ⟨1 - 2 ^ k, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨-2 * 2 ^ k, by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1)], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φt, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨1 + 8 * 2 ^ k + 16 * (2 ^ k) ^ 2, by ring⟩,
      ⟨1 + 3 * 2 ^ k + 4 * (2 ^ k) ^ 2, by ring⟩, ⟨1 + 2 * 2 ^ k + 4 * (2 ^ k) ^ 2, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, t201_φt, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨1 - 8 * (2 ^ k) ^ 2, by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 2 ^ (k + 1)], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨-2 - 8 * 2 ^ k, by ring⟩,
      ⟨-6 * 2 ^ k - 16 * (2 ^ k) ^ 2 - 16 * (2 ^ k) ^ 3, by ring⟩,
      ⟨-4 * 2 ^ k - 4 * (2 ^ k) ^ 2, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨-2 - 8 * 2 ^ k, by ring⟩, ⟨-2 * 2 ^ k, by ring⟩,
      ⟨-6 * 2 ^ k - 8 * (2 ^ k) ^ 2, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 0], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φt, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨1 - 16 * (2 ^ k) ^ 2, by ring⟩, ⟨1 - 4 * (2 ^ k) ^ 2, by ring⟩,
      ⟨1 + 2 ^ k - 8 * (2 ^ k) ^ 2 - 16 * (2 ^ k) ^ 3, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    rw [t201_ii_φe dD hE hφe]
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, t201_φt, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨2 - 32 * (2 ^ k) ^ 2, by ring⟩, ⟨1 - 8 * (2 ^ k) ^ 2, by ring⟩,
      ⟨2 + 2 * 2 ^ k - 16 * (2 ^ k) ^ 2 - 32 * (2 ^ k) ^ 3, by ring⟩⟩

theorem t201_ii_hC2 (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e, y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  intro y hy hy2 hy1 hyz
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hy2 hy1 hyz ⊢
    obtain ⟨q, hq, hq'⟩ := t201_hC2 dD hm _ (dD.nf_mem v i j l) hy2 hy1 hyz
    exact ⟨q, Subgroup.mem_sup_left hq, hq'⟩
  · simp only [bpow, ↓reduceIte] at hy2 hy1 hyz ⊢
    obtain ⟨q, hq⟩ := t201_ii_conj_e dD hE hm hφe i j l
    rw [z_om]
    refine ⟨dD.ofTorus q, Subgroup.mem_sup_left (Subgroup.mem_sup_left (dD.ofTorus_mem q)),
      ofTorus_conj_nfe dD hE hq ?_⟩
    rw [t201_ii_φe_z dD hE hm hφe, t201_d8Act_z hm]

theorem t201_d8Act_c₁ (hm : 1 ≤ m) {i j l : Bool}
    (h : (StrothTypeIndex.t201 m).action.d8Act i j l (om201 m ![1, 0, 0]) = om201 m ![1, 0, 0]) :
    i = false ∧ j = false := by
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t201_φuv_om hm, t201_φt_om hm, t201_φu_om, om201_eq_iff hm] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t201_ii_mem_of_mul_self (hm : 1 ≤ m)
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
  have hc₁ : hE.φe (om201 m ![1, 0, 0]) = om201 m ![1, 0, 0] := by
    rw [om201_apply, t201_ii_φe dD hE hφe]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [c_pow_om, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
    mul_left_inj] at hyc
  obtain ⟨rfl, rfl⟩ := t201_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
  rw [hE.nfe_e_mul_self, Bool.and_false, dD.d8_fff, mul_one, dD.ofTorus_eq_one_iff] at hy2
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have h0 := congrFun hy2 0
  simp only [EAction.sqE, EAction.twist, hve, Bool.false_eq_true, ↓reduceIte,
    SigmaFourAction.d8Act, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Bool.and_false,
    map_zero, add_zero] at h0
  have hk0 : (StrothTypeIndex.t201 m).k 0 ≠ 0 := by
    simp [StrothTypeIndex.k, Type201.k]
    omega
  have hodd : ∀ z : ℤ, ((2 * z - 1 : ℤ) : ZMod (2 ^ (StrothTypeIndex.t201 m).k 0)) ≠ 0 := by
    intro z hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have h2 : (2 : ℤ) ∣ 2 * z - 1 := dvd_trans (dvd_pow_self 2 hk0) (by exact_mod_cast hz)
    omega
  apply hodd (x 0)
  cases l <;>
    simp only [Bool.false_eq_true, ↓reduceIte, AddMonoidHom.id_apply, map_add, map_sub,
      t201_ii_φe dD hE hφe, t201_φu, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Torus.ofInt_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0 <;>
    push_cast <;> linear_combination h0

theorem t201_ii_h7 (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (hve : hE.ve = Torus.ofInt _ ![-1, 0, 0]) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ y ∈ E, y * y = 1) →
        Nat.card E ≠ 16 := by
  intro E hES hinv
  refine t201_h7 dD hm E (fun y hy => ?_) hinv
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp (hES hy)
  exact Subgroup.mem_inf.mpr ⟨t201_ii_mem_of_mul_self dD hE hm hφe hve hyS
    (Subgroup.mem_centralizer_singleton_iff.mp hyC) (hinv y hy), hyC⟩

theorem t201_ii_mem_CSc₁ (hm : 1 ≤ m)
    (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)]) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t201 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyc := Subgroup.mem_centralizer_singleton_iff.mp hyC
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hyS
  have hc₁ : hE.φe (om201 m ![1, 0, 0]) = om201 m ![1, 0, 0] := by
    rw [om201_apply, t201_ii_φe dD hE hφe]
    congr 1
    funext i
    fin_cases i <;> simp
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyc
    obtain ⟨rfl, rfl⟩ := t201_comm_c₁ dD hm hyc
    exact ⟨v, l, false, rfl⟩
  · simp only [bpow, ↓reduceIte] at hyc
    rw [c_pow_om, mul_assoc _ e, hE.e_mul_ofTorus, hc₁, ← mul_assoc, ← mul_assoc,
      mul_left_inj] at hyc
    obtain ⟨rfl, rfl⟩ := t201_d8Act_c₁ hm ((dD.nf_commute_iff _ _ _ _ _).mp hyc)
    exact ⟨v, l, true, rfl⟩

theorem t201_e_comm_iff (v₀ w : Torus (StrothTypeIndex.t201 m).k) (l k : Bool) :
    dD.ofTorus w * (dD.ofTorus v₀ * dD.d8 false false l * bpow e k) =
        dD.ofTorus v₀ * dD.d8 false false l * bpow e k * dD.ofTorus w ↔
      (StrothTypeIndex.t201 m).action.d8Act false false l (if k then hE.φe w else w) = w := by
  have hk : bpow e k * dD.ofTorus w = dD.ofTorus (if k then hE.φe w else w) * bpow e k := by
    cases k
    · simp [bpow]
    · simp only [bpow, ↓reduceIte]
      exact hE.e_mul_ofTorus w
  have hL : dD.ofTorus w * (dD.ofTorus v₀ * dD.d8 false false l * bpow e k) =
      dD.ofTorus (v₀ + w) * dD.d8 false false l * bpow e k := by
    rw [← mul_assoc, ← mul_assoc, ← dD.ofTorus_add, add_comm w v₀]
  have hR : dD.ofTorus v₀ * dD.d8 false false l * bpow e k * dD.ofTorus w =
      dD.ofTorus (v₀ + (StrothTypeIndex.t201 m).action.d8Act false false l
        (if k then hE.φe w else w)) * dD.d8 false false l * bpow e k := by
    rw [mul_assoc _ (bpow e k), hk, ← mul_assoc, mul_assoc (dD.ofTorus v₀), dD.d8_mul_ofTorus,
      ← mul_assoc, ← dD.ofTorus_add]
  rw [hL, hR, mul_left_inj, mul_left_inj, dD.ofTorus_inj.eq_iff]
  exact ⟨fun h => (add_left_cancel h).symm, fun h => by rw [h]⟩

theorem nfe_mul_inv_mem (v v' : Torus (StrothTypeIndex.t201 m).k) (l k : Bool) :
    dD.ofTorus v * dD.d8 false false l * bpow e k *
      (dD.ofTorus v' * dD.d8 false false l * bpow e k)⁻¹ ∈ D := by
  have h : dD.ofTorus v * dD.d8 false false l * bpow e k *
      (dD.ofTorus v' * dD.d8 false false l * bpow e k)⁻¹ = dD.ofTorus v * (dD.ofTorus v')⁻¹ := by
    group
  rw [h]
  exact mul_mem (dD.ofTorus_mem _) (inv_mem (dD.ofTorus_mem _))

theorem dvd_sub_val (n : ℕ) [NeZero n] (x : ℤ) : (n : ℤ) ∣ ((x : ZMod n).val : ℤ) - x := by
  rw [ZMod.val_intCast]
  exact ⟨-(x / n), by rw [Int.emod_def]; ring⟩

theorem card_le_of_cover {X : Subgroup G} {ι T : Type*} [Finite ι] [Finite T] (r : ι → G)
    (hr : ∀ j, r j ∈ X) (hcov : ∀ y ∈ X, ∃ j, y * (r j)⁻¹ ∈ D)
    (g : T → Torus (StrothTypeIndex.t201 m).k) (hg : ∀ d ∈ X, d ∈ D → ∃ s, d = dD.ofTorus (g s)) :
    Nat.card X ≤ Nat.card (ι × T) := by
  refine Stroth42Core.natCard_le_of_subset_range (fun w : ι × T => dD.ofTorus (g w.2) * r w.1)
    (fun y hy => ?_)
  obtain ⟨j, hj⟩ := hcov y hy
  obtain ⟨s, hs⟩ := hg _ (mul_mem hy (inv_mem (hr j))) hj
  exact ⟨(j, s), by simp only; rw [← hs, inv_mul_cancel_right]⟩

theorem t201_ii_comm_u (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (v₀ : Torus (StrothTypeIndex.t201 m).k) (k : Bool) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus v₀ * dD.d8 false false true * bpow e k) =
      dD.ofTorus v₀ * dD.d8 false false true * bpow e k * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ^ (m + 2) ∣ x 1 - (if k then 1 + 2 ^ (m + 1) else 1) * x 2 := by
  have hc := (t201_e_comm_iff dD hE v₀ _ true k).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  cases k
  · simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    rw [t201_φu, t201_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1
  · simp only [↓reduceIte] at hc ⊢
    rw [t201_ii_φe dD hE hφe, t201_φu, t201_ofInt_eq_iff] at hc
    obtain ⟨-, h1, -⟩ := hc
    simpa using h1

theorem t201_ii_comm_e (hφe : hE.φe = torusDiag _ ![1, 1 + 2 ^ (m + 1), 1 + 2 ^ (m + 1)])
    (v₀ : Torus (StrothTypeIndex.t201 m).k) (x : Fin 3 → ℤ)
    (h : dD.ofTorus (Torus.ofInt _ x) * (dD.ofTorus v₀ * dD.d8 false false false * bpow e true) =
      dD.ofTorus v₀ * dD.d8 false false false * bpow e true * dD.ofTorus (Torus.ofInt _ x)) :
    (2 : ℤ) ∣ x 1 ∧ (2 : ℤ) ∣ x 2 := by
  have hc := (t201_e_comm_iff dD hE v₀ _ false true).mp h
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at hc
  rw [t201_ii_φe dD hE hφe, t201_ofInt_eq_iff] at hc
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

theorem t201_ii_h9 (hm : 1 ≤ m)
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
  have hnf : ∀ y ∈ X, ∃ (v : Torus (StrothTypeIndex.t201 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k :=
    fun y hy => t201_ii_mem_CSc₁ dD hE hm hφe (hX hy)
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
        have h1 := t201_ii_comm_u dD hE hφe v₀ k₀ x (hcomm _ hd _ hx₀)
        refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((x 2 : ℤ) : ZMod (2 ^ (m + 2)))), ?_⟩
        congr 1
        rw [t201_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        have e0 := dvd_sub_val (2 ^ m) (x 0)
        have e2 := dvd_sub_val (2 ^ (m + 2)) (x 2)
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
        obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩ := t201_ii_comm_e dD hE hφe v₁ x (hcomm _ hd _ hx₁)
        refine ⟨(((x 0 : ℤ) : ZMod (2 ^ m)), ((y₁ : ℤ) : ZMod (2 ^ (m + 1))),
          ((y₂ : ℤ) : ZMod (2 ^ (m + 1)))), ?_⟩
        congr 1
        rw [t201_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        have e0 := dvd_sub_val (2 ^ m) (x 0)
        have e1 := dvd_sub_val (2 ^ (m + 1)) y₁
        have e2 := dvd_sub_val (2 ^ (m + 1)) y₂
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

end CaseII

end Stroth44Core

end CFSG.CGT.Stroth77
