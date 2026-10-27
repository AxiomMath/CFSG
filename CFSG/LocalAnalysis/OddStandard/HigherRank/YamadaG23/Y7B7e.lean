module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7d

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_t_sq (c : Ctx7 G L) : c.s.t * c.s.t = 1 := by
  rw [← pow_two, ← c.s.t_order]
  exact pow_orderOf_eq_one c.s.t

private lemma y7b_B_le_H (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.B ≤ c.s.H :=
  (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))

private lemma y7b_C_le_NBM (c : Ctx7 G L) (hb : B5Std c) :
    y7bC c.s ≤ normalizer (y7bBM c.s : Set G) := by
  refine sup_le ?_ ?_
  · intro n hn
    exact inf_normalizer_le_normalizer_sup (c.s.fr.B) (M3 c.s)
      (Subgroup.mem_inf.mpr ⟨hn.2, y7b_N_le_NM3 c hb hn⟩)
  · intro m hm
    exact Subgroup.le_normalizer (H := y7bBM c.s) (Subgroup.mem_sup_right hm)

private theorem y7b_beta_iff (c : Ctx7 G L) (hb : B5Std c) {x y : G}
    (hx : x ∈ y7bX c.s) (hy : y ∈ y7bX c.s) :
    (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s) =
      (QuotientGroup.mk (y * c.s.t * y⁻¹) : G ⧸ M3 c.s) ↔ x⁻¹ * y ∈ y7bC c.s := by
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right (y7b_t_sq c)
  have hxy : x⁻¹ * y ∈ y7bX c.s :=
    (y7bX c.s).mul_mem ((y7bX c.s).inv_mem hx) hy
  have hxN : x ∈ normalizer (M3 c.s : Set G) := (Subgroup.mem_inf.mp hx).2
  rw [QuotientGroup.eq]
  have hconj : (x * c.s.t * x⁻¹)⁻¹ * (y * c.s.t * y⁻¹) ∈ M3 c.s ↔
      x⁻¹ * ((x * c.s.t * x⁻¹)⁻¹ * (y * c.s.t * y⁻¹)) * x ∈ M3 c.s :=
    Subgroup.mem_normalizer_iff''.mp hxN _
  rw [hconj]
  have hinv : (x * c.s.t * x⁻¹)⁻¹ = x * c.s.t * x⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, htinv]
    group
  have hmid : x⁻¹ * ((x * c.s.t * x⁻¹)⁻¹ * (y * c.s.t * y⁻¹)) * x =
      ⁅c.s.t, x⁻¹ * y⁆ := by
    rw [hinv, commutatorElement_def, htinv]
    group
  rw [hmid]
  have hcomm_eq : ⁅c.s.t, x⁻¹ * y⁆ = (⁅x⁻¹ * y, c.s.t⁆)⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hcomm_eq, Subgroup.inv_mem_iff]
  exact ⟨fun h => y7b_cent_tbar c hb (x⁻¹ * y) hxy h,
    fun h => y7b_comm_t_of_mem_C c hb (x⁻¹ * y) h⟩

theorem y7b_Xp_stab (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bC c.s ⊔ M4 c.e, x ∈ normalizer (y7bBM c.s : Set G) ∧ ⁅x, c.s.t⁆ ∈ y7bBM c.s := by
  refine y7b_stab_sup (K := y7bBM c.s) (t := c.s.t) ?_ ?_
  · intro x hx
    exact ⟨y7b_C_le_NBM c hb hx,
      Subgroup.mem_sup_right (y7b_comm_t_of_mem_C c hb x hx)⟩
  · intro x hx
    exact ⟨y7b_M4_le_NBM c hb hx, y7b_comm_M4_t_mem_BM c hb x hx⟩

theorem y7b_relIndex_C_Xp (c : Ctx7 G L) (hb : B5Std c) :
    (y7bC c.s).relIndex (y7bC c.s ⊔ M4 c.e) = 4 := by
  have htN : c.s.t ∈ normalizer (M3 c.s : Set G) :=
    y7b_W_le_NM3 c hb (y7b_t_mem_W c hb)
  have htinv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right (y7b_t_sq c)
  have hX' : y7bC c.s ⊔ M4 c.e ≤ y7bX c.s :=
    sup_le (y7b_C_le_X c hb) (y7b_M4_le_X c hb)
  have hβ : ∀ x ∈ y7bC c.s ⊔ M4 c.e, ∀ y ∈ y7bC c.s ⊔ M4 c.e,
      (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s) =
        (QuotientGroup.mk (y * c.s.t * y⁻¹) : G ⧸ M3 c.s) ↔ x⁻¹ * y ∈ y7bC c.s :=
    fun x hx y hy => y7b_beta_iff c hb (hX' hx) (hX' hy)
  have hmain := y7b_relIndex_eq_ncard_image (C := y7bC c.s) (X := y7bC c.s ⊔ M4 c.e)
    le_sup_left (fun x => (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s)) hβ
  have hset : (fun x => (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s)) ''
        ((y7bC c.s ⊔ M4 c.e : Subgroup G) : Set G) =
      (fun b => (QuotientGroup.mk (b * c.s.t) : G ⧸ M3 c.s)) '' (c.s.fr.B : Set G) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨_, hxcomm⟩ := y7b_Xp_stab c hb x hx
      obtain ⟨b, hbB, m, hmM3, hbm⟩ := (y7b_mem_BM c hb).mp hxcomm
      refine ⟨b, hbB, ?_⟩
      show (QuotientGroup.mk (b * c.s.t) : G ⧸ M3 c.s) = QuotientGroup.mk (x * c.s.t * x⁻¹)
      have hxeq : x * c.s.t * x⁻¹ = (b * m) * c.s.t := by
        have h1 : x * c.s.t * x⁻¹ * c.s.t = b * m := by
          rw [← hbm, commutatorElement_def, htinv]
        calc x * c.s.t * x⁻¹ = x * c.s.t * x⁻¹ * (c.s.t * c.s.t) := by
              rw [y7b_t_sq c, mul_one]
          _ = (x * c.s.t * x⁻¹ * c.s.t) * c.s.t := by rw [← mul_assoc]
          _ = (b * m) * c.s.t := by rw [h1]
      rw [hxeq, QuotientGroup.eq]
      have hgoal : (b * c.s.t)⁻¹ * ((b * m) * c.s.t) = c.s.t⁻¹ * m * c.s.t := by group
      rw [hgoal]
      exact (Subgroup.mem_normalizer_iff''.mp htN m).mp hmM3
    · rintro ⟨b, hbB, rfl⟩
      by_cases hbF : b ∈ c.s.fr.F
      · refine ⟨1, (y7bC c.s ⊔ M4 c.e).one_mem, ?_⟩
        show QuotientGroup.mk (1 * c.s.t * 1⁻¹) = QuotientGroup.mk (b * c.s.t)
        rw [QuotientGroup.eq]
        have hgoal : (1 * c.s.t * 1⁻¹)⁻¹ * (b * c.s.t) = c.s.t⁻¹ * b * c.s.t := by group
        rw [hgoal]
        exact (Subgroup.mem_normalizer_iff''.mp htN b).mp (Subgroup.mem_sup_right hbF)
      · have hnotEF : ¬ c.s.fr.E ≤ c.s.fr.F := by
          intro hle
          have hcard : Nat.card ↥(c.s.fr.E ⊓ c.s.fr.F) = Nat.card ↥c.s.fr.E := by
            rw [inf_eq_left.mpr hle]
          rw [y7b_E_inf_F hb.hH, y7b_card_V hb.hH, y7b_card_E hb.hH] at hcard
          exact absurd hcard (by norm_num)
        obtain ⟨e, heE, heF⟩ := Set.not_subset.mp hnotEF
        obtain ⟨m, hmM4, hmφ⟩ := y7b_phi_M4 c hb e heE
        obtain ⟨k, hkN, hk3, hk1, _, _, _⟩ := f3_exists_k hb.hH
        have heB : e ∈ c.s.fr.B :=
          ((le_sup_left.trans (le_of_eq (y7b_EF_eq hb.hH))).trans inf_le_right) heE
        obtain ⟨i, hi⟩ := y7b_k_trans_BF hb.hH hkN hk3 hk1 e heB heF b hbB hbF
        have hLH : L ≤ c.s.H := s3_L_le_H c.s hb.hH.hS
        have hkiN : k ^ i ∈ normIn L c.s.fr.B := Subgroup.pow_mem (normIn L c.s.fr.B) hkN i
        have hkiC : k ^ i ∈ y7bC c.s :=
          Subgroup.mem_sup_left
            (show k ^ i ∈ normIn c.s.H c.s.fr.B from ⟨hLH hkiN.1, hkiN.2⟩)
        refine ⟨k ^ i * m, (y7bC c.s ⊔ M4 c.e).mul_mem
          (Subgroup.mem_sup_left hkiC) (Subgroup.mem_sup_right hmM4), ?_⟩
        show (QuotientGroup.mk ((k ^ i * m) * c.s.t * (k ^ i * m)⁻¹) : G ⧸ M3 c.s) =
          QuotientGroup.mk (b * c.s.t)
        have hkH : k ∈ c.s.H := hLH hkN.1
        have hkti : c.s.t * (k ^ i) = (k ^ i) * c.s.t :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem c.s.H hkH i) c.s.t (by simp)
        have hti_inv : (k ^ i)⁻¹ * c.s.t = c.s.t * (k ^ i)⁻¹ := by
          have h := congrArg Inv.inv hkti
          simpa [htinv] using h
        have hmt : m * c.s.t * m⁻¹ = e * c.s.t := by
          have h := hmφ
          rw [commutatorElement_def, htinv] at h
          calc m * c.s.t * m⁻¹ = m * c.s.t * m⁻¹ * (c.s.t * c.s.t) := by
                rw [y7b_t_sq c, mul_one]
            _ = (m * c.s.t * m⁻¹ * c.s.t) * c.s.t := by group
            _ = e * c.s.t := by rw [h]
        have hxeq : (k ^ i * m) * c.s.t * (k ^ i * m)⁻¹ =
            (k ^ i * e * (k ^ i)⁻¹) * c.s.t := by
          calc (k ^ i * m) * c.s.t * (k ^ i * m)⁻¹
              = k ^ i * (m * c.s.t * m⁻¹) * (k ^ i)⁻¹ := by group
            _ = k ^ i * (e * c.s.t) * (k ^ i)⁻¹ := by rw [hmt]
            _ = (k ^ i * e * (k ^ i)⁻¹) * c.s.t := by
                  calc k ^ i * (e * c.s.t) * (k ^ i)⁻¹
                      = k ^ i * e * (c.s.t * (k ^ i)⁻¹) := by group
                    _ = k ^ i * e * ((k ^ i)⁻¹ * c.s.t) := by rw [← hti_inv]
                    _ = (k ^ i * e * (k ^ i)⁻¹) * c.s.t := by group
        rw [hxeq, QuotientGroup.eq]
        have hgoal : ((k ^ i * e * (k ^ i)⁻¹) * c.s.t)⁻¹ * (b * c.s.t) =
            c.s.t⁻¹ * (b⁻¹ * (k ^ i * e * (k ^ i)⁻¹))⁻¹ * c.s.t := by group
        rw [hgoal]
        have hz : (b⁻¹ * (k ^ i * e * (k ^ i)⁻¹))⁻¹ ∈ M3 c.s :=
          (M3 c.s).inv_mem (Subgroup.mem_sup_right hi)
        exact (Subgroup.mem_normalizer_iff''.mp htN _).mp hz
  have hγ : ∀ b ∈ c.s.fr.B, ∀ b' ∈ c.s.fr.B,
      (QuotientGroup.mk (b * c.s.t) : G ⧸ M3 c.s) =
        (QuotientGroup.mk (b' * c.s.t) : G ⧸ M3 c.s) ↔ b⁻¹ * b' ∈ c.s.fr.F := by
    intro b hbB b' hb'B
    rw [QuotientGroup.eq]
    have hBF : b⁻¹ * b' ∈ c.s.fr.B :=
      (c.s.fr.B).mul_mem ((c.s.fr.B).inv_mem hbB) hb'B
    have hbtprod : c.s.t * (b⁻¹ * b') = (b⁻¹ * b') * c.s.t :=
      Subgroup.mem_centralizer_iff.mp (y7b_B_le_H c hb hBF) c.s.t (by simp)
    have hcomm : (b * c.s.t)⁻¹ * (b' * c.s.t) = b⁻¹ * b' := by
      calc (b * c.s.t)⁻¹ * (b' * c.s.t)
          = c.s.t⁻¹ * (b⁻¹ * b') * c.s.t := by group
        _ = c.s.t * (b⁻¹ * b') * c.s.t := by rw [htinv]
        _ = b⁻¹ * b' := by rw [hbtprod, mul_assoc, y7b_t_sq c, mul_one]
    rw [hcomm, ← y7b_B_inf_M3 c hb]
    simp [Subgroup.mem_inf, hBF]
  have hγcard : ((fun b => (QuotientGroup.mk (b * c.s.t) : G ⧸ M3 c.s)) ''
      (c.s.fr.B : Set G)).ncard = 4 := by
    rw [← y7b_relIndex_eq_ncard_image (C := c.s.fr.F) (X := c.s.fr.B) (y54_F_le_B hb.hH)
      (fun b => (QuotientGroup.mk (b * c.s.t) : G ⧸ M3 c.s)) hγ]
    exact y7b_relIndex_F_B c hb
  rw [hmain, hset, hγcard]

theorem y7b_relIndex_C_X_le (c : Ctx7 G L) (hb : B5Std c) :
    (y7bC c.s).relIndex (y7bX c.s) ≤ 7 := by
  have hβ : ∀ x ∈ y7bX c.s, ∀ y ∈ y7bX c.s,
      (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s) =
        (QuotientGroup.mk (y * c.s.t * y⁻¹) : G ⧸ M3 c.s) ↔ x⁻¹ * y ∈ y7bC c.s :=
    fun x hx y hy => y7b_beta_iff c hb hx hy
  have hmain := y7b_relIndex_eq_ncard_image (C := y7bC c.s) (X := y7bX c.s)
    (y7b_C_le_X c hb) (fun x => (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s)) hβ
  have hM3W : M3 c.s ≤ y7bW c.s := by
    have hM3C3 : M3 c.s ≤ C3 c.s := by
      rw [y54_C3_eq_M3 c.toCtx5 hb.hH]
      exact le_sup_left
    rw [y7bW]
    exact hM3C3.trans le_sup_right
  have hWncard : ((fun w => (QuotientGroup.mk w : G ⧸ M3 c.s)) ''
      (y7bW c.s : Set G)).ncard = 8 := by
    rw [← y7b_relIndex_eq_ncard_image hM3W (fun w => (QuotientGroup.mk w : G ⧸ M3 c.s))
      (fun x _ y _ => QuotientGroup.eq)]
    exact y7b_relIndex_M3_W c hb
  have hsubset : (fun x => (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s)) ''
        (y7bX c.s : Set G)
      ⊆ ((fun w => (QuotientGroup.mk w : G ⧸ M3 c.s)) '' (y7bW c.s : Set G)) \
        {QuotientGroup.mk 1} := by
    rintro w ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have hxNW : x ∈ normalizer (y7bW c.s : Set G) := (Subgroup.mem_inf.mp hx).1
      exact ⟨x * c.s.t * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxNW c.s.t).mp (y7b_t_mem_W c hb), rfl⟩
    · intro hmem1
      have h : (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s) = QuotientGroup.mk 1 := by
        simpa using hmem1
      have hmem : x * c.s.t * x⁻¹ ∈ M3 c.s := by
        have h' : (x * c.s.t * x⁻¹)⁻¹ ∈ M3 c.s := by
          simpa using (QuotientGroup.eq (a := x * c.s.t * x⁻¹) (b := 1)).mp h
        simpa using (M3 c.s).inv_mem h'
      have htM3 : c.s.t ∈ M3 c.s := by
        have hxN : x ∈ normalizer (M3 c.s : Set G) := (Subgroup.mem_inf.mp hx).2
        have hconj : x⁻¹ * (x * c.s.t * x⁻¹) * x ∈ M3 c.s :=
          (Subgroup.mem_normalizer_iff''.mp hxN _).mp hmem
        convert hconj using 1
        group
      exact y7b_t_not_mem_BM3 c hb (Subgroup.mem_sup_right htM3)
  have hd : (((fun w => (QuotientGroup.mk w : G ⧸ M3 c.s)) '' (y7bW c.s : Set G)) \
      {QuotientGroup.mk 1}).ncard = 7 := by
    have hmem1 : (QuotientGroup.mk 1 : G ⧸ M3 c.s) ∈
        (fun w => (QuotientGroup.mk w : G ⧸ M3 c.s)) '' (y7bW c.s : Set G) :=
      ⟨1, Subgroup.one_mem _, rfl⟩
    rw [Set.ncard_sdiff_singleton_of_mem hmem1, hWncard]
  rw [hmain]
  calc ((fun x => (QuotientGroup.mk (x * c.s.t * x⁻¹) : G ⧸ M3 c.s)) ''
        (y7bX c.s : Set G)).ncard
      ≤ (((fun w => (QuotientGroup.mk w : G ⧸ M3 c.s)) '' (y7bW c.s : Set G)) \
          {QuotientGroup.mk 1}).ncard := Set.ncard_le_ncard hsubset
    _ = 7 := hd

theorem y7b_X_eq_Xp (c : Ctx7 G L) (hb : B5Std c) : y7bX c.s = y7bC c.s ⊔ M4 c.e := by
  have h := y7b_eq_of_relIndex_le (C := y7bC c.s) (Z := y7bC c.s ⊔ M4 c.e) (X := y7bX c.s)
    le_sup_left (sup_le (y7b_C_le_X c hb) (y7b_M4_le_X c hb))
    (y7b_relIndex_C_Xp c hb) (by norm_num) (y7b_relIndex_C_X_le c hb) (by norm_num)
  exact h.symm

theorem y7b_X_norm_BM (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bX c.s, ∀ u ∈ y7bBM c.s, x * u * x⁻¹ ∈ y7bBM c.s := by
  intro x hx u hu
  rw [y7b_X_eq_Xp c hb] at hx
  exact (Subgroup.mem_normalizer_iff.mp (y7b_Xp_stab c hb x hx).1 u).mp hu

theorem y7b_comm_t_mem_BM (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bX c.s, ⁅x, c.s.t⁆ ∈ y7bBM c.s := by
  intro x hx
  rw [y7b_X_eq_Xp c hb] at hx
  exact (y7b_Xp_stab c hb x hx).2

end CFSG.OddStandard.HigherRank.YamadaG23
