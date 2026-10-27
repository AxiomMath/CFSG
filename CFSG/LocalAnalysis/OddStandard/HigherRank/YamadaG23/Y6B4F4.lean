module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4X2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_F_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) {f m : G} (hf : f ∈ c.s.fr.F)
    (hm : m ∈ M3 c.s) : f * m = m * f := by
  haveI := y6e_M3_comm c hF
  exact Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s)
    ((le_sup_right : c.s.fr.F ≤ M3 c.s) hf) hm

private lemma y6b_g_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) {m : G}
    (hm : m ∈ M3 c.s) : c.g * m = m * c.g := by
  have hg := hF.2.2.2.1 hRT m hm
  have hgsq : c.g * c.g = 1 := y6b_g_sq c hRT
  have hgi : c.g⁻¹ = c.g := inv_eq_of_mul_eq_one_right hgsq
  rw [hgi] at hg
  calc c.g * m = (c.g * m * c.g) * c.g := by
        rw [mul_assoc (c.g * m) c.g c.g, hgsq, mul_one]
    _ = m * c.g := by rw [hg]

private lemma y6b_E16_comm_M3 (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) {e m : G}
    (he : e ∈ y6bE16 c) (hm : m ∈ M3 c.s) : e * m = m * e := by
  have hFc : c.s.fr.F ≤ Subgroup.centralizer (M3 c.s : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro m' hm'
    exact (y6b_F_comm_M3 c hF hf hm').symm
  have hgc : zpowers c.g ≤ Subgroup.centralizer (M3 c.s : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro m' hm'
    exact (y6b_g_comm_M3 c hF hRT hm').symm
  have hmem : e ∈ Subgroup.centralizer (M3 c.s : Set G) := (sup_le hFc hgc) he
  exact (Subgroup.mem_centralizer_iff.mp hmem m hm).symm

private lemma y6b_E16_comm_t (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    {e : G} (he : e ∈ y6bE16 c) : e * c.s.t = c.s.t * e := by
  rw [y6b_mem_E16 c hH hRT] at he
  obtain ⟨f, hf, rfl | rfl⟩ := he
  · exact s3_comm_t_of_mem_A c.s (s3_F_le_A c.s hf)
  · calc f * c.g * c.s.t = f * (c.g * c.s.t) := by rw [mul_assoc]
      _ = f * (c.s.t * c.g) := by rw [y6b_g_comm_t c hRT]
      _ = f * c.s.t * c.g := by rw [mul_assoc]
      _ = c.s.t * f * c.g := by rw [s3_comm_t_of_mem_A c.s (s3_F_le_A c.s hf)]
      _ = c.s.t * (f * c.g) := by rw [mul_assoc]

private lemma y6b_E16_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {e : G}
    (he : e ∈ y6bE16 c) : e ^ 2 = 1 := by
  rw [pow_two]
  exact y6b_E_sq c hH hRT (y6b_E16_le_E c he)

private lemma y6b_E_decomp (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {e : G}
    (he : e ∈ y6bE c) :
    (∃ e₁ ∈ y6bE16 c, e = e₁) ∨ (∃ e₁ ∈ y6bE16 c, e = e₁ * c.s.t) := by
  rw [y6b_mem_E c hH hRT] at he
  obtain ⟨f, hf, h | h | h | h⟩ := he
  · exact Or.inl ⟨f, y6b_F_le_E16 c hf, h⟩
  · exact Or.inl ⟨f * c.g, (y6bE16 c).mul_mem (y6b_F_le_E16 c hf) (y6b_g_mem_E16 c), h⟩
  · exact Or.inr ⟨f, y6b_F_le_E16 c hf, h⟩
  · refine Or.inr ⟨f * c.g, (y6bE16 c).mul_mem (y6b_F_le_E16 c hf) (y6b_g_mem_E16 c), ?_⟩
    rw [h, mul_assoc]

theorem y6b_t_inv_M3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m⁻¹ := by
  rcases hF.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, -, -, hinv⟩
  · exfalso
    have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
    have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hA
    obtain ⟨hord, -⟩ := Ctx5pre.u_facts c.toCtx5.toCtx5pre hz2
    have hdt : c.d * c.s.t ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.mem_zpowers _
    have hdtM : c.d * c.s.t ∈ M3 c.s := (inf_le_right : V1 c.e ≤ M3 c.s) hdt
    have h2 : (c.d * c.s.t) ^ 2 = 1 := hE.2 _ hdtM
    have hdvd : orderOf (c.d * c.s.t) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    omega
  · exact hinv

theorem y6b_M3_sq_mem_F (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ w ∈ M3 c.s, w ^ 2 ∈ c.s.fr.F := by
  intro w hw
  obtain ⟨eM⟩ := y6e_M3_equiv c hH hF
  have hcomp : ∀ a : Multiplicative (ZMod 4), a ^ 4 = 1 := by decide
  have hpow4 : ∀ x : Fin 3 → Multiplicative (ZMod 4), x ^ 4 = 1 := fun x => by
    funext i
    simpa [Pi.pow_apply] using hcomp (x i)
  have hw4 : w ^ 4 = 1 := by
    have h1 : (⟨w, hw⟩ : ↥(M3 c.s)) ^ 4 = 1 := by
      apply eM.injective
      rw [map_pow, map_one]
      exact hpow4 _
    simpa using congrArg (fun x : ↥(M3 c.s) => (x : G)) h1
  refine y6e_sqone_mem_of_card (M := M3 c.s) (F := c.s.fr.F) le_sup_right eM (y54_F_sq hH)
    (by rw [(y54_F_isE3 hH).2]; norm_num) ((M3 c.s).pow_mem hw 2) ?_
  calc (w ^ 2) ^ 2 = w ^ (2 * 2) := (pow_mul w 2 2).symm
    _ = w ^ 4 := by norm_num
    _ = 1 := hw4

theorem y6b_M3_sqone (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ w ∈ M3 c.s, w ^ 2 = 1 → w ∈ c.s.fr.F := by
  intro w hw hw2
  obtain ⟨eM⟩ := y6e_M3_equiv c hH hF
  exact y6e_sqone_mem_of_card (M := M3 c.s) (F := c.s.fr.F) le_sup_right eM (y54_F_sq hH)
    (by rw [(y54_F_isE3 hH).2]; norm_num) hw hw2

theorem y6b_a_conj_M3_E16 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) {P : Subgroup G} (hP : Y6bPData c.toCtx5 P) {a : G} (haP : a ∈ P)
    (haF : ∀ f ∈ c.s.fr.F, a * f = f * a) :
    ∀ w ∈ M3 c.s, ∃ e ∈ y6bE16 c.toCtx5, a * w * a⁻¹ = e * w := by
  intro w hw
  by_cases hwF : w ∈ c.s.fr.F
  · refine ⟨1, (y6bE16 c.toCtx5).one_mem, ?_⟩
    rw [one_mul, haF w hwF, mul_assoc, mul_inv_cancel, mul_one]
  · have hw2ne : w ^ 2 ≠ 1 := fun h => hwF (y6b_M3_sqone c hH hF w hw h)
    have hwT3 : w ∈ y6bT3 c.toCtx5 := Subgroup.mem_sup_right hw
    have hw'T3 : a * w * a⁻¹ ∈ y6bT3 c.toCtx5 :=
      y6b_normal_of_card (P := P) (T := y6bT3 c.toCtx5) hP.1 hP.2.2.1 a haP w hwT3
    have hw'cent : ∀ f ∈ c.s.fr.F, (a * w * a⁻¹) * f = f * (a * w * a⁻¹) := by
      intro f hf
      have haf : a⁻¹ * f = f * a⁻¹ := (show Commute a f from haF f hf).inv_left
      have hwf : w * f = f * w := (y6b_F_comm_M3 c.toCtx5 hF hf hw).symm
      calc a * w * a⁻¹ * f = a * w * (a⁻¹ * f) := by group
        _ = a * w * (f * a⁻¹) := by rw [haf]
        _ = a * (w * f) * a⁻¹ := by group
        _ = a * (f * w) * a⁻¹ := by rw [hwf]
        _ = (a * f) * w * a⁻¹ := by group
        _ = (f * a) * w * a⁻¹ := by rw [haF f hf]
        _ = f * (a * w * a⁻¹) := by group
    have hw'W : a * w * a⁻¹ ∈ y6bW c.toCtx5 :=
      y6b_T3_cent_F_le_W c.toCtx5 hH hF hRT _ hw'T3 hw'cent
    rw [y6b_mem_W c.toCtx5 hH hF hRT] at hw'W
    obtain ⟨e, he, m, hm, hw'eq⟩ := hw'W
    have hw'sq : (a * w * a⁻¹) ^ 2 = w ^ 2 := by
      have h1 : (a * w * a⁻¹) ^ 2 = a * w ^ 2 * a⁻¹ := by
        simp only [pow_two]
        group
      rw [h1, haF (w ^ 2) (y6b_M3_sq_mem_F c hH hF w hw), mul_assoc, mul_inv_cancel, mul_one]
    rcases y6b_E_decomp c.toCtx5 hH hRT he with ⟨e₁, he₁, heeq⟩ | ⟨e₁, he₁, heeq⟩
    · have he₁m : Commute e₁ m := y6b_E16_comm_M3 c.toCtx5 hF hRT he₁ hm
      have hsqe : (a * w * a⁻¹) ^ 2 = m ^ 2 := by
        rw [hw'eq, heeq, he₁m.mul_pow, y6b_E16_sq c.toCtx5 hH hRT he₁, one_mul]
      have hm2 : m ^ 2 = w ^ 2 := by rw [← hsqe, hw'sq]
      haveI := y6e_M3_comm c.toCtx5 hF
      have hcomm_mw : Commute m w⁻¹ :=
        Subgroup.mul_comm_of_mem_isMulCommutative (M3 c.s) hm ((M3 c.s).inv_mem hw)
      have hsq_mw : (m * w⁻¹) ^ 2 = 1 := by
        rw [hcomm_mw.mul_pow, inv_pow w 2, hm2, mul_inv_cancel]
      have hmwF : m * w⁻¹ ∈ c.s.fr.F :=
        y6b_M3_sqone c hH hF (m * w⁻¹) ((M3 c.s).mul_mem hm ((M3 c.s).inv_mem hw)) hsq_mw
      refine ⟨e₁ * (m * w⁻¹), (y6bE16 c.toCtx5).mul_mem he₁ (y6b_F_le_E16 c.toCtx5 hmwF), ?_⟩
      rw [hw'eq, heeq]
      group
    · exfalso
      have htinv : c.s.t * m * c.s.t = m⁻¹ := by
        have h := y6b_t_inv_M3 c hH hF m hm
        have ht2 : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right (y6b_t_sq c.toCtx5)
        rwa [ht2] at h
      have htm : (c.s.t * m) ^ 2 = 1 := by
        rw [pow_two]
        calc (c.s.t * m) * (c.s.t * m) = (c.s.t * m * c.s.t) * m := by group
          _ = m⁻¹ * m := by rw [htinv]
          _ = 1 := inv_mul_cancel m
      have he1t : e₁ * c.s.t = c.s.t * e₁ := y6b_E16_comm_t c.toCtx5 hH hRT he₁
      have he1m : e₁ * m = m * e₁ := y6b_E16_comm_M3 c.toCtx5 hF hRT he₁ hm
      have hcommt : Commute e₁ (c.s.t * m) := by
        calc e₁ * (c.s.t * m) = (e₁ * c.s.t) * m := by rw [mul_assoc]
          _ = (c.s.t * e₁) * m := by rw [he1t]
          _ = c.s.t * (e₁ * m) := by rw [mul_assoc]
          _ = c.s.t * (m * e₁) := by rw [he1m]
          _ = (c.s.t * m) * e₁ := by rw [mul_assoc]
      have hsq1 : (a * w * a⁻¹) ^ 2 = 1 := by
        rw [hw'eq, heeq, mul_assoc, hcommt.mul_pow, y6b_E16_sq c.toCtx5 hH hRT he₁, htm,
          one_mul]
      rw [hw'sq] at hsq1
      exact hw2ne hsq1

end CFSG.OddStandard.HigherRank.YamadaG23
