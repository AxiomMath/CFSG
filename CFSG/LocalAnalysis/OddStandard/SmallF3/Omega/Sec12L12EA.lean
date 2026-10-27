module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec12E_f_mul_aux (t p q : G) :
    sec12f t (p * q) = p * sec12f t q * p⁻¹ * sec12f t p := by
  rw [sec12f, sec12f, sec12f]
  group

theorem sec12E_f_conj {y : G} (hy : y * t = t * y) (p : G) :
    sec12f t (y * p * y⁻¹) = y * sec12f t p * y⁻¹ := by
  have hyt : y⁻¹ * t * y = t := by rw [mul_assoc, ← hy]; group
  have hyinv : y⁻¹ * t⁻¹ = t⁻¹ * y⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hy]
  rw [sec12f, sec12f]
  calc (y * p * y⁻¹) * t * (y * p * y⁻¹)⁻¹ * t⁻¹
      = y * p * (y⁻¹ * t * y) * p⁻¹ * (y⁻¹ * t⁻¹) := by group
    _ = y * p * t * p⁻¹ * (t⁻¹ * y⁻¹) := by rw [hyt, hyinv]
    _ = y * (p * t * p⁻¹ * t⁻¹) * y⁻¹ := by group

theorem sec12E_B_comm (F : Sec12Frame t L S) {b b' : G} (hb : b ∈ secB S L)
    (hb' : b' ∈ secB S L) : b * b' = b' * b := by
  have hb'L : b' ∈ L := F.bdata.1 hb'
  have hb'C : b' ∈ centralizer (secB S L : Set G) := by
    have h : b' ∈ centralizer (secB S L : Set G) ⊓ L := by
      rw [F.bdata.2.2.1]
      exact hb'
    exact h.1
  exact (Subgroup.mem_centralizer_iff.mp hb'C) b hb

theorem sec12E_B_sq (F : Sec12Frame t L S) {b : G} (hb : b ∈ secB S L) : b * b = 1 := by
  obtain ⟨φ, hperm, -⟩ := F.bdata.2.2.2.2.2
  obtain ⟨v, hv, hvφ⟩ := (hperm.2.2.1 b).1 hb
  have h0 : v + v = 0 := by
    funext i
    show v i + v i = 0
    have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (R := ZMod 2) (p := 2)
    calc v i + v i = (2 : ZMod 2) * v i := (two_mul (v i)).symm
      _ = 0 := by rw [h2, zero_mul]
  have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hφ0 : φ 0 = 1 := by
    have h00 : φ 0 = φ 0 * φ 0 := by simpa using hperm.1 0 0 h0ev h0ev
    exact mul_eq_left.mp h00.symm
  calc b * b = φ v * φ v := by rw [hvφ]
    _ = φ (v + v) := (hperm.1 v v hv hv).symm
    _ = φ 0 := by rw [h0]
    _ = 1 := hφ0

theorem sec12E_t_comm_B (F : Sec12Frame t L S) {b : G} (hb : b ∈ secB S L) :
    t * b = b * t := by
  exact ((Subgroup.mem_centralizer_iff.mp F.htC) b (F.bdata.1 hb)).symm

theorem sec12E_t_sq (F : Sec12Frame t L S) : t * t = 1 := by
  rw [← pow_two, ← F.ht2]
  exact pow_orderOf_eq_one t

theorem sec12E_mem_A (F : Sec12Frame t L S) {x : G} :
    x ∈ secA t S L ↔ x ∈ secB S L ∨ ∃ b ∈ secB S L, x = t * b := by
  constructor
  · intro hx
    have hc : ∀ h ∈ secB S L, ∀ k ∈ zpowers t, h * k = k * h := by
      intro h hh k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      exact (Commute.symm (sec12E_t_comm_B F hh)).zpow_right n
    obtain ⟨h, hh, k, hk, hxk⟩ :=
      exists_mul_of_mem_sup_of_commute hc (show x ∈ secB S L ⊔ zpowers t from hx)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hk_cases : t ^ n = 1 ∨ t ^ n = t := by
      have hn2 : (orderOf t : ℤ) = 2 := by rw [F.ht2]; norm_num
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · left; rw [← zpow_mod_orderOf t n, hn2, h0]; simp
      · right; rw [← zpow_mod_orderOf t n, hn2, h1]; simp
    rcases hk_cases with h1 | ht
    · left; rw [hxk, h1, mul_one]; exact hh
    · right; exact ⟨h, hh, by rw [hxk, ht, (sec12E_t_comm_B F hh).symm]⟩
  · rintro (hxB | ⟨b, hb, rfl⟩)
    · exact Subgroup.mem_sup_left hxB
    · have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      have hbA : b ∈ secA t S L := Subgroup.mem_sup_left (T := zpowers t) hb
      exact (secA t S L).mul_mem htA hbA

private theorem sec12E_A_t_comm (F : Sec12Frame t L S) {a : G} (ha : a ∈ secA t S L) :
    a * t = t * a := by
  rcases (sec12E_mem_A F).mp ha with haB | ⟨b, hb, rfl⟩
  · exact (sec12E_t_comm_B F haB).symm
  · rw [show (t * b) * t = t * (b * t) by group, sec12E_t_comm_B F hb]

private theorem sec12E_A_B_comm (F : Sec12Frame t L S) {a : G} (ha : a ∈ secA t S L)
    {b : G} (hb : b ∈ secB S L) : a * b = b * a := by
  rcases (sec12E_mem_A F).mp ha with haB | ⟨b0, hb0, rfl⟩
  · exact sec12E_B_comm F haB hb
  · calc (t * b0) * b = t * (b0 * b) := by group
      _ = t * (b * b0) := by rw [sec12E_B_comm F hb0 hb]
      _ = (t * b) * b0 := by group
      _ = (b * t) * b0 := by rw [(sec12E_t_comm_B F hb).symm]
      _ = b * (t * b0) := by group

private theorem mem_secCMB_iff {p : G} :
    p ∈ secCMB t S L ↔ p ∈ secM t S L ∧ p ∈ centralizer (secB S L : Set G) := by
  rw [secCMB, Subgroup.mem_inf]

theorem sec12E_A_comm (F : Sec12Frame t L S) {a a' : G} (ha : a ∈ secA t S L)
    (ha' : a' ∈ secA t S L) : a * a' = a' * a := by
  rcases (sec12E_mem_A F).mp ha' with ha'B | ⟨b, hb, rfl⟩
  · exact sec12E_A_B_comm F ha ha'B
  · calc a * (t * b) = (a * t) * b := by group
      _ = (t * a) * b := by rw [sec12E_A_t_comm F ha]
      _ = t * (a * b) := by group
      _ = t * (b * a) := by rw [sec12E_A_B_comm F ha hb]
      _ = (t * b) * a := by group

theorem sec12E_A_sq (F : Sec12Frame t L S) {a : G} (ha : a ∈ secA t S L) : a * a = 1 := by
  rcases (sec12E_mem_A F).mp ha with haB | ⟨b, hb, rfl⟩
  · exact sec12E_B_sq F haB
  · calc (t * b) * (t * b) = t * (b * t) * b := by group
      _ = t * (t * b) * b := by rw [sec12E_t_comm_B F hb]
      _ = (t * t) * (b * b) := by group
      _ = 1 := by rw [sec12E_t_sq F, sec12E_B_sq F hb, one_mul]

theorem sec12E_A_le_P (F : Sec12Frame t L S) : secA t S L ≤ secCMB t S L := by
  intro a ha
  rw [mem_secCMB_iff]
  refine ⟨?_, ?_⟩
  · simpa only [secM] using (Subgroup.le_normalizer (H := secA t S L)) ha
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact sec12E_A_comm F (Subgroup.mem_sup_left hb) ha

theorem sec12E_C_le_P (F : Sec12Frame t L S) :
    centralizer (secA t S L : Set G) ≤ secCMB t S L := by
  intro p hp
  rw [mem_secCMB_iff]
  refine ⟨?_, ?_⟩
  · simpa only [secM] using
      (Subgroup.centralizer_le_normalizer (secA t S L : Set G)) hp
  · exact (Subgroup.centralizer_le (s := (secB S L : Set G)) (t := (secA t S L : Set G))
      (fun x hx => Subgroup.mem_sup_left hx)) hp

theorem sec12E_P_normal (F : Sec12Frame t L S) {m p : G} (hm : m ∈ secM t S L)
    (hp : p ∈ secCMB t S L) : m * p * m⁻¹ ∈ secCMB t S L := by
  rw [mem_secCMB_iff] at hp ⊢
  refine ⟨?_, ?_⟩
  · exact (secM t S L).mul_mem ((secM t S L).mul_mem hm hp.1) ((secM t S L).inv_mem hm)
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb'B : m⁻¹ * b * m ∈ secB S L := by
      simpa using F.normB m⁻¹ ((secM t S L).inv_mem hm) b hb
    have hb'p : (m⁻¹ * b * m) * p = p * (m⁻¹ * b * m) :=
      (Subgroup.mem_centralizer_iff.mp hp.2) (m⁻¹ * b * m) hb'B
    calc b * (m * p * m⁻¹) = m * (m⁻¹ * b * m) * p * m⁻¹ := by group
      _ = m * ((m⁻¹ * b * m) * p) * m⁻¹ := by group
      _ = m * (p * (m⁻¹ * b * m)) * m⁻¹ := by rw [hb'p]
      _ = (m * p * m⁻¹) * b := by group

theorem sec12E_f_mem (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    sec12f t p ∈ secB S L := by
  have hpM : p ∈ secM t S L := (mem_secCMB_iff.mp hp).1
  have hmem : p * t * p⁻¹ ∈ secTB t S L := by
    rw [F.alt1.2.1]
    exact ⟨p, hpM, rfl⟩
  obtain ⟨b, hb, hpb⟩ := hmem
  have hfp : sec12f t p = b := by
    rw [sec12f, hpb, sec12E_t_comm_B F hb]
    group
  rwa [hfp]

theorem sec12E_f_mul (F : Sec12Frame t L S) {p q : G} (hp : p ∈ secCMB t S L)
    (hq : q ∈ secCMB t S L) : sec12f t (p * q) = sec12f t p * sec12f t q := by
  have hpC : p ∈ centralizer (secB S L : Set G) := (mem_secCMB_iff.mp hp).2
  have hqB : sec12f t q ∈ secB S L := sec12E_f_mem F hq
  have hpB : sec12f t p ∈ secB S L := sec12E_f_mem F hp
  rw [sec12E_f_mul_aux]
  have hconj : p * sec12f t q * p⁻¹ = sec12f t q := by
    have hcomm : sec12f t q * p = p * sec12f t q :=
      (Subgroup.mem_centralizer_iff.mp hpC) (sec12f t q) hqB
    rw [← hcomm]; group
  rw [hconj]
  exact sec12E_B_comm F hqB hpB

theorem sec12E_f_eq_one (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    sec12f t p = 1 ↔ p ∈ centralizer (secA t S L : Set G) := by
  have hpC : p ∈ centralizer (secB S L : Set G) := (mem_secCMB_iff.mp hp).2
  constructor
  · intro hfp
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases (sec12E_mem_A F).mp ha with haB | ⟨b, hb, rfl⟩
    · exact (Subgroup.mem_centralizer_iff.mp hpC) a haB
    · have hfp' : p * t * p⁻¹ * t⁻¹ = 1 := by simpa [sec12f] using hfp
      have hpt : p * t = t * p := by
        calc p * t = (p * t * p⁻¹ * t⁻¹) * (t * p) := by group
          _ = 1 * (t * p) := by rw [hfp']
          _ = t * p := by group
      have hbp : b * p = p * b := (Subgroup.mem_centralizer_iff.mp hpC) b hb
      calc (t * b) * p = t * (b * p) := by group
        _ = t * (p * b) := by rw [hbp]
        _ = (t * p) * b := by group
        _ = (p * t) * b := by rw [hpt]
        _ = p * (t * b) := by group
  · intro hpA
    have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have htp : t * p = p * t := (Subgroup.mem_centralizer_iff.mp hpA) t htA
    rw [sec12f]
    calc p * t * p⁻¹ * t⁻¹ = (p * t) * (t * p)⁻¹ := by group
      _ = 1 := by simp [htp]

theorem sec12E_f_surj (F : Sec12Frame t L S) {b : G} (hb : b ∈ secB S L) :
    ∃ p ∈ secCMB t S L, sec12f t p = b := by
  have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hbA : b ∈ secA t S L := Subgroup.mem_sup_left (T := zpowers t) hb
  have htbA : t * b ∈ secA t S L := (secA t S L).mul_mem htA hbA
  let x : ↥(secA t S L) := ⟨t, htA⟩
  let y : ↥(secA t S L) := ⟨t * b, htbA⟩
  have hxT : (x : G) ∈ secTB t S L := ⟨1, (secB S L).one_mem, by simp [x]⟩
  have hyT : (y : G) ∈ secTB t S L := ⟨b, hb, rfl⟩
  obtain ⟨c, hc, -⟩ := F.alt1.2.2.2.2.2 x y hxT hyT
  obtain ⟨n, hn, hnmap⟩ := Subgroup.mem_map.mp c.2
  have hnP : (n : G) ∈ secCMB t S L := by
    rwa [Subgroup.mem_subgroupOf] at hn
  have hnt : (n : G) * t * (n : G)⁻¹ = t * b := by
    have h1 : ((secA t S L).normalizerMonoidHom n) x = y := by
      rw [hnmap]; exact hc
    have h2 : (((secA t S L).normalizerMonoidHom n) x : G) = (y : G) :=
      congrArg Subtype.val h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    simpa [x, y] using h2
  refine ⟨(n : G), hnP, ?_⟩
  rw [sec12f, hnt, sec12E_t_comm_B F hb]
  group

end CFSG.OddStandard.SmallF3.Omega
