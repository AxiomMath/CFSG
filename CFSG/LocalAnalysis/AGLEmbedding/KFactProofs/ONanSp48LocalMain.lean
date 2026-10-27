module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48LocalNF
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Local

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open

section Lattice

variable (r : Rels)

include r in
theorem gw_inv : gw⁻¹ = gw := inv_eq_of_mul_eq_one_right r.ww

include r in
theorem gs_inv : gs⁻¹ = gs := inv_eq_of_mul_eq_one_right r.ss

include r in
theorem conj_gw_t1 : gw * gt1 * gw⁻¹ = gt1 ^ 8 := by rw [gw_inv r]; exact r.wt1

include r in
theorem conj_gw_t2 : gw * gt2 * gw⁻¹ = gt2 := by
  rw [r.wt2, mul_assoc, mul_inv_cancel, mul_one]

include r in
theorem conj_gw_f : gw * gf * gw⁻¹ = gf := by
  rw [r.wf, mul_assoc, mul_inv_cancel, mul_one]

include r in
theorem conj_gs_t1 : gs * gt1 * gs⁻¹ = gt2 := by rw [gs_inv r]; exact r.st1

include r in
theorem conj_gs_t2 : gs * gt2 * gs⁻¹ = gt1 := by rw [gs_inv r]; exact r.st2

include r in
theorem conj_gs_f : gs * gf * gs⁻¹ = gf := by
  rw [r.sf, mul_assoc, mul_inv_cancel, mul_one]

include r in
theorem commute_t12 : Commute gt1 gt2 := r.t12

include r in
theorem conj_w_nf (i j k : ℕ) : gw * nfElt i j k * gw⁻¹ = gt1 ^ (8 * i) * gt2 ^ j * gf ^ k := by
  have h : ∀ x, gw * x * gw⁻¹ = MulAut.conj gw x := fun x => (MulAut.conj_apply gw x).symm
  rw [h, nfElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← h gt1, ← h gt2, ← h gf,
    conj_gw_t1 r, conj_gw_t2 r, conj_gw_f r, ← pow_mul, mul_comm 8 i]

include r in
theorem conj_s_nf (i j k : ℕ) : gs * nfElt i j k * gs⁻¹ = nfElt j i k := by
  have h : ∀ x, gs * x * gs⁻¹ = MulAut.conj gs x := fun x => (MulAut.conj_apply gs x).symm
  rw [h, nfElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← h gt1, ← h gt2, ← h gf,
    conj_gs_t1 r, conj_gs_t2 r, conj_gs_f r, nfElt, ((commute_t12 r).symm.pow_pow i j).eq]

variable {U : Subgroup Hh}

include r in
theorem pow_t1_mem (hw : ∀ x ∈ U, gw * x * gw⁻¹ ∈ U) {i j k : ℕ} (hx : nfElt i j k ∈ U) :
    gt1 ^ i ∈ U := by
  have hy : gt1 ^ (8 * i) * gt2 ^ j * gf ^ k ∈ U := by
    rw [← conj_w_nf r]
    exact hw _ hx
  have h2 : gt1 ^ (8 * i) * gt2 ^ j * gf ^ k * (nfElt i j k)⁻¹ ∈ U := U.mul_mem hy (U.inv_mem hx)
  have e2 : gt1 ^ (8 * i) * gt2 ^ j * gf ^ k * (nfElt i j k)⁻¹ = gt1 ^ (7 * i) := by
    have : gt1 ^ (8 * i) * gt2 ^ j * gf ^ k * (gt1 ^ i * gt2 ^ j * gf ^ k)⁻¹ =
        gt1 ^ (8 * i) * (gt1 ^ i)⁻¹ := by group
    rw [nfElt, this, show 8 * i = 7 * i + i by ring, pow_add, mul_inv_cancel_right]
  rw [e2] at h2
  have e3 : gt1 ^ i = (gt1 ^ (7 * i)) ^ 4 := by
    rw [← pow_mul, show 7 * i * 4 = i + 9 * (3 * i) by ring, pow_add, pow_mul, r.t1_9, one_pow,
      mul_one]
  rw [e3]
  exact U.pow_mem h2 4

include r in
theorem comps_mem (hw : ∀ x ∈ U, gw * x * gw⁻¹ ∈ U) (hs : ∀ x ∈ U, gs * x * gs⁻¹ ∈ U)
    {i j k : ℕ} (hx : nfElt i j k ∈ U) :
    gt1 ^ i ∈ U ∧ gt1 ^ j ∈ U ∧ gt2 ^ i ∈ U ∧ gt2 ^ j ∈ U ∧ gf ^ k ∈ U := by
  have h1 := pow_t1_mem r hw hx
  have h2 : gt1 ^ j ∈ U := pow_t1_mem r hw (by rw [← conj_s_nf r]; exact hs _ hx)
  have hc : ∀ n : ℕ, gt1 ^ n ∈ U → gt2 ^ n ∈ U := fun n hn => by
    have := hs _ hn
    rwa [← conj_pow (a := gs) (b := gt1) (i := n), conj_gs_t1 r] at this
  refine ⟨h1, h2, hc i h1, hc j h2, ?_⟩
  have : gf ^ k = (gt1 ^ i * gt2 ^ j)⁻¹ * nfElt i j k := by
    rw [nfElt, inv_mul_cancel_left]
  rw [this]
  exact U.mul_mem (U.inv_mem (U.mul_mem h1 (hc j h2))) hx

include r in
theorem t1_of_unit {i i' : ℕ} (h : i * i' % 9 = 1) (hi : gt1 ^ i ∈ U) : gt1 ∈ U := by
  have : gt1 = (gt1 ^ i) ^ i' := by
    rw [← pow_mul, pow_eq_pow_mod (i * i') r.t1_9, h, pow_one]
  rw [this]
  exact U.pow_mem hi i'

include r in
theorem t1_of_not_dvd {i : ℕ} (hi : i < 9) (h3 : ¬ 3 ∣ i) (hU : gt1 ^ i ∈ U) : gt1 ∈ U := by
  interval_cases i
  · omega
  · exact t1_of_unit r (i' := 1) (by norm_num) hU
  · exact t1_of_unit r (i' := 5) (by norm_num) hU
  · omega
  · exact t1_of_unit r (i' := 7) (by norm_num) hU
  · exact t1_of_unit r (i' := 2) (by norm_num) hU
  · omega
  · exact t1_of_unit r (i' := 4) (by norm_num) hU
  · exact t1_of_unit r (i' := 8) (by norm_num) hU

include r in
theorem f_of_pow {k : ℕ} (hk : k < 3) (hk0 : k ≠ 0) (hU : gf ^ k ∈ U) : gf ∈ U := by
  interval_cases k
  · omega
  · simpa using hU
  · have : gf = (gf ^ 2) ^ 2 := by
      rw [← pow_mul, pow_eq_pow_mod (2 * 2) r.f_3]
      norm_num
    rw [this]
    exact U.pow_mem hU 2

end Lattice

section Main

variable (hg : gensValid = true) (hnf : NF) (ho : Ord3) (hc : Centre) (r : Rels)

include hg hnf ho hc r in
theorem lattice_aux (U : Subgroup Hh) (hEU : Eh hnf ≤ U) (hUT : U ≤ Th hnf)
    (hinv : ∀ b ∈ ({gt1, gt2, gw, gs, gf} : Set Hh), ∀ x ∈ U, b * x * b⁻¹ ∈ U) :
    U = Eh hnf ∨ U = Ah hnf ho ∨ U = Th0 hnf ∨ U = Th hnf := by
  have hw : ∀ x ∈ U, gw * x * gw⁻¹ ∈ U := hinv gw (by simp)
  have hs : ∀ x ∈ U, gs * x * gs⁻¹ ∈ U := hinv gs (by simp)
  have hg2 : gt1 ∈ U → gt2 ∈ U := fun h => by
    have := hs _ h
    rwa [conj_gs_t1 r] at this
  have hdec : ∀ x ∈ U, ∃ i < 9, ∃ j < 9, ∃ k < 3, x = nfElt i j k :=
    fun x hx => (mem_Th hg hnf).1 (hUT hx)
  by_cases h1 : gt1 ∈ U <;> by_cases hf : gf ∈ U
  · right; right; right
    refine le_antisymm hUT fun x hx => ?_
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := (mem_Th hg hnf).1 hx
    exact U.mul_mem (U.mul_mem (U.pow_mem h1 i) (U.pow_mem (hg2 h1) j)) (U.pow_mem hf k)
  · right; right; left
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := hdec x hx
      have hk0 : k = 0 := by
        by_contra hk0
        exact hf (f_of_pow r hk hk0 (comps_mem r hw hs hx).2.2.2.2)
      subst hk0
      exact (mem_Th0 hg hnf).2 ⟨i, hi, j, hj, rfl⟩
    · obtain ⟨i, hi, j, hj, rfl⟩ := (mem_Th0 hg hnf).1 hx
      simp only [nfElt, pow_zero, mul_one]
      exact U.mul_mem (U.pow_mem h1 i) (U.pow_mem (hg2 h1) j)
  · right; left
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := hdec x hx
      have hcm := comps_mem r hw hs hx
      have hi3 : 3 ∣ i := by
        by_contra h
        exact h1 (t1_of_not_dvd r hi h hcm.1)
      have hj3 : 3 ∣ j := by
        by_contra h
        exact h1 (t1_of_not_dvd r hj h hcm.2.1)
      obtain ⟨a, rfl⟩ := hi3
      obtain ⟨b, rfl⟩ := hj3
      exact (mem_Ah hg hnf ho).2 ⟨a, by omega, b, by omega, k, hk, rfl⟩
    · obtain ⟨a, ha, b, hb, c, hc', rfl⟩ := (mem_Ah hg hnf ho).1 hx
      have e1 : gt1 ^ (3 * a) ∈ U :=
        hEU ((mem_Eh hg hnf hc).2 ⟨a, ha, 0, by norm_num, by simp [nfElt]⟩)
      have e2 : gt2 ^ (3 * b) ∈ U :=
        hEU ((mem_Eh hg hnf hc).2 ⟨0, by norm_num, b, hb, by simp [nfElt]⟩)
      exact U.mul_mem (U.mul_mem e1 e2) (U.pow_mem hf c)
  · left
    refine le_antisymm (fun x hx => ?_) hEU
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := hdec x hx
    have hcm := comps_mem r hw hs hx
    have hi3 : 3 ∣ i := by
      by_contra h
      exact h1 (t1_of_not_dvd r hi h hcm.1)
    have hj3 : 3 ∣ j := by
      by_contra h
      exact h1 (t1_of_not_dvd r hj h hcm.2.1)
    have hk0 : k = 0 := by
      by_contra hk0
      exact hf (f_of_pow r hk hk0 hcm.2.2.2.2)
    subst hk0
    obtain ⟨a, rfl⟩ := hi3
    obtain ⟨b, rfl⟩ := hj3
    exact (mem_Eh hg hnf hc).2 ⟨a, by omega, b, by omega, rfl⟩

include hg hnf hc in
theorem norm_of_normC {b bi : Hh} {bc bic : Pc} (hb : RepP bc b) (hbi : RepP bic bi)
    (hn : NormC bc bic) :
    (∀ x ∈ Th hnf, b * x * b⁻¹ ∈ Th hnf) ∧ (∀ x ∈ Eh hnf, b * x * b⁻¹ ∈ Eh hnf) := by
  have hinv : b⁻¹ = bi := by
    have : b * bi = 1 := eq_of_code (hb.mul hbi) RepP.one hn.inv
    exact (eq_inv_of_mul_eq_one_right this).symm
  rw [hinv]
  refine ⟨fun x ⟨p, hp, hx⟩ => ⟨_, hn.normT p hp, (hb.mul hx).mul hbi⟩, fun x hx => ?_⟩
  obtain ⟨p, hp, hx⟩ := (mem_Eh_code hg hnf hc).1 hx
  exact (mem_Eh_code hg hnf hc).2 ⟨_, hn.normE p hp, (hb.mul hx).mul hbi⟩

include hg hnf hc in
theorem norm_all (hn : NormAll) :
    ∀ b ∈ ({gt1, gt2, gw, gs, gf} : Set Hh),
      (∀ x ∈ Th hnf, b * x * b⁻¹ ∈ Th hnf) ∧ (∀ x ∈ Eh hnf, b * x * b⁻¹ ∈ Eh hnf) := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact norm_of_normC hg hnf hc (repP_gt1 hg) ((repP_gt1 hg).pow 8) hn.t1
  · exact norm_of_normC hg hnf hc (repP_gt2 hg) ((repP_gt2 hg).pow 8) hn.t2
  · exact norm_of_normC hg hnf hc (repP_gw hg) (repP_gw hg) hn.w
  · exact norm_of_normC hg hnf hc (repP_gs hg) (repP_gs hg) hn.s
  · exact norm_of_normC hg hnf hc repP_gf (repP_gf.pow 2) hn.f

include hg hnf hc in
theorem rank_aux (ho3 : Ord3) (F : Subgroup Hh) (hF : F ≤ Th0 hnf) (hFe : IsElemAbelian 3 F) :
    Nat.card F ≤ 9 := by
  have hFE : F ≤ Eh hnf := by
    intro x hx
    obtain ⟨⟨p, hp, hxp⟩, hxr⟩ := (mem_Th0_iff hnf).1 (hF hx)
    have hj : p.j = 0 := (right_eq_one_iff hxp).1 hxr
    have h3 : powP p 3 = oneP := by
      have := hxp.pow 3
      rw [hFe.2 x hx] at this
      exact this.code_eq RepP.one
    exact (mem_Eh_code hg hnf hc).2 ⟨p, ho3.order3 p hp hj h3, hxp⟩
  calc Nat.card F ≤ Nat.card (Eh hnf) := Subgroup.card_le_of_le hFE
    _ = 9 := card_Eh hg hnf hc

theorem mem_zpowers_cube {y x : Hh} (hy : y ^ 3 = 1) (hx : x ∈ Subgroup.zpowers y) :
    x = 1 ∨ x = y ∨ x = y * y := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hn : y ^ n = y ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul]
    have : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy
    rw [this, one_zpow, mul_one]
  rw [hn]
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have h3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp [sq]

theorem exists_pow_of_zpow {g : Hh} (h : g ^ 9 = 1) (m : ℤ) : ∃ a < 9, g ^ m = g ^ a := by
  refine ⟨(m % 9).toNat, by omega, ?_⟩
  conv_lhs => rw [← Int.emod_add_mul_ediv m 9]
  rw [zpow_add, zpow_mul]
  have : g ^ (9 : ℤ) = 1 := by exact_mod_cast h
  rw [this, one_zpow, mul_one, ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))]

@[expose] noncomputable def uElt : Fin 4 → Hh := ![1, gt1, gt1 ^ 2, gt2]

@[expose] noncomputable def uInv : Fin 4 → Hh := ![1, gt1 ^ 8, gt1 ^ 7, gt2 ^ 8]

include hg in
theorem repU (k : Fin 4) :
    RepP (uList[(k : ℕ)]!).1 (uElt k) ∧ RepP (uList[(k : ℕ)]!).2 (uInv k) := by
  fin_cases k
  · exact ⟨RepP.one, RepP.one⟩
  · exact ⟨repP_gt1 hg, (repP_gt1 hg).pow 8⟩
  · exact ⟨(repP_gt1 hg).pow 2, (repP_gt1 hg).pow 7⟩
  · exact ⟨repP_gt2 hg, (repP_gt2 hg).pow 8⟩

include r in
theorem uElt_mul_uInv (k : Fin 4) : uElt k * uInv k = 1 := by
  fin_cases k
  · simp [uElt, uInv]
  · simp only [uElt, uInv, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← pow_succ']; exact r.t1_9
  · show gt1 ^ 2 * gt1 ^ 7 = 1
    rw [← pow_add]; exact r.t1_9
  · show gt2 * gt2 ^ 8 = 1
    rw [← pow_succ']; exact r.t2_9

include hg hnf in
theorem uElt_mem (k : Fin 4) : uElt k ∈ Th0 hnf := by
  fin_cases k
  · exact (mem_Th0 hg hnf).2 ⟨0, by norm_num, 0, by norm_num, by simp [uElt, nfElt]⟩
  · exact (mem_Th0 hg hnf).2 ⟨1, by norm_num, 0, by norm_num, by simp [uElt, nfElt]⟩
  · exact (mem_Th0 hg hnf).2 ⟨2, by norm_num, 0, by norm_num, by simp [uElt, nfElt]⟩
  · exact (mem_Th0 hg hnf).2 ⟨0, by norm_num, 1, by norm_num, by simp [uElt, nfElt]⟩

include hg hnf ho hc r in
theorem orbit_aux (hor : ∀ p ∈ lstA, p ∈ lstE ∨ ∀ k < 4, ∀ l < 4, k = l ∨
      (cj k p ≠ oneP ∧ cj k p ≠ cj l p) ∧ cj k p ≠ mulP (cj l p) (cj l p))
    (a : Hh) (ha : a ∈ Ah hnf ho) (haE : a ∉ Eh hnf) (W : Fin 3 → Subgroup Hh) :
    ∃ u ∈ Th0 hnf, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i := by
  by_contra hcon
  push Not at hcon
  choose f hf using fun k : Fin 4 => hcon (uElt k) (uElt_mem hg hnf k)
  obtain ⟨k, l, hkl, hfkl⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  obtain ⟨p, hp, hap⟩ := ha
  have hpE : p ∉ lstE := fun hpe => haE ((mem_Eh_code hg hnf hc).2 ⟨p, hpe, hap⟩)
  have ha3 : a ^ 3 = 1 := eq_of_code (hap.pow 3) RepP.one (ho.pow3 p hp)
  have hinv : ∀ k : Fin 4, (uElt k)⁻¹ = uInv k := fun k =>
    (eq_inv_of_mul_eq_one_right (uElt_mul_uInv r k)).symm
  set c : Fin 4 → Hh := fun k => uElt k * a * uInv k with hcdef
  have hmap : ∀ k : Fin 4, (Subgroup.zpowers a).map (MulAut.conj (uElt k)).toMonoidHom =
      Subgroup.zpowers (c k) := fun k => by
    rw [MonoidHom.map_zpowers]
    congr 1
    show uElt k * a * (uElt k)⁻¹ = c k
    rw [hinv]
  have hrep : ∀ k : Fin 4, RepP (cj k p) (c k) := fun k =>
    (((repU hg k).1).mul hap).mul (repU hg k).2
  have hc3 : ∀ k : Fin 4, c k ^ 3 = 1 := fun k => by
    show (uElt k * a * uInv k) ^ 3 = 1
    rw [← hinv k, conj_pow, ha3, mul_one, mul_inv_cancel]
  have heq : Subgroup.zpowers (c k) = Subgroup.zpowers (c l) := by
    rw [← hmap, ← hmap, hf k, hf l, hfkl]
  have hmem : c k ∈ Subgroup.zpowers (c l) := heq ▸ Subgroup.mem_zpowers (c k)
  have hne : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
  have hor' := ((hor p hp).resolve_left hpE) k.1 k.2 l.1 l.2
  rcases hor'.resolve_left hne with ⟨⟨h1, h2⟩, h3⟩
  rcases mem_zpowers_cube (hc3 l) hmem with h | h | h
  · exact h1 ((h ▸ hrep k).code_eq RepP.one)
  · exact h2 ((h ▸ hrep k).code_eq (hrep l))
  · exact h3 ((h ▸ hrep k).code_eq ((hrep l).mul (hrep l)))

include r in
theorem order_t1 : orderOf gt1 = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := orderOf_eq_prime_pow (p := 3) (n := 1) (x := gt1) (by simpa using r.t1_3)
    (by simpa using r.t1_9)
  simpa using this

include r in
theorem order_t2 : orderOf gt2 = 9 := by
  have : gt2 = (MulAut.conj gs) gt1 := by rw [MulAut.conj_apply, conj_gs_t1 r]
  rw [this, MulEquiv.orderOf_eq]
  exact order_t1 r

include hg r in
theorem inf_t_aux (hom : ∀ a < 9, ∀ b < 9, powP t1c a ≠ powP t2c b ∨ a = 0) :
    Subgroup.zpowers gt1 ⊓ Subgroup.zpowers gt2 = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx2
  obtain ⟨a, ha, hma⟩ := exists_pow_of_zpow r.t1_9 m
  obtain ⟨b, hb, hnb⟩ := exists_pow_of_zpow r.t2_9 n
  rw [hnb, hma] at hn
  have hcode : powP t2c b = powP t1c a :=
    ((repP_gt2 hg).pow b).code_eq (hn ▸ ((repP_gt1 hg).pow a))
  have ha0 : a = 0 := (hom a ha b hb).resolve_left (fun h => h hcode.symm)
  rw [hma, ha0, pow_zero]
  exact Subgroup.one_mem _

end Main

theorem check_parts (h : sp48LocalCheck = true) :
    gensValid = true ∧ relOK = true ∧ normalFormOK = true ∧ centreOK = true ∧
      ordThreeOK = true ∧ normalOK = true ∧ orbitOK = true ∧ homOK = true := by
  simp only [sp48LocalCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

theorem sp48Local_of_check (h : sp48LocalCheck = true) :
    ∃ (T A E T0 : Subgroup Hh) (t1 t2 w s f : Hh), Sp48Local T A E T0 t1 t2 w s f := by
  obtain ⟨hg, hr, hn, hce, hord, hnorm, horb, hhom⟩ := check_parts h
  have hnf := nf_of_check hn
  have ho := ord3_of_check hord
  have hc := centre_of_check hce
  have r := rels_of_check hg hr
  have hN := norm_of_check hnorm
  have hor := orbit_of_check horb
  have hhm := hom_of_check hhom
  have hEcode : ∀ z, z ∈ Eh hnf → ∃ p ∈ lstE, RepP p z := fun z hz =>
    (mem_Eh_code hg hnf hc).1 hz
  refine ⟨Th hnf, Ah hnf ho, Eh hnf, Th0 hnf, gt1, gt2, gw, gs, gf, ?_⟩
  exact
  { card_T := (card_Th hg hnf).trans (by norm_num)
    T0_eq := rfl
    card_T0 := (card_Th0 hg hnf).trans (by norm_num)
    E_eq := rfl
    card_E := (card_Eh hg hnf hc).trans (by norm_num)
    E_pow := fun z hz => by
      obtain ⟨p, hp, hzp⟩ := hEcode z hz
      exact eq_of_code (hzp.pow 3) RepP.one (ho.pow3 p (hnf.subE p hp))
    A_le := fun x ⟨p, hp, hx⟩ => ⟨p, (hnf.subA p hp).1, hx⟩
    A_pow := fun a ⟨p, hp, ha⟩ => eq_of_code (ha.pow 3) RepP.one (ho.pow3 p hp)
    A_comm := fun a ⟨p, hp, ha⟩ b ⟨q, hq, hb⟩ =>
      eq_of_code (ha.mul hb) (hb.mul ha) (ho.commA p hp q hq)
    card_A := (card_Ah hg hnf ho).trans (by norm_num)
    E_le_A := fun z hz => by
      obtain ⟨p, hp, hzp⟩ := hEcode z hz
      exact ⟨p, hnf.subE p hp, hzp⟩
    t1_mem := (mem_Th0 hg hnf).2 ⟨1, by norm_num, 0, by norm_num, by simp [nfElt]⟩
    t2_mem := (mem_Th0 hg hnf).2 ⟨0, by norm_num, 1, by norm_num, by simp [nfElt]⟩
    f_mem := gf_mem hg hnf
    order_t1 := order_t1 r
    order_t2 := order_t2 r
    comm_t := r.t12
    inf_t := inf_t_aux hg r hhm
    orbit := fun a ha haE W => orbit_aux hg hnf ho hc r hor a ha haE W
    lattice := fun U hEU hUT hinv => lattice_aux hg hnf ho hc r U hEU hUT hinv
    norm_T := fun b hb x hx => (norm_all hg hnf hc hN b hb).1 x hx
    norm_E := fun b hb x hx => (norm_all hg hnf hc hN b hb).2 x hx
    rank := fun F hF hFe => rank_aux hg hnf hc ho F hF hFe }

end CFSG.AGLEmbedding.KFactProofs.Sp48
