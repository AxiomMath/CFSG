module

public import Certificates.Data.Kernel.Sp62F.Cosets
public import CFSG.Certificates.Kernel.Sp62W.Cosets
public import CFSG.Certificates.Kernel.Misc.Sp6WSound

public section

namespace CFSG.KC.Sp62F

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KD.Sp62F CFSG.KD.Sp62W CFSG.KGroups.Sp6
  CFSG.KC.Sp62W CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.H13

@[expose] noncomputable def keyH (x : H6) : ℕ := keyS (KGSp6.colsOf (mat6 x))

theorem keyH_eq {x : H6} {c : List ℕ} (h : Rep x c) : keyH x = keyS c := by
  rw [keyH, ((rep_cols x).eq_iff h).1 rfl]

theorem keyS_mul {A M : List ℕ} (hA : KGCert.ValidC A) (hM : KGCert.ValidC M)
    (hp : permS M = true) : keyS (mulC A M) = keyS A := by
  simp only [permS, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hp
  have hU : ∀ v, v ∈ planesS.map (mulVecC M) ↔ v ∈ planesS := by
    intro v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
      exact hp.1 u hu
    · exact hp.2 v
  change CFSG.KC.Sp6W.maskL _ = CFSG.KC.Sp6W.maskL _
  apply CFSG.KC.Sp6W.maskL_eq_of_iff
  intro i
  simp only [List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : mulVecC M u ∈ planesS := (hU _).1 (List.mem_map.2 ⟨u, hu, rfl⟩)
    exact ⟨_, this, (CFSG.KC.Sp6W.mulVecC_mulC hA hM u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨u', hu', he⟩ := List.mem_map.1 ((hU u).2 hu)
    exact ⟨u', hu', by rw [CFSG.KC.Sp6W.mulVecC_mulC hA hM, he]⟩

theorem keyH_mul_right (hp : gensN.all permS = true) (hi : gensN.all isoB = true) {m : H6}
    (hm : m ∈ Hgen gensN) (x : H6) : keyH (x * m) = keyH x := by
  rw [List.all_eq_true] at hp hi
  induction hm using Subgroup.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨c, hcg, rfl⟩ := hg
    have hr := (rep_cols x).mul (rep_elt (hi c hcg))
    rw [keyH_eq hr, keyH]
    exact keyS_mul (KGSp6.validC_colsOf _) (validC_of_isoB (hi c hcg)) (hp c hcg)
  | one => rw [mul_one]
  | mul a b _ _ ha hb => rw [← mul_assoc, hb, ha]
  | inv a _ ha => rw [← ha (x * a⁻¹), inv_mul_cancel_right]

theorem nodup_of_incKeys {f : ℕ × ℕ → ℕ} :
    ∀ {L : List (ℕ × ℕ)} {prev : ℕ}, incKeys f L prev = true →
      (L.map f).Nodup ∧ ∀ k ∈ L.map f, prev < k
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | p :: L, prev, h => by
    change (Nat.blt prev (f p) && incKeys f L (f p)) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hnd, hgt⟩ := nodup_of_incKeys h.2
    refine ⟨List.nodup_cons.2 ⟨fun hm => lt_irrefl _ (hgt _ hm), hnd⟩, ?_⟩
    intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact h.1
    · exact lt_trans h.1 (hgt k hk)

theorem double_cosets_N {E : ℕ → List ℕ} {L : List (ℕ × ℕ)}
    (hN : Nat.card (Hgen gensN) = 1296)
    (hE : ∀ i < 1296, isoB (E i) = true ∧ elt (E i) ∈ Hgen gensN)
    (hc : (L.length == 1120 && L.all (fun p => Nat.blt p.1 1296 && Nat.blt p.2 8) &&
      gensN.all permS && gensN.all isoB && dcReps.all isoB) = true)
    (hnd : (L.map fun p => keyS (mulC (E p.1) (dcReps.getD p.2 []))).Nodup) (x : H6) :
    ∃ r ∈ dcReps, ∃ a ∈ Hgen gensN, ∃ b ∈ Hgen gensN, x = a * elt r * b := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨hlen, hb⟩, hp⟩, hi⟩, hr⟩ := hc
  have hp' : gensN.all permS = true := List.all_eq_true.2 hp
  have hi' : gensN.all isoB = true := List.all_eq_true.2 hi
  have hrj : ∀ p ∈ L, dcReps.getD p.2 [] ∈ dcReps ∧ isoB (dcReps.getD p.2 []) = true := by
    intro p hpL
    have hj : p.2 < dcReps.length := by
      have := (hb p hpL).2
      simpa [dcReps, dcPairs] using this
    rw [List.getD_eq_getElem _ _ hj]
    exact ⟨List.getElem_mem hj, hr _ (List.getElem_mem hj)⟩
  let t : Fin 1120 → H6 := fun k =>
    elt (E (L[k.1]'(by rw [hlen]; exact k.2)).1) *
      elt (dcReps.getD (L[k.1]'(by rw [hlen]; exact k.2)).2 [])
  have hkey : ∀ k : Fin 1120, keyH (t k) =
      keyS (mulC (E (L[k.1]'(by rw [hlen]; exact k.2)).1)
        (dcReps.getD (L[k.1]'(by rw [hlen]; exact k.2)).2 [])) := by
    intro k
    have hpL := List.getElem_mem (l := L) (n := k.1) (by rw [hlen]; exact k.2)
    exact keyH_eq ((rep_elt (hE _ (hb _ hpL).1).1).mul (rep_elt (hrj _ hpL).2))
  let φ : Fin 1120 × Hgen gensN → H6 := fun p => t p.1 * p.2
  have hinj : Function.Injective φ := by
    rintro ⟨k, m⟩ ⟨k', m'⟩ h
    have hq := congrArg keyH h
    simp only [φ, keyH_mul_right hp' hi' m.2, keyH_mul_right hp' hi' m'.2, hkey] at hq
    have hk : k = k' := by
      have h1 := (List.Nodup.getElem_inj_iff hnd (i := k.1) (j := k'.1)
        (hi := by rw [List.length_map, hlen]; exact k.2)
        (hj := by rw [List.length_map, hlen]; exact k'.2)).1
      simp only [List.getElem_map] at h1
      exact Fin.ext (h1 hq)
    subst hk
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
  have hfin : Finite H6 := Nat.finite_of_card_ne_zero (by rw [card_H6]; norm_num)
  have hcard : Nat.card H6 ≤ Nat.card (Fin 1120 × Hgen gensN) := by
    rw [Nat.card_prod, hN, card_H6]
    simp
  obtain ⟨⟨k, m⟩, hx⟩ := (hinj.bijective_of_nat_card_le hcard).2 x
  have hpL := List.getElem_mem (l := L) (n := k.1) (by rw [hlen]; exact k.2)
  exact ⟨_, (hrj _ hpL).1, _, (hE _ (hb _ hpL).1).2, m, m.2, hx.symm⟩

theorem bf_mulVecC {x : H6} {c : List ℕ} (h : Rep x c) (u w : ℕ) :
    bf (mulVecC c u) (mulVecC c w) = bf u w := by
  apply KGCert.b2z_inj
  rw [KGSp6.b2z_bf, KGSp6.b2z_bf, KGSp6.mulVecC_eq, ← KGCert.decodeC_mulVec, ← KGCert.decodeC_mulVec, ← h.2,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, mat6_isIso x]

theorem centralizer_le_W (hW : Nat.card (Hgen gensWD) = 51840) (hc : dcCosetsCheck = true)
    (hz : czCheck2 = true) : Subgroup.centralizer ({elt cZ} : Set H6) ≤ Hgen gensWD := by
  intro x hx
  simp only [czCheck2, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hz
  obtain ⟨hq, hzi⟩ := hz
  have hrz := rep_elt hzi
  have hrx := rep_cols x
  set c := KGSp6.colsOf (mat6 x)
  have hcv : KGCert.ValidC c := KGSp6.validC_colsOf _
  have hzv : KGCert.ValidC cZ := validC_of_isoB hzi
  have hcomm : mulC c cZ = mulC cZ c :=
    (hrx.comm_iff hrz).1 (Subgroup.mem_centralizer_singleton_iff.1 hx)
  have hpres : ∀ y < 64, qv (mulVecC c y) = qv y := by
    intro y hy
    rw [hq (mulVecC c y) (KGCert.mulVecC_lt hcv y), hq y hy]
    have e : mulVecC cZ (mulVecC c y) = mulVecC c (mulVecC cZ y) := by
      rw [← CFSG.KC.Sp6W.mulVecC_mulC hzv hcv, ← hcomm, CFSG.KC.Sp6W.mulVecC_mulC hcv hzv]
    rw [e, bf_mulVecC hrx]
  have hq1 : qOf x = qOf 1 := by
    have h1 : Rep x (mulC c oneC) := by simpa using hrx.mul Rep.one
    rw [qOf_eq h1, qOf_eq Rep.one]
    exact qbits_map hpres KGCert.validC_oneC
  have hnd : ((List.range 28).map fun k => qbits (dcRep k)).Nodup := by
    simp only [dcCosetsCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.2
  let φ : Hgen gensWD × Fin 28 → H6 := fun p => p.1 * tE p.2
  have hinj : Function.Injective φ := by
    rintro ⟨w, k⟩ ⟨w', j⟩ h
    have hq' : qbits (dcRep k) = qbits (dcRep j) := by
      have := congrArg qOf h
      simp only [φ, qOf_mul_left hc w.2, qOf_mul_left hc w'.2] at this
      rwa [qOf_eq (rep_tE hc k.2).1, qOf_eq (rep_tE hc j.2).1] at this
    have hkj : k = j := Fin.ext (List.inj_on_of_nodup_map hnd (List.mem_range.2 k.2)
      (List.mem_range.2 j.2) hq')
    subst hkj
    exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
  have hfin : Finite H6 := Nat.finite_of_card_ne_zero (by rw [card_H6]; norm_num)
  have hcard : Nat.card H6 ≤ Nat.card (Hgen gensWD × Fin 28) := by
    rw [Nat.card_prod, hW, card_H6]
    simp
  obtain ⟨⟨w, k⟩, hxk⟩ := (hinj.bijective_of_nat_card_le hcard).2 x
  simp only [φ] at hxk
  have hk : (k : ℕ) = 0 := by
    have e1 : qOf x = qbits (dcRep k) := by
      rw [← hxk, qOf_mul_left hc w.2, qOf_eq (rep_tE hc k.2).1]
    have e0 : qOf 1 = qbits (dcRep 0) := by
      rw [qOf_eq Rep.one]
      rfl
    have := List.inj_on_of_nodup_map hnd (List.mem_range.2 k.2) (List.mem_range.2 (by norm_num))
      (e1.symm.trans (hq1.trans e0))
    exact this
  rw [← hxk, tE, if_pos hk, mul_one]
  exact w.2

end CFSG.KC.Sp62F

end
