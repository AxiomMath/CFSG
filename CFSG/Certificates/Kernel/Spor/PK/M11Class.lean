module

public import CFSG.Certificates.Kernel.Spor.PK.ClsList
import Mathlib.Data.List.Nodup
import Batteries.Data.List.Perm

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.M11Class

private def mc_pq (f h : Nat → Nat) : Bool :=
  ordF 11 (fun i => f (h i)) == 11 &&
    ordF 11 (fun i => f (h (finv 11 f (finv 11 h i)))) == 6

private theorem mc_perm_congr {n : Nat} {f g : Nat → Nat} (hf : IsPermN n f)
    (h : ∀ x < n, f x = g x) : IsPermN n g :=
  ⟨fun x hx => by rw [← h x hx]; exact hf.1 x hx,
    fun x hx y hy e => hf.2 x hx y hy (by rw [h x hx, h y hy]; exact e)⟩

private theorem mc_finv_lt (f : Nat → Nat) (y : Nat) : finv 11 f y < 11 :=
  finv_lt (by decide) f y

private theorem mc_finv_eq {n : Nat} {g : Nat → Nat} (hg : IsPermN n g) {z y : Nat} (hz : z < n)
    (h : g z = y) : finv n g y = z := by
  rw [← h]
  exact finv_apply hg hz

private theorem mc_pq_congr {f f' h h' : Nat → Nat} (hf : IsPermN 11 f) (hh : IsPermN 11 h)
    (ef : ∀ i < 11, f i = f' i) (eh : ∀ i < 11, h i = h' i) : mc_pq f h = mc_pq f' h' := by
  have hh' := mc_perm_congr hh eh
  unfold mc_pq
  have e1 : ordF 11 (fun i => f (h i)) = ordF 11 (fun i => f' (h' i)) := by
    refine ordF_congr (fun i hi => hf.1 _ (hh.1 i hi)) (fun i hi => ?_)
    rw [eh i hi]
    exact ef _ (hh'.1 i hi)
  have e2 : ordF 11 (fun i => f (h (finv 11 f (finv 11 h i)))) =
      ordF 11 (fun i => f' (h' (finv 11 f' (finv 11 h' i)))) := by
    refine ordF_congr (fun i hi => hf.1 _ (hh.1 _ (mc_finv_lt _ _))) (fun i hi => ?_)
    rw [finv_congr eh i, finv_congr ef (finv 11 h' i)]
    have hv := mc_finv_lt f' (finv 11 h' i)
    rw [eh _ hv]
    exact ef _ (hh'.1 _ hv)
  rw [e1, e2]

private theorem mc_finv_conj {f a : Nat → Nat} (hf : IsPermN 11 f) (ha : IsPermN 11 a) {j : Nat}
    (hj : j < 11) :
    finv 11 (fun i => a (f (finv 11 a i))) j = a (finv 11 f (finv 11 a j)) := by
  have hf₁ : IsPermN 11 (fun i => a (f (finv 11 a i))) := ha.comp (hf.comp ha.finv)
  obtain ⟨h2, h3⟩ := finv_spec hf (mc_finv_lt a j)
  apply mc_finv_eq hf₁ (ha.1 _ h2)
  show a (f (finv 11 a (a (finv 11 f (finv 11 a j))))) = j
  rw [finv_apply ha h2, h3]
  exact (finv_spec ha hj).2

private theorem mc_pq_sim {f h a f₁ h₁ : Nat → Nat} (hf : IsPermN 11 f) (hh : IsPermN 11 h)
    (ha : IsPermN 11 a) (ef : ∀ i < 11, f₁ i = a (f (finv 11 a i)))
    (eh : ∀ i < 11, h₁ i = a (h (finv 11 a i))) : mc_pq f₁ h₁ = mc_pq f h := by
  have hh₁ : IsPermN 11 h₁ := mc_perm_congr (ha.comp (hh.comp ha.finv)) fun i hi => (eh i hi).symm
  have e1 : ordF 11 (fun i => f₁ (h₁ i)) = ordF 11 (fun i => f (h i)) := by
    have key : ∀ i < 11, f₁ (h₁ i) = a ((fun x => f (h x)) (finv 11 a i)) := by
      intro i hi
      rw [ef _ (hh₁.1 i hi), eh i hi, finv_apply ha (hh.1 _ (mc_finv_lt a i))]
    calc ordF 11 (fun i => f₁ (h₁ i))
        = ordF 11 (fun i => a ((fun x => f (h x)) (finv 11 a i))) :=
          ordF_congr (fun i hi => by
            rw [key i hi]
            exact ha.1 _ (hf.1 _ (hh.1 _ (mc_finv_lt a i)))) key
      _ = ordF 11 (fun i => f (h i)) := ordF_conj (fun x hx => hf.1 _ (hh.1 x hx)) ha
  have e2 : ordF 11 (fun i => f₁ (h₁ (finv 11 f₁ (finv 11 h₁ i)))) =
      ordF 11 (fun i => f (h (finv 11 f (finv 11 h i)))) := by
    have key : ∀ i < 11, f₁ (h₁ (finv 11 f₁ (finv 11 h₁ i))) =
        a ((fun x => f (h (finv 11 f (finv 11 h x)))) (finv 11 a i)) := by
      intro i hi
      have h1 : finv 11 h₁ i = a (finv 11 h (finv 11 a i)) := by
        rw [finv_congr eh i]
        exact mc_finv_conj hh ha hi
      have hu := mc_finv_lt h (finv 11 a i)
      have h2 : finv 11 f₁ (finv 11 h₁ i) = a (finv 11 f (finv 11 h (finv 11 a i))) := by
        rw [h1, finv_congr ef, mc_finv_conj hf ha (ha.1 _ hu), finv_apply ha hu]
      have hv := mc_finv_lt f (finv 11 h (finv 11 a i))
      have h3 : h₁ (finv 11 f₁ (finv 11 h₁ i)) = a (h (finv 11 f (finv 11 h (finv 11 a i)))) := by
        rw [h2, eh _ (ha.1 _ hv), finv_apply ha hv]
      have hw := hh.1 _ hv
      rw [h3, ef _ (ha.1 _ hw), finv_apply ha hw]
    calc ordF 11 (fun i => f₁ (h₁ (finv 11 f₁ (finv 11 h₁ i))))
        = ordF 11 (fun i => a ((fun x => f (h (finv 11 f (finv 11 h x)))) (finv 11 a i))) :=
          ordF_congr (fun i hi => by
            rw [key i hi]
            exact ha.1 _ (hf.1 _ (hh.1 _ (mc_finv_lt f _)))) key
      _ = ordF 11 (fun i => f (h (finv 11 f (finv 11 h i)))) :=
          ordF_conj (fun x hx => hf.1 _ (hh.1 _ (mc_finv_lt f _))) ha
  unfold mc_pq
  rw [e1, e2]

private theorem mc_blk_lt (T q : Nat) : blk T 44 (mask 44) q < 2 ^ 44 := by
  rw [blk_eq]
  exact fd_lt 44 T q

private theorem mc_fd_conj {g gi : Nat} (hg : invPair (pidn 11 4) g gi = true) (x : Nat) {i : Nat}
    (hi : i < 11) :
    fd 4 (conjK 11 4 15 g gi x) i = fd 4 g (fd 4 x (finv 11 (fd 4 g) i)) := by
  rw [conjK_eq, fd_enc (fun j _ => fd_lt _ _ _) hi, (invPair_perm hg).2 i hi]

private theorem mc_conj_perm {g gi x : Nat} (hg : invPair (pidn 11 4) g gi = true)
    (hx : IsPermN 11 (fd 4 x)) : IsPermN 11 (fd 4 (conjK 11 4 15 g gi x)) := by
  have ha := (invPair_perm hg).1
  exact mc_perm_congr (ha.comp (hx.comp ha.finv)) fun i hi => (mc_fd_conj hg x hi).symm

private theorem mc_conj_pq {g gi x y : Nat} (hg : invPair (pidn 11 4) g gi = true)
    (hx : IsPermN 11 (fd 4 x)) (hy : IsPermN 11 (fd 4 y)) :
    mc_pq (fd 4 (conjK 11 4 15 g gi x)) (fd 4 (conjK 11 4 15 g gi y)) =
      mc_pq (fd 4 x) (fd 4 y) :=
  mc_pq_sim hx hy (invPair_perm hg).1 (fun i hi => mc_fd_conj hg x hi)
    (fun i hi => mc_fd_conj hg y hi)

private theorem mc_conj_inj {g gi y y' : Nat} (hg : invPair (pidn 11 4) g gi = true)
    (hy : y < 2 ^ 44) (hy' : y' < 2 ^ 44) (hyp : IsPermN 11 (fd 4 y))
    (hyp' : IsPermN 11 (fd 4 y'))
    (h : conjK 11 4 15 g gi y = conjK 11 4 15 g gi y') : y = y' := by
  have hgp := (invPair_perm hg).1
  refine eq_of_fd_eq (w := 4) (len := 11) hy hy' (fun j hj => ?_)
  have h1 : ∀ i < 11, fd 4 g (fd 4 y (finv 11 (fd 4 g) i)) =
      fd 4 g (fd 4 y' (finv 11 (fd 4 g) i)) := fun i hi => by
    rw [← mc_fd_conj hg y hi, ← mc_fd_conj hg y' hi, h]
  have h2 := h1 (fd 4 g j) (hgp.1 j hj)
  rw [finv_apply hgp hj] at h2
  exact hgp.2 _ (hyp.1 j hj) _ (hyp'.1 j hj) h2

private theorem mc_perm_map {Y : List Nat} (hnd : Y.Nodup) {T : Nat → Nat}
    (hcl : ∀ y ∈ Y, T y ∈ Y) (hinj : ∀ y ∈ Y, ∀ y' ∈ Y, T y = T y' → y = y') :
    (Y.map T).Perm Y :=
  (List.subperm_of_subset (List.Nodup.map_on hinj hnd) (fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hcl y hy)).perm_of_length_le (by simp)

private theorem mc_count_conj {g gi : Nat} (hg : invPair (pidn 11 4) g gi = true) {Y : List Nat}
    (hnd : Y.Nodup) (hY : ∀ y ∈ Y, y < 2 ^ 44 ∧ IsPermN 11 (fd 4 y))
    (hcl : ∀ y ∈ Y, conjK 11 4 15 g gi y ∈ Y) {x : Nat} (hx : IsPermN 11 (fd 4 x)) :
    Y.countP (fun y => mc_pq (fd 4 (conjK 11 4 15 g gi x)) (fd 4 y)) =
      Y.countP (fun y => mc_pq (fd 4 x) (fd 4 y)) := by
  have hperm := mc_perm_map hnd hcl fun y hy y' hy' h =>
    mc_conj_inj hg (hY y hy).1 (hY y' hy').1 (hY y hy).2 (hY y' hy').2 h
  calc Y.countP (fun y => mc_pq (fd 4 (conjK 11 4 15 g gi x)) (fd 4 y))
      = (Y.map (conjK 11 4 15 g gi)).countP
          (fun y => mc_pq (fd 4 (conjK 11 4 15 g gi x)) (fd 4 y)) :=
        (hperm.countP_eq _).symm
    _ = Y.countP (fun y => mc_pq (fd 4 (conjK 11 4 15 g gi x)) (fd 4 (conjK 11 4 15 g gi y))) :=
        List.countP_map
    _ = Y.countP (fun y => mc_pq (fd 4 x) (fd 4 y)) := by
        refine List.countP_congr (fun y hy => ?_)
        rw [mc_conj_pq hg hx (hY y hy).2]

private theorem mc_rowCnt {x xi : Nat} (hx : invPair (pidn 11 4) x xi = true)
    {YL : List (Nat × Nat)} (hY : ∀ q ∈ YL, invPair (pidn 11 4) q.1 q.2 = true) :
    rowCnt x xi YL = (YL.map Prod.fst).countP (fun y => mc_pq (fd 4 x) (fd 4 y)) := by
  rw [rowCnt_eq, List.countP_map]
  refine List.countP_congr (fun q hq => ?_)
  rw [pairOK_eq hx (hY q hq)]
  exact Iff.rfl

theorem pairCntL_class' {A Ai B Bi R Ri cap : Nat} {Bl P Lb S SY : List Nat}
    {XL YL : List (Nat × Nat)} (h : classRowOK A Ai B Bi R Ri Bl P Lb S SY XL YL cap = true) :
    pairCntL XL YL = XL.length * rowCnt R Ri YL := by
  simp only [classRowOK, strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hcls, -, -, -, hR, hA, hB, hsX, hallX, hinc, -, hsY, hallY⟩ := h
  have hallY' := (allP_iff _ _).1 hallY
  simp only [Bool.and_eq_true] at hallY'
  have hXinv := (allP_iff _ _).1 hallX
  have hYinv : ∀ q ∈ YL, invPair (pidn 11 4) q.1 q.2 = true := fun q hq => (hallY' q hq).1
  have hYperm := sameSet_perm hsY
  have hYnd : (YL.map Prod.fst).Nodup := hYperm.nodup_iff.2 (nodup_of_increasing hinc)
  have hYc : ∀ y ∈ YL.map Prod.fst, y < 2 ^ 44 ∧ IsPermN 11 (fd 4 y) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    obtain ⟨p, -, hp⟩ := List.mem_map.1 (hYperm.mem_iff.1 hy)
    exact ⟨hp ▸ mc_blk_lt _ _, (invPair_perm (hYinv q hq)).1⟩
  have hYcl : ∀ {g gi : Nat}, (∀ q ∈ YL, bmem 44 17592186044415 (packL 44 SY) (lenN SY)
      (conjK 11 4 15 g gi q.1) = true) →
        ∀ y ∈ YL.map Prod.fst, conjK 11 4 15 g gi y ∈ YL.map Prod.fst := by
    intro g gi hb y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    obtain ⟨p, hp, hpe⟩ := bmem_sound (hb q hq)
    exact hYperm.mem_iff.2 (List.mem_map.2 ⟨p, List.mem_range.2 hp, hpe⟩)
  have hclA := hYcl fun q hq => (hallY' q hq).2.1
  have hclB := hYcl fun q hq => (hallY' q hq).2.2
  obtain ⟨-, hb0, -, htree, hbperm⟩ := clsOK_spec hcls
  have hcnt : ∀ k, k < lenN S → IsPermN 11 (fd 4 (blk (packL 44 Bl) 44 (mask 44) k)) ∧
      (YL.map Prod.fst).countP
          (fun y => mc_pq (fd 4 (blk (packL 44 Bl) 44 (mask 44) k)) (fd 4 y)) =
        (YL.map Prod.fst).countP (fun y => mc_pq (fd 4 R) (fd 4 y)) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [hb0]
        exact ⟨(invPair_perm hR).1, rfl⟩
      · obtain ⟨p, hp, hkp⟩ := htree k hk hpos
        obtain ⟨hpp, hpc⟩ := ih p hp (Nat.lt_trans hp hk)
        rcases hkp with hkp | hkp
        · rw [hkp]
          exact ⟨mc_conj_perm hA hpp, (mc_count_conj hA hYnd hYc hclA hpp).trans hpc⟩
        · rw [hkp]
          exact ⟨mc_conj_perm hB hpp, (mc_count_conj hB hYnd hYc hclB hpp).trans hpc⟩
  have hXperm := sameSet_perm hsX
  have hrow : ∀ q ∈ XL, rowCnt q.1 q.2 YL = rowCnt R Ri YL := by
    intro q hq
    have hq1 : q.1 ∈ (List.range (lenN S)).map (fun k => blk (packL 44 Bl) 44 (mask 44) k) :=
      hbperm.mem_iff.2 (hXperm.mem_iff.1 (List.mem_map.2 ⟨q, hq, rfl⟩))
    obtain ⟨k, hk, hkq⟩ := List.mem_map.1 hq1
    rw [mc_rowCnt (hXinv q hq) hYinv, mc_rowCnt hR hYinv, ← hkq]
    exact (hcnt k (List.mem_range.1 hk)).2
  rw [pairCntL_eq, List.map_congr_left hrow, List.map_const', List.sum_replicate_nat]

end CFSG.KS.PK

end
