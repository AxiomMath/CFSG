module

public import Certificates.Data.Kernel.LocalQT.RankF
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public import CFSG.Certificates.Kernel.LocalQTBaseWProved

public section

namespace CFSG.KC.LQT.RW.Pf

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.RW CFSG.KC.LQT.RF CFSG.KC.LQT.BW.Pf
open CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem nbeq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [P.beq_iff, beq_iff_eq])

theorem findW_go {f f' : Nat → Bool} : ∀ (m j : Nat), (∀ x, j ≤ x → x < j + m → f x = f' x) →
    Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) m j =
    ((List.range' j m).find? f').getD 0
  | 0, _, _ => rfl
  | m + 1, j, h => by
    change Bool.rec (motive := fun _ => Nat) (Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j)) j (f j)) m (j + 1)) j
        (f j) = _
    rw [List.range'_succ, List.find?_cons, h j (Nat.le_refl _) (by omega)]
    cases f' j
    · exact findW_go m (j + 1) fun x h1 h2 => h x (by omega) (by omega)
    · rfl

theorem findW_eq {g : Nat} {f f' : Nat → Bool} (h : ∀ j < g, f j = f' j) :
    findW g f = ((List.range g).find? f').getD 0 := by
  rw [findW, List.range_eq_range']
  exact findW_go g 0 fun x _ hx => h x (by omega)

theorem find_getD_lt {g : Nat} (hg : 0 < g) (f : Nat → Bool) :
    ((List.range g).find? f).getD 0 < g := by
  cases hf : (List.range g).find? f with
  | none => exact hg
  | some j => exact List.mem_range.1 (List.mem_of_find?_eq_some hf)

theorem filterN_go (f : Nat → Bool) : ∀ (m i : Nat),
    Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
      (fun _ ih i => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ i))
        (List.cons i (ih (Nat.succ i))) (f i)) m i = (List.range' i m).filter f
  | 0, _ => rfl
  | m + 1, i => by
    change Bool.rec (motive := fun _ => List Nat) _ _ (f i) = _
    rw [List.range'_succ, List.filter_cons]
    cases f i
    · exact filterN_go f m (i + 1)
    · exact congrArg (List.cons i) (filterN_go f m (i + 1))

theorem filterN_eq (N : Nat) (f : Nat → Bool) : filterN N f = (List.range N).filter f := by
  rw [filterN, List.range_eq_range']
  exact filterN_go f N 0

theorem allR_true {lo len : Nat} {f : Nat → Bool} (h : allR lo len f = true) :
    ∀ j < len, f (lo + j) = true := by
  induction len with
  | zero => intro j hj; omega
  | succ m ih =>
    have e : allR lo (m + 1) f = CFSG.KC.Ord.andB (f (Nat.add lo m)) (allR lo m f) := rfl
    rw [e, andB_eq, Bool.and_eq_true] at h
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h.2 j hj
    · exact h.1

theorem mem_slice {l : List Nat} {K L : Nat} (hl : l.length ≤ K * L) {c : Nat} (hc : c ∈ l) :
    ∃ j < K, c ∈ sliceK l (j * L) L := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hc
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hl
      omega
    · exact h
  have hpd : p / L < K := by
    rw [Nat.div_lt_iff_lt_mul hL]
    omega
  refine ⟨p / L, hpd, ?_⟩
  have hp' : p / L * L + p % L = p := by rw [Nat.mul_comm]; exact Nat.div_add_mod p L
  have hr : p % L < L := Nat.mod_lt _ hL
  rw [sliceK]
  have h1 : p % L < (List.take L (List.drop (p / L * L) l)).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have e : (List.take L (List.drop (p / L * L) l))[p % L] = l[p] := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
  rw [← e]
  exact List.getElem_mem _

@[expose] noncomputable def genG (fP fC : Nat → Nat) (g gg i : Nat) : Nat :=
  findW g fun j => Nat.beq (fC (Nat.add (Nat.mul (fP i) gg) j)) i

@[expose] noncomputable def mulG (fP fC : Nat → Nat) (g gg : Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ k => k)
    (fun _ ih i k => Bool.rec (motive := fun _ => Nat)
      (fC (Nat.add (Nat.mul (ih (fP i) k) gg) (genG fP fC g gg i))) k
      (Nat.beq i 0)) f

theorem mulIdxW_eq (W g gg PK CK f : Nat) :
    mulIdxW W g gg PK CK f = mulG (imgW W PK) (imgW W CK) g gg f := rfl

theorem mulG_spec {N g gi : Nat} {par cl : Array Nat} {fP fC : Nat → Nat}
    (hfP : ∀ i < N, fP i = par[i]!)
    (hfC : ∀ i < N, ∀ j < g, fC (i * (g + gi) + j) = cl[i * (g + gi) + j]!)
    (hpar : ∀ i < N, 0 < i → par[i]! < i ∧ 0 < g)
    (hcl : ∀ i < N, ∀ j < g, cl[i * (g + gi) + j]! < N) :
    ∀ f i k, i < N → k < N →
      mulG fP fC g (g + gi) f i k = mulIdx g gi par cl f i k ∧ mulIdx g gi par cl f i k < N := by
  intro f
  induction f with
  | zero => intro i k _ hk; exact ⟨rfl, hk⟩
  | succ f ih =>
    intro i k hi hk
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨rfl, by simp [mulIdx, hk]⟩
    · obtain ⟨hp, hg⟩ := hpar i hi (Nat.pos_of_ne_zero hi0)
      obtain ⟨e1, h1⟩ := ih par[i]! k (by omega) hk
      have hgen : genG fP fC g (g + gi) i = genIdx g gi par cl i := by
        rw [genG, genIdx, hfP i hi]
        apply findW_eq
        intro j hj
        rw [nbeq_eq]
        change (fC (par[i]! * (g + gi) + j) == i) = _
        rw [hfC _ (by omega) j hj]
      have hglt : genIdx g gi par cl i < g := by
        rw [genIdx]
        exact find_getD_lt hg _
      have e : mulG fP fC g (g + gi) (f + 1) i k =
          fC (mulG fP fC g (g + gi) f (fP i) k * (g + gi) + genG fP fC g (g + gi) i) := by
        change Bool.rec (motive := fun _ => Nat) _ k (Nat.beq i 0) = _
        rw [beq_false hi0]
        rfl
      have e2 : mulIdx g gi par cl (f + 1) i k =
          cl[mulIdx g gi par cl f par[i]! k * (g + gi) + genIdx g gi par cl i]! := by
        simp [mulIdx, hi0]
      rw [e, e2, hfP i hi, e1, hgen, hfC _ h1 _ hglt]
      exact ⟨rfl, hcl _ h1 _ hglt⟩

theorem hasW_eq (S : List Nat) (c : Nat) : hasW S c = S.contains c := by
  rw [hasW, anyL_eq]
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨x, hx, e⟩
    rw [P.beq_iff] at e
    rw [e]
    exact hx
  · intro h
    exact ⟨c, h, P.beq_iff.2 rfl⟩

theorem mapW_eq (f : Nat → Nat) : ∀ l : List Nat, mapW f l = l.map f
  | [] => rfl
  | x :: t => by
    change f x :: mapW f t = _
    rw [mapW_eq f t, List.map_cons]

theorem any_congr_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.any_cons, List.any_cons, h x (List.mem_cons_self ..),
      ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem all_congr_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.all_cons, List.all_cons, h x (List.mem_cons_self ..),
      ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem dfsW_eq (mul : Nat → Nat → Nat) (invs : List Nat) :
    ∀ (d : Nat) (L S : List Nat), dfsW mul invs d L S = dfs mul invs d L S
  | 0, _, _ => rfl
  | d + 1, L, S => by
    change anyL invs (fun c => CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (hasW S c))
      (allL L fun l => Nat.beq (mul c l) (mul l c))) (dfsW mul invs d (c :: L) (appK S (mapW (mul c) S)))) = _
    rw [anyL_eq, dfs]
    apply any_congr_mem
    intro c _
    rw [andB_eq, andB_eq, notB_eq, hasW_eq, allL_eq, appK_eq, mapW_eq, dfsW_eq mul invs d]
    congr 2

theorem dfs_congr {N : Nat} {mul mul' : Nat → Nat → Nat}
    (hm : ∀ a < N, ∀ b < N, mul a b = mul' a b ∧ mul a b < N) {invs : List Nat}
    (hinv : ∀ c ∈ invs, c < N) : ∀ (d : Nat) (L S : List Nat), (∀ l ∈ L, l < N) →
      (∀ s ∈ S, s < N) → dfs mul invs d L S = dfs mul' invs d L S
  | 0, _, _, _, _ => rfl
  | d + 1, L, S, hL, hS => by
    rw [dfs, dfs]
    apply any_congr_mem
    intro c hc
    have hcN := hinv c hc
    have hS' : ∀ s ∈ S ++ S.map (mul c), s < N := by
      intro s hs
      rw [List.mem_append, List.mem_map] at hs
      rcases hs with hs | ⟨x, hx, rfl⟩
      · exact hS s hs
      · exact (hm c hcN x (hS x hx)).2
    have hmap : S.map (mul c) = S.map (mul' c) :=
      List.map_congr_left fun x hx => (hm c hcN x (hS x hx)).1
    have hall : (L.all fun l => mul c l == mul l c) = (L.all fun l => mul' c l == mul' l c) :=
      all_congr_mem fun l hl => by
        rw [(hm c hcN l (hL l hl)).1, (hm l (hL l hl) c hcN).1]
    rw [hall, dfs_congr hm hinv d (c :: L) (S ++ S.map (mul c))
      (fun l hl => by
        rcases List.mem_cons.1 hl with rfl | hl
        · exact hcN
        · exact hL l hl) hS', hmap]

theorem rankCheck_of_parts {N g gi d zi K L : Nat} {par cl : Array Nat} {mul : Nat → Nat → Nat}
    (hmul : ∀ i < N, ∀ k < N, mul i k = mulIdx g gi par cl N i k ∧ mul i k < N)
    (hz : zi < N) (hz0 : zi ≠ 0) (hzz : mul zi zi = 0) (hc : ∀ i < N, mul zi i = mul i zi)
    (hcov : (filterN N fun i => CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq i 0)) (Nat.beq (mul i i) 0)).length ≤ K * L)
    (hp : ∀ j < K, allL (sliceK (filterN N fun i => CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq i 0)) (Nat.beq (mul i i) 0))
      (j * L) L) (branchF mul (filterN N fun i => CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq i 0))
        (Nat.beq (mul i i) 0)) zi d) = true) :
    rankCheck N g gi par cl (d + 1) = true := by
  generalize hI : (filterN N fun i => CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq i 0)) (Nat.beq (mul i i) 0)) = invs
    at hcov hp
  have hI' : invs = (List.range N).filter fun i => i != 0 && mulIdx g gi par cl N i i == 0 := by
    rw [← hI, filterN_eq]
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [andB_eq, notB_eq, nbeq_eq, nbeq_eq, (hmul i hi i hi).1]
    rfl
  have hinvN : ∀ c ∈ invs, c < N := by
    intro c hc
    rw [hI', List.mem_filter, List.mem_range] at hc
    exact hc.1
  unfold rankCheck
  dsimp only
  rw [← hI', List.any_eq_true]
  refine ⟨zi, ?_, ?_⟩
  · rw [List.mem_filter, hI', List.mem_filter, List.mem_range]
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · rw [← (hmul zi hz zi hz).1, hzz]
      simp [hz0]
    · rw [List.all_eq_true]
      intro i hi
      rw [List.mem_range] at hi
      rw [← (hmul zi hz i hi).1, ← (hmul i hi zi hz).1, hc i hi]
      simp
  · rw [Bool.not_eq_true', dfs, List.any_eq_false]
    intro c hcm
    obtain ⟨j, hj, hjs⟩ := mem_slice hcov hcm
    have hb := hp j hj
    rw [allL_eq, List.all_eq_true] at hb
    have hbc := hb c hjs
    have hcN := hinvN c hcm
    rw [branchF, notB_eq, Bool.not_eq_true', andB_eq, andB_eq, notB_eq, hasW_eq, nbeq_eq,
      appK_eq, mapW_eq, dfsW_eq] at hbc
    have hS : ∀ s ∈ [0, zi] ++ [0, zi].map (mul c), s < N := by
      intro s hs
      simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hs
      rcases hs with (h | h) | ⟨x, (h' | h'), h⟩
      · rw [h]
        omega
      · rw [h]
        exact hz
      · rw [← h, h']
        exact (hmul c hcN 0 (by omega)).2
      · rw [← h, h']
        exact (hmul c hcN zi hz).2
    rw [dfs_congr hmul hinvN d [c, zi] _ (fun l hl => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with h | h
      · rw [h]
        exact hcN
      · rw [h]
        exact hz) hS] at hbc
    have hmap : [0, zi].map (mul c) = [0, zi].map (mulIdx g gi par cl N c) :=
      List.map_congr_left fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h
        · rw [h]
          exact (hmul c hcN 0 (by omega)).1
        · rw [h]
          exact (hmul c hcN zi hz).1
    rw [hmap, (hmul c hcN zi hz).1, (hmul zi hz c hcN).1] at hbc
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    intro h
    rw [hbc] at h
    exact Bool.false_ne_true h

end CFSG.KC.LQT.RW.Pf

end
