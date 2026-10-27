module

public import Certificates.Data.Kernel.L5.EngScp
import CFSG.Certificates.Kernel.L5.Words
import Mathlib.Data.List.GetD

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

variable {n : Nat} [Group (Idx n)]

theorem orderOf_lt (a : Idx n) : orderOf a < n + 1 := by
  let _ : Fintype (Idx n) := Fintype.ofEquiv (Fin n) (Idx.equivFin n).symm
  have h1 := orderOf_le_card_univ (x := a)
  have h2 : Fintype.card (Idx n) = n := by
    rw [Fintype.card_congr (Idx.equivFin n), Fintype.card_fin]
  omega

theorem ordGo_eq (a : Idx n) (fuel : Nat) : ∀ k, 1 ≤ k → (∀ j, 1 ≤ j → j < k → a ^ j ≠ 1) →
    orderOf a < k + fuel → ordGo a fuel (a ^ k) k = orderOf a := by
  induction fuel with
  | zero =>
    intro k hk hmin hlt
    exact absurd (pow_orderOf_eq_one a) (hmin _ (orderOf_pos a) (by omega))
  | succ f ih =>
    intro k hk hmin hlt
    unfold ordGo
    split_ifs with h
    · exact ((orderOf_eq_iff (by omega)).2 ⟨h, fun m hm hm0 => hmin m hm0 hm⟩).symm
    · rw [← pow_succ]
      refine ih (k + 1) (by omega) (fun j hj1 hj => ?_) (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hmin j hj1 hj
      · exact h

theorem ordI_eq (a : Idx n) : ordI a = orderOf a := by
  unfold ordI
  have h := ordGo_eq a n 1 le_rfl (fun j hj1 hj => by omega) (by have := orderOf_lt a; omega)
  rwa [pow_one] at h

section Hom

variable {S : Subgroup (Idx n)} (φ : S →* Idx n) (hinj : Function.Injective φ)
include hinj

theorem isInv_map (u : S) : isInv (φ u) = isInv (u : Idx n) := by
  have key : ∀ v : S, φ v = 1 ↔ (v : Idx n) = 1 := fun v => by
    rw [map_eq_one_iff φ hinj, OneMemClass.coe_eq_one]
  have h1 : φ u * φ u = 1 ↔ (u : Idx n) * u = 1 := by
    rw [← map_mul, key, Subgroup.coe_mul]
  have h2 : φ u ≠ 1 ↔ (u : Idx n) ≠ 1 := by
    rw [ne_eq, ne_eq, key]
  unfold isInv
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, h1, h2]

variable {ci : Array Nat} {ld : List Nat}
  (hblk : ∀ u : S, isInv (u : Idx n) = true → blkOf ci ld (φ u) = blkOf ci ld (u : Idx n))
include hblk

theorem ivB_map (u : S) : ivB ci ld (φ u) = ivB ci ld (u : Idx n) := by
  unfold ivB
  rw [isInv_map φ hinj u]
  split_ifs with h
  · rw [hblk u h]
  · rfl

theorem tau_map {t tp : Idx n} (ht : t ∈ S) (hφt : φ ⟨t, ht⟩ = tp) (a : S) :
    tau ci ld tp (φ a) = tau ci ld t (a : Idx n) := by
  have ho : ∀ b : S, ordI (φ b) = ordI (b : Idx n) := fun b => by
    rw [ordI_eq, ordI_eq, orderOf_injective φ hinj, Subgroup.orderOf_coe]
  have hm : φ a * tp = φ (a * ⟨t, ht⟩) := by rw [map_mul, hφt]
  have hm' : (a : Idx n) * t = ((a * ⟨t, ht⟩ : S) : Idx n) := rfl
  unfold tau
  rw [hm, hm', ho, ho, ← map_pow, ← map_pow, ivB_map φ hinj hblk, ivB_map φ hinj hblk,
    Subgroup.coe_pow, Subgroup.coe_pow]

theorem count_le {t tp : Idx n} (ht : t ∈ S) (hφt : φ ⟨t, ht⟩ = tp)
    (hcent : ∀ a, φ a * tp = tp * φ a) (L : List (Idx n)) (hL : L.Nodup) (hLS : ∀ x ∈ L, x ∈ S)
    (τ₀ : Nat × Nat × Nat × Nat) : scpRefute ci ld t tp L τ₀ = false := by
  classical
  let A := L.filter fun a => decide (tau ci ld t a = τ₀)
  let B := (elemsI n).filter fun b => decide (b * tp = tp * b) && decide (tau ci ld tp b = τ₀)
  let ψ : Idx n → Idx n := fun x => if h : x ∈ S then φ ⟨x, h⟩ else 1
  have hA : A.Nodup := hL.filter _
  have hB : B.Nodup := (nodup_elemsI n).filter _
  have hle : A.toFinset.card ≤ B.toFinset.card := by
    refine Finset.card_le_card_of_injOn ψ ?_ ?_
    · intro x hx
      rw [List.coe_toFinset, Set.mem_setOf_eq, List.mem_filter] at hx
      have hxS := hLS x hx.1
      simp only [ψ, dif_pos hxS]
      rw [List.coe_toFinset, Set.mem_setOf_eq, List.mem_filter]
      refine ⟨mem_elemsI _, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hcent _, ?_⟩
      rw [tau_map φ hinj hblk ht hφt]
      exact of_decide_eq_true hx.2
    · intro x hx y hy hxy
      rw [List.coe_toFinset, Set.mem_setOf_eq, List.mem_filter] at hx hy
      have hxS := hLS x hx.1
      have hyS := hLS y hy.1
      simp only [ψ, dif_pos hxS, dif_pos hyS] at hxy
      exact congrArg Subtype.val (hinj hxy)
  rw [List.toFinset_card_of_nodup hA, List.toFinset_card_of_nodup hB] at hle
  unfold scpRefute
  exact decide_eq_false (Nat.not_lt.2 hle)

end Hom

theorem mem_greedyGens (S init : List (Idx n)) : ∀ x ∈ init, x ∈ greedyGens S init := by
  unfold greedyGens
  induction S generalizing init with
  | nil => exact fun x hx => hx
  | cons s S ih =>
    intro x hx
    rw [List.foldl_cons]
    refine ih _ x ?_
    split_ifs
    · exact hx
    · exact List.mem_append_left _ hx

theorem mem_mkHomCtx_gens (t : Idx n) : t ∈ (mkHomCtx t).gens :=
  mem_greedyGens _ [t] t (List.mem_singleton_self t)

private theorem ksL5_wordsGo_subset_initial (gs : List (Idx n)) :
    ∀ (fuel : Nat) (vis : Array Bool) (F A : List (Idx n × List Nat)),
      ∀ p ∈ A, p ∈ wordsGo gs fuel vis F A
  | 0, _, _, _ => fun _ h => h
  | _fuel + 1, _, [], _ => fun _ h => h
  | fuel + 1, _, _ :: _, A => fun p hp =>
      ksL5_wordsGo_subset_initial gs fuel _ _ (A ++ _) p (List.mem_append_left _ hp)

private theorem ksL5_one_mem_wordsOf (gs : List (Idx n)) :
    ((1, []) : Idx n × List Nat) ∈ wordsOf gs :=
  ksL5_wordsGo_subset_initial gs n _ _ [(1, [])] (1, []) (List.mem_singleton_self _)

private theorem ksL5_gens_length_pos (t : Idx n) : 0 < (mkHomCtx t).gens.length :=
  List.length_pos_of_mem (mem_mkHomCtx_gens t)

private def ksL5WordArr (gs : List (Idx n)) : Array (Option (List Nat)) :=
  (wordsOf gs).foldl (fun a ew => a.set! ew.1.v (some ew.2)) (Array.replicate n none)

private def ksL5WordOf (gs : List (Idx n)) (x : Idx n) : List Nat :=
  ((ksL5WordArr gs).getD x.v none).getD []

private theorem ksL5_size_set (a : Array (Option (List Nat))) (i : Nat)
    (w : Option (List Nat)) : (a.set! i w).size = a.size := by
  simp [Array.set!]

private theorem ksL5_getD_set_some (a : Array (Option (List Nat))) (i j : Nat)
    (hi : i < a.size) (w : List Nat) :
    (a.set! i (some w)).getD j none = if i = j then some w else a.getD j none := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split <;> simp_all

omit [Group (Idx n)] in
private theorem ksL5_foldl_set_getD_of_not_mem (L : List (Idx n × List Nat))
    (a : Array (Option (List Nat))) (x : Idx n) (hx : x.v < a.size)
    (h : ∀ p ∈ L, p.1 ≠ x) :
    (L.foldl (fun a p => a.set! p.1.v (some p.2)) a).getD x.v none = a.getD x.v none := by
  induction L generalizing a with
  | nil => rfl
  | cons p L ih =>
    rw [List.foldl_cons]
    have hne : p.1.v ≠ x.v := fun hv => h p (by simp) (Idx.ext hv)
    by_cases hlt : p.1.v < a.size
    · have hsize : x.v < (a.set! p.1.v (some p.2)).size := by
        rw [ksL5_size_set]; exact hx
      rw [ih (a.set! p.1.v (some p.2)) hsize (fun q hq => h q (by simp [hq])),
        ksL5_getD_set_some _ _ _ hlt, if_neg hne]
    · have hset : a.set! p.1.v (some p.2) = a := by
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        simp [hlt]
      rw [hset]
      exact ih a hx (fun q hq => h q (by simp [hq]))

omit [Group (Idx n)] in
private theorem ksL5_foldl_set_exists (L : List (Idx n × List Nat))
    (a : Array (Option (List Nat))) (x : Idx n) (hx : x.v < a.size)
    (h : ∃ p ∈ L, p.1 = x) :
    ∃ w, (L.foldl (fun a p => a.set! p.1.v (some p.2)) a).getD x.v none = some w ∧
      ∃ p ∈ L, p.1 = x ∧ p.2 = w := by
  induction L generalizing a with
  | nil => obtain ⟨p, hp, _⟩ := h; exact absurd hp List.not_mem_nil
  | cons p L ih =>
    rw [List.foldl_cons]
    by_cases hpx : p.1 = x
    · rw [hpx]
      let a' : Array (Option (List Nat)) := a.set! x.v (some p.2)
      have ha' : x.v < a'.size := by rw [ksL5_size_set]; exact hx
      by_cases hL : ∃ q ∈ L, q.1 = x
      · obtain ⟨w, hw, q, hq, hqx, hqw⟩ := ih a' ha' hL
        dsimp only [a'] at hw ⊢
        exact ⟨w, hw, q, by simp [hq], hqx, hqw⟩
      · have hnot : ∀ q ∈ L, q.1 ≠ x := fun q hq hqx => hL ⟨q, hq, hqx⟩
        have hget : a'.getD x.v none = some p.2 := by
          rw [ksL5_getD_set_some _ _ _ hx, if_pos rfl]
        have hpres := ksL5_foldl_set_getD_of_not_mem L a' x ha' hnot
        dsimp only [a'] at hget hpres ⊢
        refine ⟨p.2, ?_, p, by simp, hpx, rfl⟩
        rw [hpres, hget]
    · have hL : ∃ q ∈ L, q.1 = x := by
        obtain ⟨r, hr, hrx⟩ := h
        rcases List.mem_cons.1 hr with rfl | hr
        · exact absurd hrx hpx
        · exact ⟨r, hr, hrx⟩
      have ha' : x.v < (a.set! p.1.v (some p.2)).size := by
        rw [ksL5_size_set]; exact hx
      obtain ⟨w, hw, q, hq, hqx, hqw⟩ := ih (a.set! p.1.v (some p.2)) ha' hL
      exact ⟨w, hw, q, by simp [hq], hqx, hqw⟩

private theorem ksL5_wordOf_spec (gs : List (Idx n)) (x : Idx n)
    (hx : x ∈ Subgroup.closure {g | g ∈ gs}) :
    (ksL5WordArr gs).getD x.v none = some (ksL5WordOf gs x) ∧
      ((x, ksL5WordOf gs x) : Idx n × List Nat) ∈ wordsOf gs ∧
      evW gs (ksL5WordOf gs x) = x := by
  have hmem : x ∈ (wordsOf gs).map Prod.fst := (mem_wordsOf_iff gs x).mpr hx
  obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hmem
  have hxlt : x.v < (Array.replicate n none : Array (Option (List Nat))).size := by
    simpa using x.v_lt
  obtain ⟨w, hw, q, hq, hqx, hqw⟩ :=
    ksL5_foldl_set_exists (wordsOf gs) (Array.replicate n none) x hxlt ⟨p, hp, hpx⟩
  have hword : ksL5WordOf gs x = w := by
    unfold ksL5WordOf
    rw [show ksL5WordArr gs = (wordsOf gs).foldl
      (fun a ew => a.set! ew.1.v (some ew.2)) (Array.replicate n none) from rfl, hw]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [show ksL5WordArr gs = (wordsOf gs).foldl
      (fun a ew => a.set! ew.1.v (some ew.2)) (Array.replicate n none) from rfl, hw, hword]
  · rw [hword]
    exact (@Prod.ext (Idx n) (List Nat) (x, w) q hqx.symm hqw.symm) ▸ hq
  · rw [hword]
    have := evW_wordsOf gs q hq
    rwa [hqx, hqw] at this

private theorem ksL5_mem_relsOf {gs : List (Idx n)}
    {ew : Idx n × List Nat} {i : Nat} {w' : List Nat}
    (hew : ew ∈ wordsOf gs) (hi : i < gs.length)
    (hw' : (ksL5WordArr gs).getD (ew.1 * gs.getD i 1).v none = some w')
    (hne : w' ≠ ew.2 ++ [i]) :
    (ew.2 ++ [i], w') ∈ relsOf gs (wordsOf gs) := by
  dsimp only [relsOf]
  refine List.mem_flatMap.mpr ⟨ew, hew, ?_⟩
  refine List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  change (match (ksL5WordArr gs).getD (ew.1 * gs.getD i 1).v none with
    | some w' => if decide (w' = ew.2 ++ [i]) = true then none else some (ew.2 ++ [i], w')
    | none => none) = some (ew.2 ++ [i], w')
  rw [hw']
  simp [hne]

private theorem ksL5_relsOf_step {gs : List (Idx n)} {cs : List (Idx n)}
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    {ew : Idx n × List Nat} (hew : ew ∈ wordsOf gs) {i : Nat} (hi : i < gs.length)
    {w' : List Nat} (hw' : (ksL5WordArr gs).getD (ew.1 * gs.getD i 1).v none = some w') :
    evW cs (ew.2 ++ [i]) = evW cs w' := by
  by_cases h : w' = ew.2 ++ [i]
  · rw [h]
  · exact hrel _ (ksL5_mem_relsOf hew hi hw' h)

private theorem ksL5_homGo_spec {ctx : HomCtx n} {ci : Array Nat} {ld : List Nat}
    {cands : List (Idx n)} :
    ∀ (d j : Nat) (cs : List (Idx n)), homGo ctx ci ld cands d j cs = true →
      ∃ extra : List (Idx n), (∀ c ∈ extra, c ∈ cands) ∧ extra.length = d ∧
        candOK ctx ci ld (j + d) (cs ++ extra)
  | 0, j, cs, h => by
    change candOK ctx ci ld j cs = true at h
    simpa using h
  | d + 1, j, cs, h => by
    simp only [homGo, Bool.and_eq_true] at h
    obtain ⟨-, hany⟩ := h
    obtain ⟨c, hc, hgo⟩ := List.any_eq_true.mp hany
    obtain ⟨extra, hextra, hlen, hcandok⟩ := ksL5_homGo_spec d (j + 1) (cs ++ [c]) hgo
    refine ⟨c :: extra, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hc
      · exact hextra x hx
    · simp [hlen]
    · rw [show cs ++ (c :: extra) = (cs ++ [c]) ++ extra by simp [List.append_assoc],
        show j + (d + 1) = j + 1 + d by omega]
      exact hcandok

private def ksL5F (gs : List (Idx n)) (cs : List (Idx n)) (x : Idx n) : Idx n :=
  evW cs (ksL5WordOf gs x)

private theorem ksL5_greedyGens_head (S : List (Idx n)) (t : Idx n) :
    ∀ (init : List (Idx n)), init.head? = some t → (greedyGens S init).head? = some t := by
  induction S with
  | nil => intro init h; simpa [greedyGens] using h
  | cons s S ih =>
    intro init h
    rw [greedyGens, List.foldl_cons]
    split_ifs with hc
    · exact ih init h
    · apply ih
      simp [List.head?_append, h]

private theorem ksL5_gens_head (t : Idx n) :
    (mkHomCtx t).gens[0]'(ksL5_gens_length_pos t) = t := by
  have hhead : (mkHomCtx t).gens.head? = some t := by
    unfold mkHomCtx
    exact ksL5_greedyGens_head _ t [t] (by simp)
  obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hhead
  have h0? : (mkHomCtx t).gens[0]? = some t := by rw [htail]; rfl
  obtain ⟨hlt, h0⟩ := List.getElem?_eq_some_iff.mp h0?
  simpa using h0

private theorem ksL5_evW_singleton (cs : List (Idx n)) {i : Nat} (hi : i < cs.length) :
    evW cs [i] = cs[i] := by
  unfold evW
  simp only [List.foldl_cons, List.foldl_nil, one_mul,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem ksL5_f_gen_eq_cs {gs : List (Idx n)} {cs : List (Idx n)}
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    (hcslen : cs.length = gs.length) {i : Nat} (hi : i < gs.length) :
    ksL5F gs cs (gs[i]) = cs[i] := by
  have hgen : gs[i] ∈ Subgroup.closure {g | g ∈ gs} :=
    Subgroup.subset_closure (List.getElem_mem hi)
  obtain ⟨hwa, -, -⟩ := ksL5_wordOf_spec gs (gs[i]) hgen
  have hgi : gs.getD i 1 = gs[i] := List.getD_eq_getElem gs 1 hi
  have hwa' : (ksL5WordArr gs).getD ((1 * gs.getD i 1)).v none =
      some (ksL5WordOf gs (gs[i])) := by
    rw [show (1 * gs.getD i 1).v = (gs[i]).v by rw [one_mul, hgi]]
    exact hwa
  have hstep := ksL5_relsOf_step hrel (ksL5_one_mem_wordsOf gs) hi hwa'
  have hcsi : cs.getD i 1 = cs[i] := by
    rw [List.getD_eq_getElem?_getD]
    have hi' : i < cs.length := by omega
    rw [List.getElem?_eq_getElem hi']
    rfl
  calc ksL5F gs cs (gs[i]) = evW cs (ksL5WordOf gs (gs[i])) := rfl
    _ = evW cs ([] ++ [i]) := hstep.symm
    _ = cs[i] := by simpa using ksL5_evW_singleton cs (by omega)

private theorem ksL5_f_one {gs : List (Idx n)} {cs : List (Idx n)} {tp : Idx n}
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    (hcslen : cs.length = gs.length) (hcs0 : cs.getD 0 1 = tp)
    (hgpos : 0 < gs.length) :
    ksL5F gs cs 1 = 1 := by
  obtain ⟨-, hmem1, -⟩ := ksL5_wordOf_spec gs 1 (Subgroup.one_mem _)
  have hg0 : gs.getD 0 1 = gs[0] := List.getD_eq_getElem gs 1 hgpos
  obtain ⟨hwa0, -, -⟩ :=
    ksL5_wordOf_spec gs (gs[0]) (Subgroup.subset_closure (List.getElem_mem hgpos))
  have hwa1 : (ksL5WordArr gs).getD ((1 * gs.getD 0 1)).v none =
      some (ksL5WordOf gs (gs[0])) := by
    rw [show (1 * gs.getD 0 1).v = (gs[0]).v by rw [one_mul, hg0]]
    exact hwa0
  have hstep := ksL5_relsOf_step hrel hmem1 hgpos hwa1
  have hgen0 := ksL5_f_gen_eq_cs hrel hcslen hgpos
  have hcsi0 : cs.getD 0 1 = cs[0] := List.getD_eq_getElem cs 1 (by omega)
  have hleft : evW cs (ksL5WordOf gs 1 ++ [0]) = ksL5F gs cs 1 * cs.getD 0 1 := by
    rw [evW_append_single]
    rfl
  have hright : evW cs (ksL5WordOf gs (gs[0])) = cs.getD 0 1 := by
    have h := hgen0
    unfold ksL5F at h
    rw [h, hcsi0]
  have hmul : ksL5F gs cs 1 * tp = tp := by
    rw [← hcs0, ← hleft, hstep, hright]
  exact mul_right_cancel (by rw [hmul, one_mul])

private theorem ksL5_f_mul_gen {gs : List (Idx n)} {cs : List (Idx n)}
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    (hcslen : cs.length = gs.length) {x : Idx n}
    (hx : x ∈ Subgroup.closure {g | g ∈ gs}) {i : Nat} (hi : i < gs.length) :
    ksL5F gs cs (x * gs[i]) = ksL5F gs cs x * cs[i] := by
  obtain ⟨-, hmx, -⟩ := ksL5_wordOf_spec gs x hx
  have hxgi : x * gs[i] ∈ Subgroup.closure {g | g ∈ gs} :=
    mul_mem hx (Subgroup.subset_closure (List.getElem_mem hi))
  obtain ⟨hwgi, -, -⟩ := ksL5_wordOf_spec gs (x * gs[i]) hxgi
  have hgi : gs.getD i 1 = gs[i] := List.getD_eq_getElem gs 1 hi
  have hw' : (ksL5WordArr gs).getD (x * gs.getD i 1).v none =
      some (ksL5WordOf gs (x * gs[i])) := by
    rw [show x * gs.getD i 1 = x * gs[i] by rw [hgi]]
    exact hwgi
  have hstep := ksL5_relsOf_step hrel hmx hi hw'
  have hcsi : cs.getD i 1 = cs[i] := List.getD_eq_getElem cs 1 (by omega)
  unfold ksL5F
  rw [← hstep, evW_append_single, hcsi]

private theorem ksL5_f_mul_product {gs : List (Idx n)} {cs : List (Idx n)}
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    (hcslen : cs.length = gs.length)
    (x : Idx n) (hx : x ∈ Subgroup.closure {g | g ∈ gs}) (w : List Nat) :
    ksL5F gs cs (x * evW gs w) = ksL5F gs cs x * evW cs w := by
  induction w using List.reverseRecOn with
  | nil => simp [evW]
  | append_singleton w i ih =>
    rw [evW_append_single, evW_append_single, ← mul_assoc]
    by_cases hi : i < gs.length
    · have hgi : gs.getD i 1 = gs[i] := List.getD_eq_getElem gs 1 hi
      have hcsi : cs.getD i 1 = cs[i] := List.getD_eq_getElem cs 1 (by omega)
      rw [hgi, hcsi,
        ksL5_f_mul_gen hrel hcslen (mul_mem hx (evW_mem_closure gs w)) hi, ih,
        mul_assoc]
    · have hgi : gs.getD i 1 = 1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      have hcsi : cs.getD i 1 = 1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      rw [hgi, hcsi, mul_one, mul_one]
      exact ih

private theorem ksL5_f_mul {gs : List (Idx n)} {cs : List (Idx n)}
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    (hcslen : cs.length = gs.length) (hf1 : ksL5F gs cs 1 = 1)
    (u v : Idx n) (hu : u ∈ Subgroup.closure {g | g ∈ gs})
    (hv : v ∈ Subgroup.closure {g | g ∈ gs}) :
    ksL5F gs cs (u * v) = ksL5F gs cs u * ksL5F gs cs v := by
  have hmem : v ∈ (wordsOf gs).map Prod.fst := (mem_wordsOf_iff gs v).mpr hv
  obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hmem
  have hpv' : evW gs p.2 = v := by rw [evW_wordsOf gs p hp, hpv]
  have hprod := ksL5_f_mul_product hrel hcslen u hu p.2
  rw [hpv'] at hprod
  have hf : ksL5F gs cs v = evW cs p.2 := by
    have h1 := ksL5_f_mul_product hrel hcslen 1 (Subgroup.one_mem _) p.2
    simp only [one_mul, hpv', hf1] at h1
    exact h1
  rw [hprod, hf]

private theorem ksL5_evW_central {cs : List (Idx n)} {tp : Idx n}
    (hcs : ∀ c ∈ cs, c * tp = tp * c) (w : List Nat) :
    evW cs w * tp = tp * evW cs w := by
  induction w using List.reverseRecOn with
  | nil => simp [evW]
  | append_singleton w i ih =>
    rw [evW_append_single]
    have hc : cs.getD i 1 * tp = tp * cs.getD i 1 := by
      rw [List.getD_eq_getElem?_getD]
      cases h : cs[i]? with
      | none => simp
      | some c => simpa [h] using hcs c (List.mem_of_getElem? h)
    calc (evW cs w * cs.getD i 1) * tp = evW cs w * (cs.getD i 1 * tp) := by group
      _ = evW cs w * (tp * cs.getD i 1) := by rw [hc]
      _ = (evW cs w * tp) * cs.getD i 1 := by group
      _ = (tp * evW cs w) * cs.getD i 1 := by rw [ih]
      _ = tp * (evW cs w * cs.getD i 1) := by group

private theorem ksL5_candOK_R {ctx : HomCtx n} {ci : Array Nat} {ld : List Nat} {j : Nat}
    {cs : List (Idx n)} (h : candOK ctx ci ld j cs = true) :
    ∀ r ∈ ctx.R.getD (j - 1) [], evW cs r.1 = evW cs r.2 := by
  unfold candOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem ksL5_candOK_W {ctx : HomCtx n} {ci : Array Nat} {ld : List Nat} {j : Nat}
    {cs : List (Idx n)} (h : candOK ctx ci ld j cs = true) :
    ∀ w ∈ ctx.W.getD (j - 1) [],
      (evW cs w = 1 → evW (ctx.gens.take j) w = 1) ∧
      (isInv (evW (ctx.gens.take j) w) = true →
        isInv (evW cs w) = true ∧
          blkOf ci ld (evW cs w) = blkOf ci ld (evW (ctx.gens.take j) w)) := by
  unfold candOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  intro w hw
  have h1 := h.2 w hw
  refine ⟨?_, ?_⟩
  · intro himg
    rcases h1.1.1 with hdom | hne
    · exact hdom
    · exact absurd himg hne
  · intro hinv
    rcases h1.1.2 with h | h
    · rw [hinv, Bool.not_true] at h
      exact absurd h (by simp)
    · exact h

private theorem ksL5_ctx_R_getD (t : Idx n) :
    (mkHomCtx t).R.getD ((mkHomCtx t).gens.length - 1) [] =
      relsOf (mkHomCtx t).gens (wordsOf (mkHomCtx t).gens) := by
  let gens := greedyGens ((elemsI n).filter fun s => decide (s * t = t * s)) [t]
  have hgens : (mkHomCtx t).gens = gens := rfl
  have hR : (mkHomCtx t).R = (List.range gens.length).map
      (fun j => relsOf (gens.take (j + 1)) (wordsOf (gens.take (j + 1)))) := rfl
  have hpos : 0 < gens.length := by rw [← hgens]; exact ksL5_gens_length_pos t
  have hlt : gens.length - 1 < (List.range gens.length).length := by
    simp only [List.length_range]; omega
  have hg1 : gens.length - 1 + 1 = gens.length := by omega
  rw [hR, hgens]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some, List.getElem_range, hg1, List.take_length]

private theorem ksL5_ctx_W_getD (t : Idx n) :
    (mkHomCtx t).W.getD ((mkHomCtx t).gens.length - 1) [] =
      (wordsOf (mkHomCtx t).gens).map Prod.snd := by
  let gens := greedyGens ((elemsI n).filter fun s => decide (s * t = t * s)) [t]
  have hgens : (mkHomCtx t).gens = gens := rfl
  have hW : (mkHomCtx t).W = (List.range gens.length).map
      (fun j => (wordsOf (gens.take (j + 1))).map Prod.snd) := rfl
  have hpos : 0 < gens.length := by rw [← hgens]; exact ksL5_gens_length_pos t
  have hlt : gens.length - 1 < (List.range gens.length).length := by
    simp only [List.length_range]; omega
  have hg1 : gens.length - 1 + 1 = gens.length := by omega
  rw [hW, hgens]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    Option.map_some, Option.getD_some, List.getElem_range, hg1, List.take_length]

private theorem ksL5_homExists_data {t tp : Idx n} {ci : Array Nat} {ld : List Nat}
    (h : homExists (mkHomCtx t) ci ld tp = true) :
    ∃ cs : List (Idx n),
      cs.length = (mkHomCtx t).gens.length ∧
      cs.getD 0 1 = tp ∧
      (∀ c ∈ cs, c * tp = tp * c) ∧
      (∀ r ∈ relsOf (mkHomCtx t).gens (wordsOf (mkHomCtx t).gens),
        evW cs r.1 = evW cs r.2) ∧
      (∀ w ∈ (wordsOf (mkHomCtx t).gens).map Prod.snd,
        (evW cs w = 1 → evW (mkHomCtx t).gens w = 1) ∧
        (isInv (evW (mkHomCtx t).gens w) = true → isInv (evW cs w) = true ∧
          blkOf ci ld (evW cs w) = blkOf ci ld (evW (mkHomCtx t).gens w))) := by
  let gs := (mkHomCtx t).gens
  let ctx := mkHomCtx t
  unfold homExists at h
  obtain ⟨extra, hextra_mem, hextra_len, hcand'⟩ :=
    ksL5_homGo_spec (ctx := ctx) (ci := ci) (ld := ld)
      (cands := (elemsI n).filter fun c => decide (c * tp = tp * c))
      (gs.length - 1) 1 [tp] h
  let cs := [tp] ++ extra
  have hgpos : 0 < gs.length := ksL5_gens_length_pos t
  have hcs_len : cs.length = gs.length := by
    simp only [cs, List.length_append, List.length_singleton, hextra_len]; omega
  have hcand : candOK ctx ci ld gs.length cs := by
    have hj : 1 + (gs.length - 1) = gs.length := by omega
    simpa [cs, hj] using hcand'
  have hcs0 : cs.getD 0 1 = tp := by simp [cs]
  have hcs_cent : ∀ c ∈ cs, c * tp = tp * c := by
    intro c hc
    simp only [cs, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | hc
    · rfl
    · have hc' := List.mem_filter.mp (hextra_mem c hc)
      simpa only [decide_eq_true_eq] using hc'.2
  have hRdef : ctx.R.getD (gs.length - 1) [] = relsOf gs (wordsOf gs) := ksL5_ctx_R_getD t
  have hWdef : ctx.W.getD (gs.length - 1) [] = (wordsOf gs).map Prod.snd :=
    ksL5_ctx_W_getD t
  have hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2 := by
    intro r hr
    rw [← hRdef] at hr
    exact ksL5_candOK_R hcand r hr
  have hW := ksL5_candOK_W hcand
  have hW' : ∀ w ∈ (wordsOf gs).map Prod.snd,
      (evW cs w = 1 → evW gs w = 1) ∧
      (isInv (evW gs w) = true → isInv (evW cs w) = true ∧
        blkOf ci ld (evW cs w) = blkOf ci ld (evW gs w)) := by
    intro w hw
    have h1 := hW w (by rw [hWdef]; exact hw)
    rwa [List.take_length] at h1
  exact ⟨cs, hcs_len, hcs0, hcs_cent, hrel, hW'⟩

private theorem ksL5_phi_inj {gs : List (Idx n)} {cs : List (Idx n)} {ci : Array Nat}
    {ld : List Nat}
    (hW : ∀ w ∈ (wordsOf gs).map Prod.snd,
      (evW cs w = 1 → evW gs w = 1) ∧
      (isInv (evW gs w) = true → isInv (evW cs w) = true ∧
        blkOf ci ld (evW cs w) = blkOf ci ld (evW gs w))) :
    ∀ (φ : Subgroup.closure {g | g ∈ gs} →* Idx n),
      (∀ u : Subgroup.closure {g | g ∈ gs}, φ u = ksL5F gs cs (u : Idx n)) →
      Function.Injective φ := by
  intro φ hφ
  have hker : ∀ u : Subgroup.closure {g | g ∈ gs}, φ u = 1 → u = 1 := by
    intro u hu
    have hu' : ksL5F gs cs (u : Idx n) = 1 := by rw [← hφ u]; exact hu
    obtain ⟨-, hmem, hev⟩ := ksL5_wordOf_spec gs (u : Idx n) u.2
    have hwW : ksL5WordOf gs (u : Idx n) ∈ (wordsOf gs).map Prod.snd :=
      List.mem_map.mpr ⟨(u, ksL5WordOf gs (u : Idx n)), hmem, rfl⟩
    have himg : evW cs (ksL5WordOf gs (u : Idx n)) = 1 := by
      simpa [ksL5F] using hu'
    have hdom : evW gs (ksL5WordOf gs (u : Idx n)) = 1 := (hW _ hwW).1 himg
    have : (u : Idx n) = 1 := by rw [← hev, hdom]
    exact Subtype.ext this
  intro u v huv
  have h : φ (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
  have h2 : u * v⁻¹ = 1 := hker _ h
  calc u = u * v⁻¹ * v := by group
    _ = 1 * v := by rw [h2]
    _ = v := one_mul v

private theorem ksL5_mk_phi {t tp : Idx n} {ci : Array Nat} {ld : List Nat}
    {gs : List (Idx n)} {cs : List (Idx n)}
    (hcs_len : cs.length = gs.length) (hcs0 : cs.getD 0 1 = tp)
    (hcs_cent : ∀ c ∈ cs, c * tp = tp * c)
    (hrel : ∀ r ∈ relsOf gs (wordsOf gs), evW cs r.1 = evW cs r.2)
    (hW : ∀ w ∈ (wordsOf gs).map Prod.snd,
      (evW cs w = 1 → evW gs w = 1) ∧
      (isInv (evW gs w) = true → isInv (evW cs w) = true ∧
        blkOf ci ld (evW cs w) = blkOf ci ld (evW gs w)))
    (hgpos : 0 < gs.length) (hhead : gs[0]'(hgpos) = t)
    (ht : t ∈ gs) :
    ∃ φ : Subgroup.closure {g | g ∈ gs} →* Idx n,
      (∀ u : Subgroup.closure {g | g ∈ gs}, φ u = ksL5F gs cs (u : Idx n)) ∧
      φ ⟨t, Subgroup.subset_closure ht⟩ = tp ∧
      (∀ a, φ a * tp = tp * φ a) ∧
      ∀ u : Subgroup.closure {g | g ∈ gs}, isInv (u : Idx n) = true →
        blkOf ci ld (φ u) = blkOf ci ld (u : Idx n) := by
  let S := Subgroup.closure {g | g ∈ gs}
  have hf1 : ksL5F gs cs 1 = 1 := ksL5_f_one hrel hcs_len hcs0 hgpos
  have hmul : ∀ u v : S, ksL5F gs cs ((u : Idx n) * v) = ksL5F gs cs u * ksL5F gs cs v :=
    fun u v => ksL5_f_mul hrel hcs_len hf1 (u : Idx n) (v : Idx n) u.2 v.2
  let φ : S →* Idx n := MonoidHom.mk' (fun u : S => ksL5F gs cs (u : Idx n))
    (fun u v => hmul u v)
  have hφ : ∀ u : S, φ u = ksL5F gs cs (u : Idx n) := fun u => rfl
  have hφt : φ ⟨t, Subgroup.subset_closure ht⟩ = tp := by
    have hgen0 : ksL5F gs cs (gs[0]'(hgpos)) = cs[0] := ksL5_f_gen_eq_cs hrel hcs_len hgpos
    have hcsi0 : cs.getD 0 1 = cs[0] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    have h : ksL5F gs cs t = tp := by rw [← hhead, hgen0, ← hcsi0, hcs0]
    simpa [hφ] using h
  refine ⟨φ, hφ, hφt, ?_, ?_⟩
  · intro a
    exact ksL5_evW_central hcs_cent (ksL5WordOf gs (a : Idx n))
  · intro u hu
    obtain ⟨-, hmem, hev⟩ := ksL5_wordOf_spec gs (u : Idx n) u.2
    have hwW : ksL5WordOf gs (u : Idx n) ∈ (wordsOf gs).map Prod.snd :=
      List.mem_map.mpr ⟨(u, ksL5WordOf gs (u : Idx n)), hmem, rfl⟩
    have hw := hW _ hwW
    have hdom : evW gs (ksL5WordOf gs (u : Idx n)) = (u : Idx n) := hev
    have h2 : isInv (evW cs (ksL5WordOf gs (u : Idx n))) = true ∧
        blkOf ci ld (evW cs (ksL5WordOf gs (u : Idx n))) =
          blkOf ci ld (evW gs (ksL5WordOf gs (u : Idx n))) := by
      apply hw.2
      rw [hdom]
      exact hu
    have hblk := h2.2
    rw [hdom] at hblk
    simpa [hφ, ksL5F] using hblk

theorem homExists_sound {t tp : Idx n} {ci : Array Nat} {ld : List Nat}
    (h : homExists (mkHomCtx t) ci ld tp = true) :
    ∃ φ : Subgroup.closure {g | g ∈ (mkHomCtx t).gens} →* Idx n, Function.Injective φ ∧
      φ ⟨t, Subgroup.subset_closure (mem_mkHomCtx_gens t)⟩ = tp ∧ (∀ a, φ a * tp = tp * φ a) ∧
      ∀ u : Subgroup.closure {g | g ∈ (mkHomCtx t).gens}, isInv (u : Idx n) = true →
        blkOf ci ld (φ u) = blkOf ci ld (u : Idx n) := by
  obtain ⟨cs, hlen, hzero, hcent, hrel, hW⟩ := ksL5_homExists_data h
  obtain ⟨φ, hφ, hφt, hcent', hblk⟩ :=
    ksL5_mk_phi (gs := (mkHomCtx t).gens) (cs := cs) hlen hzero hcent hrel hW
      (ksL5_gens_length_pos t) (ksL5_gens_head t) (mem_mkHomCtx_gens t)
  exact ⟨φ, ksL5_phi_inj hW φ hφ, hφt, hcent', hblk⟩

theorem homExists_false {t tp : Idx n} {ci : Array Nat} {ld : List Nat} (L : List (Idx n))
    (hL : L.Nodup) (hLS : ∀ x ∈ L, x ∈ Subgroup.closure {g | g ∈ (mkHomCtx t).gens})
    (τ₀ : Nat × Nat × Nat × Nat) (h : scpRefute ci ld t tp L τ₀ = true) :
    homExists (mkHomCtx t) ci ld tp = false := by
  rw [Bool.eq_false_iff]
  intro he
  obtain ⟨φ, hinj, hφt, hcent, hblk⟩ := homExists_sound he
  rw [count_le φ hinj hblk _ hφt hcent L hL hLS τ₀] at h
  exact Bool.false_ne_true h

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
