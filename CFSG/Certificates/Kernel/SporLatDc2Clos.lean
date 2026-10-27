module

public import CFSG.Certificates.Kernel.SporLatDc2Ctx
public import CFSG.Certificates.Kernel.SporLatDcSortSound
public import CFSG.Certificates.Kernel.SporLatDcLists

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (labF sortedLt allIdx all2 takeN lookC chunksOK allIdx_iff lookC_eq
  chunksOK_pos sortedLt_nodup)
open CFSG.KC.LQT.PW (imgW)
open MulAction

theorem takeN_eq {α : Type} : ∀ (k : ℕ) (l : List α), takeN k l = l.take k
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, a :: l => by rw [takeN, takeN_eq k l]; rfl

theorem all2_spec {α β : Type} {f : α → β → Bool} : ∀ {l : List α} {m : List β},
    all2 f l m = true →
      l.length = m.length ∧ ∀ i (hi : i < l.length) (hm : i < m.length), f l[i] m[i] = true
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | a :: l, b :: m, h => by
    rw [all2, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := all2_spec h.2
    refine ⟨by simp [h1], fun i hi hm => ?_⟩
    rcases i with _ | i
    · exact h.1
    · exact h2 i (by simpa using hi) (by simpa using hm)
  | [], _ :: _, h => by simp [all2] at h
  | _ :: _, [], h => by simp [all2] at h

theorem perm_of_ord {B : ℕ} {C : List (List (List ℕ))} {ord : List ℕ} (hC : chunksOK B C = true)
    (hol : ord.length = C.flatten.length) (hoi : ∀ i ∈ ord, i < C.flatten.length)
    (hs : sortedLt (ord.map (lookC B C)) = true) :
    (ord.map (lookC B C)).Perm C.flatten ∧ C.flatten.Nodup := by
  have hnd' := sortedLt_nodup hs
  have hsub : ord.map (lookC B C) ⊆ C.flatten := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [lookC_eq hC i (hoi i hi), List.getD_eq_getElem _ _ (hoi i hi)]
    exact List.getElem_mem _
  have hp := (List.subperm_of_subset hnd' hsub).perm_of_length_le (by simp [hol])
  exact ⟨hp, hp.nodup_iff.1 hnd'⟩

theorem rowC_spec {B w code N : ℕ} {C : List (List (List ℕ))} (hC : chunksOK B C = true)
    (hN : C.flatten.length = N) (f : List ℕ → List ℕ)
    (h : (List.zip ((List.range N).map (imgW w code)) C.flatten).all
      (fun e => Nat.blt e.1 N && lookC B C e.1 == f e.2) = true) :
    ∀ i < N, imgW w code i < N ∧ C.flatten.getD (imgW w code i) [] = f (C.flatten.getD i []) := by
  intro i hi
  have hiz : i < (List.zip ((List.range N).map (imgW w code)) C.flatten).length := by
    rw [List.length_zip, List.length_map, List.length_range, hN, Nat.min_self]; exact hi
  have e := List.all_eq_true.1 h _ (List.getElem_mem hiz)
  simp only [List.getElem_zip, List.getElem_map, List.getElem_range, Bool.and_eq_true, Nat.blt_eq,
    beq_iff_eq] at e
  refine ⟨e.1, ?_⟩
  rw [← lookC_eq hC (imgW w code i) (by omega), e.2, List.getD_eq_getElem _ _ (by omega)]

theorem treeC_spec {N ng : ℕ} {lab : List (List ℕ)} (r : ℕ → Bool) (idx : ℕ → ℕ → ℕ)
    (f : ℕ → List ℕ → List ℕ) {par via : List ℕ} (hpl : par.length = N) (hvl : via.length = N)
    (hrow : ∀ v < ng, ∀ j < N, lab.getD (idx v j) [] = f v (lab.getD j []))
    (h : allIdx (fun i e => r i || (Nat.blt e.1 i && Nat.blt e.2 ng && Nat.beq (idx e.2 e.1) i)) 0
      (List.zip par via) = true) :
    ∀ i < N, r i = false → ∃ j < i, ∃ v < ng, f v (lab.getD j []) = lab.getD i [] := by
  intro i hi hr
  have hiz : i < (List.zip par via).length := by
    rw [List.length_zip, hpl, hvl, Nat.min_self]; exact hi
  have e := (allIdx_iff _ 0 _).1 h i hiz
  simp only [Nat.zero_add, List.getElem_zip, hr, Bool.false_or, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at e
  obtain ⟨⟨hj, hv⟩, he⟩ := e
  refine ⟨_, hj, _, hv, ?_⟩
  rw [← hrow _ hv _ (by omega), he]

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

@[expose] def gens (G : List (List ℕ)) : Set Γ := {g | ∃ w ∈ G, P.elt w = g}

theorem clOK_sound {G : List (List ℕ)} (hG : ∀ w ∈ G, ∀ l ∈ w, l < P.C.ns) (x : PtL n)
    {Pr : List ℕ → Bool} {Cl : Clos} (h : clOK P.C P.D G x.val Pr Cl = true) :
    (Cl.ord.map (lookC Cl.B Cl.C)).Perm Cl.C.flatten ∧
    sortedLt (Cl.ord.map (lookC Cl.B Cl.C)) = true ∧ Cl.C.flatten.Nodup ∧
    0 < Cl.C.flatten.length ∧
    (∀ y ∈ Cl.C.flatten, ∃ k ∈ Subgroup.closure (P.gens G), ∃ w ∈ Cl.R,
      (∀ l ∈ w, l < P.C.ns) ∧ Pr (P.elt w • x).val = true ∧ y = (k • P.elt w • x).val) ∧
    (∀ k ∈ Subgroup.closure (P.gens G), ∀ z : PtL n, z.val ∈ Cl.C.flatten →
      (k • z).val ∈ Cl.C.flatten) := by
  unfold clOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hC, hRl⟩, hR⟩, hrows⟩, hpl⟩, hvl⟩, htree⟩, hol⟩, hoi⟩, hs⟩ := h
  rw [Nat.ble_eq] at hRl
  rw [Nat.beq_eq] at hpl hvl hol
  have hoi' : ∀ i ∈ Cl.ord, i < Cl.C.flatten.length := fun i hi => by
    have e := List.all_eq_true.1 hoi i hi
    rwa [Nat.blt_eq] at e
  have hns : P.C.ns ≤ P.C.nl := le_trans P.ns_le P.nf_le
  have hGl : ∀ w ∈ G, ∀ l ∈ w, l < P.C.nl := fun w hw l hl => lt_of_lt_of_le (hG w hw l hl) hns
  obtain ⟨hperm, hnd⟩ := perm_of_ord hC hol hoi' hs
  rw [takeN_eq] at hR
  obtain ⟨hRlen, hR'⟩ := all2_spec hR
  have hroot : ∀ i (hi : i < Cl.R.length), (∀ l ∈ Cl.R[i], l < P.C.ns) ∧
      Pr (P.elt Cl.R[i] • x).val = true ∧
      Cl.C.flatten.getD i [] = (P.elt Cl.R[i] • x).val := by
    intro i hi
    have e := hR' i hi (by rw [← hRlen]; exact hi)
    simp only [Bool.and_eq_true, beq_iff_eq, isS_iff, List.getElem_take] at e
    obtain ⟨⟨hw, hy⟩, hp⟩ := e
    rw [P.smul_lw (fun l hl => lt_of_lt_of_le (hw l hl) hns) x, ← hy,
      List.getD_eq_getElem _ _ (by omega)]
    exact ⟨hw, hp, rfl⟩
  have hrow : ∀ v < G.length, ∀ j < Cl.C.flatten.length,
      imgW P.D.pw (Cl.rows.getD v 0) j < Cl.C.flatten.length ∧
      Cl.C.flatten.getD (imgW P.D.pw (Cl.rows.getD v 0) j) [] =
        lw P.C (G.getD v []) (Cl.C.flatten.getD j []) := fun v hv => by
    have e := List.all_eq_true.1 hrows v (List.mem_range.2 hv)
    exact rowC_spec hC rfl (lw P.C (G.getD v [])) e
  have hrow' : ∀ v (hv : v < G.length), ∀ y ∈ Cl.C.flatten, lw P.C G[v] y ∈ Cl.C.flatten := by
    intro v hv y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    obtain ⟨h1, h2⟩ := hrow v hv i hi
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hv] at h2
    rw [← h2, List.getD_eq_getElem _ _ h1]
    exact List.getElem_mem _
  have htr := treeC_spec (ng := G.length) (lab := Cl.C.flatten) (fun i => Nat.blt i Cl.R.length)
    (fun v j => imgW P.D.pw (Cl.rows.getD v 0) j) (fun v y => lw P.C (G.getD v []) y) hpl hvl
    (fun v hv j hj => (hrow v hv j hj).2) htree
  have hreach : ∀ i < Cl.C.flatten.length, ∃ k ∈ Subgroup.closure (P.gens G),
      ∃ w ∈ Cl.R, (∀ l ∈ w, l < P.C.ns) ∧ Pr (P.elt w • x).val = true ∧
        Cl.C.flatten.getD i [] = (k • P.elt w • x).val := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hiR : i < Cl.R.length
      · obtain ⟨hw, hp, he⟩ := hroot i hiR
        exact ⟨1, Subgroup.one_mem _, Cl.R[i], List.getElem_mem _, hw, hp,
          by rw [one_smul]; exact he⟩
      · obtain ⟨j, hj, v, hv, he⟩ := htr i hi
          (Bool.eq_false_iff.2 fun h' => hiR (by rwa [Nat.blt_eq] at h'))
        obtain ⟨k, hk, w, hwR, hw, hp, hkj⟩ := ih j hj (by omega)
        have hGv : G.getD v [] ∈ G := by
          rw [List.getD_eq_getElem _ _ hv]; exact List.getElem_mem hv
        refine ⟨P.elt (G.getD v []) * k, Subgroup.mul_mem _
          (Subgroup.subset_closure ⟨_, hGv, rfl⟩) hk, w, hwR, hw, hp, ?_⟩
        rw [← he, mul_smul, P.smul_lw (hGl _ hGv), ← hkj]
  have hclosed : ∀ k ∈ Subgroup.closure (P.gens G), ∀ z : PtL n, z.val ∈ Cl.C.flatten →
      (k • z).val ∈ Cl.C.flatten := by
    intro k hk
    refine smul_mem_of_closure (F := {z : PtL n | z.val ∈ Cl.C.flatten}) ?_ hk
    rintro e ⟨w, hw, rfl⟩ z hz
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    show (P.elt G[j] • z).val ∈ Cl.C.flatten
    rw [P.smul_lw (hGl _ (List.getElem_mem hj))]
    exact hrow' j hj _ hz
  refine ⟨hperm, hs, hnd, (chunksOK_pos hC).2, fun y hy => ?_, hclosed⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  rw [← List.getD_eq_getElem _ [] hi]
  exact hreach i hi

theorem chunks_of_clOK {G : List (List ℕ)} {x : List ℕ} {Pr : List ℕ → Bool} {Cl : Clos}
    (h : clOK P.C P.D G x Pr Cl = true) : chunksOK Cl.B Cl.C = true := by
  unfold clOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1

theorem atOK_mem {Cl : Clos} (hC : chunksOK Cl.B Cl.C = true) {x : PtL n} {w : List ℕ}
    (hw : ∀ l ∈ w, l < P.C.nl) {i : ℕ} (h : atOK P.C Cl x.val w i = true) :
    (P.elt w • x).val ∈ Cl.C.flatten := by
  simp only [atOK, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  rw [P.smul_lw hw x, ← h.2, lookC_eq hC _ h.1, List.getD_eq_getElem _ _ h.1]
  exact List.getElem_mem _

theorem sLet_lt : ∀ w ∈ sLet P.C, ∀ l ∈ w, l < P.C.ns := by
  intro w hw l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hw
  rw [List.mem_singleton] at hl
  rw [hl]
  exact List.mem_range.1 hl'

theorem closure_sLet : Subgroup.closure (P.gens (sLet P.C)) = P.S := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hw
    exact P.elt_mem_S (by simpa using hl)
  · rw [S, Subgroup.closure_le]
    intro x hx
    obtain ⟨l, hl, -, rfl⟩ := P.mem_take_letter hx
    apply Subgroup.subset_closure
    exact ⟨[l], List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩, by rw [elt_cons, elt_nil, mul_one]⟩

end Dc2SoundCtx

end CFSG.KC.SLD2

end
