module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CElt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.A6C

variable {n : ℕ} {Γ : Type} [Group Γ]

private lemma derivOK_spec {step : ℕ → Mat → Mat} {k : ℕ} {x0 : Mat} {r : Rec} {N : ℕ}
    (h : derivOK step k x0 r N = true) :
    r.L.size = N ∧ r.par.size = N ∧ r.lab.size = N ∧ eqP r.L[0]! x0 = true ∧
      ∀ i < N, i = 0 ∨ (r.par[i]! < i ∧ r.lab[i]! < k ∧
        eqP r.L[i]! (step r.lab[i]! r.L[r.par[i]!]!) = true) := by
  rw [derivOK] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hL, hpar⟩, hlab⟩, hseed⟩, hall⟩ := h
  rw [beq_iff_eq] at hL hpar hlab
  refine ⟨hL, hpar, hlab, hseed, fun i hi => ?_⟩
  rcases (Bool.or_eq_true_iff.mp ((List.all_eq_true.mp hall) i (List.mem_range.mpr hi)))
    with h0 | hrest
  · exact Or.inl (by simpa [beq_iff_eq] using h0)
  · rw [Bool.and_eq_true, Bool.and_eq_true] at hrest
    obtain ⟨⟨hp, hl⟩, he⟩ := hrest
    exact Or.inr ⟨by simpa using hp, by simpa using hl, he⟩
private lemma all_simOK_getElem! {A : Array Mat} (h : A.all (simOK n) = true)
    {i : ℕ} (hi : i < A.size) : simOK n A[i]! = true := by
  simpa only [getElem!_pos A i hi] using (Array.all_eq_true.mp h) i hi
private lemma centOK_gen {E : Array Mat} {x0 : Mat}
    (h : E.all (fun e => simOK n e && commP n e x0) = true) {i : ℕ} (hi : i < E.size) :
    simOK n E[i]! = true ∧ commP n E[i]! x0 = true := by
  have h1 := (Array.all_eq_true.mp h) i hi
  rw [Bool.and_eq_true] at h1
  exact ⟨by simpa only [getElem!_pos E i hi] using h1.1,
    by simpa only [getElem!_pos E i hi] using h1.2⟩
private lemma toList_getElem_eq_getElem! {L : Array Mat} {i : ℕ} (h : i < L.toList.length) :
    L.toList[i] = L[i]! := by
  rw [← getElem!_pos L.toList i h, Array.getElem!_toList]
private lemma mem_toList_getElem! {L : Array Mat} {y : Mat} (hy : y ∈ L.toList) :
    ∃ i, i < L.size ∧ L[i]! = y := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hy
  have h1 : L.toList[i] = L[i]! := toList_getElem_eq_getElem! (L := L) (i := i) hi
  exact ⟨i, by simpa [Array.length_toList] using hi, h1.symm.trans hget⟩
private lemma nodup_map_of_keysNodup (m : A6CModel n Γ) {L : Array Mat}
    (hk : keysNodup L = true) (hsim : ∀ i < L.size, A6CSimArr n L[i]!) :
    (L.toList.map (A6CElt m)).Nodup := by
  have hnd : L.toList.Nodup := List.Nodup.of_map keyM (by
    apply a6c_nodupKeys_sound
    simpa only [keysNodup] using hk)
  refine List.Nodup.map_on (l := L.toList) (f := A6CElt m) ?_ hnd
  intro x hx y hy hxy
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy
  rw [← hxi, ← hyj] at hxy ⊢
  have hiS : i < L.size := by simpa [Array.length_toList] using hi
  have hjS : j < L.size := by simpa [Array.length_toList] using hj
  have hxy' : A6CElt m L[i]! = A6CElt m L[j]! := by
    rw [← toList_getElem_eq_getElem! (L := L) (i := i) hi,
      ← toList_getElem_eq_getElem! (L := L) (i := j) hj]
    exact hxy
  have hij : i = j := by
    by_contra hne
    have hkey : keyM L[i]! = keyM L[j]! := by
      apply (a6c_keyM_eq_iff n (hsim i hiS).1 (hsim j hjS).1).mpr
      rcases (Bool.or_eq_true_iff.mp
        ((a6cElt_eq_iff m (hsim i hiS) (hsim j hjS)).mpr hxy')) with h | h
      · exact Or.inl (congrArg (A6CToMat n) (by simpa [beq_iff_eq] using h))
      · have h' : L[i]! = negM L[j]! := by simpa [beq_iff_eq] using h
        exact Or.inr (by rw [h', a6c_toMat_negM])
    exact absurd hkey (a6c_keysNodup_sound hk hiS hjS hne)
  exact (hnd.getElem_inj_iff).mpr hij
private theorem derivOK_strong (m : A6CModel n Γ) {step : ℕ → Mat → Mat} {k : ℕ} {x0 : Mat}
    {r : Rec} {N : ℕ} (hd : derivOK step k x0 r N = true)
    (hsim : ∀ l < k, ∀ x, A6CSimArr n x → A6CSimArr n (step l x))
    (hseed : A6CSimArr n x0) (P : Mat → Prop)
    (hseedP : ∀ y, A6CSimArr n y → eqP y x0 = true → P y)
    (hPeq : ∀ u v, A6CSimArr n u → A6CSimArr n v → eqP u v = true → (P u ↔ P v))
    (hstepP : ∀ l < k, ∀ x, A6CSimArr n x → P x → P (step l x)) :
    ∀ i < N, A6CSimArr n r.L[i]! ∧ P r.L[i]! := by
  obtain ⟨_, _, _, h0, hstep⟩ := derivOK_spec hd
  have key : ∀ i, i < N → A6CSimArr n r.L[i]! ∧ P r.L[i]! := by
    intro i
    refine Nat.strong_induction_on (p := fun i => i < N →
      A6CSimArr n r.L[i]! ∧ P r.L[i]!) i ?_
    intro i ih hi
    rcases hstep i hi with hi0 | ⟨hj, hl, heq⟩
    · subst hi0
      have hs0 : A6CSimArr n r.L[0]! := by
        rcases (show r.L[0]! = x0 ∨ r.L[0]! = negM x0 by
          simpa only [eqP, Bool.or_eq_true, beq_iff_eq] using h0) with h | h
        · rw [h]; exact hseed
        · rw [h]; exact hseed.negM
      exact ⟨hs0, hseedP _ hs0 h0⟩
    · have hjN : r.par[i]! < N := lt_trans hj hi
      obtain ⟨hsimj, hPj⟩ := ih (r.par[i]!) hj hjN
      have hsims : A6CSimArr n (step (r.lab[i]!) r.L[r.par[i]!]!) :=
        hsim (r.lab[i]!) hl _ hsimj
      have hPs : P (step (r.lab[i]!) r.L[r.par[i]!]!) :=
        hstepP (r.lab[i]!) hl _ hsimj hPj
      have hsi : A6CSimArr n r.L[i]! := by
        rcases (show r.L[i]! = step (r.lab[i]!) r.L[r.par[i]!]! ∨
            r.L[i]! = negM (step (r.lab[i]!) r.L[r.par[i]!]!) by
          simpa only [eqP, Bool.or_eq_true, beq_iff_eq] using heq) with h | h
        · rw [h]; exact hsims
        · rw [h]; exact hsims.negM
      exact ⟨hsi, (hPeq _ _ hsi hsims heq).mpr hPs⟩
  exact key
theorem a6c_classOK_sound (m : A6CModel n Γ) {G : Array Mat} {x0 : Mat} {r : Rec} {N : ℕ}
    (h : classOK n G x0 r N = true) :
    r.L.toList.length = N ∧ (r.L.toList.map (A6CElt m)).Nodup ∧
      ∀ y ∈ r.L.toList, A6CSimArr n y ∧ IsConj (A6CElt m x0) (A6CElt m y) := by
  have hc := h
  rw [classOK] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hGall, hx0sim⟩, hd⟩, hk⟩ := h
  have hseed : A6CSimArr n x0 := A6CSimArr.of_simOK hx0sim
  have hsim : ∀ l < G.size, ∀ x, A6CSimArr n x → A6CSimArr n (conjStep n G l x) := by
    intro l hl x hx
    have hgl : A6CSimArr n G[l]! := A6CSimArr.of_simOK (all_simOK_getElem! hGall hl)
    simpa only [conjStep] using A6CSimArr.conjN hgl hx
  have hstepP : ∀ l < G.size, ∀ x, A6CSimArr n x →
      IsConj (A6CElt m x0) (A6CElt m x) →
      IsConj (A6CElt m x0) (A6CElt m (conjStep n G l x)) := by
    intro l hl x hx hPx
    have hgl : A6CSimArr n G[l]! := A6CSimArr.of_simOK (all_simOK_getElem! hGall hl)
    have hconj : A6CElt m (conjStep n G l x) =
        A6CElt m G[l]! * A6CElt m x * (A6CElt m G[l]!)⁻¹ := by
      simpa only [conjStep] using a6cElt_conjN m hgl hx
    rw [hconj]
    obtain ⟨c, hc'⟩ := isConj_iff.mp hPx
    refine isConj_iff.mpr ⟨A6CElt m G[l]! * c, by
      rw [show (A6CElt m G[l]! * c) * A6CElt m x0 * (A6CElt m G[l]! * c)⁻¹
          = A6CElt m G[l]! * (c * A6CElt m x0 * c⁻¹) * (A6CElt m G[l]!)⁻¹ by group,
        hc']⟩
  have key := derivOK_strong m hd hsim hseed
    (fun y => IsConj (A6CElt m x0) (A6CElt m y))
    (fun y hy heq => by
      have hyx : A6CElt m y = A6CElt m x0 := (a6cElt_eq_iff m hy hseed).mp heq
      rw [hyx])
    (fun u v hu hv heq => by
      have huv : A6CElt m u = A6CElt m v := (a6cElt_eq_iff m hu hv).mp heq
      simp only [huv])
    hstepP
  have hLs : r.L.size = N := (derivOK_spec hd).1
  refine ⟨by rw [Array.length_toList]; exact hLs, ?_, ?_⟩
  · exact nodup_map_of_keysNodup m hk (fun i hi => (key i (by rwa [hLs] at hi)).1)
  · intro y hy
    obtain ⟨i, hi, hget⟩ := mem_toList_getElem! hy
    have hiN : i < N := by rwa [hLs] at hi
    rw [← hget]
    exact key i hiN
theorem a6c_centOK_sound (m : A6CModel n Γ) {E : Array Mat} {x0 : Mat} {r : Rec}
    {N : ℕ} (h : centOK n E x0 r N = true) (hx0 : simOK n x0 = true) :
    r.L.toList.length = N ∧ (r.L.toList.map (A6CElt m)).Nodup ∧
      ∀ y ∈ r.L.toList, A6CSimArr n y ∧
        A6CElt m y * A6CElt m x0 = A6CElt m x0 * A6CElt m y := by
  rw [centOK] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hEall, hd⟩, hk⟩ := h
  have hseed : A6CSimArr n (idN n) := A6CSimArr.idN n
  have hseed_sim : A6CSimArr n x0 := A6CSimArr.of_simOK hx0
  have hsim : ∀ l < E.size, ∀ x, A6CSimArr n x → A6CSimArr n (leftStep n E l x) := by
    intro l hl x hx
    have hgl : A6CSimArr n E[l]! := A6CSimArr.of_simOK (centOK_gen hEall hl).1
    simpa only [leftStep] using A6CSimArr.mulN hgl hx
  have hstepP : ∀ l < E.size, ∀ x, A6CSimArr n x →
      (A6CElt m x * A6CElt m x0 = A6CElt m x0 * A6CElt m x) →
      (A6CElt m (leftStep n E l x) * A6CElt m x0 =
        A6CElt m x0 * A6CElt m (leftStep n E l x)) := by
    intro l hl x hx hPx
    have hgl : A6CSimArr n E[l]! := A6CSimArr.of_simOK (centOK_gen hEall hl).1
    have hcomm : A6CElt m E[l]! * A6CElt m x0 = A6CElt m x0 * A6CElt m E[l]! :=
      (a6cElt_commP m hgl hseed_sim).mp (centOK_gen hEall hl).2
    have hmul : A6CElt m (leftStep n E l x) = A6CElt m E[l]! * A6CElt m x := by
      simpa only [leftStep] using a6cElt_mulN m hgl hx
    rw [hmul]
    calc (A6CElt m E[l]! * A6CElt m x) * A6CElt m x0
        = A6CElt m E[l]! * (A6CElt m x * A6CElt m x0) := by rw [mul_assoc]
      _ = A6CElt m E[l]! * (A6CElt m x0 * A6CElt m x) := by rw [hPx]
      _ = A6CElt m x0 * (A6CElt m E[l]! * A6CElt m x) := by
          rw [← mul_assoc, hcomm, mul_assoc]
  have key := derivOK_strong m hd hsim hseed
    (fun y => A6CElt m y * A6CElt m x0 = A6CElt m x0 * A6CElt m y)
    (fun y hy heq => by
      have hyx : A6CElt m y = A6CElt m (idN n) := (a6cElt_eq_iff m hy hseed).mp heq
      rw [hyx, a6cElt_idN]; simp)
    (fun u v hu hv heq => by
      have huv : A6CElt m u = A6CElt m v := (a6cElt_eq_iff m hu hv).mp heq
      simp only [huv])
    hstepP
  have hLs : r.L.size = N := (derivOK_spec hd).1
  refine ⟨by rw [Array.length_toList]; exact hLs, ?_, ?_⟩
  · exact nodup_map_of_keysNodup m hk (fun i hi => (key i (by rwa [hLs] at hi)).1)
  · intro y hy
    obtain ⟨i, hi, hget⟩ := mem_toList_getElem! hy
    have hiN : i < N := by rwa [hLs] at hi
    rw [← hget]
    exact key i hiN
theorem a6c_complete [Finite Γ] (m : A6CModel n Γ) {G E : Array Mat} {x0 : Mat} {rc rz : Rec}
    {N N' : ℕ} (hc : classOK n G x0 rc N = true) (hz : centOK n E x0 rz N' = true)
    (hcard : N * N' = Nat.card Γ) :
    (∀ s, IsConj (A6CElt m x0) s → s ∈ rc.L.toList.map (A6CElt m)) ∧
      ∀ c, c * A6CElt m x0 = A6CElt m x0 * c → c ∈ rz.L.toList.map (A6CElt m) := by
  classical
  have hcx := hc
  rw [classOK] at hcx
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcx
  obtain ⟨⟨⟨_, hx0sim⟩, _⟩, _⟩ := hcx
  have hsnd := a6c_classOK_sound m hc
  have hznd := a6c_centOK_sound m hz hx0sim
  let S : Finset Γ := (rc.L.toList.map (A6CElt m)).toFinset
  let C : Finset Γ := (rz.L.toList.map (A6CElt m)).toFinset
  have hScard : S.card = N := by
    rw [show S = (rc.L.toList.map (A6CElt m)).toFinset from rfl,
      List.toFinset_card_of_nodup hsnd.2.1, List.length_map, hsnd.1]
  have hCcard : C.card = N' := by
    rw [show C = (rz.L.toList.map (A6CElt m)).toFinset from rfl,
      List.toFinset_card_of_nodup hznd.2.1, List.length_map, hznd.1]
  have hS : ∀ s ∈ S, IsConj (A6CElt m x0) s := by
    intro s hs
    have hs' : s ∈ rc.L.toList.map (A6CElt m) := by simpa only [S, List.mem_toFinset] using hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hs'
    exact (hsnd.2.2 y hy).2
  have hC : ∀ c ∈ C, c * A6CElt m x0 = A6CElt m x0 * c := by
    intro c hcC
    have hcC' : c ∈ rz.L.toList.map (A6CElt m) := by simpa only [C, List.mem_toFinset] using hcC
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hcC'
    exact (hznd.2.2 y hy).2
  have hcard' : S.card * C.card = Nat.card Γ := by rw [hScard, hCcard, hcard]
  obtain ⟨hSall, hCall⟩ := a6c_lemmaE (A6CElt m x0) S C hS hC hcard'
  exact ⟨fun s hs => by simpa only [S, List.mem_toFinset] using hSall s hs,
    fun c hcC => by simpa only [C, List.mem_toFinset] using hCall c hcC⟩
theorem a6c_natCard_le_length_filter (m : A6CModel n Γ) {L : List Mat} (p : Mat → Bool)
    {S : Set Γ} (hS : ∀ c ∈ S, ∃ y ∈ L, p y = true ∧ A6CElt m y = c) :
    Nat.card S ≤ (L.filter p).length := by
  classical
  have hST : S ⊆ (((L.filter p).map (A6CElt m)).toFinset : Set Γ) := by
    intro c hc
    obtain ⟨y, hyL, hp, rfl⟩ := hS c hc
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hyL, hp⟩, rfl⟩)
  calc Nat.card S ≤ Nat.card (((L.filter p).map (A6CElt m)).toFinset : Set Γ) :=
        Nat.card_mono (Finset.finite_toSet _) hST
    _ = ((L.filter p).map (A6CElt m)).toFinset.card := by
        rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ ≤ (L.filter p).length := by
        rw [← List.length_map (A6CElt m)]
        exact List.toFinset_card_le ((L.filter p).map (A6CElt m))
theorem a6c_natCard_eq_length_filter (m : A6CModel n Γ) {L : List Mat}
    (hnd : (L.map (A6CElt m)).Nodup) (p : Mat → Bool) {S : Set Γ}
    (hS : ∀ c, c ∈ S ↔ ∃ y ∈ L, p y = true ∧ A6CElt m y = c) :
    Nat.card S = (L.filter p).length := by
  classical
  have hST : S = (((L.filter p).map (A6CElt m)).toFinset : Set Γ) := by
    ext c
    rw [hS c]
    constructor
    · rintro ⟨y, hyL, hp, rfl⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hyL, hp⟩, rfl⟩)
    · intro hc
      have hc' : c ∈ ((L.filter p).map (A6CElt m)).toFinset := hc
      rw [List.mem_toFinset] at hc'
      obtain ⟨y, hyf, rfl⟩ := List.mem_map.mp hc'
      exact ⟨y, List.mem_of_mem_filter hyf, List.of_mem_filter hyf, rfl⟩
  have hTnodup : ((L.filter p).map (A6CElt m)).Nodup :=
    (List.filter_sublist.map (A6CElt m)).nodup hnd
  rw [hST, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hTnodup,
    List.length_map]
end CFSG.OddStandard.SmallF3.Omega