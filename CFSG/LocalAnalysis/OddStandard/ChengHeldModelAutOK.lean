module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelClosure
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelAut
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTables

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel Subgroup
open CFSG.OddStandard.ChengHeld.M1b (evalE)

variable {H : Type} [Group H]

theorem autOK_rec {M : RegModel} (R : Rep M H) (hT : TreeSpec M) (x : Fin 7 → H)
    (hx : ∀ j : Fin 7, R.pt (x j) = M.g j.val) {α k : ℕ} (hα : α < 3) (hk : k < 3)
    (σ : H →* H) (hσ : ActTable α k σ x) :
    (M.autMap (M.tabImgs α k)).size = M.N ∧
      ∀ h : H, (M.autMap (M.tabImgs α k))[R.pt h]! = R.pt (σ h) :=
  Rep.autMap_spec R hT _ σ x hx (Rep.tabImgs_get R x hx hα hk σ hσ)

theorem autOK_fold_mem {β : Type} (f : ℕ → List ℕ)
    (stp : β × List (List ℕ) → ℕ → β × List (List ℕ))
    (hstp : ∀ st s, (stp st s).2 = st.2 ∨ (stp st s).2 = st.2 ++ [f s]) (l : List ℕ) :
    ∀ st : β × List (List ℕ), ∀ o ∈ (l.foldl stp st).2, o ∈ st.2 ∨ ∃ s ∈ l, o = f s := by
  induction l with
  | nil => exact fun st o ho => Or.inl ho
  | cons s l ih =>
    intro st o ho
    rw [List.foldl_cons] at ho
    rcases ih _ o ho with h | ⟨s', hs', rfl⟩
    · rcases hstp st s with e | e <;> rw [e] at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_self, List.mem_singleton.1 h⟩
    · exact Or.inr ⟨s', List.mem_cons_of_mem _ hs', rfl⟩

theorem autOK_orbit_rep {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) :
    ∀ o ∈ M.twOrbits a, ∃ s : H, s * σ s = 1 ∧ R.pt s ∈ o := by
  intro o ho
  rw [twOrbits_eq_foldl] at ho
  obtain h | ⟨s, hs, rfl⟩ := autOK_fold_mem
    (fun s => ((List.range M.N).map fun x => M.m (M.m M.inv[x]! s) a[x]!).eraseDups) _
    (fun st s => by split <;> simp) _ _ o ho
  · simp at h
  · obtain ⟨t, rfl, ht⟩ := (Rep.mem_twInvs R σ ha).1 hs
    exact ⟨t, ht, (Rep.mem_twOrb R σ ha t _).2 ⟨1, by simp⟩⟩

theorem autOK_twSizes {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (hs : a.size = M.N) :
    TwSizes σ ((M.twOrbits a).map List.length) := by
  obtain ⟨S1, S2, S3, S4, S5⟩ := Rep.twOrbits_spec R σ ha hs
  have hex : ∀ o : List ℕ, ∃ s : H, o ∈ M.twOrbits a → s * σ s = 1 ∧ R.pt s ∈ o := by
    intro o
    by_cases ho : o ∈ M.twOrbits a
    · obtain ⟨s, hs1, hs2⟩ := autOK_orbit_rep R σ ha o ho
      exact ⟨s, fun _ => ⟨hs1, hs2⟩⟩
    · exact ⟨1, fun h => absurd h ho⟩
  choose rep hrep using hex
  have hcl : ∀ o ∈ M.twOrbits a, ∀ s : H, R.pt s ∈ o ↔ s ∈ twClass σ (rep o) :=
    fun o ho s => S3 o ho (rep o) s (hrep o ho).2
  refine ⟨(M.twOrbits a).map rep, ?_, ?_, ?_, ?_⟩
  · rw [List.map_map]
    refine List.map_congr_left fun o ho => ?_
    exact (R.length_eq_ncard (S1 o ho).1 (S4 o ho) (P := fun s => s ∈ twClass σ (rep o))
      (hcl o ho)).symm
  · intro s hs
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hs
    exact (hrep o ho).1
  · rw [List.pairwise_map]
    refine S5.imp_of_mem fun {o₁ o₂} h₁ h₂ hd hmem => ?_
    exact hd _ ((hcl o₁ h₁ _).2 hmem) (hrep o₂ h₂).2
  · intro s hs
    obtain ⟨o, ho, hso⟩ := S2 s hs
    exact ⟨rep o, List.mem_map_of_mem ho, (hcl o ho s).1 hso⟩

theorem autOK_flag {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (hs : a.size = M.N) (Q : H) :
    Q ∈ twClass σ 1 ↔
      ((M.twOrbits a).any fun o => o.contains 0 && o.contains (R.pt Q)) = true := by
  obtain ⟨-, S2, S3, -, -⟩ := Rep.twOrbits_spec R σ ha hs
  simp only [List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · intro hQ
    obtain ⟨o, ho, h1⟩ := S2 1 (by simp)
    refine ⟨o, ho, R.pt_one ▸ h1, (S3 o ho 1 Q h1).2 hQ⟩
  · rintro ⟨o, ho, h1, hQ⟩
    exact (S3 o ho 1 Q (by rw [R.pt_one]; exact h1)).1 hQ

theorem autOK_fixed_card {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) :
    Nat.card {h : H // σ h = h} = RegModel.card (M.fixedPts a) := by
  rw [R.card_eq_ncard (R.fixedPts_size a), R.set_fixedPts σ ha]
  exact Nat.card_coe_set_eq _

theorem autOK_T_card {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) :
    {s : H | s * σ s = 1}.ncard = (M.twInvs a).length := by
  refine (R.length_eq_ncard (Rep.twInvs_nodup a) (Rep.twInvs_lt R a)
    (P := fun s => s * σ s = 1) fun h => ?_).symm
  rw [Rep.mem_twInvs R σ ha]
  refine ⟨fun ⟨h', e, hh⟩ => ?_, fun hh => ⟨h, rfl, hh⟩⟩
  obtain rfl := R.pt_inj e
  exact hh

theorem autOK_set_closure {M : RegModel} (R : Rep M H) (l : List H) :
    R.set (M.closure (l.map R.pt)) = (Subgroup.closure {h | h ∈ l} : Set H) := by
  have hl : ∀ g ∈ l.map R.pt, g < M.N := fun g hg => by
    obtain ⟨h, -, rfl⟩ := List.mem_map.1 hg
    exact R.pt_lt h
  have e : {h : H | R.pt h ∈ l.map R.pt} = {h | h ∈ l} := by
    ext h
    simp only [Set.mem_ofPred_eq, List.mem_map, R.pt_inj.eq_iff, exists_eq_right]
  rw [R.set_closure hl, e]

theorem autOK_fixed_le {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (l : List H)
    (hb : bSubset (M.fixedPts a) (M.closure (l.map R.pt)) = true) :
    {h | σ h = h} ⊆ (Subgroup.closure {h | h ∈ l} : Set H) := by
  rw [← R.set_fixedPts σ ha, ← autOK_set_closure R l]
  exact (R.bSubset_iff (R.fixedPts_size a)).1 hb

theorem autOK_fixed_eq {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (l : List H)
    (hb : M.fixedPts a = M.closure (l.map R.pt)) :
    {h | σ h = h} = (Subgroup.closure {h | h ∈ l} : Set H) := by
  rw [← R.set_fixedPts σ ha, ← autOK_set_closure R l, hb]

theorem autOK_graph {M : RegModel} (R : Rep M H) (σ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (σ h)) (hs : a.size = M.N) {o : List ℕ}
    (ho : (M.twOrbits a).find? (fun o => o.contains 0) = some o) {Q : H}
    (hQ : o.contains (R.pt Q) = true) : Q ∈ twClass σ 1 := by
  obtain ⟨-, -, S3, -, -⟩ := Rep.twOrbits_spec R σ ha hs
  have h0 : R.pt 1 ∈ o := by
    have h0' := List.find?_some ho
    rw [R.pt_one]
    exact List.contains_iff_mem.1 h0'
  exact (S3 o (List.mem_of_find?_eq_some ho) 1 Q h0).1 (List.contains_iff_mem.1 hQ)

theorem autOK_fixedSub_zero (x : Fin 7 → H) :
    fixedSub 0 x = Subgroup.closure {h | h ∈ [x 0, x 1, x 3 * x 4, x 6]} := by
  rw [fixedSub, ite_eq_left rfl]
  congr 1
  ext h
  simp

theorem autOK_fixedSub_one (x : Fin 7 → H) :
    fixedSub 1 x = Subgroup.closure {h | h ∈ [x 0, x 1, x 2]} := by
  rw [fixedSub, ite_eq_right (by decide), ite_eq_left rfl]
  congr 1
  ext h
  simp

theorem autOK_fixedSub_two (x : Fin 7 → H) :
    fixedSub 2 x = Subgroup.closure {h | h ∈ [x 0, x 3 * x 4 * x 6 * x 2]} := by
  rw [fixedSub, ite_eq_right (by decide), ite_eq_right (by decide)]
  congr 1
  ext h
  simp

theorem autOK_facts {α : ℕ} (hα : α ≤ 2) (h : autOK α = true) (x : Fin 7 → H)
    (R : Rep (mkReg α) H) (hx : ∀ j : Fin 7, R.pt (x j) = (mkReg α).g j.val)
    (hT : TreeSpec (mkReg α)) {k : ℕ} (hk : k < 3) (σ : H →* H) (hσ : ActTable α k σ x) :
    AutFacts α k σ x := by
  unfold autOK at h
  generalize mkReg α = M at h R hx hT
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hs, ha⟩ := autOK_rec R hT x hx (by omega) hk σ hσ
  obtain ⟨⟨⟨⟨hI, hF⟩, hTw⟩, hO⟩, hQ⟩ := h1 k (by simp; omega)
  have e0 : M.g 0 = R.pt (x 0) := (hx 0).symm
  have e1 : M.g 1 = R.pt (x 1) := (hx 1).symm
  have e2 : M.g 2 = R.pt (x 2) := (hx 2).symm
  have e3 : M.g 3 = R.pt (x 3) := (hx 3).symm
  have e4 : M.g 4 = R.pt (x 4) := (hx 4).symm
  have e6 : M.g 6 = R.pt (x 6) := (hx 6).symm
  have hq : (if α = 2 then M.g 0 else M.pw (M.g 0) 2) = R.pt (qOf α x) := by
    rw [qOf, apply_ite R.pt, R.pt_pow, e0]
  have LF : [M.g 0, M.g 1, M.m (M.g 3) (M.g 4), M.g 6] =
      [x 0, x 1, x 3 * x 4, x 6].map R.pt := by
    simp only [List.map_cons, List.map_nil, R.pt_mul, e0, e1, e3, e4, e6]
  have LG : [M.g 0, M.g 1, M.g 2] = [x 0, x 1, x 2].map R.pt := by
    simp only [List.map_cons, List.map_nil, e0, e1, e2]
  have LU : [M.g 0, M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)] =
      [x 0, x 3 * x 4 * x 6 * x 2].map R.pt := by
    simp only [List.map_cons, List.map_nil, R.pt_mul, e0, e2, e3, e4, e6]
  rw [hq] at hQ h2
  rw [LF, LG, LU] at h2
  refine ⟨((R.isInvolAut_iff σ ha hs).1 hI).1, by rw [autOK_fixed_card R σ ha, hF],
    by rw [autOK_T_card R σ ha, hTw], hO ▸ autOK_twSizes R σ ha hs,
    by rw [autOK_flag R σ ha hs, hQ], fun hα1 => ?_, fun hα2 => ?_, fun hα2 hk1 => ?_⟩
  · rw [ite_eq_right (show ¬ α = 2 by omega)] at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨hb0, hb1⟩, hb2⟩ := h2
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · rw [autOK_fixedSub_zero]
      exact autOK_fixed_le R σ ha _ hb0
    · rw [autOK_fixedSub_one]
      exact autOK_fixed_le R σ ha _ hb1
    · rw [autOK_fixedSub_two]
      exact autOK_fixed_le R σ ha _ hb2
  · rw [ite_eq_left hα2] at h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨⟨⟨hb0, hb1⟩, hb2⟩, -⟩ := h2
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · rw [autOK_fixedSub_zero]
      exact autOK_fixed_eq R σ ha _ hb0
    · rw [autOK_fixedSub_one]
      exact autOK_fixed_eq R σ ha _ hb1
    · rw [autOK_fixedSub_two]
      exact autOK_fixed_eq R σ ha _ hb2
  · subst hk1
    rw [ite_eq_left hα2] at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨-, hm⟩ := h2
    have hq2 : qOf α x = x 0 := by rw [qOf, ite_eq_left hα2]
    split at hm
    · rename_i o ho
      simp only [Bool.and_eq_true, hq2, e1, e2, ← R.pt_mul] at hm
      obtain ⟨⟨m1, m2⟩, m3⟩ := hm
      exact ⟨autOK_graph R σ ha hs ho m1, autOK_graph R σ ha hs ho m2,
        autOK_graph R σ ha hs ho m3⟩
    · exact absurd hm Bool.false_ne_true

end CFSG.OddStandard.ChengHeld.Model
