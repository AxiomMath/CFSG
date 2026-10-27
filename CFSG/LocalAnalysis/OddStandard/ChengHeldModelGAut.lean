module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelClosure
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelAut
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelRegular
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTables

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel Subgroup
open CFSG.OddStandard.ChengHeld.M1b (evalE)

variable {H : Type} [Group H]

namespace Rep

theorem gAut_spec {M : RegModel} (R : Rep M H) (x : Fin 7 → H)
    (hx : ∀ j : Fin 7, R.pt (x j) = M.g j.val) (hT : TreeSpec M) {α : ℕ} (hα : α < 3)
    (γ : H →* H) (hγ : GTable α γ x) :
    (M.autMap (M.gImgs α)).size = M.N ∧
      ∀ h : H, (M.autMap (M.gImgs α))[R.pt h]! = R.pt (γ h) :=
  R.autMap_spec hT _ γ x hx (R.gImgs_get x hx hα γ hγ)

theorem set_closure_pts3 {M : RegModel} (R : Rep M H) (a b c : H) :
    R.set (M.closure [R.pt a, R.pt b, R.pt c]) = (closure {a, b, c} : Set H) := by
  have hs : {h : H | R.pt h ∈ [R.pt a, R.pt b, R.pt c]} = {a, b, c} := by
    ext h
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.mem_nil_iff, or_false, R.pt_inj.eq_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [R.set_closure (by simp [R.pt_lt]), hs]

theorem stable_of_elems_all {M : RegModel} (R : Rep M H) {B : Array Bool} (hB : B.size = M.N)
    {a : Array ℕ} (σ : H → H) (ha : ∀ h, a[R.pt h]! = R.pt (σ h))
    (hc : ((elems B).all fun z => B[a[z]!]!) = true) : ∀ y ∈ R.set B, σ y ∈ R.set B := by
  intro y hy
  have hy' : B[a[R.pt y]!]! = true :=
    List.all_eq_true.1 hc (R.pt y) ((R.mem_elems_iff_exists_pt hB).2 ⟨y, rfl, hy⟩)
  rw [ha] at hy'
  exact hy'

theorem fixedFree_of_count {M : RegModel} (R : Rep M H) (x0 : H) (γ : H →* H)
    (hγ0 : γ x0 = x0) {a : Array ℕ} (ha : ∀ h, a[R.pt h]! = R.pt (γ h))
    (hc : ((List.range M.N).filter fun z =>
      (M.closure [R.pt x0])[M.m M.inv[z]! a[z]!]!).length = card (M.closure [R.pt x0])) :
    ∀ y : H, y⁻¹ * γ y ∈ zpowers x0 → y ∈ zpowers x0 := by
  have := R.finite
  have hlt : ∀ g ∈ [R.pt x0], g < M.N := by simp [R.pt_lt]
  have hZ : R.set (M.closure [R.pt x0]) = (zpowers x0 : Set H) := by
    have hs : {h : H | R.pt h ∈ [R.pt x0]} = {x0} := by
      ext h
      simp only [Set.mem_ofPred_eq, List.mem_singleton, R.pt_inj.eq_iff, Set.mem_singleton_iff]
    rw [R.set_closure hlt, hs, zpowers_eq_closure]
  have hmem : ∀ h : H, R.pt h ∈ (List.range M.N).filter (fun z =>
      (M.closure [R.pt x0])[M.m M.inv[z]! a[z]!]!) ↔ h⁻¹ * γ h ∈ zpowers x0 := by
    intro h
    simp only [List.mem_filter, List.mem_range, ← R.pt_inv, ha, ← R.pt_mul]
    rw [← SetLike.mem_coe, ← hZ]
    exact ⟨fun hh => hh.2, fun hh => ⟨R.pt_lt h, hh⟩⟩
  have hlen := R.length_eq_ncard (List.nodup_range.filter _) (fun z hz => by
    simp only [List.mem_filter, List.mem_range] at hz
    exact hz.1) hmem
  have hcard : card (M.closure [R.pt x0]) = (zpowers x0 : Set H).ncard := by
    rw [R.card_eq_ncard (R.closure_size hlt), hZ]
  have hsub : (zpowers x0 : Set H) ⊆ {h | h⁻¹ * γ h ∈ zpowers x0} := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    show (x0 ^ k)⁻¹ * γ (x0 ^ k) ∈ zpowers x0
    rw [map_zpow, hγ0, inv_mul_cancel]
    exact one_mem _
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [← hlen, hc, hcard])
  intro y hy
  have hy' : y ∈ {h | h⁻¹ * γ h ∈ zpowers x0} := hy
  rw [← heq] at hy'
  exact hy'

theorem orbit_maps_lt {M : RegModel} (R : Rep M H) {maps : List (Array ℕ)} {Fs : List (H → H)}
    (h1 : ∀ f ∈ maps, ∃ F ∈ Fs, ∀ h, f[R.pt h]! = R.pt (F h)) :
    ∀ f ∈ maps, ∀ y < M.N, f[y]! < M.N := by
  intro f hf y hy
  obtain ⟨F, -, hF⟩ := h1 f hf
  obtain ⟨h, rfl⟩ := R.pt_surj y hy
  rw [hF]
  exact R.pt_lt _

theorem mem_orbitOf_self {M : RegModel} (R : Rep M H) {maps : List (Array ℕ)}
    {Fs : List (H → H)} (h1 : ∀ f ∈ maps, ∃ F ∈ Fs, ∀ h, f[R.pt h]! = R.pt (F h)) (s : H) :
    R.pt s ∈ M.orbitOf maps (R.pt s) :=
  (orbitOf_spec maps (R.pt_lt s) (R.orbit_maps_lt h1)).2.2.1

theorem isOrbitOf_orbitOf {M : RegModel} (R : Rep M H) {maps : List (Array ℕ)}
    {Fs : List (H → H)} (h1 : ∀ f ∈ maps, ∃ F ∈ Fs, ∀ h, f[R.pt h]! = R.pt (F h))
    (h2 : ∀ F ∈ Fs, ∃ f ∈ maps, ∀ h, f[R.pt h]! = R.pt (F h)) (s : H) :
    IsOrbitOf Fs s {h | R.pt h ∈ M.orbitOf maps (R.pt s)} := by
  obtain ⟨-, -, hmem, hcl, hmin⟩ := orbitOf_spec maps (R.pt_lt s) (R.orbit_maps_lt h1)
  refine ⟨hmem, fun F hF y hy => ?_, fun P hsP hP => ?_⟩
  · obtain ⟨f, hf, hfF⟩ := h2 F hF
    show R.pt (F y) ∈ M.orbitOf maps (R.pt s)
    rw [← hfF]
    exact hcl _ hy f hf
  · intro h hh
    obtain ⟨h', hh'P, hh'⟩ := hmin (fun z => ∃ h' ∈ P, R.pt h' = z) ⟨s, hsP, rfl⟩
      (fun f hf y ⟨h', hh'P, hy⟩ => by
        obtain ⟨F, hF, hfF⟩ := h1 f hf
        exact ⟨F h', hP F hF h' hh'P, by rw [← hy, hfF]⟩) _ hh
    rw [← R.pt_inj hh']
    exact hh'P

theorem isOrbitOf_of_points {M : RegModel} (R : Rep M H) {maps : List (Array ℕ)}
    {Fs : List (H → H)} (h1 : ∀ f ∈ maps, ∃ F ∈ Fs, ∀ h, f[R.pt h]! = R.pt (F h))
    (h2 : ∀ F ∈ Fs, ∃ f ∈ maps, ∀ h, f[R.pt h]! = R.pt (F h)) (s : H) {T : List ℕ}
    (hnd : T.Nodup) (hsub : ∀ z ∈ T, z ∈ M.orbitOf maps (R.pt s))
    (hlen : (M.orbitOf maps (R.pt s)).length ≤ T.length) {O : Set H}
    (hO : ∀ h, h ∈ O ↔ R.pt h ∈ T) : IsOrbitOf Fs s O := by
  have hp := (hnd.subperm hsub).perm_of_length_le hlen
  have hO' : O = {h | R.pt h ∈ M.orbitOf maps (R.pt s)} := by
    ext h
    rw [hO, Set.mem_ofPred_eq, hp.mem_iff]
  rw [hO']
  exact R.isOrbitOf_orbitOf h1 h2 s

theorem isOrbitOf_of_subset {M : RegModel} (R : Rep M H) {maps : List (Array ℕ)}
    {Fs : List (H → H)} (h1 : ∀ f ∈ maps, ∃ F ∈ Fs, ∀ h, f[R.pt h]! = R.pt (F h))
    (h2 : ∀ F ∈ Fs, ∃ f ∈ maps, ∀ h, f[R.pt h]! = R.pt (F h)) (s : H) {O : Set H}
    (hsub : ∀ h ∈ O, R.pt h ∈ M.orbitOf maps (R.pt s))
    (hlen : (M.orbitOf maps (R.pt s)).length ≤ O.ncard) : IsOrbitOf Fs s O := by
  have := R.finite
  obtain ⟨hnd, hlt, -⟩ := orbitOf_spec maps (R.pt_lt s) (R.orbit_maps_lt h1)
  have hc := R.length_eq_ncard hnd hlt (P := fun h => R.pt h ∈ M.orbitOf maps (R.pt s))
    (fun h => Iff.rfl)
  have hO : O = {h | R.pt h ∈ M.orbitOf maps (R.pt s)} :=
    Set.eq_of_subset_of_ncard_le hsub (hc ▸ hlen)
  rw [hO]
  exact R.isOrbitOf_orbitOf h1 h2 s

theorem gMaps_corr {M : RegModel} (R : Rep M H) (x : Fin 7 → H)
    (hx : ∀ j : Fin 7, R.pt (x j) = M.g j.val) (γ : H →* H) {a : Array ℕ}
    (ha : ∀ h, a[R.pt h]! = R.pt (γ h)) :
    (∀ f ∈ a :: (List.range 7).map (fun j => M.conjArr (M.g j)), ∃ F ∈ gMaps γ x,
      ∀ h, f[R.pt h]! = R.pt (F h)) ∧
    (∀ F ∈ gMaps γ x, ∃ f ∈ a :: (List.range 7).map (fun j => M.conjArr (M.g j)),
      ∀ h, f[R.pt h]! = R.pt (F h)) := by
  have hc : ∀ j < 7, ∀ h, (M.conjArr (M.g j))[R.pt h]! =
      R.pt ((natFam x j)⁻¹ * h * natFam x j) := by
    intro j hj h
    have e : M.g j = R.pt (natFam x j) := by
      rw [show natFam x j = x ⟨j, hj⟩ from natFam_fin x ⟨j, hj⟩]
      exact (hx ⟨j, hj⟩).symm
    rw [e]
    exact R.conjArr_spec _ _
  constructor
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨γ, List.mem_cons_self, ha⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, hj, rfl⟩),
        hc j (List.mem_range.1 hj)⟩
  · intro F hF
    rcases List.mem_cons.1 hF with rfl | hF
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hF
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨j, hj, rfl⟩),
        hc j (List.mem_range.1 hj)⟩

end Rep

theorem gTable_fix_zero {α : ℕ} (x : Fin 7 → H) (γ : H →* H) (hγ : GTable α γ x) :
    γ (x 0) = x 0 := by
  have hmem : ((0 : ℕ), vt) ∈ gRels α := by
    unfold gRels
    split_ifs <;> exact List.mem_cons_self
  have h0 := hγ _ hmem
  have e : natFam x 0 = x 0 := natFam_fin x 0
  change γ (natFam x 0) = natFam x 0 at h0
  rwa [e] at h0

theorem gAutOK_facts {α : ℕ} (hα : α ≤ 2) (h : gAutOK α = true) (x : Fin 7 → H)
    (R : Rep (mkReg α) H) (hx : ∀ j : Fin 7, R.pt (x j) = (mkReg α).g j.val)
    (hT : TreeSpec (mkReg α)) (γ : H →* H) (hγ : GTable α γ x) : GFacts α γ x := by
  unfold gAutOK at h
  generalize mkReg α = M at h R hx hT
  have e0 : M.g 0 = R.pt (x 0) := (hx 0).symm
  have e1 : M.g 1 = R.pt (x 1) := (hx 1).symm
  have e2 : M.g 2 = R.pt (x 2) := (hx 2).symm
  simp only [Bool.and_eq_true, beq_iff_eq, e0, e1, e2, ← R.pt_mul, ← R.pt_pow] at h
  obtain ⟨-, ha⟩ := R.gAut_spec x hx hT (by omega) γ hγ
  generalize M.autMap (M.gImgs α) = a at h ha
  obtain ⟨⟨⟨⟨⟨-, hBij⟩, hOrd⟩, hCnt⟩, hDst⟩, hRest⟩ := h
  have := R.finite
  have hsurj := (R.isBij_iff γ ha).1 hBij
  have hbij : Function.Bijective γ := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  have hp := (R.permOrd_eq_iff γ ha (k := 3) ⟨by norm_num, by norm_num⟩).1 hOrd
  have hord3 : (∀ h, γ (γ (γ h)) = h) ∧ ∃ h, γ h ≠ h :=
    ⟨fun h => hp.1 h, hp.2 1 one_pos (by norm_num)⟩
  have hff := R.fixedFree_of_count (x 0) γ (gTable_fix_zero x γ hγ) ha hCnt
  have hDset := R.set_closure_pts3 (x 0) (x 1) (x 2)
  have hDst' := R.stable_of_elems_all (R.closure_size (by simp [R.pt_lt])) γ ha hDst
  have hD : ∀ y ∈ sD x, γ y ∈ sD x := by
    intro y hy
    have := hDst' y (by rw [hDset]; exact hy)
    rw [hDset] at this
    exact this
  obtain ⟨h1, h2⟩ := R.gMaps_corr x hx γ ha
  by_cases hα2 : α = 2
  · subst hα2
    rw [ite_eq_left rfl] at hRest
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hRest
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hq1⟩, hp3⟩, hp1⟩, hp2⟩, ht3⟩, ht1⟩, ht2⟩, h7⟩ := hRest
    have hnd7 := nodup_of_length_eraseDups h7
    refine ⟨hbij, hord3, hff, hD, fun _ => ⟨?_, ?_, ?_, List.Nodup.of_map R.pt hnd7⟩,
      fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · refine R.isOrbitOf_of_points h1 h2 (x 0) (T := [R.pt (x 0)]) (List.nodup_singleton _)
        ?_ (by rw [hq1]; rfl) fun h => ?_
      · intro z hz
        rw [List.mem_singleton] at hz
        rw [hz]
        exact R.mem_orbitOf_self h1 _
      · simp only [Set.mem_singleton_iff, List.mem_singleton, R.pt_inj.eq_iff]
    · refine R.isOrbitOf_of_points h1 h2 (x 1)
        (T := [R.pt (x 1), R.pt (x 0 * x 1 * x 2), R.pt (x 0 * x 2)])
        (hnd7.sublist (.cons_cons _ (.cons_cons _ (.cons_cons _ (List.nil_sublist _)))))
        ?_ (by rw [hp3]; rfl) fun h => ?_
      · intro z hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact R.mem_orbitOf_self h1 _
        · exact hp1
        · exact hp2
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.mem_nil_iff,
          or_false, R.pt_inj.eq_iff]
    · refine R.isOrbitOf_of_points h1 h2 (x 2)
        (T := [R.pt (x 2), R.pt (x 0 * x 1), R.pt (x 1 * x 2)])
        (hnd7.sublist (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _
          (List.nil_sublist _))))))))
        ?_ (by rw [ht3]; rfl) fun h => ?_
      · intro z hz
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact R.mem_orbitOf_self h1 _
        · exact ht1
        · exact ht2
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.mem_nil_iff,
          or_false, R.pt_inj.eq_iff]
  · rw [ite_eq_right hα2] at hRest
    simp only [Bool.and_eq_true, beq_iff_eq] at hRest
    obtain ⟨⟨⟨hV8, hVst⟩, hl6⟩, hall⟩ := hRest
    have hVset := R.set_closure_pts3 (x 0 ^ 2) (x 1) (x 0 * x 2)
    have hVsz : (M.closure [R.pt (x 0 ^ 2), R.pt (x 1), R.pt (x 0 * x 2)]).size = M.N :=
      R.closure_size (by simp [R.pt_lt])
    have hVst' := R.stable_of_elems_all hVsz γ ha hVst
    have hV : ∀ y ∈ sV x, γ y ∈ sV x := by
      intro y hy
      have := hVst' y (by rw [hVset]; exact hy)
      rw [hVset] at this
      exact this
    refine ⟨hbij, hord3, hff, hD, fun h => absurd h hα2, fun _ => hV, fun _ => ?_⟩
    have hVc : (sV x : Set H).ncard = 8 := by
      rw [R.card_eq_ncard hVsz, hVset] at hV8
      exact hV8
    refine R.isOrbitOf_of_subset h1 h2 (x 1) ?_ ?_
    · rintro h ⟨hhV, hn⟩
      have hhV' : h ∈ R.set (M.closure [R.pt (x 0 ^ 2), R.pt (x 1), R.pt (x 0 * x 2)]) := by
        rw [hVset]
        exact hhV
      have := List.all_eq_true.1 hall (R.pt h)
        ((R.mem_elems_iff_exists_pt hVsz).2 ⟨h, rfl, hhV'⟩)
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
      rcases this with (h0 | hq) | hL
      · exact absurd (Or.inl (R.pt_inj (h0.trans R.pt_one.symm))) hn
      · exact absurd (Or.inr (R.pt_inj hq)) hn
      · exact hL
    · have h2le : ({1, x 0 ^ 2} : Set H).ncard ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
      have := Set.ncard_le_ncard_sdiff_add_ncard (sV x : Set H) {1, x 0 ^ 2}
      omega

end CFSG.OddStandard.ChengHeld.Model
