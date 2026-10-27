module

public import Certificates.Data.Kernel.HSMK
public import CFSG.Certificates.Kernel.WEMKSound
import all CFSG.Certificates.Kernel.WEMKSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMaxAbstract

public section

namespace CFSG.StandardType.ZS.HSMK

open Certificates.ExcModel Certificates.WEMK Certificates.HSMK Certificates.TWLK CFSG.StandardType.ZS
  CFSG.StandardType.ZS.WEMK
open scoped Matrix

@[expose] def uset (n : ℕ) (G : List KPair) : Set (owEm_GL n) := {u | ∃ q ∈ G, (u : Mat n) = toM n (mat n q)}

theorem isOneN_sound {n : ℕ} {A : NMat} (h : isOneN n A = true) : toM n A = 1 := by
  rw [isOneN, decide_eq_true_eq] at h
  rw [h, idN_spec]

theorem npowN_length (n : ℕ) (A : NMat) : ∀ k, (npowN n A k).length = n
  | 0 => by simp [npowN, idN]
  | k + 1 => by simp [npowN, nmul, npowN_length n A k]

theorem toM_npowN (n : ℕ) (A : NMat) (hA : WF n A) : ∀ k, toM n (npowN n A k) = toM n A ^ k
  | 0 => by rw [npowN, idN_spec, pow_zero]
  | k + 1 => by rw [npowN, toM_nmul n _ _ (npowN_length n A k) hA, toM_npowN n A hA k, pow_succ]

theorem getD_mem_of_lt {α : Type*} {l : List α} {d : α} {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem rel_sound {n : ℕ} {T : List NMat} {E : List (List ℕ)} (h : kRel n T E = true) (hT : ∀ s ∈ T, WF n s) :
    ∀ i < T.length, ∀ j < T.length,
      (toM n (T.getD i []) * toM n (T.getD j [])) ^ ((E.getD i []).getD j 0) = 1 := by
  intro i hi j hj
  simp only [kRel, List.all_eq_true, List.mem_range] at h
  have hmi := hT _ (getD_mem_of_lt (d := []) hi)
  have hmj := hT _ (getD_mem_of_lt (d := []) hj)
  have hA := wf_nmul n _ _ hmi.1 hmj
  rw [← toM_nmul n _ _ hmi.1 hmj, ← toM_npowN n _ hA.1, isOneN_sound (h i hi j hj)]

theorem extra_sound {n : ℕ} {T : List NMat} (h : kExtra n T = true) (hT : ∀ s ∈ T, WF n s) (h3 : 3 < T.length) :
    (toM n (T.getD 2 []) * toM n (T.getD 1 []) * toM n (T.getD 2 []) * toM n (T.getD 3 [])) ^ 3 = 1 := by
  have m1 := hT _ (getD_mem_of_lt (d := []) (show 1 < T.length by omega))
  have m2 := hT _ (getD_mem_of_lt (d := []) (show 2 < T.length by omega))
  have m3 := hT _ (getD_mem_of_lt (d := []) h3)
  have r1 := wf_nmul n _ _ m2.1 m1
  have r2 := wf_nmul n _ _ r1.1.1 m2
  have r3 := wf_nmul n _ _ r2.1.1 m3
  rw [← toM_nmul n _ _ m2.1 m1, ← toM_nmul n _ _ r1.1.1 m2, ← toM_nmul n _ _ r2.1.1 m3, ← toM_npowN n _ r3.1,
    isOneN_sound h]

theorem gen_wf {n : ℕ} {T : List NMat} {V : List KPair} {tab : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : kGen n T V tab par = true) : ∀ s ∈ T, WF n s := by
  simp only [kGen, Bool.and_eq_true] at h
  intro s hs
  have w := List.all_eq_true.mp h.1.1.1.1.1 s hs
  simp only [wfM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at w
  exact ⟨w.1, w.2⟩

theorem gen_sound {n : ℕ} {T : List NMat} {V : List KPair} {tab : List (List ℕ)} {par : List (ℕ × ℕ)}
    (h : kGen n T V tab par = true) (hT0 : 0 < T.length) (gens : Set (Mat n))
    (hTg : ∀ s < T.length, toM n (T.getD s []) ∈ gens) (hgX : ∀ g ∈ gens, ∃ i < V.length, Lm n V i = g) :
    (∀ s ∈ T, WF n s ∧ toM n s * toM n s = 1) ∧
      glClosure gens = Subgroup.closure {g : owEm_GL n | ∃ s < T.length, (g : Mat n) = toM n (T.getD s [])} ∧
      ∀ q ∈ V, ∃ u ∈ glClosure gens, (u : Mat n) = toM n (mat n q) := by
  simp only [kGen, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hwf, hinv⟩, hV0⟩, h0⟩, htab⟩, hpar⟩ := h
  rw [decide_eq_true_eq] at hV0 h0
  have hSf : ∀ s ∈ T, WF n s ∧ toM n s * toM n s = 1 := by
    intro s hs
    have w := List.all_eq_true.mp hwf s hs
    simp only [wfM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at w
    have i := List.all_eq_true.mp hinv s hs
    simp only [isOneN, decide_eq_true_eq] at i
    refine ⟨⟨w.1, w.2⟩, ?_⟩
    rw [← toM_nmul n s s w.1 ⟨w.1, w.2⟩, i, idN_spec]
  have hSi : ∀ s < T.length, toM n (T.getD s []) * toM n (T.getD s []) = 1 := fun s hs =>
    (hSf _ (getD_mem_of_lt hs)).2
  let gu : ℕ → owEm_GL n := fun s => if hs : s < T.length then owEm_unit _ (hSi s hs) else 1
  let H : Subgroup (owEm_GL n) := Subgroup.closure {g : owEm_GL n | ∃ s < T.length, (g : Mat n) = toM n (T.getD s [])}
  have hguv : ∀ s < T.length, (gu s : Mat n) = toM n (T.getD s []) := fun s hs => by simp [gu, hs, owEm_unit]
  have hgu : ∀ s < T.length, gu s ∈ H ∧ (gu s)⁻¹ = gu s := fun s hs =>
    ⟨Subgroup.subset_closure ⟨s, hs, hguv s hs⟩, by simp only [gu, hs, dif_pos, owEm_unit_inv]⟩
  have htab' : ∀ i < V.length, ∀ s < T.length, (tab.getD i []).getD s 0 < V.length ∧
      (gu s : Mat n) * Lm n V i * (gu s : Mat n) = Lm n V ((tab.getD i []).getD s 0) := by
    intro i hi s hs
    rw [hguv s hs]
    exact tab_sound htab hSf hi hs
  let r0 := gu 0
  have hr0 : (r0 : Mat n) = Lm n V 0 := by
    change (gu 0 : Mat n) = _
    rw [hguv 0 hT0, Lm, h0]
  have hr0H : r0 ∈ H := (hgu 0 hT0).1
  have hconj := par_conj H gu T.length V.length (Lm n V) tab par r0 hr0 hgu htab' (par_sound hpar)
  have hM : glClosure gens = H := by
    apply le_antisymm
    · unfold glClosure
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨i, hi, hig⟩ := hgX _ hg
      obtain ⟨m, hm, e⟩ := hconj i hi
      have : g = m * r0 * m⁻¹ := Units.ext (by rw [e, hig])
      rw [this]
      exact mul_mem (mul_mem hm hr0H) (inv_mem hm)
    · unfold glClosure
      rw [Subgroup.closure_le]
      rintro g ⟨s, hs, hg⟩
      apply Subgroup.subset_closure
      change (g : Mat n) ∈ gens
      rw [hg]
      exact hTg s hs
  refine ⟨hSf, hM, fun q hq => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  obtain ⟨m, hm, e⟩ := hconj i hi
  refine ⟨m * r0 * m⁻¹, by rw [hM]; exact mul_mem (mul_mem hm hr0H) (inv_mem hm), ?_⟩
  rw [e, Lm, List.getD_eq_getElem _ _ hi]

@[instance_reducible]
private def hsmk_mulAction {n : ℕ} : MulAction (owEm_GL n) (Fin n → ZMod 13) :=
  MulAction.compHom _ (Units.coeHom (Mat n))

attribute [local instance] hsmk_mulAction

theorem pword_sound {n : ℕ} (G : List KPair) (hG : ∀ q ∈ G, ∃ u : owEm_GL n, (u : Mat n) = toM n (mat n q)) :
    ∀ (w v : List ℕ), (∀ g ∈ w, g < G.length) →
      ∃ m ∈ Subgroup.closure (uset n G), (m : Mat n) *ᵥ vecN n v = vecN n (pword n G v w)
  | [], v, _ => ⟨1, one_mem _, by simp [pword]⟩
  | g :: w, v, hw => by
    have hg := hw g (by simp)
    have hq : G.getD g kP0 ∈ G := getD_mem_of_lt hg
    obtain ⟨u, hu⟩ := hG _ hq
    obtain ⟨m, hm, e⟩ := pword_sound G hG w (nmv (mat n (G.getD g kP0)) v) (fun g' h' => hw g' (by simp [h']))
    refine ⟨m * u, mul_mem hm (Subgroup.subset_closure ⟨_, hq, hu⟩), ?_⟩
    have hp : pword n G v (g :: w) = pword n G (nmv (mat n (G.getD g kP0)) v) w := rfl
    rw [hp, ← e, vecN_nmv n _ (wf_mat n _).1, Units.val_mul, ← Matrix.mulVec_mulVec, hu]

theorem orb_sound {n : ℕ} (G : List KPair) (hG : ∀ q ∈ G, ∃ u : owEm_GL n, (u : Mat n) = toM n (mat n q))
    (b : List ℕ) : ∀ (R : List (List ℕ × List ℕ)) (u : List ℕ), kOrb n G u R = true →
      (∃ m ∈ Subgroup.closure (uset n G), (m : Mat n) *ᵥ vecN n b = vecN n u) →
      ∀ r ∈ R, wfV n r.2 = true ∧ ∃ m ∈ Subgroup.closure (uset n G), (m : Mat n) *ᵥ vecN n b = vecN n r.2
  | [], _, _, _ => by simp
  | r :: rs, u, h, ⟨m, hm, e⟩ => by
    simp only [kOrb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hw, hwf⟩, hpw⟩, hrest⟩ := h
    obtain ⟨m', hm', e'⟩ := pword_sound G hG r.1 u hw
    have hr : ∃ m ∈ Subgroup.closure (uset n G), (m : Mat n) *ᵥ vecN n b = vecN n r.2 :=
      ⟨m' * m, mul_mem hm' hm, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, e, e', hpw]⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hwf, hr⟩
    · exact orb_sound G hG b rs r.2 hrest hr x hx

theorem vecN_inj {n : ℕ} {v w : List ℕ} (hv : wfV n v = true) (hw : wfV n w = true) (h : vecN n v = vecN n w) :
    v = w := by
  simp only [wfV, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv hw
  apply List.ext_getElem (by rw [hv.1, hw.1])
  intro i hi hi'
  have hin : i < n := hv.1 ▸ hi
  have e := congrFun h ⟨i, hin⟩
  simp only [vecN] at e
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  have := congrArg ZMod.val e
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (hv.2 _ (List.getElem_mem hi)),
    Nat.mod_eq_of_lt (hw.2 _ (List.getElem_mem hi'))] at this

theorem closure_fix {n : ℕ} (X : Set (owEm_GL n)) (v : Fin n → ZMod 13) (hX : ∀ u ∈ X, (u : Mat n) *ᵥ v = v) :
    ∀ u ∈ Subgroup.closure X, (u : Mat n) *ᵥ v = v := by
  intro u hu
  have hle : Subgroup.closure X ≤ MulAction.stabilizer (owEm_GL n) v := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact hX x hx
  have := hle hu
  rwa [MulAction.mem_stabilizer_iff] at this

theorem lev_card {n : ℕ} {G : List KPair} {b : List ℕ} {R : List (List ℕ × List ℕ)} (h : kLev n G b R = true)
    (hG : ∀ q ∈ G, ∃ u : owEm_GL n, (u : Mat n) = toM n (mat n q)) (Γ B : Subgroup (owEm_GL n))
    (hΓ : Subgroup.closure (uset n G) ≤ Γ) (hBΓ : B ≤ Γ) (hB : ∀ u ∈ B, (u : Mat n) *ᵥ vecN n b = vecN n b)
    {k : ℕ} (hk : k ≤ Nat.card B) : R.length * k ≤ Nat.card Γ := by
  simp only [kLev, Bool.and_eq_true] at h
  obtain ⟨⟨-, ho⟩, hinc⟩ := h
  have hrec := orb_sound G hG b R b ho ⟨1, one_mem _, by simp⟩
  have hpw := List.pairwise_map.mp (CFSG.StandardType.TWLK.kIncr_pairwise _ hinc)
  have hnd : (R.map fun r => vecN n r.2).Nodup := by
    refine List.pairwise_map.mpr (hpw.imp_of_mem fun {r s} hr hs hlt heq => ?_)
    have := vecN_inj (hrec r hr).1 (hrec s hs).1 heq
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hsub : (((R.map fun r => vecN n r.2).toFinset : Finset (Fin n → ZMod 13)) : Set (Fin n → ZMod 13)) ⊆
      MulAction.orbit Γ (vecN n b) := by
    intro y hy
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    obtain ⟨-, m, hm, e⟩ := hrec r hr
    exact ⟨⟨m, hΓ hm⟩, e⟩
  have hm : R.length ≤ (MulAction.orbit Γ (vecN n b)).ncard :=
    calc R.length = (R.map fun r => vecN n r.2).length := (List.length_map _).symm
      _ = (R.map fun r => vecN n r.2).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = (((R.map fun r => vecN n r.2).toFinset : Finset (Fin n → ZMod 13)) : Set (Fin n → ZMod 13)).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit Γ (vecN n b)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hBa : B ≤ MulAction.stabilizer (owEm_GL n) (vecN n b) := fun u hu => by
    rw [MulAction.mem_stabilizer_iff]
    exact hB u hu
  exact CFSG.AGLEmbedding.KFactProofs.Fi22Five.le_card_of_orbit_stabilizer Γ B (vecN n b) hBΓ hBa hm hk

theorem chain_sound {n : ℕ} : ∀ (L : List (List ℕ × (List (List ℕ × List ℕ) × List KPair))) (G : List KPair),
    kChain n G L = true → (∀ q ∈ G, ∃ u : owEm_GL n, (u : Mat n) = toM n (mat n q)) →
    (L.map fun l => l.2.1.length).prod ≤ Nat.card (Subgroup.closure (uset n G))
  | [], G, _, _ => by
    have hpos : 0 < Nat.card (Subgroup.closure (uset n G)) :=
      Nat.card_pos_iff.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩
    simp only [List.map_nil, List.prod_nil]
    omega
  | l :: ls, G, h, hG => by
    simp only [kChain, Bool.and_eq_true] at h
    obtain ⟨⟨hlev, hsub⟩, hrest⟩ := h
    simp only [kSub, List.all_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hsub
    have hG' : ∀ q ∈ l.2.2, ∃ u : owEm_GL n, (u : Mat n) = toM n (mat n q) := fun q hq => by
      obtain ⟨⟨p, hp, rfl⟩, -⟩ := hsub q hq
      exact hG p hp
    have ih := chain_sound ls l.2.2 hrest hG'
    have hle : Subgroup.closure (uset n l.2.2) ≤ Subgroup.closure (uset n G) := by
      refine Subgroup.closure_mono ?_
      rintro u ⟨q, hq, e⟩
      obtain ⟨⟨p, hp, rfl⟩, -⟩ := hsub q hq
      exact ⟨p, hp, e⟩
    have hfix : ∀ u ∈ Subgroup.closure (uset n l.2.2), (u : Mat n) *ᵥ vecN n l.1 = vecN n l.1 := by
      refine closure_fix _ _ ?_
      rintro u ⟨q, hq, e⟩
      rw [e, ← vecN_nmv n _ (wf_mat n _).1, (hsub q hq).2]
    simp only [List.map_cons, List.prod_cons]
    exact lev_card hlev hG _ _ le_rfl hle hfix ih

theorem tfix_sound {n : ℕ} {T : List NMat} {b : List ℕ} (h : (T.all fun s => decide (nmv s b = b)) = true)
    (hT : ∀ s ∈ T, WF n s) :
    ∀ u ∈ Subgroup.closure {g : owEm_GL n | ∃ s < T.length, (g : Mat n) = toM n (T.getD s [])},
      (u : Mat n) *ᵥ vecN n b = vecN n b := by
  refine closure_fix _ _ ?_
  rintro u ⟨s, hs, e⟩
  have hm : T.getD s [] ∈ T := getD_mem_of_lt hs
  rw [e, ← vecN_nmv n _ (hT _ hm), of_decide_eq_true (List.all_eq_true.mp h _ hm)]

end CFSG.StandardType.ZS.HSMK

end
