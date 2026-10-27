module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8TwoBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8TwoCert
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open Subgroup

variable {K : Type} [Field K]

structure ZxData (F Δ : List (Fin Tag.E8.rank → ℤ))
    (kills : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)))
    (ws : List (List (Fin Tag.E8.rank))) : Prop where
  nodup : (F ++ kills.map Prod.fst).Nodup
  roots : ∀ α ∈ F ++ kills.map Prod.fst, IsRoot .E8 α ∧ 15 ≤ height α
  orth : F.Pairwise fun σ σ' => iform σ σ' = 0
  cover : ∀ γ, IsRoot .E8 γ → 0 < height γ → γ ∉ F ++ kills.map Prod.fst →
    ∃ δ ∈ Δ, IsRoot .E8 (γ + δ)
  deltas : ∀ δ ∈ Δ, IsRoot .E8 δ ∧ 0 < height δ ∧ ∀ σ ∈ F, 0 ≤ iform δ σ
  killers : ∀ p ∈ kills, IsRoot .E8 p.2 ∧ (IsRoot .E8 (p.1 - p.2) ∧ 0 < height (p.1 - p.2)) ∧
    p.1 - p.2 ∉ F ++ kills.map Prod.fst ∧ (-p.2 ≠ p.1 ∧ -p.2 ≠ -p.1) ∧
    (∀ α ∈ F ++ kills.map Prod.fst, α ≠ p.1 → -p.2 ≠ α ∧ -p.2 ≠ -α ∧ ¬ IsRoot .E8 (-p.2 + α)) ∧
    ∀ σ ∈ F, 0 ≤ iform (-p.2) σ
  swaps : ∀ ω ∈ ws, (F.map fun σ => ω.foldr (reflect .E8) σ).Perm F ∧
    ∀ σ ∈ F, ω.foldr (reflect .E8) (ω.foldr (reflect .E8) σ) = σ
  chain : List.zipWith (fun ω σ => ω.foldr (reflect .E8) σ) ws F = F.tail

theorem symmetrizedCartan_e8 : Tag.E8.symmetrizedCartan = Tag.E8.cartan :=
  Matrix.one_mul _

theorem zipWith_ofFn_e8 {n : ℕ} (f : ℤ → ℤ → ℤ) (a b : Fin n → ℤ) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn fun i => f (a i) (b i) :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by simp

theorem iform_eq_e8Dot (γ δ : Fin Tag.E8.rank → ℤ) : iform γ δ = e8Dot γ δ := by
  rw [e8Dot, e8CartanList, zipWith_ofFn_e8, List.sum_ofFn, iform, symmetrizedCartan_e8]
  simp only [Finset.mul_sum, mul_assoc]

theorem getD_ofFn_e8 (v : Fin Tag.E8.rank → ℤ) (k : Fin Tag.E8.rank) :
    (List.ofFn v).getD k 0 = v k := by
  simp

theorem ofFn_reflect_e8 (i : Fin Tag.E8.rank) (v : Fin Tag.E8.rank → ℤ) :
    List.ofFn (reflect .E8 i v) = e8ReflectL i (List.ofFn v) := by
  rw [e8ReflectL]
  congr 1
  funext k
  simp only [getD_ofFn_e8, reflect, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem ofFn_foldr_reflect_e8 (ω : List (Fin Tag.E8.rank)) (σ : Fin Tag.E8.rank → ℤ) :
    List.ofFn (ω.foldr (reflect .E8) σ) = ω.foldr e8ReflectL (List.ofFn σ) := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [List.foldr_cons, List.foldr_cons, ofFn_reflect_e8, ih]

theorem ZxData.of_checkB
    {F : List (Fin Tag.E8.rank → ℤ)} {Δc : List ((Fin Tag.E8.rank → ℤ) × List ℤ)}
    {kills : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ))}
    {ws : List (List (Fin Tag.E8.rank))} (h : zxCheckB F Δc kills ws = true) :
    ZxData F (Δc.map Prod.fst) kills ws := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  simp only [zxCheckB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hr : ∀ v : Fin Tag.E8.rank → ℤ, List.ofFn v ∈ Tag.artifactRoots .E8 → IsRoot .E8 v :=
    fun v hv => isRoot_iff_mem_artifactRoots.2 hv
  refine ⟨h1, fun α hα => ⟨hr _ (h2 α hα).1, (h2 α hα).2⟩,
    h3.imp fun h => by rw [iform_eq_e8Dot]; exact h, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ hγp hγL
    rcases h4 _ (isRoot_iff_mem_artifactRoots.1 hγ) with (hs | hm) | ⟨p, hp, hpr⟩
    · rw [List.sum_ofFn] at hs
      exact absurd hs (not_le.2 hγp)
    · obtain ⟨α, hα, he⟩ := List.mem_map.1 hm
      rw [List.ofFn_injective he] at hα
      exact absurd hα hγL
    · obtain ⟨⟨⟨e, hpr'⟩, -⟩, -⟩ := h5 p hp
      have hf : iform γ p.1 = -1 := by
        rw [iform_eq_e8Dot, e8Dot, ← e]
        exact hpr
      exact ⟨p.1, List.mem_map_of_mem hp, (classD4_isRoot_add hτ hγ (hr _ hpr') hf).1⟩
  · intro δ hδ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hδ
    obtain ⟨⟨⟨e, hpr⟩, hpos⟩, hF⟩ := h5 p hp
    refine ⟨hr _ hpr, hpos, fun σ hσ => ?_⟩
    rw [iform_comm, iform_eq_e8Dot, e8Dot, ← e]
    exact hF σ hσ
  · intro p hp
    obtain ⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := h6 p hp
    refine ⟨hr _ k1, ⟨hr _ k2, k3⟩, k4, ⟨k5, k6⟩, fun α hα hne => ?_, fun σ hσ => ?_⟩
    · rcases k7 α hα with h | ⟨⟨a1, a2⟩, a3⟩
      · exact absurd h hne
      · exact ⟨a1, a2, fun hroot => a3 (isRoot_iff_mem_artifactRoots.1 hroot)⟩
    · rw [iform_eq_e8Dot]
      exact k8 σ hσ
  · intro ω hω
    obtain ⟨hperm, hinv⟩ := h7 ω hω
    refine ⟨?_, fun σ hσ => List.ofFn_injective ?_⟩
    · rw [← List.map_perm_map_iff List.ofFn_injective, List.map_map]
      have e : (List.ofFn ∘ fun σ => ω.foldr (reflect .E8) σ) =
          fun σ => ω.foldr e8ReflectL (List.ofFn σ) :=
        funext fun σ => ofFn_foldr_reflect_e8 ω σ
      rw [e]
      exact hperm
    · rw [ofFn_foldr_reflect_e8, ofFn_foldr_reflect_e8]
      exact hinv σ hσ
  · apply List.map_injective_iff.2 List.ofFn_injective
    rw [List.map_zipWith]
    simp only [ofFn_foldr_reflect_e8]
    exact h8

theorem rootSpan_le_of_subset_e8
    {τ : Tag} {R : Type} [CommRing R] {S T : Set (Fin τ.rank → ℤ)} (h : S ⊆ T) :
    rootSpan τ R S ≤ rootSpan τ R T :=
  biSup_mono h

theorem mul_comm_of_mem_closure_odd_e8 {G : Type*} [Group G] {t x : G}
    (hx : x ∈ closure {c : G | c * t = t * c ∧ Odd (orderOf c)}) : x * t = t * x := by
  have hle : closure {c : G | c * t = t * c ∧ Odd (orderOf c)} ≤ centralizer {t} :=
    (closure_le _).2 fun c hc => mem_centralizer_singleton_iff.2 hc.1
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem pinnedX_comm_e8FramePt
    {F : List (Fin Tag.E8.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E8 σ) {δ : Fin Tag.E8.rank → ℤ}
    (hδ : IsRoot .E8 δ) (hδF : ∀ σ ∈ F, 0 ≤ iform δ σ) (a : K) :
    (⟨pinnedX .E8 K δ a, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E8 K) * e8FramePt K F =
      e8FramePt K F * ⟨pinnedX .E8 K δ a, pinnedX_mem_adjointGroup _ _⟩ := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  apply Subtype.ext
  show pinnedX .E8 K δ a * (F.map fun σ => pinnedX .E8 K σ 1).prod =
    (F.map fun σ => pinnedX .E8 K σ 1).prod * pinnedX .E8 K δ a
  exact (Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
    exact classD4_commute_pinnedX hτ hδ (hF σ hσ) (hδF σ hσ) a 1).eq

theorem eq_one_or_eq_of_mem_zx_e8
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) {F Δ : List (Fin Tag.E8.rank → ℤ)}
    {kills : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ))}
    {ws : List (List (Fin Tag.E8.rank))} (hD : ZxData F Δ kills ws) {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail .E8 h)
    (hU : ∀ x : adjointGroup .E8 K, (x : ModGL .E8 K) ∈ heightSeries .E8 K h →
      x * e8FramePt K F = e8FramePt K F * x)
    {w : adjointGroup .E8 K} (hw : w ∈ Exc.zx (e8FramePt K F)) :
    w = 1 ∨ w = e8FramePt K F := by
  classical
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  have hLr : ∀ α ∈ F ++ kills.map Prod.fst, IsRoot .E8 α ∧ 0 < height α := fun α hα =>
    ⟨(hD.roots α hα).1, by linarith [(hD.roots α hα).2]⟩
  have hFr : ∀ σ ∈ F, IsRoot .E8 σ := fun σ hσ => (hD.roots σ (List.mem_append_left _ hσ)).1
  have hw' : w ∈ Exc.cent (e8FramePt K F) ∧
      (∀ c ∈ Exc.cent (e8FramePt K F), w * c = c * w) ∧ w * w = 1 := hw
  have hcoe : ∀ c : adjointGroup .E8 K, c * e8FramePt K F = e8FramePt K F * c →
      (w : ModGL .E8 K) * c = c * w := fun c hc =>
    congrArg Subtype.val (hw'.2.1 c (mem_centralizer_singleton_iff.2 hc))
  have hwB : (w : ModGL .E8 K) ∈ borelGroup .E8 K := by
    refine mem_borelGroup_of_normalizes_heightSeries h1 hd w.2 fun h' hh x hx => ?_
    have hx' : x ∈ heightSeries .E8 K h := heightSeries_antitone_annih hh hx
    have hxC : x ∈ adjointGroup .E8 K :=
      posUnipotent_le_adjointGroup (heightSeries_le_posUnipotent h hx')
    have e : (w : ModGL .E8 K) * x = x * w := hcoe ⟨x, hxC⟩ (hU ⟨x, hxC⟩ hx')
    rw [e, mul_inv_cancel_right]
    exact hx
  have hwU := mem_posUnipotent_of_mem_borelGroup_two hK hwB
  have hΔ : ∀ δ ∈ {δ | δ ∈ Δ}, IsRoot .E8 δ ∧ 0 < height δ := fun δ hδ =>
    ⟨(hD.deltas δ hδ).1, (hD.deltas δ hδ).2.1⟩
  have hwΔ : ∀ δ ∈ {δ | δ ∈ Δ}, (w : ModGL .E8 K) * pinnedX .E8 K δ 1 =
      pinnedX .E8 K δ 1 * w := fun δ hδ =>
    hcoe (e8RootElt δ) (pinnedX_comm_e8FramePt hFr (hD.deltas δ hδ).1 (hD.deltas δ hδ).2.2 1)
  have hwL : (w : ModGL .E8 K) ∈ rootSpan .E8 K {γ | γ ∈ F ++ kills.map Prod.fst} := by
    refine rootSpan_le_of_subset_e8 (fun γ hγ => ?_)
      (mem_rootSpan_annRoots_of_commute hτ hΔ hwU hwΔ)
    rw [mem_annRoots_iff hΔ] at hγ
    by_contra hn
    obtain ⟨δ, hδ, hr⟩ := hD.cover γ hγ.1 hγ.2.1 hn
    exact hγ.2.2 δ hδ hr
  obtain ⟨c, hc⟩ := exists_eq_prod_of_mem_rootSpan_e8 hD.nodup hLr
    (fun α hα => (hD.roots α hα).2) hwL
  have hkill : ∀ p ∈ kills, c p.1 = 0 := by
    intro p hp
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hD.killers p hp
    have hcomm := hcoe (e8RootElt (-p.2)) (pinnedX_comm_e8FramePt hFr (IsRoot.neg k1) k6 1)
    rw [hc] at hcomm
    exact coeff_eq_zero_of_commute_neg_mem_e8 hD.nodup hLr
      (List.mem_append_right _ (List.mem_map_of_mem hp)) k1 k2 k3 k4 k5 c hcomm.symm
  have hwF : (w : ModGL .E8 K) = (F.map fun σ => pinnedX .E8 K σ (c σ)).prod := by
    have hN : ((kills.map Prod.fst).map fun α => pinnedX .E8 K α (c α)).prod = 1 :=
      List.prod_eq_one fun x hx => by
        obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
        rw [hkill p hp, pinnedX_zero]
    rw [hc, List.map_append, List.prod_append, hN, mul_one]
  have hswap : ∀ ω ∈ ws, ∀ σ ∈ F, c (ω.foldr (reflect .E8) σ) = c σ := by
    intro ω hω
    obtain ⟨hperm, hinv⟩ := hD.swaps ω hω
    have hn : e8WordElt ω * e8FramePt K F = e8FramePt K F * e8WordElt ω :=
      Subtype.ext (wordProd_comm_framePt_e8 hFr hD.orth ω hperm)
    have hcomm := hcoe (e8WordElt ω) hn
    rw [hwF] at hcomm
    exact coeff_smul_eq_of_commute_word_e8 (List.nodup_append.1 hD.nodup).1
      (fun σ hσ => hLr σ (List.mem_append_left _ hσ)) hD.orth ω hperm hinv c hcomm.symm
  have hall := coeff_eq_coeff_of_zipWith_eq_tail
    (fun (ω : List (Fin Tag.E8.rank)) σ => ω.foldr (reflect .E8) σ) c hD.chain hswap
  rcases eq_one_or_eq_of_coeffs_e8 hK c hall with h0 | h0
  · exact Or.inl (Subtype.ext (by rw [hwF, h0]; rfl))
  · exact Or.inr (Subtype.ext (by rw [hwF, h0]; rfl))

theorem card_zx_le_two_of_forall {C : Type*} [Group C] {x : C}
    (h : ∀ w ∈ Exc.zx x, w = 1 ∨ w = x) : Nat.card (Exc.zx x) ≤ 2 := by
  have hsub : ((Exc.zx x : Subgroup C) : Set C) ⊆ {1, x} := fun w hw => h w hw
  calc Nat.card (Exc.zx x) = ((Exc.zx x : Subgroup C) : Set C).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, x} : Set C).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

theorem card_zx_le_two_e8_x
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e8FramePt K [highRoot .E8])) ≤ 2 := by
  have hτ : Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 := Or.inr (Or.inr rfl)
  have ht : ((e8FramePt K [highRoot .E8] : adjointGroup .E8 K) : ModGL .E8 K) =
      pinnedX .E8 K (highRoot .E8) 1 := by
    simp [e8FramePt]
  refine card_zx_le_two_of_forall fun w hw => eq_one_or_eq_of_mem_zx_e8 hK
    (ZxData.of_checkB e8ZxX_check : ZxData [highRoot .E8] _ _ _) le_rfl
    (simpleDiffTail_one .E8) (fun x hx => ?_) hw
  rw [heightSeries_one] at hx
  exact mul_comm_of_mem_closure_odd_e8 (posUnipotent_le_closure_odd_E_two hτ hK ht hx)

theorem card_zx_le_two_e8_y
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e8FramePt K oddDerivE8YFrame)) ≤ 2 :=
  card_zx_le_two_of_forall fun _ hw => eq_one_or_eq_of_mem_zx_e8 hK
    (ZxData.of_checkB e8ZxY_check : ZxData oddDerivE8YFrame _ _ _) (by norm_num)
    simpleDiffTail_E8_7
    (fun x hx => mul_comm_of_mem_closure_odd_e8 (heightSeries_le_closure_odd_E8_y
      (t := e8FramePt K oddDerivE8YFrame) rfl x hx)) hw

theorem card_zx_le_two_e8_z
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e8FramePt K oddDerivE8ZFrame)) ≤ 2 :=
  card_zx_le_two_of_forall fun _ hw => eq_one_or_eq_of_mem_zx_e8 hK
    (ZxData.of_checkB e8ZxZ_check : ZxData oddDerivE8ZFrame _ _ _) (by norm_num)
    simpleDiffTail_E8_11
    (fun x hx => mul_comm_of_mem_closure_odd_e8 (heightSeries_le_closure_odd_E8_z
      (t := e8FramePt K oddDerivE8ZFrame) rfl x hx)) hw

theorem card_zx_le_two_e8_u
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e8FramePt K oddDerivE8UFrame)) ≤ 2 :=
  card_zx_le_two_of_forall fun _ hw => eq_one_or_eq_of_mem_zx_e8 hK
    (ZxData.of_checkB e8ZxU_check : ZxData oddDerivE8UFrame _ _ _) (by norm_num)
    simpleDiffTail_E8_13
    (fun x hx => mul_comm_of_mem_closure_odd_e8 (heightSeries_le_closure_odd_E8_u
      (t := e8FramePt K oddDerivE8UFrame) rfl x hx)) hw

theorem card_zx_e8Reps_two
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ x ∈ e8Reps K, Nat.card (Exc.zx x) < 4 := by
  obtain ⟨cX, cY, cZ, cU⟩ := isConj_e8FramePt_inner (K := K)
  have key : ∀ t x : adjointGroup .E8 K, IsConj t x → Nat.card (Exc.zx t) ≤ 2 →
      Nat.card (Exc.zx x) < 4 := by
    intro t x htx ht
    obtain ⟨g, hg⟩ := isConj_iff.1 htx
    rw [← hg, Exc.card_zx_conj]
    omega
  intro x hx
  simp only [e8Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact key _ _ cX (card_zx_le_two_e8_x hK)
  · exact key _ _ cY (card_zx_le_two_e8_y hK)
  · exact key _ _ cZ (card_zx_le_two_e8_z hK)
  · exact key _ _ cU (card_zx_le_two_e8_u hK)

end CFSG.ComponentClassification.RankTwoExceptional.E8
