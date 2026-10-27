module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7TwoBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7TwoCert
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open Subgroup

variable {K : Type} [Field K]

structure ZxData7 (F Δ : List (Fin Tag.E7.rank → ℤ))
    (kills : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)))
    (ws : List (List (Fin Tag.E7.rank)))
    (links : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) ×
      (Fin Tag.E7.rank → ℤ))) : Prop where
  nodup : (F ++ kills.map Prod.fst).Nodup
  roots : ∀ α ∈ F ++ kills.map Prod.fst, IsRoot .E7 α ∧ 9 ≤ height α
  orth : F.Pairwise fun σ σ' => iform σ σ' = 0
  cover : ∀ γ, IsRoot .E7 γ → 0 < height γ → γ ∉ F ++ kills.map Prod.fst →
    ∃ δ ∈ Δ, IsRoot .E7 (γ + δ)
  deltas : ∀ δ ∈ Δ, IsRoot .E7 δ ∧ 0 < height δ ∧ ∀ σ ∈ F, 0 ≤ iform δ σ
  killers : ∀ p ∈ kills, IsRoot .E7 p.2 ∧ (IsRoot .E7 (p.1 - p.2) ∧ 0 < height (p.1 - p.2)) ∧
    p.1 - p.2 ∉ F ++ kills.map Prod.fst ∧ (-p.2 ≠ p.1 ∧ -p.2 ≠ -p.1) ∧
    (∀ α ∈ F ++ kills.map Prod.fst, α ≠ p.1 → -p.2 ≠ α ∧ -p.2 ≠ -α ∧ ¬ IsRoot .E7 (-p.2 + α)) ∧
    ∀ σ ∈ F, 0 ≤ iform (-p.2) σ
  swaps : ∀ ω ∈ ws, (F.map fun σ => ω.foldr (reflect .E7) σ).Perm F ∧
    ∀ σ ∈ F, ω.foldr (reflect .E7) (ω.foldr (reflect .E7) σ) = σ
  linked : ∀ p ∈ links, IsRoot .E7 p.1 ∧ IsRoot .E7 p.2.1 ∧ p.2.2.1 ∈ F ∧ p.2.2.2 ∈ F ∧
    p.2.2.1 ≠ p.2.2.2 ∧ p.1 + p.2.2.1 = p.2.1 + p.2.2.2 ∧ IsRoot .E7 (p.1 + p.2.2.1) ∧
    0 < height (p.1 + p.2.2.1) ∧ iform p.1 p.2.2.1 = -1 ∧ iform p.2.1 p.2.2.2 = -1 ∧
    (∀ σ ∈ F, σ ≠ p.2.2.1 → 0 ≤ iform p.1 σ) ∧ (∀ σ ∈ F, σ ≠ p.2.2.2 → 0 ≤ iform p.2.1 σ) ∧
    0 ≤ iform p.1 (p.1 + p.2.2.1) ∧ 0 ≤ iform (p.1 + p.2.2.1) p.2.2.1
  chain : List.IsChain (fun σ σ' => (∃ ω ∈ ws, ω.foldr (reflect .E7) σ = σ') ∨
    ∃ p ∈ links, p.2.2.1 = σ ∧ p.2.2.2 = σ') F

theorem symmetrizedCartan_e7 : Tag.E7.symmetrizedCartan = Tag.E7.cartan :=
  Matrix.one_mul _

theorem zipWith_ofFn_e7 {n : ℕ} (f : ℤ → ℤ → ℤ) (a b : Fin n → ℤ) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn fun i => f (a i) (b i) :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by simp

theorem rootSpan_le_of_subset_e7
    {τ : Tag} {R : Type} [CommRing R] {S T : Set (Fin τ.rank → ℤ)} (h : S ⊆ T) :
    rootSpan τ R S ≤ rootSpan τ R T :=
  biSup_mono h

theorem iform_eq_e7Dot (γ δ : Fin Tag.E7.rank → ℤ) : iform γ δ = e7Dot γ δ := by
  rw [e7Dot, e7CartanList, zipWith_ofFn_e7, List.sum_ofFn, iform, symmetrizedCartan_e7]
  simp only [Finset.mul_sum, mul_assoc]

theorem getD_ofFn_e7 (v : Fin Tag.E7.rank → ℤ) (k : Fin Tag.E7.rank) :
    (List.ofFn v).getD k 0 = v k := by
  simp

theorem ofFn_reflect_e7 (i : Fin Tag.E7.rank) (v : Fin Tag.E7.rank → ℤ) :
    List.ofFn (reflect .E7 i v) = e7ReflectL i (List.ofFn v) := by
  rw [e7ReflectL]
  congr 1
  funext k
  simp only [getD_ofFn_e7, reflect, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem ofFn_foldr_reflect_e7 (ω : List (Fin Tag.E7.rank)) (σ : Fin Tag.E7.rank → ℤ) :
    List.ofFn (ω.foldr (reflect .E7) σ) = ω.foldr e7ReflectL (List.ofFn σ) := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [List.foldr_cons, List.foldr_cons, ofFn_reflect_e7, ih]

theorem isChain_of_chainB {α : Type} {r : α → α → Bool} {R : α → α → Prop}
    (h : ∀ a b, r a b = true → R a b) : ∀ l : List α, e7ChainB r l = true → List.IsChain R l
  | [], _ => .nil
  | [a], _ => .singleton a
  | a :: b :: l, hl => by
    rw [e7ChainB, Bool.and_eq_true] at hl
    exact .cons_cons (h a b hl.1) (isChain_of_chainB h (b :: l) hl.2)

theorem eq_of_isChain {α β : Type} {R : α → α → Prop} (c : α → β) {l : List α}
    (h : List.IsChain R l) : (∀ a ∈ l, ∀ b ∈ l, R a b → c a = c b) →
      ∀ a ∈ l, ∀ b ∈ l, c a = c b := by
  induction h with
  | nil => exact fun _ a ha => absurd ha List.not_mem_nil
  | singleton x =>
    intro _ a ha b hb
    rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
  | @cons_cons x y l hr h ih =>
    intro hR a ha b hb
    have ih' := ih fun a' ha' b' hb' =>
      hR a' (List.mem_cons_of_mem _ ha') b' (List.mem_cons_of_mem _ hb')
    have hxy := hR x List.mem_cons_self y (List.mem_cons_of_mem _ List.mem_cons_self) hr
    have key : ∀ z ∈ x :: y :: l, c z = c y := fun z hz => by
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact ih' z hz y List.mem_cons_self
    rw [key a ha, key b hb]

theorem ZxData7.of_check
    {F : List (Fin Tag.E7.rank → ℤ)} {Δc : List ((Fin Tag.E7.rank → ℤ) × List ℤ)}
    {kills : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))}
    {ws : List (List (Fin Tag.E7.rank))}
    {links : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) ×
      (Fin Tag.E7.rank → ℤ))} (h : zxCheckE7 F Δc kills ws links = true) :
    ZxData7 F (Δc.map Prod.fst) kills ws links := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  simp only [zxCheckE7, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have hr : ∀ v : Fin Tag.E7.rank → ℤ, List.ofFn v ∈ Tag.artifactRoots .E7 → IsRoot .E7 v :=
    fun v hv => isRoot_iff_mem_artifactRoots.2 hv
  refine ⟨h1, fun α hα => ⟨hr _ (h2 α hα).1, (h2 α hα).2⟩,
    h3.imp fun h => by rw [iform_eq_e7Dot]; exact h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ hγp hγL
    rcases h4 _ (isRoot_iff_mem_artifactRoots.1 hγ) with (hs | hm) | ⟨p, hp, hpr⟩
    · rw [List.sum_ofFn] at hs
      exact absurd hs (not_le.2 hγp)
    · obtain ⟨α, hα, he⟩ := List.mem_map.1 hm
      rw [List.ofFn_injective he] at hα
      exact absurd hα hγL
    · obtain ⟨⟨⟨e, hpr'⟩, -⟩, -⟩ := h5 p hp
      have hf : iform γ p.1 = -1 := by
        rw [iform_eq_e7Dot, e7Dot, ← e]
        exact hpr
      exact ⟨p.1, List.mem_map_of_mem hp, (classD4_isRoot_add hτ hγ (hr _ hpr') hf).1⟩
  · intro δ hδ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hδ
    obtain ⟨⟨⟨e, hpr⟩, hpos⟩, hF⟩ := h5 p hp
    refine ⟨hr _ hpr, hpos, fun σ hσ => ?_⟩
    rw [iform_comm, iform_eq_e7Dot, e7Dot, ← e]
    exact hF σ hσ
  · intro p hp
    obtain ⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := h6 p hp
    refine ⟨hr _ k1, ⟨hr _ k2, k3⟩, k4, ⟨k5, k6⟩, fun α hα hne => ?_, fun σ hσ => ?_⟩
    · rcases k7 α hα with h | ⟨⟨a1, a2⟩, a3⟩
      · exact absurd h hne
      · exact ⟨a1, a2, fun hroot => a3 (isRoot_iff_mem_artifactRoots.1 hroot)⟩
    · rw [iform_eq_e7Dot]
      exact k8 σ hσ
  · intro ω hω
    obtain ⟨hperm, hinv⟩ := h7 ω hω
    refine ⟨?_, fun σ hσ => List.ofFn_injective ?_⟩
    · rw [← List.map_perm_map_iff List.ofFn_injective, List.map_map]
      have e : (List.ofFn ∘ fun σ => ω.foldr (reflect .E7) σ) =
          fun σ => ω.foldr e7ReflectL (List.ofFn σ) :=
        funext fun σ => ofFn_foldr_reflect_e7 ω σ
      rw [e]
      exact hperm
    · rw [ofFn_foldr_reflect_e7, ofFn_foldr_reflect_e7]
      exact hinv σ hσ
  · intro p hp
    have hl := h8 p hp
    simp only [e7LinkB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hl
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨l1, l2⟩, l3⟩, l4⟩, l5⟩, l6⟩, l7⟩, l8⟩, l9⟩, l10⟩, l11⟩, l12⟩, l13⟩,
      l14⟩ := hl
    refine ⟨hr _ l1, hr _ l2, l3, l4, l5, l6, hr _ l7, l8, by rw [iform_eq_e7Dot]; exact l9,
      by rw [iform_eq_e7Dot]; exact l10, fun σ hσ hne => ?_, fun σ hσ hne => ?_,
      by rw [iform_eq_e7Dot]; exact l13, by rw [iform_eq_e7Dot]; exact l14⟩
    · rcases l11 σ hσ with h | h
      · exact absurd h hne
      · rw [iform_eq_e7Dot]
        exact h
    · rcases l12 σ hσ with h | h
      · exact absurd h hne
      · rw [iform_eq_e7Dot]
        exact h
  · refine isChain_of_chainB (fun σ σ' hb => ?_) F h9
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨ω, hω, he⟩ | ⟨p, hp, he₁, he₂⟩
    · exact Or.inl ⟨ω, hω, List.ofFn_injective (by rw [ofFn_foldr_reflect_e7]; exact he)⟩
    · exact Or.inr ⟨p, hp, he₁, he₂⟩

theorem pinnedX_comm_e7FramePt
    {F : List (Fin Tag.E7.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E7 σ) {δ : Fin Tag.E7.rank → ℤ}
    (hδ : IsRoot .E7 δ) (hδF : ∀ σ ∈ F, 0 ≤ iform δ σ) (a : K) :
    (⟨pinnedX .E7 K δ a, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E7 K) * e7FramePt K F =
      e7FramePt K F * ⟨pinnedX .E7 K δ a, pinnedX_mem_adjointGroup _ _⟩ := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  apply Subtype.ext
  show pinnedX .E7 K δ a * (F.map fun σ => pinnedX .E7 K σ 1).prod =
    (F.map fun σ => pinnedX .E7 K σ 1).prod * pinnedX .E7 K δ a
  exact (Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
    exact classD4_commute_pinnedX hτ hδ (hF σ hσ) (hδF σ hσ) a 1).eq

noncomputable abbrev e7PairElt
    (a b : Fin Tag.E7.rank → ℤ) : adjointGroup .E7 K :=
  e7RootElt a * e7RootElt b

theorem eq_one_or_eq_of_mem_zx_e7
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) {F Δ : List (Fin Tag.E7.rank → ℤ)}
    {kills : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))}
    {ws : List (List (Fin Tag.E7.rank))}
    {links : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) ×
      (Fin Tag.E7.rank → ℤ))} (hD : ZxData7 F Δ kills ws links) {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail .E7 h)
    (hU : ∀ x : adjointGroup .E7 K, (x : ModGL .E7 K) ∈ heightSeries .E7 K h →
      x * e7FramePt K F = e7FramePt K F * x)
    {w : adjointGroup .E7 K} (hw : w ∈ Exc.zx (e7FramePt K F)) :
    w = 1 ∨ w = e7FramePt K F := by
  classical
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hLr : ∀ α ∈ F ++ kills.map Prod.fst, IsRoot .E7 α ∧ 0 < height α := fun α hα =>
    ⟨(hD.roots α hα).1, by linarith [(hD.roots α hα).2]⟩
  have hFr : ∀ σ ∈ F, IsRoot .E7 σ := fun σ hσ => (hD.roots σ (List.mem_append_left _ hσ)).1
  have hFnd : F.Nodup := (List.nodup_append.1 hD.nodup).1
  have hFp : ∀ σ ∈ F, IsRoot .E7 σ ∧ 0 < height σ := fun σ hσ => hLr σ (List.mem_append_left _ hσ)
  have hw' : w ∈ Exc.cent (e7FramePt K F) ∧
      (∀ c ∈ Exc.cent (e7FramePt K F), w * c = c * w) ∧ w * w = 1 := hw
  have hcoe : ∀ c : adjointGroup .E7 K, c * e7FramePt K F = e7FramePt K F * c →
      (w : ModGL .E7 K) * c = c * w := fun c hc =>
    congrArg Subtype.val (hw'.2.1 c (mem_centralizer_singleton_iff.2 hc))
  have hwB : (w : ModGL .E7 K) ∈ borelGroup .E7 K := by
    refine mem_borelGroup_of_normalizes_heightSeries h1 hd w.2 fun h' hh x hx => ?_
    have hx' : x ∈ heightSeries .E7 K h := heightSeries_antitone_annih hh hx
    have hxC : x ∈ adjointGroup .E7 K :=
      posUnipotent_le_adjointGroup (heightSeries_le_posUnipotent h hx')
    have e : (w : ModGL .E7 K) * x = x * w := hcoe ⟨x, hxC⟩ (hU ⟨x, hxC⟩ hx')
    rw [e, mul_inv_cancel_right]
    exact hx
  have hwU := mem_posUnipotent_of_mem_borelGroup_card_two hK hwB
  have hΔ : ∀ δ ∈ {δ | δ ∈ Δ}, IsRoot .E7 δ ∧ 0 < height δ := fun δ hδ =>
    ⟨(hD.deltas δ hδ).1, (hD.deltas δ hδ).2.1⟩
  have hwΔ : ∀ δ ∈ {δ | δ ∈ Δ}, (w : ModGL .E7 K) * pinnedX .E7 K δ 1 =
      pinnedX .E7 K δ 1 * w := fun δ hδ =>
    hcoe (e7RootElt δ) (pinnedX_comm_e7FramePt hFr (hD.deltas δ hδ).1 (hD.deltas δ hδ).2.2 1)
  have hwL : (w : ModGL .E7 K) ∈ rootSpan .E7 K {γ | γ ∈ F ++ kills.map Prod.fst} := by
    refine rootSpan_le_of_subset_e7 (fun γ hγ => ?_)
      (mem_rootSpan_annRoots_of_commute hτ hΔ hwU hwΔ)
    rw [mem_annRoots_iff hΔ] at hγ
    by_contra hn
    obtain ⟨δ, hδ, hr⟩ := hD.cover γ hγ.1 hγ.2.1 hn
    exact hγ.2.2 δ hδ hr
  obtain ⟨c, hc⟩ := exists_eq_prod_of_mem_rootSpan (fun γ hγ => height_le_of_isRoot_e7 hγ)
    (by norm_num : (17 : ℤ) < 2 * 9) hD.nodup hLr (fun α hα => (hD.roots α hα).2) hwL
  have hkill : ∀ p ∈ kills, c p.1 = 0 := by
    intro p hp
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hD.killers p hp
    have hcomm := hcoe (e7RootElt (-p.2)) (pinnedX_comm_e7FramePt hFr (IsRoot.neg k1) k6 1)
    rw [hc] at hcomm
    exact coeff_eq_zero_of_commute_neg_mem hτ hD.nodup hLr
      (List.mem_append_right _ (List.mem_map_of_mem hp)) k1 k2 k3 k4 k5 c hcomm.symm
  have hwF : (w : ModGL .E7 K) = (F.map fun σ => pinnedX .E7 K σ (c σ)).prod := by
    have hN : ((kills.map Prod.fst).map fun α => pinnedX .E7 K α (c α)).prod = 1 :=
      List.prod_eq_one fun x hx => by
        obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
        rw [hkill p hp, pinnedX_zero]
    rw [hc, List.map_append, List.prod_append, hN, mul_one]
  have hswap : ∀ ω ∈ ws, ∀ σ ∈ F, c (ω.foldr (reflect .E7) σ) = c σ := by
    intro ω hω
    obtain ⟨hperm, hinv⟩ := hD.swaps ω hω
    have hn : e7WordElt ω * e7FramePt K F = e7FramePt K F * e7WordElt ω :=
      Subtype.ext (wordProd_comm_framePt hτ hFr hD.orth ω hperm)
    have hcomm := hcoe (e7WordElt ω) hn
    rw [hwF] at hcomm
    exact coeff_smul_eq_of_commute_word hτ hFnd hFp hD.orth ω hperm hinv c hcomm.symm
  have hlink : ∀ p ∈ links, c p.2.2.1 = c p.2.2.2 := by
    intro p hp
    obtain ⟨ha, hb, h₁, h₂, hne, hμ, -, hμp, ha₁, hb₂, haF, hbF, haμ, hμ₁⟩ := hD.linked p hp
    set F' := (F.erase p.2.2.1).erase p.2.2.2
    have h₂' : p.2.2.2 ∈ F.erase p.2.2.1 := (hFnd.mem_erase_iff).2 ⟨hne.symm, h₂⟩
    have hperm : F.Perm (p.2.2.1 :: p.2.2.2 :: F') :=
      (List.perm_cons_erase h₁).trans (List.Perm.cons _ (List.perm_cons_erase h₂'))
    have hF'F : ∀ σ ∈ F', σ ∈ F ∧ σ ≠ p.2.2.1 ∧ σ ≠ p.2.2.2 := fun σ hσ => by
      have hnd1 : (F.erase p.2.2.1).Nodup := hFnd.erase _
      obtain ⟨hσ2, hσ1⟩ := hnd1.mem_erase_iff.1 hσ
      obtain ⟨hσ1', hσF⟩ := hFnd.mem_erase_iff.1 hσ1
      exact ⟨hσF, hσ1', hσ2⟩
    have hσ₁r := hFr _ h₁
    have hσ₂r := hFr _ h₂
    have hF'r : ∀ σ ∈ F', IsRoot .E7 σ := fun σ hσ => hFr σ (hF'F σ hσ).1
    have haF' : ∀ σ ∈ F', 0 ≤ iform p.1 σ := fun σ hσ => haF σ (hF'F σ hσ).1 (hF'F σ hσ).2.1
    have hbF' : ∀ σ ∈ F', 0 ≤ iform p.2.1 σ := fun σ hσ => hbF σ (hF'F σ hσ).1 (hF'F σ hσ).2.2
    have hprod1 : (F.map fun σ => pinnedX .E7 K σ 1).prod =
        ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ 1).prod :=
      classD4_frame_prod_perm hτ hFr hD.orth hperm fun _ => 1
    have hprodc : (F.map fun σ => pinnedX .E7 K σ (c σ)).prod =
        ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ (c σ)).prod :=
      classD4_frame_prod_perm hτ hFr hD.orth hperm c
    have h1' : pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1 *
        ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ 1).prod *
          (pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1)⁻¹ =
        ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ 1).prod := by
      have h := conj_link_eq (K := K) hτ hσ₁r hσ₂r hF'r ha hb rfl hμ.symm ha₁ hb₂
        (hbF _ h₁ hne) (haF _ h₂ hne.symm) haμ hμ₁ haF' hbF' fun _ => (1 : K)
      simp only [CharTwo.add_self_eq_zero, pinnedX_zero, one_mul] at h
      exact h
    have hg : e7PairElt p.1 p.2.1 * e7FramePt K F = e7FramePt K F * e7PairElt p.1 p.2.1 := by
      apply Subtype.ext
      show pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1 * (F.map fun σ => pinnedX .E7 K σ 1).prod =
        (F.map fun σ => pinnedX .E7 K σ 1).prod * (pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1)
      rw [hprod1]
      calc _ = pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1 *
            ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ 1).prod *
              (pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1)⁻¹ *
                (pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1) := by group
        _ = _ := by rw [h1']
    have hcomm := hcoe (e7PairElt p.1 p.2.1) hg
    rw [hwF] at hcomm
    have hcomm' : pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1 *
        ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ (c σ)).prod =
      ((p.2.2.1 :: p.2.2.2 :: F').map fun σ => pinnedX .E7 K σ (c σ)).prod *
        (pinnedX .E7 K p.1 1 * pinnedX .E7 K p.2.1 1) := by
      rw [← hprodc]
      exact hcomm.symm
    exact coeff_eq_of_commute_link hτ hσ₁r hσ₂r hF'r ha hb rfl hμ.symm ha₁ hb₂ (hbF _ h₁ hne)
      (haF _ h₂ hne.symm) haμ hμ₁ haF' hbF' hμp c hcomm'
  have hall : ∀ σ ∈ F, ∀ σ' ∈ F, c σ = c σ' := eq_of_isChain c hD.chain fun σ hσ σ' _ hs => by
    rcases hs with ⟨ω, hω, rfl⟩ | ⟨p, hp, rfl, rfl⟩
    · exact (hswap ω hω σ hσ).symm
    · exact hlink p hp
  rcases eq_one_or_eq_of_coeffs hK c hall with h0 | h0
  · exact Or.inl (Subtype.ext (by rw [hwF, h0]; rfl))
  · exact Or.inr (Subtype.ext (by rw [hwF, h0]; rfl))

theorem card_zx_le_two_of_forall_e7 {C : Type*} [Group C] {x : C}
    (h : ∀ w ∈ Exc.zx x, w = 1 ∨ w = x) : Nat.card (Exc.zx x) ≤ 2 := by
  have hsub : ((Exc.zx x : Subgroup C) : Set C) ⊆ {1, x} := fun w hw => h w hw
  calc Nat.card (Exc.zx x) = ((Exc.zx x : Subgroup C) : Set C).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ({1, x} : Set C).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

theorem mul_comm_of_mem_closure_odd_e7 {G : Type*} [Group G] {t x : G}
    (hx : x ∈ closure {c : G | c * t = t * c ∧ Odd (orderOf c)}) : x * t = t * x := by
  have hle : closure {c : G | c * t = t * c ∧ Odd (orderOf c)} ≤ centralizer {t} :=
    (closure_le _).2 fun c hc => mem_centralizer_singleton_iff.2 hc.1
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem card_zx_le_two_e7_x
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e7FramePt K [highRoot .E7])) ≤ 2 := by
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  have ht : ((e7FramePt K [highRoot .E7] : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K (highRoot .E7) 1 := by
    simp [e7FramePt]
  refine card_zx_le_two_of_forall_e7 fun w hw => eq_one_or_eq_of_mem_zx_e7 hK
    (ZxData7.of_check e7ZxX_check : ZxData7 [highRoot .E7] _ _ _ _) le_rfl
    (simpleDiffTail_one .E7) (fun x hx => ?_) hw
  rw [heightSeries_one] at hx
  exact mul_comm_of_mem_closure_odd_e7 (posUnipotent_le_closure_odd_E_two hτ hK ht hx)

theorem card_zx_le_two_e7_y
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e7FramePt K oddDerivE7YFrame)) ≤ 2 :=
  card_zx_le_two_of_forall_e7 fun _ hw => eq_one_or_eq_of_mem_zx_e7 hK
    (ZxData7.of_check e7ZxY_check : ZxData7 oddDerivE7YFrame _ _ _ _) (by norm_num)
    simpleDiffTail_E7_5
    (fun x hx => mul_comm_of_mem_closure_odd_e7 (heightSeries_le_closure_odd_E7_y
      (t := e7FramePt K oddDerivE7YFrame) rfl x hx)) hw

theorem card_zx_le_two_e7_z
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e7FramePt K oddDerivE7ZFrame)) ≤ 2 :=
  card_zx_le_two_of_forall_e7 fun _ hw => eq_one_or_eq_of_mem_zx_e7 hK
    (ZxData7.of_check e7ZxZ_check : ZxData7 oddDerivE7ZFrame _ _ _ _) (by norm_num)
    simpleDiffTail_E7_7
    (fun x hx => mul_comm_of_mem_closure_odd_e7 (heightSeries_le_closure_odd_E7_z
      (t := e7FramePt K oddDerivE7ZFrame) rfl x hx)) hw

theorem card_zx_le_two_e7_u
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e7FramePt K oddDerivE7UFrame)) ≤ 2 :=
  card_zx_le_two_of_forall_e7 fun _ hw => eq_one_or_eq_of_mem_zx_e7 hK
    (ZxData7.of_check e7ZxU_check : ZxData7 oddDerivE7UFrame _ _ _ _) (by norm_num)
    simpleDiffTail_E7_10
    (fun x hx => mul_comm_of_mem_closure_odd_e7 (heightSeries_le_closure_odd_E7_u
      (t := e7FramePt K oddDerivE7UFrame) rfl x hx)) hw

theorem card_zx_le_two_e7_v
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    Nat.card (Exc.zx (e7FramePt K oddDerivE7VFrame)) ≤ 2 :=
  card_zx_le_two_of_forall_e7 fun _ hw => eq_one_or_eq_of_mem_zx_e7 hK
    (ZxData7.of_check e7ZxV_check : ZxData7 oddDerivE7VFrame _ _ _ _) (by norm_num)
    simpleDiffTail_E7_10
    (fun x hx => mul_comm_of_mem_closure_odd_e7 (heightSeries_le_closure_odd_E7_v
      (t := e7FramePt K oddDerivE7VFrame) rfl x hx)) hw

theorem card_zx_e7Reps_two
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∀ x ∈ e7Reps K, Nat.card (Exc.zx x) < 4 := by
  obtain ⟨cX, cY, cZ, cU, cV⟩ := isConj_e7FramePt_inner (K := K)
  have key : ∀ t x : adjointGroup .E7 K, IsConj t x → Nat.card (Exc.zx t) ≤ 2 →
      Nat.card (Exc.zx x) < 4 := by
    intro t x htx ht
    obtain ⟨g, hg⟩ := isConj_iff.1 htx
    rw [← hg, Exc.card_zx_conj]
    omega
  intro x hx
  simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact key _ _ cX (card_zx_le_two_e7_x hK)
  · exact key _ _ cY (card_zx_le_two_e7_y hK)
  · exact key _ _ cZ (card_zx_le_two_e7_z hK)
  · exact key _ _ cU (card_zx_le_two_e7_u hK)
  · exact key _ _ cV (card_zx_le_two_e7_v hK)

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
