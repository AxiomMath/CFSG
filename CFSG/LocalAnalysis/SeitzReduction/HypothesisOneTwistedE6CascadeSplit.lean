module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeTree
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassCascade

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

@[expose] def twistedE6SplitWord : List (Fin TwistTag.E6.tag.rank) := ([1, 3, 2] : List (Fin 6))

@[expose] def twistedE6SplitWordInv : List (Fin TwistTag.E6.tag.rank) := ([2, 3, 1] : List (Fin 6))

@[expose] def twistedE6WordAct (ω : List (Fin TwistTag.E6.tag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ℤ :=
  ω.foldr (fun i v => reflect TwistTag.E6.tag i v) v

@[expose] def twistedE6SplitCasc : List (Fin TwistTag.E6.tag.rank → ℤ) := [e6CascC, e6RootA4]

set_option synthInstance.maxSize 2048 in
theorem twistedE6Split_checks :
    twistedE6CascPosA3'.Nodup ∧
    (∀ δ ∈ twistedE6CascPosA3', δ ∈ twistedE6PosRoots ∧
      permLattice TwistTag.E6.perm δ = δ ∧ iform twistedE6CascPairE6 δ = 0 ∧
      iform (permLattice TwistTag.E6.perm twistedE6CascPairE6) δ = 0 ∧
      twistedE6WordAct twistedE6SplitWord δ ∈ twistedE6CascPosA3) ∧
    (∀ δ ∈ twistedE6PosRoots, iform twistedE6CascPairE6 δ = 0 →
      iform (permLattice TwistTag.E6.perm twistedE6CascPairE6) δ = 0 → δ ∈ twistedE6CascPosA3') ∧
    (∀ δ ∈ twistedE6PosRoots,
      (∀ l ∈ List.finRange TwistTag.E6.tag.rank, l ∉ twistedE6CascJA3 → δ l = 0) →
        δ ∈ twistedE6CascPosA3) ∧
    (∀ β ∈ twistedE6CascPosA3,
      twistedE6WordAct twistedE6SplitWord (twistedE6WordAct twistedE6SplitWordInv β) = β ∧
      twistedE6WordAct twistedE6SplitWordInv β ∈ twistedE6CascPosA3') ∧
    (∀ j ∈ twistedE6CascJA3,
      twistedE6WordAct twistedE6SplitWord (twistedE6WordAct twistedE6SplitWordInv
        (Pi.single j 1)) = Pi.single j 1 ∧
      twistedE6WordAct twistedE6SplitWord (twistedE6WordAct twistedE6SplitWordInv
        (-Pi.single j 1)) = -Pi.single j 1 ∧
      permLattice TwistTag.E6.perm (twistedE6WordAct twistedE6SplitWordInv (Pi.single j 1)) =
        twistedE6WordAct twistedE6SplitWordInv (Pi.single j 1) ∧
      permLattice TwistTag.E6.perm (twistedE6WordAct twistedE6SplitWordInv (-Pi.single j 1)) =
        twistedE6WordAct twistedE6SplitWordInv (-Pi.single j 1) ∧
      iform twistedE6CascPairE6 (twistedE6WordAct twistedE6SplitWordInv (Pi.single j 1)) = 0 ∧
      iform (permLattice TwistTag.E6.perm twistedE6CascPairE6)
        (twistedE6WordAct twistedE6SplitWordInv (Pi.single j 1)) = 0 ∧
      iform twistedE6CascPairE6 (twistedE6WordAct twistedE6SplitWordInv (-Pi.single j 1)) = 0 ∧
      iform (permLattice TwistTag.E6.perm twistedE6CascPairE6)
        (twistedE6WordAct twistedE6SplitWordInv (-Pi.single j 1)) = 0) ∧
    (∀ s ∈ twistedE6SplitCasc, s ∈ twistedE6CascPosA3 ∧
      twistedE6WordAct twistedE6SplitWordInv s ∈ twistedE6CascPosA3') ∧
    (∀ a ∈ twistedE6SplitCasc, ∀ b ∈ twistedE6SplitCasc, iform a b = 0 →
      iform (twistedE6WordAct twistedE6SplitWordInv a)
        (twistedE6WordAct twistedE6SplitWordInv b) = 0) ∧
    (∀ a ∈ twistedE6SplitCasc, ∀ b ∈ twistedE6SplitCasc,
      twistedE6WordAct twistedE6SplitWordInv a = twistedE6WordAct twistedE6SplitWordInv b →
        a = b) := by
  decide +kernel

theorem twistedE6Split_cascadeCheck :
    cascadeCheck TwistTag.E6.tag twistedE6SplitCasc 3 twistedE6CascJA3 = true := by
  decide +kernel

theorem IsRoot.twistedE6WordAct {v : Fin TwistTag.E6.tag.rank → ℤ}
    (hv : IsRoot TwistTag.E6.tag v) (ω : List (Fin TwistTag.E6.tag.rank)) :
    IsRoot TwistTag.E6.tag (twistedE6WordAct ω v) := by
  unfold CFSG.SeitzReduction.twistedE6WordAct
  induction ω with
  | nil => exact hv
  | cons j ω ih => exact IsRoot.reflect j ih

@[expose] def twistedE6FixedField (σ : K →+* K) : Subfield K := σ.eqLocusField (RingHom.id K)

theorem twistedE6FixedField_charP [CharP K 2] (σ : K →+* K) :
    CharP (twistedE6FixedField σ) 2 where
  cast_eq_zero_iff x := by
    rw [← map_eq_zero_iff (twistedE6FixedField σ).subtype Subtype.val_injective, map_natCast,
      CharP.cast_eq_zero_iff K 2]


theorem twistedE6_word_inv_conj_pinnedX {L : Type} [Field L] [CharP L 2]
    (ω ω' : List (Fin TwistTag.E6.tag.rank)) {v : Fin TwistTag.E6.tag.rank → ℤ}
    (hv : IsRoot TwistTag.E6.tag (twistedE6WordAct ω' v))
    (hww : twistedE6WordAct ω (twistedE6WordAct ω' v) = v) (e : L) :
    ((ω.map fun j => weylElt TwistTag.E6.tag L j 1).prod)⁻¹ * pinnedX TwistTag.E6.tag L v e *
        (ω.map fun j => weylElt TwistTag.E6.tag L j 1).prod =
      pinnedX TwistTag.E6.tag L (twistedE6WordAct ω' v) e := by
  have h := twistedE6_list_weylElt_conj_pinnedX (K := L) ω hv e
  change _ = pinnedX TwistTag.E6.tag L (twistedE6WordAct ω (twistedE6WordAct ω' v)) e at h
  rw [hww] at h
  rw [← h]
  group

theorem twistedE6_weylElt_one_eq {L : Type} [Field L] (j : Fin TwistTag.E6.tag.rank) :
    weylElt TwistTag.E6.tag L j 1 = pinnedX TwistTag.E6.tag L (Pi.single j 1) 1 *
      pinnedX TwistTag.E6.tag L (-Pi.single j 1) (-1) *
        pinnedX TwistTag.E6.tag L (Pi.single j 1) 1 := by
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul, pinnedX_single, pinnedX_neg_single]
  simp

theorem twistedE6_pinnedX_mem_pairCentralizer {γ v : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hv : IsRoot TwistTag.E6.tag v) (h1 : iform γ v = 0)
    (h2 : iform (permLattice TwistTag.E6.perm γ) v = 0) (e : K) :
    pinnedX TwistTag.E6.tag K v e ∈ twistedE6PairCentralizer K γ := by
  refine Subgroup.mem_iInf.2 fun e' => Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (twistedE6_commute_of_iform_eq_zero hv hγ (by rw [iform_comm]; exact h1) e e').eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (twistedE6_commute_of_iform_eq_zero hv (hγ.permLattice TwistTag.E6.cartan_perm)
      (by rw [iform_comm]; exact h2) e e').eq

theorem twistedE6LevelA3'_holds [CharP K 2] (σ : K →+* K) : TwistedE6LevelA3' K σ := by
  classical
  intro z hz hzΓ hz2
  obtain ⟨hnd, hA, hA', hA3, hinv, hj, hcasc, hcascO, hcascI⟩ := twistedE6Split_checks
  have hr := twistedE6CascadeTree_roots
  have hPosA3 := hr.2.2.2.2.2.1
  have hG := twistedE6_isRoot_of_mem_posRoots hr.2.2.2.2.2.2.2.2.1.1
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  generalize hLdef : twistedE6CascPosA3' = L at hnd hA hA' hz ⊢
  have hS : ∀ α ∈ {δ | δ ∈ L}, IsRoot TwistTag.E6.tag α ∧ 0 < height α := fun α hα =>
    twistedE6_isRoot_of_mem_posRoots (hA α hα).1
  have hclosed : ∀ α ∈ {δ | δ ∈ L}, ∀ β ∈ {δ | δ ∈ L}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ {δ | δ ∈ L} := by
    intro α hα β hβ a b ha hb hroot
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have hpos : 0 < height (a • α + b • β) := by
      rw [height_nsmul_add_nsmul]; nlinarith [(hS α hα).2, (hS β hβ).2]
    have e : (a • α + b • β : Fin TwistTag.E6.tag.rank → ℤ) = (a : ℤ) • α + (b : ℤ) • β := by
      rw [natCast_zsmul, natCast_zsmul]
    refine hA' _ (mem_twistedE6PosRoots hroot hpos) ?_ ?_
    · rw [e, iform_add_right, iform_smul_right, iform_smul_right, (hA α hα).2.2.1,
        (hA β hβ).2.2.1, mul_zero, mul_zero, add_zero]
    · rw [e, iform_add_right, iform_smul_right, iform_smul_right, (hA α hα).2.2.2.1,
        (hA β hβ).2.2.2.1, mul_zero, mul_zero, add_zero]
  set e : Fin L.length → Fin TwistTag.E6.tag.rank → ℤ := L.get with he
  have heinj : Function.Injective e := List.nodup_iff_injective_get.1 hnd
  have herange : Set.range e = {δ | δ ∈ L} := Set.range_list_get L
  have hbij := bijOn_prod_pinnedX K hS hclosed e heinj herange
  obtain ⟨d, -, hd⟩ := hbij.surjOn hz
  have hd' : (List.ofFn fun k => pinnedX TwistTag.E6.tag K (e k) (d k)).prod = z := hd
  have hek : ∀ k, e k ∈ L := fun k => List.get_mem L k
  have hfix : ∀ k, σ (d k) = d k := by
    have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hzΓ).2
    rw [← hd', map_list_prod, List.map_ofFn] at hF
    have hF' : (List.ofFn fun k => pinnedX TwistTag.E6.tag K (e k) (σ (d k))).prod =
        (List.ofFn fun k => pinnedX TwistTag.E6.tag K (e k) (d k)).prod := by
      rw [← hF]
      refine congrArg List.prod (List.ofFn_inj.2 (funext fun k => ?_))
      simp only [Function.comp_apply]
      rw [twistHom_pinnedX_eq_of_charTwo (CharP.cast_eq_zero K 2) σ (hS _ (hek k)).1,
        (hA _ (hek k)).2.1]
    exact fun k => congrFun (hbij.injOn (Set.mem_univ _) (Set.mem_univ _) hF') k
  set F₀ := twistedE6FixedField σ with hF₀
  have : CharP F₀ 2 := twistedE6FixedField_charP σ
  set ι : F₀ →+* K := F₀.subtype with hι
  set d₀ : Fin L.length → F₀ := fun k => ⟨d k, hfix k⟩ with hd₀
  set z₀ : ModGL TwistTag.E6.tag F₀ :=
    (List.ofFn fun k => pinnedX TwistTag.E6.tag F₀ (e k) (d₀ k)).prod with hz₀def
  have hz₀ : baseChangeGL ι z₀ = z := by
    rw [← hd', hz₀def, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (List.ofFn_inj.2 (funext fun k => ?_))
    simp only [Function.comp_apply, baseChangeGL_pinnedX]
    rfl
  have hz₀2 : z₀ ^ 2 = 1 :=
    baseChangeGL_injective ι (by rw [map_pow, hz₀, hz2, map_one])
  set n : ModGL TwistTag.E6.tag F₀ :=
    (twistedE6SplitWord.map fun j => weylElt TwistTag.E6.tag F₀ j 1).prod with hn
  have hconj : n * z₀ * n⁻¹ = (List.ofFn fun k => pinnedX TwistTag.E6.tag F₀
      (twistedE6WordAct twistedE6SplitWord (e k)) (d₀ k)).prod := by
    rw [hz₀def, List.ofFn_eq_map, conj_list_prod_map, List.ofFn_eq_map]
    refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
    exact twistedE6_list_weylElt_conj_pinnedX (K := F₀) twistedE6SplitWord (hS _ (hek k)).1 _
  have hmemJ : n * z₀ * n⁻¹ ∈ rootSpan TwistTag.E6.tag F₀
      (parabolicPosRoots TwistTag.E6.tag {j | j ∈ twistedE6CascJA3}) := by
    rw [hconj]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    have hk := hPosA3 _ (hA _ (hek k)).2.2.2.2
    exact (le_iSup₂_of_le _ (twistedE6_mem_parabolic_of_mem hk.1 hk.2) le_rfl :
      rootSubgroup TwistTag.E6.tag F₀ _ ≤ _) (Subgroup.subset_closure ⟨d₀ k, rfl⟩)
  have hsq : (n * z₀ * n⁻¹) ^ 2 = 1 := by rw [conj_pow, hz₀2, mul_one, mul_inv_cancel]
  obtain ⟨g₀, hg₀, S, hSnd, hSc, hSo, c₀, hc₀, he₀⟩ := cascade_exists_conj_of_check (K := F₀) hτ
    twistedE6SplitCasc 3 twistedE6CascJA3 twistedE6Split_cascadeCheck (n * z₀ * n⁻¹) hmemJ hsq
  have hinvconj : ∀ s ∈ S, ∀ x : F₀, n⁻¹ * pinnedX TwistTag.E6.tag F₀ s x * n =
      pinnedX TwistTag.E6.tag F₀ (twistedE6WordAct twistedE6SplitWordInv s) x := fun s hs x => by
    have hs' := hcasc s (hSc s hs).1
    exact twistedE6_word_inv_conj_pinnedX twistedE6SplitWord twistedE6SplitWordInv
      (twistedE6_isRoot_of_mem_posRoots (hA _ (hLdef ▸ hs'.2)).1).1 (hinv s hs'.1).1 x
  set G₀ := n⁻¹ * g₀ * n with hG₀
  have hG₀z : G₀ * z₀ * G₀⁻¹ = (S.map fun s => pinnedX TwistTag.E6.tag F₀
      (twistedE6WordAct twistedE6SplitWordInv s) (c₀ s)).prod := by
    have e1 : G₀ * z₀ * G₀⁻¹ = n⁻¹ * (g₀ * (n * z₀ * n⁻¹) * g₀⁻¹) * n := by rw [hG₀]; group
    have e2 := conj_list_prod_map n⁻¹ S (fun s => pinnedX TwistTag.E6.tag F₀ s (c₀ s))
    rw [inv_inv] at e2
    rw [e1, he₀, e2]
    exact congrArg List.prod (List.map_congr_left fun s hs => hinvconj s hs (c₀ s))
  set G := baseChangeGL ι G₀ with hGdef
  have hGz : G * z * G⁻¹ = (S.map fun s => pinnedX TwistTag.E6.tag K
      (twistedE6WordAct twistedE6SplitWordInv s) (ι (c₀ s))).prod := by
    rw [hGdef, ← hz₀, ← map_inv, ← map_mul, ← map_mul, hG₀z, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun s _ => baseChangeGL_pinnedX ι _ _)
  have hgood : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag v →
      permLattice TwistTag.E6.perm v = v → iform twistedE6CascPairE6 v = 0 →
      iform (permLattice TwistTag.E6.perm twistedE6CascPairE6) v = 0 → ∀ x : K, σ x = x →
        pinnedX TwistTag.E6.tag K v x ∈ graphFixedRootGroup TwistTag.E6 K σ ⊓
          twistedE6PairCentralizer K twistedE6CascPairE6 := fun v hv hρ h1 h2 x hx =>
    Subgroup.mem_inf.2 ⟨pinnedX_mem_graphFixedRootGroup_of_fixed σ hv hρ hx,
      twistedE6_pinnedX_mem_pairCentralizer hG.1 hv h1 h2 x⟩
  let φ : ModGL TwistTag.E6.tag F₀ →* ModGL TwistTag.E6.tag K :=
    (baseChangeGL ι).comp (MulAut.conj n⁻¹).toMonoidHom
  have hφ : ∀ g, φ g = baseChangeGL ι (n⁻¹ * g * n) := fun g => by
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hle : cascadeConjGroup TwistTag.E6.tag F₀ {j | j ∈ twistedE6CascJA3} ≤
      (graphFixedRootGroup TwistTag.E6 K σ ⊓ twistedE6PairCentralizer K twistedE6CascPairE6).comap
        φ := by
    refine sup_le (iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_)
      ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
      have hβ3 : β ∈ twistedE6CascPosA3 :=
        hA3 β (mem_twistedE6PosRoots hβ.2.1 hβ.2.2) (fun l _ hl => hβ.1.2 l hl)
      obtain ⟨hww, hw'⟩ := hinv β hβ3
      obtain ⟨h1, h2, h3, h4, -⟩ := hA _ (hLdef ▸ hw')
      rw [twistedE6_word_inv_conj_pinnedX twistedE6SplitWord twistedE6SplitWordInv
        (twistedE6_isRoot_of_mem_posRoots h1).1 hww x, baseChangeGL_pinnedX]
      exact hgood _ (twistedE6_isRoot_of_mem_posRoots h1).1 h2 h3 h4 _ x.2
    · rintro _ ⟨j, hjJ, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, hφ, twistedE6_weylElt_one_eq]
      obtain ⟨hw1, hw2, hρ1, hρ2, h11, h12, h21, h22⟩ := hj j hjJ
      have hr1 := IsRoot.twistedE6WordAct (isRoot_single TwistTag.E6.tag j) twistedE6SplitWordInv
      have hr2 := IsRoot.twistedE6WordAct (isRoot_neg_single TwistTag.E6.tag j)
        twistedE6SplitWordInv
      rw [show n⁻¹ * (pinnedX TwistTag.E6.tag F₀ (Pi.single j 1) 1 *
          pinnedX TwistTag.E6.tag F₀ (-Pi.single j 1) (-1) *
          pinnedX TwistTag.E6.tag F₀ (Pi.single j 1) 1) * n =
          (n⁻¹ * pinnedX TwistTag.E6.tag F₀ (Pi.single j 1) 1 * n) *
          (n⁻¹ * pinnedX TwistTag.E6.tag F₀ (-Pi.single j 1) (-1) * n) *
          (n⁻¹ * pinnedX TwistTag.E6.tag F₀ (Pi.single j 1) 1 * n) by group,
        twistedE6_word_inv_conj_pinnedX _ _ hr1 hw1, twistedE6_word_inv_conj_pinnedX _ _ hr2 hw2,
        map_mul, map_mul, baseChangeGL_pinnedX, baseChangeGL_pinnedX, map_one, map_neg, map_one]
      have g1 := hgood _ hr1 hρ1 h11 h12 1 (map_one σ)
      have g2 := hgood _ hr2 hρ2 h21 h22 (-1) (by rw [map_neg, map_one])
      exact mul_mem (mul_mem g1 g2) g1
  have hGmem := hle hg₀
  rw [Subgroup.mem_comap, hφ] at hGmem
  have hcfix : ∀ s ∈ S, permLattice TwistTag.E6.perm (twistedE6WordAct twistedE6SplitWordInv s) =
      twistedE6WordAct twistedE6SplitWordInv s := fun s hs =>
    (hA _ (hLdef ▸ (hcasc s (hSc s hs).1).2)).2.1
  have hunits : (S.map (twistedE6WordAct twistedE6SplitWordInv)).flatMap twistedE6Unit =
      S.map (twistedE6WordAct twistedE6SplitWordInv) := by
    have h : ∀ γ ∈ S.map (twistedE6WordAct twistedE6SplitWordInv), twistedE6Unit γ = [γ] :=
      fun γ hγ => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hγ
        exact twistedE6Unit_of_fixed (hcfix s hs)
    rw [List.flatMap_congr h, List.flatMap_singleton']
  refine ⟨G, (Subgroup.mem_inf.1 hGmem).2, (Subgroup.mem_inf.1 hGmem).1,
    S.map (twistedE6WordAct twistedE6SplitWordInv), ⟨?_, ?_, ?_⟩,
    fun β => ι (c₀ (twistedE6WordAct twistedE6SplitWord β)), ?_, ?_⟩
  · rw [hunits]
    exact hSnd.map_on fun a ha b hb h => hcascI a (hSc a ha).1 b (hSc b hb).1 h
  · rw [hunits]
    intro β hβ
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hβ
    have hsL : twistedE6WordAct twistedE6SplitWordInv s ∈ L := hLdef ▸ (hcasc s (hSc s hs).1).2
    exact ⟨(hS _ hsL).1, (hS _ hsL).2, hsL⟩
  · rw [hunits, List.pairwise_map]
    exact hSo.imp_of_mem fun ha hb h => hcascO _ (hSc _ ha).1 _ (hSc _ hb).1 h
  · intro γ hγ
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hγ
    dsimp only
    rw [(hinv s (hcasc s (hSc s hs).1).1).1]
    exact ⟨fun h => hc₀ s hs ((map_eq_zero_iff ι Subtype.val_injective).1 h),
      fun _ => RingHom.mem_eqLocusField.1 (c₀ s).2⟩
  · rw [hGz, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun s hs => ?_)
    simp only [Function.comp_apply]
    rw [(hinv s (hcasc s (hSc s hs).1).1).1, twistedE6RelX_of_fixed σ (hcfix s hs)]

end CFSG.SeitzReduction
