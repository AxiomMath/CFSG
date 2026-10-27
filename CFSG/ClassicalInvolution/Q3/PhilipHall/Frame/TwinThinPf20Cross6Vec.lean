module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinH1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinComm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf11Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18Cross
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf4Thin
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt
public import CFSG.ClassicalInvolution.Q3.TL3T42
public import CFSG.ClassicalInvolution.Q3.TL3T48
public import CFSG.ClassicalInvolution.Q3.TL3T52A
public import CFSG.ClassicalInvolution.Q3.TL3T56
public import CFSG.ClassicalInvolution.Q3.TL3T57
public import CFSG.ClassicalInvolution.Q3.TL3T60
public import CFSG.ClassicalInvolution.Q3.TL3T61
public import CFSG.ClassicalInvolution.Q3.TL4AECoverH
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

local notation "gCentMembers" => CFSG.ClassicalInvolution.Generic.centMembers
local notation "gCentLayer" => CFSG.ClassicalInvolution.Generic.centLayer

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem mem_centMembers_of_label {m : ℕ} (hm : 5 ≤ m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {u : G}
    (hu : u ∈ pSpan (fam K (conjSub g (piGen π)))) {a c : Fin m} (hac : a ≠ c)
    (hφ : J.φ ⟨u, hu⟩ = AE.mkQ m (ofVec (TL4.pairVec a c)))
    {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π))) {δ : Finset (Fin m)} {hδ : δ.card = 4}
    {b : Bool} (hlab : (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
      AE.memBar δ hδ b) (haδ : a ∉ δ) (hcδ : c ∉ δ) :
    L ∈ gCentMembers (CoreAssembly.conjClass K₀) u := by
  refine CFSG.ClassicalInvolution.Generic.mem_centMembers_iff_commute.mpr ⟨S.fam_mem hL, fun k hk => ?_⟩
  have hcomm := (AEIdent.comm_pairVec_iff J hm (fun L hL => S.card8 L (S.fam_mem hL))
    (fun L hL x hx => by rw [S.fam_gen] at hx; exact fam_inv L hL x hx)
    (fun L hL L' hL' he => S.eq_of_map_le hm J hL hL' (le_of_eq he)) hac hφ hL hlab).mpr ⟨haδ, hcδ⟩
  exact (hcomm k hk).symm

theorem exists_vector_of_secYu {m : ℕ} (hm : 7 ≤ m) (htw : S.TwinLab m)
    (hAut : TwinThinPf8.AEAut m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hsec : SecYu K₀ K K' z π g) :
    ∀ J' ∈ π, ∀ t : G, IsUniqueInvolution J' t →
      ∃ w : Wr m, Cross.InducedBy J t w ∧ w.perm = 1 := by
  classical
  have hm5 : 5 ≤ m := by omega
  obtain ⟨α, h, b, hlab⟩ := J.label K S.mem_fam_self
  obtain ⟨u, a, c, ha, hc, hac, hpair, huX, hu', hφu⟩ := S.exists_pairInv hm5 htw J hlab
  obtain ⟨-, hS2, k, hk5, ⟨Ju⟩⟩ := hsec u hpair
  intro J' hJ' t ht
  obtain ⟨w, hw, hfix⟩ := S.exists_induced_fix hm5 hAut htw J hJ' ht hlab
  refine ⟨w, hw, ?_⟩
  have hmemπ : J' ∈ gCentMembers (CoreAssembly.conjClass K₀) u :=
    CFSG.ClassicalInvolution.Generic.mem_centMembers_iff_commute.mpr
      ⟨S.mem_of_mem_pi hJ', fun x hx => huX x (le_piGen hJ' hx)⟩
  have htO : t ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) :=
    hS2 J' hmemπ t ht
  have hN : t ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G) :=
    S.mem_normalizer_pSpan_fam (S.cent_of_involution_pi hm5 htw J hJ' ht)
  refine TwinThinPf20.perm_eq_one_of_pair_comm hm a c w.perm (hfix a ha) (hfix c hc) ?_
  intro p q hpq hpa hpc hqa hqc δ hδ haδ hcδ x hx
  obtain ⟨R, hRsub, hRcard⟩ : ∃ R : Finset (Fin m), R ⊆ (Finset.univ \ {a, c, p, q}) ∧ R.card = 3 := by
    have h1 := Finset.le_card_sdiff ({a, c, p, q} : Finset (Fin m)) Finset.univ
    have h2 : ({a, c, p, q} : Finset (Fin m)).card ≤ 4 := Finset.card_le_four
    rw [Finset.card_univ, Fintype.card_fin] at h1
    obtain ⟨R, hR, hRc⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ {a, c, p, q}) (n := 3)
      (by omega)
    exact ⟨R, hR, hRc⟩
  have hRnot : ∀ y ∈ R, y ≠ a ∧ y ≠ c ∧ y ≠ p ∧ y ≠ q := by
    intro y hy
    have := hRsub hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
      not_or] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  have hpR : p ∉ R := fun hh => (hRnot p hh).2.2.1 rfl
  have hqR : q ∉ R := fun hh => (hRnot q hh).2.2.2 rfl
  have hγ₁ : (insert p R).card = 4 := by rw [Finset.card_insert_of_notMem hpR, hRcard]
  have hγ₂ : (insert q R).card = 4 := by rw [Finset.card_insert_of_notMem hqR, hRcard]
  have haγ₁ : a ∉ insert p R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hh => hpa hh.symm, fun hh => (hRnot a hh).1 rfl⟩
  have hcγ₁ : c ∉ insert p R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hh => hpc hh.symm, fun hh => (hRnot c hh).2.1 rfl⟩
  have haγ₂ : a ∉ insert q R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hh => hqa hh.symm, fun hh => (hRnot a hh).1 rfl⟩
  have hcγ₂ : c ∉ insert q R := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hh => hqc hh.symm, fun hh => (hRnot c hh).2.1 rfl⟩
  obtain ⟨L₁, hL₁, hlab₁⟩ := J.label_surj (insert p R) hγ₁ true
  obtain ⟨L₂, hL₂, hlab₂⟩ := J.label_surj (insert q R) hγ₂ true
  obtain ⟨z₁, hz₁, hφz₁⟩ := TL4.AECov.exists_isUniqueInvolution J hm5 hL₁
    (S.card8 L₁ (S.fam_mem hL₁)) hlab₁
  obtain ⟨z₂, hz₂, hφz₂⟩ := TL4.AECov.exists_isUniqueInvolution J hm5 hL₂
    (S.card8 L₂ (S.fam_mem hL₂)) hlab₂
  have hL₁u := S.mem_centMembers_of_label hm5 J hu' hac hφu hL₁ hlab₁ haγ₁ hcγ₁
  have hL₂u := S.mem_centMembers_of_label hm5 J hu' hac hφu hL₂ hlab₂ haγ₂ hcγ₂
  have hz₁O : z₁ ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) :=
    hS2 L₁ hL₁u z₁ hz₁
  have hz₂O : z₂ ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) :=
    hS2 L₂ hL₂u z₂ hz₂
  have he₀O : z₁ * z₂ ∈ pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u)) :=
    (pCoreOf 2 (pSpan (gCentMembers (CoreAssembly.conjClass K₀) u))).mul_mem hz₁O hz₂O
  have hcent := Cross.comm_central_of_pCore hk5 Ju htO he₀O
  obtain ⟨Lδ, hLδ, hlabδ⟩ := J.label_surj δ hδ true
  have hLδu := S.mem_centMembers_of_label hm5 J hu' hac hφu hLδ hlabδ haδ hcδ
  have hLδY : Lδ ≤ pSpan (gCentMembers (CoreAssembly.conjClass K₀) u) :=
    CFSG.ClassicalInvolution.Generic.le_centLayer hLδu
  rw [← hlabδ] at hx
  obtain ⟨l, hl, hlx⟩ := J.exists_of_mem_map hLδ hx
  have hcl := hcent l (hLδY hl)
  have he₀ : z₁ * z₂ ∈ pSpan (fam K (conjSub g (piGen π))) :=
    mul_mem (le_pSpan hL₁ hz₁.mem) (le_pSpan hL₂ hz₂.mem)
  have hc₁ : t * (z₁ * z₂) * t⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) :=
    TwinThinPf.conj_mem_of_normalizer hN he₀
  have hc₀ : t * (z₁ * z₂) * t⁻¹ * (z₁ * z₂)⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) :=
    mul_mem hc₁ (inv_mem he₀)
  have hφe₀ : J.φ ⟨z₁ * z₂, he₀⟩ = AE.mkQ m (ofVec (TL4.pairVec p q)) := by
    have e1 : (⟨z₁ * z₂, he₀⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) =
        ⟨z₁, le_pSpan hL₁ hz₁.mem⟩ * ⟨z₂, le_pSpan hL₂ hz₂.mem⟩ := rfl
    rw [e1, map_mul, hφz₁, hφz₂]
    show AE.mkQ m (zOf (AE.emb (insert p R) hγ₁)) * AE.mkQ m (zOf (AE.emb (insert q R) hγ₂)) = _
    rw [← map_mul, TwinThinPf10.zOf_eq_ofVec, TwinThinPf10.zOf_eq_ofVec, TL4.ofVec_mul_ofVec]
    congr 2
    funext x
    have hr1 : ∀ y, y ∈ Set.range (AE.emb (insert p R) hγ₁) ↔ y ∈ insert p R := fun y => by
      rw [AE.range_emb]; exact Finset.mem_coe
    have hr2 : ∀ y, y ∈ Set.range (AE.emb (insert q R) hγ₂) ↔ y ∈ insert q R := fun y => by
      rw [AE.range_emb]; exact Finset.mem_coe
    simp only [hr1, hr2, TL4.pairVec_apply, Pi.add_apply, Finset.mem_insert]
    by_cases hxp : x = p
    · subst hxp
      have : x ∉ R := hpR
      simp [hpq, this]
    · by_cases hxq : x = q
      · subst hxq
        have : x ∉ R := hqR
        simp [Ne.symm hpq, this]
      · by_cases hxR : x ∈ R
        · simp [hxp, hxq, hxR]
          decide
        · simp [hxp, hxq, hxR]
  have hφc₀ : J.φ ⟨t * (z₁ * z₂) * t⁻¹ * (z₁ * z₂)⁻¹, hc₀⟩ =
      AE.mkQ m (ofVec (TL4.pairVec (w.perm p) (w.perm q) + TL4.pairVec p q)) := by
    have e1 : (⟨t * (z₁ * z₂) * t⁻¹ * (z₁ * z₂)⁻¹, hc₀⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) =
        ⟨t * (z₁ * z₂) * t⁻¹, hc₁⟩ * ⟨z₁ * z₂, he₀⟩⁻¹ := rfl
    have e2 := hw ⟨z₁ * z₂, he₀⟩ ⟨t * (z₁ * z₂) * t⁻¹, hc₁⟩ rfl
    rw [e1, map_mul, map_inv, e2, hφe₀, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    rw [TwinThinPf10.conj_ofVec, TwinThinPf20.ofVec_inv_eq, ← map_mul, TL4.ofVec_mul_ofVec]
    congr 2
    funext y
    simp [TL4.pairVec_apply, Equiv.symm_apply_eq]
  have hcomm : J.φ ⟨l, le_pSpan hLδ hl⟩ * J.φ ⟨t * (z₁ * z₂) * t⁻¹ * (z₁ * z₂)⁻¹, hc₀⟩ =
      J.φ ⟨t * (z₁ * z₂) * t⁻¹ * (z₁ * z₂)⁻¹, hc₀⟩ * J.φ ⟨l, le_pSpan hLδ hl⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg J.φ (Subtype.ext hcl)
  rw [hφc₀, hlx] at hcomm
  exact hcomm.symm

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
