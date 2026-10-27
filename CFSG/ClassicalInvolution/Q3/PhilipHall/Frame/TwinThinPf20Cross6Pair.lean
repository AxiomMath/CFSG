module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Iface
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf17Lab8Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf14Ab8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf16F7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Y

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

namespace Cross

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ}

theorem exists_vec_of_pCore (hk : 5 ≤ k) (I : AEIdent P k) {x : G} (hx : x ∈ pCoreOf 2 (pSpan P)) :
    ∃ hxP : x ∈ pSpan P, ∃ v : Fin k → ZMod 2, I.φ ⟨x, hxP⟩ = mkQ k (ofVec v) := by
  have hxX : x ∈ pSpan P := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _ hx
  set T : Subgroup ↥(pSpan P) := (pCoreOf 2 (pSpan P)).subgroupOf (pSpan P) with hT
  have hTn : T.Normal := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2
    (pSpan P) (pSpan P) le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hT2 : IsPGroup 2 ↥T :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 (pSpan P)).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 (pSpan P))).symm
  have hxT : (⟨x, hxX⟩ : ↥(pSpan P)) ∈ T := hx
  have hker := TL4.AECov.le_ker_permHom_of_normal I hk hTn hT2 hxT
  obtain ⟨v, -, hv⟩ := TL4.AECov.exists_vec_of_mem_ker_permHom I hker
  exact ⟨hxX, v, hv⟩

theorem comm_central_of_pCore (hk : 5 ≤ k) (I : AEIdent P k) {x y : G}
    (hx : x ∈ pCoreOf 2 (pSpan P)) (hy : y ∈ pCoreOf 2 (pSpan P)) :
    ∀ w ∈ pSpan P, w * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * w := by
  obtain ⟨hxP, v₁, hv₁⟩ := exists_vec_of_pCore hk I hx
  obtain ⟨hyP, v₂, hv₂⟩ := exists_vec_of_pCore hk I hy
  set X₁ : ↥(pSpan P) := ⟨x, hxP⟩
  set Y₁ : ↥(pSpan P) := ⟨y, hyP⟩
  have hcomm : ofVec v₁ * ofVec v₂ = ofVec v₂ * (ofVec v₁ : Wr k) := by
    rw [TL4.ofVec_mul_ofVec, TL4.ofVec_mul_ofVec, add_comm]
  have hker : X₁ * Y₁ * X₁⁻¹ * Y₁⁻¹ ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hv₁, hv₂]
    simp only [← map_inv, ← map_mul]
    rw [hcomm]
    simp
  intro w hw
  have hc := Subgroup.mem_center_iff.mp (I.ker_le hker) ⟨w, hw⟩
  exact congrArg Subtype.val hc

end Cross

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem pow_four_of_mem {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K₀) {l : G} (hl : l ∈ L) :
    l * l * (l * l) = 1 := by
  obtain ⟨e⟩ := S.iso_q8 hL
  have h4 : ∀ q : QuaternionGroup 2, q * q * (q * q) = 1 := by decide
  have h3 := h4 (e ⟨l, hl⟩)
  have h5 : (⟨l, hl⟩ : ↥L) * ⟨l, hl⟩ * (⟨l, hl⟩ * ⟨l, hl⟩) = 1 := by
    apply e.injective
    rw [map_mul, map_mul, map_one]
    exact h3
  exact congrArg Subtype.val h5

theorem exists_pairInv {m : ℕ} (hm : 5 ≤ m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {α : Finset (Fin m)} {h : α.card = 4} {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    ∃ (u : G) (a c : Fin m), a ∈ α ∧ c ∈ α ∧ a ≠ c ∧ PairInv K K' z π g u ∧
      (∀ x ∈ piGen π, x * u = u * x) ∧
      ∃ hu : u ∈ pSpan (fam K (conjSub g (piGen π))),
        J.φ ⟨u, hu⟩ = AE.mkQ m (AE.Wr.ofVec (TL4.pairVec a c)) := by
  have hlab' := htw J hlab
  obtain ⟨l, hl, l', hl', a, ha, c, hc, hac, hll, hI⟩ :=
    J.exists_mul_eq_pairVec S.mem_fam_self S.twin_mem_fam hlab hlab'
  have hlX : ∀ x ∈ piGen π, x * l = l * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.1 hl) x hx
  have hl'X : ∀ x ∈ piGen π, x * l' = l' * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.2 hl') x hx
  have hcommB : ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar α h (!b), x * y = y * x := by
    cases b
    · intro x hx y hy
      exact (comm_memBar_twin α h y hy x hx).symm
    · exact comm_memBar_twin α h
  have hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
    refine S.commutes_of_map_comm_gen (fun L hL => S.fam_mem hL) J
      (J.isPGroup_ker S.hOdd) S.mem_fam_self S.twin_mem_fam S.hne.symm ?_
    intro x hx y hy
    rw [hlab] at hx
    rw [hlab'] at hy
    exact hcommB x hx y hy
  have hl2 : l * l = 1 ∨ l * l = z :=
    S.hz.unique (l * l) (K.mul_mem hl hl) (S.pow_four_of_mem S.hK hl)
  have hl'2 : l' * l' = 1 ∨ l' * l' = z :=
    S.hz'.unique (l' * l') (K'.mul_mem hl' hl') (S.pow_four_of_mem S.hK'.1 hl')
  have hzK : J.φ ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ = AE.zBar α h :=
    J.map_eq_zBar hm S.mem_fam_self (S.card8 K S.hK) hlab S.hz
  have hz1 : J.φ ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ ≠ 1 := by
    rw [hzK]; exact AE.zBar_ne_one hm α h
  have e : (l * l') * (l * l') = (l * l) * (l' * l') := by
    calc (l * l') * (l * l') = l * (l' * l) * l' := by group
      _ = l * (l * l') * l' := by rw [← hKK' l hl l' hl']
      _ = (l * l) * (l' * l') := by group
  have himg : J.φ ⟨(l * l') * (l * l'), mul_mem hll hll⟩ = 1 := by
    have e2 : (⟨(l * l') * (l * l'), mul_mem hll hll⟩ :
        ↥(pSpan (fam K (conjSub g (piGen π))))) = ⟨l * l', hll⟩ * ⟨l * l', hll⟩ := rfl
    rw [e2, map_mul, hI, ← map_mul, TL4.ofVec_mul_ofVec]
    have h0 : (TL4.pairVec a c + TL4.pairVec a c : Fin m → ZMod 2) = 0 := by
      funext x
      exact zmod_two_add_self _
    rw [h0]
    exact (congrArg (mkQ m) (rfl : (ofVec (0 : Fin m → ZMod 2)) = 1)).trans (map_one _)
  have huu : (l * l') * (l * l') = 1 := by
    have h12 : (l * l) * (l' * l') = 1 ∨ (l * l) * (l' * l') = z := by
      rcases hl2 with h1 | h1 <;> rcases hl'2 with h2 | h2
      · left; rw [h1, h2, one_mul]
      · right; rw [h1, h2, one_mul]
      · right; rw [h1, h2, mul_one]
      · left; rw [h1, h2, S.hz.sq]
    rcases h12 with h1 | h1
    · exact e.trans h1
    · exfalso
      apply hz1
      have : (⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) =
          ⟨(l * l') * (l * l'), mul_mem hll hll⟩ := Subtype.ext (e.trans h1).symm
      rw [this]
      exact himg
  have huO : l * l' ∈ pCoreOf 2 (conjSub g (piGen π)) :=
    S.lab8_ker_permHom_le_pCore J ⟨⟨l * l', hll⟩, (TL4.AECov.mem_ker_permHom J).mpr (by
      show permQ m (J.φ ⟨l * l', hll⟩) = 1
      rw [hI]; rfl), rfl⟩
  have hu1 : l * l' ≠ 1 := by
    intro h1
    apply AE.vbar_pairVec_ne_one (by omega) hac
    rw [← hI]
    have : (⟨l * l', hll⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) = 1 := Subtype.ext h1
    rw [this, map_one]
  have huz : l * l' ≠ z := by
    intro h1
    have h2 : AE.mkQ m (ofVec (TL4.pairVec a c)) = AE.zBar α h := by
      rw [← hI, ← hzK]
      exact congrArg J.φ (Subtype.ext h1)
    have h3 : AE.zBar α h = AE.mkQ m (ofVec (fun x => if x ∈ Set.range (AE.emb α h) then 1 else 0)) := by
      show AE.mkQ m (zOf (AE.emb α h)) = _
      rw [TwinThinPf10.zOf_eq_ofVec]
    rw [h3, TwinThinPf18.mkQ_ofVec_eq_iff] at h2
    have hlt : ({a, c} : Finset (Fin m)).card < α.card :=
      lt_of_le_of_lt Finset.card_le_two (by omega)
    obtain ⟨d, hdα, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    have hrange : ∀ x, x ∈ Set.range (AE.emb α h) ↔ x ∈ α := fun x => by
      rw [AE.range_emb]; exact Finset.mem_coe
    rcases h2 with h2 | h2
    · have := h2 d
      simp [TL4.pairVec_apply, hd.1, hd.2, hrange, hdα] at this
    · have := h2 a
      simp [TL4.pairVec_apply, hac, hrange, ha] at this
  refine ⟨l * l', a, c, ha, hc, hac, ⟨Subgroup.mul_mem_sup hl hl', huO, huu, hu1, huz⟩, ?_, hll, hI⟩
  intro x hx
  calc x * (l * l') = (x * l) * l' := by group
    _ = (l * x) * l' := by rw [hlX x hx]
    _ = l * (x * l') := by group
    _ = l * (l' * x) := by rw [hl'X x hx]
    _ = (l * l') * x := by group

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
