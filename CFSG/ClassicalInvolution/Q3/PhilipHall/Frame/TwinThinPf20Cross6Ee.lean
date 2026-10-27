module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Q8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Loc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf15Ker
public import CFSG.ClassicalInvolution.Q3.TL4AECoverH
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

section General

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_conj_mem_self {H : Subgroup G} {y : G} (hy : y ∈ H) {p : G}
    (hp : p ∈ pCoreOf 2 H) : y * p * y⁻¹ ∈ pCoreOf 2 H := by
  have hT := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 H H le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hpH : p ∈ H := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H hp
  have := hT.conj_mem ⟨p, hpH⟩ (Subgroup.mem_subgroupOf.mpr hp) ⟨y, hy⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem pCoreOf_conj_mem {H : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (H : Set G)) {x : G}
    (hx : x ∈ pCoreOf 2 H) : c * x * c⁻¹ ∈ pCoreOf 2 H := by
  set P₂ := pCoreOf 2 H with hP₂
  have hHn : ∀ y, y ∈ H ↔ c * y * c⁻¹ ∈ H := fun y => Subgroup.mem_normalizer_iff.mp hc y
  have hQH : conjSub c P₂ ≤ H := by
    intro q hq
    rw [mem_conjSub_iff] at hq
    have h1 : c⁻¹ * q * c ∈ H := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H hq
    have h2 := (hHn _).mp h1
    have e : c * (c⁻¹ * q * c) * c⁻¹ = q := by group
    rwa [e] at h2
  have hQn : ∀ y ∈ H, ∀ q ∈ conjSub c P₂, y * q * y⁻¹ ∈ conjSub c P₂ := by
    intro y hy q hq
    rw [mem_conjSub_iff] at hq ⊢
    have hy' : c⁻¹ * y * c ∈ H := by
      have := (hHn (c⁻¹ * y * c)).mpr (by
        have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
        rw [e]; exact hy)
      exact this
    have e : c⁻¹ * (y * q * y⁻¹) * c = (c⁻¹ * y * c) * (c⁻¹ * q * c) * (c⁻¹ * y * c)⁻¹ := by group
    rw [e]
    exact pCoreOf_conj_mem_self hy' hq
  have hQ2 : IsPGroup 2 ↥(conjSub c P₂) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.equivMapOfInjective P₂ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)
  have hle := Cross.le_pCoreOf_of_inv hQH hQn hQ2
  exact hle (conj_mem_conjSub hx)

theorem inducedBy_of_mem {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) {c : G}
    (hc : c ∈ pSpan P) {w : Wr n} (hw : I.φ ⟨c, hc⟩ = AE.mkQ n w) : Cross.InducedBy I c w := by
  intro x y hxy
  have e : y = (⟨c, hc⟩ : ↥(pSpan P)) * x * (⟨c, hc⟩ : ↥(pSpan P))⁻¹ := Subtype.ext hxy
  rw [e, map_mul, map_mul, map_inv, hw]

theorem comm_ker_of_pCore {P : Set (Subgroup G)} {k : ℕ} (hk : 5 ≤ k) (I : AEIdent P k) {x y : G}
    (hx : x ∈ pCoreOf 2 (pSpan P)) (hy : y ∈ pCoreOf 2 (pSpan P)) :
    ∃ hc : x * y * x⁻¹ * y⁻¹ ∈ pSpan P, I.φ ⟨x * y * x⁻¹ * y⁻¹, hc⟩ = 1 := by
  obtain ⟨hxP, v₁, hv₁⟩ := Cross.exists_vec_of_pCore hk I hx
  obtain ⟨hyP, v₂, hv₂⟩ := Cross.exists_vec_of_pCore hk I hy
  have hc : x * y * x⁻¹ * y⁻¹ ∈ pSpan P :=
    mul_mem (mul_mem (mul_mem hxP hyP) (inv_mem hxP)) (inv_mem hyP)
  refine ⟨hc, ?_⟩
  have e : (⟨x * y * x⁻¹ * y⁻¹, hc⟩ : ↥(pSpan P)) =
      ⟨x, hxP⟩ * ⟨y, hyP⟩ * ⟨x, hxP⟩⁻¹ * ⟨y, hyP⟩⁻¹ := rfl
  have hcomm : ofVec v₁ * ofVec v₂ = ofVec v₂ * (ofVec v₁ : Wr k) := by
    rw [TL4.ofVec_mul_ofVec, TL4.ofVec_mul_ofVec, add_comm]
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hv₁, hv₂]
  simp only [← map_inv, ← map_mul]
  rw [hcomm]
  simp

theorem sq_ker_of_pCore {P : Set (Subgroup G)} {k : ℕ} (hk : 5 ≤ k) (I : AEIdent P k) {x : G}
    (hx : x ∈ pCoreOf 2 (pSpan P)) :
    ∃ hc : x * x ∈ pSpan P, I.φ ⟨x * x, hc⟩ = 1 := by
  obtain ⟨hxP, v₁, hv₁⟩ := Cross.exists_vec_of_pCore hk I hx
  have hc : x * x ∈ pSpan P := mul_mem hxP hxP
  refine ⟨hc, ?_⟩
  have e : (⟨x * x, hc⟩ : ↥(pSpan P)) = ⟨x, hxP⟩ * ⟨x, hxP⟩ := rfl
  rw [e, map_mul, hv₁, ← map_mul, TL4.ofVec_mul_ofVec]
  have h0 : (v₁ + v₁ : Fin k → ZMod 2) = 0 := by
    funext i
    exact zmod_two_add_self _
  rw [h0]
  exact (congrArg (AE.mkQ k) (rfl : (ofVec (0 : Fin k → ZMod 2)) = 1)).trans (map_one _)

theorem conj_wc_embed {n : ℕ} (ι : Fin 4 ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range ι) (m' : Wr 4) :
    (twinVec ι j * embed ι yQ) * embed ι m' * (twinVec ι j * embed ι yQ)⁻¹ =
      embed ι ((ofVec (vec4 [0]) * yQ) * m' * (ofVec (vec4 [0]) * yQ)⁻¹) := by
  have hinv : (twinVec ι j)⁻¹ = twinVec ι j := inv_eq_of_mul_eq_one_right (twinVec_mul_self ι j)
  calc (twinVec ι j * embed ι yQ) * embed ι m' * (twinVec ι j * embed ι yQ)⁻¹
      = twinVec ι j * (embed ι yQ * embed ι m' * (embed ι yQ)⁻¹) * (twinVec ι j)⁻¹ := by group
    _ = twinVec ι j * embed ι (yQ * m' * yQ⁻¹) * twinVec ι j := by
        rw [hinv, map_mul, map_mul, map_inv]
    _ = embed ι (ofVec (vec4 [0]) * (yQ * m' * yQ⁻¹) * ofVec (vec4 [0])) :=
        twinVec_conj_embed ι hj _
    _ = _ := by
        rw [mul_inv_rev, TwinThinPf20.ofVec_inv_eq]
        congr 1
        group

end General

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem pCore_comm {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {x y : G}
    (hx : x ∈ pCoreOf 2 (conjSub g (piGen π))) (hy : y ∈ pCoreOf 2 (conjSub g (piGen π))) :
    x * y = y * x := by
  have hP : pCoreOf 2 (pSpan (fam K (conjSub g (piGen π)))) = pCoreOf 2 (conjSub g (piGen π)) := by
    rw [S.fam_gen]
  rw [← hP] at hx hy
  have hxX : x ∈ pSpan (fam K (conjSub g (piGen π))) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _ hx
  have hyX : y ∈ pSpan (fam K (conjSub g (piGen π))) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _ hy
  set T : Subgroup ↥(pSpan (fam K (conjSub g (piGen π)))) :=
    (pCoreOf 2 (pSpan (fam K (conjSub g (piGen π))))).subgroupOf
      (pSpan (fam K (conjSub g (piGen π)))) with hT
  have hTn : T.Normal := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2
    (pSpan (fam K (conjSub g (piGen π)))) (pSpan (fam K (conjSub g (piGen π)))) le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hT2 : IsPGroup 2 ↥T :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2
      (pSpan (fam K (conjSub g (piGen π))))).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2
          (pSpan (fam K (conjSub g (piGen π)))))).symm
  have h := TL4.aeCoverElemO2_proved G _ m J hm (S.aeCoverHyp hm hm8 J) T hTn hT2
    ⟨x, hxX⟩ hx ⟨y, hyX⟩ hy
  exact congrArg Subtype.val h.1

theorem exists_cprime {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {u : G}
    (huO : u ∈ pCoreOf 2 (conjSub g (piGen π))) (hu' : u ∈ pSpan (fam K (conjSub g (piGen π))))
    {a c : Fin m} (hφu : J.φ ⟨u, hu'⟩ = AE.mkQ m (ofVec (TL4.pairVec a c)))
    (U : Finset (Fin m)) (hU : U.card = 4) (haU : a ∉ U) (hcU : c ∉ U) :
    ∃ (c' : G) (hc' : c' ∈ pSpan (fam K (conjSub g (piGen π)))), c' * u = u * c' ∧
      J.φ ⟨c', hc'⟩ = AE.mkQ m (twinVec (AE.emb U hU) a * embed (AE.emb U hU) yQ) := by
  classical
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  set ι := AE.emb U hU with hι
  have hrange : ∀ x, x ∈ Set.range ι ↔ x ∈ U := fun x => by
    rw [hι, AE.range_emb]; exact Finset.mem_coe
  obtain ⟨y', hyφ, a₃, hy3⟩ : ∃ y' : ↥(pSpan (fam K (conjSub g (piGen π)))),
      J.φ y' = AE.yBar U hU ∧ ∃ a₃ : ℕ, y' ^ 3 ^ a₃ = 1 := by
    have hmem : AE.yBar U hU ∈ J.φ.range := by
      rw [J.range_eq]; exact AE.yBar_mem U hU
    exact J.exists_lift_pow_three hmem (AE.yBar_pow_three U hU)
  have hyu : (y' : G) * u = u * (y' : G) := by
    have hcomm : J.φ y' * J.φ ⟨u, hu'⟩ = J.φ ⟨u, hu'⟩ * J.φ y' := by
      rw [hyφ, hφu]
      show AE.mkQ m (yOf ι) * AE.mkQ m (ofVec (TL4.pairVec a c)) =
        AE.mkQ m (ofVec (TL4.pairVec a c)) * AE.mkQ m (yOf ι)
      rw [← map_mul, ← map_mul]
      congr 1
      have h1 := TwinThinPf10.conj_ofVec (yOf ι) (TL4.pairVec a c)
      have h2 : (fun x => TL4.pairVec a c ((yOf ι).perm.symm x)) = TL4.pairVec a c := by
        funext x
        by_cases hx : x ∈ Set.range ι
        · obtain ⟨i, rfl⟩ := hx
          have hxa : ι i ≠ a := fun h => haU (h ▸ (hrange _).mp ⟨i, rfl⟩)
          have hxc : ι i ≠ c := fun h => hcU (h ▸ (hrange _).mp ⟨i, rfl⟩)
          have hs : (yOf ι).perm.symm (ι i) ∈ Set.range ι := by
            show (embedPerm ι yQ.perm).symm (ι i) ∈ Set.range ι
            rw [embedPerm_symm_apply]
            exact ⟨_, rfl⟩
          obtain ⟨j, hj⟩ := hs
          rw [← hj]
          have hja : ι j ≠ a := fun h => haU (h ▸ (hrange _).mp ⟨j, rfl⟩)
          have hjc : ι j ≠ c := fun h => hcU (h ▸ (hrange _).mp ⟨j, rfl⟩)
          simp [TL4.pairVec_apply, hxa, hxc, hja, hjc]
        · have : (yOf ι).perm.symm x = x := by
            show (embedPerm ι yQ.perm).symm x = x
            exact embedPerm_symm_of_not_mem ι _ hx
          rw [this]
      rw [h2] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1)
    have := hk
    have h3 := J.comm_of_pow_three hk hy3 (w := ⟨u, hu'⟩) hcomm
    exact congrArg Subtype.val h3
  have hak : a ∉ Set.range ι := fun h => haU ((hrange a).mp h)
  obtain ⟨e, heφ⟩ : ∃ e : ↥(pSpan (fam K (conjSub g (piGen π)))),
      J.φ e = AE.mkQ m (twinVec ι a) := by
    have hmem : AE.mkQ m (twinVec ι a) ∈ J.φ.range := by
      rw [J.range_eq]
      exact ⟨_, (twinVec_mem ι hak ⊤).1, rfl⟩
    obtain ⟨e, he⟩ := hmem
    exact ⟨e, he⟩
  have heO : (e : G) ∈ pCoreOf 2 (conjSub g (piGen π)) :=
    S.lab8_ker_permHom_le_pCore J ⟨e, (TL4.AECov.mem_ker_permHom J).mpr (by
      rw [heφ]; rfl), rfl⟩
  have heu : (e : G) * u = u * (e : G) := S.pCore_comm hm hm8 J heO huO
  refine ⟨(e : G) * (y' : G), mul_mem e.2 y'.2, ?_, ?_⟩
  · calc (e : G) * (y' : G) * u = (e : G) * ((y' : G) * u) := by group
      _ = (e : G) * (u * (y' : G)) := by rw [hyu]
      _ = ((e : G) * u) * (y' : G) := by group
      _ = (u * (e : G)) * (y' : G) := by rw [heu]
      _ = u * ((e : G) * (y' : G)) := by group
  · have e1 : (⟨(e : G) * (y' : G), mul_mem e.2 y'.2⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) =
        e * y' := rfl
    rw [e1, map_mul, heφ, hyφ]
    show AE.mkQ m (twinVec ι a) * AE.mkQ m (yOf ι) = _
    rw [← map_mul]
    rfl

theorem conjSub_mem_pair {m : ℕ} (hm : 5 ≤ m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    {g₀ : G} (hN : g₀ ∈ Subgroup.normalizer (pSpan (fam K (conjSub g (piGen π))) : Set G))
    (hfam : ∀ L ∈ fam K (conjSub g (piGen π)), conjSub g₀ L ∈ fam K (conjSub g (piGen π)))
    {w : Wr m} (hw : Cross.InducedBy J g₀ w) (U : Finset (Fin m)) (hU : U.card = 4)
    (hp : ∀ x, x ∈ U ↔ w.perm x ∈ U) {Lp Lm : Subgroup G}
    (hLp : Lp ∈ fam K (conjSub g (piGen π))) (hLm : Lm ∈ fam K (conjSub g (piGen π)))
    (hlabp : (Lp.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar U hU true)
    (hlabm : (Lm.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar U hU false)
    {L : Subgroup G} (hL : L = Lp ∨ L = Lm) :
    conjSub g₀ L = Lp ∨ conjSub g₀ L = Lm := by
  have key : ∀ (L : Subgroup G), L ∈ fam K (conjSub g (piGen π)) → ∀ c : Bool,
      (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar U hU c →
      conjSub g₀ L = Lp ∨ conjSub g₀ L = Lm := by
    intro L hL c hlab
    obtain ⟨c', hc'⟩ := TwinThinPf20.conj_memBar_of_preserves hm U hU w hp c
    have himg := Cross.map_conjSub_of_induced J hN hw L
    rw [hlab, hc'] at himg
    have hmem := hfam L hL
    cases c'
    · right
      exact S.eq_of_map_le hm J hmem hLm (le_of_eq (himg.trans hlabm.symm))
    · left
      exact S.eq_of_map_le hm J hmem hLp (le_of_eq (himg.trans hlabp.symm))
  rcases hL with rfl | rfl
  · exact key _ hLp true hlabp
  · exact key _ hLm false hlabm

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
