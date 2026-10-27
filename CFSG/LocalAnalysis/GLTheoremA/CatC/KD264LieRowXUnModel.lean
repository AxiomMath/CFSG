module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarQuotient
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

abbrev xunK : Type := GaloisField 2 (2 * 1)

theorem xunK_card : Nat.card xunK = 2 ^ (2 * 1) :=
  GaloisField.card 2 (2 * 1) (by norm_num)

noncomputable def xunH : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 xunK :=
  ⟨Nat.prime_two, le_rfl, xunK_card⟩

abbrev xunM (N : ℕ) : Type := StatedProj (StatedSU N (2 ^ 1) xunK)

@[expose] noncomputable def xunConj (N : ℕ) (hN : 1 ≤ N) : uU xunH N →* MulAut (xunM N) :=
  uConjAut xunH hN

theorem isGood_iff_map_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) (F : Subgroup (MulAut S)) :
    IsGood 3 F ↔ IsGood 3 (F.map (MulAut.congr e).toMonoidHom) := by
  have key : (⨅ f ∈ F.map (MulAut.congr e).toMonoidHom, fixSubgroup f) =
      (⨅ f ∈ F, fixSubgroup f).map e.toMonoidHom := by
    apply le_antisymm
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      refine Subgroup.mem_iInf.2 fun f => Subgroup.mem_iInf.2 fun hf => ?_
      have hx' : x ∈ fixSubgroup (MulAut.congr e f) :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx (MulAut.congr e f))
          (Subgroup.mem_map_of_mem _ hf)
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr] at hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have hyeq : y = e.symm x := by
        rw [← hyx]
        simp
      rw [← hyeq]
      exact hy
    · rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.mem_iInf.2 fun g => Subgroup.mem_iInf.2 fun hg => ?_
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hg
      show e y ∈ fixSubgroup (MulAut.congr e f)
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy f) hf)
  unfold IsGood
  rw [key, ← glaPLayer_map_eq_of_injective Nat.prime_three e.toMonoidHom e.injective]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective _ e.injective)).symm

theorem isElemAbelian_map_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ}
    {φ : G →* H} (hφ : Function.Injective φ) {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map φ) := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, φ x * φ y = φ y * φ x := fun x hx y hy => by
    have h1 : (⟨x, hx⟩ : E) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hE.1.is_comm.comm _ _
    have h2 : x * y = y * x := congrArg Subtype.val h1
    rw [← map_mul, ← map_mul, h2]
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    change (a : H) * (b : H) = (b : H) * (a : H)
    rw [← hxa, ← hyb]
    exact hcomm x hx y hy
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem pRank_map_of_injective {G H : Type} [Group G] [Group H] [Finite G] [Finite H] {p : ℕ}
    (hp : p.Prime) {φ : G →* H} (hφ : Function.Injective φ) {E : Subgroup G}
    (hE : IsElemAbelian p E) :
    CFSG.Open.pRank p (E.map φ) = CFSG.Open.pRank p E := by
  have hE' := isElemAbelian_map_of_injective hφ hE
  have h1 := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hE'
  have h2 := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hE
  rw [Subgroup.card_map_of_injective hφ] at h1
  have hk : p ^ CFSG.Open.pRank p (E.map φ) = p ^ CFSG.Open.pRank p E := h1.symm.trans h2
  exact Nat.pow_right_injective hp.two_le hk

theorem projSU_mulEquiv_two_one (N p f : ℕ) [Fact p.Prime] (hp : p = 2) (hf : f = 1) :
    Nonempty (CFSG.PGLModel.projSU N p f ≃* CFSG.PGLModel.projSU N 2 1) := by
  subst hp
  subst hf
  exact ⟨MulEquiv.refl _⟩

theorem nonempty_mulEquiv_xunM (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid) (hq : q.card = 2) :
    Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA n q, hv⟩ ≃* xunM (n + 1)) := by
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq
    (q := q) Nat.prime_two (r := 2) (s := 1) (by norm_num) (by simpa using hq)
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e2⟩ := projSU_mulEquiv_two_one (n + 1) q.p q.exponent h1 h2
  let H : Subgroup (GL (Fin (n + 1)) xunK) := CFSG.Open.StatedSU (n + 1) (2 ^ 1) xunK
  have hPI : CFSG.PGLModel.projImage H = CFSG.PGLModel.projSU (n + 1) 2 1 :=
    CFSG.RankThree.PartTwo.Census.projImage_statedSU (n + 1) 2 1
  let e3 : CFSG.PGLModel.projSU (n + 1) 2 1 ≃* xunM (n + 1) :=
    (MulEquiv.subgroupCongr hPI).symm.trans
      (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage H).symm
  exact ⟨(CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU n q hv).trans
    (e2.trans e3)⟩

theorem mem_range_xunConj_of_pow_three {N : ℕ} (hN : 9 ≤ N) (α : MulAut (xunM N))
    (h3 : α ^ 3 = 1) : ∃ g : uU xunH N, xunConj N (by omega) g = α := by
  have hN3 : 3 ≤ N := by omega
  have hq : ¬(N = 3 ∧ 2 ^ 1 = 2) := fun h => by omega
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut xunH hN3 hq α
  have hφ3 : φ ^ 3 = 1 := by
    have := congrArg (uFactor xunH hN3 hq) h3
    rw [map_pow, hα, uFactor_apply, map_one] at this
    exact this
  rcases CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.ringEquiv_eq_refl_or_bar xunH φ with h1 | h1
  · refine ⟨A, ?_⟩
    have hφ1 : φ = 1 := h1
    subst hφ1
    rw [hα, map_one]
    exact (mul_one _).symm
  · exfalso
    obtain ⟨ω, hω0, hω1⟩ :=
      CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.exists_ne_zero_ne_one xunH
    have hb : ∀ a : xunK, φ a = a ^ 2 := fun a => by
      rw [h1 a, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
      norm_num
    haveI : Fintype xunK := Fintype.ofFinite xunK
    have hcard : Fintype.card xunK = 4 := by
      rw [← Nat.card_eq_fintype_card, xunK_card]
      norm_num
    have hpow : ω ^ 4 = ω := by
      have := FiniteField.pow_card ω
      rw [hcard] at this
      exact this
    have h3ω : φ (φ (φ ω)) = ω := by
      have e3 : (φ ^ 3) ω = φ (φ (φ ω)) := by
        rw [pow_succ, pow_two]
        rfl
      rw [← e3, hφ3]
      rfl
    rw [hb, hb, hb] at h3ω
    have h8 : ω ^ 8 = ω ^ 2 := by
      calc ω ^ 8 = (ω ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ω ^ 2 := by rw [hpow]
        _ = ω ^ 2 := rfl
    rw [show ((ω ^ 2) ^ 2) ^ 2 = ω ^ 8 by ring, h8] at h3ω
    have : ω * (ω - 1) = 0 := by linear_combination h3ω
    rcases mul_eq_zero.1 this with h | h
    · exact hω0 h
    · exact hω1 (sub_eq_zero.1 h)

theorem le_range_xunConj_of_isElemAbelian {N : ℕ} (hN : 9 ≤ N)
    (A : Subgroup (MulAut (xunM N))) (hA : IsElemAbelian 3 A) :
    ∀ a ∈ A, ∃ g : uU xunH N, xunConj N (by omega) g = a := by
  intro a ha
  apply mem_range_xunConj_of_pow_three hN a
  exact hA.2 a ha

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

end
