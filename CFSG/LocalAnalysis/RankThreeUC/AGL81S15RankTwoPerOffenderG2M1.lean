module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderCommQuasi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2OneFactor
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base1
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules Matrix
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.Ch11.SecB.K5
open scoped IsMulCommutative

theorem exists_mat_g2_of_natural {G : Type*} [Group G] {L : Subgroup G} {F : Type} [Field F]
    [CharP F 2] (e : ↥L ≃* ↥(cayleyGroup F)) :
    ∃ (Mat : ↥L →* Matrix.GeneralLinearGroup (Fin 6) F) (P : (Ix3 → F) ≃+ (Fin 6 → F)),
      Function.Injective Mat ∧ Mat.range = (g2Six (K := F)).range ∧
      ∀ (l : ↥L) (w : Ix3 → F),
        P (g2Act (e l) w) = (Mat l : Matrix (Fin 6) (Fin 6) F) *ᵥ P w := by
  let Mat : ↥L →* Matrix.GeneralLinearGroup (Fin 6) F := g2Six.comp e.toMonoidHom
  let P : (Ix3 → F) ≃+ (Fin 6 → F) := (LinearEquiv.funCongrLeft F F e6.symm).toAddEquiv
  refine ⟨Mat, P, ?_, ?_, ?_⟩
  · exact g2Six_injective.comp e.injective
  · ext g
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨e l, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨e.symm h, by simp [Mat]⟩
  · intro l w
    have h1 : ((g2Six (e l) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        ((g2Mat (e l) : GL Ix3 F) : Matrix Ix3 Ix3 F).submatrix e6.symm e6.symm := rfl
    change P (g2Act (e l) w) = ((g2Six (e l) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ P w
    rw [h1, Matrix.submatrix_mulVec_equiv]
    funext i
    have hP : ∀ v : Ix3 → F, P v = v ∘ e6.symm := fun v => by
      funext j
      simp [P, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    rw [hP, hP, ← g2Mat_mulVec]
    simp [Function.comp_def]

theorem exists_natQuot_g2
    {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥L) {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* ↥(cayleyGroup F)) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hbest : IsBestOffenderOn ρ A ⊤)
    (hnot : ¬ A ≤ L ⊔ Subgroup.centralizer (L : Set G)) :
    ∃ N : NatQuot ρ L F 6, N.Mat.range = (g2Six (K := F)).range ∧
      (∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2) {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x}) ∧
      ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I := by
  classical
  have hntL : Nontrivial ↥L := by
    have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L ⧸ Subgroup.center ↥L)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) x
    exact ⟨y, 1, fun h => hx (by rw [← hy, h, map_one])⟩
  have hLA : ⁅L, A⁆ = L := commutator_eq_of_isQuasisimple_of_not_le hq hAN hnot
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    have hbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply hfaith
      ext v
      rw [map_one, Module.End.one_apply]
      exact (h hl).2 v Submodule.mem_top
    exact (Subgroup.nontrivial_iff_ne_bot L).mp hntL hbot
  have hA2 : CFSG.IsElementaryAbelian 2 A := by
    refine (isElemAbelianOn_top_iff (ρ := ρ) (A := A) ?_).mpr hbest.1
    intro a ha hfix
    apply hfaith
    ext v
    rw [map_one, Module.End.one_apply]
    exact hfix v
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbestB, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hbest
  have hBNsub : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hBNmem : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun b hb l hl =>
    (Subgroup.mem_normalizer_iff.mp (hBNsub hb) l).mp hl
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    have h : b ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
    simpa [pow_two] using h
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun a ha c hc => hAc a (hBA ha) c (hBA hc)
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hinner : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l :=
    strictMin_inner_g2 hn hFc ρ L B
      (e.trans (MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup.symm))
      hq hBNmem hB2 hBc hUinv hLU hbestB hquad hmove
  obtain ⟨r, Vs, i₀, φ, hVs, htriv, hnat⟩ :=
    exists_series_natural_factor_g2 ρ L B hn hF e hq.1 hq.2 hB2 hBc hinner
      (U := commOn ρ L ⊤) le_rfl hUinv hbestB hmove hBU
  obtain ⟨Mat, P, hMatinj, hrange, hP⟩ := exists_mat_g2_of_natural (G := G) (L := L) e
  let φ' : ((Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)) ≃+ (Fin 6 → F) :=
    φ.trans P
  have hφ' : ∀ (l : ↥L)
      (x : (Vs i₀.succ).toSubmodule ⧸ factorSub (Vs i₀.castSucc) (Vs i₀.succ)),
      φ' (factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x) =
        (Mat l : Matrix (Fin 6) (Fin 6) F) *ᵥ φ' x := by
    intro l x
    have h1 := hnat (e l) x
    rw [MulEquiv.symm_apply_apply] at h1
    change P (φ (factorRep (Vs i₀.castSucc) (Vs i₀.succ) l x)) =
      (Mat l : Matrix (Fin 6) (Fin 6) F) *ᵥ P (φ x)
    rw [h1, hP l (φ x)]
  obtain ⟨N, hNMat, hNI, hNIcomm⟩ :=
    NatQuot.exists_of_series_natural_factor ρ L hq.1 Mat hMatinj Vs hVs i₀ htriv φ' hφ'
  refine ⟨N, ?_, hNIcomm, ?_⟩
  · rw [hNMat, hrange]
  · intro a ha v hv
    rw [hNI] at hv ⊢
    exact isInvariant_commOn_top (ρ := ρ) hAN a ha v hv

end CFSG.LocalAnalysis.RankThreeUC.S15

end
