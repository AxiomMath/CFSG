module

public import CFSG.CGT.PushingUpLit.CGT6.EmbConcl
public import CFSG.CGT.PushingUpLit.CGT6.EmbHol
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatAmb
public import CFSG.CGT.PushingUpLit.CGT6.EmbeddingNodes
public import CFSG.CGT.PushingUpLit.CGT6.OmegaModel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.SixThree
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem not_isPGroup_autOn {V Y : Subgroup G} [V.Normal] (hY : InClassX ↥Y)
    (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) : ¬ IsPGroup 2 ↥(autOn Y V) := by
  intro h
  refine InClassX.not_isPGroup hY ?_
  have hK : Y ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn Y := inf_centralizer_le_oTwoIn hY hU
  intro y
  have hy : ambRho V y ∈ autOn Y V := by
    rw [← map_ambRho V Y]
    exact ⟨y, y.2, rfl⟩
  obtain ⟨k, hk⟩ := h ⟨ambRho V y, hy⟩
  have hk' : ambRho V ((y : G) ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have hker : (y : G) ^ 2 ^ k ∈ oTwoIn Y :=
    hK ⟨Y.pow_mem y.2 _, by rw [← ker_ambRho V]; exact hk'⟩
  obtain ⟨j, hj⟩ := SixThree.isPGroup_oTwoIn Y ⟨_, hker⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have := congrArg Subtype.val hj
  simpa [pow_add, pow_mul] using this

omit [Finite G] in
theorem conjClosure_le_of_map_eq {G' : Type*} [Group G'] {Y Xt : Subgroup G} (ρ : G →* G')
    (hCN : ρ.ker ≤ Subgroup.normalizer (Y : Set G)) (hXt : Xt ≤ (Y.map ρ).comap ρ) :
    conjClosure Y Xt ≤ Y := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  obtain ⟨y₀, hy₀, h0⟩ := Subgroup.mem_comap.mp (hXt hg)
  have hc : y₀⁻¹ * g ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h0, inv_mul_cancel]
  have hcn : y₀⁻¹ * g ∈ Subgroup.normalizer (Y : Set G) := hCN hc
  have e : g * y * g⁻¹ = y₀ * ((y₀⁻¹ * g) * y * (y₀⁻¹ * g)⁻¹) * y₀⁻¹ := by group
  rw [e]
  exact Y.mul_mem (Y.mul_mem hy₀ ((Subgroup.mem_normalizer_iff.mp hcn y).mp hy)) (Y.inv_mem hy₀)

omit [Finite G] in
theorem isSubnormal_comap_ambRho {V : Subgroup G} [V.Normal] {Xh : Subgroup (MulAut ↥V)}
    (hs : (Xh.subgroupOf (autOn (⊤ : Subgroup G) V)).IsSubnormal) :
    (Xh.comap (ambRho V)).IsSubnormal := by
  have : Xh.comap (ambRho V) = (Xh.subgroupOf (autOn (⊤ : Subgroup G) V)).comap (ambRhoHat V) := by
    ext g
    rfl
  rw [this]
  exact hs.comap _

omit [Finite G] in
theorem isSubnormal_conjClosure {Y Xt : Subgroup G} (hY : Y ≤ Xt) (hXt : Xt.IsSubnormal) :
    (conjClosure Y Xt).IsSubnormal :=
  Subgroup.IsSubnormal.trans (conjClosure_le hY)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (conjClosure_le hY)).mpr
      le_normalizer_conjClosure).isSubnormal hXt

end Helpers

@[expose] def NatOmega {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V) (n : ℕ)
    (Xh : Subgroup (MulAut ↥V)) : Prop :=
  @IsNatSectionBy ↥V (commGroupOfElemAbelian hV) _ _ _ _ (omegaPlusAct n) Xh
      (@commV ↥V (commGroupOfElemAbelian hV) Xh) ⊥ ∨
    @IsNatSectionBy ↥V (commGroupOfElemAbelian hV) _ _ _ _ (omegaMinusAct n) Xh
      (@commV ↥V (commGroupOfElemAbelian hV) Xh) ⊥

section Concl

variable {G : Type} [Group G] [Finite G]

theorem emb_concl (hMinus : EmbDictMinus) (hArrow : EmbDictArrow) (hOmega : EmbOmega)
    (hchar : IsCharacteristicP 2 G) {Y V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
    (hY : InClassX ↥Y) (hVY : V ≤ Subgroup.normalizer (Y : Set G)) (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆)
    (hQU : ⁅pCore 2 G ⊓ Subgroup.centralizer (V : Set G), Y⁆ = ⁅oTwoIn Y, Y⁆)
    (hCY : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y)
    (Xh : Subgroup (MulAut ↥V)) (hYX : autOn Y V ≤ Xh) (hXG : Xh ≤ autOn (⊤ : Subgroup G) V)
    (hXs : (Xh.subgroupOf (autOn (⊤ : Subgroup G) V)).IsSubnormal)
    (hout : (InClassX ↥(yuHolOf hV Xh) ∧ ArrowNat (yuHolOf hV (autOn Y V)) (yuHolOf hV Xh)) ∨
      (⁅Y, Y⁆ = Y ∧ ∃ n : ℕ, 2 ≤ n ∧ NatOmega hV n Xh ∧
        (autOn Y V = Xh ∨ (Nonempty (↥(autOn Y V) ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
          Nat.card ↥(@commV ↥V (commGroupOfElemAbelian hV) (autOn Y V)) = 2 ^ (3 * n))))) :
    ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧
      Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
      IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) ∧
      ((InClassX ↥X ∧ ⁅oTwoIn X, X⁆ ≤ V ∧ ArrowNat Y X) ∨ OmegaFourOutcome V Y X) := by
  classical
  have hNo : SubTwo.NoTwoQuotient Y := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hYhat : (Y.map (ambRho V)) = autOn Y V := map_ambRho V Y
  have hYXt : Y ≤ Xh.comap (ambRho V) := fun y hy => by
    apply hYX
    rw [← hYhat]
    exact ⟨y, hy, rfl⟩
  have hCXt : Subgroup.centralizer (V : Set G) ≤ Xh.comap (ambRho V) :=
    centralizer_le_comap_ambRho V Xh
  have hXtsub : (Xh.comap (ambRho V)).IsSubnormal := isSubnormal_comap_ambRho hXs
  have hXle : conjClosure Y (Xh.comap (ambRho V)) ≤ Xh.comap (ambRho V) := conjClosure_le hYXt
  have hXsub : (conjClosure Y (Xh.comap (ambRho V))).IsSubnormal :=
    isSubnormal_conjClosure hYXt hXtsub
  have hCX : Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer (conjClosure Y (Xh.comap (ambRho V)) : Set G) :=
    hCXt.trans le_normalizer_conjClosure
  obtain ⟨hQXV, hXCQ, hXCX⟩ := emb_conj_facts (Xt := Xh.comap (ambRho V)) hchar (hQU.trans hU.symm)
  have hX2 : IsPGroup 2 ↥(conjClosure Y (Xh.comap (ambRho V)) ⊓ Subgroup.centralizer (V : Set G)) :=
    (pCore_isPGroup (p := 2) (G := G)).to_le hXCQ
  have hres : oResidualTwo ↥(conjClosure Y (Xh.comap (ambRho V))) = ⊤ :=
    oResidualTwo_conjClosure hNo
  have hfit : generalizedFitting ↥(conjClosure Y (Xh.comap (ambRho V))) =
      pCore 2 ↥(conjClosure Y (Xh.comap (ambRho V))) :=
    generalizedFitting_eq_pCore_of_isSubnormal hchar hXsub
  have hρX : (conjClosure Y (Xh.comap (ambRho V))).map (ambRho V) ≤ Xh :=
    Subgroup.map_le_iff_le_comap.mpr hXle
  have hρY : Y.map (ambRho V) ≤ (conjClosure Y (Xh.comap (ambRho V))).map (ambRho V) :=
    Subgroup.map_mono le_conjClosure
  have hρXn : (((conjClosure Y (Xh.comap (ambRho V))).map (ambRho V)).subgroupOf Xh).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hρX]
    intro xh hxh
    have h1 : xh ∈ autOn (⊤ : Subgroup G) V := hXG hxh
    rw [← map_ambRho V ⊤] at h1
    obtain ⟨g, -, rfl⟩ := h1
    exact map_mem_normalizer_map (ambRho V) (le_normalizer_conjClosure (show g ∈ Xh.comap (ambRho V) from hxh))
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hVX : V ≤ Subgroup.normalizer (conjClosure Y (Xh.comap (ambRho V)) : Set G) :=
    hVC.trans hCX
  have hkerN : (ambRho V).ker ≤ Subgroup.normalizer (Y : Set G) := by
    rw [ker_ambRho V]
    exact fun c hc => (hCY hc).1
  have hXYimp : autOn Y V = Xh → conjClosure Y (Xh.comap (ambRho V)) ≤ Y := by
    intro hEq
    refine conjClosure_le_of_map_eq (ambRho V) hkerN (fun g hg => ?_)
    have h1 : ambRho V g ∈ Xh := hg
    rw [← hEq, ← hYhat] at h1
    exact h1
  have hperfX : ⁅Y, Y⁆ = Y → ⁅conjClosure Y (Xh.comap (ambRho V)),
      conjClosure Y (Xh.comap (ambRho V))⁆ = conjClosure Y (Xh.comap (ambRho V)) :=
    commutator_conjClosure_eq_self
  have hYXc : Y ≤ conjClosure Y (Xh.comap (ambRho V)) := le_conjClosure
  refine ⟨conjClosure Y (Xh.comap (ambRho V)), le_conjClosure, hXsub, hCX, hX2, ?_⟩
  generalize conjClosure Y (Xh.comap (ambRho V)) = X at *
  rcases hout with ⟨hXhat, harr⟩ | ⟨hYperf, n, hn, hnat, hYX2⟩
  ·
    left
    have hnot : ¬ IsPGroup 2 ↥(X.map (ambRho V)) := fun h => by
      have := h.to_le hρY
      rw [hYhat] at this
      exact not_isPGroup_autOn hY hU this
    have hXeq : X.map (ambRho V) = Xh :=
      @eq_of_inClassX_yuHol ↥V (commGroupOfElemAbelian hV) _ _ _ hρX hρXn hXhat hnot
    have hXhat' : autOn X V = Xh := (map_ambRho V X).symm.trans hXeq
    have hXcl : InClassX ↥(yuHolOf hV (autOn X V)) := by
      rw [hXhat']
      exact hXhat
    obtain ⟨hXc, hUX⟩ := hMinus G V X hV hVX hX2 hres hfit hXCX hXcl
    refine ⟨hXc, hUX.le.trans (Subgroup.commutator_le_left V X), ?_⟩
    by_cases hyu : yuHolOf hV (autOn Y V) = yuHolOf hV (autOn X V)
    · have hEq : autOn Y V = autOn X V := @yuHol_inj ↥V (commGroupOfElemAbelian hV) _ _ hyu
      exact Or.inl (le_antisymm hYXc (hXYimp (hEq.trans hXhat')))
    · refine hArrow G V Y X hV hYXc hY hXc hVY hU hVX hUX.symm hX2 hyu ?_
      rw [hXhat']
      exact harr
  · by_cases hEq : autOn Y V = Xh
    ·
      have hXeqY : X = Y := le_antisymm (hXYimp hEq) hYXc
      rw [hXeqY]
      left
      exact ⟨hY, by rw [← hU]; exact Subgroup.commutator_le_left V Y, Or.inl rfl⟩
    ·
      right
      obtain ⟨hSL, hcard⟩ := hYX2.resolve_left hEq
      have hΩ := @hOmega ↥V (commGroupOfElemAbelian hV) _ hV2 Xh (autOn Y V) n hn hnat hYX hEq
        hSL hcard
      have hXeq : X.map (ambRho V) = Xh := hΩ.1 _ (by rw [← hYhat]; exact hρY) hρX hρXn
      have hXhat' : autOn X V = Xh := (map_ambRho V X).symm.trans hXeq
      have hnat' : NatOmega hV n (autOn X V) := by
        rw [hXhat']
        exact hnat
      have : NeZero n := ⟨by omega⟩
      have key : (IsNatBy (omegaPlusAct n) X ⁅X, V⁆ ∨ IsNatBy (omegaMinusAct n) X ⁅X, V⁆) ∧
          (⁅X, V⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
          X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) ≤
            Subgroup.centralizer (V : Set G) := by
        rcases hnat' with h | h
        · obtain ⟨h1, h2, h3⟩ := isNatBy_of_isNatSectionBy hV
            (fun s hs => omegaPlusAct_faithful hs) (fun m hm => omegaPlusAct_fixed hm) h
          exact ⟨Or.inl h1, h2, h3⟩
        · obtain ⟨h1, h2, h3⟩ := isNatBy_of_isNatSectionBy hV
            (fun s hs => omegaMinusAct_faithful hs) (fun m hm => omegaMinusAct_fixed hm) h
          exact ⟨Or.inr h1, h2, h3⟩
      refine ⟨hres, hperfX hYperf, n, hn, key.1, key.2.1, key.2.2, ?_⟩
      intro hsn
      apply hΩ.2
      have h1 : ((Y.map (ambRho V)).subgroupOf (X.map (ambRho V))).IsSubnormal := by
        let f : ↥X →* ↥(X.map (ambRho V)) :=
          ((ambRho V).comp X.subtype).codRestrict (X.map (ambRho V)) fun x => ⟨x, x.2, rfl⟩
        have hf : Function.Surjective f := by
          rintro ⟨_, ⟨x, hx, rfl⟩⟩
          exact ⟨⟨x, hx⟩, rfl⟩
        have hmap : (Y.subgroupOf X).map f = (Y.map (ambRho V)).subgroupOf (X.map (ambRho V)) := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x, hx, rfl⟩
          · intro hz
            obtain ⟨y, hy, hyz⟩ := hz
            exact ⟨⟨y, hYXc hy⟩, hy, Subtype.ext hyz⟩
        rw [← hmap]
        exact Subgroup.IsSubnormal.map hf hsn
      rw [hXeq, hYhat] at h1
      exact h1

end Concl

end CFSG.CGT.PushingUpLit.CGT6
