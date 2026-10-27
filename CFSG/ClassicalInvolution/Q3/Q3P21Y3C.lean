module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y2C
public import CFSG.ClassicalInvolution.Q3.Q3TCD4
public import CFSG.ClassicalInvolution.Q3.Q3TCD4Clique
public import CFSG.ClassicalInvolution.Q3.Q3PAR1
public import CFSG.ClassicalInvolution.Q3.Q3TIVFinal
public import CFSG.ClassicalInvolution.Q3.Q3TPSChart
public import CFSG.ClassicalInvolution.Q3.Q3EXModel
public import CFSG.ClassicalInvolution.Q3.Q3TY12
public import CFSG.ClassicalInvolution.Q3.Q3TIVSm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinRow)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL)
open CFSG.ClassicalInvolution.RouteD.NonClassical (le_centralizer_of_commutes)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)


section Std

theorem conjSub_eq_of_stdPair3 {X : Type} [Group X] [Finite X] {A B : Subgroup X} {t : X}
    (ht : IsClassicalMember3 B t)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W A B) : conjSub t A = A := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨e⟩ := Q3PAR.nonempty_ringEquiv_zmod_three card_gf3
  obtain ⟨θ, -, hker, hU, hV⟩ :=
    WeakCT.pair_normalize (WeakCT.LinearBlockStandardPair.of_ringEquiv e hW)
  have h2 : (2 : F3) ≠ 0 := by decide
  have htmem : t ∈ (blockSL F3 3 2 1 (by omega)).range.map θ := by
    have : t ∈ B := ht.mem
    rwa [← hV] at this
  have hteq : t = θ (b1 (-1)) :=
    Gaps.eq_block_neg_one h2 hker (j := 1) (by omega) htmem ht.orderOf_eq_two
  have hle : conjSub t A ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' := ha
    rw [← hU] at ha'
    obtain ⟨_, ⟨A', rfl⟩, rfl⟩ := ha'
    obtain ⟨B', hB'⟩ := Q3PAR.exists_swap A'
    have key : t * θ (b0 A') * t⁻¹ = θ (b0 B') := by
      rw [hteq, ← map_inv, ← map_mul, ← map_mul, hB', mul_inv_cancel_right]
    show t * θ (b0 A') * t⁻¹ ∈ A
    rw [key, ← hU]
    exact ⟨_, ⟨B', rfl⟩, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).toEquiv).le

end Std

section Chain

theorem clique_comp3 {X : Type} [Group X] (cc : CompData) (hk : cc = CompData.model .POmegaPlus 4)
    (hpc : PowCop3 cc) (φ : cc.G →* X) (hker : φ.ker ≤ Subgroup.center cc.G) {A B C : Subgroup cc.G}
    (hA : A ∈ cc.fund) (hB : B ∈ cc.fund) (hC : C ∈ cc.fund) (hAB : Commutes A B)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (A.map φ) (C.map φ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (B.map φ) (C.map φ) := by
  subst hk
  have : Finite (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial
      statedLieAdmissible_plus4_three
  obtain ⟨W₁, hW₁⟩ := exists_lin_of_map_pow3 (not_three_dvd_card_center_of_cop hpc.cop) φ hker
    (hpc.pow3 A hA) (hpc.pow3 C hC) hlin
  obtain ⟨W₂, hW₂⟩ := d4LinearClique3 A hA B hB C hC hAB ⟨W₁, hW₁⟩
  exact ⟨_, Gaps.linearBlockStandardPair_map φ hker hW₂⟩

theorem chainParity3 (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 2 (CompData.model .PSU 4) (conjClass3 K) z)
    (c : Q3TP.TCtxS3 .PSU 4 (conjClass3 K) K z) {N K₂ : Subgroup G} {t : G}
    (hNΩ : N ∈ conjClass3 K) (hNt : IsClassicalMember3 N t)
    (hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z}) (hK₂K : K₂ ≠ K)
    (hnotTwin : ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T)
    (hKK₂ : Commutes K K₂) (p1 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K N)
    (p2 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₂) :
    ∃ (T K₃ : Subgroup G) (w : G), T ∈ centralizingMembers (conjClass3 K) {z} ∧
      locImg (conjClass3 K) z T ≤ c.d.Q₁ ∧ K₃ ∈ centralizingMembers (conjClass3 K) {z} ∧
      K₃ ≠ K ∧ K₃ ≠ T ∧ K₃ ≠ K₂ ∧ Commutes K₂ K₃ ∧ ¬ locImg (conjClass3 K) z K₂ ≤ c.d.Q₁ ∧
      ¬ locImg (conjClass3 K) z K₃ ≤ c.d.Q₁ ∧ IsClassicalMember3 K₂ w ∧ w * t = t * w ∧
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₃) ∧
      ∀ y : G, y ∈ locLayer (conjClass3 K) z → y * w * y⁻¹ = w →
        K ≤ Subgroup.centralizer ({y} : Set G) → T ≤ Subgroup.centralizer ({y} : Set G) →
        (∀ k ∈ K₂, y * k * y⁻¹ = t * k * t⁻¹) → (∀ k ∈ K₃, y * k * y⁻¹ = t * k * t⁻¹) →
        y * t * y⁻¹ = t := by
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  have hcls : TwinInvolution3 := Q3TIV.twinInvolution3_of_odd3 h3
  obtain ⟨W₁, hW₁⟩ := p1
  obtain ⟨W₂, hW₂⟩ := p2
  have hzt : z * t = t * z := RouteD.Gaps.standardPair_involutions_commute h2 hW₁ hR.cls.mem
    hNt.mem hR.cls.orderOf_eq_two hNt.orderOf_eq_two
  have ht : t * z * t⁻¹ = z := by
    rw [← hzt, mul_inv_cancel_right]
  obtain ⟨w, hw⟩ := hΩ.classical K₂ hK₂.1
  have hwt : w * t = t * w :=
    (RouteD.Gaps.standardPair_involutions_commute h2 hW₂ hNt.mem hw.mem hNt.orderOf_eq_two
      hw.orderOf_eq_two).symm
  have hzw' : z * w = w * z := hKK₂ z hR.cls.mem w hw.mem
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hTK : T ≠ K := c.twin_ne hTz hTQ.le
  have hTcomm : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ T → Commutes T L :=
    fun L hL hLT => c.commutes_T_of_ne hTz hTQ.le hL hLT
  have hTw : IsTwinAt (conjClass3 K) K T z :=
    ⟨hTz, hTK, hTcomm, fun L hL hLK => c.commutes_K_of_ne hL hLK⟩
  have clsT : IsClassicalMember3 T z := hcls G hnab K z hR .PSU 4 hrow hshape T hTw
  have hK₂T : K₂ ≠ T := hnotTwin T hTw
  have hKT : Commutes K T := hTw.comm_K T hTz hTw.ne
  have hTK₂ : Commutes T K₂ := hTcomm K₂ hK₂ hK₂T
  have hK₂Q : ¬ locImg (conjClass3 K) z K₂ ≤ c.d.Q₁ := fun h =>
    hK₂T (c.eq_of_locImg_le_Q₁ hK₂ hTz h hTQ.le)
  obtain ⟨R₀, hR₀, hK₂R⟩ := c.exists_fund_of_ne hK₂ hK₂K hK₂Q
  have hzw : z ≠ w := by
    rintro rfl
    exact Q3TP.not_locImg_eq_map_fund3S c.hY hK₂ hw c.d.ψ c.d.ker_le hR₀ hK₂R
  obtain ⟨hP1x, hO3x⟩ := hP G K z hR K₂ hK₂.1 w hw hKK₂ hzw
  have hNK : N ≠ K := fun e => ne_of_linearBlockStandardPair hW₁ e.symm
  have hKNnc : ¬ Commutes K N := not_commutes_of_linearBlockStandardPair hW₁
  have hNx : N ∈ centralizingMembers (conjClass3 K) {z * w} :=
    ⟨hNΩ, Q3PAR.chain_product_centralizes3 hR.cls hw hKK₂ ⟨W₁, hW₁⟩ ⟨W₂, hW₂⟩⟩
  have hlink : LinkedAtProduct (conjClass3 K) K z w := ⟨N, hNx, hNK, hKNnc⟩
  obtain ⟨ι, -, D, cx, hk, -, hKc, hK₂c, hTc, hallc⟩ :=
    exists_d4_component_of_twin_product3 Q3W.EX.mfTwin3 h3 hnab hR hTz hTK hTcomm hK₂ hK₂K hK₂T
      hw hzw hP1x hO3x hlink
  have hNc : N ∈ compMembers3 (conjClass3 K) (z * w) D cx := hallc N hNx hNK hKNnc
  obtain ⟨cw⟩ := Q3TPS.TCtxS3.exists_ctx_member c hsingle hK₂.1 hw
  obtain ⟨K₃, hK₃w, hK₃Q⟩ := cw.exists_twin
  have hK₃tw : IsTwinAt (conjClass3 K) K₂ K₃ w :=
    ⟨hK₃w, cw.twin_ne hK₃w hK₃Q.le, fun L hL hLT => cw.commutes_T_of_ne hK₃w hK₃Q.le hL hLT,
      fun L hL hLK => cw.commutes_K_of_ne hL hLK⟩
  have hSw : RouteD3Setup K₂ w := RouteD3Setup.of_mem_conjClass3 hR hK₂.1 hw
  have hclsK₂ : conjClass3 K₂ = conjClass3 K := conjClass3_eq_of_mem hK₂.1
  have hshapeK₂ : LocalShapeC3 2 (CompData.model .PSU 4) (conjClass3 K₂) w :=
    localShapeC3_at_member hR hshape hK₂.1 hw
  have hK₃tw' : IsTwinAt (conjClass3 K₂) K₂ K₃ w := by
    rw [hclsK₂]
    exact hK₃tw
  have clsK₃ : IsClassicalMember3 K₃ w := hcls G hnab K₂ w hSw .PSU 4 hrow hshapeK₂ K₃ hK₃tw'
  have hK₃Ω : K₃ ∈ conjClass3 K := hK₃w.1
  have hK₃K : K₃ ≠ K := fun h => hzw (involution_unique3 hR.cls (h ▸ clsK₃))
  have hK₃T : K₃ ≠ T := fun h => hzw (involution_unique3 clsT (h ▸ clsK₃))
  have hKw : K ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hKΩ hw.mem hKK₂
  have hTw' : T ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hTz.1 hw.mem hTK₂
  have hK₃Kc : Commutes K₃ K := hK₃tw.comm_T K hKw hK₃K.symm
  have hK₃Tc : Commutes K₃ T := hK₃tw.comm_T T hTw' hK₃T.symm
  have hK₂K₃ : Commutes K₂ K₃ := hK₃tw.comm_K K₃ hK₃tw.mem hK₃tw.ne
  have hK₃z : K₃ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hK₃Ω hR.cls.mem hK₃Kc
  have hK₃x : K₃ ∈ centralizingMembers (conjClass3 K) {z * w} :=
    ⟨hK₃Ω, fun n hn => mem_centralizer_mul (hK₃z.2 hn) (isSubnormal_le clsK₃.subnormal hn)⟩
  obtain ⟨i₃, hi₃⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₃, hK₃x, rfl⟩)
  have hi₃c : i₃ = cx := by
    by_contra hne
    have hcm := commutes_of_ne_comp3 hΩ hex hP1x hO3x D (Ne.symm hne) hNc ⟨hK₃x, hi₃⟩
    have hNw : N ≤ Subgroup.centralizer ({w} : Set G) := le_centralizer_of_commutes hcm clsK₃.mem
    have hNz : N ≤ Subgroup.centralizer ({z} : Set G) := fun n hn =>
      mem_centralizer_left_of_mul (hNx.2 hn) (hNw hn)
    rcases cp_at_member3 h3 hnab hR hKΩ hR.cls (L := N) ⟨hNΩ, hNz⟩ with hc | he
    · exact hKNnc hc
    · exact hNK he
  have hK₃c : K₃ ∈ compMembers3 (conjClass3 K) (z * w) D cx := ⟨hK₃x, hi₃c ▸ hi₃⟩
  have hpc : PowCop3 (D.kind cx) := (component_facts (D.kind cx) hk).2.1
  obtain ⟨R₂, hR₂⟩ := exists_corr_left3 hΩ hex hP1x hO3x D hK₂c
  obtain ⟨R₃, hR₃⟩ := exists_corr_left3 hΩ hex hP1x hO3x D hK₃c
  obtain ⟨RN, hRN⟩ := exists_corr_left3 hΩ hex hP1x hO3x D hNc
  have hcomm₂₃ : Commutes R₂ R₃ :=
    (corr_commutes3 hΩ hex hP1x hO3x hpc hR₂ hR₃).mp hK₂K₃
  obtain ⟨W₃, hW₃⟩ := Gaps.linearBlockStandardPair_locImg_of_members (p := 3) (f := 1) hP1x
    hK₂c.1 hNc.1 (linearBlockStandardPair_symm hW₂)
  rw [hR₂.2.2, hRN.2.2] at hW₃
  obtain ⟨W₄, hW₄⟩ := clique_comp3 (D.kind cx) hk hpc (D.hom cx) (D.ker_le_center cx) hR₂.2.1
    hR₃.2.1 hRN.2.1 hcomm₂₃ ⟨W₃, hW₃⟩
  rw [← hR₃.2.2, ← hRN.2.2] at hW₄
  obtain ⟨W₅, hW₅⟩ := linearBlockStandardPair_of_locImg3' hΩ hex hP1x hO3x hK₃c.1 hNc.1 hW₄
  have hstdNK₃ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W N K₃ :=
    ⟨W₅, linearBlockStandardPair_symm hW₅⟩
  have hK₃Q : ¬ locImg (conjClass3 K) z K₃ ≤ c.d.Q₁ := fun h =>
    hK₃T (c.eq_of_locImg_le_Q₁ hK₃z hTz h hTQ.le)
  refine ⟨T, K₃, w, hTz, hTQ.le, hK₃z, hK₃K, hK₃T, hK₃tw.ne, hK₂K₃, hK₂Q, hK₃Q, hw, hwt,
    hstdNK₃, ?_⟩
  intro y hy hyw hyK hyT hy₂ hy₃
  have hyz : y * z * y⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer (conjClass3 K) {z} hy)
  have hyx : y * (z * w) * y⁻¹ = z * w := by
    calc y * (z * w) * y⁻¹ = (y * z * y⁻¹) * (y * w * y⁻¹) := by group
      _ = z * w := by rw [hyz, hyw]
  have hwx : w * (z * w) * w⁻¹ = z * w := by
    calc w * (z * w) * w⁻¹ = w * z * (w * w⁻¹) := by group
      _ = z * w := by rw [mul_inv_cancel, mul_one, hzw']
  have htw : t * w * t⁻¹ = w := by
    rw [← hwt, mul_inv_cancel_right]
  have htx : t * (z * w) * t⁻¹ = z * w := by
    calc t * (z * w) * t⁻¹ = (t * z * t⁻¹) * (t * w * t⁻¹) := by group
      _ = z * w := by rw [ht, htw]
  have htK : conjSub t K = K := conjSub_eq_of_stdPair3 hNt ⟨W₁, hW₁⟩
  have htK₂ : conjSub t K₂ = K₂ :=
    conjSub_eq_of_stdPair3 hNt ⟨W₂, linearBlockStandardPair_symm hW₂⟩
  exact parity_element3 hΩ hex hP1x hO3x D hk hKc hTc hK₂c hK₃c hNc hTK.symm hKT
    hK₃tw.ne.symm hKK₂ hK₃Kc.symm hTK₂ hK₃Tc.symm hw hNt hwx htx hwt htK htK₂ hyx hyK hyT hy₂ hy₃

end Chain

end CFSG.ClassicalInvolution.Q3.Q3P21
