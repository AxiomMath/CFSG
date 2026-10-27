module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigC4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.innerModOdd_t_t (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayer R t) t := by
  refine innerModOdd_of_actsTriv fun z hz => ?_
  have hzt : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
  rw [show t * z * t⁻¹ * z⁻¹ = 1 by rw [hzt]; group]
  exact Subgroup.one_mem _

theorem Z2SetR.innerModOdd_t_u (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayer R t) u := by
  refine ⟨u, coreAt_le_linkLayerAt hs.hJ (Subgroup.subset_closure
    ⟨⟨hs.hu.mem, Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm.symm⟩,
      Balance.isPGroup_zpowers_of_mul_self_eq_one hs.u2⟩), actsLike_refl _ u⟩

theorem Z2SetR.innerModOdd_u_u (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) u := by
  refine innerModOdd_of_actsTriv fun z hz => ?_
  have hzu : u * z = z * u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
  rw [show u * z * u⁻¹ * z⁻¹ = 1 by rw [hzu]; group]
  exact Subgroup.one_mem _

theorem Z2SetR.innerModOdd_u_t (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) t := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  refine ⟨t, coreAt_le_linkLayerAt hKJ (Subgroup.subset_closure
    ⟨⟨hs.large.datum.isUniqueInvolution_core.mem,
      Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm⟩,
      Balance.isPGroup_zpowers_of_mul_self_eq_one hs.t2⟩), actsLike_refl _ t⟩

theorem Z2SetR.innerModOdd_t_of_mem_omegaNbr (hs : Z2SetR r n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hy : IsUniqueInvolution L y) : InnerModOdd (linkLayer R t) y := by
  have hyL : y ∈ coreAt t L := Subgroup.subset_closure
    ⟨⟨hy.mem, hyA.1.2⟩, Balance.isPGroup_zpowers_of_mul_self_eq_one hy.sq⟩
  refine ⟨y, coreAt_le_linkLayerAt hL hyL, fun z _ => ?_⟩
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem Z2SetR.innerModOdd_u_of_mem_omegaNbr (hs : Z2SetR r n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (hy : IsUniqueInvolution L y) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y := by
  have hyL : y ∈ coreAt u L := Subgroup.subset_closure
    ⟨⟨hy.mem, hyA.2⟩, Balance.isPGroup_zpowers_of_mul_self_eq_one hy.sq⟩
  refine ⟨y, coreAt_le_linkLayerAt hL hyL, fun z _ => ?_⟩
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem Z2SetR.isSylow2In_edgeCent_t (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    IsSylow2In (edgeCent (P : Subgroup Y) t u) (Subgroup.centralizer ({t} : Set Y)) := by
  classical
  have hΩ := hs.large.datum.hypOmegaGen
  have ht := hs.large.datum.isUniqueInvolution_core
  have hTF := TightLargeHypR.typeRFam hs.large
  have hA2 : IsPGroup 2 ↥(edgeCent (P : Subgroup Y) t u) :=
    P.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hT₀A : T₀ ≤ edgeCent (P : Subgroup Y) t u := fun x hx =>
    ⟨⟨hs.hT₀P hx, S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hs.hT₀N hx)⟩,
      hTF.le_centralizer hs.hJ.1 hs.hu (hs.hT₀.1 hx)⟩
  have hfixA : ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      (∀ a ∈ edgeCent (P : Subgroup Y) t u, conjSub a J' = J') → J' = J := by
    intro J' hJ' hfix
    by_contra hne
    have hJJ' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J' :=
      ⟨hs.hJ.1, fun h => hne h.symm, T₀, mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀, hs.hT₀.1,
        fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hfix x (hT₀A hx))⟩
    exact hs.not_mem_omegaNbr_J hJ' (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ'.1 hs.hJ.1 hJJ')
  let act : ∀ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({t} : Set Y) →
      MulAction ↥Q ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :=
    fun Q hQ =>
      { smul := fun q J' => ⟨conjSub (q : Y) J'.1, conjSub_mem_omegaNbr_core hs.large J'.2 (hQ q.2)⟩
        one_smul := fun J' => Subtype.ext (conjSub_one _)
        mul_smul := fun q₁ q₂ J' => Subtype.ext (conjSub_mul _ _ _) }
  have hAt : edgeCent (P : Subgroup Y) t u ≤ Subgroup.centralizer ({t} : Set Y) :=
    inf_le_left.trans inf_le_right
  refine ⟨hAt, hA2, fun V hVt hV2 hAV => ?_⟩
  have hVJ : ∀ v ∈ V, conjSub v J = J := by
    letI := act _ hAt
    letI := act V hVt
    have hFA : MulAction.fixedPoints ↥(edgeCent (P : Subgroup Y) t u)
        ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) = {⟨J, hs.hJ⟩} := by
      ext J'
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro h
        exact Subtype.ext (hfixA J'.1 J'.2 fun a ha => congrArg Subtype.val (h ⟨a, ha⟩))
      · rintro rfl a
        exact Subtype.ext (hs.conjSub_J_fix (conj_eq_of_comm
          (Subgroup.mem_centralizer_singleton_iff.mp a.2.2)))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := hA2.card_modEq_card_fixedPoints
      ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    have h2 := hV2.card_modEq_card_fixedPoints
      ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    have hc1 : Nat.card ↥({⟨J, hs.hJ⟩} : Set
        ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))) = 1 := Nat.card_unique
    rw [hFA, hc1] at h1
    have hne : (MulAction.fixedPoints ↥V
        ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      have hc0 : Nat.card ↥(∅ : Set
          ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))) = 0 := by simp
      rw [h, hc0] at h2
      have h3 := h1.symm.trans h2
      simp [Nat.ModEq] at h3
    obtain ⟨J', hJ'⟩ := hne
    have hJ'J : J'.1 = J :=
      hfixA J'.1 J'.2 fun a ha => congrArg Subtype.val (hJ' ⟨a, hAV ha⟩)
    intro v hv
    have h4 := congrArg Subtype.val (hJ' ⟨v, hv⟩)
    rw [← hJ'J]
    exact h4
  have hVu : V ≤ Subgroup.centralizer ({u} : Set Y) := fun v hv =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hs.hu
      (mem_normalizer_iff_conjSub_eq.mpr (hVJ v hv))
  obtain ⟨c, -, hcV⟩ := hs.exists_conj_le_edgeCent hV2 hVt hVu
  have hcard : Nat.card ↥V ≤ Nat.card ↥(edgeCent (P : Subgroup Y) t u) := by
    rw [← natCard_conjSub' c V]
    exact Subgroup.card_le_of_le hcV
  exact (Subgroup.eq_of_le_of_card_ge hAV hcard).symm

theorem Z2SetR.eq_of_two_lt_card (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y}
    (hy : IsUniqueInvolution L y) (h4 : 2 < Nat.card ↥(L ⊓ (P : Subgroup Y))) :
    y = t ∨ y = u :=
  C264.z2BigStar_of_models (z2BigModelArith_holds r) (z2BigModelPiCyc_holds r) hr Y R S t J u R₀
    T₀ P hs L hL y hy h4

theorem Z2SetR.exists_conj_le_edgeCent_t (hs : Z2SetR r n R S t J u R₀ T₀ P) {V : Subgroup Y}
    (hV : IsPGroup 2 ↥V) (hVt : V ≤ Subgroup.centralizer ({t} : Set Y)) :
    ∃ d ∈ Subgroup.centralizer ({t} : Set Y),
      conjSub d V ≤ edgeCent (P : Subgroup Y) t u := by
  obtain ⟨V', hV', hVV'⟩ := IsSylow2In.exists_ge hV hVt
  obtain ⟨d, hd, hdV'⟩ := exists_conjSub_eq_of_isSylow2In hV' hs.isSylow2In_edgeCent_t
  refine ⟨d, hd, ?_⟩
  rw [← hdV']
  exact conjSub_mono (n := d) hVV'

theorem Z2SetR.mem_E_of_conj_mem_E (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y c : Y}
    (hc : c ∈ Subgroup.centralizer ({t * u} : Set Y)) (hw : c * y * c⁻¹ = t ∨ c * y * c⁻¹ = u)
    (hyP : y ∈ (P : Subgroup Y)) : y ∈ Subgroup.closure ({t, u} : Set Y) := by
  have hwM : c * y * c⁻¹ ∈ Subgroup.closure ({t * u, t} : Set Y) ⊔
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
    refine Subgroup.mem_sup_left ?_
    rw [hs.aux_closure_eq]
    rcases hw with h | h <;> rw [h] <;> exact Subgroup.subset_closure (by simp)
  have hyM := (Subgroup.mem_normalizer_iff.mp (h1 (inv_mem hc)) _).mp hwM
  have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
  rw [e] at hyM
  obtain ⟨e', he', o, ho, rfl⟩ := hs.aux_mem_sup hyM
  have heP : e' ∈ (P : Subgroup Y) := (hs.aux_E_le he').1.1
  have hoP : o ∈ (P : Subgroup Y) := by
    have h := mul_mem (inv_mem heP) hyP
    rwa [inv_mul_cancel_left] at h
  rw [aux_eq_one_of_mem_odd (P := P) (odd_natCard_oddCoreOf _) ho hoP, mul_one]
  exact he'

theorem Z2SetR.mem_E_of_two_lt_card (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hy : IsUniqueInvolution L y)
    (hyP : y ∈ (P : Subgroup Y)) {W : Subgroup Y} (hW2 : IsPGroup 2 ↥W) (hWL : W ≤ L)
    (hWa : W ≤ Subgroup.centralizer ({t * u} : Set Y)) (hW4 : 2 < Nat.card ↥W) :
    y ∈ Subgroup.closure ({t, u} : Set Y) := by
  obtain ⟨c, hc, hcW⟩ := hs.exists_conj_le hW2 hWa
  have hcard : 2 < Nat.card ↥(conjSub c L ⊓ (P : Subgroup Y)) := by
    refine lt_of_lt_of_le (by rwa [natCard_conjSub']) (Subgroup.card_le_of_le
      (le_inf (conjSub_mono (n := c) hWL) hcW))
  rcases hs.eq_of_two_lt_card hr (hs.mem_cls_conj hL c) (hy.conj c) hcard with h | h
  · exact hs.mem_E_of_conj_mem_E h1 hc (Or.inl h) hyP
  · exact hs.mem_E_of_conj_mem_E h1 hc (Or.inr h) hyP

theorem Z2SetR.exists_sylow_E_invariant (hs : Z2SetR r n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {W : Subgroup Y} (hWA : W ≤ edgeCent (P : Subgroup Y) t u)
    (hWy : W ≤ Subgroup.centralizer ({y} : Set Y)) (hWL : W ≤ L) :
    ∃ Ry : Subgroup Y, IsSylow2In Ry L ∧ W ≤ Ry ∧
      ∀ z ∈ Subgroup.closure ({t, u} : Set Y), z ∈ Subgroup.normalizer (Ry : Set Y) := by
  have hTF := TightLargeHypR.typeRFam hs.large
  have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.1.2
  have hyu' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.2
  have hEy : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.centralizer ({y} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyt'.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyu'.symm
  have hEW2 : IsPGroup 2 ↥(Subgroup.closure ({t, u} : Set Y) ⊔ W) :=
    (edgeCent_isPGroup P t u).to_le (sup_le hs.aux_E_le hWA)
  obtain ⟨X, hX, hEX⟩ := IsSylow2In.exists_ge hEW2 (sup_le hEy hWy)
  have hRy := Asc77.isSylow2In_inf_of_le_normalizer hX (hTF.le_centralizer hL hyL)
    (hTF.tight L hL y hyL)
  refine ⟨X ⊓ L, hRy, le_inf (le_sup_right.trans hEX) hWL, fun z hz => ?_⟩
  have hzX : z ∈ X := (le_sup_left.trans hEX) hz
  have hzL : z ∈ Subgroup.normalizer (L : Set Y) := hTF.tight L hL y hyL (hEy hz)
  rw [mem_normalizer_iff_conjSub_eq] at hzL ⊢
  rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj z).injective]
  exact congrArg₂ (· ⊓ ·) (mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hzX)) hzL

theorem natCard_eq_of_quat {G : Type} [Group G] {Q : Subgroup G} (hr : 2 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) : Nat.card ↥Q = 2 ^ r := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  ring

theorem Z2SetR.ne_u_of_natCard_lt (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y}
    (hyL : IsUniqueInvolution L y) {V : Subgroup Y}
    (hV : IsSylow2In V (L ⊓ Subgroup.centralizer ({t} : Set Y))) (hVc : Nat.card ↥V < 2 ^ r) :
    y ≠ u := by
  intro hyu
  rw [hyu] at hyL
  have hLJ : L = J := hs.eq_J_of_inv hL hyL
  subst hLJ
  obtain ⟨e, -⟩ := hs.exists_quat_T₀ hr
  have hT : Nat.card ↥T₀ = 2 ^ r := natCard_eq_of_quat (by omega) e
  have hle := hV.natCard_le hs.hT₀.2.1 (le_inf hs.hT₀.1 hs.T₀_le_cent_t)
  omega

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
