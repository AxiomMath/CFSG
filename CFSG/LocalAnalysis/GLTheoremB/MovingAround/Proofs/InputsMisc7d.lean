module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7c
import CFSG.RankThree.PartOne.MB3.OddOutLinear
import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.RankThree.PartOne.AUTSL.OddOutRee
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.PSL2Odd
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
import CFSG.RankThree.PartOne.KLC.D4OutCentral
import CFSG.Quasithin.Vol2.Ch11SKFIto
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7d

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.RankThree.PartOne.OutStructure (OutPNice)
open scoped commutatorElement

section Abstract

variable {p : ℕ}

theorem hasNormalPComplement_of_quotient {G : Type*} [Group G] [Finite G] [hp : Fact p.Prime]
    {H : Subgroup G} [H.Normal] (hH : ∀ h ∈ H, h ^ p = 1 → h = 1)
    (hq : CFSG.HasNormalPComplement p (G ⧸ H)) : CFSG.HasNormalPComplement p G := by
  obtain ⟨M, hMn, hMc, hMq⟩ := hq
  haveI := hMn
  refine ⟨M.comap (QuotientGroup.mk' H), inferInstance, ?_, ?_⟩
  · rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxp : (x : G) ^ p = 1 := by
      rw [← hx, ← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    have h1 : QuotientGroup.mk' H (x : G) = 1 :=
      InputsMisc5.eq_one_of_pow_of_coprime (k := 1) hMc x.2
        (by rw [pow_one, ← map_pow, hxp, map_one])
    have h2 : (x : G) = 1 := hH _ ((QuotientGroup.eq_one_iff _).1 h1) hxp
    have h3 : x = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hMq (QuotientGroup.mk (QuotientGroup.mk' H g))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, map_pow]
    exact hk

theorem hasNormalPComplement_quotient_of_le {A : Type*} [Group A] [Finite A] [hp : Fact p.Prime]
    {I D : Subgroup A} [I.Normal] [D.Normal] (hID : I ≤ D) (hD : ∀ δ ∈ D, δ ^ p ∈ I → δ ∈ I)
    (hq : CFSG.HasNormalPComplement p (A ⧸ D)) : CFSG.HasNormalPComplement p (A ⧸ I) := by
  haveI : (D.map (QuotientGroup.mk' I)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective I)
  refine hasNormalPComplement_of_quotient (H := D.map (QuotientGroup.mk' I)) ?_ ?_
  · rintro _ ⟨δ, hδ, rfl⟩ hδp
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hδp
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hD δ hδ hδp
  · let e := QuotientGroup.quotientQuotientEquivQuotient I D hID
    exact InputsMisc5.hasNormalPComplement_of_injective e.toMonoidHom e.injective hq

theorem hasNormalPComplement_outer_of_outPNice {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    (h : OutPNice p X) : CFSG.HasNormalPComplement p (Outer X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, E, hID, hD2, hpE, hcomm, -⟩ := h
  have hDE : ∀ δ ∈ D, δ ∈ E := fun δ hδ => hpE δ ⟨0, by rwa [pow_zero, pow_one]⟩
  haveI : D.Normal := ⟨fun δ hδ γ => by
    have e : γ * δ * γ⁻¹ = ⁅γ, δ⁆ * δ := by rw [commutatorElement_def]; group
    rw [e]
    exact D.mul_mem (hcomm γ δ (hDE δ hδ)) hδ⟩
  refine hasNormalPComplement_quotient_of_le hID
    (fun δ hδ hδp => hD2 δ hδ 1 (by rwa [pow_one])) ?_
  refine InputsMisc5.hasNormalPComplement_of_pElements_central fun g hg => ?_
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨k, hk⟩ := hg
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  have hαE := hpE α ⟨k, hk⟩
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ((⁅γ, α⁆ : MulAut X) : MulAut X ⧸ D) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (hcomm γ α hαE)
  rw [← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end Abstract

section ThreePoint

variable {A : Type*} [Group A] {X : Type*} [MulAction A X] {p : ℕ}

theorem fix_or_swap {F y z : X} (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hyz : y ≠ z) {g : A} (hg : g • F = y)
    {e : A} (he : e • F = F) : (e • y = y ∧ e • z = z) ∨ (e • y = z ∧ e • z = y) := by
  have hFy : F ≠ y := by
    intro h
    apply hyz
    rw [← hκy, ← h, hκF]
  have hFz : F ≠ z := by
    intro h
    apply hFy
    have : κ • F = κ • y := by rw [hκF, hκy, h]
    exact smul_left_cancel κ this
  have hey : e • y = F ∨ e • y = y ∨ e • y = z := by
    have := hO (e * g)
    rwa [mul_smul, hg] at this
  have hez : e • z = F ∨ e • z = y ∨ e • z = z := by
    have := hO (e * (κ * g))
    rwa [mul_smul, mul_smul, hg, hκy] at this
  have hey' : e • y ≠ F := fun h => hFy (smul_left_cancel e (he.trans h.symm))
  have hez' : e • z ≠ F := fun h => hFz (smul_left_cancel e (he.trans h.symm))
  have hne : e • y ≠ e • z := fun h => hyz (smul_left_cancel e h)
  rcases hey with h1 | h1 | h1
  · exact absurd h1 hey'
  · rcases hez with h2 | h2 | h2
    · exact absurd h2 hez'
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, h2⟩
  · rcases hez with h2 | h2 | h2
    · exact absurd h2 hez'
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne

theorem commutator_smul_of_fix_or_swap {y z : X} {a b : A}
    (ha : (a • y = y ∧ a • z = z) ∨ (a • y = z ∧ a • z = y))
    (hb : (b • y = y ∧ b • z = z) ∨ (b • y = z ∧ b • z = y)) : ⁅a, b⁆ • y = y := by
  rw [commutatorElement_def, mul_smul, mul_smul, mul_smul]
  rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · rw [inv_smul_eq_iff.2 hb1.symm, inv_smul_eq_iff.2 ha1.symm, hb1, ha1]
  · rw [inv_smul_eq_iff.2 hb2.symm, inv_smul_eq_iff.2 ha2.symm, hb2, ha1]
  · rw [inv_smul_eq_iff.2 hb1.symm, inv_smul_eq_iff.2 ha2.symm, hb2, ha2]
  · rw [inv_smul_eq_iff.2 hb2.symm, inv_smul_eq_iff.2 ha1.symm, hb1, ha2]

theorem commutator_mem_normalCore {F y z : X} (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    {a b : A} (ha : a • F = F) (hb : b • F = F) :
    ⁅a, b⁆ ∈ (MulAction.stabilizer A F).normalCore := by
  show ∀ g : A, g * ⁅a, b⁆ * g⁻¹ ∈ MulAction.stabilizer A F
  intro g
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← eq_inv_smul_iff]
  have hO' : ∀ c : A, c • F = F ∨ c • F = z ∨ c • F = y := fun c => by
    rcases hO c with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  rcases hO g⁻¹ with h | h | h
  · rw [h, commutatorElement_def, mul_smul, mul_smul, mul_smul, inv_smul_eq_iff.2 hb.symm,
      inv_smul_eq_iff.2 ha.symm, hb, ha]
  · rw [h]
    exact commutator_smul_of_fix_or_swap (fix_or_swap hO hκF hκy hyz h ha)
      (fix_or_swap hO hκF hκy hyz h hb)
  · rw [h]
    exact commutator_smul_of_fix_or_swap (fix_or_swap hO' hκF hκz hyz.symm h ha)
      (fix_or_swap hO' hκF hκz hyz.symm h hb)

theorem coprime_index_of_forall_pow [Finite A] [hp : Fact p.Prime] {I D : Subgroup A} [I.Normal]
    (hD : ∀ δ ∈ D, δ ^ p ∈ I → δ ∈ I) : Nat.Coprime p (I.subgroupOf D).index := by
  haveI : (I.subgroupOf D).Normal := Subgroup.Normal.subgroupOf inferInstance D
  rw [Nat.Prime.coprime_iff_not_dvd hp.out, Subgroup.index_eq_card]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (δ : A) ^ p ∈ I := by
    have h0 : (QuotientGroup.mk δ : D ⧸ I.subgroupOf D) ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h0
    simpa using h0
  have h2 : (QuotientGroup.mk δ : D ⧸ I.subgroupOf D) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hD δ δ.2 h1
  rw [h2, orderOf_one] at hx
  exact hp.out.one_lt.ne hx

theorem exists_pPrime_subgroup {I C D : Subgroup A} (hIC : I ≤ C) (hID : I ≤ D)
    (hCD : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ D) {r : ℕ} (hrc : Nat.Coprime p r)
    (hDr : ∀ δ ∈ D, δ ^ r ∈ I) :
    ∃ R : Subgroup A, ∀ x, x ∈ R ↔ x ∈ C ∧ ∃ m : ℕ, Nat.Coprime p m ∧ x ^ m ∈ I := by
  refine ⟨{ carrier := {x | x ∈ C ∧ ∃ m : ℕ, Nat.Coprime p m ∧ x ^ m ∈ I}
            mul_mem' := ?_
            one_mem' := ⟨C.one_mem, 1, Nat.coprime_one_right p, by rw [one_pow]; exact I.one_mem⟩
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro a b ⟨haC, m, hm, ham⟩ ⟨hbC, n, hn, hbn⟩
    refine ⟨C.mul_mem haC hbC, m * n * r,
      Nat.Coprime.mul_right (Nat.Coprime.mul_right hm hn) hrc, ?_⟩
    have hD' : (a * b) ^ (m * n) ∈ D := by
      haveI : (D.subgroupOf C).Normal := ⟨fun d hd c => by
        rw [Subgroup.mem_subgroupOf] at hd ⊢
        have e : ((c * d * c⁻¹ : C) : A) = ⁅(c : A), (d : A)⁆ * d := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        rw [e]
        exact D.mul_mem (hCD c c.2 d d.2) hd⟩
      let π := QuotientGroup.mk' (D.subgroupOf C)
      have hcomm : Commute (π ⟨a, haC⟩) (π ⟨b, hbC⟩) := by
        have h1 : π ⁅(⟨a, haC⟩ : C), ⟨b, hbC⟩⁆ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          simpa [commutatorElement_def] using hCD a haC b hbC
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have ha1 : π ⟨a, haC⟩ ^ m = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hID ham
      have hb1 : π ⟨b, hbC⟩ ^ n = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hID hbn
      have h2 : π ((⟨a, haC⟩ * ⟨b, hbC⟩ : C) ^ (m * n)) = 1 := by
        rw [map_pow, map_mul, hcomm.mul_pow, pow_mul, ha1, one_pow, one_mul, mul_comm m n, pow_mul,
          hb1, one_pow]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
      simpa using h2
    rw [pow_mul]
    exact hDr _ hD'
  · rintro x ⟨hxC, m, hm, hxm⟩
    exact ⟨C.inv_mem hxC, m, hm, by rw [inv_pow]; exact I.inv_mem hxm⟩

theorem hasNormalPComplement_quotient_of_three_point [Finite A] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {I D : Subgroup A} [I.Normal] (hID : I ≤ D) (hD : ∀ δ ∈ D, δ ^ p ∈ I → δ ∈ I)
    {F y z : X} (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hI : ∀ n ∈ I, n • F = F) (hE : ∀ a b : A, a • F = F → b • F = F → ⁅a, b⁆ ∈ D) :
    CFSG.HasNormalPComplement p (A ⧸ I) := by
  set C := (MulAction.stabilizer A F).normalCore with hCdef
  have hCS : ∀ c ∈ C, c • F = F := fun c hc => Subgroup.normalCore_le _ hc
  have hIC : I ≤ C := Subgroup.normal_le_normalCore.2 fun n hn => hI n hn
  have hCD : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ D := fun a ha b hb => hE a b (hCS a ha) (hCS b hb)
  have hrc : Nat.Coprime p (I.subgroupOf D).index := coprime_index_of_forall_pow hD
  have hDr : ∀ δ ∈ D, δ ^ (I.subgroupOf D).index ∈ I := by
    intro δ hδ
    haveI : (I.subgroupOf D).Normal := Subgroup.Normal.subgroupOf inferInstance D
    have := Subgroup.pow_index_mem (I.subgroupOf D) (⟨δ, hδ⟩ : D)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨R, hR⟩ := exists_pPrime_subgroup hIC hID hCD hrc hDr
  haveI : R.Normal := ⟨fun x hx g => by
    obtain ⟨hxC, m, hm, hxm⟩ := (hR x).1 hx
    refine (hR _).2 ⟨(Subgroup.normalCore_normal _).conj_mem x hxC g, m, hm, ?_⟩
    rw [conj_pow]
    exact (inferInstance : I.Normal).conj_mem _ hxm g⟩
  have hIR : I ≤ R := fun x hx =>
    (hR x).2 ⟨hIC hx, 1, Nat.coprime_one_right p, by rwa [pow_one]⟩
  have hRp : ∀ δ ∈ R, δ ^ p ∈ I → δ ∈ I := fun δ hδ hδp => by
    obtain ⟨-, m, hm, hδm⟩ := (hR δ).1 hδ
    refine CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_not_dvd hp.out hδp (m := (m : ℤ))
      (by rwa [zpow_natCast]) ?_
    rw [Int.natCast_dvd_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hm
  have hRF : ∀ n ∈ R, n • F = F := fun n hn => hCS n ((hR n).1 hn).1
  have hER : ∀ a b : A, a • F = F → b • F = F → ⁅a, b⁆ ∈ R := fun a b ha hb =>
    (hR _).2 ⟨commutator_mem_normalCore hO hκF hκy hκz hyz ha hb, _, hrc, hDr _ (hE a b ha hb)⟩
  have hq : CFSG.HasNormalPComplement p (A ⧸ R) := by
    rw [CFSG.GroupTheory.hasNormalPComplement_iff_exists]
    refine CFSG.Quasithin.Vol2.Ch11.SecS.KF.ito_normalPComplement (by omega) fun x hx => ?_
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro x'
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x'
    have h1 : ((⁅γ, α⁆ : A) : A ⧸ R) = 1 := (QuotientGroup.eq_one_iff _).2
      (CFSG.RankThree.PartOne.KLC.commutator_mem_of_three_point_orbit R hO hκF hκy hκz hyz hRF
        hER hp.out hp5 hx γ)
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  exact hasNormalPComplement_quotient_of_le hIR hRp hq

end ThreePoint

section D4

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Automorphisms
  CFSG.RankThree.PartOne.OutStructure
open scoped Pointwise

theorem hasNormalPComplement_outer_POmegaPlus_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Type} [Group X] {r m : ℕ} (h : CFSG.Open.StatedClassicalModel X .POmegaPlus 4 r m) :
    CFSG.HasNormalPComplement p (Outer X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 r m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' := card_abelianization_le_four_of_bound (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  have hP : CFSG.HasNormalPComplement p
      (Outer (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    hasNormalPComplement_quotient_of_three_point hp5 (inner_le_orthD _)
      (fun δ hδ hδp => orthD_D2_of_bound _ hQ hab' hp hp5 hδ (k := 1) (by rwa [pow_one]))
      (F := projectivePointFamily (coordinateQuadPlus 4 K)) (y := plusCX 4 K)
      (z := plusCXstar 4 K (by omega))
      (fun a => by
        have := hsub (MulAction.mem_orbit _ a)
        simpa using this)
      hκF hκy hκz hyz
      (by
        rintro _ ⟨g, rfl⟩
        exact CFSG.RankThree.PartOne.KLC.inner_smul_pointFamily_coordinate K g)
      (fun a b ha hb => by
        have ha' : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
          rw [← hEA]
          exact (mem_projectivePointFamilyAut_iff _ _).2 ha
        have hb' : b ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
          rw [← hEA]
          exact (mem_projectivePointFamilyAut_iff _ _).2 hb
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 ha'
        obtain ⟨g', rfl⟩ := MonoidHom.mem_range.1 hb'
        exact comm_mem_orthD _ g g')
  haveI : Finite X := Finite.of_equiv _ (coordinatePlusWitnessEquiv K e).symm.toEquiv
  let e' := CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (coordinatePlusWitnessEquiv K e)
  exact InputsMisc5.hasNormalPComplement_of_injective e'.toMonoidHom e'.injective hP

end D4

section Arith

theorem dvd_of_mul_eq {c d N p : ℕ} (hd : 0 < d) (h : c * d = N) (hpd : p * d ∣ N) : p ∣ c := by
  rw [← h] at hpd
  exact Nat.dvd_of_mul_dvd_mul_right hd hpd

theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  have h : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ?_)) _
    rw [Nat.pow_mod, h]
  · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ?_)) _
    rw [Nat.pow_mod, h]

theorem dvd_card_of_dvd_gcd_sub {c n q p : ℕ} (hn : 3 ≤ n)
    (h : c * Nat.gcd n (q - 1) = q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1))
    (hp : p ∣ Nat.gcd n (q - 1)) : p ∣ c := by
  have hd : 0 < Nat.gcd n (q - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  refine dvd_of_mul_eq hd h ?_
  have hpq : p ∣ q - 1 := hp.trans (Nat.gcd_dvd_right _ _)
  have h23 : (q ^ 2 - 1) * (q ^ 3 - 1) ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]
      omega
    have := Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hsub
    rwa [Finset.prod_pair (by norm_num)] at this
  have h1 : p * Nat.gcd n (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [mul_comm p]
    exact Nat.mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one q 2))
      (hpq.trans (Nat.sub_one_dvd_pow_sub_one q 3))
  exact (h1.trans h23).trans (dvd_mul_left _ _)

theorem dvd_card_of_dvd_gcd_add {c n q p : ℕ} (hn : 3 ≤ n)
    (h : c * Nat.gcd n (q + 1) = q ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1))
    (hp : p ∣ Nat.gcd n (q + 1)) : p ∣ c := by
  have hd : 0 < Nat.gcd n (q + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  refine dvd_of_mul_eq hd h ?_
  have hpq : p ∣ q + 1 := hp.trans (Nat.gcd_dvd_right _ _)
  have h23 : (q ^ 2 - 1) * (q ^ 3 + 1) ∣
      ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]
      omega
    have := Finset.prod_dvd_prod_of_subset _ _
      (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hsub
    rwa [Finset.prod_pair (by norm_num), if_pos (by decide : Even 2),
      if_neg (by decide : ¬ Even 3)] at this
  have hq2 : q + 1 ∣ q ^ 2 - 1 := by
    have e : q ^ 2 - 1 = q ^ 2 - 1 ^ 2 := by rw [one_pow]
    rw [e, Nat.sq_sub_sq]
    exact dvd_mul_right _ _
  have hq3 : q + 1 ∣ q ^ 3 + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    rwa [one_pow] at this
  have h1 : p * Nat.gcd n (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [mul_comm p]
    exact Nat.mul_dvd_mul ((Nat.gcd_dvd_right _ _).trans hq2) (hpq.trans hq3)
  exact (h1.trans h23).trans (dvd_mul_left _ _)

theorem three_dvd_card_E6 {c q : ℕ} (h : c * Nat.gcd 3 (q - 1) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) *
    (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) : 3 ∣ c := by
  by_cases h3 : 3 ∣ q - 1
  · rw [Nat.gcd_eq_left h3] at h
    refine dvd_of_mul_eq (by norm_num) h ?_
    exact Nat.mul_dvd_mul (Dvd.dvd.mul_left (h3.trans (Nat.sub_one_dvd_pow_sub_one q 5)) _)
      (h3.trans (Nat.sub_one_dvd_pow_sub_one q 2))
  · have hg : Nat.gcd 3 (q - 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [hg, mul_one] at h
    rw [h]
    refine (three_dvd_mul_sq_sub_one q).trans (Nat.mul_dvd_mul ?_ dvd_rfl)
    exact (((((dvd_pow_self q (by norm_num)).mul_right _).mul_right _).mul_right _).mul_right
      _).mul_right _

theorem three_dvd_card_twistedE6 {c q : ℕ} (h : c * Nat.gcd 3 (q + 1) = q ^ 36 * (q ^ 12 - 1) *
    (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) : 3 ∣ c := by
  by_cases h3 : 3 ∣ q + 1
  · rw [Nat.gcd_eq_left h3] at h
    refine dvd_of_mul_eq (by norm_num) h ?_
    have hq2 : q + 1 ∣ q ^ 2 - 1 := by
      have e : q ^ 2 - 1 = q ^ 2 - 1 ^ 2 := by rw [one_pow]
      rw [e, Nat.sq_sub_sq]
      exact dvd_mul_right _ _
    have hq5 : q + 1 ∣ q ^ 5 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 5)
      rwa [one_pow] at this
    exact Nat.mul_dvd_mul (Dvd.dvd.mul_left (h3.trans hq5) _) (h3.trans hq2)
  · have hg : Nat.gcd 3 (q + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [hg, mul_one] at h
    rw [h]
    refine (three_dvd_mul_sq_sub_one q).trans (Nat.mul_dvd_mul ?_ dvd_rfl)
    exact (((((dvd_pow_self q (by norm_num)).mul_right _).mul_right _).mul_right _).mul_right
      _).mul_right _

theorem three_dvd_card_D4 {c q : ℕ} (h : c * Nat.gcd 4 (q ^ 4 - 1) =
    q ^ (4 * (4 - 1)) * (q ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1)) : 3 ∣ c := by
  have hcop : Nat.Coprime 3 (Nat.gcd 4 (q ^ 4 - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [h]
  have h1 : q ^ (2 * 1) - 1 ∣ ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (by simp)
  have h2 : q ∣ q ^ (4 * (4 - 1)) * (q ^ 4 - 1) := (dvd_pow_self q (by norm_num)).mul_right _
  exact (three_dvd_mul_sq_sub_one q).trans (Nat.mul_dvd_mul h2 h1)

end Arith

section Main

open CFSG.RankThree.PartOne.OutStructure CFSG.Blueprint


theorem resOddTrivialLie_holds : InputsMisc7.ResOddTrivialLie := by
  intro K _ _ hs hnab t n ℓ f hadm hmodel ht p hp hp2 hpK
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard :=
    (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K t n ℓ f hadm hmodel).2.1
  have nice : OutPNice p K → CFSG.HasNormalPComplement p (Outer K) :=
    hasNormalPComplement_outer_of_outPNice hp
  rcases hmodel with ⟨-, hcl⟩ | ⟨-, -, hch⟩ | ⟨-, -, hree⟩ | ⟨-, rfl, hsz⟩
  · cases t
    case PSL =>
      by_cases hn : n = 2
      · subst hn
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact nice (outPNice_PSL_two hp hcl)
        · exact nice
            (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_PSL_two_odd_all hp hp2 hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact nice (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl fun hd =>
          hpK (dvd_card_of_dvd_gcd_sub hn3 hcard hd))
    case PSU =>
      have hn3 : 3 ≤ n := hcl.1.2.2.1
      exact nice (outPNice_PSU_odd hp hcl fun hd => hpK (dvd_card_of_dvd_gcd_add hn3 hcard hd))
    case PSp =>
      by_cases hn : n = 2
      · subst hn
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact nice (outPNice_PSp_two hp hcl)
        · exact nice (CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact nice (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl)
    case POmegaOdd =>
      exact nice (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaOdd_all hp hp2 hcl)
    case POmegaPlus =>
      by_cases hn : n = 4
      · subst hn
        by_cases hp3 : p = 3
        · subst hp3
          exact absurd (three_dvd_card_D4 hcard) hpK
        · exact hasNormalPComplement_outer_POmegaPlus_four hp
            (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hcl
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact nice
          (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaPlus_all_ge_five hp hp2 hn5 hcl)
    case POmegaMinus =>
      exact nice (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaMinus_all hp hp2 hcl)
    all_goals exact hcl.2.elim
  · cases t
    case G2 =>
      by_cases h2 : ℓ = 2
      · subst h2
        exact nice (outPNice_G2 hp hch)
      · by_cases h3 : ℓ = 3
        · subst h3
          exact nice (outPNice_G2_three hp hch)
        · exact nice (outPNice_G2_odd hp h2 h3 hch)
    case F4 =>
      by_cases h2 : ℓ = 2
      · subst h2
        exact nice (outPNice_F4 hp hch)
      · exact nice (outPNice_F4_odd hp h2 hch)
    case E6 =>
      by_cases hp3 : p = 3
      · subst hp3
        exact absurd (three_dvd_card_E6 hcard) hpK
      · exact nice (outPNice_E6_gen hp hp3 hp2 hch)
    case E7 => exact nice (outPNice_E7_gen hp hp2 hch)
    case E8 => exact nice (outPNice_E8_gen hp hch)
    case twistedE6 =>
      by_cases hp3 : p = 3
      · subst hp3
        exact absurd (three_dvd_card_twistedE6 hcard) hpK
      · exact nice (outPNice_twistedE6_gen hp hp3 hch)
    case trialityD4 =>
      exact InputsMisc7.hasNormalPComplement_of_isMulCommutative
        (InputsMisc7.isMulCommutative_outer_trialityD4 hch)
    all_goals exact hch.2.elim
  · cases t
    case twistedG2 =>
      have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact nice (CFSG.RankThree.PartOne.AUTSL.outPNice_twistedG2 hp hree)
    case twistedF4 =>
      have h2 : ℓ = 2 := hree.1.2.2.2.1
      subst h2
      exact nice (outPNice_twistedF4 hp hree)
    case Tits => exact absurd rfl ht
    all_goals
      obtain ⟨-, a, -, hm⟩ := hree
      exact hm.elim
  · have h2 : ℓ = 2 := hsz.1
    subst h2
    exact nice (outPNice_Suzuki hp hsz)

theorem input7_10_1Rest_of_residues (hE6 : InputsMisc7.ResOddE6) (hTwE6 : InputsMisc7.ResOddTwE6)
    (hD4 : InputsMisc7.ResOddD4) : InputsMisc7c.Input7_10_1Rest :=
  ⟨hE6, hTwE6, hD4, resOddTrivialLie_holds⟩

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7d
