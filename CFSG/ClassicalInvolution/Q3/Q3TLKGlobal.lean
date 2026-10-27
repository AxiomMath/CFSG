module

public import CFSG.ClassicalInvolution.Q3.Q3TIYAtT
public import CFSG.ClassicalInvolution.Q3.Q3TZClos
public import CFSG.ClassicalInvolution.Q3.Q3TZTrans
public import CFSG.ClassicalInvolution.Q3.Q3TLKAct
public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT
public import CFSG.ClassicalInvolution.RouteD.TWZConj
public import CFSG.ClassicalInvolution.RouteD.TWZLayer
public import CFSG.ClassicalInvolution.Q3.Q3TIYComp
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TY6
public import CFSG.ClassicalInvolution.RouteD.TWZLinkAux
public import CFSG.ClassicalInvolution.RouteD.TWZPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TIV CFSG.ClassicalInvolution.Q3.Q3TZ
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow TwinDatumOn
  TwinMFGenerationOn)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)
open scoped MatrixGroups



section Lifting

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_le_of_locImg_le3 {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    {H₀ : Subgroup ↥(locLayer Ω x)} (h : locImg Ω x L ≤ H₀.map (locMk Ω x)) :
    L.subgroupOf (locLayer Ω x) ≤ H₀ := by
  have hexp : ∀ m ∈ L.subgroupOf (locLayer Ω x), m ^ 12 = 1 := by
    intro m hm
    obtain ⟨z, hz⟩ := hΩ.classical L hL.1
    have := pow_twelve_of_exact hz (hex L hL.1) (m : G) (Subgroup.mem_subgroupOf.mp hm)
    exact Subtype.ext (by simpa using this)
  refine Q3TZ.le_of_le_sup_central_of_exponent (O := classicalInvolutionOddCore ↥(locLayer Ω x))
    hP1 (fun o ho => Q3TZ.coprime_six_of_mem_oddCore3 hO3 ho) hexp ?_
  intro a ha
  obtain ⟨h₀, hh₀, hh₀a⟩ := h ⟨a, ha, rfl⟩
  have e : a = h₀ * (h₀⁻¹ * a) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hh₀) (Subgroup.mem_sup_right ?_)
  refine (QuotientGroup.eq_one_iff _).mp ?_
  show locMk Ω x (h₀⁻¹ * a) = 1
  rw [map_mul, map_inv, hh₀a, inv_mul_cancel]

end Lifting

section Exact

variable {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem exists_inv_conj_of_exact3 (hz : IsClassicalMember3 K z)
    (hex : classicalInvolutionOddCore K = ⊥) {a : G} (ha : a ∈ K) (haa : a * a = z) :
    ∃ n ∈ K, n * a * n⁻¹ = a⁻¹ := by
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hex
  have hzK : (⟨z, hz.mem⟩ : K) = e.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨z, hz.mem⟩).mp
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
  have hA : e ⟨a, ha⟩ * e ⟨a, ha⟩ = -1 := by
    have h : (⟨a, ha⟩ : K) * ⟨a, ha⟩ = ⟨z, hz.mem⟩ := Subtype.ext haa
    rw [← map_mul, h, hzK, e.apply_symm_apply]
  obtain ⟨N, hN⟩ := TWZ.sl2_exists_conj_inv hodd (e ⟨a, ha⟩) hA
  refine ⟨((e.symm N : K) : G), (e.symm N).2, ?_⟩
  have h1 : e (e.symm N * ⟨a, ha⟩ * (e.symm N)⁻¹) = e (⟨a, ha⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, e.apply_symm_apply]
    exact hN
  have h2 := e.injective h1
  exact congrArg Subtype.val h2

end Exact

section Member

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem member_t_le_of_centralizers3 (e : TwinElt K T z)
    (hMF : TwinMFGenerationOn tY (modelUniv tY nY 3 1 Nat.prime_three))
    (A : AtT3 K T J z t tY nY) (H : Subgroup G)
    (hHz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hHu : Subgroup.centralizer ({e.u} : Set G) ≤ H)
    (hHzu : Subgroup.centralizer ({z * e.u} : Set G) ≤ H) (hz2 : z * z = 1)
    (hu2 : e.u * e.u = 1) (hzu : z * e.u = e.u * z) {N : Subgroup G}
    (hN : N ∈ centralizingMembers (conjClass3 K) {t}) (hNJ : N ≠ J) (hNJ₂ : N ≠ A.J₂) :
    N ≤ H := by
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts3 A e
  obtain ⟨RN, hRN, hNR⟩ := A.c.big_of_ne A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso hN hNJ hNJ₂
  have hgen := hMF A.RK A.RT A.x A.x' A.hdat ã hãR ã' hã'R hsq hsq' RN hRN
  set w₁ : ↥(locLayer (conjClass3 K) t) := ⟨z, A.hzY⟩ with hw₁
  set w₂ : ↥(locLayer (conjClass3 K) t) := ⟨e.u, huY⟩ with hw₂
  have hzu2 : z * e.u * (z * e.u) = 1 := by
    calc z * e.u * (z * e.u) = z * (e.u * z) * e.u := by group
      _ = z * (z * e.u) * e.u := by rw [← hzu]
      _ = (z * z) * (e.u * e.u) := by group
      _ = 1 := by rw [hz2, hu2, one_mul]
  have hw₁₁ : w₁ * w₁ = 1 := Subtype.ext hz2
  have hw₂₂ : w₂ * w₂ = 1 := Subtype.ext hu2
  have hw₃₃ : w₁ * w₂ * (w₁ * w₂) = 1 := Subtype.ext hzu2
  have hψ₃ : A.c.d.ψ (A.x * (ã * ã')) = locMk (conjClass3 K) t (w₁ * w₂) := by
    rw [map_mul, A.hxz, hψu, ← map_mul]
  have hloc : locImg (conjClass3 K) t N ≤
      ((Subgroup.centralizer ({w₁} : Set ↥(locLayer (conjClass3 K) t)) ⊔
        Subgroup.centralizer ({w₂} : Set ↥(locLayer (conjClass3 K) t))) ⊔
        Subgroup.centralizer ({w₁ * w₂} : Set ↥(locLayer (conjClass3 K) t))).map
          (locMk (conjClass3 K) t) := by
    rw [hNR, Subgroup.map_sup, Subgroup.map_sup]
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le_sup (sup_le_sup (TwinY.map_centralizer_le_locMk hw₁₁ A.c.d.ψ A.hxz)
      (TwinY.map_centralizer_le_locMk hw₂₂ A.c.d.ψ hψu))
      (TwinY.map_centralizer_le_locMk hw₃₃ A.c.d.ψ hψ₃)
  have hsub := subgroupOf_le_of_locImg_le3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hN hloc
  intro n hn
  have hnY : n ∈ locLayer (conjClass3 K) t := le_centralizingLayer hN hn
  have hmem := hsub (Subgroup.mem_subgroupOf.mpr hn :
    (⟨n, hnY⟩ : ↥(locLayer (conjClass3 K) t)) ∈ N.subgroupOf (locLayer (conjClass3 K) t))
  have hle : ((Subgroup.centralizer ({w₁} : Set ↥(locLayer (conjClass3 K) t)) ⊔
        Subgroup.centralizer ({w₂} : Set ↥(locLayer (conjClass3 K) t))) ⊔
        Subgroup.centralizer ({w₁ * w₂} : Set ↥(locLayer (conjClass3 K) t))) ≤
      H.comap (locLayer (conjClass3 K) t).subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      refine hHz ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · intro y hy
      refine hHu ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · intro y hy
      refine hHzu ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  exact hle hmem

end Member

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem exists_twin_frame3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) :
    ∃ (J J₂ : Subgroup G) (t : G), J ∈ centralizingMembers (conjClass3 K) {z} ∧ J ≠ K ∧
      J ≠ T ∧ IsClassicalMember3 J t ∧ t ≠ z ∧
      J₂ ∈ centralizingMembers (conjClass3 K) {t} ∧ J₂ ≠ J ∧ IsClassicalMember3 J₂ t ∧
      Commutes J₂ K ∧ Commutes J₂ T ∧
      (∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J → Commutes J L) := by
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hKiso hTiso
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨J₂, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso, -⟩ :=
    exists_twin_iso_at_t3 hR hT.ne.symm hT.mem hKiso hTiso clsT hJ hJK hJT hJt htz
  exact ⟨J, J₂, t, hJ, hJK, hJT, hJt, htz, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso⟩

end Frame

section Global

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem false_of_layer_le_centralizer_tz3 (h3 : OddThreeFreeInput) (hR : RouteD3Setup K z)
    (hrow : TwinRow tY nY) (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (e : TwinElt K T z) {J : Subgroup G} {t : G}
    (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hJiso : ∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J → Commutes J L)
    (hZt : ∀ N ∈ centralizingMembers (conjClass3 K) {e.u},
      N ≤ Subgroup.centralizer ({t * z} : Set G)) : False := by
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hz2 : z * z = 1 := hR.cls.isCentralInvolution.sq
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, CFSG.ClassicalInvolution.isSubnormal_le hR.cls.subnormal⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hΦu : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (conjClass3 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (Commutes.symm (hKiso N hN hNK))
      (Commutes.symm (hTiso N hN hNT))
  obtain ⟨L', hL', hL'J, hnc⟩ := c.exists_noncomm_of_ne hKz hT.mem hT.ne.symm hKiso hTiso hJ hJK
    hJT
  refine hnc ?_
  by_cases hL'K : L' = K
  · rw [hL'K]
    exact Commutes.symm (hKiso J hJ hJK)
  by_cases hL'T : L' = T
  · rw [hL'T]
    exact Commutes.symm (hTiso J hJ hJT)
  have hL'u : L' ∈ centralizingMembers (conjClass3 K) {e.u} := hΦu L' hL' hL'K hL'T
  have hzt := hZt L' hL'u
  have hL't : L' ∈ centralizingMembers (conjClass3 K) {t} := by
    refine ⟨hL'.1, fun l hl => ?_⟩
    have h1 : l * z = z * l := Subgroup.mem_centralizer_singleton_iff.mp (hL'.2 hl)
    have h2 : l * (t * z) = (t * z) * l := Subgroup.mem_centralizer_singleton_iff.mp (hzt hl)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * t = l * t * (z * z) := by rw [hz2, mul_one]
      _ = l * (t * z) * z := by group
      _ = (t * z) * l * z := by rw [h2]
      _ = (t * z) * (l * z) := by group
      _ = (t * z) * (z * l) := by rw [h1]
      _ = t * (z * z) * l := by group
      _ = t * l := by rw [hz2, mul_one]
  exact hJiso L' hL't hL'J

theorem false_of_layer_le_centralizer3 (h3 : OddThreeFreeInput)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z)
    (hMF : TwinMFGenerationOn tY (modelUniv tY nY 3 1 Nat.prime_three))
    (hZ : ∀ N ∈ centralizingMembers (conjClass3 K) {e.u},
      N ≤ Subgroup.centralizer ({z} : Set G)) : False := by
  classical
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hKex := c.hex K hKΩ
  have hTex := c.hex T hT.mem.1
  have hz2 : z * z = 1 := hR.cls.isCentralInvolution.sq
  have hz1 : z ≠ 1 := hR.cls.ne_one
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hzu : z * e.u = e.u * z :=
    (e.u_comm_z (CFSG.ClassicalInvolution.isSubnormal_le hR.cls.subnormal)
      (CFSG.ClassicalInvolution.isSubnormal_le clsT.subnormal)).symm
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, CFSG.ClassicalInvolution.isSubnormal_le hR.cls.subnormal⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -⟩ := exists_twin_frame3 h3 hnab hR hrow hshape
    hT clsT
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  have hKu : K ∉ centralizingMembers (conjClass3 K) {e.u} := fun h =>
    twinElt_not_le_centralizer_left3 e hR.cls hKex hKT' h.2
  have hTu : T ∉ centralizingMembers (conjClass3 K) {e.u} := fun h =>
    twinElt_not_le_centralizer_right3 e clsT hTex hKT' h.2
  have hΦu : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (conjClass3 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (Commutes.symm (hKiso N hN hNK))
      (Commutes.symm (hTiso N hN hNT))
  have hΩuz : ∀ N ∈ centralizingMembers (conjClass3 K) {e.u},
      N ∈ centralizingMembers (conjClass3 K) {z} ∧ N ≠ K ∧ N ≠ T := fun N hN =>
    ⟨⟨hN.1, hZ N hN⟩, fun h => hKu (h ▸ hN), fun h => hTu (h ▸ hN)⟩
  set Y : Subgroup G := centralizingLayer (conjClass3 K) {e.u} with hY
  set H : Subgroup G := Subgroup.normalizer (Y : Set G) with hH
  have hHu : Subgroup.centralizer ({e.u} : Set G) ≤ H :=
    centralizer_le_normalizer_centralizingLayer hR.inClass.conjInvariant e.u
  have hΦH : ∀ N ∈ centralizingMembers (conjClass3 K) {e.u}, N ≤ H := fun N hN =>
    (le_centralizingLayer hN).trans Subgroup.le_normalizer
  have hKH : K ≤ H := by
    intro k hk
    refine mem_normalizer_centralizingLayer_of_forall fun N hN n hn => ?_
    obtain ⟨hNz, hNK, -⟩ := hΩuz N hN
    exact hKiso N hNz hNK k hk n hn
  have hTH : T ≤ H := by
    intro k hk
    refine mem_normalizer_centralizingLayer_of_forall fun N hN n hn => ?_
    obtain ⟨hNz, -, hNT⟩ := hΩuz N hN
    exact hTiso N hNz hNT k hk n hn
  have hconjmem : ∀ c' ∈ Subgroup.centralizer ({z} : Set G), ∀ L ∈ centralizingMembers
      (conjClass3 K) {z}, conjSub c' L ∈ centralizingMembers (conjClass3 K) {z} := by
    intro c' hc L hL
    have hcz : c' * z * c'⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have := centralizingMembers_conj hR.inClass.conjInvariant c' z
    rw [hcz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  have hconjz : ∀ c' ∈ Subgroup.centralizer ({z} : Set G), ∀ B ∈ centralizingMembers
      (conjClass3 K) {z}, (∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ B → Commutes B L) →
      ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → N ≠ T → conjSub c' N ≠ B := by
    intro c' hc B hB hiso N hN hNK hNT hEq
    obtain ⟨L', hL', hL'N, hnc⟩ := c.exists_noncomm_of_ne hKz hT.mem hT.ne.symm hKiso hTiso hN hNK
      hNT
    have hne : conjSub c' L' ≠ B := by
      intro h
      apply hL'N
      apply conjSub_injective c'
      rw [h, ← hEq]
    have hcomm := hiso _ (hconjmem c' hc L' hL') hne
    rw [← hEq] at hcomm
    exact hnc ((commutes_conjSub_iff c').mp hcomm)
  have hHz : Subgroup.centralizer ({z} : Set G) ≤ H := by
    refine le_normalizer_centralizingLayer_of_forall fun c' hc N hN => ?_
    obtain ⟨hNz, hNK, hNT⟩ := hΩuz N hN
    exact hΦu _ (hconjmem c' hc N hNz) (hconjz c' hc K hKz hKiso N hNz hNK hNT)
      (hconjz c' hc T hT.mem hTiso N hNz hNK hNT)
  obtain ⟨n, hnK, hna⟩ := exists_inv_conj_of_exact3 hR.cls hKex e.mem_a e.mul_self_a
  have hna' : n * e.a' = e.a' * n := hKT' n hnK e.a' e.mem_a'
  have h1 : z * e.a = e.a⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_assoc, e.mul_self_a, hz2])
  have hnu : n * e.u * n⁻¹ = z * e.u := by
    have e1 : n * e.u * n⁻¹ = (n * e.a * n⁻¹) * (n * e.a' * n⁻¹) := by
      unfold TwinElt.u
      group
    have e2 : n * e.a' * n⁻¹ = e.a' := by rw [hna']; group
    rw [e1, hna, e2, ← h1]
    unfold TwinElt.u
    group
  have hHzu : Subgroup.centralizer ({z * e.u} : Set G) ≤ H := by
    intro c' hc
    have hc' : c' * (z * e.u) = (z * e.u) * c' := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hn1 : n * e.u = z * e.u * n := by
      calc n * e.u = n * e.u * n⁻¹ * n := by group
        _ = z * e.u * n := by rw [hnu]
    have hn2 : n⁻¹ * (z * e.u) = e.u * n⁻¹ := by
      calc n⁻¹ * (z * e.u) = n⁻¹ * (z * e.u * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * e.u) * n⁻¹ := by rw [hn1]
        _ = e.u * n⁻¹ := by group
    have hdu : n⁻¹ * c' * n ∈ Subgroup.centralizer ({e.u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n⁻¹ * c' * n * e.u = n⁻¹ * c' * (n * e.u) := by group
        _ = n⁻¹ * c' * (z * e.u * n) := by rw [hn1]
        _ = n⁻¹ * (c' * (z * e.u)) * n := by group
        _ = n⁻¹ * ((z * e.u) * c') * n := by rw [hc']
        _ = (n⁻¹ * (z * e.u)) * c' * n := by group
        _ = e.u * n⁻¹ * c' * n := by rw [hn2]
        _ = e.u * (n⁻¹ * c' * n) := by group
    have hceq : c' = n * (n⁻¹ * c' * n) * n⁻¹ := by group
    rw [hceq]
    exact H.mul_mem (H.mul_mem (hKH hnK) (hHu hdu)) (H.inv_mem (hKH hnK))
  have hJu : J ∈ centralizingMembers (conjClass3 K) {e.u} := hΦu J hJ hJK hJT
  have hJ₂u : A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} :=
    hΦu A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hYt : centralizingLayer (conjClass3 K) {t} ≤ H := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNJ : N = J
    · rw [hNJ]; exact hΦH J hJu
    by_cases hNJ₂ : N = A.J₂
    · rw [hNJ₂]; exact hΦH A.J₂ hJ₂u
    exact member_t_le_of_centralizers3 e hMF A H hHz hHu hHzu hz2 hu2 hzu hN hNJ hNJ₂
  have hYz : centralizingLayer (conjClass3 K) {z} ≤ H := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNK : N = K
    · rw [hNK]; exact hKH
    by_cases hNT : N = T
    · rw [hNT]; exact hTH
    exact hΦH N (hΦu N hN hNK hNT)
  have hHtop : H = ⊤ :=
    eq_top_of_layers3 ((CoreAssembly.deltaConnected_iff K).mp hR.conn) c hR.cls hT hJ hJK hJT A hYz
      hYt
  have hnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hHtop
  have := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
  · have hmem : t ∈ Y := le_centralizingLayer hJu hJt.mem
    rw [h, Subgroup.mem_bot] at hmem
    exact hJt.ne_one hmem
  · have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgY : g ∈ Y := by rw [h]; trivial
      have hk : ∀ N ∈ centralizingMembers (conjClass3 K) {e.u}, ∀ n ∈ N, z * n = n * z :=
        fun N hN n hn => (Subgroup.mem_centralizer_singleton_iff.mp (hZ N hN hn)).symm
      have h2 := conj_eq_of_forall_mem hk hgY
      calc g * z = z * g * z⁻¹ * z := by rw [h2]
        _ = z * g := by group
    rw [hcen, Subgroup.mem_bot] at hzc
    exact hz1 hzc

end Global

end CFSG.ClassicalInvolution.Q3.Q3TLK
