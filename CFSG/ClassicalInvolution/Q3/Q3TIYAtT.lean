module

public import CFSG.ClassicalInvolution.Q3.Q3TIVCent
public import CFSG.ClassicalInvolution.Q3.Q3TIVSm2
public import CFSG.ClassicalInvolution.Q3.Q3TY12
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn)


section Element

variable {G : Type} [Group G] {K T : Subgroup G} {z : G}

theorem twinElt_not_le_centralizer_left3 (e : TwinElt K T z) (hz : IsClassicalMember3 K z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hKT : Commutes K T) :
    ¬ K ≤ Subgroup.centralizer ({e.u} : Set G) := by
  intro hle
  have hc : ∀ k ∈ K, k * e.a = e.a * k := by
    intro k hk
    have h1 : k * e.u = e.u * k := Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
    have h2 : k * e.a' = e.a' * k := hKT k hk _ e.mem_a'
    have h3 : k * e.a * e.a' = e.a * k * e.a' := by
      calc k * e.a * e.a' = k * e.u := by unfold TwinElt.u; group
        _ = e.u * k := h1
        _ = e.a * (e.a' * k) := by unfold TwinElt.u; group
        _ = e.a * (k * e.a') := by rw [h2]
        _ = e.a * k * e.a' := by group
    exact mul_right_cancel h3
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hsq := e.mul_self_a
  rcases Q3TY.eq_one_or_eq_of_central3 hz hexK e.mem_a hc with h1 | h1
  · rw [h1, one_mul] at hsq
    exact hz.ne_one hsq.symm
  · rw [h1, hz2] at hsq
    exact hz.ne_one hsq.symm

theorem twinElt_not_le_centralizer_right3 (e : TwinElt K T z) (hzT : IsClassicalMember3 T z)
    (hexT : classicalInvolutionOddCore T = ⊥) (hKT : Commutes K T) :
    ¬ T ≤ Subgroup.centralizer ({e.u} : Set G) := by
  intro hle
  have hc : ∀ k ∈ T, k * e.a' = e.a' * k := by
    intro k hk
    have h1 : k * e.u = e.u * k := Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
    have h2 : e.a * k = k * e.a := hKT _ e.mem_a k hk
    have h3 : e.a * (k * e.a') = e.a * (e.a' * k) := by
      calc e.a * (k * e.a') = (e.a * k) * e.a' := by group
        _ = (k * e.a) * e.a' := by rw [h2]
        _ = k * e.u := by unfold TwinElt.u; group
        _ = e.u * k := h1
        _ = e.a * (e.a' * k) := by unfold TwinElt.u; group
    exact mul_left_cancel h3
  have hz2 : z * z = 1 := hzT.isCentralInvolution.sq
  have hsq := e.mul_self_a'
  rcases Q3TY.eq_one_or_eq_of_central3 hzT hexT e.mem_a' hc with h1 | h1
  · rw [h1, one_mul] at hsq
    exact hzT.ne_one hsq.symm
  · rw [h1, hz2] at hsq
    exact hzT.ne_one hsq.symm

end Element

theorem not_commutes_self_of_mem3 {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) : ∀ L ∈ conjClass3 K, ¬ Commutes L L := fun L hL => by
  obtain ⟨w, hw⟩ := hR.inClass.classical L hL
  exact not_commutes_self3 hw

section Twin

variable {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}

theorem exists_twin_iso_at_t3 (hR : RouteD3Setup K z) (hKT : K ≠ T)
    (hTmem : T ∈ centralizingMembers (conjClass3 K) {z})
    (hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N)
    (clsT : IsClassicalMember3 T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (hJt : IsClassicalMember3 J t) (htz : t ≠ z) :
    ∃ J' : Subgroup G, J' ∈ centralizingMembers (conjClass3 K) {t} ∧ J' ≠ J ∧
      IsClassicalMember3 J' t ∧ Commutes J' K ∧ Commutes J' T ∧
      (∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J → Commutes J L) ∧
      (∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J' → Commutes J' L) := by
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hUz := isUniqueInvolution_of_exact3 (hex K hKΩ) hR.cls
  have hUt := isUniqueInvolution_of_exact3 (hex J hJ.1) hJt
  have hUT := isUniqueInvolution_of_exact3 (hex T hTmem.1) clsT
  obtain ⟨g, hg0⟩ := hJ.1
  have hg : conjSub g K = J := hg0
  have hgz : t = g * z * g⁻¹ := by
    have h1 := hUz.conj g
    rw [hg] at h1
    exact hUt.eq h1
  have hΩc : centralizingMembers (conjClass3 K) {t} =
      conjSub g '' centralizingMembers (conjClass3 K) {z} := by
    rw [hgz]
    exact centralizingMembers_conj hR.inClass.conjInvariant g z
  have hT'cls : IsClassicalMember3 (conjSub g T) t := by
    have := clsT.conj g
    rwa [← hgz] at this
  have hT'Ω : conjSub g T ∈ conjClass3 K := hR.inClass.conjInvariant g T hTmem.1
  have hJT' : J ≠ conjSub g T := by
    intro h
    apply hKT
    have h1 : conjSub g K = conjSub g T := hg.trans h
    have h2 := congrArg (conjSub g⁻¹) h1
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  have hT'iso : ∀ N ∈ centralizingMembers (conjClass3 K) {t}, N ≠ conjSub g T →
      Commutes (conjSub g T) N := by
    intro N hN hne
    rw [hΩc] at hN
    obtain ⟨N₁, hN₁, rfl⟩ := hN
    have hne' : N₁ ≠ T := fun h => hne (by rw [h])
    exact (hTiso N₁ hN₁ hne').conjSub g
  have hJt' : J ∈ centralizingMembers (conjClass3 K) {t} := ⟨hJ.1, isSubnormal_le hJt.subnormal⟩
  have hKt : K ∈ centralizingMembers (conjClass3 K) {t} := by
    refine ⟨hKΩ, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKiso J hJ hJK k hk t hJt.mem
  have hTt : T ∈ centralizingMembers (conjClass3 K) {t} := by
    refine ⟨hTmem.1, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hTiso J hJ hJT k hk t hJt.mem
  have hKne : K ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution K t := by
      rw [h]
      exact isUniqueInvolution_of_exact3 (hex _ hT'Ω) hT'cls
    exact htz (hUz.eq h2).symm
  have hTne : T ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution T t := by
      rw [h]
      exact isUniqueInvolution_of_exact3 (hex _ hT'Ω) hT'cls
    exact htz (hUT.eq h2).symm
  refine ⟨conjSub g T, ?_, fun h => hJT' h.symm, hT'cls, hT'iso K hKt hKne, hT'iso T hTt hTne,
    ?_, hT'iso⟩
  · rw [hΩc]
    exact ⟨T, hTmem, rfl⟩
  · intro L hL hLJ
    rw [hΩc] at hL
    obtain ⟨N₁, hN₁, rfl⟩ := hL
    have hne : N₁ ≠ K := fun h => hLJ (by rw [h, hg])
    rw [← hg]
    exact (hKiso N₁ hN₁ hne).conjSub g

variable [IsSimpleGroup G]

theorem involution_ne_of_member3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    {tY : StatedLieTag} {nY : ℕ} (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (hJ : J ∈ centralizingMembers (conjClass3 K) {z})
    (hJK : J ≠ K) (hJT : J ≠ T) (hJt : IsClassicalMember3 J t) : t ≠ z := by
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨⟨1, conjSub_one K⟩, isSubnormal_le hR.cls.subnormal⟩
  intro htz
  subst htz
  obtain ⟨L', hL', hL'J, hnc⟩ := c.exists_noncomm_of_ne hKz hT.mem hT.ne.symm
    (fun N hN hNK => hT.comm_K N hN hNK) (fun N hN hNT => hT.comm_T N hN hNT) hJ hJK hJT
  rcases cp_at_member3 h3 hnab hR hJ.1 hJt hL' with h | h
  · exact hnc h
  · exact hL'J h

end Twin

structure AtT3 {G : Type} [Group G] (K T J : Subgroup G) (z t : G) (tY : StatedLieTag)
    (nY : ℕ) where
  J₂ : Subgroup G
  c : TwinLoc3 tY nY (conjClass3 K) t
  clsJ : IsClassicalMember3 J t
  clsJ₂ : IsClassicalMember3 J₂ t
  RK : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K
  RT : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K
  x : (modelUniv tY nY 3 1 Nat.prime_three).K
  x' : (modelUniv tY nY 3 1 Nat.prime_three).K
  hzY : z ∈ locLayer (conjClass3 K) t
  hJ₂z : J₂ ∈ centralizingMembers (conjClass3 K) {z}
  hJ₂K : J₂ ≠ K
  hJ₂T : J₂ ≠ T
  hJ₂t : J₂ ∈ centralizingMembers (conjClass3 K) {t}
  hJ₂J : J₂ ≠ J
  hJt : J ∈ centralizingMembers (conjClass3 K) {t}
  hJiso : ∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J → Commutes J L
  hJ₂iso : ∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J₂ → Commutes J₂ L
  hKt : K ∈ centralizingMembers (conjClass3 K) {t}
  hTt : T ∈ centralizingMembers (conjClass3 K) {t}
  hRK : RK ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D
  hKR : locImg (conjClass3 K) t K = RK.map c.d.ψ
  hRT : RT ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D
  hTR : locImg (conjClass3 K) t T = RT.map c.d.ψ
  hxz : c.d.ψ x = Gaps.locMk (conjClass3 K) t ⟨z, hzY⟩
  hx'z : c.d.ψ x' = Gaps.locMk (conjClass3 K) t ⟨z, hzY⟩
  hdat : TwinDatumOn tY (modelUniv tY nY 3 1 Nat.prime_three) RK RT x x'

section Exists

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem exists_atT3 (h3 : OddThreeFreeInput) (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z)
    (hJ : J ∈ centralizingMembers (conjClass3 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hJt : IsClassicalMember3 J t) (htz : t ≠ z) : Nonempty (AtT3 K T J z t tY nY) := by
  have rf := twinRowFacts3_of_row hrow
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hKT : K ≠ T := hT.ne.symm
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  obtain ⟨J₂, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso, hJ₂iso⟩ :=
    exists_twin_iso_at_t3 hR hKT hT.mem hKiso hTiso clsT hJ hJK hJT hJt htz
  have hncs := not_commutes_self_of_mem3 hR
  have hJ₂z : J₂ ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hJ₂t.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hJ₂K.symm z hR.cls.mem y hy).symm⟩
  have hJ₂K' : J₂ ≠ K := fun h => hncs K hKΩ (by rw [h] at hJ₂K; exact hJ₂K)
  have hJ₂T' : J₂ ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hJ₂T; exact hJ₂T)
  have hJΩ : J ∈ conjClass3 K := hJ.1
  have hcl : conjClass3 J = conjClass3 K := conjClass3_eq_of_mem hJΩ
  have hSJ : RouteD3Setup J t := RouteD3Setup.of_mem_conjClass3 hR hJΩ hJt
  have hshape_t : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 J) t :=
    Q3TY.localShapeC3_at_member hR hshape hJΩ hJt
  obtain ⟨c0⟩ := TwinLoc3.of_setup rf h3 hSJ hshape_t
  rw [hcl] at c0
  have hJmem : J ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hJΩ, isSubnormal_le hJt.subnormal⟩
  have hJJ₂ : J ≠ J₂ := fun h => hJ₂J h.symm
  have hmemt : ∀ L : Subgroup G, L ∈ conjClass3 K → Commutes J L →
      L ∈ centralizingMembers (conjClass3 K) {t} := fun L hL hc =>
    ⟨hL, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hc t hJt.mem y hy).symm⟩
  have hKt : K ∈ centralizingMembers (conjClass3 K) {t} :=
    hmemt K hKΩ (hKiso J hJ hJK).symm
  have hTt : T ∈ centralizingMembers (conjClass3 K) {t} :=
    hmemt T hT.mem.1 (hTiso J hJ hJT).symm
  obtain ⟨RK, hRK, hKR⟩ := c0.big_of_ne hJmem hJ₂t hJJ₂ hJiso hJ₂iso hKt hJK.symm hJ₂K'.symm
  obtain ⟨RT, hRT, hTR⟩ := c0.big_of_ne hJmem hJ₂t hJJ₂ hJiso hJ₂iso hTt hJT.symm hJ₂T'.symm
  have hzY : z ∈ locLayer (conjClass3 K) t := le_centralizingLayer hKt hR.cls.mem
  obtain ⟨_, x, hxR, hxc, hx1, hx⟩ := c0.exists_central_lift hKt hR.cls hRK hKR
  obtain ⟨_, x', hx'R, hx'c, hx'1, hx'⟩ := c0.exists_central_lift hTt clsT hRT hTR
  have hxz : c0.d.ψ x = Gaps.locMk (conjClass3 K) t ⟨z, hzY⟩ := hx.symm
  have hx'z : c0.d.ψ x' = Gaps.locMk (conjClass3 K) t ⟨z, hzY⟩ := hx'.symm
  have hsame : x * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K := by
    refine c0.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxz, hx'z, mul_inv_cancel]
  have hRKT : RK ≠ RT := fun h => hKT (locImg_injOn3 c0.hΩ c0.hex c0.hP1 c0.hO3 hKt hTt
    (by rw [hKR, hTR, h]))
  exact ⟨{
    J₂ := J₂
    c := c0
    clsJ := hJt
    clsJ₂ := hJ₂cls
    RK := RK
    RT := RT
    x := x
    x' := x'
    hzY := hzY
    hJ₂z := hJ₂z
    hJ₂K := hJ₂K'
    hJ₂T := hJ₂T'
    hJ₂t := hJ₂t
    hJ₂J := hJ₂J
    hJt := hJmem
    hJiso := hJiso
    hJ₂iso := hJ₂iso
    hKt := hKt
    hTt := hTt
    hRK := hRK
    hKR := hKR
    hRT := hRT
    hTR := hTR
    hxz := hxz
    hx'z := hx'z
    hdat := {
      mem := hRK
      mem' := hRT
      ne := hRKT
      comm := (c0.commutes_iff_fund hKt hTt hRK hKR hTR).mp hKT'
      hx := hxR
      hx' := hx'R
      cx := hxc
      cx' := hx'c
      nx := hx1
      nx' := hx'1
      same := hsame } }⟩

theorem exists_lifts3 (A : AtT3 K T J z t tY nY) (e : TwinElt K T z) :
    ∃ ã ∈ A.RK, ∃ ã' ∈ A.RT,
      ã * ã * A.x⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      ã' * ã' * A.x'⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      ∃ huY : e.u ∈ locLayer (conjClass3 K) t,
        A.c.d.ψ (ã * ã') = Gaps.locMk (conjClass3 K) t ⟨e.u, huY⟩ := by
  have haY : e.a ∈ locLayer (conjClass3 K) t := le_centralizingLayer A.hKt e.mem_a
  have ha'Y : e.a' ∈ locLayer (conjClass3 K) t := le_centralizingLayer A.hTt e.mem_a'
  have huY : e.u ∈ locLayer (conjClass3 K) t := mul_mem haY ha'Y
  have haK : Gaps.locMk (conjClass3 K) t ⟨e.a, haY⟩ ∈ locImg (conjClass3 K) t K :=
    ⟨⟨e.a, haY⟩, Subgroup.mem_subgroupOf.mpr e.mem_a, rfl⟩
  have ha'T : Gaps.locMk (conjClass3 K) t ⟨e.a', ha'Y⟩ ∈ locImg (conjClass3 K) t T :=
    ⟨⟨e.a', ha'Y⟩, Subgroup.mem_subgroupOf.mpr e.mem_a', rfl⟩
  rw [A.hKR] at haK
  rw [A.hTR] at ha'T
  obtain ⟨ã, hãR, hãa⟩ := Subgroup.mem_map.mp haK
  obtain ⟨ã', hã'R, hã'a⟩ := Subgroup.mem_map.mp ha'T
  refine ⟨ã, hãR, ã', hã'R, ?_, ?_, huY, ?_⟩
  · refine A.c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hãa, A.hxz, ← map_mul]
    have : (⟨e.a, haY⟩ * ⟨e.a, haY⟩ : ↥(locLayer (conjClass3 K) t)) = ⟨z, A.hzY⟩ :=
      Subtype.ext e.mul_self_a
    rw [this, mul_inv_cancel]
  · refine A.c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hã'a, A.hx'z, ← map_mul]
    have : (⟨e.a', ha'Y⟩ * ⟨e.a', ha'Y⟩ : ↥(locLayer (conjClass3 K) t)) = ⟨z, A.hzY⟩ :=
      Subtype.ext e.mul_self_a'
    rw [this, mul_inv_cancel]
  · rw [map_mul, hãa, hã'a, ← map_mul]
    rfl

theorem AtT3.nbhd_iff (A : AtT3 K T J z t tY nY) {N : Subgroup G} (hN : N ∈ conjClass3 K) :
    (N = J ∨ Commutes N J) ↔ (N = A.J₂ ∨ Commutes N A.J₂) := by
  have hJJ₂ : Commutes J A.J₂ := A.hJiso A.J₂ A.hJ₂t A.hJ₂J
  have hmem : ∀ {M : Subgroup G}, IsClassicalMember3 M t → Commutes N M →
      N ∈ centralizingMembers (conjClass3 K) {t} := fun hM hc =>
    ⟨hN, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hc y hy t hM.mem)⟩
  constructor
  · rintro (h | hc)
    · rw [h]
      exact Or.inr hJJ₂
    · have hNt := hmem A.clsJ hc
      by_cases h : N = A.J₂
      · exact Or.inl h
      · exact Or.inr (A.hJ₂iso N hNt h).symm
  · rintro (h | hc)
    · rw [h]
      exact Or.inr hJJ₂.symm
    · have hNt := hmem A.clsJ₂ hc
      by_cases h : N = J
      · exact Or.inl h
      · exact Or.inr (A.hJiso N hNt h).symm

end Exists

end CFSG.ClassicalInvolution.Q3.Q3TIV
