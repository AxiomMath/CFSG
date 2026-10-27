module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2Trans
public import CFSG.ClassicalInvolution.RouteD.TwinYR2XO
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Rows
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore signalizerFunctorEk)

local notation "𝒞" => CoreAssembly.conjClass

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}

theorem exists_twin_iso_at_t (S : RouteDSetup p f K z)
    (hKT : K ≠ T) (hTmem : T ∈ centralizingMembers (𝒞 K) {z})
    (hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N)
    (hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) (htz : t ≠ z) :
    ∃ J' : Subgroup G, J' ∈ centralizingMembers (𝒞 K) {t} ∧ J' ≠ J ∧
      IsClassicalMember p f J' t ∧ Commutes J' K ∧ Commutes J' T ∧
      (∀ L ∈ centralizingMembers (𝒞 K) {t}, L ≠ J → Commutes J L) ∧
      (∀ L ∈ centralizingMembers (𝒞 K) {t}, L ≠ J' → Commutes J' L) := by
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five clsT
  obtain ⟨g, hg0⟩ := hJ.1
  have hg : conjSub g K = J := hg0
  have hgz : t = g * z * g⁻¹ := by
    have h1 := hUz.conj g
    rw [hg] at h1
    exact hUt.eq h1
  have hΩc : centralizingMembers (𝒞 K) {t} = conjSub g '' centralizingMembers (𝒞 K) {z} := by
    rw [hgz]
    exact centralizingMembers_conj S.inClass.conjInvariant g z
  have hT'cls : IsClassicalMember p f (conjSub g T) t := by
    have := clsT.conj g
    rwa [← hgz] at this
  have hJT' : J ≠ conjSub g T := by
    intro h
    apply hKT
    have h1 : conjSub g K = conjSub g T := hg.trans h
    have h2 := congrArg (conjSub g⁻¹) h1
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
  have hT'iso : ∀ N ∈ centralizingMembers (𝒞 K) {t}, N ≠ conjSub g T →
      Commutes (conjSub g T) N := by
    intro N hN hne
    rw [hΩc] at hN
    obtain ⟨N₁, hN₁, rfl⟩ := hN
    have hne' : N₁ ≠ T := fun h => hne (by rw [h])
    exact (hTiso N₁ hN₁ hne').conjSub g
  have hJt' : J ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hJ.1, le_centralizer_of_isClassicalMember hJt⟩
  have hKt : K ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨CoreAssembly.mem_conjClass_self K, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKiso J hJ hJK k hk t hJt.mem
  have hTt : T ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨hTmem.1, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hTiso J hJ hJT k hk t hJt.mem
  have hKne : K ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution K t := by
      rw [h]
      exact ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hT'cls
    exact htz (hUz.eq h2).symm
  have hTne : T ≠ conjSub g T := by
    intro h
    have h2 : IsUniqueInvolution T t := by
      rw [h]
      exact ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hT'cls
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

end Twin

section Model

variable (p f : ℕ) [Fact p.Prime] (tY : StatedLieTag) (nY : ℕ)

structure TwinDatum (R R' : Subgroup (modelUniv tY nY p f Fact.out).K)
    (x x' : (modelUniv tY nY p f Fact.out).K) : Prop where
  mem : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D
  mem' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D
  ne : R ≠ R'
  comm : Commutes R R'
  hx : x ∈ R
  hx' : x' ∈ R'
  cx : ∀ r ∈ R, x * r = r * x
  cx' : ∀ r ∈ R', x' * r = r * x'
  nx : x ≠ 1
  nx' : x' ≠ 1
  same : x * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K

@[expose] def TwinMFCommutant : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY p f Fact.out).K) (x x' : (modelUniv tY nY p f Fact.out).K),
    TwinDatum p f tY nY R R' x x' →
    ∀ R'' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      (∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
        Commutes S R → Commutes S R' → Commutes R'' S) → R'' = R ∨ R'' = R'

@[expose] def TwinMFCentralizing : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY p f Fact.out).K) (x x' : (modelUniv tY nY p f Fact.out).K),
    TwinDatum p f tY nY R R' x x' →
    ∀ a ∈ R, ∀ a' ∈ R', a * a * x⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K →
      a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K →
      ∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
        (∀ s ∈ S, (a * a') * s = s * (a * a')) →
        ∃ g : (modelUniv tY nY p f Fact.out).K, g * (a * a') = (a * a') * g ∧
          Commutes (conjSub g S) R ∧ Commutes (conjSub g S) R'

@[expose] def TwinMFGeneration : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY p f Fact.out).K) (x x' : (modelUniv tY nY p f Fact.out).K),
    TwinDatum p f tY nY R R' x x' →
    ∀ a ∈ R, ∀ a' ∈ R', a * a * x⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K →
      a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K →
      ∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
        S ≤ Subgroup.centralizer ({x} : Set (modelUniv tY nY p f Fact.out).K) ⊔
          Subgroup.centralizer ({a * a'} : Set (modelUniv tY nY p f Fact.out).K) ⊔
          Subgroup.centralizer ({x * (a * a')} : Set (modelUniv tY nY p f Fact.out).K)

end Model

section Involution

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem locMk_involution_ne_one {x : G} {L : Subgroup G} {w : G}
    (hL : L ∈ centralizingMembers Ω {x}) (hw : IsClassicalMember p f L w) :
    locMk Ω x ⟨w, le_centralizingLayer hL hw.mem⟩ ≠ 1 := by
  intro h1
  set wY : ↥(locLayer Ω x) := ⟨w, le_centralizingLayer hL hw.mem⟩ with hwY
  have hwO : wY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := (QuotientGroup.eq_one_iff wY).mp h1
  have h2 : orderOf wY = 2 := by
    rw [hwY, Subgroup.orderOf_mk]
    exact hw.orderOf_eq_two
  have h3 : orderOf (⟨wY, hwO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have h4 := orderOf_dvd_natCard (⟨wY, hwO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
  rw [h3] at h4
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
    (even_iff_two_dvd.mpr h4)

end Involution

section AtTData

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure AtT (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (K T J : Subgroup G) (z t : G)
    (tY : StatedLieTag) (nY : ℕ) where
  J₂ : Subgroup G
  d : ShapeDictT2 p f tY nY (𝒞 K) t
  RK : Subgroup (modelUniv tY nY p f Fact.out).K
  RT : Subgroup (modelUniv tY nY p f Fact.out).K
  x : (modelUniv tY nY p f Fact.out).K
  x' : (modelUniv tY nY p f Fact.out).K
  hzY : z ∈ locLayer (𝒞 K) t
  rf : TwinRowFacts p f tY nY
  hP1 : LocalOddCentral (𝒞 K) {t}
  hJ₂z : J₂ ∈ centralizingMembers (𝒞 K) {z}
  hJ₂K : J₂ ≠ K
  hJ₂T : J₂ ≠ T
  hJ₂t : J₂ ∈ centralizingMembers (𝒞 K) {t}
  hJ₂J : J₂ ≠ J
  hJt : J ∈ centralizingMembers (𝒞 K) {t}
  hJiso : ∀ L ∈ centralizingMembers (𝒞 K) {t}, L ≠ J → Commutes J L
  hJ₂iso : ∀ L ∈ centralizingMembers (𝒞 K) {t}, L ≠ J₂ → Commutes J₂ L
  hKt : K ∈ centralizingMembers (𝒞 K) {t}
  hTt : T ∈ centralizingMembers (𝒞 K) {t}
  hRK : RK ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D
  hKR : locImg (𝒞 K) t K = RK.map d.ψ
  hRT : RT ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D
  hTR : locImg (𝒞 K) t T = RT.map d.ψ
  hxz : d.ψ x = locMk (𝒞 K) t ⟨z, hzY⟩
  hx'z : d.ψ x' = locMk (𝒞 K) t ⟨z, hzY⟩
  hdat : TwinDatum p f tY nY RK RT x x'

theorem exists_atT {K T J : Subgroup G} {z t : G} {tY : StatedLieTag} {nY : ℕ}
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) (htz : t ≠ z) :
    Nonempty (AtT p f K T J z t tY nY) := by
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hKT : K ≠ T := hT.ne.symm
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  obtain ⟨J₂, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso, hJ₂iso⟩ :=
    exists_twin_iso_at_t S hKT hT.mem hKiso hTiso clsT hJ hJK hJT hJt htz
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  have hJ₂z : J₂ ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hJ₂t.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hJ₂K.symm z S.cls.mem y hy).symm⟩
  have hJ₂K' : J₂ ≠ K := fun h => hncs K hKΩ (by rw [h] at hJ₂K; exact hJ₂K)
  have hJ₂T' : J₂ ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hJ₂T; exact hJ₂T)
  have hJΩ : J ∈ 𝒞 K := hJ.1
  have hcl : 𝒞 J = 𝒞 K := conjClass_eq_of_mem hJΩ
  have hP1t : LocalOddCentral (𝒞 K) {t} := by
    have := (S.of_mem_conjClass hJΩ hJt).p1
    rwa [hcl] at this
  have hshape_t : LocalShapeT p f 2 tY nY (𝒞 K) t := localShapeT_at_member S hJΩ hJt hshape
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hJΩ hJt hshape_t
  have hJmem : J ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hJΩ, le_centralizer_of_isClassicalMember hJt⟩
  have hJJ₂ : J ≠ J₂ := fun h => hJ₂J h.symm
  have hmemt : ∀ L : Subgroup G, L ∈ 𝒞 K → Commutes J L → L ∈ centralizingMembers (𝒞 K) {t} :=
    fun L hL hc => ⟨hL, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hc t hJt.mem y hy).symm⟩
  have hKt : K ∈ centralizingMembers (𝒞 K) {t} := hmemt K hKΩ (hKiso J hJ hJK).symm
  have hTt : T ∈ centralizingMembers (𝒞 K) {t} := hmemt T hT.mem.1 (hTiso J hJ hJT).symm
  obtain ⟨RK, hRK, hKR⟩ := big_of_ne S.inClass S.exact hP1t rf d hJmem hJ₂t hJJ₂ hJiso hJ₂iso hKt
    hJK.symm hJ₂K'.symm
  obtain ⟨RT, hRT, hTR⟩ := big_of_ne S.inClass S.exact hP1t rf d hJmem hJ₂t hJJ₂ hJiso hJ₂iso hTt
    hJT.symm hJ₂T'.symm
  have hzY : z ∈ locLayer (𝒞 K) t := le_centralizingLayer hKt S.cls.mem
  have hzK : locMk (𝒞 K) t ⟨z, hzY⟩ ∈ locImg (𝒞 K) t K :=
    ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr S.cls.mem, rfl⟩
  have hzT : locMk (𝒞 K) t ⟨z, hzY⟩ ∈ locImg (𝒞 K) t T :=
    ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr clsT.mem, rfl⟩
  rw [hKR] at hzK
  rw [hTR] at hzT
  obtain ⟨x, hxR, hxz⟩ := Subgroup.mem_map.mp hzK
  obtain ⟨x', hx'R, hx'z⟩ := Subgroup.mem_map.mp hzT
  have hζ1 : locMk (𝒞 K) t ⟨z, hzY⟩ ≠ 1 := locMk_involution_ne_one hKt S.cls
  have hx1 : x ≠ 1 := fun h => hζ1 (by rw [← hxz, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => hζ1 (by rw [← hx'z, h, map_one])
  have hsame : x * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K := by
    refine d.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxz, hx'z, mul_inv_cancel]
  have hcentral : ∀ {L : Subgroup G} {R : Subgroup (modelUniv tY nY p f Fact.out).K}
      {y : (modelUniv tY nY p f Fact.out).K} (hzL : ∀ k ∈ L, z * k = k * z)
      (hLR : locImg (𝒞 K) t L = R.map d.ψ) (hRp : R ≤ ⁅R, R⁆)
      (hy : d.ψ y = locMk (𝒞 K) t ⟨z, hzY⟩), ∀ r ∈ R, y * r = r * y := by
    intro L R y hzL hLR hRp hy
    refine commutes_of_commutator_mem_center hRp fun r hr => d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hy]
    have hrL : d.ψ r ∈ locImg (𝒞 K) t L := hLR ▸ Subgroup.mem_map_of_mem _ hr
    obtain ⟨k, hk, hkr⟩ := hrL
    rw [← hkr]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    show locMk (𝒞 K) t ⟨z, hzY⟩ * locMk (𝒞 K) t k = locMk (𝒞 K) t k * locMk (𝒞 K) t ⟨z, hzY⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hzL k (Subgroup.mem_subgroupOf.mp hk)
  have hRKT : RK ≠ RT := fun h => hKT (locImg_injOn S.inClass hP1t hKt hTt (by rw [hKR, hTR, h]))
  refine ⟨{
    J₂ := J₂
    d := d
    RK := RK
    RT := RT
    x := x
    x' := x'
    hzY := hzY
    rf := rf
    hP1 := hP1t
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
      comm := (commutes_iff_fund S.inClass hP1t rf d hKt hTt hRK hKR hTR).mp hKT'
      hx := hxR
      hx' := hx'R
      cx := hcentral S.cls.isCentralInvolution.central hKR (rf.perf RK hRK) hxz
      cx' := hcentral clsT.isCentralInvolution.central hTR (rf.perf RT hRT) hx'z
      nx := hx1
      nx' := hx'1
      same := hsame } }⟩

end AtTData

section NoCentral

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twinYNoCentralOn_of_model {P : StatedLieTag → ℕ → Prop}
    (hMF : ∀ tY nY, TwinRow tY nY → P tY nY → TwinMFCommutant p f tY nY) :
    TwinYNoCentralOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  by_contra hno
  push Not at hno
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  have hMJ : Commutes M J := hno J hJ hJK hJT
  have hMJ₂ : Commutes M A.J₂ := hno A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hMt : M ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hM.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hMJ y hy t hJt.mem)⟩
  have hMJne : M ≠ J := fun h => hncs J hJ.1 (by rw [h] at hMJ; exact hMJ)
  have hMJ₂ne : M ≠ A.J₂ := fun h => hncs A.J₂ A.hJ₂t.1 (by rw [h] at hMJ₂; exact hMJ₂)
  obtain ⟨RM, hRM, hMR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hMt hMJne hMJ₂ne
  have hcomm : ∀ S' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      Commutes S' A.RK → Commutes S' A.RT → Commutes RM S' := by
    intro S' hS' hcK hcT
    obtain ⟨L, hLmem, hLS⟩ := mem_locFamily_iff.mp (A.d.mem_fam S' hS')
    have hLJ : L ≠ J := by
      intro h
      subst h
      exact not_fund_of_isolated S.inClass A.hP1 A.rf A.d hLmem A.hJiso hS' hLS
    have hLJ₂ : L ≠ A.J₂ := by
      intro h
      subst h
      exact not_fund_of_isolated S.inClass A.hP1 A.rf A.d hLmem A.hJ₂iso hS' hLS
    have hLK : Commutes L K :=
      (commutes_iff_fund S.inClass A.hP1 A.rf A.d hLmem A.hKt hS' hLS A.hKR).mpr hcK
    have hLT : Commutes L T :=
      (commutes_iff_fund S.inClass A.hP1 A.rf A.d hLmem A.hTt hS' hLS A.hTR).mpr hcT
    have hLz : L ∈ centralizingMembers (𝒞 K) {z} :=
      ⟨hLmem.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (hLK y hy z S.cls.mem)⟩
    have hLK' : L ≠ K := fun h => hncs K hKΩ (by rw [h] at hLK; exact hLK)
    have hLT' : L ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hLT; exact hLT)
    exact (commutes_iff_fund S.inClass A.hP1 A.rf A.d hMt hLmem hRM hMR hLS).mp
      (hno L hLz hLK' hLT')
  have hMKu : K ∉ centralizingMembers (𝒞 K) {e.u} :=
    e.not_mem_centralizingMembers_left S.cls (S.exact K hKΩ) hodd hKT'
  have hMTu : T ∉ centralizingMembers (𝒞 K) {e.u} :=
    e.not_mem_centralizingMembers_right clsT (S.exact T hT.mem.1) hodd hKT'
  rcases hMF tY nY hrow hP A.RK A.RT A.x A.x' A.hdat RM hRM hcomm with h | h
  · have hMK : M = K := locImg_injOn S.inClass A.hP1 hMt A.hKt (by rw [hMR, A.hKR, h])
    exact hMKu (hMK ▸ hM)
  · have hMT : M = T := locImg_injOn S.inClass A.hP1 hMt A.hTt (by rw [hMR, A.hTR, h])
    exact hMTu (hMT ▸ hM)

end NoCentral

section Lifting

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_lift_commuting {x : G} {w y₀ : ↥(locLayer Ω x)} (hw : w * w = 1)
    (h : locMk Ω x y₀ * locMk Ω x w = locMk Ω x w * locMk Ω x y₀) :
    ∃ y : ↥(locLayer Ω x), locMk Ω x y = locMk Ω x y₀ ∧ y * w = w * y := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hw1 : y₀ * w * y₀⁻¹ * (y₀ * w * y₀⁻¹) = 1 := by
    calc y₀ * w * y₀⁻¹ * (y₀ * w * y₀⁻¹) = y₀ * (w * w) * y₀⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have e1 : locMk Ω x y₀ * locMk Ω x w * (locMk Ω x y₀)⁻¹ = locMk Ω x w := by
    rw [h]; group
  have hmem : y₀ * w * y₀⁻¹ * w ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show locMk Ω x (y₀ * w * y₀⁻¹ * w) = 1
    rw [map_mul, map_mul, map_mul, map_inv, e1, ← map_mul, hw, map_one]
  obtain ⟨o, hoN, hoeq⟩ :=
    CFSG.ClassicalInvolution.Generic.DeltaClosure.exists_conj_of_mul_mem hw hw1 hodd hmem
  have ho1 : locMk Ω x o = 1 := (QuotientGroup.eq_one_iff o).mpr hoN
  refine ⟨o⁻¹ * y₀, ?_, ?_⟩
  · rw [map_mul, map_inv, ho1, inv_one, one_mul]
  · have h1 : y₀ * w = o * w * o⁻¹ * y₀ := by
      calc y₀ * w = y₀ * w * y₀⁻¹ * y₀ := by group
        _ = o * w * o⁻¹ * y₀ := by rw [hoeq]
    calc o⁻¹ * y₀ * w = o⁻¹ * (y₀ * w) := by group
      _ = o⁻¹ * (o * w * o⁻¹ * y₀) := by rw [h1]
      _ = w * (o⁻¹ * y₀) := by group

theorem centralizer_locMk_le {x : G} {w : ↥(locLayer Ω x)} (hw : w * w = 1) :
    Subgroup.centralizer ({locMk Ω x w} : Set (locQuot Ω x)) ≤
      (Subgroup.centralizer ({w} : Set ↥(locLayer Ω x))).map (locMk Ω x) := by
  intro c hc
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective c
  have h : locMk Ω x y₀ * locMk Ω x w = locMk Ω x w * locMk Ω x y₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  obtain ⟨y, hy, hyw⟩ := exists_lift_commuting hw h
  exact ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hyw, hy⟩

theorem map_centralizer_le_locMk {x : G} {w : ↥(locLayer Ω x)} (hw : w * w = 1) {K : Type*}
    [Group K] (ψ : K →* locQuot Ω x) {k : K} (hk : ψ k = locMk Ω x w) :
    (Subgroup.centralizer ({k} : Set K)).map ψ ≤
      (Subgroup.centralizer ({w} : Set ↥(locLayer Ω x))).map (locMk Ω x) := by
  refine le_trans ?_ (centralizer_locMk_le hw)
  rintro _ ⟨c, hc, rfl⟩
  rw [← hk, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp hc]

omit [Finite G] in
theorem le_oddCoreIn_sup_of_locImg_le {x : G} {L : Subgroup G} {H₀ : Subgroup ↥(locLayer Ω x)}
    (hL : L ≤ locLayer Ω x) (h : locImg Ω x L ≤ H₀.map (locMk Ω x)) :
    L ≤ oddCoreIn (centLayer Ω x) ⊔ H₀.map (locLayer Ω x).subtype := by
  intro n hn
  obtain ⟨h₀, hh₀, hmk⟩ := h ⟨⟨n, hL hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  have hker : (⟨n, hL hn⟩ : ↥(locLayer Ω x)) * h₀⁻¹ ∈
      classicalInvolutionOddCore ↥(locLayer Ω x) := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show locMk Ω x (⟨n, hL hn⟩ * h₀⁻¹) = 1
    rw [map_mul, map_inv, ← hmk, mul_inv_cancel]
  have e : n = (((⟨n, hL hn⟩ : ↥(locLayer Ω x)) * h₀⁻¹ : ↥(locLayer Ω x)) : G) * (h₀ : G) := by
    simp
  rw [e]
  exact Subgroup.mul_mem_sup ⟨_, hker, rfl⟩ ⟨_, hh₀, rfl⟩

end Lifting

section Involutions

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem involution_ne_of_member [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hJt : IsClassicalMember p f J t) : t ≠ z := by
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  intro htz
  subst htz
  obtain ⟨L', hL', hL'J, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩ hT.mem
    hT.ne.symm hKiso hTiso hJ hJK hJT
  rcases S.cp_at_member hcen hJ.1 hJt hL' with h | h
  · exact hnc h
  · exact hL'J h

end Involutions

section Visible

variable {p f : ℕ} [Fact p.Prime]

theorem exists_lifts {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}
    {tY : StatedLieTag} {nY : ℕ} (A : AtT p f K T J z t tY nY) (e : TwinElt K T z) :
    ∃ ã ∈ A.RK, ∃ ã' ∈ A.RT,
      ã * ã * A.x⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K ∧
      ã' * ã' * A.x'⁻¹ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K ∧
      ∃ huY : e.u ∈ locLayer (𝒞 K) t,
        A.d.ψ (ã * ã') = locMk (𝒞 K) t ⟨e.u, huY⟩ := by
  have haY : e.a ∈ locLayer (𝒞 K) t := le_centralizingLayer A.hKt e.mem_a
  have ha'Y : e.a' ∈ locLayer (𝒞 K) t := le_centralizingLayer A.hTt e.mem_a'
  have huY : e.u ∈ locLayer (𝒞 K) t := mul_mem haY ha'Y
  have haK : locMk (𝒞 K) t ⟨e.a, haY⟩ ∈ locImg (𝒞 K) t K :=
    ⟨⟨e.a, haY⟩, Subgroup.mem_subgroupOf.mpr e.mem_a, rfl⟩
  have ha'T : locMk (𝒞 K) t ⟨e.a', ha'Y⟩ ∈ locImg (𝒞 K) t T :=
    ⟨⟨e.a', ha'Y⟩, Subgroup.mem_subgroupOf.mpr e.mem_a', rfl⟩
  rw [A.hKR] at haK
  rw [A.hTR] at ha'T
  obtain ⟨ã, hãR, hãa⟩ := Subgroup.mem_map.mp haK
  obtain ⟨ã', hã'R, hã'a⟩ := Subgroup.mem_map.mp ha'T
  refine ⟨ã, hãR, ã', hã'R, ?_, ?_, huY, ?_⟩
  · refine A.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hãa, A.hxz, ← map_mul]
    have : (⟨e.a, haY⟩ * ⟨e.a, haY⟩ : ↥(locLayer (𝒞 K) t)) = ⟨z, A.hzY⟩ :=
      Subtype.ext e.mul_self_a
    rw [this, mul_inv_cancel]
  · refine A.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hã'a, A.hx'z, ← map_mul]
    have : (⟨e.a', ha'Y⟩ * ⟨e.a', ha'Y⟩ : ↥(locLayer (𝒞 K) t)) = ⟨z, A.hzY⟩ :=
      Subtype.ext e.mul_self_a'
    rw [this, mul_inv_cancel]
  · rw [map_mul, hãa, hã'a, ← map_mul]
    rfl

theorem twinYVisibleOn_of_model {P : StatedLieTag → ℕ → Prop}
    (hMF : ∀ tY nY, TwinRow tY nY → P tY nY → TwinMFCentralizing p f tY nY) :
    TwinYVisibleOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt M hM hMt hMJ
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hXO := twinYXOrbit p f G hnab K z S tY nY hrow hshape T hT clsT e
  by_cases hM2 : M = A.J₂
  · obtain ⟨y, hy, hyJ⟩ := hXO J hJ hJK hJT A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
    exact ⟨y, centralizingLayer_le_centralizer (𝒞 K) {e.u} hy, by rw [hyJ, hM2]⟩
  have hMtm : M ∈ centralizingMembers (𝒞 K) {t} := ⟨hM.1, hMt⟩
  obtain ⟨RM, hRM, hMR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hMtm hMJ hM2
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  have hcommM : ∀ s ∈ RM, (ã * ã') * s = s * (ã * ã') := by
    have h1 : locImg (𝒞 K) t M ≤ Subgroup.centralizer ({locMk (𝒞 K) t ⟨e.u, huY⟩} : Set _) :=
      (le_centralizer_iff_locImg S.inClass A.hP1 hMtm ⟨e.u, huY⟩).mp hM.2
    have h2 : RM ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY p f Fact.out).K) :=
      (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf RM hRM) (ã * ã')).mpr (by
        rw [hψu, ← hMR]
        exact h1)
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hs)).symm
  obtain ⟨g, hgu, hgK, hgT⟩ := hMF tY nY hrow hP A.RK A.RT A.x A.x' A.hdat ã hãR ã' hã'R hsq hsq'
    RM hRM hcommM
  have hgfund := conjSub_mem_fundamentalSubgroups hRM g
  obtain ⟨L, hLmem, hLS⟩ := mem_locFamily_iff.mp (A.d.mem_fam _ hgfund)
  have hLK : Commutes L K :=
    (commutes_iff_fund S.inClass A.hP1 A.rf A.d hLmem A.hKt hgfund hLS A.hKR).mpr hgK
  have hLT : Commutes L T :=
    (commutes_iff_fund S.inClass A.hP1 A.rf A.d hLmem A.hTt hgfund hLS A.hTR).mpr hgT
  have hLz : L ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hLmem.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hLK y hy z S.cls.mem)⟩
  have hLK' : L ≠ K := fun h => hncs K hKΩ (by rw [h] at hLK; exact hLK)
  have hLT' : L ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hLT; exact hLT)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(locLayer (𝒞 K) t), locMk (𝒞 K) t y₀ = A.d.ψ g :=
    QuotientGroup.mk_surjective _
  have hcomm : locMk (𝒞 K) t y₀ * locMk (𝒞 K) t ⟨e.u, huY⟩ =
      locMk (𝒞 K) t ⟨e.u, huY⟩ * locMk (𝒞 K) t y₀ := by
    rw [hy₀, ← hψu, ← map_mul, ← map_mul, hgu]
  obtain ⟨y, hyk, hyw⟩ := exists_lift_commuting (w := ⟨e.u, huY⟩) (Subtype.ext hu2) hcomm
  have hyu : (y : G) ∈ Subgroup.centralizer ({e.u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyw)
  have hyt : (y : G) ∈ Subgroup.centralizer ({t} : Set G) :=
    centralizingLayer_le_centralizer (𝒞 K) {t} y.2
  have hMy : conjSub (y : G) M ∈ centralizingMembers (𝒞 K) {t} := by
    refine ⟨S.inClass.conjInvariant _ M hM.1, fun x hx => ?_⟩
    have h1 : (y : G)⁻¹ * x * y ∈ M := mem_conjSub_iff.mp hx
    have h2 := hMt h1
    have e' : x = (y : G) * ((y : G)⁻¹ * x * y) * (y : G)⁻¹ := by group
    rw [e']
    exact mul_mem (mul_mem hyt h2) (inv_mem hyt)
  have hMyL : conjSub (y : G) M = L := by
    refine locImg_injOn S.inClass A.hP1 hMy hLmem ?_
    rw [locImg_conjSub_layer M y, hMR, hyk, hy₀, hLS]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp
  obtain ⟨x₁, hx₁, hxJ⟩ := hXO J hJ hJK hJT L hLz hLK' hLT'
  refine ⟨(y : G)⁻¹ * x₁, mul_mem (inv_mem hyu) (centralizingLayer_le_centralizer (𝒞 K) {e.u} hx₁),
    ?_⟩
  rw [conjSub_mul, hxJ, ← hMyL, conjSub_inv_conjSub]

end Visible

section Generation

variable {p f : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem mem_centralizer_pair {G : Type} [Group G] {n x y : G} (hx : x * n = n * x)
    (hy : y * n = n * y) :
    n ∈ Subgroup.centralizer ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | rfl
  · exact hx
  · exact hy

theorem twinYGenTOn_of_model {P : StatedLieTag → ℕ → Prop}
    (hMF : ∀ tY nY, TwinRow tY nY → P tY nY → TwinMFGeneration p f tY nY) :
    TwinYGenTOn p f P := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  have hKex := S.exact K hKΩ
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have ht1 : t ≠ 1 := ne_one_of_orderOf_eq_two hJt.orderOf_eq_two
  have hu1 : e.u ≠ 1 := e.u_ne_one S.cls hKex hodd hKT'
  have huz : e.u ≠ z := e.u_ne_z S.cls hKex hodd hKT'
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  have hzt : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.mp (hJ.2 hJt.mem)).symm
  have hut : e.u * t = t * e.u := (Subgroup.mem_centralizer_singleton_iff.mp (hJu.2 hJt.mem)).symm
  have hzu : z * e.u = e.u * z :=
    (e.u_comm_z (le_centralizer_of_isClassicalMember S.cls)
      (le_centralizer_of_isClassicalMember clsT)).symm
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hT.comm_K J hJ hJK k hk t hJt.mem)
  have hnotK : ¬ K ≤ Subgroup.centralizer ({e.u} : Set G) :=
    e.not_le_centralizer_left S.cls hKex hodd hKT'
  have hut' : e.u ≠ t := fun h => hnotK (by rw [h]; exact hKt)
  have hzut : z * e.u ≠ t := by
    intro h
    apply hnotK
    have hu_eq : e.u = z * t := by
      calc e.u = z * (z * e.u) := by rw [← mul_assoc, hz2, one_mul]
        _ = z * t := by rw [h]
    intro k hk
    have hkz : k * z = z * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isClassicalMember S.cls hk)
    have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKt hk)
    rw [Subgroup.mem_centralizer_singleton_iff, hu_eq]
    calc k * (z * t) = (k * z) * t := by group
      _ = (z * k) * t := by rw [hkz]
      _ = z * (k * t) := by group
      _ = z * (t * k) := by rw [hkt]
      _ = z * t * k := by group
  have hzu2 : z * e.u * (z * e.u) = 1 := by
    calc z * e.u * (z * e.u) = z * (e.u * z) * e.u := by group
      _ = z * (z * e.u) * e.u := by rw [← hzu]
      _ = (z * z) * (e.u * e.u) := by group
      _ = 1 := by rw [hz2, hu2, one_mul]
  have hzu1 : z * e.u ≠ 1 := fun h =>
    huz ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hz2))
  have hzutc : z * e.u * t = t * (z * e.u) := by
    calc z * e.u * t = z * (e.u * t) := by group
      _ = z * (t * e.u) := by rw [hut]
      _ = (z * t) * e.u := by group
      _ = (t * z) * e.u := by rw [hzt]
      _ = t * (z * e.u) := by group
  set B := Subgroup.closure ({z, e.u, t} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have huB : e.u ∈ B := Subgroup.subset_closure (by simp)
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hF₁ : Subgroup.closure ({z, t} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    closure_pair_mem_signalizer hzB htB hz2 ht2 hz1 ht1 htz.symm hzt
  have hF₂ : Subgroup.closure ({e.u, t} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    closure_pair_mem_signalizer huB htB hu2 ht2 hu1 ht1 hut' hut
  have hF₃ : Subgroup.closure ({z * e.u, t} : Set G) ∈ signalizerFunctorEk 2 2 B :=
    closure_pair_mem_signalizer (mul_mem hzB huB) htB hzu2 ht2 hzu1 ht1 hzut hzutc
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  have hY : exactLayer (𝒞 K) t = centLayer (𝒞 K) t := by
    unfold exactLayer centLayer
    rw [centMembers_exactFamily, exactFamily_eq_centMembers_of_exact S.exact S.inClass.classical]
  unfold CentralizerGenerationStar
  rw [hY]
  refine centLayer_le fun N hN => ?_
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := hN.2
  by_cases hNJ : N = J ∨ N = A.J₂
  · have hNz : N ≤ Subgroup.centralizer ({z} : Set G) := by
      rcases hNJ with rfl | rfl
      · exact hJ.2
      · exact A.hJ₂z.2
    exact le_sup_of_le_right (le_iSup₂_of_le _ hF₁ (le_inf (le_centralizer_pair hNz hNt)
      (le_centLayer hN)))
  push Not at hNJ
  obtain ⟨RN, hRN, hNR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hN hNJ.1 hNJ.2
  have hgen := hMF tY nY hrow hP A.RK A.RT A.x A.x' A.hdat ã hãR ã' hã'R hsq hsq' RN hRN
  set w₁ : ↥(locLayer (𝒞 K) t) := ⟨z, A.hzY⟩ with hw₁
  set w₂ : ↥(locLayer (𝒞 K) t) := ⟨e.u, huY⟩ with hw₂
  have hw₁₁ : w₁ * w₁ = 1 := Subtype.ext hz2
  have hw₂₂ : w₂ * w₂ = 1 := Subtype.ext hu2
  have hw₃₃ : w₁ * w₂ * (w₁ * w₂) = 1 := Subtype.ext hzu2
  have hψ₃ : A.d.ψ (A.x * (ã * ã')) = locMk (𝒞 K) t (w₁ * w₂) := by
    rw [map_mul, A.hxz, hψu, ← map_mul]
  have hloc : locImg (𝒞 K) t N ≤
      ((Subgroup.centralizer ({w₁} : Set ↥(locLayer (𝒞 K) t)) ⊔
        Subgroup.centralizer ({w₂} : Set ↥(locLayer (𝒞 K) t))) ⊔
        Subgroup.centralizer ({w₁ * w₂} : Set ↥(locLayer (𝒞 K) t))).map (locMk (𝒞 K) t) := by
    rw [hNR, Subgroup.map_sup, Subgroup.map_sup]
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le_sup (sup_le_sup (map_centralizer_le_locMk hw₁₁ A.d.ψ A.hxz)
      (map_centralizer_le_locMk hw₂₂ A.d.ψ hψu)) (map_centralizer_le_locMk hw₃₃ A.d.ψ hψ₃)
  have hN' := le_oddCoreIn_sup_of_locImg_le (le_centLayer hN) hloc
  refine hN'.trans (sup_le_sup_left ?_ _)
  have key : ∀ {f₀ : G} {F : Subgroup G} (w : ↥(locLayer (𝒞 K) t)), (w : G) = f₀ →
      F = Subgroup.closure ({f₀, t} : Set G) → F ∈ signalizerFunctorEk 2 2 B →
      (Subgroup.centralizer ({w} : Set ↥(locLayer (𝒞 K) t))).map (locLayer (𝒞 K) t).subtype ≤
        ⨆ F ∈ signalizerFunctorEk 2 2 B,
          (Subgroup.centralizer (F : Set G) ⊓ centLayer (𝒞 K) t) := by
    intro f₀ F w hw hF hFs
    rintro _ ⟨y, hy, rfl⟩
    have hyw : (y : G) * f₀ = f₀ * (y : G) := by
      rw [← hw]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    have hyt : (y : G) * t = t * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer (𝒞 K) {t} y.2)
    have hmem : (y : G) ∈ Subgroup.centralizer (F : Set G) ⊓ centLayer (𝒞 K) t := by
      refine ⟨?_, y.2⟩
      rw [hF]
      exact mem_centralizer_pair hyw.symm hyt.symm
    exact (le_iSup₂_of_le F hFs le_rfl : Subgroup.centralizer (F : Set G) ⊓ centLayer (𝒞 K) t ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ centLayer (𝒞 K) t)) hmem
  rw [Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le (sup_le (key w₁ rfl rfl hF₁) (key w₂ rfl rfl hF₂)) (key (w₁ * w₂) rfl rfl hF₃)

end Generation

end CFSG.ClassicalInvolution.RouteD.TwinY
