module

public import CFSG.GH74.Generic.BProg.Stage2Defs
public import CFSG.GH74.GLS.C3.Layer1.St1Iv251
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
import CFSG.GH74.GLS.TwoThin.Rank
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

namespace T1Sylow

open C3.Layer1 C3.Layer1.PumpCalc C3.Layer1.PumpRigid C3.Layer1.Iv251 CFSG.ComponentClassification

private theorem x_mem_Q_aux (hs : Stage2Setup G x K A M P Q) : x ∈ Q := by
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hKC : K ≤ centralizer ({x} : Set G) := hs.pair.1.1.1.2.2.1
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxP : x ∈ P := by
    obtain ⟨S, hS⟩ := hs.sylowP
    have hcent : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ∈
        Subgroup.center ↥(centralizer ({x} : Set G)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : (g : G) ∈ centralizer ({x} : Set G) := g.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg)
    have hN : (zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))).Normal :=
      normal_of_le_center (zpowers_le.2 hcent)
    have hx'2 : orderOf (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
      rw [← orderOf_injective (centralizer ({x} : Set G)).subtype
        (centralizer ({x} : Set G)).subtype_injective ⟨x, hxC⟩]
      exact hx2
    have hp : IsPGroup 2 (zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx'2, pow_one]
    have hle := IsPGroup.le_sylow_of_normal hp S
    rw [← hS]
    exact ⟨⟨x, hxC⟩, hle (mem_zpowers _), rfl⟩
  have hcentK : x ∈ centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => mem_centralizer_singleton_iff.mp (hKC hk)
  have hN : x ∈ normalizer (K : Set G) := Subgroup.centralizer_le_normalizer (K : Set G) hcentK
  have hxCxK : x ∈ CxK x K := by
    refine Subgroup.mem_inf.2 ⟨hxC, hN, TwoThin.mem_normalizer_pPrimeCoreOf hN, fun k hk => ?_⟩
    have : ⁅k, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_singleton_iff.mp (hKC hk))
    rw [this]
    exact one_mem _
  rw [hs.Q_eq]
  exact Subgroup.mem_inf.2 ⟨hxP, hxCxK⟩

theorem exists_cover {u : G} {K K' : Subgroup G} (hlt : PumpUpLT 2 x K u K')
    (hxK' : x ∈ normalizer (K' : Set G)) (hle : TwoThin.hatCard K' ≤ TwoThin.hatCard K) :
    ∃ Λ : Subgroup G, IsLam x u K Λ ∧ Λ ≤ K' ∧
      ∀ k ∈ K', ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K', k = l * o := by
  obtain ⟨Λ, hΛ, hK'c, -, -, -, hcases⟩ :=
    PumpRigid.rigid_step hlt (TwoThin.mem_centralizer_symm hlt.2.2.1) hle
  have hEq : PumpCalc.bar u Λ = PumpCalc.bar u K' := (hcases.resolve_right (fun h => h.1 hxK')).2
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hΛ.le.trans inf_le_right
  have hΛK' : Λ ≤ K' := by
    have hperf : Group.IsPerfect ↥(Λ.subgroupOf (centralizer ({u} : Set G))) :=
      Subgroup.isPerfect_iff.mpr (lam_perfect_Y hΛ)
    have hM2 : TwoComponents.IsTwoComponent (K'.subgroupOf (centralizer ({u} : Set G))) :=
      (TwoThin.isPCompIn_two_iff.mp hK'c).2
    have hmap : (Λ.subgroupOf (centralizer ({u} : Set G))).map
        (TwoThin.barMk ↥(centralizer ({u} : Set G))) ≤
        (K'.subgroupOf (centralizer ({u} : Set G))).map
          (TwoThin.barMk ↥(centralizer ({u} : Set G))) := hEq.le
    intro a ha
    have haY : a ∈ centralizer ({u} : Set G) := hΛY ha
    have := PumpRigid.le_of_perfect_map_le hperf hM2 hmap
      (Subgroup.mem_subgroupOf.mpr ha : (⟨a, haY⟩ : ↥(centralizer ({u} : Set G))) ∈ _)
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨Λ, hΛ, hΛK', fun k hk => ?_⟩
  have hkY : k ∈ centralizer ({u} : Set G) := hK'c.1 hk
  have hmem : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨k, hkY⟩ ∈ PumpCalc.bar u Λ := by
    rw [hEq]
    exact ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  obtain ⟨m, hm, hmk⟩ := hmem
  have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
  refine ⟨m, hmΛ, (m : G)⁻¹ * k, ?_, by group⟩
  have hmK' : (m : G) ∈ K' := hΛK' hmΛ
  have h1 : (m : G)⁻¹ * k ∈ K' := mul_mem (inv_mem hmK') hk
  refine PumpRigid.mem_pPrimeCoreOf_of_barMk_eq_one' hK'c.1 h1 (hK'c.1 h1) ?_
  have : (⟨(m : G)⁻¹ * k, hK'c.1 h1⟩ : ↥(centralizer ({u} : Set G))) = m⁻¹ * ⟨k, hkY⟩ := rfl
  rw [this, map_mul, map_inv, hmk, inv_mul_cancel]

theorem mem_CxK_of_cover {u s : G} {K' Λ : Subgroup G}
    (hK'c : IsPCompIn 2 (centralizer ({u} : Set G)) K') (hΛK' : Λ ≤ K')
    (hcov : ∀ k ∈ K', ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K', k = l * o)
    (hsu : s ∈ centralizer ({u} : Set G)) (hsΛ : s ∈ normalizer (Λ : Set G))
    (hcomm : ∀ l ∈ Λ, ⁅l, s⁆ ∈ pPrimeCoreOf 2 Λ) : s ∈ CxK u K' := by
  have hsinv : ∀ p ∈ Λ, s⁻¹ * p * s ∈ Λ := fun p hp => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hsΛ) p).mp hp
    simpa using this
  have hK''c := isPCompIn_conj_of_mem_normalizer hK'c (Subgroup.le_normalizer hsu)
  have hkK'' : Λ ≤ K'.map (MulAut.conj s).toMonoidHom := fun p hp =>
    ⟨s⁻¹ * p * s, hΛK' (hsinv p hp), by simp [MulAut.conj_apply]; group⟩
  have hEq : K' = K'.map (MulAut.conj s).toMonoidHom :=
    eq_of_isPCompIn_of_cover hK'c hK''c hΛK' hkK'' hcov
  have hsK' : s ∈ normalizer (K' : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq.symm
  have hsO : s ∈ normalizer (pPrimeCoreOf 2 K' : Set G) := TwoThin.mem_normalizer_pPrimeCoreOf hsK'
  refine Subgroup.mem_inf.2 ⟨hsu, hsK', hsO, fun k hk => ?_⟩
  obtain ⟨p, hp, o, ho, rfl⟩ := hcov k hk
  have hpK' : p ∈ K' := hΛK' hp
  have h1 : ⁅p, s⁆ ∈ pPrimeCoreOf 2 K' := pPrimeCoreOf_le_of_cover hΛK' hcov (hcomm p hp)
  have h2 : ⁅o, s⁆ ∈ pPrimeCoreOf 2 K' := by
    have e : ⁅o, s⁆ = o * (s * o⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem ho ((Subgroup.mem_normalizer_iff.mp hsO _).mp (inv_mem ho))
  have e2 : ⁅p * o, s⁆ = p * ⁅o, s⁆ * p⁻¹ * ⁅p, s⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  exact mul_mem (TwoThin.pPrimeCoreOf_normalized K' hpK' h2) h1

end T1Sylow

open T1Sylow in
theorem Q_syl_M (hs : Stage2Setup G x K A M P Q) (_hKM : K ≤ M) (hQM : Q ≤ M) :
    IsSylowOf 2 Q (M ⊓ centralizerSection K (pPrimeCoreOf 2 K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := hs.pair.1.1.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hs.pair.1.1.1.2.2
  have hILo : IsILo 2 x K := hs.pair.1.1.1
  have hterm : IsTwoTerminal x K := hs.pair.1.2.2
  have hQsyl : IsSylowOf 2 Q (CxK x K) := hs.sylowQ
  have hxQ : x ∈ Q := x_mem_Q_aux hs
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hQC : Q ≤ M ⊓ centralizerSection K (pPrimeCoreOf 2 K) := fun q hq =>
    Subgroup.mem_inf.2 ⟨hQM hq, (Subgroup.mem_inf.1 (hQsyl.le hq)).2⟩
  obtain ⟨R, hRsyl, hQR⟩ := C3.Layer1.Iv251.exists_isSylowOf_ge hQC hQsyl.isPGroup
  suffices hRQ : R ≤ Q from by
    have : R = Q := le_antisymm hRQ hQR
    rw [← this]
    exact hRsyl
  have hRp : IsPGroup 2 ↥R := hRsyl.isPGroup
  have hRcomm : ∀ r ∈ R, ∀ k ∈ K, ⁅k, r⁆ ∈ pPrimeCoreOf 2 K := fun r hr k hk =>
    (Subgroup.mem_inf.1 (hRsyl.le hr)).2.2.2 k hk
  have hRx : ∀ c ∈ R, c ∈ centralizer ({x} : Set G) → c ∈ CxK x K := fun c hcR hcx =>
    Subgroup.mem_inf.2 ⟨hcx, (Subgroup.mem_inf.1 (hRsyl.le hcR)).2⟩
  have hCRQ : R ⊓ centralizer ({x} : Set G) = Q :=
    hQsyl.eq_of_le (le_inf hQR (hQsyl.le.trans inf_le_left)) (fun c hc => hRx c hc.1 hc.2)
      hRp.to_inf_left
  have hRne : R ≠ ⊥ := fun h => hx1 (by simpa [h] using hQR hxQ)
  obtain ⟨u, huR, hu2, huc⟩ := C3.Layer1.Iv251.exists_central_involution hRp le_rfl
    Subgroup.le_normalizer hRne
  have hux : u ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (huc x (hQR hxQ))
  have huQ : u ∈ Q := by
    rw [← hCRQ]
    exact ⟨huR, hux⟩
  have huQc : ∀ q ∈ Q, u * q = q * u := fun q hq => huc q (hQR hq)
  have hucs : u ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    (Subgroup.mem_inf.1 (hQsyl.le huQ)).2
  have hR3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := by
    have h3 : 3 ≤ pRank 2 G := by
      rw [pRank_two_eq_twoRank]
      exact hs.hyp.rank
    exact fun y hy => TwoThin.rankThreeCentralizers G hs.hyp.simple hs.hyp.nonab h3 y hy
  obtain ⟨K_u, hltu⟩ := C3.Layer1.PumpRigid.exists_pumpUpLT hILo hu2 (hQsyl.le huQ) (hR3 u hu2)
  obtain ⟨hxKu, ⟨e⟩⟩ := hterm.2.1 u K_u hltu
  have hQu : IsSylowOf 2 Q (CxK u K_u) := hterm.2.2 Q hQsyl u K_u hltu huQ huQc
  have hKuc : IsPCompIn 2 (centralizer ({u} : Set G)) K_u := hltu.2.1.2.2
  have hle : TwoThin.hatCard K_u ≤ TwoThin.hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, hΛK', hcov⟩ := exists_cover hltu hxKu hle
  have hΛK : Λ ≤ K := fun l hl => (hΛ.le hl).1
  have hRle : R ≤ CxK u K_u := fun r hr => by
    have hru : r ∈ centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (huc r hr).symm
    have hrΛ : r ∈ normalizer (Λ : Set G) :=
      C3.Layer1.PumpRigid.mem_normalizer_lam hΛ hru (Subgroup.mem_inf.1 (hRsyl.le hr)).2.1
    refine mem_CxK_of_cover hKuc hΛK' hcov hru hrΛ fun l hl => ?_
    have hcΛ : ⁅l, r⁆ ∈ Λ := by
      have e : ⁅l, r⁆ = l * (r * l⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hl ((Subgroup.mem_normalizer_iff.mp hrΛ _).mp (inv_mem hl))
    exact C3.Layer1.Iv251.inf_pPrimeCoreOf_le hΛK ⟨hcΛ, hRcomm r hr l (hΛK hl)⟩
  exact (hQu.eq_of_le hQR hRle hRp).le

theorem exists_isMinSubnormalIn (hKM : K ≤ M) : ∃ H : Subgroup G, IsMinSubnormalIn K M H := by
  let s : Set (Subgroup G) := {J | K ≤ J ∧ GLS.IsSubnormalIn J M}
  have hne : s.Nonempty := by
    refine ⟨M, hKM, le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top.isSubnormal
  obtain ⟨L, hLs, hmin⟩ := Set.exists_min_image s (fun J => Nat.card J) (Set.toFinite s) hne
  exact ⟨L, hLs.1, hLs.2, fun J hKJ hJL hJs =>
    Subgroup.eq_of_le_of_card_ge hJL (hmin J ⟨hKJ, hJs⟩)⟩

end CFSG.GH74.Generic.BProg.B2
