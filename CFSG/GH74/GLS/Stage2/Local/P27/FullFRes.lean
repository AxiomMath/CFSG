module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFOut
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFC1
import CFSG.GH74.GLS.Stage1.Main.P49HBase

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Action

variable {X : Type} [Group X]

@[expose] noncomputable def actHom (K : Subgroup X) [K.Normal] :
    X →* MulAut (↥K ⧸ pPrimeCore 2 ↥K) where
  toFun c := QuotientGroup.congr (pPrimeCore 2 ↥K) (pPrimeCore 2 ↥K) (MulAut.conjNormal (H := K) c)
    (pPrimeCore_map_iso 2 (MulAut.conjNormal (H := K) c))
  map_one' := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H y => simp
  map_mul' a b := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H y =>
      show (QuotientGroup.mk (MulAut.conjNormal (H := K) (a * b) y) : ↥K ⧸ pPrimeCore 2 ↥K) =
        QuotientGroup.mk (MulAut.conjNormal (H := K) a (MulAut.conjNormal (H := K) b y))
      rw [map_mul]; rfl

theorem actHom_mk (K : Subgroup X) [K.Normal] (c : X) (y : ↥K) :
    actHom K c (QuotientGroup.mk y : ↥K ⧸ pPrimeCore 2 ↥K) =
      QuotientGroup.mk (MulAut.conjNormal (H := K) c y) := rfl

theorem commutator_mem_sup_ker (K : Subgroup X) [K.Normal]
    (hOut : OutAbel (↥K ⧸ pPrimeCore 2 ↥K)) (a b : X) :
    ⁅a, b⁆ ∈ K ⊔ (actHom K).ker := by
  obtain ⟨j, hj⟩ := hOut (actHom K a) (actHom K b)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective j
  have h1 : actHom K ⁅a, b⁆ = actHom K (y : X) := by
    have e : actHom K ⁅a, b⁆ = actHom K a * actHom K b * (actHom K a)⁻¹ * (actHom K b)⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv]
    rw [e, hj]
    ext z
    induction z using QuotientGroup.induction_on with
    | H w =>
      show (QuotientGroup.mk y * QuotientGroup.mk w * (QuotientGroup.mk y)⁻¹ :
          ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk (MulAut.conjNormal (H := K) (y : X) w)
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
  have h2 : ⁅a, b⁆ * (y : X)⁻¹ ∈ (actHom K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  have e : ⁅a, b⁆ = (⁅a, b⁆ * (y : X)⁻¹) * (y : X) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup h2 y.2

end Action

section Jx

variable {G : Type} [Group G] [Finite G]

instance Jx_subgroupOf_normal (x : G) : ((Jx x).subgroupOf (centralizer ({x} : Set G))).Normal :=
  ⟨fun k hk n => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact P34.Jx_normalized x n n.2 k hk⟩

theorem ker_actHom_le_CxK (x : G) :
    (actHom ((Jx x).subgroupOf (centralizer ({x} : Set G)))).ker.map
      (centralizer ({x} : Set G)).subtype ≤ CxK x (Jx x) := by
  have hn := Jx_subgroupOf_normal x
  rintro _ ⟨c, hc, rfl⟩
  have hJc : ((c : ↥(centralizer ({x} : Set G))) : G) ∈ normalizer ((Jx x : Subgroup G) : Set G) :=
    S45.mem_normalizer_Jx c.2
  refine ⟨c.2, hJc, TwoThin.mem_normalizer_pPrimeCoreOf hJc, fun k hk => ?_⟩
  have hkC : k ∈ centralizer ({x} : Set G) := P34.Jx_le_centralizer x hk
  set K : Subgroup ↥(centralizer ({x} : Set G)) :=
    (Jx x).subgroupOf (centralizer ({x} : Set G)) with hK
  let y : ↥K := ⟨⟨k, hkC⟩, Subgroup.mem_subgroupOf.2 hk⟩
  have h1 : actHom K c (QuotientGroup.mk y : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk y := by
    have := MonoidHom.mem_ker.1 hc
    rw [this]; rfl
  rw [actHom_mk] at h1
  have h2 : y / (MulAut.conjNormal (H := K) c y) ∈ pPrimeCore 2 ↥K :=
    (QuotientGroup.eq_iff_div_mem).1 h1.symm
  let ι : ↥K ≃* ↥(Jx x) :=
    Subgroup.subgroupOfEquivOfLe (P34.Jx_le_centralizer x : Jx x ≤ centralizer ({x} : Set G))
  have h3 : ι (y / (MulAut.conjNormal (H := K) c y)) ∈ pPrimeCore 2 ↥(Jx x) := by
    rw [← pPrimeCore_map_iso 2 ι]
    exact Subgroup.mem_map_of_mem _ h2
  refine Subgroup.mem_map.2 ⟨_, h3, ?_⟩
  have e1 : ((ι y : ↥(Jx x)) : G) = k := rfl
  have e2 : ((ι (MulAut.conjNormal (H := K) c y) : ↥(Jx x)) : G) = (c : G) * k * (c : G)⁻¹ := rfl
  show ((ι (y / MulAut.conjNormal (H := K) c y) : ↥(Jx x)) : G) = ⁅k, (c : G)⁆
  rw [map_div, Subgroup.coe_div, e1, e2, commutatorElement_def, div_eq_mul_inv]
  group

theorem commutator_mem_J_sup_CxK {x : G} (hOut : OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)))
    {a b : G} (ha : a ∈ centralizer ({x} : Set G)) (hb : b ∈ centralizer ({x} : Set G)) :
    ⁅a, b⁆ ∈ Jx x ⊔ CxK x (Jx x) := by
  have hn := Jx_subgroupOf_normal x
  set K : Subgroup ↥(centralizer ({x} : Set G)) :=
    (Jx x).subgroupOf (centralizer ({x} : Set G)) with hK
  let ι : ↥K ≃* ↥(Jx x) :=
    Subgroup.subgroupOfEquivOfLe (P34.Jx_le_centralizer x : Jx x ≤ centralizer ({x} : Set G))
  have hOut' : OutAbel (↥K ⧸ pPrimeCore 2 ↥K) :=
    OutAbel.of_mulEquiv (QuotientGroup.congr (pPrimeCore 2 ↥K) (pPrimeCore 2 ↥(Jx x)) ι
      (pPrimeCore_map_iso 2 ι)).symm hOut
  have h := commutator_mem_sup_ker K hOut' ⟨a, ha⟩ ⟨b, hb⟩
  have h2 : (⁅a, b⁆ : G) ∈ (K ⊔ (actHom K).ker).map (centralizer ({x} : Set G)).subtype :=
    ⟨_, h, rfl⟩
  have e : K.map (centralizer ({x} : Set G)).subtype = Jx x :=
    Subgroup.map_subgroupOf_eq_of_le (P34.Jx_le_centralizer x : Jx x ≤ centralizer ({x} : Set G))
  rw [Subgroup.map_sup, e] at h2
  exact (sup_le_sup_left (ker_actHom_le_CxK x) _) h2

end Jx

section Residual

variable {G : Type} [Group G] [Finite G]

theorem le_oPrimeResidualOf_of_perfect {X P : Subgroup G} (hPX : P ≤ X) (hP : ⁅P, P⁆ = P) :
    P ≤ oPrimeResidualOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : (oPrimeResidual 2 ↥X).Normal :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H.oPrimeResidual_two_normal ↥X
  set M : Subgroup ↥(P.subgroupOf X) := (oPrimeResidual 2 ↥X).subgroupOf (P.subgroupOf X) with hM
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hPperf' : Group.IsPerfect ↥(P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have hMn : M.Normal := Subgroup.Normal.subgroupOf hRn _
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(P.subgroupOf X)) := inferInstance
  have hSM : (S : Subgroup ↥(P.subgroupOf X)) ≤ M := by
    intro x hx
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    have := congrArg (fun z : ↥S => (((z : ↥(P.subgroupOf X)) : ↥X))) hk
    simpa using this
  have hodd : Odd M.index := by
    have h1 : M.index ∣ (S : Subgroup ↥(P.subgroupOf X)).index := Subgroup.index_dvd_of_le hSM
    have h2 : ¬ 2 ∣ (S : Subgroup ↥(P.subgroupOf X)).index := S.not_dvd_index
    exact Odd.of_dvd_nat (Nat.odd_iff.2 (by omega)) h1
  have : Group.IsPerfect (↥(P.subgroupOf X) ⧸ M) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective M)
  have : Group.IsSolvable (↥(P.subgroupOf X) ⧸ M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (↥(P.subgroupOf X) ⧸ M) := by
    by_contra hns
    have : Nontrivial (↥(P.subgroupOf X) ⧸ M) := not_subsingleton_iff_nontrivial.1 hns
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥(P.subgroupOf X) ⧸ M)
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  have hMtop : M = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have : Nat.card (↥(P.subgroupOf X) ⧸ M) = 1 := Nat.card_unique
    exact this
  intro p hp
  have hpX : p ∈ X := hPX hp
  have : (⟨⟨p, hpX⟩, Subgroup.mem_subgroupOf.2 hp⟩ : ↥(P.subgroupOf X)) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact ⟨⟨p, hpX⟩, this, rfl⟩

omit [Finite G] in
theorem le_oPrimeResidualOf_of_isPGroup' {X T : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup 2 ↥T) :
    T ≤ oPrimeResidualOf 2 X := by
  intro t ht
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine ⟨⟨t, hTX ht⟩, Subgroup.subset_closure ⟨k, ?_⟩, rfl⟩
  apply Subtype.ext
  have := congrArg (fun u : ↥T => (u : G)) hk
  simpa using this

theorem fullF_res {x : G} {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hOut : OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))) (hE : HasNormal2Compl (CxK x (Jx x))) :
    oPrimeResidualOf 2 (centralizer ({x} : Set G)) ⊔ pPrimeCoreOf 2 (centralizer ({x} : Set G)) =
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := by
  apply le_antisymm
  · refine sup_le ?_ (le_sup_left.trans le_sup_left)
    rw [oPrimeResidualOf]
    refine Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le _).2 ?_)
    rintro c ⟨k, hk⟩
    have hck : ((c : G)) ^ (2 ^ k) = 1 := by
      have := congrArg (fun u : ↥(centralizer ({x} : Set G)) => (u : G)) hk
      simpa using this
    have hz : IsPGroup 2 ↥(zpowers (c : G)) :=
      IsPGroup.of_card_dvd_pow (n := k) (by
        rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hck)
    obtain ⟨k₀, hk₀, hconj⟩ := exists_conj_le_of_isSylowOf hT (R := zpowers (c : G))
      ((Subgroup.zpowers_le).2 c.2) hz
    set t : G := k₀⁻¹ * (c : G) * k₀ with ht
    have htT : t ∈ T := hconj (c : G) (Subgroup.mem_zpowers _)
    have hcom : ⁅k₀, t⁆ ∈ Jx x ⊔ CxK x (Jx x) :=
      commutator_mem_J_sup_CxK hOut hk₀ (hT.le htT)
    have hle : Jx x ⊔ (pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ T) ≤
        pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T :=
      sup_le (le_sup_right.trans le_sup_left)
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    have hcom' : ⁅k₀, t⁆ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T :=
      hle ((sup_le_sup_left (cxK_le_sup hT hE) (Jx x)) hcom)
    have hTle : T ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T := le_sup_right
    have hceq : (c : G) = ⁅k₀, t⁆ * t := by
      rw [commutatorElement_def, ht]; group
    show (c : G) ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ Jx x ⊔ T
    rw [hceq]
    exact Subgroup.mul_mem _ hcom' (hTle htT)
  · refine sup_le (sup_le le_sup_right ?_) ?_
    · exact le_sup_of_le_left (le_oPrimeResidualOf_of_perfect (P34.Jx_le_centralizer x)
        (pLayerOf_two_perfect_P27 _))
    · exact le_sup_of_le_left (le_oPrimeResidualOf_of_isPGroup' hT.le hT.isPGroup)

end Residual

end CFSG.GH74.GLS.Stage2.Local.P27
