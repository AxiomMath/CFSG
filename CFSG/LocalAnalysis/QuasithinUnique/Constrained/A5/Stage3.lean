module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3Rho
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
open scoped MatrixGroups

local instance glMulAction : MulAction (GL (Fin 4) (ZMod 2)) V4 where
  smul g v := (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v
  one_smul v := by
    show ((1 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = v
    rw [Units.val_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show ((g * h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v =
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        ((h : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem t1_mem_M1 (C : StdCfg T M H S L) : ((C.iV w04w : ↥H) : G) ∈ T ⊔ borelK M L :=
  Subgroup.mem_sup_left (C.hcs.le_T (C.iV_mem_S w04w))

theorem exists_iV_of_mem_U (C : StdCfg T M H S L) {y : G} (hy : y ∈ blockU L) :
    ∃ w : evenWeight 5, y = ((C.iV w : ↥H) : G) := by
  refine ⟨Multiplicative.toAdd (C.D.β ⟨y, hy⟩), ?_⟩
  rw [C.iV_coe, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem U_comm (C : StdCfg T M H S L) {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L) :
    a * b = b * a := by
  obtain ⟨w₁, rfl⟩ := C.exists_iV_of_mem_U ha
  obtain ⟨w₂, rfl⟩ := C.exists_iV_of_mem_U hb
  exact congrArg Subtype.val (C.iV_comm w₁ w₂)

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem exists_E8_not_conj {x : G} (hxT : x ∈ T) (hxS : x ∉ S) :
    ∃ e : evenWeight 5, e.1 4 = 0 ∧ x * ((C.iV e : ↥H) : G) * x⁻¹ ∉ blockU L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, huH, huUx, hπu⟩ := C.exists_Ux_swap hxT hxS
  have hu0 : x * u * x⁻¹ ∈ blockU L :=
    (mem_conjSubgroup_iff (A := blockU L) (g := x) (x := u)).mp huUx
  have hcomm : ∀ e : evenWeight 5, e.1 4 = 0 →
      (⟨u, huH⟩ : ↥H) * C.iV e = C.iV e * ⟨u, huH⟩ := by
    intro e he
    have h1 := C.U_comm hu0 (hcon e he)
    apply Subtype.ext
    show u * ((C.iV e : ↥H) : G) = ((C.iV e : ↥H) : G) * u
    calc u * ((C.iV e : ↥H) : G)
        = x⁻¹ * ((x * u * x⁻¹) * (x * ((C.iV e : ↥H) : G) * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * ((C.iV e : ↥H) : G) * x⁻¹) * (x * u * x⁻¹)) * x := by rw [h1]
      _ = ((C.iV e : ↥H) : G) * u := by group
  let e0 : evenWeight 5 := ⟨![1, 0, 1, 0, 0], e02_even⟩
  have hfix := X.vact_fixed_of_comm ⟨u, huH⟩ e0 (hcomm e0 e02_four)
  rw [hπu] at hfix
  exact swap_moves_e02 (congrArg Subtype.val hfix)

theorem mem_S_of_trivial_action {t : G} (ht : t ∈ T)
    (hct : ∀ p ∈ borelP M L, t * p * t⁻¹ * p⁻¹ ∈ centerOf (borelP M L)) : t ∈ S := by
  by_contra hS
  obtain ⟨e, he4, hne⟩ := X.exists_E8_not_conj ht hS
  apply hne
  have hP : ((C.iV e : ↥H) : G) ∈ borelP M L := X.iV_mem_P he4
  have hz := hct _ hP
  have hzU : t * ((C.iV e : ↥H) : G) * t⁻¹ * ((C.iV e : ↥H) : G)⁻¹ ∈ blockU L := by
    rcases (X.centerOf_P_iff _).mp hz with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact C.zU_mem
  have hιU : ((C.iV e : ↥H) : G) ∈ blockU L := C.iV_mem_U e
  have hdecomp : t * ((C.iV e : ↥H) : G) * t⁻¹ =
      (t * ((C.iV e : ↥H) : G) * t⁻¹ * ((C.iV e : ↥H) : G)⁻¹) * ((C.iV e : ↥H) : G) := by group
  rw [hdecomp]
  exact mul_mem hzU hιU

@[expose] noncomputable def rawP (p : ↥(borelP M L)) : RP :=
  X.raw ⟨(p : G), C.hcs.sylow.le (X.P_le_S p.2)⟩

theorem rawP_mul (p q : ↥(borelP M L)) : X.rawP (p * q) = rmul (X.rawP p) (X.rawP q) :=
  X.raw_mul ⟨(p : G), C.hcs.sylow.le (X.P_le_S p.2)⟩ ⟨(q : G), C.hcs.sylow.le (X.P_le_S q.2)⟩

theorem raw_one' : X.raw 1 = rone := by
  rw [← X.emb_zero_one]
  exact X.raw_emb 0 1

theorem rawP_one : X.rawP 1 = rone := X.raw_one'

theorem rawP_inPraw (p : ↥(borelP M L)) : inPraw (X.rawP p) :=
  (X.raw_P_iff ⟨(p : G), C.hcs.sylow.le (X.P_le_S p.2)⟩).mp p.2

theorem rawP_inj {p q : ↥(borelP M L)} (h : X.rawP p = X.rawP q) : p = q :=
  Subtype.ext (congrArg (fun y : ↥H => (y : G)) (X.raw_inj h))

theorem zU_mem_P : C.zU ∈ borelP M L :=
  (Subgroup.mem_inf.mp ((X.centerOf_P_iff _).mpr (Or.inr rfl))).1

theorem rawP_zU : X.rawP ⟨C.zU, X.zU_mem_P⟩ = zraw := by
  have h : X.rawP ⟨C.zU, X.zU_mem_P⟩ = X.raw (C.iV StdCfg.z0V) := rfl
  rw [h, X.raw_iV]
  try rfl

@[expose] noncomputable def thG
    : ↥(borelP M L) →* Multiplicative V4 where
  toFun p := Multiplicative.ofAdd (thRaw (X.rawP p))
  map_one' := by
    show Multiplicative.ofAdd (thRaw (X.rawP 1)) = 1
    rw [X.rawP_one, thRaw_rone, ofAdd_zero]
  map_mul' p q := by
    show Multiplicative.ofAdd (thRaw (X.rawP (p * q))) =
      Multiplicative.ofAdd (thRaw (X.rawP p)) * Multiplicative.ofAdd (thRaw (X.rawP q))
    rw [X.rawP_mul, thRaw_mul' (X.rawP_inPraw p) (X.rawP_inPraw q), ofAdd_add]

theorem thG_ker
    : (X.thG).ker = (centerOf (borelP M L)).subgroupOf (borelP M L) := by
  ext p
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, X.centerOf_P_iff]
  constructor
  · intro h
    have h0 : thRaw (X.rawP p) = 0 := by
      have := congrArg Multiplicative.toAdd h
      exact this
    rcases thRaw_ker' (X.rawP_inPraw p) h0 with h1 | h1
    · left
      have : p = 1 := X.rawP_inj (h1.trans X.rawP_one.symm)
      simp [this]
    · right
      have : p = ⟨C.zU, X.zU_mem_P⟩ := X.rawP_inj (h1.trans X.rawP_zU.symm)
      rw [this]
  · rintro (h | h)
    · have : p = 1 := Subtype.ext h
      rw [this]
      exact map_one _
    · have : p = ⟨C.zU, X.zU_mem_P⟩ := Subtype.ext h
      rw [this]
      show Multiplicative.ofAdd (thRaw (X.rawP ⟨C.zU, X.zU_mem_P⟩)) = 1
      rw [X.rawP_zU, thRaw_zraw, ofAdd_zero]

theorem thG_surj : Function.Surjective X.thG := by
  intro v
  obtain ⟨hr, hv⟩ := thRaw_pre' (Multiplicative.toAdd v)
  have hmem : ((X.emb ⟨(preraw (Multiplicative.toAdd v)).1, hr.1.1⟩
      (preraw (Multiplicative.toAdd v)).2 : ↥H) : G) ∈ borelP M L :=
    (X.raw_P_iff _).mpr (by rw [X.raw_emb]; exact hr)
  refine ⟨⟨_, hmem⟩, ?_⟩
  have h1 : X.rawP ⟨_, hmem⟩ = preraw (Multiplicative.toAdd v) :=
    X.raw_emb ⟨(preraw (Multiplicative.toAdd v)).1, hr.1.1⟩ (preraw (Multiplicative.toAdd v)).2
  show Multiplicative.ofAdd (thRaw (X.rawP ⟨_, hmem⟩)) = v
  rw [h1, hv, ofAdd_toAdd]

theorem sq_cases (p : ↥(borelP M L)) :
    (((p : G) * p = 1) ∧ quadHyp (Multiplicative.toAdd (X.thG p)) = 0) ∨
    (((p : G) * p = C.zU) ∧ quadHyp (Multiplicative.toAdd (X.thG p)) = 1) := by
  have hmul : X.rawP (p * p) = rmul (X.rawP p) (X.rawP p) := X.rawP_mul p p
  rcases thRaw_q' (X.rawP_inPraw p) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨?_, h1⟩
    have : p * p = 1 := X.rawP_inj (by rw [hmul, h2, X.rawP_one])
    exact congrArg Subtype.val this
  · right
    refine ⟨?_, h1⟩
    have : p * p = ⟨C.zU, X.zU_mem_P⟩ := X.rawP_inj (by rw [hmul, h2, X.rawP_zU])
    exact congrArg Subtype.val this

theorem mem_U_of_W0
    {q : ↥(borelP M L)} (h : inW0 (Multiplicative.toAdd (X.thG q))) :
    (q : G) ∈ blockU L := by
  have h1 : (X.rawP q).2 = 1 := thRaw_W0' (X.rawP_inPraw q) h
  have h2 : C.D.π ⟨(q : G), C.hcs.sylow.le (X.P_le_S q.2)⟩ = 1 := h1
  rw [← C.Q_eq_U X.hTC]
  exact (C.hker _).mp h2

theorem mem_U_of_thG_one
    {q : ↥(borelP M L)} (h : X.thG q = 1) : (q : G) ∈ blockU L := by
  have h1 : q ∈ (X.thG).ker := h
  rw [X.thG_ker] at h1
  rcases (X.centerOf_P_iff (q : G)).mp h1 with h2 | h2
  · rw [h2]
    exact one_mem _
  · rw [h2]
    exact C.zU_mem

theorem M1_normalizes {m : G} (hm : m ∈ T ⊔ borelK M L) {p : G} (hp : p ∈ borelP M L) :
    m * p * m⁻¹ ∈ borelP M L :=
  (Subgroup.mem_normalizer_iff.mp (sup_le X.T_normalizes_P X.K_normalizes_P hm) p).mp hp

theorem exists_rho_M1
    : ∃ ρ : ↥(T ⊔ borelK M L) →* GL (Fin 4) (ZMod 2),
    ∀ (m : ↥(T ⊔ borelK M L)) (x y : ↥(borelP M L)), (y : G) = m * x * m⁻¹ →
      Multiplicative.toAdd (X.thG y) =
        (ρ m : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (X.thG x)) :=
  exists_rho X.thG X.thG_surj X.thG_ker (fun m hm p hp => X.M1_normalizes hm hp)
    (fun m hm z hz => by
      have hc : z * m = m * z := Subgroup.mem_centralizer_iff.mp (X.M1_cent hm) z hz
      have : m * z * m⁻¹ = z := by
        calc m * z * m⁻¹ = z * m * m⁻¹ := by rw [hc]
          _ = z := by group
      rw [this]
      exact hz)

@[expose] noncomputable def rho
    : ↥(T ⊔ borelK M L) →* GL (Fin 4) (ZMod 2) :=
  Classical.choose X.exists_rho_M1

theorem rho_spec
    : ∀ (m : ↥(T ⊔ borelK M L)) (x y : ↥(borelP M L)), (y : G) = m * x * m⁻¹ →
    Multiplicative.toAdd (X.thG y) =
      ((X.rho m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        (Multiplicative.toAdd (X.thG x)) :=
  Classical.choose_spec X.exists_rho_M1

noncomputable abbrev rhoM
    (m : ↥(T ⊔ borelK M L)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ((X.rho m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))

theorem rhoM_mul
    (m m' : ↥(T ⊔ borelK M L)) : X.rhoM (m * m') = X.rhoM m * X.rhoM m' := by
  simp [rhoM, map_mul]

theorem rhoM_one : X.rhoM 1 = 1 := by simp [rhoM]

theorem rhoM_inv_mul
    (m : ↥(T ⊔ borelK M L)) : X.rhoM m⁻¹ * X.rhoM m = 1 := by
  rw [← X.rhoM_mul, inv_mul_cancel, X.rhoM_one]

theorem rhoM_spec
    (m : ↥(T ⊔ borelK M L)) (x y : ↥(borelP M L)) (h : (y : G) = m * x * m⁻¹) :
    Multiplicative.toAdd (X.thG y) = (X.rhoM m).mulVec (Multiplicative.toAdd (X.thG x)) :=
  X.rho_spec m x y h

theorem M1_cent_zU {m : G} (hm : m ∈ T ⊔ borelK M L) : m * C.zU * m⁻¹ = C.zU := by
  have hc : C.zU * m = m * C.zU :=
    Subgroup.mem_centralizer_iff.mp (X.M1_cent hm) C.zU ((X.centerOf_P_iff _).mpr (Or.inr rfl))
  calc m * C.zU * m⁻¹ = C.zU * m * m⁻¹ := by rw [hc]
    _ = C.zU := by group

theorem rhoM_quad (m : ↥(T ⊔ borelK M L)) (v : V4) :
    quadHyp ((X.rhoM m).mulVec v) = quadHyp v := by
  obtain ⟨p, hp⟩ := X.thG_surj (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (X.thG p) := by rw [hp]; rfl
  let y : ↥(borelP M L) := ⟨(m : G) * p * (m : G)⁻¹, X.M1_normalizes m.2 p.2⟩
  have h1 := X.rhoM_spec m p y rfl
  rw [hv, ← h1]
  have hyy : (y : G) * y = (m : G) * ((p : G) * p) * (m : G)⁻¹ := by
    show (m : G) * p * (m : G)⁻¹ * ((m : G) * p * (m : G)⁻¹) = _
    group
  rcases X.sq_cases p with ⟨hp1, hq1⟩ | ⟨hp1, hq1⟩ <;>
    rcases X.sq_cases y with ⟨hy1, hq2⟩ | ⟨hy1, hq2⟩
  · rw [hq1, hq2]
  · exfalso
    apply C.zU_ne_one
    calc C.zU = (y : G) * y := hy1.symm
      _ = (m : G) * ((p : G) * p) * (m : G)⁻¹ := hyy
      _ = 1 := by rw [hp1]; group
  · exfalso
    apply C.zU_ne_one
    calc C.zU = (m : G) * C.zU * (m : G)⁻¹ := (X.M1_cent_zU m.2).symm
      _ = (m : G) * ((p : G) * p) * (m : G)⁻¹ := by rw [hp1]
      _ = (y : G) * y := hyy.symm
      _ = 1 := hy1
  · rw [hq1, hq2]

theorem rho_range_le : X.rho.range ≤ O4PlusTwo := by
  rintro _ ⟨m, rfl⟩
  intro v
  exact X.rhoM_quad m v

theorem rho_eq
    (m : ↥(T ⊔ borelK M L)) (h : ↥H) (hmh : (h : G) = (m : G))
    (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (g g' : RP)
    (hg : X.raw h = g) (hg' : X.raw h⁻¹ = g')
    (hA : ∀ r : RP, inPraw r → A.mulVec (thRaw r) = thRaw (rmul (rmul g r) g')) :
    X.rhoM m = A := by
  have key : ∀ v : V4, (X.rhoM m).mulVec v = A.mulVec v := by
    intro v
    obtain ⟨p, hp⟩ := X.thG_surj (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (X.thG p) := by rw [hp]; rfl
    let y : ↥(borelP M L) := ⟨(m : G) * p * (m : G)⁻¹, X.M1_normalizes m.2 p.2⟩
    have h1 := X.rhoM_spec m p y rfl
    rw [hv, ← h1]
    show thRaw (X.rawP y) = A.mulVec (thRaw (X.rawP p))
    rw [hA _ (X.rawP_inPraw p)]
    congr 1
    have hy : X.rawP y = X.raw (h * ⟨(p : G), C.hcs.sylow.le (X.P_le_S p.2)⟩ * h⁻¹) := by
      unfold rawP
      congr 1
      apply Subtype.ext
      show (m : G) * p * (m : G)⁻¹ = (h : G) * p * (h : G)⁻¹
      rw [hmh]
    rw [hy, X.raw_mul, X.raw_mul, hg, hg']
    try rfl
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem s01_mem_M1 : ((X.s sa : ↥H) : G) ∈ T ⊔ borelK M L :=
  Subgroup.mem_sup_left (C.hcs.le_T (X.s_mem_S sa_mem))

theorem c3_mem_K : ((X.s c3 : ↥H) : G) ∈ borelK M L :=
  X.s_mem_K ((mem_A4std _).mpr ((mem_A4set _).mpr
    ⟨c3_four, Equiv.Perm.mem_alternatingGroup.mp c3_mem_alt⟩))

theorem c3_mem_M1 : ((X.s c3 : ↥H) : G) ∈ T ⊔ borelK M L := Subgroup.mem_sup_right X.c3_mem_K

theorem rho_t1
    : X.rhoM ⟨((C.iV w04w : ↥H) : G), C.t1_mem_M1⟩ = Mt1 := by
  have hinv : (C.iV w04w)⁻¹ = C.iV w04w := inv_eq_of_mul_eq_one_right (C.iV_self w04w)
  refine X.rho_eq _ (C.iV w04w) rfl Mt1 gt1 gt1 (X.raw_iV w04w) ?_ (fun r hr => Mt1_act' hr)
  rw [hinv]
  exact X.raw_iV w04w

theorem rho_s01
    : X.rhoM ⟨((X.s sa : ↥H) : G), X.s01_mem_M1⟩ = Ms01 := by
  have hinv : (X.s sa)⁻¹ = X.s sa := by
    rw [← map_inv]
    exact congrArg X.s (Equiv.swap_inv (0 : Fin 5) 1)
  refine X.rho_eq _ (X.s sa) rfl Ms01 gs01 gs01 (X.raw_s sa) ?_ (fun r hr => Ms01_act' hr)
  rw [hinv]
  exact X.raw_s sa

theorem rho_k : X.rhoM ⟨((X.s c3 : ↥H) : G), X.c3_mem_M1⟩ = Mk := by
  have hinv : (X.s c3)⁻¹ = X.s (c3 * c3) := by
    rw [← map_inv, c3_inv]
  refine X.rho_eq _ (X.s c3) rfl Mk gk gkinv (X.raw_s c3) ?_ (fun r hr => Mk_act' hr)
  rw [hinv]
  exact X.raw_s (c3 * c3)

theorem trans_sing (s s' : V4) (hs : inSing s) (hs' : inSing s') :
    ∃ m : ↥(T ⊔ borelK M L), (X.rhoM m).mulVec s = s' := by
  classical
  let R : V4 → V4 → Prop := fun a b => ∃ m : ↥(T ⊔ borelK M L), (X.rhoM m).mulVec a = b
  have Rrefl : ∀ a, R a a := fun a => ⟨1, by rw [X.rhoM_one, Matrix.one_mulVec]⟩
  have Rtrans : ∀ a b c, R a b → R b c → R a c := by
    rintro a b c ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m' * m, by rw [X.rhoM_mul, Matrix.mulVec_mulVec]⟩
  have Rsymm : ∀ a b, R a b → R b a := by
    rintro a b ⟨m, rfl⟩
    exact ⟨m⁻¹, by rw [Matrix.mulVec_mulVec, X.rhoM_inv_mul, Matrix.one_mulVec]⟩
  have Rt1 : ∀ a, R a (Mt1.mulVec a) := fun a => ⟨⟨_, C.t1_mem_M1⟩, by rw [X.rho_t1]⟩
  have Rs01 : ∀ a, R a (Ms01.mulVec a) := fun a => ⟨⟨_, X.s01_mem_M1⟩, by rw [X.rho_s01]⟩
  have Rk : ∀ a, R a (Mk.mulVec a) := fun a => ⟨⟨_, X.c3_mem_M1⟩, by rw [X.rho_k]⟩
  have Rgen : ∀ (i : Fin 3) a, R a (gact i a) := by
    intro i a
    fin_cases i
    · exact Rt1 a
    · exact Rs01 a
    · exact Rk a
  have Rword : ∀ (w : List (Fin 3)) a, R a (wact w a) := by
    intro w a
    induction w with
    | nil => exact Rrefl a
    | cons i w ih => exact Rtrans _ _ _ ih (Rgen i (wact w a))
  have h6 : ∀ a ∈ sing6, ∀ b ∈ sing6, R a b := by
    intro a ha b hb
    obtain ⟨w, -, hw⟩ := sing6_conn a ha b hb
    rw [← hw]
    exact Rword w a
  have hW0 : ∀ a b : V4, inW0 a → a ≠ 0 → inW0 b → b ≠ 0 → R a b := by
    intro a b ha ha0 hb hb0
    rcases Mk_trans_W0 a ha ha0 b hb hb0 with h | h | h
    · rw [h]
      exact Rrefl a
    · rw [h]
      exact Rk a
    · rw [h]
      exact Rtrans _ _ _ (Rk a) (Rk _)
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  obtain ⟨e, he4, hxe⟩ := X.exists_E8_not_conj hxT hxS
  have hxM : x ∈ T ⊔ borelK M L := Subgroup.mem_sup_left hxT
  let p : ↥(borelP M L) := ⟨((C.iV e : ↥H) : G), X.iV_mem_P he4⟩
  let y : ↥(borelP M L) := ⟨x * (p : G) * x⁻¹, X.M1_normalizes hxM p.2⟩
  have hyU : (y : G) ∉ blockU L := hxe
  let w : V4 := Multiplicative.toAdd (X.thG p)
  let w' : V4 := Multiplicative.toAdd (X.thG y)
  have hww' : (X.rhoM ⟨x, hxM⟩).mulVec w = w' := (X.rhoM_spec ⟨x, hxM⟩ p y rfl).symm
  have hwW0 : inW0 w := by
    have h1 : X.rawP p = (e.1, 1) := X.raw_iV e
    show thRaw (X.rawP p) 0 = 0 ∧ thRaw (X.rawP p) 2 = 0
    rw [h1]
    exact thRaw_one_W0 e.1
  have hw'0 : w' ≠ 0 := by
    intro h0
    apply hyU
    apply X.mem_U_of_thG_one
    exact h0
  have hw'W0 : ¬ inW0 w' := fun h => hyU (X.mem_U_of_W0 h)
  have hw0 : w ≠ 0 := by
    intro h0
    apply hw'0
    rw [← hww', h0, Matrix.mulVec_zero]
  have hwq : quadHyp w = 0 := (W0_sing w hwW0 hw0).1
  have hw'q : quadHyp w' = 0 := by
    rw [← hww', X.rhoM_quad]
    exact hwq
  have hw'6 : w' ∈ sing6 := by
    simp only [sing6, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hw'q, hw'0⟩, hw'W0⟩
  have hRww' : R w w' := ⟨⟨x, hxM⟩, hww'⟩
  have e1W0 : inW0 (![0, 1, 0, 0] : V4) := by decide +kernel
  have e1ne : (![0, 1, 0, 0] : V4) ≠ 0 := by decide +kernel
  have hto : ∀ a, inSing a → R a ![0, 1, 0, 0] := by
    intro a ha
    by_cases hW : inW0 a
    · exact hW0 a _ hW ha.2 e1W0 e1ne
    · have ha6 : a ∈ sing6 := by
        simp only [sing6, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ha, hW⟩
      exact Rtrans _ _ _ (h6 a ha6 w' hw'6) (Rtrans _ _ _ (Rsymm _ _ hRww')
        (hW0 w _ hwW0 hw0 e1W0 e1ne))
  exact Rtrans _ _ _ (hto s hs) (Rsymm _ _ (hto s' hs'))

theorem nine_dvd : 9 ∣ Nat.card X.rho.range := by
  let v0 : V4 := ![0, 1, 0, 0]
  have hv0 : inSing v0 := by decide +kernel
  have horb : MulAction.orbit ↥X.rho.range v0 = {v | inSing v} := by
    ext v
    constructor
    · rintro ⟨γ, rfl⟩
      obtain ⟨_, ⟨m, rfl⟩⟩ := γ
      refine ⟨?_, ?_⟩
      · show quadHyp ((X.rhoM m).mulVec v0) = 0
        rw [X.rhoM_quad]
        exact hv0.1
      · intro h0
        have h1 : (X.rhoM m⁻¹).mulVec ((X.rhoM m).mulVec v0) = v0 := by
          rw [Matrix.mulVec_mulVec, X.rhoM_inv_mul, Matrix.one_mulVec]
        have h2 : (X.rhoM m).mulVec v0 = 0 := h0
        rw [h2, Matrix.mulVec_zero] at h1
        exact hv0.2 h1.symm
    · intro hv
      obtain ⟨m, hm⟩ := X.trans_sing v0 v hv0 hv
      exact ⟨⟨X.rho m, m, rfl⟩, hm⟩
  have hncard : (MulAction.orbit ↥X.rho.range v0).ncard = 9 := by
    rw [horb]
    have : ({v | inSing v} : Set V4) = ↑(Finset.univ.filter fun v : V4 => inSing v) := by
      ext v
      simp
    rw [this, Set.ncard_coe_finset, nine_sing]
  rw [← hncard, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem eight_dvd : 8 ∣ Nat.card X.rho.range := by
  classical
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  have hSM : S ≤ T ⊔ borelK M L := C.hcs.le_T.trans le_sup_left
  have hTM : T ≤ T ⊔ borelK M L := le_sup_left
  let rS : Subgroup (GL (Fin 4) (ZMod 2)) := (X.rho.comp (Subgroup.inclusion hSM)).range
  let rT : Subgroup (GL (Fin 4) (ZMod 2)) := (X.rho.comp (Subgroup.inclusion hTM)).range
  have hrST : rS ≤ rT := by
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨s, C.hcs.le_T s.2⟩, rfl⟩
  have hrT : rT ≤ X.rho.range := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  have hxM : x ∈ T ⊔ borelK M L := hTM hxT
  have hx_rT : X.rho ⟨x, hxM⟩ ∈ rT := ⟨⟨x, hxT⟩, rfl⟩
  have hx_rS : X.rho ⟨x, hxM⟩ ∉ rS := by
    rintro ⟨s, hs⟩
    have hs' : X.rho ⟨(s : G), hSM s.2⟩ = X.rho ⟨x, hxM⟩ := hs
    have ht : (s : G)⁻¹ * x ∈ T := mul_mem (inv_mem (C.hcs.le_T s.2)) hxT
    have hρ1 : X.rho ⟨(s : G)⁻¹ * x, hTM ht⟩ = 1 := by
      have : (⟨(s : G)⁻¹ * x, hTM ht⟩ : ↥(T ⊔ borelK M L)) =
          ⟨(s : G), hSM s.2⟩⁻¹ * ⟨x, hxM⟩ := rfl
      rw [this, map_mul, map_inv, hs']
      exact inv_mul_cancel _
    have hS : (s : G)⁻¹ * x ∈ S := by
      apply X.mem_S_of_trivial_action ht
      intro p hp
      let p' : ↥(borelP M L) := ⟨p, hp⟩
      let y : ↥(borelP M L) := ⟨(s : G)⁻¹ * x * p * ((s : G)⁻¹ * x)⁻¹,
        X.M1_normalizes (hTM ht) hp⟩
      have h1 := X.rhoM_spec ⟨(s : G)⁻¹ * x, hTM ht⟩ p' y rfl
      have hM1 : X.rhoM ⟨(s : G)⁻¹ * x, hTM ht⟩ = 1 := by
        show ((X.rho ⟨(s : G)⁻¹ * x, hTM ht⟩ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1
        simp [hρ1]
      rw [hM1, Matrix.one_mulVec] at h1
      have h2 : X.thG (y * p'⁻¹) = 1 := by
        have hyp : X.thG y = X.thG p' := by
          have := congrArg Multiplicative.ofAdd h1
          simpa using this
        rw [map_mul, map_inv, hyp]
        exact mul_inv_cancel _
      have h3 : y * p'⁻¹ ∈ (X.thG).ker := h2
      rw [X.thG_ker] at h3
      exact h3
    exact hxS (by simpa using mul_mem s.2 hS)
  have hrS4 : 4 ≤ Nat.card rS := by
    let a : GL (Fin 4) (ZMod 2) := X.rho ⟨_, C.t1_mem_M1⟩
    let b : GL (Fin 4) (ZMod 2) := X.rho ⟨_, X.s01_mem_M1⟩
    have ha : a ∈ rS := ⟨⟨_, C.iV_mem_S w04w⟩, rfl⟩
    have hb : b ∈ rS := ⟨⟨_, X.s_mem_S sa_mem⟩, rfl⟩
    let u : Fin 4 → GL (Fin 4) (ZMod 2) := ![1, a, b, a * b]
    have hu_mem : ∀ i, u i ∈ rS := by
      intro i
      fin_cases i
      · exact one_mem _
      · exact ha
      · exact hb
      · exact mul_mem ha hb
    have hu_mat : ∀ i, ((u i : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        (![1, Mt1, Ms01, Mt1 * Ms01] : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2)) i := by
      intro i
      have hat : ((a : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Mt1 := X.rho_t1
      have hbt : ((b : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Ms01 := X.rho_s01
      fin_cases i
      · rfl
      · exact hat
      · exact hbt
      · show ((a * b : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = Mt1 * Ms01
        rw [Units.val_mul, hat, hbt]
    have hinj : Function.Injective (fun i => (⟨u i, hu_mem i⟩ : ↥rS)) := by
      intro i j hij
      have h1 := congrArg (fun z : ↥rS => ((z : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) hij
      simp only [hu_mat] at h1
      exact S4_inj i j h1
    calc 4 = Nat.card (Fin 4) := by simp
      _ ≤ Nat.card rS := Nat.card_le_card_of_injective _ hinj
  have hlt : Nat.card rS < Nat.card rT := by
    by_contra hge
    push Not at hge
    have : rS = rT := Subgroup.eq_of_le_of_card_ge hrST hge
    apply hx_rS
    rw [this]
    exact hx_rT
  have hpos : 0 < Nat.card rT := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hrST
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · omega
      · omega
    · exact h
  have h8 : 8 ≤ Nat.card rT := by
    rw [hk]
    calc 8 = 4 * 2 := by norm_num
      _ ≤ Nat.card rS * k := Nat.mul_le_mul hrS4 hk2
  have hpg : IsPGroup 2 ↥rT :=
    (C.hcs.setting.sylow.2.1).of_surjective (X.rho.comp (Subgroup.inclusion hTM)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hpg
  have hn3 : 3 ≤ n := by
    by_contra hlt3
    push Not at hlt3
    have : 2 ^ n ≤ 4 := by
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    omega
  have h8dvd : 8 ∣ Nat.card rT := by
    have h83 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h83, hn]
    exact pow_dvd_pow 2 hn3
  exact h8dvd.trans (Subgroup.card_dvd_of_le hrT)

theorem card_range_rho :
    Nat.card X.rho.range = 72 := by
  have h72 : 72 ∣ Nat.card X.rho.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 9) X.eight_dvd X.nine_dvd
  have hpos : 0 < Nat.card X.rho.range := Nat.card_pos
  have hle : Nat.card X.rho.range ≤ 72 :=
    (Subgroup.card_le_of_le X.rho_range_le).trans card_O4PlusTwo_le
  exact le_antisymm hle (Nat.le_of_dvd hpos h72)

theorem rho_range_eq :
    X.rho.range = O4PlusTwo := by
  apply Subgroup.eq_of_le_of_card_ge X.rho_range_le
  have h1 := card_O4PlusTwo_le
  have h2 := X.card_range_rho
  omega

theorem o4
    : ActsAsO4Plus (T ⊔ borelK M L) (borelP M L) (centerOf (borelP M L)) :=
  ⟨X.thG, X.rho, X.thG_surj, X.thG_ker, fun m x y hxy => X.rho_spec m x y hxy, X.rho_range_eq⟩

theorem irredV
    (What : V4 → Prop) (hzero : What 0) (hadd : ∀ a b, What a → What b → What (a + b))
    (hinv : ∀ (m : ↥(T ⊔ borelK M L)) v, What v → What ((X.rhoM m).mulVec v))
    (hne : ∃ v, v ≠ 0 ∧ What v) : ∀ v, What v := by
  have hsing : ∃ s, What s ∧ inSing s := by
    obtain ⟨v, hvne, hv⟩ := hne
    by_cases hW0 : inW0 v
    · exact ⟨v, hv, W0_sing v hW0 hvne⟩
    · obtain ⟨h1, h2⟩ := t1_step v hW0
      refine ⟨Mt1.mulVec v + v, hadd _ _ ?_ hv, W0_sing _ h1 h2⟩
      have := hinv ⟨_, C.t1_mem_M1⟩ v hv
      rwa [X.rho_t1] at this
  obtain ⟨s, hs, hss⟩ := hsing
  have hall : ∀ s', inSing s' → What s' := by
    intro s' hs'
    obtain ⟨m, hm⟩ := X.trans_sing s s' hss hs'
    rw [← hm]
    exact hinv m s hs
  intro v
  rcases sing_gen v with h0 | h1 | ⟨a, b, ha, hb, hab⟩
  · rw [h0]
    exact hzero
  · exact hall v h1
  · rw [← hab]
    exact hadd _ _ (hall a ha) (hall b hb)

theorem irred
    (W : Subgroup G) (hZW : centerOf (borelP M L) ≤ W) (hWP : W ≤ borelP M L)
    (hn : T ⊔ borelK M L ≤ Subgroup.normalizer (W : Set G)) :
    W = centerOf (borelP M L) ∨ W = borelP M L := by
  classical
  by_cases h : W ≤ centerOf (borelP M L)
  · exact Or.inl (le_antisymm h hZW)
  right
  apply le_antisymm hWP
  let What : V4 → Prop := fun v =>
    ∃ q : ↥(borelP M L), (q : G) ∈ W ∧ Multiplicative.toAdd (X.thG q) = v
  have hzero : What 0 := ⟨1, one_mem _, by rw [map_one, toAdd_one]⟩
  have hadd : ∀ a b, What a → What b → What (a + b) := by
    rintro a b ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
    exact ⟨q₁ * q₂, mul_mem hq₁ hq₂, by rw [map_mul, toAdd_mul]⟩
  have hinv : ∀ (m : ↥(T ⊔ borelK M L)) v, What v → What ((X.rhoM m).mulVec v) := by
    rintro m v ⟨q, hq, rfl⟩
    refine ⟨⟨(m : G) * q * (m : G)⁻¹, X.M1_normalizes m.2 q.2⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hn m.2) q).mp hq
    · exact X.rhoM_spec m q _ rfl
  obtain ⟨w0, hw0, hw0Z⟩ := IsConcreteLE.not_le_iff_exists.mp h
  have hw0P : w0 ∈ borelP M L := hWP hw0
  let q0 : ↥(borelP M L) := ⟨w0, hw0P⟩
  have hv : What (Multiplicative.toAdd (X.thG q0)) := ⟨q0, hw0, rfl⟩
  have hvne : Multiplicative.toAdd (X.thG q0) ≠ 0 := by
    intro h0
    apply hw0Z
    have h1 : q0 ∈ (X.thG).ker := h0
    rw [X.thG_ker] at h1
    exact h1
  have hv_all := X.irredV What hzero hadd hinv ⟨_, hvne, hv⟩
  intro p hp
  obtain ⟨q, hqW, hq⟩ := hv_all (Multiplicative.toAdd (X.thG ⟨p, hp⟩))
  have hq' : X.thG q = X.thG ⟨p, hp⟩ := Multiplicative.toAdd.injective hq
  have h1 : (⟨p, hp⟩ * q⁻¹ : ↥(borelP M L)) ∈ (X.thG).ker := by
    show X.thG (⟨p, hp⟩ * q⁻¹) = 1
    rw [map_mul, map_inv, hq']
    exact mul_inv_cancel _
  rw [X.thG_ker] at h1
  have h2 : p * (q : G)⁻¹ ∈ W := hZW h1
  have : p = (p * (q : G)⁻¹) * q := by group
  rw [this]
  exact mul_mem h2 hqW

theorem step3
    (h2 : A5Step2 T M H S L) : A5Step3 T M H S L := by
  have hTC := X.hTC
  refine
    { toA5Step2 := h2
      o4 := ?_
      irred := ?_
      U_not_le := C.U_not_le_O2_M1 }
  · rw [hTC, sup_bot_eq, sup_bot_eq]
    exact X.o4
  · rw [hTC, sup_bot_eq, sup_bot_eq]
    exact fun W hZW hWP hn => X.irred W hZW hWP hn

end Sec

theorem lemma2_4_29_3
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_3 := by
  intro G _ _ T M H S L cfg h2
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  exact X.step3 h2

end CFSG.QuasithinUnique.A5
