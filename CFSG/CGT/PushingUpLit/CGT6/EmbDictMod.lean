module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbDictXfer

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section Dict

variable {G : Type} [Group G] [Finite G]

structure Dict0 (V A : Subgroup G) [V.Normal] : Prop where
  hK : KTwo V A
  hR : SubTwo.NoTwoQuotient A

structure DictHyp (V A : Subgroup G) [V.Normal] : Prop extends Dict0 V A where
  hP : ⁅V, A⁆ = ⁅oTwoIn A, A⁆
  hZ : ∀ u ∈ ⁅oTwoIn A, A⁆, ∀ q ∈ oTwoIn A, u * q = q * u

variable {V A : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V) (D0 : Dict0 V A)
  (D : DictHyp V A)

omit [Finite G] in
theorem A_le_normalizer : A ≤ Subgroup.normalizer (V : Set G) :=
  le_trans le_top (top_le_normalizer_of_normal V)

omit [Finite G] in
theorem mem_V_of_mem_comm {g : G} (hg : g ∈ ⁅V, A⁆) : g ∈ V :=
  Subgroup.commutator_le_left V A hg

omit [Finite G] in
include hV in
theorem mem_commOn_of_mem_comm {g : G} (hg : g ∈ ⁅V, A⁆) :
    (⟨g, mem_V_of_mem_comm hg⟩ : ↥V) ∈ commOn hV A := by
  rw [commOn_eq hV (A_le_normalizer (V := V) (A := A)), Subgroup.mem_subgroupOf]
  show g ∈ ⁅A, V⁆
  rw [Subgroup.commutator_comm]
  exact hg

omit [Finite G] in
include hV in
theorem mem_comm_of_mem_commOn {w : ↥V} (hw : w ∈ commOn hV A) : (w : G) ∈ ⁅V, A⁆ := by
  rw [commOn_eq hV (A_le_normalizer (V := V) (A := A)), Subgroup.mem_subgroupOf] at hw
  rw [Subgroup.commutator_comm]
  exact hw

omit [Finite G] in
theorem comm_mem_comm {m : G} (hm : m ∈ ⁅V, A⁆) {a : G} (ha : a ∈ A) : ⁅m, a⁆ ∈ ⁅V, A⁆ :=
  Subgroup.commutator_mem_commutator (mem_V_of_mem_comm hm) ha

@[expose] noncomputable def mkV (g : G) (hg : g ∈ ⁅V, A⁆) : ↥(commOn hV A) :=
  ⟨⟨g, mem_V_of_mem_comm hg⟩, mem_commOn_of_mem_comm hV hg⟩

omit [Finite G] in
include hV in
theorem incPhi_mkV_comm {m : G} (hm : m ∈ ⁅V, A⁆) (a : ↥A) :
    incPhi hV A (mkV hV ⁅m, (a : G)⁆ (comm_mem_comm hm a.2)) =
      ⁅incPhi hV A (mkV hV m hm), sigPhi hV A a⁆ := by
  have h1 := @comm_yuInc_yuSec ↥V (commGroupOfElemAbelian hV) (autOn A V)
    (rhoA V A a) (mkV hV m hm)
  refine Eq.trans ?_ h1.symm
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  show ⁅m, (a : G)⁆ = m * ((((ambRho V (a : G)) (mkV hV m hm).1⁻¹ : ↥V)) : G)
  rw [ambRho_apply_coe, commutatorElement_def]
  simp [mul_assoc, mkV]

omit [Finite G] in
include D0 hV in
theorem incPhi_mem_pCore (w : ↥(commOn hV A)) :
    incPhi hV A w ∈ pCore 2 ↥(yuHolOf hV (autOn A V)) := by
  rw [pCore_phi hV A D0.hK]
  exact Subgroup.mem_comap.mpr (by
    rw [show projPhi hV A (incPhi hV A w) = 1 from rfl]
    exact Subgroup.one_mem _)

omit [Finite G] in
include D0 hV in
theorem sigPhi_mem_pCore {q : ↥A} (hq : q ∈ pCore 2 ↥A) :
    sigPhi hV A q ∈ pCore 2 ↥(yuHolOf hV (autOn A V)) := by
  rw [pCore_phi hV A D0.hK]
  exact Subgroup.mem_comap.mpr ⟨q, hq, rfl⟩

include D0 hV in
theorem incPhi_mem_of_comm (N : Subgroup ↥(yuHolOf hV (autOn A V)))
    (hN : ∀ (m : G) (hm : m ∈ ⁅V, A⁆) (a : ↥A),
      incPhi hV A (mkV hV ⁅m, (a : G)⁆ (comm_mem_comm hm a.2)) ∈ N) (w : ↥(commOn hV A)) :
    incPhi hV A w ∈ N := by
  have hV2 : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using hV.2 v v.2)⟩
  let W' : Subgroup G :=
    { carrier := {g | ∃ (hg : g ∈ V) (hc : (⟨g, hg⟩ : ↥V) ∈ commOn hV A),
        incPhi hV A ⟨⟨g, hg⟩, hc⟩ ∈ N}
      one_mem' := ⟨V.one_mem, (commOn hV A).one_mem, by
        have : (⟨⟨1, V.one_mem⟩, (commOn hV A).one_mem⟩ : ↥(commOn hV A)) = 1 := rfl
        rw [this, map_one]
        exact N.one_mem⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨h₁, c₁, t₁⟩ ⟨h₂, c₂, t₂⟩
        refine ⟨V.mul_mem h₁ h₂, (commOn hV A).mul_mem c₁ c₂, ?_⟩
        have : (⟨⟨g₁ * g₂, V.mul_mem h₁ h₂⟩, (commOn hV A).mul_mem c₁ c₂⟩ : ↥(commOn hV A)) =
            ⟨⟨g₁, h₁⟩, c₁⟩ * ⟨⟨g₂, h₂⟩, c₂⟩ := rfl
        rw [this, map_mul]
        exact N.mul_mem t₁ t₂
      inv_mem' := by
        rintro g ⟨h, c, t⟩
        refine ⟨V.inv_mem h, (commOn hV A).inv_mem c, ?_⟩
        have : (⟨⟨g⁻¹, V.inv_mem h⟩, (commOn hV A).inv_mem c⟩ : ↥(commOn hV A)) =
            (⟨⟨g, h⟩, c⟩ : ↥(commOn hV A))⁻¹ := rfl
        rw [this, map_inv]
        exact N.inv_mem t }
  have hW : ⁅⁅V, A⁆, A⁆ = ⁅V, A⁆ :=
    SixThree.commutator_commutator_eq D0.hR hV2 (A_le_normalizer (V := V) (A := A))
  have hWle : ⁅V, A⁆ ≤ W' := by
    rw [← hW]
    refine Subgroup.commutator_le.mpr (fun m hm a ha => ?_)
    exact ⟨mem_V_of_mem_comm (comm_mem_comm hm ha),
      mem_commOn_of_mem_comm hV (comm_mem_comm hm ha), hN m hm ⟨a, ha⟩⟩
  obtain ⟨hg, hc, ht⟩ := hWle (mem_comm_of_mem_commOn hV w.2)
  exact ht

include D0 hV in
theorem incPhi_mem_shortU (w : ↥(commOn hV A)) :
    incPhi hV A w ∈ shortU ↥(yuHolOf hV (autOn A V)) := by
  refine incPhi_mem_of_comm hV D0 _ (fun m hm a => ?_) w
  rw [incPhi_mkV_comm hV hm a]
  refine Subgroup.commutator_mem_commutator ?_ (Subgroup.mem_top _)
  rw [pCore_phi hV A D0.hK]
  exact Subgroup.mem_comap.mpr (by
    rw [show projPhi hV A (incPhi hV A _) = 1 from rfl]
    exact Subgroup.one_mem _)

omit [Finite G] in
include D in
theorem mem_V_of_mem_U {g : G} (hg : g ∈ ⁅oTwoIn A, A⁆) : g ∈ V := by
  rw [← D.hP] at hg
  exact Subgroup.commutator_le_left V A hg

omit [Finite G] in
include D hV in
theorem mem_commOn_of_mem_U {g : G} (hg : g ∈ ⁅oTwoIn A, A⁆) :
    (⟨g, mem_V_of_mem_U D hg⟩ : ↥V) ∈ commOn hV A := by
  rw [commOn_eq hV (A_le_normalizer (V := V) (A := A)), Subgroup.mem_subgroupOf]
  show g ∈ ⁅A, V⁆
  rw [Subgroup.commutator_comm, D.hP]
  exact hg

omit [Finite G] in
include D hV in
theorem mem_U_of_mem_commOn {w : ↥V} (hw : w ∈ commOn hV A) : (w : G) ∈ ⁅oTwoIn A, A⁆ := by
  rw [commOn_eq hV (A_le_normalizer (V := V) (A := A)), Subgroup.mem_subgroupOf] at hw
  rw [← D.hP, Subgroup.commutator_comm]
  exact hw

omit [Finite G] [V.Normal] in
theorem coe_mem_U (u : ↥(shortU ↥A)) : ((u : ↥A) : G) ∈ ⁅oTwoIn A, A⁆ := by
  rw [← SixThree.map_shortU A]
  exact Subgroup.mem_map.mpr ⟨(u : ↥A), u.2, rfl⟩

omit [Finite G] [V.Normal] in
theorem mem_shortU_of_mem_U {a : ↥A} (h : (a : G) ∈ ⁅oTwoIn A, A⁆) : a ∈ shortU ↥A := by
  rw [← SixThree.map_shortU A] at h
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp h
  have : b = a := Subtype.ext hba
  rwa [← this]

@[expose] noncomputable def uComm : ↥(shortU ↥A) →* ↥(commOn hV A) where
  toFun u := ⟨⟨((u : ↥A) : G), mem_V_of_mem_U D (coe_mem_U u)⟩,
    mem_commOn_of_mem_U hV D (coe_mem_U u)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
theorem uComm_injective : Function.Injective (uComm hV D) := fun _ _ h =>
  Subtype.ext (Subtype.ext (congrArg (fun x : ↥(commOn hV A) => ((x : ↥V) : G)) h))

omit [Finite G] in
include D hV in
theorem shortU_phi_le_ker : shortU ↥(yuHolOf hV (autOn A V)) ≤ (projPhi hV A).ker := by
  unfold shortU
  rw [Subgroup.commutator_le]
  intro p hp x _
  rw [pCore_phi hV A D.hK] at hp
  obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hp)
  obtain ⟨a, ha⟩ := rhoA_surjective V A (projPhi hV A x)
  rw [MonoidHom.mem_ker, map_commutatorElement, ← hqp, ← ha, ← map_commutatorElement,
    ← MonoidHom.mem_ker, mem_ker_rhoA]
  have hqO : (q : G) ∈ oTwoIn A := ⟨q, hq, rfl⟩
  have h1 : ((⁅q, a⁆ : ↥A) : G) ∈ ⁅oTwoIn A, A⁆ :=
    Subgroup.commutator_mem_commutator hqO a.2
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1 (mem_V_of_mem_U D h1)

include D hV in
theorem shortU_phi_eq_ker : shortU ↥(yuHolOf hV (autOn A V)) = (projPhi hV A).ker := by
  refine le_antisymm (shortU_phi_le_ker hV D) (fun x hx => ?_)
  rw [ker_projPhi hV A] at hx
  obtain ⟨w, rfl⟩ := hx
  exact incPhi_mem_shortU hV D.toDict0 w

@[expose] noncomputable def kappa0 :
    ↥(shortU ↥A) →* ↥(shortU ↥(yuHolOf hV (autOn A V))) :=
  ((incPhi hV A).comp (uComm hV D)).codRestrict _ fun u =>
    incPhi_mem_shortU hV D.toDict0 (uComm hV D u)

theorem coe_kappa0 (u : ↥(shortU ↥A)) :
    ((kappa0 hV D u : ↥(shortU ↥(yuHolOf hV (autOn A V)))) : ↥(yuHolOf hV (autOn A V))) =
      incPhi hV A (uComm hV D u) := rfl

theorem kappa0_injective : Function.Injective (kappa0 hV D) := fun _ _ h =>
  uComm_injective hV D (@yuInc_injective ↥V (commGroupOfElemAbelian hV) (autOn A V) _ _
    (congrArg Subtype.val h))

theorem kappa0_surjective : Function.Surjective (kappa0 hV D) := by
  intro y
  have hy : (y : ↥(yuHolOf hV (autOn A V))) ∈ (projPhi hV A).ker :=
    shortU_phi_le_ker hV D y.2
  rw [ker_projPhi hV A] at hy
  obtain ⟨w, hw⟩ := hy
  have hwU := mem_U_of_mem_commOn hV D w.2
  have hwA : ((w : ↥V) : G) ∈ A :=
    (SixThree.oTwoIn_le A) ((SixThree.U_le_oTwoIn A) hwU)
  refine ⟨⟨⟨(w : G), hwA⟩, mem_shortU_of_mem_U hwU⟩, Subtype.ext ?_⟩
  rw [coe_kappa0]
  exact hw

@[expose] noncomputable def kappa : ↥(shortU ↥A) ≃* ↥(shortU ↥(yuHolOf hV (autOn A V))) :=
  MulEquiv.ofBijective (kappa0 hV D) ⟨kappa0_injective hV D, kappa0_surjective hV D⟩

theorem coe_kappa (u : ↥(shortU ↥A)) :
    ((kappa hV D u : ↥(shortU ↥(yuHolOf hV (autOn A V)))) : ↥(yuHolOf hV (autOn A V))) =
      incPhi hV A (uComm hV D u) := rfl

omit [Finite G] [V.Normal] in
include hV in
theorem conj_incPhi_exists (x : ↥(yuHolOf hV (autOn A V))) (u : ↥(commOn hV A)) :
    ∃ u' : ↥(commOn hV A),
      ((u' : ↥V) = ((x : HolOf hV).right : MulAut ↥V) (u : ↥V)) ∧
        x * incPhi hV A u * x⁻¹ = incPhi hV A u' :=
  ⟨⟨_, @apply_mem_commV_self ↥V (commGroupOfElemAbelian hV) (autOn A V) _ x.2.2 _ u.2⟩, rfl,
    @conj_yuInc ↥V (commGroupOfElemAbelian hV) (autOn A V) x u⟩

omit [Finite G] in
include hV in
theorem right_apply_coe (x : ↥(yuHolOf hV (autOn A V))) (a : ↥A)
    (ha : rhoA V A a = projPhi hV A x) (v : ↥V) :
    ((((x : HolOf hV).right : MulAut ↥V) v : ↥V) : G) = (a : G) * (v : G) * (a : G)⁻¹ := by
  have h : ((x : HolOf hV).right : MulAut ↥V) = ambRho V (a : G) := (congrArg Subtype.val ha).symm
  rw [h, ambRho_apply_coe]

include D hV in
theorem kappa_mem_C (u : ↥(shortU ↥A)) :
    ((kappa hV D u : ↥(shortU ↥(yuHolOf hV (autOn A V)))) : ↥(yuHolOf hV (autOn A V))) ∈
      shortC ↥(yuHolOf hV (autOn A V)) ↔ (u : ↥A) ∈ shortC ↥A := by
  have hA : (u : ↥A) ∈ shortC ↥A ↔ ∀ a : ↥A, a * (u : ↥A) = (u : ↥A) * a := by
    unfold shortC
    rw [Subgroup.mem_inf, Subgroup.mem_center_iff]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hΦ : ((kappa hV D u : ↥(shortU ↥(yuHolOf hV (autOn A V)))) :
      ↥(yuHolOf hV (autOn A V))) ∈ shortC ↥(yuHolOf hV (autOn A V)) ↔
      ∀ x : ↥(yuHolOf hV (autOn A V)), x * incPhi hV A (uComm hV D u) =
        incPhi hV A (uComm hV D u) * x := by
    unfold shortC
    rw [Subgroup.mem_inf, Subgroup.mem_center_iff]
    exact ⟨fun h => h.2, fun h => ⟨(kappa hV D u).2, h⟩⟩
  rw [hA, hΦ]
  constructor
  · intro h a
    obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV (sigPhi hV A a) (uComm hV D u)
    have h2 : incPhi hV A u' = incPhi hV A (uComm hV D u) := by
      rw [← hu'2, h (sigPhi hV A a)]
      group
    have h3 : u' = uComm hV D u :=
      @yuInc_injective ↥V (commGroupOfElemAbelian hV) (autOn A V) _ _ h2
    have h4 : (a : G) * ((u : ↥A) : G) * (a : G)⁻¹ = ((u : ↥A) : G) := by
      have h5 := right_apply_coe hV (sigPhi hV A a) a rfl (uComm hV D u).1
      have h6 : ((((sigPhi hV A a : ↥(yuHolOf hV (autOn A V))) : HolOf hV).right :
          MulAut ↥V) ((uComm hV D u).1 : ↥V) : ↥V) = ((uComm hV D u).1 : ↥V) := by
        rw [← hu'1, h3]
      exact h5.symm.trans (congrArg Subtype.val h6)
    apply Subtype.ext
    show (a : G) * ((u : ↥A) : G) = ((u : ↥A) : G) * (a : G)
    calc (a : G) * ((u : ↥A) : G) = ((a : G) * ((u : ↥A) : G) * (a : G)⁻¹) * a := by group
      _ = ((u : ↥A) : G) * (a : G) := by rw [h4]
  · intro h x
    obtain ⟨a, ha⟩ := rhoA_surjective V A (projPhi hV A x)
    have h4 : (a : G) * ((u : ↥A) : G) * (a : G)⁻¹ = ((u : ↥A) : G) := by
      have := congrArg Subtype.val (h a)
      calc (a : G) * ((u : ↥A) : G) * (a : G)⁻¹ = ((u : ↥A) : G) * (a : G) * (a : G)⁻¹ := by
            rw [show ((a : G) * ((u : ↥A) : G)) = ((u : ↥A) : G) * (a : G) from this]
        _ = ((u : ↥A) : G) := by group
    obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV x (uComm hV D u)
    have h3 : u' = uComm hV D u := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [hu'1]
      exact (right_apply_coe hV x a ha (uComm hV D u).1).trans h4
    rw [h3] at hu'2
    rw [mul_inv_eq_iff_eq_mul] at hu'2
    exact hu'2

include D hV in
@[expose] noncomputable def shortIsoPhi : ShortIso ↥A ↥(yuHolOf hV (autOn A V)) where
  e := (ePhi hV A D.hK).symm
  κ := kappa hV D
  mem_C := kappa_mem_C hV D
  conj l₁ l₂ h u hu := by
    have h1 : (l₁ : ↥A ⧸ pCore 2 ↥A) = lamPhi hV A D.hK l₂ := by
      have := congrArg (ePhi hV A D.hK) h
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨a₀, ha₀⟩ := rhoA_surjective V A (projPhi hV A l₂)
    have h2 : (l₁ : ↥A ⧸ pCore 2 ↥A) = (a₀ : ↥A ⧸ pCore 2 ↥A) := by
      rw [h1]
      show lamHat A D.hK (projPhi hV A l₂) = _
      rw [← ha₀, lamHat_rhoA]
    have hq : l₁⁻¹ * a₀ ∈ pCore 2 ↥A := QuotientGroup.eq.mp h2
    have hqO : (((l₁⁻¹ * a₀ : ↥A)) : G) ∈ oTwoIn A := ⟨_, hq, rfl⟩
    have hZ := D.hZ _ (coe_mem_U u) _ hqO
    obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV l₂ (uComm hV D u)
    rw [coe_kappa, coe_kappa, hu'2]
    congr 1
    refine Subtype.ext (Subtype.ext ?_)
    rw [hu'1, right_apply_coe hV l₂ a₀ ha₀]
    have ha₀' : (a₀ : G) = (l₁ : G) * ((l₁⁻¹ * a₀ : ↥A) : G) := by
      simp
    show (l₁ : G) * ((u : ↥A) : G) * (l₁ : G)⁻¹ = (a₀ : G) * ((u : ↥A) : G) * (a₀ : G)⁻¹
    rw [ha₀']
    have : ((l₁⁻¹ * a₀ : ↥A) : G) * ((u : ↥A) : G) * ((l₁⁻¹ * a₀ : ↥A) : G)⁻¹ = ((u : ↥A) : G) := by
      rw [← hZ]
      group
    calc (l₁ : G) * ((u : ↥A) : G) * (l₁ : G)⁻¹
        = (l₁ : G) * (((l₁⁻¹ * a₀ : ↥A) : G) * ((u : ↥A) : G) * ((l₁⁻¹ * a₀ : ↥A) : G)⁻¹) *
            (l₁ : G)⁻¹ := by rw [this]
      _ = _ := by group

end Dict

end CFSG.CGT.PushingUpLit.CGT6
