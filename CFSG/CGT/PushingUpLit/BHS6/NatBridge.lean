module

public import CFSG.CGT.PushingUpLit.BHS.OffenderBridge
public import CFSG.CGT.PushingUpLit.BHS6.SixFour
public import CFSG.CGT.PushingUpLit.BHS6.Conj
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def actOn (V X : Subgroup Γ)
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) : ↥X →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hX)

theorem actOn_apply_coe {V X : Subgroup Γ} (hX : X ≤ Subgroup.normalizer (V : Set Γ)) (x : ↥X)
    (v : ↥V) : ((actOn V X hX x v : ↥V) : Γ) = (x : Γ) * v * (x : Γ)⁻¹ :=
  conjAct_apply' V (Subgroup.inclusion hX x) v

theorem range_actOn (V X : Subgroup Γ) (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    (actOn V X hX).range = autOn X V := by
  unfold actOn autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem ker_actOn (V X : Subgroup Γ) (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    (actOn V X hX).ker = (X ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf X := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : Γ)) h
    simp only [actOn_apply_coe, MulAut.one_apply] at this
    have h2 : (a : Γ) * v * (a : Γ)⁻¹ = v := this
    calc v * (a : Γ) = ((a : Γ) * v * (a : Γ)⁻¹) * a := by rw [h2]
      _ = a * v := by group
  · rintro ⟨-, hc⟩
    ext v
    rw [actOn_apply_coe, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hc v v.2
    show (a : Γ) * v * (a : Γ)⁻¹ = v
    rw [← h, mul_inv_cancel_right]

@[expose] noncomputable def actOnRange (V X : Subgroup Γ)
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) : ↥X →* ↥(autOn X V) :=
  (actOn V X hX).codRestrict (autOn X V) fun x => by
    rw [← range_actOn V X hX]
    exact ⟨x, rfl⟩

theorem actOnRange_surjective (V X : Subgroup Γ) (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    Function.Surjective (actOnRange V X hX) := by
  rintro ⟨y, hy⟩
  rw [← range_actOn V X hX] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

theorem ker_actOnRange (V X : Subgroup Γ) (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    (actOnRange V X hX).ker = (X ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf X := by
  rw [← ker_actOn V X hX]
  ext x
  simp only [MonoidHom.mem_ker, actOnRange, MonoidHom.codRestrict_apply]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

@[expose] noncomputable def commOn {V : Subgroup Γ} (hV : IsElemAbelian 2 V) (X : Subgroup Γ) :
    Subgroup ↥V :=
  @commV ↥V (commGroupOfElemAbelian hV) (autOn X V)

@[expose] noncomputable def fixOn {V : Subgroup Γ} (hV : IsElemAbelian 2 V) (X : Subgroup Γ) :
    Subgroup ↥V :=
  @fixV ↥V (commGroupOfElemAbelian hV) (autOn X V)

theorem commutator_le_of_le_normalizer {V X : Subgroup Γ}
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) : ⁅X, V⁆ ≤ V :=
  Subgroup.le_normalizer_iff_commutator_le_right.mp hX

theorem map_commOn {V X : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    (commOn hV X).map V.subtype = ⁅X, V⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold commOn commV
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, rfl⟩
    rw [← range_actOn V X hX] at hσ
    obtain ⟨g, rfl⟩ := hσ
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show ((actOn V X hX g v * v⁻¹ : ↥V) : Γ) ∈ ⁅X, V⁆
    rw [Subgroup.coe_mul, actOn_apply_coe, Subgroup.coe_inv]
    have e : (g : Γ) * v * (g : Γ)⁻¹ * (v : Γ)⁻¹ = ⁅(g : Γ), (v : Γ)⁆ := by
      rw [commutatorElement_def]
    rw [e]
    exact Subgroup.commutator_mem_commutator g.2 v.2
  · rw [Subgroup.commutator_le]
    intro g hg v hv
    have hmem : actOn V X hX ⟨g, hg⟩ ⟨v, hv⟩ * (⟨v, hv⟩ : ↥V)⁻¹ ∈ commOn hV X :=
      Subgroup.subset_closure ⟨_, by rw [← range_actOn V X hX]; exact ⟨_, rfl⟩, ⟨v, hv⟩, rfl⟩
    refine ⟨_, hmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, actOn_apply_coe]
    rw [commutatorElement_def]

theorem commOn_eq {V X : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    commOn hV X = (⁅X, V⁆ : Subgroup Γ).subgroupOf V := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← map_commOn hV hX]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem fixOn_eq {V X : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (hX : X ≤ Subgroup.normalizer (V : Set Γ)) :
    fixOn hV X = (Subgroup.centralizer (X : Set Γ)).subgroupOf V := by
  ext v
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (actOn V X hX ⟨a, ha⟩)
      (by rw [← range_actOn V X hX]; exact ⟨_, rfl⟩)
    have h3 : (a : Γ) * v * (a : Γ)⁻¹ = v := by
      have := actOn_apply_coe hX ⟨a, ha⟩ v
      rw [← this]
      exact congrArg (fun x : ↥V => (x : Γ)) h1
    calc (a : Γ) * v = ((a : Γ) * v * (a : Γ)⁻¹) * a := by group
      _ = v * a := by rw [h3]
  · intro h x hx
    rw [← range_actOn V X hX] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Subtype.ext
    rw [actOn_apply_coe]
    have := h a a.2
    rw [this, mul_inv_cancel_right]

@[expose] def IsNatBy {S M : Type*} [Group S] [Group M] (act : S → M → M) (E W : Subgroup Γ) :
    Prop :=
  ∃ (φ : ↥E →* S) (ψ : ↥W →* M), Function.Surjective φ ∧
    φ.ker = (E ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf E ∧ Function.Surjective ψ ∧
    ψ.ker = (W ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf W ∧
    ∀ (e : ↥E) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
      ψ ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = act (φ e) (ψ w)

theorem isNatSL_iff {E W : Subgroup Γ} {n : ℕ} :
    IsNatSL E W n ↔ IsNatBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (m : Multiplicative (Fin 2 → GaloisField 2 n)) =>
        Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd m))) E W := Iff.rfl

theorem isNatSym_iff {E W : Subgroup Γ} {m : ℕ} :
    IsNatSym E W m ↔ IsNatBy (fun (s : Equiv.Perm (Fin m)) (v : ↥(coreMod m)) => coreAct m s v)
      E W := Iff.rfl

@[expose] def IsNatAlt (E W : Subgroup Γ) (n : ℕ) : Prop :=
  IsNatBy (fun (s : alternatingGroup (Fin n)) (v : ↥(coreMod n)) =>
    coreAct n (s : Equiv.Perm (Fin n)) v) E W

@[expose] def IsNatSectionBy {V : Type*} [CommGroup V] {S M : Type*} [Group S] [Group M]
    (act : S → M → M) (X : Subgroup (MulAut V)) (P Z : Subgroup V) : Prop :=
  (∀ x ∈ X, ∀ p ∈ P, x p ∈ P) ∧ ∃ (θ : X ≃* S) (β : ↥P →* M),
    Function.Surjective β ∧ β.ker = Z.subgroupOf P ∧
    ∀ (x : X) (p : ↥P) (hp : (x : MulAut V) p ∈ P),
      β ⟨(x : MulAut V) p, hp⟩ = act (θ x) (β p)

theorem isSLNatSection_iff {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)} {P Z : Subgroup V}
    {k : ℕ} :
    IsSLNatSection X P Z k ↔ IsNatSectionBy
      (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))
        (m : Multiplicative (Fin 2 → GaloisField 2 k)) =>
          Multiplicative.ofAdd ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec
            (Multiplicative.toAdd m))) X P Z := Iff.rfl

theorem isAltNatSection_iff {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)} {P Z : Subgroup V}
    {n : ℕ} :
    IsAltNatSection X P Z n ↔ IsNatSectionBy
      (fun (s : alternatingGroup (Fin n)) (v : ↥(coreMod n)) =>
        coreAct n (s : Equiv.Perm (Fin n)) v) X P Z := Iff.rfl

theorem isNatSectionBy_autOn {V X W : Subgroup Γ} {S M : Type*} [Group S] [Group M]
    {act : S → M → M} (hV : IsElemAbelian 2 V) (hXV : X ≤ Subgroup.normalizer (V : Set Γ))
    (hnat : IsNatBy act X W) (hVW : ⁅X, V⁆ ≤ W)
    (hfac : ∀ w ∈ W, ∃ p ∈ (⁅X, V⁆ : Subgroup Γ),
      ∃ c ∈ W ⊓ Subgroup.centralizer (X : Set Γ), w = p * c)
    (hker : X ⊓ Subgroup.centralizer (V : Set Γ) = X ⊓ Subgroup.centralizer (W : Set Γ)) :
    @IsNatSectionBy ↥V (commGroupOfElemAbelian hV) S M _ _ act (autOn X V) (commOn hV X)
      (commOn hV X ⊓ fixOn hV X) := by
  classical
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  have hcomm : commOn hV X = (⁅X, V⁆ : Subgroup Γ).subgroupOf V := commOn_eq hV hXV
  have hfix : fixOn hV X = (Subgroup.centralizer (X : Set Γ)).subgroupOf V := fixOn_eq hV hXV
  have hXVV : ⁅X, V⁆ ≤ V := commutator_le_of_le_normalizer hXV
  have hPW : ∀ x : ↥(commOn hV X), ((x : ↥V) : Γ) ∈ W := fun x => by
    have : (x : ↥V) ∈ (⁅X, V⁆ : Subgroup Γ).subgroupOf V := hcomm ▸ x.2
    exact hVW this
  have hPX : ∀ x : ↥(commOn hV X), ((x : ↥V) : Γ) ∈ (⁅X, V⁆ : Subgroup Γ) := fun x => by
    have : (x : ↥V) ∈ (⁅X, V⁆ : Subgroup Γ).subgroupOf V := hcomm ▸ x.2
    exact this
  let ι : ↥(commOn hV X) →* ↥W :=
    MonoidHom.mk' (fun x => ⟨((x : ↥V) : Γ), hPW x⟩) fun a b => rfl
  have hι : ∀ x : ↥(commOn hV X), ((ι x : ↥W) : Γ) = ((x : ↥V) : Γ) := fun x => rfl
  refine ⟨?_, ?_⟩
  ·
    intro x hx p hp
    rw [← range_actOn V X hXV] at hx
    obtain ⟨g, rfl⟩ := hx
    rw [hcomm, Subgroup.mem_subgroupOf] at hp ⊢
    rw [actOn_apply_coe]
    have hn : (g : Γ) ∈ Subgroup.normalizer ((⁅X, V⁆ : Subgroup Γ) : Set Γ) :=
      mem_normalizer_commutator (Subgroup.le_normalizer g.2) (hXV g.2)
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp hp
  ·
    have hρs := actOnRange_surjective V X hXV
    have hkerEq : (actOnRange V X hXV).ker = φ.ker := by
      rw [ker_actOnRange, hφk, hker]
    let θ : ↥(autOn X V) ≃* S :=
      (QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφs))
    have hθ : ∀ g : ↥X, θ (actOnRange V X hXV g) = φ g := fun g => by
      show (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
        ((QuotientGroup.quotientMulEquivOfEq hkerEq)
          ((QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm
            (actOnRange V X hXV g))) = φ g
      have : (QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm (actOnRange V X hXV g) =
          (QuotientGroup.mk g : ↥X ⧸ (actOnRange V X hXV).ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [this]
      rfl
    refine ⟨θ, ψ.comp ι, ?_, ?_, ?_⟩
    ·
      intro m
      obtain ⟨w, hw⟩ := hψs m
      obtain ⟨p, hp, c, hc, hwpc⟩ := hfac (w : Γ) w.2
      have hpV : p ∈ V := hXVV hp
      have hpP : (⟨p, hpV⟩ : ↥V) ∈ commOn hV X := by
        rw [hcomm, Subgroup.mem_subgroupOf]
        exact hp
      refine ⟨⟨⟨p, hpV⟩, hpP⟩, ?_⟩
      have hcker : (⟨c, hc.1⟩ : ↥W) ∈ ψ.ker := by
        rw [hψk, Subgroup.mem_subgroupOf]
        exact hc
      have hpW : p ∈ W := hVW hp
      have hw' : w = (⟨p, hpW⟩ : ↥W) * ⟨c, hc.1⟩ := Subtype.ext hwpc
      have : ψ (ι ⟨⟨p, hpV⟩, hpP⟩) = ψ w := by
        have h1 : ι ⟨⟨p, hpV⟩, hpP⟩ = ⟨p, hpW⟩ := rfl
        rw [h1, hw', map_mul, MonoidHom.mem_ker.mp hcker, mul_one]
      rw [MonoidHom.comp_apply, this, hw]
    ·
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        hfix, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      have h1 : ψ (ι x) = 1 ↔ ι x ∈ ψ.ker := (MonoidHom.mem_ker).symm
      rw [h1, hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hι, Subgroup.mem_centralizer_iff]
      constructor
      · intro h
        exact ⟨x.2, h.2⟩
      · intro h
        exact ⟨hPW x, h.2⟩
    ·
      intro x p hp
      obtain ⟨g, rfl⟩ := hρs x
      have hcoe : (((actOnRange V X hXV g : MulAut ↥V)) p : ↥V) = actOn V X hXV g p := rfl
      have hgp : (g : Γ) * ((p : ↥V) : Γ) * (g : Γ)⁻¹ ∈ W := by
        have := hPW ⟨_, hp⟩
        simpa [hcoe, actOn_apply_coe] using this
      have key := hψe g (ι p) hgp
      rw [hθ g]
      simp only [MonoidHom.comp_apply]
      rw [← key]
      rfl

section Block

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.QuasithinUnique

variable {E : Subgroup Γ}

theorem mem_pCore_iff_mem_pCoreOf (x : ↥E) :
    x ∈ CFSG.pCore 2 ↥E ↔ (x : Γ) ∈ pCoreOf 2 E := (CFSG.mem_openPCoreOf_iff x).symm

theorem map_shortU_eq_pCoreOf (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) :
    (shortU ↥E).map E.subtype = pCoreOf 2 E := by
  rw [map_shortU_subtype, blockU, oTwoIn_eq_pCoreOf, hperf]

theorem map_shortC_eq (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) :
    (shortC ↥E).map E.subtype = pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) := by
  rw [map_shortC_subtype, blockZ, blockU, oTwoIn_eq_pCoreOf, hperf]

theorem mem_shortC_iff (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) (x : ↥E) :
    x ∈ shortC ↥E ↔ (x : Γ) ∈ pCoreOf 2 E ⊓ Subgroup.centralizer (E : Set Γ) := by
  rw [← map_shortC_eq hperf]
  exact (Subgroup.mem_map_iff_mem E.subtype_injective).symm

theorem mem_shortU_iff (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) (x : ↥E) :
    x ∈ shortU ↥E ↔ (x : Γ) ∈ pCoreOf 2 E := by
  rw [← map_shortU_eq_pCoreOf hperf]
  exact (Subgroup.mem_map_iff_mem E.subtype_injective).symm

@[expose] noncomputable def shortUEquiv (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) :
    ↥(shortU ↥E) ≃* ↥(pCoreOf 2 E) :=
  (Subgroup.equivMapOfInjective (shortU ↥E) E.subtype E.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_shortU_eq_pCoreOf hperf))

theorem shortUEquiv_coe (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) (u : ↥(shortU ↥E)) :
    ((shortUEquiv hperf u : ↥(pCoreOf 2 E)) : Γ) = (((u : ↥E)) : Γ) := rfl

theorem inf_centralizer_pCoreOf_eq (hchar : CharTwo E)
    (hW : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x) :
    E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) = pCoreOf 2 E := by
  refine le_antisymm hchar fun x hx => Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E hx
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hW y hy x hx)

theorem pCore_eq_inf_centralizer (hchar : CharTwo E)
    (hW : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x) :
    CFSG.pCore 2 ↥E = (E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ)).subgroupOf E := by
  ext x
  rw [Subgroup.mem_subgroupOf, inf_centralizer_pCoreOf_eq hchar hW,
    mem_pCore_iff_mem_pCoreOf]

theorem isNatSL_of_isNaturalSLTwoModule {n : ℕ} (hchar : CharTwo E)
    (hW : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x)
    (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) (hnat : IsNaturalSLTwoModule ↥E n) :
    IsNatSL E (pCoreOf 2 E) n := by
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  let eU := shortUEquiv hperf
  let φ' : ↥E →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (φ : (↥E ⧸ CFSG.pCore 2 ↥E) →* _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥E))
  have hφ'k : φ'.ker = (E ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf E := by
    rw [← pCore_eq_inf_centralizer hchar hW]
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk x) = 1 ↔ x ∈ CFSG.pCore 2 ↥E
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨φ', ψ.comp eU.symm.toMonoidHom, φ.surjective.comp (QuotientGroup.mk'_surjective _), hφ'k,
    hψs.comp eU.symm.surjective, ?_, ?_⟩
  · ext w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      MulEquiv.coe_toMonoidHom]
    have h1 : ψ (eU.symm w) = 1 ↔ eU.symm w ∈ ψ.ker := MonoidHom.mem_ker.symm
    have hcoe : (((eU.symm w : ↥(shortU ↥E)) : ↥E) : Γ) = (w : Γ) := by
      have := shortUEquiv_coe hperf (eU.symm w)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, hψk, Subgroup.mem_subgroupOf, mem_shortC_iff hperf, hcoe]
  · intro e w hw
    set u : ↥(shortU ↥E) := eU.symm w with hu
    have hu1 : ((u : ↥E) : Γ) = (w : Γ) := by
      have := shortUEquiv_coe hperf (eU.symm w)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hu' : e * (u : ↥E) * e⁻¹ ∈ shortU ↥E := by
      rw [← Subgroup.mem_map_iff_mem E.subtype_injective, map_shortU_eq_pCoreOf hperf]
      show ((e * (u : ↥E) * e⁻¹ : ↥E) : Γ) ∈ W
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
      exact hw
    have hsub : eU.symm ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = ⟨e * (u : ↥E) * e⁻¹, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((e : Γ) * w * (e : Γ)⁻¹) = ((e * (u : ↥E) * e⁻¹ : ↥E) : Γ)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
    have key := hψe e u u.2 hu'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hsub, key]
    rfl

theorem isNatAlt_of_isNaturalAltModule {m : ℕ} (hchar : CharTwo E)
    (hW : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x)
    (hperf : ⁅pCoreOf 2 E, E⁆ = pCoreOf 2 E) (hnat : IsNaturalAltModule ↥E m) :
    IsNatAlt E (pCoreOf 2 E) (2 * m + 1) := by
  obtain ⟨φ, ψ, hsum, hsurj, hψk, hψe⟩ := hnat
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  let eU := shortUEquiv hperf
  let φ' : ↥E →* alternatingGroup (Fin (2 * m + 1)) :=
    (φ : (↥E ⧸ CFSG.pCore 2 ↥E) →* _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥E))
  have hφ'k : φ'.ker = (E ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf E := by
    rw [← pCore_eq_inf_centralizer hchar hW]
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk x) = 1 ↔ x ∈ CFSG.pCore 2 ↥E
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  let ψ' : ↥W →* ↥(coreMod (2 * m + 1)) :=
    (ψ.comp eU.symm.toMonoidHom).codRestrict (coreMod (2 * m + 1)) fun w => by
      rw [mem_coreMod]
      exact hsum _
  have hψ'coe : ∀ w : ↥W, ((ψ' w : ↥(coreMod (2 * m + 1))) : PermMod (2 * m + 1)) =
      ψ (eU.symm w) := fun w => rfl
  refine ⟨φ', ψ', φ.surjective.comp (QuotientGroup.mk'_surjective _), hφ'k, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd (v : PermMod (2 * m + 1))) v.2
    refine ⟨eU u, Subtype.ext ?_⟩
    rw [hψ'coe, MulEquiv.symm_apply_apply, hu]
    rfl
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ' w = 1 ↔ ψ (eU.symm w) = 1 := by
      constructor
      · intro h
        have := congrArg Subtype.val h
        exact this
      · intro h
        exact Subtype.ext h
    have hcoe : (((eU.symm w : ↥(shortU ↥E)) : ↥E) : Γ) = (w : Γ) := by
      have := shortUEquiv_coe hperf (eU.symm w)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, ← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf, mem_shortC_iff hperf, hcoe]
  · intro e w hw
    set u : ↥(shortU ↥E) := eU.symm w with hu
    have hu1 : ((u : ↥E) : Γ) = (w : Γ) := by
      have := shortUEquiv_coe hperf (eU.symm w)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hu' : e * (u : ↥E) * e⁻¹ ∈ shortU ↥E := by
      rw [← Subgroup.mem_map_iff_mem E.subtype_injective, map_shortU_eq_pCoreOf hperf]
      show ((e * (u : ↥E) * e⁻¹ : ↥E) : Γ) ∈ W
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
      exact hw
    have hsub : eU.symm ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = ⟨e * (u : ↥E) * e⁻¹, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((e : Γ) * w * (e : Γ)⁻¹) = ((e * (u : ↥E) * e⁻¹ : ↥E) : Γ)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
    have key := hψe e u u.2 hu'
    apply Subtype.ext
    rw [hψ'coe, hsub, key, coreAct_coe, hψ'coe]
    rfl

end Block

section BlockLevel

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.QuasithinUnique

variable [Finite Γ] {G T E : Subgroup Γ}

theorem isNatSL_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {n : ℕ} (hn : IsNaturalSLTwoModule ↥E n) : IsNatSL E (blockW E) n := by
  rw [blockW_eq_pCoreOf hE]
  exact isNatSL_of_isNaturalSLTwoModule (charTwo_of_isBTBlock hG hT hE) hE.elemAbelian.1
    hE.perfect hn

theorem isNatAlt_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {m : ℕ} (hm : IsNaturalAltModule ↥E m) : IsNatAlt E (blockW E) (2 * m + 1) := by
  rw [blockW_eq_pCoreOf hE]
  exact isNatAlt_of_isNaturalAltModule (charTwo_of_isBTBlock hG hT hE) hE.elemAbelian.1
    hE.perfect hm

theorem bridge_data_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {V : Subgroup Γ} (hVQ : V ≤ pCoreOf 2 G) (hEV : E ≤ Subgroup.normalizer (V : Set Γ))
    (hne : ⁅E, V⁆ ≠ ⊥) :
    ⁅E, V⁆ ≤ blockW E ∧
      (∀ w ∈ blockW E, ∃ p ∈ (⁅E, V⁆ : Subgroup Γ),
        ∃ c ∈ blockW E ⊓ Subgroup.centralizer (E : Set Γ), w = p * c) ∧
      E ⊓ Subgroup.centralizer (V : Set Γ) = E ⊓ Subgroup.centralizer (blockW E : Set Γ) := by
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  rw [blockW_eq_pCoreOf hE]
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  set C₀ : Subgroup Γ := W ⊓ Subgroup.centralizer (E : Set Γ) with hC₀
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := hE.elemAbelian.1
  have hW2 : IsPGroup 2 ↥W := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E
  have hVW : ⁅E, V⁆ ≤ W :=
    (Subgroup.commutator_mono le_rfl hVQ).trans (commutator_pCoreOf_le hT hE)
  have hC₀W : C₀ ≤ W := inf_le_left
  have hC₀c : C₀ ≤ Subgroup.centralizer (E : Set Γ) := inf_le_right
  have hcomm : ∀ a ∈ (⁅E, V⁆ : Subgroup Γ), ∀ c ∈ C₀, a * c = c * a :=
    fun a ha c hc => hWab a (hVW ha) c (hC₀W hc)
  have hNn : ∀ g ∈ E, ∀ n ∈ (⁅E, V⁆ ⊔ C₀ : Subgroup Γ),
      g * n * g⁻¹ ∈ (⁅E, V⁆ ⊔ C₀ : Subgroup Γ) := by
    intro g hg n hn
    obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup' hcomm hn
    have hgc : g * c = c * g := Subgroup.mem_centralizer_iff.mp (hC₀c hc) g hg
    have h3 : g * (a * c) * g⁻¹ = (g * a * g⁻¹) * c := by
      calc g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * a * g⁻¹) * c := by rw [hgc]; group
    rw [h3]
    have hgN : g ∈ Subgroup.normalizer ((⁅E, V⁆ : Subgroup Γ) : Set Γ) :=
      mem_normalizer_commutator (Subgroup.le_normalizer hg) (hEV hg)
    exact mul_mem ((le_sup_left : (⁅E, V⁆ : Subgroup Γ) ≤ ⁅E, V⁆ ⊔ C₀)
      ((Subgroup.mem_normalizer_iff.mp hgN a).mp ha)) ((le_sup_right : C₀ ≤ ⁅E, V⁆ ⊔ C₀) hc)
  have hirr := pCoreOf_irred hE hchar (⁅E, V⁆ ⊔ C₀) le_sup_right (sup_le hVW hC₀W) hNn
  have hfac : ∀ w ∈ W, ∃ p ∈ (⁅E, V⁆ : Subgroup Γ), ∃ c ∈ C₀, w = p * c := by
    rcases hirr with h | h
    · exfalso
      apply hne
      have hle : (⁅E, V⁆ : Subgroup Γ) ≤ C₀ := le_sup_left.trans h.le
      have hodd : ∀ e ∈ E, Odd (orderOf e) → e ∈ Subgroup.centralizer (V : Set Γ) := by
        intro e he hodd
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hkp : ⁅e, v⁆ ∈ C₀ := hle (Subgroup.commutator_mem_commutator he hv)
        have := commute_of_odd_of_stab' (hW2.to_le hC₀W) hodd
          (fun w hw => Subgroup.mem_centralizer_iff.mp (hC₀c hw) e he) hkp
        calc v * e = (e * v * e⁻¹) * e := by rw [this]
          _ = e * v := by group
      have hEC : E ≤ Subgroup.centralizer (V : Set Γ) :=
        le_of_forall_odd_le (opResidual_eq_of_isBTBlock hE) hodd
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro e he v hv
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hEC he) v hv).symm
    · intro w hw
      have hw' : w ∈ (⁅E, V⁆ ⊔ C₀ : Subgroup Γ) := h ▸ hw
      obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup' hcomm hw'
      exact ⟨a, ha, c, hc, rfl⟩
  refine ⟨hVW, hfac, le_antisymm ?_ ?_⟩
  · intro k hk
    refine Subgroup.mem_inf.2 ⟨hk.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨p, hp, c, hc, rfl⟩ := hfac w hw
    have hpV : p ∈ V := commutator_le_of_le_normalizer hEV hp
    have h1 : p * k = k * p := Subgroup.mem_centralizer_iff.mp hk.2 p hpV
    have h2 : c * k = k * c := (Subgroup.mem_centralizer_iff.mp (hC₀c hc) k hk.1).symm
    calc p * c * k = p * (c * k) := by group
      _ = p * (k * c) := by rw [h2]
      _ = (p * k) * c := by group
      _ = (k * p) * c := by rw [h1]
      _ = k * (p * c) := by group
  · intro k hk
    have hkW : k ∈ W := hchar hk
    refine Subgroup.mem_inf.2 ⟨hk.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hWz := (six_four_a hG hT hE).2
    rw [blockW_eq_pCoreOf hE] at hWz
    have hkz : k ∈ Subgroup.centralizer (pCoreOf 2 G : Set Γ) :=
      (C1GN.omegaOneCenterOf_le_centerOf _ (hWz hkW)).2
    exact Subgroup.mem_centralizer_iff.mp hkz v (hVQ hv)

theorem isSLNatSection_autOn_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {n : ℕ} (hn : IsNaturalSLTwoModule ↥E n) {V : Subgroup Γ}
    (hV : IsElemAbelian 2 V) (hVQ : V ≤ pCoreOf 2 G)
    (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) (hne : ⁅E, V⁆ ≠ ⊥) :
    @IsSLNatSection ↥V (commGroupOfElemAbelian hV) (autOn E V) (commOn hV E)
      (commOn hV E ⊓ fixOn hV E) n := by
  obtain ⟨hVW, hfac, hker⟩ := bridge_data_of_isBTBlock hG hT hE hVQ hEV hne
  exact (@isSLNatSection_iff ↥V (commGroupOfElemAbelian hV) _ _ _ n).mpr
    (isNatSectionBy_autOn hV hEV (isNatSL_iff.mp (isNatSL_of_isBTBlock hG hT hE hn)) hVW hfac hker)

theorem isAltNatSection_autOn_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {m : ℕ} (hm : IsNaturalAltModule ↥E m) {V : Subgroup Γ}
    (hV : IsElemAbelian 2 V) (hVQ : V ≤ pCoreOf 2 G)
    (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) (hne : ⁅E, V⁆ ≠ ⊥) :
    @IsAltNatSection ↥V (commGroupOfElemAbelian hV) (autOn E V) (commOn hV E)
      (commOn hV E ⊓ fixOn hV E) (2 * m + 1) := by
  obtain ⟨hVW, hfac, hker⟩ := bridge_data_of_isBTBlock hG hT hE hVQ hEV hne
  exact (@isAltNatSection_iff ↥V (commGroupOfElemAbelian hV) _ _ _ (2 * m + 1)).mpr
    (isNatSectionBy_autOn hV hEV (isNatAlt_of_isBTBlock hG hT hE hm) hVW hfac hker)

omit [Finite Γ] in
theorem isElemAbelian_omegaOneCenter_pCoreOf (G : Subgroup Γ) :
    IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 G)) := by
  have hcomm : ∀ x ∈ omegaOneCenterOf (pCoreOf 2 G), ∀ y ∈ omegaOneCenterOf (pCoreOf 2 G),
      x * y = y * x := fun x hx y hy => by
    have h1 := C1GN.omegaOneCenterOf_le_centerOf _ hx
    exact (Subgroup.mem_centralizer_iff.mp h1.2 y (C1GN.omegaOneCenterOf_le_self _ hy)).symm
  refine isElemAbelian_of_forall' hcomm fun x hx => ?_
  unfold omegaOneCenterOf omegaOneOf at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => simp
  | mul x y hx hy hx2 hy2 =>
    have hxy : Commute x y := hcomm x hx y hy
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

omit [Finite Γ] in
theorem le_normalizer_omegaOneCenter_pCoreOf (G : Subgroup Γ) :
    G ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 G) : Set Γ) := fun g hg => by
  refine mem_normalizer_of_conjSub_eq ?_
  rw [← omegaOneCenterOf_conjSub, conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf_self' G hg)]

omit [Finite Γ] in
theorem omegaOneCenter_le_pCoreOf (G : Subgroup Γ) :
    omegaOneCenterOf (pCoreOf 2 G) ≤ pCoreOf 2 G := C1GN.omegaOneCenterOf_le_self _

theorem commutator_omegaOneCenter_eq (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) : ⁅E, omegaOneCenterOf (pCoreOf 2 G)⁆ = blockW E := by
  have hWV : blockW E ≤ omegaOneCenterOf (pCoreOf 2 G) := (six_four_a hG hT hE).2
  refine le_antisymm ?_ ?_
  · rw [blockW_eq_pCoreOf hE]
    exact (Subgroup.commutator_mono le_rfl (omegaOneCenter_le_pCoreOf G)).trans
      (commutator_pCoreOf_le hT hE)
  · calc blockW E = ⁅blockW E, E⁆ := by rw [blockW_eq_pCoreOf hE]; exact hE.perfect.symm
      _ ≤ ⁅omegaOneCenterOf (pCoreOf 2 G), E⁆ := Subgroup.commutator_mono hWV le_rfl
      _ = ⁅E, omegaOneCenterOf (pCoreOf 2 G)⁆ := Subgroup.commutator_comm _ _

theorem commutator_omegaOneCenter_ne_bot (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) : ⁅E, omegaOneCenterOf (pCoreOf 2 G)⁆ ≠ ⊥ := by
  rw [commutator_omegaOneCenter_eq hG hT hE, blockW_eq_pCoreOf hE]
  exact pCoreOf_ne_bot hE (charTwo_of_isBTBlock hG hT hE)

end BlockLevel

end CFSG.CGT.PushingUpLit.BHS6
