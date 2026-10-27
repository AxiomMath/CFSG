module

public import CFSG.LargeExtraspecial.S5Five
public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKCliff
public import CFSG.Quasithin.Background.HM22Out
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213C

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin.B45Mat.M22 CFSG.GH74.GLS.IVK
  CFSG.CharacterTheory.SteinbergBY
open scoped MonoidAlgebra

theorem isIrreducible_comp_of_surjective' {k : Type*} [Field k] {G H V : Type*} [Monoid G]
    [Monoid H] [AddCommGroup V] [Module k V] (ρ : Representation k H V) (f : G →* H)
    (hf : Function.Surjective f) (hirr : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f) := by
  let : Representation.IsIrreducible ρ := hirr
  have hbot : (⊥ : Subrepresentation (ρ.comp f)) ≠ ⊤ := by
    intro heq
    have hsub : (⊥ : Submodule k V) = ⊤ := congrArg Subrepresentation.toSubmodule heq
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ)
    exact Subrepresentation.toSubmodule_injective hsub
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, ?_⟩
  intro U
  let U' : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        obtain ⟨g, rfl⟩ := hf h
        exact U.apply_mem_toSubmodule g hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top U' with hb | ht
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation ρ => S.toSubmodule) hb)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht)

theorem m22_irreducible_dim
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G22 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W ≤ 33) :
    (finrank (ZMod 2) W = 1 ∧ ∀ g, τ g = 1) ∨ finrank (ZMod 2) W = 10 := by
  rcases m22_binary_cases W τ hτ hW with he | he | he
  · obtain ⟨e⟩ := he
    left
    refine ⟨?_, fun g => ?_⟩
    · rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    · refine LinearMap.ext fun w => ?_
      have h := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w
      have h3 : rep1 g = 1 := rfl
      rw [matrixBaseChange_apply, h3, RingHom.coe_id, Matrix.map_id, Matrix.one_mulVec,
        Representation.Equiv.coe_toIntertwiningMap] at h
      exact e.injective h
  · obtain ⟨e⟩ := he
    right
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  · obtain ⟨e⟩ := he
    right
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]

theorem false_of_irreducible_twelve
    {H : Type} [Group H] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    (hρ : ρ.IsIrreducible) (hinj : Function.Injective ρ) (K : Subgroup H) [K.Normal]
    (e : G22 ≃* K) (hd : finrank (ZMod 2) V = 12) : False := by
  have hcard : Nat.card G22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  have hKne : Nontrivial K := by
    have : Nontrivial G22 := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    exact e.toEquiv.nontrivial_congr.mp this
  have hKinj : Function.Injective (resRep ρ K) := hinj.comp K.subtype_injective
  have hmin : ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
      (σ : Representation (ZMod 2) ↥K W), IsSimpleModule (ZMod 2)[↥K] σ.asModule →
      (∃ x, σ x ≠ 1) → 10 ≤ finrank (ZMod 2) W := by
    intro W _ _ _ σ hσ ⟨x, hx⟩
    have hirr : σ.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr hσ
    by_cases hW : finrank (ZMod 2) W ≤ 33
    · have hτ := isIrreducible_comp_of_surjective' σ e.toMonoidHom e.surjective hirr
      rcases m22_irreducible_dim (σ.comp e.toMonoidHom) hτ hW with ⟨-, htriv⟩ | h10
      · exfalso
        apply hx
        have := htriv (e.symm x)
        simpa using this
      · omega
    · omega
  have hsimple := CFSG.GH74.GLS.Stage4.Rest.Mix11cK.clifford_core ρ
    ((Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ) K hKinj hKne hmin
    (m := 10) (by omega)
  have hτ := isIrreducible_comp_of_surjective' (resRep ρ K) e.toMonoidHom e.surjective
    ((Representation.irreducible_iff_isSimpleModule_asModule _).mpr hsimple)
  rcases m22_irreducible_dim _ hτ (by omega) with ⟨h1, -⟩ | h10 <;> omega

section Rep

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def mbarRep (S : Setting G) : Representation (ZMod 2) S.Mbar S.Qt :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (S.O.subtype.comp S.Mbar.subtype)

theorem mbarRep_injective (S : Setting G) : Function.Injective (mbarRep S) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => LinearMap.congr_fun h v))

theorem finrank_Qt_of_width_six (S : Setting G) (hw : S.width = 6) :
    finrank (ZMod 2) S.Qt = 12 := by
  rw [S.finrank_Qt_eq_two_mul_width, hw]

theorem irr_of_not_isReducible_aux (S : Setting G) (hirr : ¬ S.IsReducible) : S5.Irr S := by
  intro U hU
  by_contra h
  push Not at h
  exact hirr ⟨U, h.1, h.2, fun m v hv => hU _ ⟨m, rfl⟩ v hv⟩

theorem mbarRep_isIrreducible (S : Setting G) (hw : S.width = 6) (hirr : S5.Irr S) :
    (mbarRep S).IsIrreducible := by
  have hnt : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2)
    (by rw [finrank_Qt_of_width_six S hw]; norm_num)
  have hbot : (⊥ : Subrepresentation (mbarRep S)) ≠ ⊤ := fun h =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, fun U => ?_⟩
  rcases hirr U.toSubmodule (fun x hx u hu => U.apply_mem_toSubmodule ⟨x, hx⟩ hu) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end Rep

section Center

variable {G : Type} [Group G] [Finite G]

theorem center_timmesfeldLayer_normal (S : Setting G) :
    ((Subgroup.center (timmesfeldLayer S.Mbar)).map (timmesfeldLayer S.Mbar).subtype).Normal := by
  have hEn : (timmesfeldLayer S.Mbar).Normal := CFSG.ComponentClassification.Layer.normal S.Mbar
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hn
  refine ⟨⟨g * c * g⁻¹, hEn.conj_mem c c.2 g⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro e
  apply Subtype.ext
  have he' : g⁻¹ * (e : S.Mbar) * g ∈ timmesfeldLayer S.Mbar := by
    have := hEn.conj_mem (e : S.Mbar) e.2 g⁻¹
    simpa using this
  have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp (SetLike.mem_coe.mp hc) ⟨_, he'⟩)
  simp only [Subgroup.coe_mul] at hcomm ⊢
  calc (e : S.Mbar) * (g * c * g⁻¹) = g * ((g⁻¹ * (e : S.Mbar) * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * (e : S.Mbar) * g)) * g⁻¹ := by rw [hcomm]
    _ = g * c * g⁻¹ * e := by group

theorem card_center_layer_dvd_three (S : Setting G)
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3) :
    Nat.card (Subgroup.center (timmesfeldLayer S.Mbar)) ∣ 3 := by
  set Z := (Subgroup.center (timmesfeldLayer S.Mbar)).map (timmesfeldLayer S.Mbar).subtype
  have hZfit : Z ≤ timmesfeldFitting S.Mbar := by
    rw [timmesfeldFitting.eq_sSup]
    exact le_sSup ⟨center_timmesfeldLayer_normal S, inferInstance⟩
  have h1 : Nat.card Z = Nat.card (Subgroup.center (timmesfeldLayer S.Mbar)) :=
    Subgroup.card_map_of_injective (timmesfeldLayer S.Mbar).subtype_injective
  rw [← h1]
  exact (Subgroup.card_dvd_of_le (hZfit.trans (S5.fitting_le_oddCore S))).trans hodd

theorem card_center_layer_ne_one
    (S : Setting G) (hw : S.width = 6) (hirr : S5.Irr S)
    (hM : CFSG.Blueprint.NativeSporadic.IsSporadic
      (↥(timmesfeldLayer S.Mbar) ⧸ Subgroup.center ↥(timmesfeldLayer S.Mbar)) .M22) :
    Nat.card (Subgroup.center (timmesfeldLayer S.Mbar)) ≠ 1 := by
  intro h1
  have hEn : (timmesfeldLayer S.Mbar).Normal := CFSG.ComponentClassification.Layer.normal S.Mbar
  have hbot : Subgroup.center (timmesfeldLayer S.Mbar) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  obtain ⟨f⟩ := hM
  let e0 : (↥(timmesfeldLayer S.Mbar) ⧸ Subgroup.center ↥(timmesfeldLayer S.Mbar)) ≃*
      ↥(timmesfeldLayer S.Mbar) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  exact false_of_irreducible_twelve (mbarRep S) (mbarRep_isIrreducible S hw hirr)
    (mbarRep_injective S) (timmesfeldLayer S.Mbar) (f.symm.trans e0)
    (finrank_Qt_of_width_six S hw)

theorem card_center_layer_eq_three
    (S : Setting G) (hw : S.width = 6) (hirr : S5.Irr S)
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hM : CFSG.Blueprint.NativeSporadic.IsSporadic
      (↥(timmesfeldLayer S.Mbar) ⧸ Subgroup.center ↥(timmesfeldLayer S.Mbar)) .M22) :
    Nat.card (Subgroup.center (timmesfeldLayer S.Mbar)) = 3 :=
  ((Nat.dvd_prime Nat.prime_three).mp (card_center_layer_dvd_three S hodd)).resolve_left
    (card_center_layer_ne_one S hw hirr hM)

end Center

section Centralizer

@[expose] noncomputable def linMulAut (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    (V ≃ₗ[ZMod 2] V) →* MulAut (Multiplicative V) where
  toFun f := AddEquiv.toMultiplicative f.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem linMulAut_injective (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (linMulAut V) := by
  intro f g h
  refine LinearEquiv.ext fun v => ?_
  have := congrArg (fun φ : MulAut (Multiplicative V) => Multiplicative.toAdd
    (φ (Multiplicative.ofAdd v))) h
  exact this

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def mbarAut (S : Setting G) : S.Mbar →* MulAut (Multiplicative S.Qt) :=
  (linMulAut S.Qt).comp (S.O.subtype.comp S.Mbar.subtype)

theorem mbarAut_injective (S : Setting G) : Function.Injective (mbarAut S) :=
  (linMulAut_injective S.Qt).comp (Subtype.val_injective.comp Subtype.val_injective)

theorem centralizer_eq_center_of_width_six (hT12 : Quasithin.H13.KG82HatM22Twelve)
    (S : Setting G) (hw : S.width = 6) {E : Subgroup S.Mbar} (hq : CFSG.Open.IsQuasisimple ↥E)
    (hZ : Nat.card (Subgroup.center ↥E) = 3)
    (hM : Quasithin.IsSporadic .M22 (↥E ⧸ Subgroup.center ↥E)) :
    Subgroup.centralizer (E : Set S.Mbar) = (Subgroup.center ↥E).map E.subtype := by
  have hWc : Nat.card (Multiplicative S.Qt) = 2 ^ 12 := by
    have h1 : Nat.card (Multiplicative S.Qt) = Nat.card S.Qt :=
      Nat.card_congr Multiplicative.toAdd
    rw [h1, S.card_Qt, finrank_Qt_of_width_six S hw]
  have hW2 : ∀ w : Multiplicative S.Qt, w ^ 2 = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [sq, toAdd_mul, toAdd_one]
    exact ZModModule.add_self _
  have hρi : Function.Injective ((mbarAut S).comp E.subtype) :=
    (mbarAut_injective S).comp E.subtype_injective
  have hcen := hT12 ↥E hq hZ hM (Multiplicative S.Qt) hWc hW2 ((mbarAut S).comp E.subtype) hρi
  apply le_antisymm
  · intro d hd
    have h1 : mbarAut S d ∈ Subgroup.centralizer
        (((mbarAut S).comp E.subtype).range : Set (MulAut (Multiplicative S.Qt))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_iff.mp hd k k.2
    rw [hcen] at h1
    obtain ⟨k, hk, hkd⟩ := h1
    exact ⟨k, hk, mbarAut_injective S hkd⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk ⟨h, hh⟩)

end Centralizer

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem isAutTripleM22_of_M22_core
    (hT12 : Quasithin.H13.KG82HatM22Twelve) (hOut : Quasithin.H13.KG82HatM22Out)
    (S : Setting G) (hw : S.width = 6) (hirr : ¬ S.IsReducible)
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hM : CFSG.Blueprint.NativeSporadic.IsSporadic
      (↥(timmesfeldLayer S.Mbar) ⧸ Subgroup.center ↥(timmesfeldLayer S.Mbar)) .M22)
    (hout : ∃ x : S.Mbar, x ∉ timmesfeldLayer S.Mbar) :
    Quasithin.H13.J4.IsAutTripleM22 (S.M ⧸ CFSG.pCore 2 S.M) := by
  have hEn : (timmesfeldLayer S.Mbar).Normal := CFSG.ComponentClassification.Layer.normal S.Mbar
  have hZ := card_center_layer_eq_three S hw (irr_of_not_isReducible_aux S hirr) hodd hM
  have hCK := centralizer_eq_center_of_width_six hT12 S hw hq hZ hM
  have h2 := Quasithin.H13.card_le_two_mul_82 (timmesfeldLayer S.Mbar) hq hZ hM hCK
  have hX : Nat.card S.Mbar = 2 * Nat.card (timmesfeldLayer S.Mbar) := by
    obtain ⟨x, hx⟩ := hout
    have hc := (timmesfeldLayer S.Mbar).card_mul_index
    have hpos : 0 < Nat.card (timmesfeldLayer S.Mbar) := Nat.card_pos
    have hne1 : (timmesfeldLayer S.Mbar).index ≠ 1 := fun h =>
      hx (by rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top x)
    have hne0 : (timmesfeldLayer S.Mbar).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : Nat.card (timmesfeldLayer S.Mbar) * (timmesfeldLayer S.Mbar).index ≤
        Nat.card (timmesfeldLayer S.Mbar) * 2 := by rw [hc]; omega
    have := Nat.le_of_mul_le_mul_left hle hpos
    have hidx : (timmesfeldLayer S.Mbar).index = 2 := by omega
    rw [← hc, hidx, mul_comm]
  exact (Quasithin.H13.isAutTripleM22_82 hOut (timmesfeldLayer S.Mbar) hq hZ hM hCK hX).of_mulEquiv
    (S.quotientEquivMbar.symm.trans (QuotientGroup.quotientMulEquivOfEq S.Q_eq_pCore))

theorem isAutTripleM22_of_M22
    (S : Setting G) (hw : S.width = 6) (hirr : ¬ S.IsReducible)
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hq : CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar))
    (hM : CFSG.Blueprint.NativeSporadic.IsSporadic
      (↥(timmesfeldLayer S.Mbar) ⧸ Subgroup.center ↥(timmesfeldLayer S.Mbar)) .M22)
    (hout : ∃ x : S.Mbar, x ∉ timmesfeldLayer S.Mbar) :
    Quasithin.H13.J4.IsAutTripleM22 (S.M ⧸ CFSG.pCore 2 S.M) :=
  isAutTripleM22_of_M22_core CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Twelve_holds
    CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Out_holds S hw hirr hodd hq hM hout

end Assembly

end CFSG.GF2Type.Smith1979
