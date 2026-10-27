module

public import CFSG.GF2Type.SmithTypeE.LMod.RhoFaith
public import CFSG.GF2Type.SmithTypeE.L6.Defs
public import CFSG.GF2Type.SmithTypeE.L6.IdGramPhi
public import CFSG.GF2Type.SmithTypeE.L6.IdModCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.LMod
open CFSG.LargeExtraspecial.SMod20 (V)
open CFSG.SmithL6 (wt)
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def PhiO (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V) :
    S.O →* (V ≃ₗ[ZMod 2] V) where
  toFun s := φ.symm.trans ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).trans φ)
  map_one' := by
    ext v
    simp
  map_mul' s t := by
    ext v
    simp only [Subgroup.coe_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

theorem PhiO_injective (φ : S.Qt ≃ₗ[ZMod 2] V) : Function.Injective (PhiO S φ) := by
  intro s t h
  apply Subtype.ext
  ext u
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => φ.symm (f (φ u))) h
  simpa [PhiO] using this

@[expose] noncomputable def PhiB (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V) :
    S.Mbar →* (V ≃ₗ[ZMod 2] V) :=
  (PhiO S φ).comp S.Mbar.subtype

theorem PhiB_injective (φ : S.Qt ≃ₗ[ZMod 2] V) : Function.Injective (PhiB S φ) :=
  (PhiO_injective φ).comp Subtype.val_injective

theorem PhiB_rhoM (φ : S.Qt ≃ₗ[ZMod 2] V) (m : S.M) : PhiB S φ (rhoM S m) = Phi S φ m := rfl

theorem isSimpleGroup_T6 : IsSimpleGroup T6 := by
  have : IsSimpleGroup PSL(6, ZMod 2) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 6 (by norm_num) (.inl (by norm_num))
      (.inl (by norm_num))
  exact pslT6.symm.isSimpleGroup

section Equiv

variable {φ : S.Qt ≃ₗ[ZMod 2] V}

theorem range_rhoMod_le (h5 : ∀ k < 1953, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    rhoMod.range ≤ (PhiB S φ).range := by
  have H : ∀ x ∈ Subgroup.closure (Set.range tvP), ∀ hx : x ∈ T6,
      rhoMod ⟨x, hx⟩ ∈ (PhiB S φ).range := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨k, rfl⟩ := hx'
      intro _
      obtain ⟨m, hm⟩ := h5 k k.2
      exact ⟨rhoM S m, by rw [PhiB_rhoM, hm, rhoMod_tvP]⟩
    | one =>
      intro h
      rw [show (⟨1, h⟩ : T6) = 1 from rfl, map_one]
      exact (PhiB S φ).range.one_mem
    | mul x y hx hy ihx ihy =>
      intro h
      have hxT : x ∈ T6 := hx
      have hyT : y ∈ T6 := hy
      rw [show (⟨x * y, h⟩ : T6) = ⟨x, hxT⟩ * ⟨y, hyT⟩ from rfl, map_mul]
      exact (PhiB S φ).range.mul_mem (ihx hxT) (ihy hyT)
    | inv x hx ihx =>
      intro h
      have hxT : x ∈ T6 := hx
      rw [show (⟨x⁻¹, h⟩ : T6) = (⟨x, hxT⟩ : T6)⁻¹ from rfl, map_inv]
      exact (PhiB S φ).range.inv_mem (ihx hxT)
  rintro _ ⟨t, rfl⟩
  exact H _ t.2 t.2

theorem card_comap_range_rhoMod (h5 : ∀ k < 1953, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    Nat.card (rhoMod.range.comap (PhiB S φ)) = Nat.card T6 := by
  have e1 := Subgroup.card_map_of_injective (K := rhoMod.range.comap (PhiB S φ))
    (PhiB_injective φ)
  rw [Subgroup.map_comap_eq_self (range_rhoMod_le h5)] at e1
  rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).toEquiv]

theorem exists_mem_Mbar0_of_clause5 (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    (h5 : ∀ k < 1953, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    ∃ x ∈ rhoMod.range.comap (PhiB S φ), x ∈ Mbar0 S ∧ x ≠ 1 := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  have : (Mbar0 S).Normal := timmesfeldFStar_normal _
  by_contra hno
  push Not at hno
  have hinj : Function.Injective
      ((QuotientGroup.mk' (Mbar0 S)).comp (rhoMod.range.comap (PhiB S φ)).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h1
    exact Subtype.ext (hno x hx ((QuotientGroup.eq_one_iff x).1 h1))
  have hle := Nat.card_le_card_of_injective _ hinj
  have hcent : centralizer (Mbar0 S : Set S.Mbar) ≤ Mbar0 S :=
    CFSG.Adapters.generalized_fitting_self_centralizing S.Mbar
  obtain ⟨e⟩ := hU
  have hidx := index_dvd_two_of_mulEquiv_psl (by norm_num) (Mbar0 S) e hcent
  have h2 := Nat.le_of_dvd (by norm_num) hidx
  have hcard : Nat.card T6 = 20158709760 := by
    rw [← Nat.card_congr pslT6.toEquiv, card_PSL_six_two]
  rw [card_comap_range_rhoMod h5, hcard] at hle
  have : Nat.card (S.Mbar ⧸ Mbar0 S) = (Mbar0 S).index := rfl
  omega

theorem range_rhoMod_eq (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    (h5 : ∀ k < 1953, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    rhoMod.range = (Mbar0 S).map (PhiB S φ) := by
  have hT := range_rhoMod_le h5
  set K : Subgroup T6 := ((Mbar0 S).map (PhiB S φ)).comap rhoMod with hKdef
  have hKn : K.Normal := ⟨fun x hx t => by
    obtain ⟨m, hm⟩ := hT ⟨t, rfl⟩
    obtain ⟨m₀, hm₀, hm₀x⟩ := hx
    refine ⟨m * m₀ * m⁻¹, (timmesfeldFStar_normal S.Mbar).conj_mem _ hm₀ m, ?_⟩
    rw [map_mul, map_mul, map_inv, hm, hm₀x, map_mul, map_mul, map_inv]⟩
  have := isSimpleGroup_T6
  have hle : rhoMod.range ≤ (Mbar0 S).map (PhiB S φ) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
    · exfalso
      obtain ⟨x, ⟨t, ht⟩, hx0, hx1⟩ := exists_mem_Mbar0_of_clause5 hU h5
      have htK : t ∈ K := ⟨x, hx0, ht.symm⟩
      rw [hK, Subgroup.mem_bot] at htK
      apply hx1
      apply PhiB_injective φ
      rw [← ht, htK, map_one, map_one]
    · rintro _ ⟨t, rfl⟩
      exact (hK ▸ Subgroup.mem_top t : t ∈ K)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) fun f g h => LinearEquiv.ext
      (congrFun h)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (PhiB_injective φ),
    ← Nat.card_congr (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).toEquiv]
  obtain ⟨e⟩ := hU
  rw [Nat.card_congr (e.trans pslT6).toEquiv]

theorem exists_equiv_of_clause5 (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    (h5 : ∀ k < 1953, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    ∃ ψ : Mbar0 S ≃* T6, ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S,
      Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩) := by
  have heq := range_rhoMod_eq hU h5
  refine ⟨((Mbar0 S).equivMapOfInjective (PhiB S φ) (PhiB_injective φ)).trans
    ((MulEquiv.subgroupCongr heq.symm).trans
      (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).symm), fun m h0 => ?_⟩
  have key : ∀ y : rhoMod.range,
      rhoMod ((MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).symm y) = y := fun y => by
    have := MonoidHom.ofInjective_apply rhoMod_injective
      (x := (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).symm y)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, key]
  rfl

end Equiv

section Cl

variable
  {φ : S.Qt ≃ₗ[ZMod 2] V} {ψ : Mbar0 S ≃* T6}

theorem cl_eq_wtV_of_equiv (hw : S.width = 10)
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩)) {h : G}
    (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hbne : h * S.z * h⁻¹ ≠ S.z) :
    φ (S.cl (h * S.z * h⁻¹)) = wtV (planeOf S ψ h) := by
  have hfix : ∀ p ∈ planeSet (planeOf S ψ h), tvEquiv p.val (φ (S.cl (h * S.z * h⁻¹))) =
      φ (S.cl (h * S.z * h⁻¹)) := by
    intro p hp
    have hpU : tvP p ∈ UA (planeOf S ψ h).val := tvP_mem_UA (Finset.mem_coe.2 hp)
    rw [← planeOf_spec ψ hw hbQ hbne] at hpU
    obtain ⟨ℓ, hℓL, hℓp⟩ := hpU
    have hℓL' : (ℓ : S.O) ∈ S.Lbar h := mem_subgroupOf.mp hℓL
    obtain ⟨m₀, hm₀, hm₀ℓ⟩ := Lbar_le_Mbar0 ψ hw hbQ hbne hℓL'
    obtain ⟨y, hyL, hyℓ⟩ := S.mem_Lbar_iff.mp hℓL'
    have hyM : rhoM S y = ℓ := Subtype.ext hyℓ
    have hℓ0 : ℓ ∈ Mbar0 S := by
      have : m₀ = ℓ := Subtype.ext hm₀ℓ
      exact this ▸ hm₀
    have hy0 : rhoM S y ∈ Mbar0 S := hyM ▸ hℓ0
    have hψy : ψ ⟨rhoM S y, hy0⟩ = ⟨tvP p, tvP_mem p⟩ := by
      apply Subtype.ext
      rw [← piM_of_mem]
      show piM S ψ (rhoM S y) = tvP p
      rw [hyM, hℓp]
    have hPhi : Phi S φ y = tvEquiv p := by rw [hψ y hy0, hψy, rhoMod_tvP]
    have hyb : (y : G) * (h * S.z * h⁻¹) * (y : G)⁻¹ = h * S.z * h⁻¹ := by
      have := (S.conjBy h).z_comm_QG hyL.1
      rw [Setting.conjBy_z] at this
      rw [this, mul_inv_cancel_right]
    rw [← hPhi, Phi_cl y hbQ, hyb]
  rcases (fixed_iff (planeOf S ψ h).2 _).1 hfix with h0 | h0
  · exact absurd ((map_eq_zero_iff φ φ.injective).1 h0) (S.cl_conj_z_ne_zero hbQ hbne)
  · exact h0

theorem isModelPhi_of_equiv [IsSimpleGroup G] (I : Inputs10)
    (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩)) :
    IsModelPhi S ψ φ := by
  intro i
  obtain ⟨h, hbQ, hbne, rfl⟩ := exists_planeOf_eq ψ hw haQ hne i
  rw [← cl_eq_xcl I ψ hw hbQ hbne]
  exact cl_eq_wtV_of_equiv hw hψ hbQ hbne

theorem exists_isModelPhi_of_clauses_Phi [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hφ : SmithL6Clauses1235 S φ) :
    ∃ ψ : Mbar0 S ≃* T6, IsModelPhi S ψ φ ∧
      ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩) := by
  obtain ⟨-, h2, -, h5⟩ := hφ
  have h5' : ∀ k < 1953, ∃ m : S.M, Phi S φ m = tvEquiv k := fun k hk => by
    obtain ⟨m, hm, hA⟩ := h5 k hk
    exact ⟨⟨m, hm⟩, (acts_iff hm hk).mp hA⟩
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_clause5 hU h5'
  obtain ⟨c, hc, hcQ, hcw⟩ := h2 0 (by norm_num)
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have hne : g * S.z * g⁻¹ ≠ S.z := by
    intro h
    rw [h, S.cl_z, map_zero] at hcw
    exact idWt_ne_zero (show (0 : ℕ) < 1395 by norm_num) (hcw.symm.trans (by decide))
  exact ⟨ψ, isModelPhi_of_equiv I hw hcQ hne hψ, hψ⟩

theorem cl_conj_eq_rhoMod_of_Phi
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (c : G) (hc : c ∈ S.M) (h0 : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) ∈ Mbar0 S) (u : G)
    (hu : u ∈ S.QG) :
    φ (S.cl (c * u * c⁻¹)) =
      rhoMod (ψ ⟨⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩, h0⟩) (φ (S.cl u)) := by
  rw [← Phi_cl ⟨c, hc⟩ hu, hψ ⟨c, hc⟩ h0]
  rfl

end Cl

end CFSG.GF2Type.SmithTypeE.L6
