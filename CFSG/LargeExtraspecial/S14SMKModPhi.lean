module

public import CFSG.LargeExtraspecial.S14SMKGramDefs
public import CFSG.LargeExtraspecial.S14SMKGramPhi
public import CFSG.LargeExtraspecial.S14SMKModCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20 QuadraticMap

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

theorem rhoMod_injective :
    Function.Injective (rhoMod : T46 →* (V ≃ₗ[ZMod 2] V)) := by
  have := isSimpleGroup_T46
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal rhoMod.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    obtain ⟨v, hli, hv, -⟩ := exists_qaBasis (i := 0) (by norm_num)
    obtain ⟨p, -, k, -, hvs⟩ := hv 0
    have h1 : rhoMod ⟨tvP p, tvP_mem p⟩ = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
    rw [rhoMod_tvP] at h1
    have h2 := hli.ne_zero 0
    rw [hvs, h1] at h2
    exact h2 (CharTwo.add_self_eq_zero _)

@[expose] noncomputable def PhiB (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V) :
    S.Mbar →* (V ≃ₗ[ZMod 2] V) :=
  (PhiO S φ).comp S.Mbar.subtype

theorem PhiB_injective (φ : S.Qt ≃ₗ[ZMod 2] V) : Function.Injective (PhiB S φ) :=
  (PhiO_injective φ).comp Subtype.val_injective

theorem PhiB_rhoM (φ : S.Qt ≃ₗ[ZMod 2] V) (m : S.M) : PhiB S φ (rhoM S m) = Phi S φ m := rfl

section Equiv

variable
  {φ : S.Qt ≃ₗ[ZMod 2] V}

theorem range_rhoMod_le (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    rhoMod.range ≤ (PhiB S φ).range := by
  have H : ∀ x ∈ Subgroup.closure (Set.range tvP), ∀ hx : x ∈ T46,
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
      rw [show (⟨1, h⟩ : T46) = 1 from rfl, map_one]
      exact (PhiB S φ).range.one_mem
    | mul x y hx hy ihx ihy =>
      intro h
      have hxT : x ∈ T46 := T46_eq_closure ▸ hx
      have hyT : y ∈ T46 := T46_eq_closure ▸ hy
      rw [show (⟨x * y, h⟩ : T46) = ⟨x, hxT⟩ * ⟨y, hyT⟩ from rfl, map_mul]
      exact (PhiB S φ).range.mul_mem (ihx hxT) (ihy hyT)
    | inv x hx ihx =>
      intro h
      have hxT : x ∈ T46 := T46_eq_closure ▸ hx
      rw [show (⟨x⁻¹, h⟩ : T46) = (⟨x, hxT⟩ : T46)⁻¹ from rfl, map_inv]
      exact (PhiB S φ).range.inv_mem (ihx hxT)
  rintro _ ⟨t, rfl⟩
  exact H _ (T46_eq_closure ▸ t.2) t.2

theorem card_comap_range_rhoMod (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    Nat.card (rhoMod.range.comap (PhiB S φ)) = Nat.card T46 := by
  have e1 := Subgroup.card_map_of_injective (K := rhoMod.range.comap (PhiB S φ))
    (PhiB_injective φ)
  rw [Subgroup.map_comap_eq_self (range_rhoMod_le h5)] at e1
  rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective (f := rhoMod) rhoMod_injective).toEquiv]

theorem exists_mem_Mbar0_of_clause5 (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) :
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
  have hidx := outU62Input S.Mbar (Mbar0 S) (timmesfeldFStar_normal _) hU hcent
  have h6 := Nat.le_of_dvd (by norm_num) hidx
  rw [card_comap_range_rhoMod h5, card_T46] at hle
  have : Nat.card (S.Mbar ⧸ Mbar0 S) = (Mbar0 S).index := rfl
  omega

theorem range_rhoMod_eq (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    rhoMod.range = (Mbar0 S).map (PhiB S φ) := by
  have hT := range_rhoMod_le h5
  set K : Subgroup T46 := ((Mbar0 S).map (PhiB S φ)).comap rhoMod with hKdef
  have hKn : K.Normal := ⟨fun x hx t => by
    obtain ⟨m, hm⟩ := hT ⟨t, rfl⟩
    obtain ⟨m₀, hm₀, hm₀x⟩ := hx
    refine ⟨m * m₀ * m⁻¹, (timmesfeldFStar_normal S.Mbar).conj_mem _ hm₀ m, ?_⟩
    rw [map_mul, map_mul, map_inv, hm, hm₀x, map_mul, map_mul, map_inv]⟩
  have := isSimpleGroup_T46
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
  rw [Nat.card_congr (e.trans tpsuT46).toEquiv]

theorem exists_equiv_of_clause5 (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    (h5 : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k) :
    ∃ ψ : Mbar0 S ≃* T46, ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S,
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
  {φ : S.Qt ≃ₗ[ZMod 2] V} {ψ : Mbar0 S ≃* T46}

theorem cl_eq_wtV_of_equiv (hw : S.width = 10)
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩)) {h : G}
    (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hbne : h * S.z * h⁻¹ ≠ S.z) :
    φ (S.cl (h * S.z * h⁻¹)) = wtV (planeOf S ψ h) := by
  have hfix : ∀ p ∈ planeSet (planeOf S ψ h), tvEquiv p.val (φ (S.cl (h * S.z * h⁻¹))) =
      φ (S.cl (h * S.z * h⁻¹)) := by
    intro p hp
    have hpU : tvP p ∈ UA (planeOf S ψ h).val :=
      tvP_mem_UA (by rw [wPlane_eq_planeSet (planeOf S ψ h).2]; exact hp)
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

end Cl

theorem exists_isModelPhi_of_clauses
    [IsSimpleGroup G]
    (I : Inputs10) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6))
    {φ : S.Qt ≃ₗ[ZMod 2] V} (hφ : SmithEClauses1235 S φ) :
    ∃ ψ : Mbar0 S ≃* T46, IsModelPhi S ψ φ ∧
      ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩) := by
  obtain ⟨-, h2, -, h5⟩ := hφ
  have h5' : ∀ k < 693, ∃ m : S.M, Phi S φ m = tvEquiv k := fun k hk => by
    obtain ⟨m, hm, hA⟩ := h5 k hk
    exact ⟨⟨m, hm⟩, (acts_iff hm hk).mp hA⟩
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_clause5 hU h5'
  obtain ⟨c, hc, hcQ, hcw⟩ := h2 0 (by norm_num)
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have hne : g * S.z * g⁻¹ ≠ S.z := by
    intro h
    rw [h, S.cl_z, map_zero] at hcw
    exact SMG.wt_ne_zero (show (0 : ℕ) < 891 by norm_num) (hcw.symm.trans (by decide))
  exact ⟨ψ, isModelPhi_of_equiv I hw hcQ hne hψ, hψ⟩

end CFSG.LargeExtraspecial.S14.SMK
