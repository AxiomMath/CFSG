module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixRadicalLabels
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeAffineOrbitAction

public noncomputable section

universe u

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight

open Subgroup Module Matrix MulAction SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise BinarySymThreeOrbit

@[expose] def glLin : GL (Fin 3) (ZMod 2) ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glLin_apply (D : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    glLin D v = (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := by
  rw [glLin, MulEquiv.trans_apply, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

section LinearPart

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem exists_affineLinearPart (k : affinePerms E) :
    ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, (k : Equiv.Perm E) v = (k : Equiv.Perm E) 0 + A v := by
  obtain ⟨a, A, h⟩ := k.2
  exact ⟨A, fun v => by rw [h, h, map_zero, add_zero]⟩

@[expose] def affineLinearPart (k : affinePerms E) : E ≃ₗ[ZMod 2] E :=
  (exists_affineLinearPart k).choose

theorem apply_eq_add_affineLinearPart (k : affinePerms E) (v : E) :
    (k : Equiv.Perm E) v = (k : Equiv.Perm E) 0 + affineLinearPart k v :=
  (exists_affineLinearPart k).choose_spec v

theorem affineLinearPart_apply (k : affinePerms E) (v : E) :
    affineLinearPart k v = (k : Equiv.Perm E) v - (k : Equiv.Perm E) 0 := by
  rw [apply_eq_add_affineLinearPart k v, add_sub_cancel_left]

@[expose] def affineLinearPartHom : affinePerms E →* (E ≃ₗ[ZMod 2] E) where
  toFun := affineLinearPart
  map_one' := LinearEquiv.ext fun v => by
    rw [affineLinearPart_apply]
    simp
  map_mul' k k' := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, affineLinearPart_apply, affineLinearPart_apply k',
      map_sub, affineLinearPart_apply k, affineLinearPart_apply k]
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
    abel

theorem affineLinearPartHom_apply (k : affinePerms E) (v : E) :
    affineLinearPartHom k v = (k : Equiv.Perm E) v - (k : Equiv.Perm E) 0 :=
  affineLinearPart_apply k v

end LinearPart

section Labels

variable {G : Type*} [Group G] {E : Type*} {M : Subgroup G} {z : G}

@[expose] def labelPerm (ℓ : E ≃ conjClass M z) : M →* Equiv.Perm E :=
  (Equiv.permCongrHom ℓ.symm).toMonoidHom.comp (toPermHom M (conjClass M z))

theorem labelPerm_apply (ℓ : E ≃ conjClass M z) (m : M) (v : E) :
    labelPerm ℓ m v = ℓ.symm (m • ℓ v) :=
  rfl

theorem coe_labelPerm (ℓ : E ≃ conjClass M z) (m : M) (v : E) :
    (ℓ (labelPerm ℓ m v) : G) = m * ℓ v * (m : G)⁻¹ := by
  rw [labelPerm_apply, Equiv.apply_symm_apply, coe_smul_conjClass]

theorem labelPerm_eq_iff (ℓ : E ≃ conjClass M z) {m : M} {v w : E} :
    labelPerm ℓ m v = w ↔ (m : G) * ℓ v * (m : G)⁻¹ = ℓ w := by
  rw [← coe_labelPerm, Subtype.coe_inj, ℓ.injective.eq_iff]

theorem ker_labelPerm (ℓ : E ≃ conjClass M z) :
    (labelPerm ℓ).ker = (toPermHom M (conjClass M z)).ker := by
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, labelPerm, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

end Labels

section Core

variable {G : Type*} [Group G] {M N₀ R : Subgroup G} {z : G}

theorem affine_structure_of_labels (ℓ : (Fin 3 → ZMod 2) ≃ conjClass M z)
    (hℓ0 : (ℓ 0 : G) = z) (hstab : M ⊓ centralizer ({z} : Set G) = N₀)
    (hker : (toPermHom M (conjClass M z)).ker = R.subgroupOf M) (hRN₀ : R ≤ N₀)
    (hMR : M ≤ normalizer (R : Set G)) (hR : Nat.card R = 128)
    (hlin : ∀ n ∈ N₀, ∃ A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
      ∀ v, n * (ℓ v : G) * n⁻¹ = ℓ (A v))
    (hsurj : ∀ A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), ∃ n ∈ N₀,
      ∀ v, n * (ℓ v : G) * n⁻¹ = ℓ (A v)) :
    (labelPerm ℓ).range = affinePerms (Fin 3 → ZMod 2) ∧
    (∀ k : Equiv.Perm (Fin 3 → ZMod 2), k ∈ (labelPerm ℓ).range ↔
      ∃ (a : Fin 3 → ZMod 2) (D : GL (Fin 3) (ZMod 2)),
        ∀ v, k v = a + (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ∧
    (labelPerm ℓ).ker = R.subgroupOf M ∧ (R.subgroupOf M).Normal ∧
    (∀ [(R.subgroupOf M).Normal], ∃ ι : M ⧸ R.subgroupOf M ≃* affinePerms (Fin 3 → ZMod 2),
      ∀ m : M, (ι (m : M ⧸ R.subgroupOf M) : Equiv.Perm (Fin 3 → ZMod 2)) = labelPerm ℓ m) ∧
    ∃ D : Subgroup G,
      D = ((translationPerms (Fin 3 → ZMod 2)).comap (labelPerm ℓ)).map M.subtype ∧
      D = CFSG.Assembly.pCoreOf 2 M ∧ Nat.card D = 1024 ∧ R ≤ D ∧ D ≤ M ∧
      (R.subgroupOf D).Normal ∧
      (∀ [(R.subgroupOf D).Normal], IsElementaryAbelian 2 (D ⧸ R.subgroupOf D) ∧
        Nat.card (D ⧸ R.subgroupOf D) = 8) ∧
      (D : Set G) * (N₀ : Set G) = M ∧ D ⊓ centralizer ({z} : Set G) = R ∧ D ⊓ N₀ = R ∧
      ∃ μ : M →* GL (Fin 3) (ZMod 2), Function.Surjective μ ∧ μ.ker = D.subgroupOf M ∧
        (∀ (m : M) (v : Fin 3 → ZMod 2), labelPerm ℓ m v =
          labelPerm ℓ m 0 + (μ m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ∧
        (D.subgroupOf M).Normal ∧
        ∀ [(D.subgroupOf M).Normal], ∃ κ : M ⧸ D.subgroupOf M ≃* GL (Fin 3) (ZMod 2),
          ∀ m : M, κ (m : M ⧸ D.subgroupOf M) = μ m := by
  classical
  set ρ := labelPerm ℓ with hρdef
  set K := ρ.range with hKdef
  have hN₀M : N₀ ≤ M := by rw [← hstab]; exact inf_le_left
  have hN₀C : N₀ ≤ centralizer ({z} : Set G) := by rw [← hstab]; exact inf_le_right
  have hRM : R ≤ M := hRN₀.trans hN₀M
  have hfix : ∀ m : M, ρ m 0 = 0 ↔ (m : G) ∈ N₀ := fun m => by
    rw [hρdef, labelPerm_eq_iff, hℓ0, ← hstab, mem_inf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
  have htrans : ∀ v w : Fin 3 → ZMod 2, ∃ k ∈ K, k v = w := fun v w => by
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (ℓ v) (ℓ w)
    exact ⟨ρ m, ⟨m, rfl⟩, by rw [hρdef, labelPerm_apply, hm, Equiv.symm_apply_apply]⟩
  have hstabK : K ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3 → ZMod 2)) (0 : Fin 3 → ZMod 2) =
      linearPerms (Fin 3 → ZMod 2) := by
    ext k
    rw [mem_inf, MonoidHom.mem_range, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    constructor
    · rintro ⟨⟨m, rfl⟩, h0⟩
      obtain ⟨A, hA⟩ := hlin m ((hfix m).1 h0)
      exact ⟨A, fun v => (labelPerm_eq_iff ℓ).2 (hA v)⟩
    · rintro ⟨A, hA⟩
      obtain ⟨n, hn, hnA⟩ := hsurj A
      refine ⟨⟨⟨n, hN₀M hn⟩, Equiv.ext fun v => ?_⟩, by rw [hA, map_zero]⟩
      rw [hA]
      exact (labelPerm_eq_iff ℓ).2 (hnA v)
  obtain ⟨hKaff, hTK, -, hTcomm, hTsq, hTcard, hTn, -, hTmax, -, -, -, -⟩ :=
    binary_affine_eight_full_linear_point_stabilizer (Module.finrank_fin_fun (ZMod 2)) K htrans
      hstabK
  have hkerρ : ρ.ker = R.subgroupOf M := (ker_labelPerm ℓ).trans hker
  have hRnM : (R.subgroupOf M).Normal := ⟨fun r hr m => by
    rw [mem_subgroupOf] at hr ⊢
    simpa using (mem_normalizer_iff.1 (hMR m.2) r).1 hr⟩
  have hrange : ∀ k : Equiv.Perm (Fin 3 → ZMod 2), k ∈ K ↔
      ∃ (a : Fin 3 → ZMod 2) (D : GL (Fin 3) (ZMod 2)),
        ∀ v, k v = a + (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := fun k => by
    rw [hKaff]
    constructor
    · rintro ⟨a, A, hA⟩
      exact ⟨a, glLin.symm A, fun v => by rw [hA, ← glLin_apply, MulEquiv.apply_symm_apply]⟩
    · rintro ⟨a, D, hD⟩
      exact ⟨a, glLin D, fun v => by rw [hD, glLin_apply]⟩
  set C := (translationPerms (Fin 3 → ZMod 2)).comap ρ with hC
  set D := C.map M.subtype with hD
  have hDM : D ≤ M := map_subtype_le C
  have hmemD : ∀ g : G, g ∈ D ↔ ∃ h : g ∈ M, ρ ⟨g, h⟩ ∈ translationPerms (Fin 3 → ZMod 2) :=
    fun g => by
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m.2, hm⟩
      · rintro ⟨h, ht⟩
        exact ⟨⟨g, h⟩, ht, rfl⟩
  have hDsub : D.subgroupOf M = C := comap_map_eq_self_of_injective M.subtype_injective C
  have hRD : R ≤ D := fun r hr => (hmemD r).2 ⟨hRM hr, by
    have h1 : (⟨r, hRM hr⟩ : M) ∈ ρ.ker := by
      rw [hkerρ]
      exact mem_subgroupOf.2 hr
    rw [MonoidHom.mem_ker.1 h1]
    exact one_mem _⟩
  set ψ : D →* Equiv.Perm (Fin 3 → ZMod 2) := ρ.comp (inclusion hDM) with hψ
  have hψrange : ψ.range = translationPerms (Fin 3 → ZMod 2) := by
    ext t
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨_, ht⟩ := (hmemD d).1 d.2
      exact ht
    · intro ht
      obtain ⟨m, hm⟩ := hTK ht
      have hmD : (m : G) ∈ D := (hmemD m).2 ⟨m.2, by
        show ρ m ∈ _
        rw [hm]
        exact ht⟩
      exact ⟨⟨m, hmD⟩, hm⟩
  have hψker : ψ.ker = R.subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hkerρ,
      mem_subgroupOf]
    rfl
  have hidx : (R.subgroupOf D).index = 8 := by
    rw [← hψker, index_ker, hψrange, hTcard]
  have hcardD : Nat.card D = 1024 := by
    have h := (R.subgroupOf D).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hRD).toEquiv, hR, hidx] at h
    rw [← h]
  have hCcard : Nat.card C = 1024 := by
    rw [← hcardD, hD, card_map_of_injective M.subtype_injective]
  have hCnormal : C.Normal := ⟨fun c hc m => by
    rw [mem_comap] at hc ⊢
    have h := hTn.conj_mem ⟨ρ c, hTK hc⟩ (mem_subgroupOf.2 hc) ⟨ρ m, ⟨m, rfl⟩⟩
    rw [mem_subgroupOf] at h
    simpa using h⟩
  have hpcore : C = CFSG.Assembly.pCore 2 M := by
    apply le_antisymm
    · exact CFSG.Assembly.Dichotomy.CentralizerContainment.le_pCore_assembly hCnormal
        (IsPGroup.of_card (n := 10) (by rw [hCcard]; norm_num))
    · rw [← map_le_iff_le_comap]
      apply hTmax
      · rintro _ ⟨p, -, rfl⟩
        exact ⟨p, rfl⟩
      · refine ⟨fun x hx k => ?_⟩
        rw [mem_subgroupOf] at hx ⊢
        obtain ⟨p, hp, hpx⟩ := hx
        obtain ⟨m, hm⟩ := k.2
        refine ⟨m * p * m⁻¹,
          (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 M).conj_mem p
            hp m, ?_⟩
        simp only [map_mul, map_inv, hm, hpx, coe_mul, coe_inv]
      · exact (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 M).map ρ
  have hDpcore : D = CFSG.Assembly.pCoreOf 2 M := by
    rw [hD, hpcore]
    rfl
  have hRnD : (R.subgroupOf D).Normal := ⟨fun r hr d => by
    rw [mem_subgroupOf] at hr ⊢
    simpa using (mem_normalizer_iff.1 (hMR (hDM d.2)) r).1 hr⟩
  have helem : ∀ [(R.subgroupOf D).Normal], IsElementaryAbelian 2 (D ⧸ R.subgroupOf D) ∧
      Nat.card (D ⧸ R.subgroupOf D) = 8 := by
    intro inst
    have hmk : ∀ x y : D, ψ x = ψ y → (x : D ⧸ R.subgroupOf D) = y := fun x y h => by
      rw [QuotientGroup.eq, ← hψker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hψT : ∀ x : D, ψ x ∈ translationPerms (Fin 3 → ZMod 2) := fun x => hψrange ▸ ⟨x, rfl⟩
    have hcomm : IsMulCommutative (D ⧸ R.subgroupOf D) := ⟨⟨fun a c => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      apply hmk
      rw [map_mul, map_mul]
      exact hTcomm _ (hψT x) _ (hψT y)⟩⟩
    refine ⟨{ exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_ }, hidx⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    apply hmk
    rw [map_pow, pow_two, map_one]
    exact hTsq _ (hψT x)
  have hDN : (D : Set G) * (N₀ : Set G) = M := by
    ext g
    rw [Set.mem_mul]
    constructor
    · rintro ⟨d, hd, n, hn, rfl⟩
      exact M.mul_mem (hDM hd) (hN₀M hn)
    · intro hg
      obtain ⟨m, hm⟩ := hTK (⟨ρ ⟨g, hg⟩ 0, fun v => rfl⟩ :
        Equiv.addLeft (ρ ⟨g, hg⟩ 0) ∈ translationPerms (Fin 3 → ZMod 2))
      have hmD : (m : G) ∈ D := (hmemD m).2 ⟨m.2, by
        show ρ m ∈ _
        rw [hm]
        exact ⟨ρ ⟨g, hg⟩ 0, fun v => rfl⟩⟩
      refine ⟨m, hmD, (m : G)⁻¹ * g, ?_, by group⟩
      have h0 : ρ (m⁻¹ * ⟨g, hg⟩) 0 = 0 := by
        rw [map_mul, map_inv, Equiv.Perm.mul_apply, hm, Equiv.Perm.inv_def,
          Equiv.symm_apply_eq]
        exact (add_zero _).symm
      exact (hfix _).1 h0
  have hDH : D ⊓ centralizer ({z} : Set G) = R := by
    apply le_antisymm
    · rintro g ⟨hgD, hgC⟩
      obtain ⟨hgM, a, ha⟩ := (hmemD g).1 hgD
      have hgN₀ : g ∈ N₀ := by
        rw [← hstab]
        exact mem_inf.2 ⟨hgM, hgC⟩
      have h0 : ρ ⟨g, hgM⟩ 0 = 0 := (hfix ⟨g, hgM⟩).2 hgN₀
      have ha0 : a = 0 := by
        have h := ha 0
        rw [h0, add_zero] at h
        exact h.symm
      have h1 : ρ ⟨g, hgM⟩ = 1 := Equiv.ext fun v => by
        rw [ha, ha0, zero_add]
        rfl
      have h2 : (⟨g, hgM⟩ : M) ∈ R.subgroupOf M := hkerρ ▸ MonoidHom.mem_ker.2 h1
      exact mem_subgroupOf.1 h2
    · exact le_inf hRD (hRN₀.trans hN₀C)
  have hDN₀ : D ⊓ N₀ = R :=
    le_antisymm (fun g hg => hDH ▸ mem_inf.2 ⟨(mem_inf.1 hg).1, hN₀C (mem_inf.1 hg).2⟩)
      (le_inf hRD hRN₀)
  have hKaffmem : ∀ m : M, ρ m ∈ affinePerms (Fin 3 → ZMod 2) := fun m => hKaff ▸ ⟨m, rfl⟩
  set ρ' : M →* affinePerms (Fin 3 → ZMod 2) := ρ.codRestrict _ hKaffmem with hρ'
  set μ : M →* GL (Fin 3) (ZMod 2) :=
    (glLin.symm.toMonoidHom.comp affineLinearPartHom).comp ρ' with hμdef
  have hμ : ∀ (m : M) (v : Fin 3 → ZMod 2), glLin (μ m) v = ρ m v - ρ m 0 := fun m v => by
    rw [hμdef, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, affineLinearPartHom_apply]
    rfl
  have hμ' : ∀ (m : M) (v : Fin 3 → ZMod 2),
      ρ m v = ρ m 0 + (μ m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := fun m v => by
    rw [← glLin_apply, hμ]
    abel
  have hμker : μ.ker = D.subgroupOf M := by
    rw [hDsub]
    ext m
    rw [MonoidHom.mem_ker, mem_comap]
    constructor
    · intro h1
      refine ⟨ρ m 0, fun v => ?_⟩
      rw [hμ' m v, h1, Units.val_one, one_mulVec]
    · rintro ⟨a, ha⟩
      apply glLin.injective
      apply LinearEquiv.ext
      intro v
      rw [hμ, map_one, ha, ha, add_zero, add_sub_cancel_left]
      rfl
  have hμsurj : Function.Surjective μ := fun D₀ => by
    have hmem : (glLin D₀).toEquiv ∈ K := by
      have h : (glLin D₀).toEquiv ∈ linearPerms (Fin 3 → ZMod 2) := ⟨glLin D₀, fun v => rfl⟩
      rw [← hstabK] at h
      exact (mem_inf.1 h).1
    obtain ⟨m, hm⟩ := hmem
    refine ⟨m, glLin.injective (LinearEquiv.ext fun v => ?_)⟩
    rw [hμ, hm]
    simp
  have hρ'surj : Function.Surjective ρ' := fun k => by
    obtain ⟨m, hm⟩ : (k : Equiv.Perm (Fin 3 → ZMod 2)) ∈ K := by
      rw [hKaff]
      exact k.2
    exact ⟨m, Subtype.ext hm⟩
  have hρ'ker : ρ'.ker = R.subgroupOf M := by
    rw [← hkerρ]
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  refine ⟨hKaff, hrange, hkerρ, hRnM, fun {inst} => ⟨(QuotientGroup.quotientMulEquivOfEq
    hρ'ker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ρ' hρ'surj), fun m => rfl⟩,
    D, rfl, hDpcore, hcardD, hRD, hDM, hRnD, helem, hDN, hDH, hDN₀, μ, hμsurj, hμker, hμ',
    hDsub ▸ hCnormal, fun {inst} => ⟨(QuotientGroup.quotientMulEquivOfEq hμker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective μ hμsurj), fun m => rfl⟩⟩

end Core

@[expose] def altLabel (v : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨altMat v, mem_binarySymMatrices.2 (altMat_transpose v)⟩

theorem coe_altLabel (v : Fin 3 → ZMod 2) :
    (altLabel v : Matrix (Fin 3) (Fin 3) (ZMod 2)) = altMat v :=
  rfl

theorem altLabel_zero : altLabel 0 = 0 :=
  Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> rfl)

theorem altLabel_injective : Function.Injective altLabel := fun _ _ h =>
  altMat_injective (congrArg Subtype.val h)

theorem symThreeCongr_label (D : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    symThreeCongr D (BinarySymThreeOrbit.label v) =
      BinarySymThreeOrbit.label ((D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) :=
  Subtype.ext (by
    rw [coe_symThreeCongr, BinarySymThreeOrbit.coe_label, BinarySymThreeOrbit.coe_label,
      mul_vecMulVec_mul_transpose])

theorem symThreeCongr_altLabel (D : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    symThreeCongr D (altLabel v) =
      altLabel (((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ v) :=
  Subtype.ext (by rw [coe_symThreeCongr, coe_altLabel, coe_altLabel, mul_altMat_mul_transpose])

section Setting

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem rankOne_labels_injective :
    Function.Injective fun v : Fin 3 → ZMod 2 =>
      z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label v)) := fun _ _ h =>
  BinarySymThreeOrbit.label_injective
    (Multiplicative.ofAdd.injective (tauHom_injective φ he (mul_left_cancel h)))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem alt_labels_injective :
    Function.Injective fun v : Fin 3 → ZMod 2 =>
      z * tauHom φ he (Multiplicative.ofAdd (altLabel v)) := fun _ _ h =>
  altLabel_injective (Multiplicative.ofAdd.injective (tauHom_injective φ he (mul_left_cancel h)))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem range_rankOne_labels :
    Set.range (fun v : Fin 3 → ZMod 2 =>
      z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label v))) =
      {z} ∪ z • tauSet φ e (fun B => B.rank = 1) := by
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨v, rfl⟩
    by_cases hv : v = 0
    · left
      rw [hv, BinarySymThreeOrbit.label_zero, ofAdd_zero, map_one, mul_one]
    · right
      exact ⟨_, (mem_tauSet_iff φ he).2 ⟨Multiplicative.ofAdd (BinarySymThreeOrbit.label v),
        (sym_rank_one_iff (BinarySymThreeOrbit.label v)).2 ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨0, by rw [BinarySymThreeOrbit.label_zero, ofAdd_zero, map_one, mul_one]⟩
    · obtain ⟨B, hB, rfl⟩ := (mem_tauSet_iff φ he).1 ha
      obtain ⟨v, -, hv⟩ := (sym_rank_one_iff (Multiplicative.toAdd B)).1 hB
      refine ⟨v, ?_⟩
      have hBv : Multiplicative.ofAdd (BinarySymThreeOrbit.label v) = B :=
        Multiplicative.toAdd.injective (Subtype.ext hv.symm)
      rw [hBv]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem range_alt_labels :
    Set.range (fun v : Fin 3 → ZMod 2 => z * tauHom φ he (Multiplicative.ofAdd (altLabel v))) =
      {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) := by
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨v, rfl⟩
    by_cases hv : v = 0
    · left
      rw [hv, altLabel_zero, ofAdd_zero, map_one, mul_one]
    · right
      exact ⟨_, (mem_tauSet_iff φ he).2 ⟨Multiplicative.ofAdd (altLabel v),
        (sym_rank_two_alternating_iff (altLabel v)).2 ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨0, by rw [altLabel_zero, ofAdd_zero, map_one, mul_one]⟩
    · obtain ⟨B, hB, rfl⟩ := (mem_tauSet_iff φ he).1 ha
      obtain ⟨v, -, hv⟩ := (sym_rank_two_alternating_iff (Multiplicative.toAdd B)).1 hB
      refine ⟨v, ?_⟩
      have hBv : Multiplicative.ofAdd (altLabel v) = B :=
        Multiplicative.toAdd.injective (Subtype.ext hv.symm)
      rw [hBv]

include hzC hsup hinf hz hb hnd hV he in
theorem degree_eight_structure (M : Subgroup G) (hSM : 𝒮 ≤ M) (hMN : M ≤ 𝒩)
    (h8 : Nat.card (conjClass M z) = 8) :
    (conjClass M z = {z} ∪ z • tauSet φ e (fun B => B.rank = 1) ∨
      conjClass M z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)) ∧
    ∃ ℓ : (Fin 3 → ZMod 2) ≃ conjClass M z, (ℓ 0 : G) = z ∧
      ((conjClass M z = {z} ∪ z • tauSet φ e (fun B => B.rank = 1) ∧
          ∀ v, ∃ (a : G) (ha : a ∈ L), (ℓ v : G) = z * a ∧
            LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 (vecMulVec v v) 0 1) ∨
        (conjClass M z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) ∧
          ∀ v, ∃ (a : G) (ha : a ∈ L), (ℓ v : G) = z * a ∧
            LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 (altMat v) 0 1)) ∧
      ∃ ρ : M →* Equiv.Perm (Fin 3 → ZMod 2),
        (∀ (m : M) (v : Fin 3 → ZMod 2), (ℓ (ρ m v) : G) = m * ℓ v * (m : G)⁻¹) ∧
        ρ.range = affinePerms (Fin 3 → ZMod 2) ∧
        (∀ k : Equiv.Perm (Fin 3 → ZMod 2), k ∈ ρ.range ↔
          ∃ (a : Fin 3 → ZMod 2) (D : GL (Fin 3) (ZMod 2)),
            ∀ v, k v = a + (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ∧
        ρ.ker = (ℛ).subgroupOf M ∧ ((ℛ).subgroupOf M).Normal ∧
        (∀ [((ℛ).subgroupOf M).Normal],
          ∃ ι : M ⧸ (ℛ).subgroupOf M ≃* affinePerms (Fin 3 → ZMod 2),
            ∀ m : M, (ι (m : M ⧸ (ℛ).subgroupOf M) : Equiv.Perm (Fin 3 → ZMod 2)) = ρ m) ∧
        ∃ D : Subgroup G,
          D = ((translationPerms (Fin 3 → ZMod 2)).comap ρ).map M.subtype ∧
          D = CFSG.Assembly.pCoreOf 2 M ∧ Nat.card D = 1024 ∧ ℛ ≤ D ∧ D ≤ M ∧
          ((ℛ).subgroupOf D).Normal ∧
          (∀ [((ℛ).subgroupOf D).Normal], IsElementaryAbelian 2 (D ⧸ (ℛ).subgroupOf D) ∧
            Nat.card (D ⧸ (ℛ).subgroupOf D) = 8) ∧
          (D : Set G) * ((𝒮 : Subgroup G) : Set G) = M ∧
          D ⊓ centralizer ({z} : Set G) = ℛ ∧ D ⊓ 𝒮 = ℛ ∧
          ∃ μ : M →* GL (Fin 3) (ZMod 2), Function.Surjective μ ∧ μ.ker = D.subgroupOf M ∧
            (∀ (m : M) (v : Fin 3 → ZMod 2), ρ m v =
              ρ m 0 + (μ m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ∧
            (D.subgroupOf M).Normal ∧
            ∀ [(D.subgroupOf M).Normal], ∃ κ : M ⧸ D.subgroupOf M ≃* GL (Fin 3) (ZMod 2),
              ∀ m : M, κ (m : M ⧸ D.subgroupOf M) = μ m := by
  have hSM' : 𝒮 < M := by
    refine lt_of_le_of_ne hSM fun h => ?_
    have h1 : conjClass M z = {z} := by
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        rw [← h] at hm
        rw [Set.mem_singleton_iff, mem_centralizer_singleton_iff.1 (mem_inf.1 hm).2,
          mul_inv_cancel_right]
      · intro hx
        rw [Set.mem_singleton_iff.1 hx]
        exact self_mem_conjClass M z
    rw [h1, Nat.card_coe_set_eq, Set.ncard_singleton] at h8
    exact absurd h8 (by norm_num)
  have hcases :=
    (fusionOrbitPattern hzC hsup hinf hz hb hnd hV φ he hSM' hMN).2.2.2.2.2.2.2.2.1 h8
  have hker := ker_toPermHom_conjClass_eq hzC hsup hinf hz hb hnd hV φ he hSM' hMN
  have hstab := inf_centralizer_eq φ hSM hMN
  have hRS := radical_le_stab hzC hinf hz hb hnd hV φ he
  have hRc := (radical_facts hzC hinf hz hb hnd hV φ he).2.2
  obtain ⟨σ, hσs, -, -, hσ⟩ := exists_sigma hzC hsup hinf hb hnd hV φ he
  have hconj : ∀ (n : 𝒮) (B : binarySymMatrices 3),
      (n : G) * (z * tauHom φ he (Multiplicative.ofAdd B)) * (n : G)⁻¹ =
        z * tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ n) B)) := fun n B => by
    have hnz : (n : G) * z = z * n := mem_centralizer_singleton_iff.1 (mem_inf.1 n.2).2
    rw [← RadicalLabels.conj_tauHom_of_sigma φ he σ hσ n B]
    calc (n : G) * (z * tauHom φ he (Multiplicative.ofAdd B)) * (n : G)⁻¹ =
        ((n : G) * z) * tauHom φ he (Multiplicative.ofAdd B) * (n : G)⁻¹ := by group
      _ = z * ((n : G) * tauHom φ he (Multiplicative.ofAdd B) * (n : G)⁻¹) := by
        rw [hnz]
        group
  refine ⟨hcases, ?_⟩
  rcases hcases with h1 | h2
  ·
    let ℓ : (Fin 3 → ZMod 2) ≃ conjClass M z :=
      (Equiv.ofInjective _ (rankOne_labels_injective φ he)).trans
        (Set.equivOfEq ((range_rankOne_labels φ he).trans h1.symm))
    have hℓ : ∀ v, (ℓ v : G) =
        z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label v)) := fun v => rfl
    have hℓ0 : (ℓ 0 : G) = z := by
      rw [hℓ, BinarySymThreeOrbit.label_zero, ofAdd_zero, map_one, mul_one]
    have hact : ∀ (n : 𝒮) (v : Fin 3 → ZMod 2),
        (n : G) * ℓ v * (n : G)⁻¹ = ℓ ((σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) :=
      fun n v => by rw [hℓ, hℓ, hconj, symThreeCongr_label]
    have hlin : ∀ n ∈ 𝒮, ∃ A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
        ∀ v, n * (ℓ v : G) * n⁻¹ = ℓ (A v) := fun n hn =>
      ⟨glLin (σ ⟨n, hn⟩), fun v => by
        rw [glLin_apply]
        exact hact ⟨n, hn⟩ v⟩
    have hsurj : ∀ A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), ∃ n ∈ 𝒮,
        ∀ v, n * (ℓ v : G) * n⁻¹ = ℓ (A v) := fun A => by
      obtain ⟨n, hn⟩ := hσs (glLin.symm A)
      refine ⟨n, n.2, fun v => ?_⟩
      rw [hact n v, hn, ← glLin_apply, MulEquiv.apply_symm_apply]
    exact ⟨ℓ, hℓ0, Or.inl ⟨h1, fun v => ⟨_, tauHom_mem φ he _, hℓ v, toMatrix_tauHom φ he _⟩⟩,
      labelPerm ℓ, coe_labelPerm ℓ,
      affine_structure_of_labels ℓ hℓ0 hstab hker hRS hMN hRc hlin hsurj⟩
  ·
    let ℓ : (Fin 3 → ZMod 2) ≃ conjClass M z :=
      (Equiv.ofInjective _ (alt_labels_injective φ he)).trans
        (Set.equivOfEq ((range_alt_labels φ he).trans h2.symm))
    have hℓ : ∀ v, (ℓ v : G) = z * tauHom φ he (Multiplicative.ofAdd (altLabel v)) :=
      fun v => rfl
    have hℓ0 : (ℓ 0 : G) = z := by
      rw [hℓ, altLabel_zero, ofAdd_zero, map_one, mul_one]
    let tr : GL (Fin 3) (ZMod 2) → GL (Fin 3) (ZMod 2) := fun D =>
      nonsingInvUnit ((D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)
        (by rw [det_transpose, det_GL_three_eq_one]; exact isUnit_one)
    have htr : ∀ D, (tr D : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (D : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := fun D => rfl
    have hact : ∀ (n : 𝒮) (v : Fin 3 → ZMod 2), (n : G) * ℓ v * (n : G)⁻¹ =
        ℓ ((((σ n)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ v) :=
      fun n v => by rw [hℓ, hℓ, hconj, symThreeCongr_altLabel]
    have hlin : ∀ n ∈ 𝒮, ∃ A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
        ∀ v, n * (ℓ v : G) * n⁻¹ = ℓ (A v) := fun n hn =>
      ⟨glLin (tr (σ ⟨n, hn⟩)⁻¹), fun v => by
        rw [glLin_apply, htr]
        exact hact ⟨n, hn⟩ v⟩
    have hsurj : ∀ A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), ∃ n ∈ 𝒮,
        ∀ v, n * (ℓ v : G) * n⁻¹ = ℓ (A v) := fun A => by
      obtain ⟨n, hn⟩ := hσs (tr (glLin.symm A))⁻¹
      refine ⟨n, n.2, fun v => ?_⟩
      rw [hact n v, hn, inv_inv, htr, transpose_transpose, ← glLin_apply,
        MulEquiv.apply_symm_apply]
    exact ⟨ℓ, hℓ0, Or.inr ⟨h2, fun v => ⟨_, tauHom_mem φ he _, hℓ v, toMatrix_tauHom φ he _⟩⟩,
      labelPerm ℓ, coe_labelPerm ℓ,
      affine_structure_of_labels ℓ hℓ0 hstab hker hRS hMN hRc hlin hsurj⟩

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight

