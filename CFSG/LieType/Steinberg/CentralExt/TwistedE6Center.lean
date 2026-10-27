module

public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus

public noncomputable section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.CentralExt.AdjointClosed
  CFSG.LieType.Chevalley.ExceptionalCover

section General

variable {k : Type} [Field k] (θ : k →+* k)

theorem mem_center_of_coe_mem_center {g : fixedGroup k θ}
    (hg : (g : e6Data_valid.minGroup k) ∈ Subgroup.center (e6Data_valid.minGroup k)) :
    g ∈ Subgroup.center (fixedGroup k θ) :=
  Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hg h)

theorem exists_minTorus_of_mem_center (hθ : ∀ c, θ (θ c) = c) {z : fixedGroup k θ}
    (hz : z ∈ Subgroup.center (fixedGroup k θ)) :
    ∃ u ∈ centerChars .E6 k, minTorus e6Data_valid k u = (z : e6Data_valid.minGroup k) := by
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have hext := twistedDatum_steinbergExtras θ hθ
  have hBU := twistedDatum_bruhatExtras θ
  have h1 := CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU
    ((CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU) ▸ hz)
  have h2 : (z : e6Data_valid.minGroup k) ∈ (⨆ i, hHat k θ i).map (fixedGroup k θ).subtype :=
    ⟨z, h1, rfl⟩
  rw [Subgroup.map_iSup] at h2
  have hle : (⨆ a, e6Data_valid.torus k a) ≤ (minTorus e6Data_valid k).range := by
    refine iSup_le fun a => ?_
    intro _ hx
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus k).1 hx
    exact ⟨Pi.mulSingle a t, minTorus_mulSingle e6Data_valid k a t⟩
  obtain ⟨u, hu⟩ : (z : e6Data_valid.minGroup k) ∈ (minTorus e6Data_valid k).range := by
    refine (iSup_le fun i => ?_ : (⨆ i, (hHat k θ i).map (fixedGroup k θ).subtype) ≤ _) h2
    rintro _ ⟨y, hy, rfl⟩
    exact hle (hHatE_le_iSup_torus θ i
      (show (y : e6Data_valid.minGroup k) ∈ hHatE k θ i from hy))
  refine ⟨u, Subgroup.mem_iInf.2 fun j => ?_, hu⟩
  rw [MonoidHom.mem_ker]
  have hconj : ∀ x : fixedGroup k θ, (z : e6Data_valid.minGroup k) * x = x * z := fun x =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz x).symm
  have hα : IsRoot .E6 (Pi.single j 1) := isRoot_single .E6 j
  have e1 := minTorus_conj_xm e6Data_valid k u hα 1
  rw [hu] at e1
  by_cases hfix : rho (Pi.single j 1) = Pi.single j 1
  ·
    have hx := hconj (xFixed θ hα hfix 1 (map_one θ))
    rw [xFixed_val] at hx
    have e2 : (z : e6Data_valid.minGroup k) * e6Data_valid.xm k (Pi.single j 1) 1 *
        (z : e6Data_valid.minGroup k)⁻¹ = e6Data_valid.xm k (Pi.single j 1) 1 := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hx
    have := e6Data_valid.xm_injective k hα (e1.symm.trans e2)
    exact Units.ext (by simpa using this)
  ·
    have e2 := minTorus_conj_xm e6Data_valid k u (isRoot_rho hα)
      ((twistSign (Pi.single j 1) : k) * θ 1)
    rw [hu] at e2
    have hx := hconj (xPair θ hθ hα hfix 1)
    rw [xPair_val] at hx
    have e3 : e6Data_valid.xm k (Pi.single j 1) (((rootChar k (Pi.single j 1) u : kˣ) : k) * 1) *
        e6Data_valid.xm k (rho (Pi.single j 1))
          (((rootChar k (rho (Pi.single j 1)) u : kˣ) : k) *
            ((twistSign (Pi.single j 1) : k) * θ 1)) =
        e6Data_valid.xm k (Pi.single j 1) 1 *
          e6Data_valid.xm k (rho (Pi.single j 1)) ((twistSign (Pi.single j 1) : k) * θ 1) := by
      rw [← e1, ← e2]
      calc _ = (z : e6Data_valid.minGroup k) * (e6Data_valid.xm k (Pi.single j 1) 1 *
            e6Data_valid.xm k (rho (Pi.single j 1))
              ((twistSign (Pi.single j 1) : k) * θ 1)) * (z : e6Data_valid.minGroup k)⁻¹ := by
            group
        _ = _ := by rw [mul_inv_eq_iff_eq_mul]; exact hx
    have := (xm_mul_xm_rho_inj hα hfix e3).1
    exact Units.ext (by simpa using this)

theorem coe_mem_center_of_mem_center (hθ : ∀ c, θ (θ c) = c) {z : fixedGroup k θ}
    (hz : z ∈ Subgroup.center (fixedGroup k θ)) :
    (z : e6Data_valid.minGroup k) ∈ Subgroup.center (e6Data_valid.minGroup k) := by
  obtain ⟨u, hu, e⟩ := exists_minTorus_of_mem_center θ hθ hz
  rw [← e]
  exact (minTorus_mem_center_iff e6Data_valid k u).2 hu

theorem center_fixedGroup_eq (hθ : ∀ c, θ (θ c) = c) :
    Subgroup.center (fixedGroup k θ) =
      (Subgroup.center (e6Data_valid.minGroup k)).subgroupOf (fixedGroup k θ) := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  exact ⟨coe_mem_center_of_mem_center θ hθ, mem_center_of_coe_mem_center θ⟩

theorem sigma_minTorus_tvec {v : kˣ} (hv : v ^ 3 = 1) :
    sigma k θ (minTorus e6Data_valid k (tvec v e6c)) =
      minTorus e6Data_valid k (tvec (Units.map (θ : k →* k) v)⁻¹ e6c) := by
  rw [sigma_minTorus]
  congr 1
  funext b
  have hw : Units.map (θ : k →* k) v ^ (3 : ℤ) = 1 := by
    rw [← map_zpow, zpow_ofNat, hv, map_one]
  obtain ⟨m, hm⟩ : (3 : ℤ) ∣ e6c (rhoPerm.symm b) + e6c b := by
    refine Int.dvd_of_emod_eq_zero ?_
    revert b
    decide
  change Units.map (θ : k →* k) (v ^ e6c (rhoPerm.symm b)) = (Units.map (θ : k →* k) v)⁻¹ ^ e6c b
  rw [map_zpow, show e6c (rhoPerm.symm b) = 3 * m - e6c b by omega, zpow_sub, zpow_mul, hw,
    one_zpow, one_mul, inv_zpow]

theorem minTorus_tvec_mem_fixedGroup_iff {v : kˣ} (hv : v ^ 3 = 1) :
    minTorus e6Data_valid k (tvec v e6c) ∈ fixedGroup k θ ↔ Units.map (θ : k →* k) v = v⁻¹ := by
  rw [mem_fixedGroup, sigma_minTorus_tvec θ hv, (minTorus_injective e6Data_valid k).eq_iff]
  refine ⟨fun h => ?_, fun h => by rw [h, inv_inv]⟩
  have h0 := congrFun h ⟨0, by decide⟩
  change (Units.map (θ : k →* k) v)⁻¹ ^ (1 : ℤ) = v ^ (1 : ℤ) at h0
  rw [zpow_one, zpow_one] at h0
  exact inv_eq_iff_eq_inv.1 h0

end General

section Finite

variable {k : Type} [Field k] {θ : k →+* k} {q : ℕ}

theorem mem_rootsOfUnity_gcd_iff (hθq : ∀ c, θ c = c ^ q) {v : kˣ} :
    v ∈ rootsOfUnity (Nat.gcd 3 (q + 1)) k ↔ v ^ 3 = 1 ∧ Units.map (θ : k →* k) v = v⁻¹ := by
  have hθv : Units.map (θ : k →* k) v = v ^ q :=
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hθq v)
  rw [mem_rootsOfUnity, pow_gcd_eq_one, hθv, eq_inv_iff_mul_eq_one, ← pow_succ]

variable (k) in
@[expose] def e6CenterTorus : kˣ →* e6Data_valid.minGroup k :=
  (minTorus e6Data_valid k).comp (MonoidHom.pi fun m => zpowGroupHom (e6c m))

@[expose] def centerHom (hθq : ∀ c, θ c = c ^ q) :
    rootsOfUnity (Nat.gcd 3 (q + 1)) k →* Subgroup.center (fixedGroup k θ) :=
  (((e6CenterTorus k).comp (rootsOfUnity _ k).subtype).codRestrict (fixedGroup k θ) fun v =>
    (minTorus_tvec_mem_fixedGroup_iff θ ((mem_rootsOfUnity_gcd_iff hθq).1 v.2).1).2
      ((mem_rootsOfUnity_gcd_iff hθq).1 v.2).2).codRestrict _ fun v =>
    mem_center_of_coe_mem_center θ ((minTorus_mem_center_iff e6Data_valid k _).2
      (tvec_mem_centerChars ((mem_rootsOfUnity_gcd_iff hθq).1 v.2).1 e6c_dvd))

theorem coe_centerHom (hθq : ∀ c, θ c = c ^ q) (v : rootsOfUnity (Nat.gcd 3 (q + 1)) k) :
    ((centerHom hθq v : fixedGroup k θ) : e6Data_valid.minGroup k) =
      minTorus e6Data_valid k (tvec (v : kˣ) e6c) :=
  rfl

theorem centerHom_injective (hθq : ∀ c, θ c = c ^ q) :
    Function.Injective (centerHom (k := k) hθq) := by
  intro v w h
  have h' : minTorus e6Data_valid k (tvec (v : kˣ) e6c) =
      minTorus e6Data_valid k (tvec (w : kˣ) e6c) := by
    rw [← coe_centerHom hθq v, ← coe_centerHom hθq w, h]
  have h0 := congrFun (minTorus_injective e6Data_valid k h') ⟨0, by decide⟩
  change (v : kˣ) ^ (1 : ℤ) = (w : kˣ) ^ (1 : ℤ) at h0
  rw [zpow_one, zpow_one] at h0
  exact Subtype.ext h0

theorem centerHom_surjective [Finite k] (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) :
    Function.Surjective (centerHom (k := k) hθq) := by
  rintro ⟨z, hz⟩
  obtain ⟨u, hu, e⟩ := exists_minTorus_of_mem_center θ (theta_theta_of_card hk hθq) hz
  have hu' : u = tvec (u ⟨0, by decide⟩) e6c :=
    funext fun m => eq_zpow_of_mem_centerChars e6C_spec hu m
  have hv3 : u ⟨0, by decide⟩ ^ 3 = 1 := pow_eq_one_of_mem_centerChars e6B_spec hu _
  have hfix : minTorus e6Data_valid k (tvec (u ⟨0, by decide⟩) e6c) ∈ fixedGroup k θ := by
    rw [← hu', e]
    exact z.2
  refine ⟨⟨u ⟨0, by decide⟩, (mem_rootsOfUnity_gcd_iff hθq).2
    ⟨hv3, (minTorus_tvec_mem_fixedGroup_iff θ hv3).1 hfix⟩⟩, Subtype.ext (Subtype.ext ?_)⟩
  rw [coe_centerHom, ← hu', e]

@[expose] def centerEquivRootsOfUnity [Finite k] (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) :
    Subgroup.center (fixedGroup k θ) ≃* rootsOfUnity (Nat.gcd 3 (q + 1)) k :=
  (MulEquiv.ofBijective (centerHom hθq)
    ⟨centerHom_injective hθq, centerHom_surjective hk hθq⟩).symm

theorem centerEquivRootsOfUnity_symm_apply [Finite k] (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) (v : rootsOfUnity (Nat.gcd 3 (q + 1)) k) :
    (centerEquivRootsOfUnity hk hθq).symm v = centerHom hθq v :=
  rfl

theorem card_center_fixedGroup [Finite k] (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) :
    Nat.card (Subgroup.center (fixedGroup k θ)) = Nat.gcd 3 (q + 1) ∧
      IsCyclic (Subgroup.center (fixedGroup k θ)) := by
  let e := centerEquivRootsOfUnity hk hθq
  have : NeZero (Nat.gcd 3 (q + 1)) := ⟨(Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'⟩
  have : Fintype k := Fintype.ofFinite k
  refine ⟨?_, isCyclic_of_surjective e.symm e.symm.surjective⟩
  rw [Nat.card_congr e.toEquiv, SLClosed.card_rootsOfUnity_eq_gcd, Fintype.card_eq_nat_card, hk]
  have h := Nat.sq_sub_sq q 1
  rw [one_pow] at h
  exact Nat.gcd_eq_left ((Nat.gcd_dvd_right 3 (q + 1)).trans ⟨q - 1, h⟩)

end Finite

section Isogeny

open CFSG.Blueprint CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Simplicity

variable {k : Type} [Field k] [Finite k] {θ : k →+* k}

theorem ker_twistedIsogeny_eq_center (hθ : ∀ c, θ (θ c) = c) (hK : 4 ≤ Nat.card k) :
    (twistedIsogeny θ hθ hK).ker = Subgroup.center (fixedGroup k θ) := by
  refine le_antisymm (fun g hg => ?_) (fun z hz => ?_)
  ·
    have h1 : (g : e6Data_valid.minGroup k) ∈ (e6IsogenyT k).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (congrArg (fun y : ↥⁅twistedFixedGroup .E6 k θ,
        twistedFixedGroup .E6 k θ⁆ => (y : ModGL TwistTag.E6.tag k)) ((MonoidHom.mem_ker).1 hg))
    exact mem_center_of_coe_mem_center θ (ker_e6IsogenyT_le_center k h1)
  ·
    have hzE := coe_mem_center_of_mem_center θ hθ hz
    have hc : e6IsogenyT k (z : e6Data_valid.minGroup k) ∈
        Subgroup.center (adjointGroup TwistTag.E6.tag k) :=
      Subgroup.mem_center_iff.2 fun a => by
        obtain ⟨g, rfl⟩ := e6IsogenyT_surjective (k := k) a
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzE g]
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    have h1 := congrArg Subtype.val hc
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h1

end Isogeny

end CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
