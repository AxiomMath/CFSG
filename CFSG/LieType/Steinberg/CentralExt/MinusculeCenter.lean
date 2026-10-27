module

public import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed CFSG.LieType.TitsSimplicity CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem

namespace CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section Chars

variable (τ : Tag) (k : Type) [Field k]

@[expose] def centerChars : Subgroup (Fin τ.rank → kˣ) :=
  ⨅ i : Fin τ.rank, (rootChar k (Pi.single i 1 : Fin τ.rank → ℤ)).ker

variable {τ k}

theorem rootChar_single (i : Fin τ.rank) (u : Fin τ.rank → kˣ) :
    rootChar k (Pi.single i 1 : Fin τ.rank → ℤ) u = ∏ j, u j ^ τ.cartan j i := by
  rw [rootChar_apply]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp [cartanCoord, Pi.single_apply]

theorem mem_centerChars {u : Fin τ.rank → kˣ} :
    u ∈ centerChars τ k ↔ ∀ i, ∏ j, u j ^ τ.cartan j i = 1 := by
  simp only [centerChars, Subgroup.mem_iInf, MonoidHom.mem_ker, rootChar_single]

theorem rootChar_eq_prod (γ : Fin τ.rank → ℤ) (u : Fin τ.rank → kˣ) :
    rootChar k γ u = ∏ i, rootChar k (Pi.single i 1 : Fin τ.rank → ℤ) u ^ γ i := by
  rw [rootChar_apply]
  simp only [rootChar_single]
  simp_rw [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun j _ => zpow_sum_eq_prod _ _ _

theorem rootChar_eq_one_of_mem {u : Fin τ.rank → kˣ} (hu : u ∈ centerChars τ k)
    (γ : Fin τ.rank → ℤ) : rootChar k γ u = 1 := by
  rw [rootChar_eq_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have h := (Subgroup.mem_iInf.1 hu) i
  rw [MonoidHom.mem_ker] at h
  rw [h, one_zpow]

theorem tvec_mem_centerChars {n : ℕ} {v : kˣ} (hv : v ^ n = 1) {s : Fin τ.rank → ℤ}
    (hs : ∀ i, (n : ℤ) ∣ ∑ j, s j * cartanCoord (Pi.single i 1 : Fin τ.rank → ℤ) j) :
    tvec v s ∈ centerChars τ k := by
  refine Subgroup.mem_iInf.2 fun i => ?_
  rw [MonoidHom.mem_ker, rootChar_tvec]
  obtain ⟨m, hm⟩ := hs i
  rw [hm, zpow_mul, zpow_natCast, hv, one_zpow]

theorem pow_eq_one_of_mem_centerChars {B : Fin τ.rank → Fin τ.rank → ℤ} {e : ℕ}
    (hB : ∀ a m : Fin τ.rank, ∑ i, τ.cartan a i * B i m = if a = m then (e : ℤ) else 0)
    {u : Fin τ.rank → kˣ} (hu : u ∈ centerChars τ k) (m : Fin τ.rank) : u m ^ e = 1 := by
  have h := mem_centerChars.1 hu
  have h1 : ∏ i, (∏ a, u a ^ τ.cartan a i) ^ B i m = 1 :=
    Finset.prod_eq_one fun i _ => by rw [h i, one_zpow]
  have h2 : ∏ i, (∏ a, u a ^ τ.cartan a i) ^ B i m = u m ^ (e : ℤ) := by
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp_rw [← zpow_sum_eq_prod, hB]
    rw [Finset.prod_eq_single m]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  rw [h2] at h1
  exact_mod_cast h1

theorem eq_zpow_of_mem_centerChars {C : Fin τ.rank → Fin τ.rank → ℤ} {c : Fin τ.rank → ℤ}
    {i₀ : Fin τ.rank}
    (hC : ∀ a m : Fin τ.rank,
      ∑ i, τ.cartan a i * C i m + (if a = i₀ then c m else 0) = if a = m then 1 else 0)
    {u : Fin τ.rank → kˣ} (hu : u ∈ centerChars τ k) (m : Fin τ.rank) : u m = u i₀ ^ c m := by
  have h := mem_centerChars.1 hu
  have h1 : ∏ i, (∏ a, u a ^ τ.cartan a i) ^ C i m = 1 :=
    Finset.prod_eq_one fun i _ => by rw [h i, one_zpow]
  have hC' : ∀ a, ∑ i, τ.cartan a i * C i m =
      (if a = m then 1 else 0) - (if a = i₀ then c m else 0) := fun a => by
    rw [← hC a m]
    ring
  have h2 : ∏ i, (∏ a, u a ^ τ.cartan a i) ^ C i m = u m * (u i₀ ^ c m)⁻¹ := by
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp_rw [← zpow_sum_eq_prod, hC', zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    · rw [Finset.prod_eq_single m (fun a _ ha => by rw [ite_eq_right ha, zpow_zero]) (by simp)]
      simp
    · rw [Finset.prod_eq_single i₀ (fun a _ ha => by rw [ite_eq_right ha, zpow_zero]) (by simp)]
      simp
  rw [h2, mul_inv_eq_one] at h1
  exact h1

end Chars

section Center

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

theorem endo_minTorus (u : Fin τ.rank → kˣ) :
    hV.endo k (minTorus hV k u) = diagOp fun a => ((∏ j, u j ^ D.wt a j : kˣ) : k) := by
  induction u using torusVec_induction with
  | h1 =>
    rw [map_one, hV.endo_one, ← diagOp_one]
    congr 1
    funext a
    simp
  | hmul t t' ht ht' =>
    rw [map_mul, hV.endo_mul, ht, ht', diagOp_mul]
    congr 1
    funext a
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]
  | hsingle j s =>
    rw [minTorus_mulSingle, hV.endo_hm, MinData.hDiag]
    congr 1
    funext a
    rw [Finset.prod_eq_single j (fun b _ hb => by rw [Pi.mulSingle_eq_of_ne hb, one_zpow])
      (by simp), Pi.mulSingle_eq_same]

theorem minTorus_injective : Function.Injective (minTorus hV k) := by
  intro u u' h
  have h' := congrArg (hV.endo k) h
  rw [endo_minTorus, endo_minTorus] at h'
  have hd := diagOp_injective h'
  funext i
  refine hV.charHom_eq_of_wt k (fun a => ?_) i
  have := congrFun hd a
  apply Additive.toMul.injective
  rw [MinData.Valid.charHom_apply, MinData.Valid.charHom_apply]
  exact Units.ext this

theorem minTorus_mem_center_iff (u : Fin τ.rank → kˣ) :
    minTorus hV k u ∈ Subgroup.center (hV.minGroup k) ↔ u ∈ centerChars τ k := by
  constructor
  · intro hz
    refine Subgroup.mem_iInf.2 fun i => ?_
    rw [MonoidHom.mem_ker]
    have hα : IsRoot τ (Pi.single i 1) := isRoot_single τ i
    have h1 : minTorus hV k u * hV.xm k (Pi.single i 1) 1 * (minTorus hV k u)⁻¹ =
        hV.xm k (Pi.single i 1) 1 := by
      rw [(Subgroup.mem_center_iff.1 hz _).symm, mul_inv_cancel_right]
    rw [minTorus_conj_xm hV k u hα, mul_one] at h1
    exact Units.ext (by rw [hV.xm_injective k hα h1, Units.val_one])
  · intro hu
    have hle : (⨆ γ ∈ {γ | IsRoot τ γ}, hV.rootGroup k γ) ≤
        Subgroup.centralizer {minTorus hV k u} := by
      refine iSup₂_le fun γ hγ => ?_
      intro g hg
      obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := minTorus_conj_xm hV k u hγ c
      rw [rootChar_eq_one_of_mem hu, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    rw [hV.iSup_rootGroup k] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := hle (Subgroup.mem_top g)
    rw [Subgroup.mem_centralizer_singleton_iff] at h3
    exact h3

theorem center_le_range_minTorus (hA : TauCeti.IsFiniteType τ.cartan)
    (hct : IsCTGroupDatum (coxeterMatrix (hV.minDatum hA k).isFiniteType).toCoxeterSystem
      (weylAction (hV.minDatum hA k).isFiniteType) (hV.minDatum hA k).roots
      (hV.minDatum hA k).rootGroup (hV.nm k) (hV.torus k))
    (hext : SteinbergExtras (hV.minDatum hA k) (hV.nm k) (hV.torus k))
    (hBU : BruhatExtras (hV.minDatum hA k) (hV.torus k)) :
    Subgroup.center (hV.minGroup k) ≤ (minTorus hV k).range := by
  intro z hz
  have h1 := (center_eq_normalCore_borel hct hext hBU) ▸ hz
  have h2 := normalCore_borel_le_iSup hct hBU h1
  have hle : (⨆ a, hV.torus k a) ≤ (minTorus hV k).range := by
    refine iSup_le fun a => ?_
    intro _ hx
    obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hx
    exact ⟨Pi.mulSingle a t, minTorus_mulSingle hV k a t⟩
  exact hle h2

noncomputable def centerEquiv (hA : TauCeti.IsFiniteType τ.cartan)
    (hct : IsCTGroupDatum (coxeterMatrix (hV.minDatum hA k).isFiniteType).toCoxeterSystem
      (weylAction (hV.minDatum hA k).isFiniteType) (hV.minDatum hA k).roots
      (hV.minDatum hA k).rootGroup (hV.nm k) (hV.torus k))
    (hext : SteinbergExtras (hV.minDatum hA k) (hV.nm k) (hV.torus k))
    (hBU : BruhatExtras (hV.minDatum hA k) (hV.torus k)) :
    centerChars τ k ≃* Subgroup.center (hV.minGroup k) := by
  let f : centerChars τ k →* hV.minGroup k := (minTorus hV k).comp (centerChars τ k).subtype
  have hf : Function.Injective f := (minTorus_injective hV k).comp Subtype.val_injective
  have hrange : f.range = Subgroup.center (hV.minGroup k) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact (minTorus_mem_center_iff hV k u).2 u.2
    · intro hz
      obtain ⟨u, rfl⟩ := center_le_range_minTorus hV k hA hct hext hBU hz
      exact ⟨⟨u, (minTorus_mem_center_iff hV k u).1 hz⟩, rfl⟩
  exact (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)

end Center


section E6E7

@[expose] def e6C : Fin (Tag.rank .E6) → Fin (Tag.rank .E6) → ℤ :=
  ![![0, 1, -1, 2, 0, -2], ![0, 2, 0, 3, 1, -1], ![0, 2, 0, 4, 1, -2], ![0, 3, 0, 6, 2, -2],
    ![0, 2, 0, 4, 2, -1], ![0, 1, 0, 2, 1, 0]]

@[expose] def e6c : Fin (Tag.rank .E6) → ℤ := ![1, 0, 2, 0, 1, 2]

@[expose] def e6B : Fin (Tag.rank .E6) → Fin (Tag.rank .E6) → ℤ :=
  ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
    ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]

@[expose] def e7C : Fin (Tag.rank .E7) → Fin (Tag.rank .E7) → ℤ :=
  ![![2, 0, 3, 4, 1, 2, -1], ![2, 0, 4, 6, 1, 3, -2], ![3, 0, 6, 8, 2, 4, -2],
    ![4, 0, 8, 12, 3, 6, -3], ![3, 0, 6, 9, 3, 5, -2], ![2, 0, 4, 6, 2, 4, -1],
    ![1, 0, 2, 3, 1, 2, 0]]

@[expose] def e7c : Fin (Tag.rank .E7) → ℤ := ![0, 1, 0, 0, 1, 0, 1]

@[expose] def e7B : Fin (Tag.rank .E7) → Fin (Tag.rank .E7) → ℤ :=
  ![![4, 4, 6, 8, 6, 4, 2], ![4, 7, 8, 12, 9, 6, 3], ![6, 8, 12, 16, 12, 8, 4],
    ![8, 12, 16, 24, 18, 12, 6], ![6, 9, 12, 18, 15, 10, 5], ![4, 6, 8, 12, 10, 8, 4],
    ![2, 3, 4, 6, 5, 4, 3]]

theorem e6C_spec : ∀ a m : Fin (Tag.rank .E6), ∑ i, Tag.cartan .E6 a i * e6C i m +
    (if a = ⟨0, by decide⟩ then e6c m else 0) = if a = m then 1 else 0 := by decide

theorem e6B_spec : ∀ a m : Fin (Tag.rank .E6),
    ∑ i, Tag.cartan .E6 a i * e6B i m = if a = m then ((3 : ℕ) : ℤ) else 0 := by decide

theorem e6c_dvd : ∀ i : Fin (Tag.rank .E6),
    ((3 : ℕ) : ℤ) ∣ ∑ j, e6c j * cartanCoord (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) j := by
  intro i
  refine Int.dvd_of_emod_eq_zero ?_
  revert i
  decide

theorem e7C_spec : ∀ a m : Fin (Tag.rank .E7), ∑ i, Tag.cartan .E7 a i * e7C i m +
    (if a = ⟨1, by decide⟩ then e7c m else 0) = if a = m then 1 else 0 := by decide

theorem e7B_spec : ∀ a m : Fin (Tag.rank .E7),
    ∑ i, Tag.cartan .E7 a i * e7B i m = if a = m then ((2 : ℕ) : ℤ) else 0 := by decide

theorem e7c_dvd : ∀ i : Fin (Tag.rank .E7),
    ((2 : ℕ) : ℤ) ∣ ∑ j, e7c j * cartanCoord (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) j := by
  intro i
  refine Int.dvd_of_emod_eq_zero ?_
  revert i
  decide

variable (k : Type) [Field k]

noncomputable def e6CenterCharsEquiv : centerChars .E6 k ≃* rootsOfUnity 3 k := by
  let φ : centerChars .E6 k →* kˣ :=
    (Pi.evalMonoidHom (fun _ => kˣ) ⟨0, by decide⟩).comp (centerChars .E6 k).subtype
  have hφ : Function.Injective φ := by
    intro u u' h
    apply Subtype.ext
    funext m
    rw [eq_zpow_of_mem_centerChars e6C_spec u.2 m, eq_zpow_of_mem_centerChars e6C_spec u'.2 m]
    change u.1 _ = u'.1 _ at h
    rw [h]
  have hrange : φ.range = rootsOfUnity 3 k := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      rw [mem_rootsOfUnity]
      exact pow_eq_one_of_mem_centerChars e6B_spec u.2 _
    · intro hv
      rw [mem_rootsOfUnity] at hv
      refine ⟨⟨tvec v e6c, tvec_mem_centerChars hv e6c_dvd⟩, ?_⟩
      exact zpow_one v
  exact (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)

noncomputable def e7CenterCharsEquiv : centerChars .E7 k ≃* rootsOfUnity 2 k := by
  let φ : centerChars .E7 k →* kˣ :=
    (Pi.evalMonoidHom (fun _ => kˣ) ⟨1, by decide⟩).comp (centerChars .E7 k).subtype
  have hφ : Function.Injective φ := by
    intro u u' h
    apply Subtype.ext
    funext m
    rw [eq_zpow_of_mem_centerChars e7C_spec u.2 m, eq_zpow_of_mem_centerChars e7C_spec u'.2 m]
    change u.1 _ = u'.1 _ at h
    rw [h]
  have hrange : φ.range = rootsOfUnity 2 k := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      rw [mem_rootsOfUnity]
      exact pow_eq_one_of_mem_centerChars e7B_spec u.2 _
    · intro hv
      rw [mem_rootsOfUnity] at hv
      refine ⟨⟨tvec v e7c, tvec_mem_centerChars hv e7c_dvd⟩, ?_⟩
      exact zpow_one v
  exact (MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)

variable
  [Finite k]

theorem card_center_e6 :
    Nat.card (Subgroup.center (e6Data_valid.minGroup k)) = Nat.gcd 3 (Nat.card k - 1) ∧
      IsCyclic (Subgroup.center (e6Data_valid.minGroup k)) := by
  let e := (centerEquiv e6Data_valid k isFiniteType_cartan_E6 (e6Datum_isCTGroupDatum k)
    (e6Datum_steinbergExtras k) (e6Datum_bruhatExtras k)).symm.trans (e6CenterCharsEquiv k)
  have : Fintype k := Fintype.ofFinite k
  refine ⟨?_, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩
  rw [Nat.card_congr e.toEquiv, SLClosed.card_rootsOfUnity_eq_gcd, Fintype.card_eq_nat_card]

theorem card_center_e7 :
    Nat.card (Subgroup.center (e7Data_valid.minGroup k)) = Nat.gcd 2 (Nat.card k - 1) ∧
      IsCyclic (Subgroup.center (e7Data_valid.minGroup k)) := by
  let e := (centerEquiv e7Data_valid k isFiniteType_cartan_E7 (e7Datum_isCTGroupDatum k)
    (e7Datum_steinbergExtras k) (e7Datum_bruhatExtras k)).symm.trans (e7CenterCharsEquiv k)
  have : Fintype k := Fintype.ofFinite k
  refine ⟨?_, isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective⟩
  rw [Nat.card_congr e.toEquiv, SLClosed.card_rootsOfUnity_eq_gcd, Fintype.card_eq_nat_card]

end E6E7

end CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
