module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTypeE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Type

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule


section Lists

theorem list_prod_sq_eq_one {M ι : Type*} [Monoid M] {l : List ι} (hl : l.Nodup) (f : ι → M)
    (hc : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute (f x) (f y)) (h2 : ∀ x ∈ l, f x ^ 2 = 1) :
    ((l.map f).prod) ^ 2 = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons]
    have hcm : Commute (f a) (l.map f).prod := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      exact hc a List.mem_cons_self b (List.mem_cons_of_mem _ hb) fun hab => hl.1 (hab ▸ hb)
    rw [hcm.mul_pow, h2 a List.mem_cons_self, ih hl.2
      (fun x hx y hy hxy => hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)), one_mul]

end Lists

section Uniq

variable {Ĝ G : Type*} [Group Ĝ] [Group G] [Finite Ĝ] {π : Ĝ →* G} {p : ℕ} [Fact p.Prime]

theorem IsCentralCover.eq_of_isPElt_of_map_eq (h : IsCentralCover π p) {x y : Ĝ}
    (hx : IsPElt p x) (hy : IsPElt p y) (hxy : π x = π y) : x = y := by
  have hP : IsPGroup p (Subgroup.zpowers (π x)) := by
    obtain ⟨k, hk⟩ := hx.map π
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨k, Subtype.ext ?_⟩
    show (π x ^ n) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hm := h.isPElt_mul hP (x := x⁻¹) (y := y)
    (by rw [map_inv]; exact inv_mem (Subgroup.mem_zpowers _))
    (by rw [← hxy]; exact Subgroup.mem_zpowers _) hx.inv hy
  have hker : x⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  exact inv_mul_eq_one.1 (h.eq_one_of_isPElt hker hm)

end Uniq

section Rank

variable {K : Type} [Field K]

variable (K) in
@[expose] def slMin (i : Fin (Tag.rank .E6)) : SL2 K →* ↥(e6Data_valid.minGroup K) :=
  (e6Data_valid.slHom K i).codRestrict _ (e6Data_valid.slHom_mem K i)

theorem slMin_upper (i : Fin (Tag.rank .E6)) (c : K) :
    slMin K i (uSL c) = e6Data_valid.xm K (Pi.single i 1) c :=
  e6Data_valid.endo_injective K (by
    rw [e6Data_valid.endo_xm]
    exact e6Data_valid.blockOp_upper K i c)

theorem slMin_lower (i : Fin (Tag.rank .E6)) (c : K) :
    slMin K i (vSL c) = e6Data_valid.xm K (-Pi.single i 1) c :=
  e6Data_valid.endo_injective K (by
    rw [e6Data_valid.endo_xm]
    exact e6Data_valid.blockOp_lower K i c)

theorem slMin_diag (i : Fin (Tag.rank .E6)) (t : Kˣ) :
    slMin K i (HSL t) = e6Data_valid.hm K i t :=
  e6Data_valid.endo_injective K (by
    rw [e6Data_valid.endo_hm]
    exact e6Data_valid.blockOp_diag K i t)

theorem slMin_weyl (i : Fin (Tag.rank .E6)) : slMin K i WSL = e6Data_valid.nm K i :=
  e6Data_valid.endo_injective K (by
    rw [e6Data_valid.endo_nm]
    exact e6Data_valid.blockOp_weyl K i)

end Rank

section Orbit

variable {K : Type} [Field K]

open CFSG.LieType.Steinberg.TwistedE6 (commute_rankOne_orbit nd slHom_mem_rankOne)

theorem orbit_pair_aux : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (i j : Fin TwistTag.E6.tag.rank),
    i ∈ TwistTag.E6.orbit a → j ∈ TwistTag.E6.orbit a → i ≠ j →
      (i.val = 2 ∧ j.val = 4) ∨ (i.val = 0 ∧ j.val = 5) ∨ (i.val = 4 ∧ j.val = 2) ∨
        (i.val = 5 ∧ j.val = 0) := by
  decide

theorem commute_slMin {a : Fin TwistTag.E6.foldedTag.rank} {i j : Fin TwistTag.E6.tag.rank}
    (hi : i ∈ TwistTag.E6.orbit a) (hj : j ∈ TwistTag.E6.orbit a) (hij : i ≠ j) (M N : SL2 K) :
    Commute (slMin K i M) (slMin K j N) := by
  rcases orbit_pair_aux a i j hi hj hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact commute_rankOne_orbit (Or.inl ⟨Fin.ext h1, Fin.ext h2⟩) (slHom_mem_rankOne i M)
      (slHom_mem_rankOne j N)
  · exact commute_rankOne_orbit (Or.inr ⟨Fin.ext h1, Fin.ext h2⟩) (slHom_mem_rankOne i M)
      (slHom_mem_rankOne j N)
  · exact (commute_rankOne_orbit (Or.inl ⟨Fin.ext h2, Fin.ext h1⟩) (slHom_mem_rankOne j N)
      (slHom_mem_rankOne i M)).symm
  · exact (commute_rankOne_orbit (Or.inr ⟨Fin.ext h2, Fin.ext h1⟩) (slHom_mem_rankOne j N)
      (slHom_mem_rankOne i M)).symm

variable (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)

@[expose] def minOrbitHom : SL2 (orbitField TwistTag.E6 K σ a) →* ↥(e6Data_valid.minGroup K) where
  toFun g := ((List.range (TwistTag.E6.orbit a).card).map fun k =>
    slMin K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
      (Matrix.SpecialLinearGroup.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype) g)).prod
  map_one' := by simp
  map_mul' g g' := by
    simp only [map_mul]
    refine list_prod_map_mul_of_commute_of_ne List.nodup_range _ _ fun k hk l hl hkl => ?_
    have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    refine commute_slMin (a := a) (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k)
      (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) l) (fun h => hkl ?_) _ _
    exact TwistTag.E6.injOn_pow_orbitMin a (Finset.mem_coe.2 (Finset.mem_range.2 hk'))
      (Finset.mem_coe.2 (Finset.mem_range.2 hl')) h

theorem minOrbitHom_apply (g : SL2 (orbitField TwistTag.E6 K σ a)) :
    minOrbitHom σ a g = ((List.range (TwistTag.E6.orbit a).card).map fun k =>
      slMin K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
        (Matrix.SpecialLinearGroup.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype)
          g)).prod := rfl

theorem minOrbitHom_uSL (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (uSL c) = ((List.range (TwistTag.E6.orbit a).card).map fun k =>
      e6Data_valid.xm K (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1)
        ((σ ^ k) (c : K))).prod := by
  rw [minOrbitHom_apply]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_uSL]
  exact slMin_upper _ _

theorem minOrbitHom_vSL (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (vSL c) = ((List.range (TwistTag.E6.orbit a).card).map fun k =>
      e6Data_valid.xm K (-Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1)
        ((σ ^ k) (c : K))).prod := by
  rw [minOrbitHom_apply]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_vSL]
  exact slMin_lower _ _

theorem minOrbitHom_HSL (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    minOrbitHom σ a (HSL u) = ((List.range (TwistTag.E6.orbit a).card).map fun k =>
      e6Data_valid.hm K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
        (Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom u)).prod := by
  rw [minOrbitHom_apply]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [map_HSL]
  exact slMin_diag _ _

theorem minOrbitHom_WSL :
    minOrbitHom σ a WSL = ((TwistTag.E6.orbitWord a).map (e6Data_valid.nm K)).prod := by
  rw [minOrbitHom_apply, TwistTag.E6.orbitWord_eq_map_range]
  refine congrArg List.prod ((List.map_congr_left fun k _ => ?_).trans (List.map_map).symm)
  rw [map_WSL]
  exact slMin_weyl _

end Orbit

section Compat

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K)
  (a : Fin TwistTag.E6.foldedTag.rank)

theorem xm_sq (γ : Fin (Tag.rank .E6) → ℤ) (c : K) : e6Data_valid.xm K γ c ^ 2 = 1 := by
  rw [pow_two, ← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]

theorem slMin_upper_sq (i : Fin (Tag.rank .E6)) (s : K) : slMin K i (uSL s) ^ 2 = 1 := by
  rw [slMin_upper]
  exact xm_sq _ _

theorem slMin_lower_sq (i : Fin (Tag.rank .E6)) (s : K) : slMin K i (vSL s) ^ 2 = 1 := by
  rw [slMin_lower]
  exact xm_sq _ _

theorem minOrbitHom_uSL_sq (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (uSL c) ^ 2 = 1 := by
  rw [minOrbitHom_apply]
  refine list_prod_sq_eq_one List.nodup_range _ (fun k hk l hl hkl => ?_) (fun k hk => ?_)
  · have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    refine commute_slMin (a := a) (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k)
      (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) l) (fun h => hkl ?_) _ _
    exact TwistTag.E6.injOn_pow_orbitMin a (Finset.mem_coe.2 (Finset.mem_range.2 hk'))
      (Finset.mem_coe.2 (Finset.mem_range.2 hl')) h
  · rw [map_uSL]
    exact slMin_upper_sq _ _

theorem minOrbitHom_vSL_sq (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (vSL c) ^ 2 = 1 := by
  rw [minOrbitHom_apply]
  refine list_prod_sq_eq_one List.nodup_range _ (fun k hk l hl hkl => ?_) (fun k hk => ?_)
  · have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    refine commute_slMin (a := a) (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k)
      (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) l) (fun h => hkl ?_) _ _
    exact TwistTag.E6.injOn_pow_orbitMin a (Finset.mem_coe.2 (Finset.mem_range.2 hk'))
      (Finset.mem_coe.2 (Finset.mem_range.2 hl')) h
  · rw [map_vSL]
    exact slMin_lower_sq _ _

theorem iso_minOrbitHom_uSL (c : orbitField TwistTag.E6 K σ a) :
    ((Isogeny.e6IsogenyT K (minOrbitHom σ a (uSL c)) : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) = (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) := by
  rw [minOrbitHom_uSL, coe_orbitX, map_list_prod, Subgroup.val_list_prod]
  refine congrArg List.prod ((List.map_map).trans ?_)
  rw [List.map_map]
  exact List.map_congr_left fun k _ => coe_e6IsogenyT_xm_single _ _

theorem iso_minOrbitHom_vSL (c : orbitField TwistTag.E6 K σ a) :
    ((Isogeny.e6IsogenyT K (minOrbitHom σ a (vSL c)) : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) = (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) := by
  rw [minOrbitHom_vSL, coe_orbitY, map_list_prod, Subgroup.val_list_prod]
  refine congrArg List.prod ((List.map_map).trans ?_)
  rw [List.map_map]
  exact List.map_congr_left fun k _ => coe_e6IsogenyT_xm_neg_single _ _

theorem iso_minOrbitHom_HSL (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    ((Isogeny.e6IsogenyT K (minOrbitHom σ a (HSL u)) : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) = (orbitH TwistTag.E6 K σ a u : ModGL TwistTag.E6.tag K) := by
  rw [minOrbitHom_HSL, coe_orbitH, map_list_prod, Subgroup.val_list_prod]
  refine congrArg List.prod ((List.map_map).trans ?_)
  rw [List.map_map]
  exact List.map_congr_left fun k _ => coe_e6IsogenyT_hm _ _

theorem canonMin_orbitReflection :
    canonMin K (TwistTag.E6.orbitReflection a) = minOrbitHom σ a WSL := by
  rw [minOrbitHom_WSL]
  have hred : (coxeterSystem TwistTag.E6.tag).IsReduced (TwistTag.E6.orbitWord a) := by
    rw [CoxeterSystem.IsReduced]
    exact (length_orbitReflection a).trans (TwistTag.E6.length_orbitWord a).symm
  exact canonMin_wordProd (ω := TwistTag.E6.orbitWord a) hred

end Compat

section Cover

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  (a : Fin TwistTag.E6.foldedTag.rank)

instance finite_fixedGroup_inst : Finite ↥(TwistedE6.fixedGroup K σ) := finite_fixedGroup σ

theorem uSL_zero' {F : Type*} [Field F] : (uSL (0 : F) : SL2 F) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem vSL_zero' {F : Type*} [Field F] : (vSL (0 : F) : SL2 F) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL]

include hf hK hσ in
theorem mem_fixedGroup_of_pLift {P : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hP : IsPGroup 2 P) {g : ↥(graphFixedRootGroup TwistTag.E6 K σ)} (hg : g ∈ P)
    {y : ↥(e6Data_valid.minGroup K)} (hy : IsPElt 2 y)
    (hyg : ((Isogeny.e6IsogenyT K y : ↥(adjointGroup TwistTag.E6.tag K)) :
      ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K)) :
    y ∈ TwistedE6.fixedGroup K σ := by
  obtain ⟨x, hx, hπ⟩ := exists_pLift (h := isCentralCover_coverHom hf hK σ hσ) (hP := hP) hg
  have hxe : IsPElt 2 (x : ↥(e6Data_valid.minGroup K)) := by
    obtain ⟨k, hk⟩ := hx.2
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxy : Isogeny.e6IsogenyT K y = Isogeny.e6IsogenyT K (x : ↥(e6Data_valid.minGroup K)) :=
    Subtype.ext (hyg.trans (by rw [← hπ]; exact (coe_coverHom hf hK σ hσ x).symm))
  have := (isCentralCover_e6IsogenyT (K := K)).eq_of_isPElt_of_map_eq hy hxe hxy
  rw [this]
  exact x.2

include hf hK hσ in
theorem minOrbitHom_uSL_mem (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (uSL c) ∈ TwistedE6.fixedGroup K σ := by
  have hD := twistedE6Datum hf hK σ hσ
  exact mem_fixedGroup_of_pLift hf hK σ hσ
    ((twistedE6Datum hf hK σ hσ).isPGroup_U.to_le ((twistedE6Datum hf hK σ hσ).X_le a))
    (xC_mem_X a c) ⟨1, by simpa using minOrbitHom_uSL_sq σ a c⟩
    (by rw [iso_minOrbitHom_uSL]; rfl)

include hf hK hσ in
theorem minOrbitHom_vSL_mem (c : orbitField TwistTag.E6 K σ a) :
    minOrbitHom σ a (vSL c) ∈ TwistedE6.fixedGroup K σ := by
  exact mem_fixedGroup_of_pLift hf hK σ hσ
    (P := (twistedE6Datum hf hK σ hσ).Y a)
    ((twistedE6Datum hf hK σ hσ).isPGroup_L.to_le ((twistedE6Datum hf hK σ hσ).Y_le a))
    (g := yC TwistTag.E6 K σ a c) (orbitY_mem_Yg a c) ⟨1, by simpa using minOrbitHom_vSL_sq σ a c⟩
    (by rw [iso_minOrbitHom_vSL]; rfl)

include hf hK hσ in
theorem nhat_coe :
    (((twistedE6CoverData hf hK σ hσ).nhat a : ↥(TwistedE6.fixedGroup K σ)) :
      ↥(e6Data_valid.minGroup K)) = minOrbitHom σ a WSL := by
  show canonMin K (((relCs TwistTag.E6).simple a : ↥(relWeylTwist TwistTag.E6)) :
    WeylGroup TwistTag.E6.tag) = _
  rw [relCs_simple]
  exact canonMin_orbitReflection σ a

include hf hK hσ in
theorem minOrbitHom_WSL_mem : minOrbitHom σ a WSL ∈ TwistedE6.fixedGroup K σ := by
  rw [← nhat_coe hf hK σ hσ a]
  exact ((twistedE6CoverData hf hK σ hσ).nhat a).2

include hf hK hσ in
theorem minOrbitHom_HSL_mem (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    minOrbitHom σ a (HSL u) ∈ TwistedE6.fixedGroup K σ := by
  have key : ∀ w : (orbitField TwistTag.E6 K σ a)ˣ,
      minOrbitHom σ a (HSL (-w)) ∈ TwistedE6.fixedGroup K σ := by
    intro w
    have h := congrArg (minOrbitHom σ a) (uSL_mul_WSL w)
    rw [map_mul, map_mul, map_mul] at h
    have e : minOrbitHom σ a (HSL (-w)) =
        (minOrbitHom σ a (vSL ((w⁻¹ : (orbitField TwistTag.E6 K σ a)ˣ) :
          orbitField TwistTag.E6 K σ a)))⁻¹ *
        (minOrbitHom σ a (uSL (w : orbitField TwistTag.E6 K σ a)) * minOrbitHom σ a WSL) *
        (minOrbitHom σ a (uSL (-((w⁻¹ : (orbitField TwistTag.E6 K σ a)ˣ) :
          orbitField TwistTag.E6 K σ a))))⁻¹ := by
      rw [h]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (minOrbitHom_vSL_mem hf hK σ hσ a _))
      (mul_mem (minOrbitHom_uSL_mem hf hK σ hσ a _) (minOrbitHom_WSL_mem hf hK σ hσ a)))
      (inv_mem (minOrbitHom_uSL_mem hf hK σ hσ a _))
  simpa using key (-u)

include hf hK hσ in
@[expose] def hatX (c : orbitField TwistTag.E6 K σ a) : ↥(TwistedE6.fixedGroup K σ) :=
  ⟨minOrbitHom σ a (uSL c), minOrbitHom_uSL_mem hf hK σ hσ a c⟩

include hf hK hσ in
@[expose] def hatY (c : orbitField TwistTag.E6 K σ a) : ↥(TwistedE6.fixedGroup K σ) :=
  ⟨minOrbitHom σ a (vSL c), minOrbitHom_vSL_mem hf hK σ hσ a c⟩

include hf hK hσ in
@[expose] def hatH (u : (orbitField TwistTag.E6 K σ a)ˣ) : ↥(TwistedE6.fixedGroup K σ) :=
  ⟨minOrbitHom σ a (HSL u), minOrbitHom_HSL_mem hf hK σ hσ a u⟩

include hf hK hσ in
theorem coverHom_hatX (c : orbitField TwistTag.E6 K σ a) :
    coverHom hf hK σ hσ (hatX hf hK σ hσ a c) = xC TwistTag.E6 K σ a c :=
  Subtype.ext ((coe_coverHom hf hK σ hσ _).trans (iso_minOrbitHom_uSL σ a c))

include hf hK hσ in
theorem coverHom_hatY (c : orbitField TwistTag.E6 K σ a) :
    coverHom hf hK σ hσ (hatY hf hK σ hσ a c) = yC TwistTag.E6 K σ a c :=
  Subtype.ext ((coe_coverHom hf hK σ hσ _).trans (iso_minOrbitHom_vSL σ a c))

include hf hK hσ in
theorem coverHom_hatH (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    coverHom hf hK σ hσ (hatH hf hK σ hσ a u) = hC TwistTag.E6 K σ a u :=
  Subtype.ext ((coe_coverHom hf hK σ hσ _).trans (iso_minOrbitHom_HSL σ a u))

include hf hK hσ in
theorem hatX_sq (c : orbitField TwistTag.E6 K σ a) : hatX hf hK σ hσ a c ^ 2 = 1 :=
  Subtype.ext (minOrbitHom_uSL_sq σ a c)

include hf hK hσ in
theorem hatY_sq (c : orbitField TwistTag.E6 K σ a) : hatY hf hK σ hσ a c ^ 2 = 1 :=
  Subtype.ext (minOrbitHom_vSL_sq σ a c)

include hf hK hσ in
@[expose] def twistedE6CoverRankOne :
    CoverRankOne (twistedE6CoverData hf hK σ hσ) (fun a => orbitField TwistTag.E6 K σ a) where
  x s c := hatX hf hK σ hσ s c
  y s c := hatY hf hK σ hσ s c
  hh s u := hatH hf hK σ hσ s u
  x_mem s c := by
    refine (twistedE6CoverData hf hK σ hσ).mem_lX.2 ⟨?_, 1, ?_⟩
    · rw [coverHom_hatX]
      exact xC_mem_X s c
    · exact hatX_sq hf hK σ hσ s c
  x_surj s g hg := by
    obtain ⟨c, hc⟩ := mem_X_twistedDatum.1 hg.1
    refine ⟨c, pLift_inj (h := isCentralCover_coverHom hf hK σ hσ) ?_ hg ?_⟩
    · refine (twistedE6CoverData hf hK σ hσ).mem_lX.2 ⟨?_, 1, ?_⟩
      · rw [coverHom_hatX]
        exact xC_mem_X s c
      · exact hatX_sq hf hK σ hσ s c
    · rw [coverHom_hatX]
      exact hc
  x_zero s := Subtype.ext (by
    show minOrbitHom σ s (uSL 0) = 1
    rw [uSL_zero', map_one])
  x_inj s c d h := by
    have h1 := congrArg (coverHom hf hK σ hσ) h
    rw [coverHom_hatX, coverHom_hatX] at h1
    exact xC_injective s h1
  y_mem s c := by
    refine (twistedE6CoverData hf hK σ hσ).mem_lL.2 ⟨?_, 1, ?_⟩
    · rw [coverHom_hatY]
      exact Subgroup.mem_subgroupOf.2 (yC_mem s c)
    · exact hatY_sq hf hK σ hσ s c
  hh_mem s u := by
    rw [Subgroup.mem_comap, coverHom_hatH]
    exact hC_mem_H s u
  hh_mul s u v := Subtype.ext (by
    show minOrbitHom σ s (HSL (u * v)) = minOrbitHom σ s (HSL u) * minOrbitHom σ s (HSL v)
    rw [HSL_mul, map_mul])
  hh_one s := Subtype.ext (by
    show minOrbitHom σ s (HSL 1) = 1
    rw [HSL_one, map_one])
  phi_id s u := Subtype.ext (by
    show minOrbitHom σ s (uSL (u : orbitField TwistTag.E6 K σ s)) *
      (((twistedE6CoverData hf hK σ hσ).nhat s : ↥(TwistedE6.fixedGroup K σ)) :
        ↥(e6Data_valid.minGroup K)) = _
    rw [nhat_coe hf hK σ hσ s]
    have h := congrArg (minOrbitHom σ s) (uSL_mul_WSL u)
    rw [map_mul, map_mul, map_mul] at h
    exact h)
  psi_id s u := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [nhat_coe hf hK σ hσ s]
    have h := congrArg (minOrbitHom σ s) (WSL_mul_uSL_mul_WSL u)
    simp only [map_mul] at h
    exact h

include hf hK hσ in
theorem twistedCover_pow (h : ↥(TwistedE6.fixedGroup K σ))
    (hh : h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :
    h ^ (Nat.card K - 1) = 1 := by
  have hT : ((Isogeny.e6IsogenyT K (h : ↥(e6Data_valid.minGroup K)) :
      ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) ∈
      torusGroup TwistTag.E6.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1
      (show ((coverHom hf hK σ hσ h : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) ∈ graphFixedRootTorus TwistTag.E6 K σ from hh)).1).1
  exact Subtype.ext (pow_card_sub_one_of_isogeny_mem_torusGroup hT)

include hf hK hσ in
theorem twistedCover_hodd : ∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ),
    IsPElt 2 h → h = 1 := by
  intro h hh ⟨k, hk⟩
  have hN := twistedCover_pow hf hK σ hσ h hh
  have hev : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩)
  have hlt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨r, hr⟩ := hev
  have hodd : Nat.Coprime (2 ^ k) (Nat.card K - 1) := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.coprime_two_left]
    exact ⟨r - 1, by omega⟩
  have h1 : orderOf h ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf h ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one hN
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hodd h1 h2)

include hf hK hσ in
theorem twistedCover_split (k : Type*) [Field k] [Algebra K k] :
    SplitOver k ((twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :=
  splitOver_of_pow_card_sub_one k (twistedCover_pow hf hK σ hσ)

include hf hK hσ in
theorem twisted_exists_isCoverType {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] [CharP k 2] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V}
    (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ χ : ↥(TwistedE6.fixedGroup K σ) → k, ∃ J : Finset (Fin TwistTag.E6.foldedTag.rank),
      IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J :=
  exists_isCoverType hρ (twistedCover_split hf hK σ hσ k)

include hf hK hσ in
theorem twisted_isCoverType_unique {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] [CharP k 2] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V}
    (hρ : IsSimpleRep ρ) {y y' : V} {χ χ' : ↥(TwistedE6.fixedGroup K σ) → k}
    {J J' : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (ht' : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y' χ' J') :
    (∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), χ h = χ' h) ∧ J = J' :=
  IsCoverType.unique hρ (twistedCover_split hf hK σ hσ k) ht ht'

include hf hK hσ in
theorem twisted_iso_of_isCoverType {k V V' : Type*} [Field k] [Algebra K k] [AddCommGroup V]
    [Module k V] [AddCommGroup V'] [Module k V'] [CharP k 2]
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V}
    {ρ' : Representation k ↥(TwistedE6.fixedGroup K σ) V'} (hρ : IsSimpleRep ρ)
    (hρ' : IsSimpleRep ρ') {y : V} {y' : V'} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (ht' : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ' y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : ↥(TwistedE6.fixedGroup K σ)) (v : V), β (ρ g v) = ρ' g (β v) :=
  iso_of_isCoverType (twistedCover_hodd hf hK σ hσ) hρ hρ' (twistedCover_split hf hK σ hσ k) ht ht'

open Classical in
include hf hK hσ in
theorem twisted_mu_eq {k V : Type*} [Field k] [Algebra K k] [AddCommGroup V] [Module k V]
    [CharP k 2] {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    {μ : Fin TwistTag.E6.foldedTag.rank → k}
    (hμ : (twistedE6CoverData hf hK σ hσ).datum.IsCurtisType ρ y χ μ)
    (s : Fin TwistTag.E6.foldedTag.rank) [Fintype (orbitField TwistTag.E6 K σ s)ˣ] :
    μ s = if (∀ u : (orbitField TwistTag.E6 K σ s)ˣ, χ (hatH hf hK σ hσ s u) = 1) ∧ s ∉ J then
      ∑ u : (orbitField TwistTag.E6 K σ s)ˣ, χ (hatH hf hK σ hσ s u) else 0 := by
  convert IsCoverType.mu_eq (R := twistedE6CoverRankOne hf hK σ hσ)
    (twistedCover_hodd hf hK σ hσ) ht hμ s <;> rfl

end Cover

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
