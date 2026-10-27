module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx

public section

namespace CFSG.HardMathSupport.C14IdxDet

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.C14Idx

open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L] {ι : Type}

@[expose] def PerpOf (Ψ : Set (Fin τ.rank → ℤ)) (lam : Fin τ.rank → ℤ) : Prop :=
  ∀ α ∈ Ψ, ∑ i, α i * lam i = 0

@[expose] def WtEquiv (Ψ : Set (Fin τ.rank → ℤ)) (u v : Fin τ.rank → ℤ) : Prop :=
  ∀ lam, PerpOf Ψ lam → ∑ i, (u i - v i) * lam i = 0

@[expose] def wtClass (Ψ : Set (Fin τ.rank → ℤ)) (ℓ₀ : Label τ) : Set (Label τ) :=
  {ℓ | WtEquiv Ψ (labelWt τ ℓ) (labelWt τ ℓ₀)}

theorem rootChar_mul_left (a b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one_left (v : Fin τ.rank → ℤ) : rootChar (1 : Fin τ.rank → Lˣ) v = 1 := by
  simp [rootChar]

theorem rootChar_inv_left (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem rootChar_zsmul (a : Fin τ.rank → Lˣ) (k : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (k • v) = rootChar a v ^ k := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul, mul_comm]

theorem rootChar_neg (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← neg_one_zsmul, rootChar_zsmul, zpow_neg_one]

theorem rootChar_cochar (lam : Fin τ.rank → ℤ) (c : Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (cochar lam c) v = c ^ (∑ i, v i * lam i) := by
  simp only [rootChar, cochar, ← zpow_mul, mul_comm (lam _)]
  exact Finset.prod_zpow_eq_zpow_sum _ _ _

@[expose] def zGen (Ψ : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → Lˣ) :=
  {s | ∃ (lam : Fin τ.rank → ℤ) (c : Lˣ), PerpOf Ψ lam ∧ s = cochar lam c}

theorem rootChar_eq_one_of_mem_closure {Ψ : Set (Fin τ.rank → ℤ)} {s : Fin τ.rank → Lˣ}
    (hs : s ∈ Subgroup.closure (zGen Ψ)) {v : Fin τ.rank → ℤ} (hv : WtEquiv Ψ v 0) :
    rootChar s v = 1 := by
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨lam, c, hlam, rfl⟩ := hx
    rw [rootChar_cochar]
    have := hv lam hlam
    simp only [Pi.zero_apply, sub_zero] at this
    rw [this, zpow_zero]
  | one => exact rootChar_one_left v
  | mul x y _ _ hx hy => rw [rootChar_mul_left, hx, hy, one_mul]
  | inv x _ hx => rw [rootChar_inv_left, hx, inv_one]

theorem rootChar_eq_of_wtEquiv {Ψ : Set (Fin τ.rank → ℤ)} {s : Fin τ.rank → Lˣ}
    (hs : s ∈ Subgroup.closure (zGen Ψ)) {u v : Fin τ.rank → ℤ} (huv : WtEquiv Ψ u v) :
    rootChar s u = rootChar s v := by
  have h0 : WtEquiv Ψ (u - v) 0 := fun lam hlam => by
    have := huv lam hlam
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using this
  have := rootChar_eq_one_of_mem_closure hs h0
  rwa [rootChar_sub, mul_inv_eq_one] at this

theorem exists_of_mem_famZ {a : ι → Fin τ.rank → Lˣ} {g : ModGL τ L} (hg : g ∈ famZ a) :
    ∃ s ∈ Subgroup.closure (zGen (familyKernel a)), g = rootDiagUnit τ s := by
  have hset : {g : ModGL τ L | ∃ (lam : Fin τ.rank → ℤ) (c : Lˣ),
      (∀ α ∈ familyKernel a, ∑ i, α i * lam i = 0) ∧ g = rootDiagUnit τ (cochar lam c)} =
      rootDiagUnitHom τ L '' zGen (familyKernel a) := by
    ext g
    constructor
    · rintro ⟨lam, c, hlam, rfl⟩
      exact ⟨_, ⟨lam, c, hlam, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨lam, c, hlam, rfl⟩, rfl⟩
      exact ⟨lam, c, hlam, rfl⟩
  rw [famZ, hset, ← MonoidHom.map_closure] at hg
  obtain ⟨s, hs, rfl⟩ := hg
  exact ⟨s, hs, rfl⟩

theorem rootDiagUnit_apply_apply (s : Fin τ.rank → Lˣ) (w : RootModule τ L) (ℓ : Label τ) :
    (rootDiagUnit τ s : Module.End L (RootModule τ L)) w ℓ =
      (rootChar s (labelWt τ ℓ) : L) * w ℓ := by
  classical
  change rootDiag s w ℓ = _
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
  | single b r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, rootDiag_single, smul_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hb : b = ℓ
    · subst hb
      simp only [Finsupp.single_eq_same]
      ring
    · simp [Finsupp.single_apply, hb]

theorem exists_zpow_ne_one [IsAlgClosed L] {k : ℤ} (hk : k ≠ 0) : ∃ c : Lˣ, c ^ k ≠ 1 := by
  classical
  have hn : 0 < k.natAbs := Int.natAbs_pos.2 hk
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    ((Polynomial.nthRoots k.natAbs (1 : L)).toFinset ∪ {0})
  rw [Finset.mem_union, not_or, Multiset.mem_toFinset, Finset.mem_singleton] at hx
  have hx0 : x ≠ 0 := hx.2
  refine ⟨Units.mk0 x hx0, fun h => hx.1 ?_⟩
  rw [Polynomial.mem_nthRoots hn]
  have h' : (Units.mk0 x hx0) ^ k.natAbs = 1 := by
    rcases Int.natAbs_eq k with h1 | h1
    · rw [h1] at h; exact_mod_cast h
    · rw [h1, zpow_neg, inv_eq_one] at h; exact_mod_cast h
  have := congrArg Units.val h'
  simpa using this

@[expose] noncomputable def wtSpace (Ψ : Set (Fin τ.rank → ℤ)) (ℓ₀ : Label τ) :
    Submodule L (RootModule τ L) :=
  Finsupp.supported L L (wtClass Ψ ℓ₀)

theorem mem_wtSpace {Ψ : Set (Fin τ.rank → ℤ)} {ℓ₀ : Label τ} {w : RootModule τ L} :
    w ∈ wtSpace (L := L) Ψ ℓ₀ ↔ ∀ ℓ, ¬ WtEquiv Ψ (labelWt τ ℓ) (labelWt τ ℓ₀) → w ℓ = 0 := by
  rw [wtSpace, Finsupp.mem_supported']
  rfl

theorem rootDiagUnit_apply_of_mem_wtSpace {Ψ : Set (Fin τ.rank → ℤ)} {s : Fin τ.rank → Lˣ}
    (hs : s ∈ Subgroup.closure (zGen Ψ)) {ℓ₀ : Label τ} {w : RootModule τ L}
    (hw : w ∈ wtSpace Ψ ℓ₀) :
    (rootDiagUnit τ s : Module.End L (RootModule τ L)) w =
      (rootChar s (labelWt τ ℓ₀) : L) • w := by
  ext ℓ
  rw [rootDiagUnit_apply_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hℓ : WtEquiv Ψ (labelWt τ ℓ) (labelWt τ ℓ₀)
  · rw [rootChar_eq_of_wtEquiv hs hℓ]
  · rw [mem_wtSpace.1 hw ℓ hℓ, mul_zero, mul_zero]

theorem apply_mem_wtSpace [IsAlgClosed L] {a : ι → Fin τ.rank → Lˣ} {m : ModGL τ L}
    (hm : ∀ z ∈ famZ a, z * m = m * z) {ℓ₀ : Label τ} {w : RootModule τ L}
    (hw : w ∈ wtSpace (familyKernel a) ℓ₀) :
    (m : Module.End L (RootModule τ L)) w ∈ wtSpace (familyKernel a) ℓ₀ := by
  rw [mem_wtSpace]
  intro ℓ hℓ
  simp only [WtEquiv, not_forall] at hℓ
  obtain ⟨lam, hlam, hk⟩ := hℓ
  obtain ⟨c, hc⟩ := exists_zpow_ne_one (L := L) hk
  have hzs : cochar lam c ∈ Subgroup.closure (zGen (familyKernel a)) :=
    Subgroup.subset_closure ⟨lam, c, hlam, rfl⟩
  have hzZ : rootDiagUnit τ (cochar lam c) ∈ famZ a := Subgroup.subset_closure ⟨lam, c, hlam, rfl⟩
  have hcomm := congrArg (fun u : ModGL τ L => (u : Module.End L (RootModule τ L)) w ℓ) (hm _ hzZ)
  simp only [Units.val_mul, Module.End.mul_apply] at hcomm
  rw [rootDiagUnit_apply_apply, rootDiagUnit_apply_of_mem_wtSpace hzs hw, map_smul,
    Finsupp.smul_apply, smul_eq_mul, rootChar_cochar, rootChar_cochar] at hcomm
  have hne : ((c ^ (∑ i, labelWt τ ℓ i * lam i) : Lˣ) : L) ≠
      ((c ^ (∑ i, labelWt τ ℓ₀ i * lam i) : Lˣ) : L) := by
    intro h
    apply hc
    have h' := Units.val_injective h
    rw [← mul_inv_eq_one, ← zpow_sub, ← Finset.sum_sub_distrib] at h'
    simpa only [sub_mul] using h'
  have h0 := sub_eq_zero.2 hcomm
  rw [← sub_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

@[expose] noncomputable def wtStab (Ψ : Set (Fin τ.rank → ℤ)) (ℓ₀ : Label τ) :
    Subgroup (ModGL τ L) where
  carrier := {g | ∀ w ∈ wtSpace (L := L) Ψ ℓ₀,
    (g : Module.End L (RootModule τ L)) w ∈ wtSpace Ψ ℓ₀ ∧
      ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) w ∈ wtSpace Ψ ℓ₀}
  mul_mem' {g h} hg hh w hw := by
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul, Module.End.mul_apply]
      exact (hg _ (hh w hw).1).1
    · simp only [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
      exact (hh _ (hg w hw).2).2
  one_mem' w hw := by
    simp only [inv_one, Units.val_one, Module.End.one_apply]
    exact ⟨hw, hw⟩
  inv_mem' {g} hg w hw := by
    simp only [inv_inv]
    exact ⟨(hg w hw).2, (hg w hw).1⟩

theorem mem_wtStab {Ψ : Set (Fin τ.rank → ℤ)} {ℓ₀ : Label τ} {g : ModGL τ L} :
    g ∈ wtStab (L := L) Ψ ℓ₀ ↔ ∀ w ∈ wtSpace (L := L) Ψ ℓ₀,
      (g : Module.End L (RootModule τ L)) w ∈ wtSpace Ψ ℓ₀ ∧
        ((g⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) w ∈ wtSpace Ψ ℓ₀ := Iff.rfl

@[expose] noncomputable def wtRestrict (Ψ : Set (Fin τ.rank → ℤ)) (ℓ₀ : Label τ) :
    wtStab (L := L) Ψ ℓ₀ →* Module.End L (wtSpace (L := L) Ψ ℓ₀) where
  toFun g := ((g : ModGL τ L) : Module.End L (RootModule τ L)).restrict
    fun w hw => (mem_wtStab.1 g.2 w hw).1
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem wtRestrict_apply {Ψ : Set (Fin τ.rank → ℤ)} {ℓ₀ : Label τ} (g : wtStab (L := L) Ψ ℓ₀)
    (w : wtSpace (L := L) Ψ ℓ₀) :
    ((wtRestrict Ψ ℓ₀ g w : wtSpace (L := L) Ψ ℓ₀) : RootModule τ L) =
      ((g : ModGL τ L) : Module.End L (RootModule τ L)) w := rfl

@[expose] noncomputable def wtDet (Ψ : Set (Fin τ.rank → ℤ)) (ℓ₀ : Label τ) :
    wtStab (L := L) Ψ ℓ₀ →* L :=
  (@LinearMap.det (wtSpace (L := L) Ψ ℓ₀) _ L _ _).comp (wtRestrict Ψ ℓ₀)

theorem wtDet_apply {Ψ : Set (Fin τ.rank → ℤ)} {ℓ₀ : Label τ} (g : wtStab (L := L) Ψ ℓ₀) :
    wtDet Ψ ℓ₀ g = (@LinearMap.det (wtSpace (L := L) Ψ ℓ₀) _ L _ _) (wtRestrict Ψ ℓ₀ g) := rfl

theorem wtDet_commutator {Ψ : Set (Fin τ.rank → ℤ)} {ℓ₀ : Label τ} (x y : wtStab (L := L) Ψ ℓ₀) :
    wtDet (L := L) Ψ ℓ₀ ⁅x, y⁆ = 1 := by
  have h : ∀ u : wtStab (L := L) Ψ ℓ₀, wtDet (L := L) Ψ ℓ₀ u * wtDet (L := L) Ψ ℓ₀ u⁻¹ = 1 :=
    fun u => by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [commutatorElement_def, map_mul, map_mul, map_mul]
  calc _ = (wtDet (L := L) Ψ ℓ₀ x * wtDet (L := L) Ψ ℓ₀ x⁻¹) *
        (wtDet (L := L) Ψ ℓ₀ y * wtDet (L := L) Ψ ℓ₀ y⁻¹) := by ring
    _ = 1 := by rw [h, h, one_mul]

theorem coe_mem_wtStab_of_mem_famM
    [IsAlgClosed L] {a : ι → Fin τ.rank → Lˣ}
    (hcent : ∀ g ∈ famZ a, ∀ m ∈ famM a, g * (m : ModGL τ L) = m * g)
    {m : adjointGroup τ L} (hm : m ∈ famM a) (ℓ₀ : Label τ) :
    (m : ModGL τ L) ∈ wtStab (familyKernel a) ℓ₀ := fun w hw =>
  ⟨apply_mem_wtSpace (fun z hz => hcent z hz m hm) hw, by
    rw [← Subgroup.coe_inv]
    exact apply_mem_wtSpace (fun z hz => hcent z hz _ (inv_mem hm)) hw⟩

theorem wtDet_eq_one_of_mem_famS
    [IsAlgClosed L] {a : ι → Fin τ.rank → Lˣ}
    (hcent : ∀ g ∈ famZ a, ∀ m ∈ famM a, g * (m : ModGL τ L) = m * g)
    {g : adjointGroup τ L} (hg : g ∈ famS a) (ℓ₀ : Label τ) :
    ∃ h : (g : ModGL τ L) ∈ wtStab (familyKernel a) ℓ₀,
      wtDet (L := L) (familyKernel a) ℓ₀ ⟨g, h⟩ = 1 := by
  let N : Subgroup (adjointGroup τ L) :=
    ((wtDet (L := L) (familyKernel a) ℓ₀).ker.map
      (wtStab (familyKernel a) ℓ₀).subtype).comap (adjointGroup τ L).subtype
  have hle : famS a ≤ N := by
    rw [famS, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨⁅⟨_, coe_mem_wtStab_of_mem_famM hcent h₁ ℓ₀⟩,
      ⟨_, coe_mem_wtStab_of_mem_famM hcent h₂ ℓ₀⟩⁆, wtDet_commutator _ _, ?_⟩)
    simp [commutatorElement_def]
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hle hg))
  have hxg' : (x : ModGL τ L) = g := hxg
  have hmem : (g : ModGL τ L) ∈ wtStab (familyKernel a) ℓ₀ := hxg' ▸ x.2
  refine ⟨hmem, ?_⟩
  have : (⟨(g : ModGL τ L), hmem⟩ : wtStab (L := L) (familyKernel a) ℓ₀) = x :=
    Subtype.ext hxg'.symm
  rw [this]
  exact hx

theorem finrank_wtSpace (Ψ : Set (Fin τ.rank → ℤ)) (ℓ₀ : Label τ) :
    Module.finrank L (wtSpace (L := L) Ψ ℓ₀) = Nat.card (wtClass Ψ ℓ₀) := by
  classical
  rw [wtSpace, (Finsupp.supportedEquivFinsupp (M := L) (R := L) (wtClass Ψ ℓ₀)).finrank_eq,
    Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

theorem wtDet_rootDiagUnit {Ψ : Set (Fin τ.rank → ℤ)} {s : Fin τ.rank → Lˣ}
    (hs : s ∈ Subgroup.closure (zGen Ψ)) (ℓ₀ : Label τ)
    (h : rootDiagUnit τ s ∈ wtStab (L := L) Ψ ℓ₀) :
    wtDet (L := L) Ψ ℓ₀ ⟨rootDiagUnit τ s, h⟩ =
      (rootChar s (labelWt τ ℓ₀) : L) ^ Nat.card (wtClass Ψ ℓ₀) := by
  have hr : wtRestrict Ψ ℓ₀ ⟨rootDiagUnit τ s, h⟩ = (rootChar s (labelWt τ ℓ₀) : L) • LinearMap.id :=
    LinearMap.ext fun w => Subtype.ext ((wtRestrict_apply _ w).trans
      (rootDiagUnit_apply_of_mem_wtSpace hs w.2))
  have key : wtDet (L := L) Ψ ℓ₀ ⟨rootDiagUnit τ s, h⟩ =
      (@LinearMap.det (wtSpace (L := L) Ψ ℓ₀) _ L _ _) ((rootChar s (labelWt τ ℓ₀) : L) • LinearMap.id) := by
    rw [wtDet_apply, hr]
  haveI : Module.Free L (wtSpace (L := L) Ψ ℓ₀) := Module.Free.of_divisionRing L ↥(wtSpace (L := L) Ψ ℓ₀)
  rw [key, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_wtSpace]

theorem familyGroup_le_centralizer
    {a : ι → Fin τ.rank → Lˣ} {s : Fin τ.rank → Lˣ}
    (hs : ∀ α ∈ familyKernel a, rootChar s α = 1) :
    familyGroup a ≤ Subgroup.centralizer {rootDiagUnit τ s} := by
  refine sup_le (fun h hh => ?_) (iSup₂_le fun α hα => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (rootDiagUnit_mul_comm_of_mem_torusGroup s hh).symm
  · rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have := rootDiagUnit_conj_pinnedX s hα.1 c
    rw [hs α hα, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem famZ_comm_famM
    {a : ι → Fin τ.rank → Lˣ} {g : ModGL τ L} (hg : g ∈ famZ a)
    {m : adjointGroup τ L} (hm : m ∈ famM a) : g * (m : ModGL τ L) = m * g := by
  have hle : famZ a ≤ Subgroup.centralizer (familyGroup a) := by
    rw [famZ, Subgroup.closure_le]
    rintro _ ⟨lam, c, hlam, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    refine Subgroup.mem_centralizer_singleton_iff.1 (familyGroup_le_centralizer
      (fun α hα => ?_) hh)
    rw [rootChar_cochar, hlam α hα, zpow_zero]
  exact (Subgroup.mem_centralizer_iff.1 (hle hg) _ (Subgroup.mem_subgroupOf.1 hm)).symm

@[expose] def latGen (Ψ : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {v | WtEquiv Ψ v 0} ∪ Set.range fun ℓ : Label τ => (Nat.card (wtClass Ψ ℓ) : ℤ) • labelWt τ ℓ

theorem exists_pow_eq_one_of_mem_famZ_famS
    [IsAlgClosed L] {a : ι → Fin τ.rank → Lˣ} (N : ℕ)
    (hlat : ∀ i, (N • Pi.single i 1 : Fin τ.rank → ℤ) ∈
      AddSubgroup.closure (latGen (familyKernel a)))
    (g : adjointGroup τ L) (hgZ : (g : ModGL τ L) ∈ famZ a) (hgS : g ∈ famS a) :
    ∃ s : Fin τ.rank → Lˣ, s ^ N = 1 ∧ (g : ModGL τ L) = rootDiagUnit τ s := by
  have hcent : ∀ g ∈ famZ a, ∀ m ∈ famM a, g * (m : ModGL τ L) = m * g :=
    fun _ hg _ hm => famZ_comm_famM hg hm
  obtain ⟨s, hs, hgs⟩ := exists_of_mem_famZ hgZ
  have hdet : ∀ ℓ₀ : Label τ,
      rootChar s (labelWt τ ℓ₀) ^ Nat.card (wtClass (familyKernel a) ℓ₀) = 1 := by
    intro ℓ₀
    obtain ⟨h, h1⟩ := wtDet_eq_one_of_mem_famS hcent hgS ℓ₀
    have h' : rootDiagUnit τ s ∈ wtStab (L := L) (familyKernel a) ℓ₀ := hgs ▸ h
    have hx : (⟨rootDiagUnit τ s, h'⟩ : wtStab (L := L) (familyKernel a) ℓ₀) = ⟨g, h⟩ :=
      Subtype.ext hgs.symm
    have h2 := wtDet_rootDiagUnit hs ℓ₀ h'
    rw [hx, h1] at h2
    exact Units.val_eq_one.1 (by rw [Units.val_pow_eq_pow_val]; exact h2.symm)
  have hchar : ∀ v ∈ AddSubgroup.closure (latGen (familyKernel a)), rootChar s v = 1 := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      rcases hv with hv | ⟨ℓ, rfl⟩
      · exact rootChar_eq_one_of_mem_closure hs hv
      · rw [rootChar_zsmul, zpow_natCast, hdet]
    | zero => exact rootChar_zero s
    | add u v _ _ hu hv => rw [rootChar_add, hu, hv, one_mul]
    | neg u _ hu => rw [rootChar_neg, hu, inv_one]
  have hsN : s ^ N = 1 := funext fun i => by
    have := hchar _ (hlat i)
    rw [rootChar_nsmul_single] at this
    rw [Pi.pow_apply, Pi.one_apply, this]
  exact ⟨s, hsN, hgs⟩

theorem pow_eq_one_of_mem_famZ_famS
    [IsAlgClosed L] {a : ι → Fin τ.rank → Lˣ} (N : ℕ)
    (hlat : ∀ i, (N • Pi.single i 1 : Fin τ.rank → ℤ) ∈
      AddSubgroup.closure (latGen (familyKernel a)))
    (g : adjointGroup τ L) (hgZ : (g : ModGL τ L) ∈ famZ a) (hgS : g ∈ famS a) : g ^ N = 1 := by
  obtain ⟨s, hsN, hgs⟩ := exists_pow_eq_one_of_mem_famZ_famS N hlat g hgZ hgS
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, hgs, OneMemClass.coe_one]
  change (rootDiagUnitHom τ L s) ^ N = 1
  rw [← map_pow, hsN, map_one]

theorem finite_famZ_inf_famS
    [IsAlgClosed L] {a : ι → Fin τ.rank → Lˣ} (N : ℕ) (hN : 0 < N)
    (hlat : ∀ i, (N • Pi.single i 1 : Fin τ.rank → ℤ) ∈
      AddSubgroup.closure (latGen (familyKernel a))) :
    Finite {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a} := by
  classical
  have hU : {u : Lˣ | u ^ N = 1}.Finite := by
    refine ((Polynomial.nthRoots N (1 : L)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn).subset fun u hu => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hN]
    rw [← Units.val_pow_eq_pow_val, hu.out, Units.val_one]
  have hS : (Set.pi Set.univ fun _ : Fin τ.rank => {u : Lˣ | u ^ N = 1}).Finite :=
    Set.Finite.pi fun _ => hU
  have hT : {g : adjointGroup τ L | (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a}.Finite := by
    refine ((hS.image (rootDiagUnit τ)).preimage Subtype.val_injective.injOn).subset ?_
    rintro g ⟨hgZ, hgS⟩
    obtain ⟨s, hsN, hgs⟩ := exists_pow_eq_one_of_mem_famZ_famS N hlat g hgZ hgS
    exact ⟨s, fun i _ => congrFun hsN i, hgs.symm⟩
  exact hT.to_subtype

@[expose] def F4ZSLattice : Prop :=
  ∀ Ψ : Set (Fin Tag.F4.rank → ℤ), (∀ α ∈ Ψ, IsRoot Tag.F4 α) →
    ∀ i, (6 • Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ AddSubgroup.closure (latGen Ψ)

theorem pow_six_of_mem_famZ_famS_F4_of_lattice
    [IsAlgClosed L] (hF4 : F4ZSLattice)
    (a : ι → Fin Tag.F4.rank → Lˣ) (g : adjointGroup Tag.F4 L) (hgZ : (g : ModGL Tag.F4 L) ∈ famZ a) (hgS : g ∈ famS a) :
    g ^ 6 = 1 :=
  pow_eq_one_of_mem_famZ_famS 6 (hF4 _ fun _ hα => hα.1) g hgZ hgS

end CFSG.HardMathSupport.C14IdxDet
