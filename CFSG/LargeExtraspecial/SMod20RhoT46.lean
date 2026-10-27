module

public import CFSG.LargeExtraspecial.SMod20Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.SmithE CFSG.F4.Native CFSG.Fischer

theorem uPos_le (x : Nat) : uPos[x]! ≤ 693 := by
  by_cases hx : x < 4096
  · exact uPos_get_le hx
  · rw [getElem!_neg uPos x (by simp [uPos]; omega)]
    decide

theorem ap_tvTable_eq (c : Nat) {i : Nat} (hi : i < 693) :
    CFSG.Sporadic.Th.Native.ap (tvTable c) i = uPos[normC (tvC c uPts[i]!)]! := by
  unfold CFSG.Sporadic.Th.Native.ap tvTable
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (lt_of_le_of_lt (uPos_le _) (by norm_num))]

theorem tvP_val (m a : Fin 693) :
    (tvP m a).val = ptImg m.val a.val := by
  have h := rep_tvP m a.val a.2
  rw [CFSG.Sporadic.Th.idx_of_lt _ a.2, tvTabs_get m, ap_tvTable_eq _ a.2] at h
  exact h.symm

theorem map_planeSet_tvP
    {k i : Nat} (hk : k < 693) (hi : i < 891) :
    (planeSet i).map (tvP ⟨k, hk⟩).toEmbedding = planeSet (planeImg k i) := by
  obtain ⟨hj, -, hpts⟩ := tw_parts hk hi
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    rw [mem_planeSet, Equiv.toEmbedding_apply, tvP_val]
    exact hpts a.val a.2 (mem_planeSet.mp ha)
  · rw [Finset.card_map, card_planeSet hi, card_planeSet hj]

@[expose] def PermPlanes (g : Equiv.Perm (Fin 693)) : Prop :=
  ∀ i < 891, ∃ j < 891, (planeSet i).map g.toEmbedding = planeSet j

theorem PermPlanes.mul {g h : Equiv.Perm (Fin 693)} (hg : PermPlanes g) (hh : PermPlanes h) :
    PermPlanes (g * h) := by
  intro i hi
  obtain ⟨j, hj, hij⟩ := hh i hi
  obtain ⟨l, hl, hjl⟩ := hg j hj
  refine ⟨l, hl, ?_⟩
  rw [← hjl, ← hij, Finset.map_map]
  rfl

theorem PermPlanes.inv {g : Equiv.Perm (Fin 693)}
    (hg : PermPlanes g) : PermPlanes g⁻¹ := by
  choose f hf hfe using hg
  let F : Fin 891 → Fin 891 := fun i => ⟨f i.val i.2, hf i.val i.2⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hab' : f a.val a.2 = f b.val b.2 := congrArg Fin.val hab
    have e : (planeSet a.val).map g.toEmbedding = (planeSet b.val).map g.toEmbedding := by
      rw [hfe a.val a.2, hfe b.val b.2, hab']
    exact Fin.ext (planeSet_injective a.2 b.2 (Finset.map_injective _ e))
  intro i hi
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hF) ⟨i, hi⟩
  refine ⟨j.val, j.2, ?_⟩
  have e := hfe j.val j.2
  have hfj : f j.val j.2 = i := congrArg Fin.val hj
  rw [hfj] at e
  rw [← e, Finset.map_map]
  convert Finset.map_refl
  ext a
  simp

theorem permPlanes_tvP
    (k : Fin 693) : PermPlanes (tvP k) := fun i hi =>
  ⟨planeImg k.val i, (tw_parts k.2 hi).1, map_planeSet_tvP k.2 hi⟩

theorem permPlanes_of_mem
    {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) : PermPlanes g := by
  rw [T46_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact permPlanes_tvP k
  | one => intro i hi; exact ⟨i, hi, by ext a; simp; rfl⟩
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

section Action

theorem exists_planeAct (g : T46) (i : Fin 891) :
    ∃ j : Fin 891,
      (planeSet i.val).map (g : Equiv.Perm (Fin 693)).toEmbedding = planeSet j.val := by
  obtain ⟨j, hj, e⟩ := permPlanes_of_mem g.2 i.val i.2
  exact ⟨⟨j, hj⟩, e⟩

@[expose] noncomputable def planeAct (g : T46) (i : Fin 891) : Fin 891 :=
  Classical.choose (exists_planeAct g i)

theorem map_planeSet_planeAct (g : T46) (i : Fin 891) :
    (planeSet i.val).map (g : Equiv.Perm (Fin 693)).toEmbedding = planeSet (planeAct g i).val :=
  Classical.choose_spec (exists_planeAct g i)

theorem planeAct_eq_iff (g : T46) (i j : Fin 891) :
    planeAct g i = j ↔ (planeSet i.val).map (g : Equiv.Perm (Fin 693)).toEmbedding =
      planeSet j.val := by
  rw [map_planeSet_planeAct]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (planeSet_injective (planeAct g i).2 j.2 h)⟩

noncomputable instance planeAction : MulAction T46 (Fin 891) where
  smul := planeAct
  one_smul i := (planeAct_eq_iff 1 i i).mpr (by ext a; simp; rfl)
  mul_smul g h i := by
    show planeAct (g * h) i = planeAct g (planeAct h i)
    refine (planeAct_eq_iff (g * h) i _).mpr ?_
    rw [← map_planeSet_planeAct g, ← map_planeSet_planeAct h, Finset.map_map]
    rfl

theorem map_planeSet_smul (g : T46) (i : Fin 891) :
    (planeSet i.val).map (g : Equiv.Perm (Fin 693)).toEmbedding = planeSet (g • i).val :=
  map_planeSet_planeAct g i

theorem tvP_smul (k : Fin 693) (i : Fin 891) :
    (⟨tvP k, tvP_mem k⟩ : T46) • i = ⟨planeImg k.val i.val, (tw_parts k.2 i.2).1⟩ :=
  (planeAct_eq_iff _ i _).mpr (map_planeSet_tvP k.2 i.2)

theorem opp_smul (g : T46) (i j : Fin 891) : Opp (g • i).val (g • j).val ↔ Opp i.val j.val := by
  rw [Opp, Opp, ← map_planeSet_smul, ← map_planeSet_smul, Finset.disjoint_map]

end Action

theorem ext_wtV {L L' : V →ₗ[ZMod 2] V}
    (h : ∀ i : Fin 891, L (wtV i.val) = L' (wtV i.val)) : L = L' :=
  LinearMap.ext_on_range span_wtV h

section Rho

theorem span_wtV_smul (g : T46) :
    Submodule.span (ZMod 2) (Set.range fun i : Fin 891 => wtV (g • i).val) = ⊤ := by
  have : (Set.range fun i : Fin 891 => wtV (g • i).val) =
      Set.range fun i : Fin 891 => wtV i.val := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨g • i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g⁻¹ • i, by show wtV (g • g⁻¹ • i).val = wtV i.val; rw [smul_inv_smul]⟩
  rw [this, span_wtV]

theorem fModel_wtV_smul (g : T46) (i j : Fin 891) :
    fModel (wtV (g • i).val) (wtV (g • j).val) = fModel (wtV i.val) (wtV j.val) := by
  rw [fModel_wtV (g • i).2 (g • j).2, fModel_wtV i.2 j.2]
  by_cases h : Opp i.val j.val
  · simp only [h, (opp_smul g i j).mpr h, ↓reduceIte]
  · simp only [h, mt (opp_smul g i j).mp h, ↓reduceIte]

theorem exists_rhoLin (g : T46) :
    ∃ L : V →ₗ[ZMod 2] V, ∀ i : Fin 891, L (wtV i.val) = wtV (g • i).val :=
  exists_linear_of_gram (K := ZMod 2) (W := V) (W' := V) (ι := Fin 891) fModel fModel span_wtV
    (span_wtV_smul g) (fun _ hv => fModel_nondegenerate hv) (fun i j => fModel_wtV_smul g i j)

@[expose] noncomputable def rhoLin (g : T46) :
    V →ₗ[ZMod 2] V :=
  Classical.choose (exists_rhoLin g)

theorem rhoLin_wtV (g : T46) (i : Fin 891) :
    rhoLin g (wtV i.val) = wtV (g • i).val :=
  Classical.choose_spec (exists_rhoLin g) i

theorem rhoLin_mul (g h : T46) :
    rhoLin (g * h) = rhoLin g ∘ₗ rhoLin h :=
  ext_wtV fun i => by rw [LinearMap.comp_apply, rhoLin_wtV, rhoLin_wtV, rhoLin_wtV, mul_smul]

theorem rhoLin_one : rhoLin 1 = LinearMap.id :=
  ext_wtV fun i => by rw [rhoLin_wtV, one_smul, LinearMap.id_apply]

@[expose] noncomputable def rhoMod :
    T46 →* (V ≃ₗ[ZMod 2] V) where
  toFun g := LinearEquiv.ofLinearMap (rhoLin g) (rhoLin g⁻¹)
    (by rw [← rhoLin_mul, mul_inv_cancel, rhoLin_one])
    (by rw [← rhoLin_mul, inv_mul_cancel, rhoLin_one])
  map_one' := LinearEquiv.ext fun v => by
    show rhoLin 1 v = v
    rw [rhoLin_one, LinearMap.id_apply]
  map_mul' g h := LinearEquiv.ext fun v => by
    show rhoLin (g * h) v = rhoLin g (rhoLin h v)
    rw [rhoLin_mul, LinearMap.comp_apply]

theorem rhoMod_wtV (g : T46) (i : Fin 891) :
    rhoMod g (wtV i.val) = wtV (g • i).val :=
  rhoLin_wtV g i

theorem rhoMod_tvP (k : Fin 693) :
    rhoMod ⟨tvP k, tvP_mem k⟩ = tvEquiv k.val := by
  apply LinearEquiv.toLinearMap_injective
  refine ext_wtV fun i => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, rhoMod_wtV, tvP_smul, tvEquiv_wtV k.2 i.2]

theorem rhoMod_conj_tvEquiv (g : T46) (k : Fin 693) :
    rhoMod g * tvEquiv k.val * (rhoMod g)⁻¹ = tvEquiv ((g : Equiv.Perm (Fin 693)) k).val := by
  rw [← rhoMod_tvP, ← rhoMod_tvP, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg rhoMod (Subtype.ext ((isPolarAut_of_mem g.2).mul_tvP_mul_inv k))

theorem fModel_rhoMod (g : T46) (v w : V) :
    fModel (rhoMod g v) (rhoMod g w) = fModel v w := by
  have key : fModel.compl₁₂ (rhoMod g : V →ₗ[ZMod 2] V) (rhoMod g : V →ₗ[ZMod 2] V) = fModel := by
    refine LinearMap.ext_on_range span_wtV fun i => ?_
    refine LinearMap.ext_on_range span_wtV fun j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, rhoMod_wtV]
    exact fModel_wtV_smul g i j
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B v w) key
  simpa using this

end Rho

end CFSG.LargeExtraspecial.SMod20
