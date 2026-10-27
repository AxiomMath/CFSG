module

public import CFSG.LieType.Simplicity.TitsBits
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4Data

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F4Sym

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits

@[expose] def f4Root : Fin 10 → (Fin Tag.F4.rank → ℤ) :=
  ![![1, 2, 3, 2], ![1, 1, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 0], ![2, 3, 4, 2], ![1, 3, 4, 2],
    ![1, 2, 4, 2], ![1, 2, 2, 0], ![1, 1, 2, 0], ![0, 1, 2, 0]]

@[expose] def f4Gen : Fin 6 → (Fin Tag.F4.rank → ℤ) :=
  ![![0, 1, 2, 2], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, -1, -2, -2], ![-1, 0, 0, 0], ![0, -1, 0, 0]]

@[expose] def f4Pos : Fin 10 → ℕ := ![44, 16, 8, 2, 43, 39, 35, 21, 13, 7]

@[expose] def f4GenPos : Fin 6 → ℕ := ![15, 0, 1, 23, 4, 6]

theorem f4Pos_spec : ∀ i : Fin 10, f4Pos i < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (f4Pos i) = f4Root i := by
  decide +kernel

theorem f4GenPos_spec : ∀ j : Fin 6, f4GenPos j < Tag.F4.rootCertificate.roots.length ∧
    Tag.F4.rootCertificate.root (f4GenPos j) = f4Gen j := by
  decide +kernel

theorem f4Root_injective : Function.Injective f4Root := by
  decide +kernel

theorem f4Root_height_pos : ∀ i : Fin 10, 0 < height (f4Root i) := by
  decide +kernel

section Roots


theorem isRoot_f4Root (i : Fin 10) : IsRoot .F4 (f4Root i) := by
  have h : ∀ i, f4Root i ∈ rootFinset .F4 := by decide +kernel
  exact mem_rootFinset.1 (h i)

theorem isRoot_f4Gen (j : Fin 6) : IsRoot .F4 (f4Gen j) := by
  have h : ∀ j, f4Gen j ∈ rootFinset .F4 := by decide +kernel
  exact mem_rootFinset.1 (h j)

end Roots

@[expose] def selBits (P : ℕ) (e : ZMod 2) : ℕ := if e.val = 0 then oneBits else P

@[expose] def bitsProd : List ℕ → ℕ
  | [] => oneBits
  | b :: l => mul b (bitsProd l)

section Elements

variable (K : Type) [Field K]

@[expose] noncomputable def f4a (i : Fin 10) : adjointGroup .F4 K :=
  ⟨pinnedX .F4 K (f4Root i) 1, pinnedX_mem_adjointGroup _ 1⟩

@[expose] noncomputable def f4g (j : Fin 6) : adjointGroup .F4 K :=
  ⟨pinnedX .F4 K (f4Gen j) 1, pinnedX_mem_adjointGroup _ 1⟩

variable {K} [CharP K 2]

theorem inv_pinnedX_one (α : Fin Tag.F4.rank → ℤ) :
    (pinnedX .F4 K α 1)⁻¹ = pinnedX .F4 K α 1 := by
  rw [pinnedX_neg, CharTwo.neg_eq]

theorem f4a_inv (i : Fin 10) : (f4a K i)⁻¹ = f4a K i :=
  Subtype.ext (inv_pinnedX_one _)

theorem f4g_inv (j : Fin 6) : (f4g K j)⁻¹ = f4g K j :=
  Subtype.ext (inv_pinnedX_one _)

theorem f4a_sq (i : Fin 10) : f4a K i ^ 2 = 1 := by
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.2 (f4a_inv i).symm

theorem pinnedX_one_pow (α : Fin Tag.F4.rank → ℤ) (n : ℕ) :
    pinnedX .F4 K α 1 ^ n = pinnedX .F4 K α (n : K) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, pinnedX_add]

theorem hasBits_pow_val {g : adjointGroup .F4 K} {P : ℕ} (hg : HasBits K g P) (e : ZMod 2) :
    HasBits K (g ^ e.val) (selBits P e) := by
  have h : e.val < 2 := ZMod.val_lt e
  unfold selBits
  split_ifs with h0
  · rw [h0, pow_zero]
    exact hasBits_one
  · rw [show e.val = 1 by omega, pow_one]
    exact hg

theorem hasBits_list_prod {ι : Type} (f : ι → adjointGroup .F4 K) (b : ι → ℕ)
    (hf : ∀ x, HasBits K (f x) (b x)) :
    ∀ L : List ι, HasBits K (L.map f).prod (bitsProd (L.map b))
  | [] => hasBits_one
  | x :: L => by
    rw [List.map_cons, List.prod_cons, List.map_cons, bitsProd]
    exact (hf x).mul (hasBits_list_prod f b hf L)

end Elements

theorem f4_comm_bits : ∀ i j : Fin 10,
    mul (pack (eltBits (f4Pos i))) (pack (eltBits (f4Pos j))) % 2 ^ 2704 =
      mul (pack (eltBits (f4Pos j))) (pack (eltBits (f4Pos i))) % 2 ^ 2704 := by
  decide +kernel

theorem f4_act_bits : ∀ (j : Fin 6) (i : Fin 10),
    mul (mul (pack (eltBits (f4GenPos j))) (pack (eltBits (f4Pos i))))
        (pack (eltBits (f4GenPos j))) % 2 ^ 2704 =
      bitsProd ((List.finRange 10).map fun k =>
        selBits (pack (eltBits (f4Pos k)))
          (CFSG.AGLEmbedding.R3.actMatN 2 f4Mod.basis.length (f4Mod.acts.get j) k i)) %
        2 ^ 2704 := by
  decide +kernel

section Group

variable
  {K : Type} [Field K] [CharP K 2]

theorem hasBits_pinnedX_one {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β)
    {a : ℕ} (ha : a < ReeTag.F4.tag.rootCertificate.roots.length)
    (hroot : ReeTag.F4.tag.rootCertificate.root a = β) :
    HasBits K ⟨pinnedX ReeTag.F4.tag K β 1, pinnedX_mem_adjointGroup β 1⟩ (pack (eltBits a)) := by
  have h1 := hasBits_eltElement (K := K) ⟨β, hβ⟩
  rw [RootOps.rootPos_eq ha hroot] at h1
  have hs : ((rootOperatorFamily ReeTag.F4.tag).pinnedFamilySign β : K) * 1 = 1 := by
    rw [mul_one]
    rcases (rootOperatorFamily ReeTag.F4.tag).pinnedFamilySign_eq β with h | h <;> rw [h]
    · simp
    · simp [CharTwo.neg_eq]
  have h2 : (rootOperatorFamily ReeTag.F4.tag).eltElement ⟨β, hβ⟩ 1 =
      ⟨pinnedX ReeTag.F4.tag K β 1, pinnedX_mem_adjointGroup β 1⟩ := by
    apply Subtype.ext
    change (rootOperatorFamily ReeTag.F4.tag).eltUnit K ⟨β, hβ⟩ 1 = pinnedX ReeTag.F4.tag K β 1
    rw [(rootOperatorFamily ReeTag.F4.tag).pinnedX_eq_eltUnit K hβ, hs]
  rwa [h2] at h1

theorem hasBits_f4a (i : Fin 10) : HasBits K (f4a K i) (pack (eltBits (f4Pos i))) :=
  hasBits_pinnedX_one (isRoot_f4Root i) (f4Pos_spec i).1 (f4Pos_spec i).2

theorem hasBits_f4g (j : Fin 6) : HasBits K (f4g K j) (pack (eltBits (f4GenPos j))) :=
  hasBits_pinnedX_one (isRoot_f4Gen j) (f4GenPos_spec j).1 (f4GenPos_spec j).2

theorem f4a_comm (i j : Fin 10) : f4a K i * f4a K j = f4a K j * f4a K i :=
  (((hasBits_f4a i).mul (hasBits_f4a j)).eq_iff ((hasBits_f4a j).mul (hasBits_f4a i))).2
    (f4_comm_bits i j)

theorem f4_act (j : Fin 6) (i : Fin 10) :
    f4g K j * f4a K i * (f4g K j)⁻¹ = ((List.finRange 10).map fun k =>
      f4a K k ^ (CFSG.AGLEmbedding.R3.actMatN 2 f4Mod.basis.length (f4Mod.acts.get j) k i).val
      ).prod := by
  rw [f4g_inv]
  have hl := hasBits_list_prod (fun k => f4a K k ^
      (CFSG.AGLEmbedding.R3.actMatN 2 f4Mod.basis.length (f4Mod.acts.get j) k i).val)
    (fun k => selBits (pack (eltBits (f4Pos k)))
      (CFSG.AGLEmbedding.R3.actMatN 2 f4Mod.basis.length (f4Mod.acts.get j) k i))
    (fun k => hasBits_pow_val (hasBits_f4a k) _) (List.finRange 10)
  exact ((((hasBits_f4g j).mul (hasBits_f4a i)).mul (hasBits_f4g j)).eq_iff hl).2
    (f4_act_bits j i)

theorem f4_indep (c : Fin 10 → ZMod 2)
    (h : ((List.finRange 10).map fun k => f4a K k ^ (c k).val).prod = 1) : c = 0 := by
  have hpos : ∀ i, IsRoot .F4 (f4Root i) ∧ 0 < height (f4Root i) := fun i =>
    ⟨isRoot_f4Root i, f4Root_height_pos i⟩
  have key := (positive_root_product_injectivity .F4 K f4Root f4Root_injective hpos).2
  have hl : (List.ofFn fun i => pinnedX .F4 K (f4Root i) (((c i).val : ℕ) : K)) =
      ((List.finRange 10).map fun k => f4a K k ^ (c k).val).map (adjointGroup .F4 K).subtype := by
    rw [List.ofFn_eq_map, List.map_map]
    refine List.map_congr_left fun k _ => ?_
    rw [Function.comp_apply, map_pow]
    exact (pinnedX_one_pow _ _).symm
  have h1 : (List.ofFn fun i => pinnedX .F4 K (f4Root i) (((c i).val : ℕ) : K)).prod = 1 := by
    rw [hl, ← map_list_prod, h, map_one]
  have h0 : (List.ofFn fun i => pinnedX .F4 K (f4Root i) (0 : K)).prod = 1 := by
    simp only [pinnedX_zero]
    rw [List.ofFn_const, List.prod_replicate, one_pow]
  have hd0 := key (a₁ := fun k => (((c k).val : ℕ) : K)) (a₂ := fun _ => 0) (h1.trans h0.symm)
  funext k
  have hk : (((c k).val : ℕ) : K) = 0 := congrFun hd0 k
  have h2 : 2 ∣ (c k).val := (CharP.cast_eq_zero_iff K 2 _).1 hk
  have h3 : (c k).val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt (c k))
  exact (ZMod.val_eq_zero (c k)).1 h3

end Group

end CFSG.LocalAnalysis.GLTheoremA.F4Sym
