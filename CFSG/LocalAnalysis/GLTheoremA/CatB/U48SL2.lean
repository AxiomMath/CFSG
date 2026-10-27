module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Blocks
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.PartTwo.Sec21.Item228Census4ProofCore
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Fix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockEmb_injective mem_range_blockEmb_iff)

noncomputable section

theorem isSimpleGroup_su2 : IsSimpleGroup (Su K 2 3 2) := by
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := 2)
    (f := 3) card_K
  have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K 2 3) = 2 ^ 3 :=
    CFSG.LieType.Steinberg.card_fixedSubfield card_K
  have hs : IsSimpleGroup (SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K 2 3)) :=
    CFSG.RankThree.PartTwo.Sec21.Item228Census4Proof.isSimpleGroup_SL_two_of_charTwo
      (by rw [hF]; norm_num)
  haveI := hs
  haveI : IsSimpleGroup (StatedSU 2 (2 ^ 3) K) := e.symm.isSimpleGroup
  exact (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2)
    (f := 3) card_K 2)).isSimpleGroup

theorem card_su2 : Nat.card (Su K 2 3 2) = 504 := by
  have h := CFSG.RankThree.SubgroupLists.card_statedSU_two (K := K) (r := 2) (f := 3) card_K
  rw [← Nat.card_congr (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
    (F := K) (p := 2) (f := 3) card_K 2)).toEquiv] at h
  rw [h]
  norm_num

abbrev W0 : Subgroup SU4 := (blockEmb K 2 3 4 2 0 (by norm_num)).range

theorem mem_W0_iff (g : SU4) :
    g ∈ W0 ↔ g • (Pi.single 2 1 : Fin 4 → K) = Pi.single 2 1 ∧
      g • (Pi.single 3 1 : Fin 4 → K) = Pi.single 3 1 := by
  rw [mem_range_blockEmb_iff]
  constructor
  · intro h
    exact ⟨h 2 (by simp), h 3 (by simp)⟩
  · rintro ⟨h2, h3⟩ l hl
    have : l = 2 ∨ l = 3 := by
      have := l.isLt
      by_cases h0 : l.val < 2
      · exfalso; exact hl ⟨Nat.zero_le _, by omega⟩
      · have : l.val = 2 ∨ l.val = 3 := by omega
        rcases this with h | h
        · left; exact Fin.ext h
        · right; exact Fin.ext h
    rcases this with rfl | rfl
    · exact h2
    · exact h3

theorem isSimpleGroup_W0 : IsSimpleGroup ↥W0 := by
  haveI := isSimpleGroup_su2
  exact (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := 2) (f := 3)
    (by norm_num : 0 + 2 ≤ 4))).symm.isSimpleGroup

theorem card_W0 : Nat.card ↥W0 = 504 := by
  have h := Nat.card_congr (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := 2) (f := 3)
    (by norm_num : 0 + 2 ≤ 4))).toEquiv
  exact h.symm.trans card_su2

theorem not_isMulCommutative_W0 : ¬ IsMulCommutative ↥W0 := by
  intro h
  haveI := isSimpleGroup_W0
  have hp := (Group.is_simple_iff_prime_card (α := ↥W0)).mp isSimpleGroup_W0
  rw [card_W0] at hp
  norm_num at hp

theorem three_dvd_W0 : 3 ∣ Nat.card ↥W0 := by
  rw [card_W0]; norm_num

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)

theorem ent_mul_torus (g : SU4) (a : Fin 3 → μ3) (i j : Fin 4) :
    ent (g * torusSU4 a) i j = ent g i j * ent (torusSU4 a) j j := by
  simp only [ent, Subgroup.coe_mul, Units.val_mul, coe_torusSU4, mul_diagonal, diagonal_apply_eq]

theorem ent_torus_mul (g : SU4) (a : Fin 3 → μ3) (i j : Fin 4) :
    ent (torusSU4 a * g) i j = ent (torusSU4 a) i i * ent g i j := by
  simp only [ent, Subgroup.coe_mul, Units.val_mul, coe_torusSU4, diagonal_mul, diagonal_apply_eq]

@[expose] def z0 (t : μ3) : SU4 := torusSU4 fun i => if i = 2 then t else 1

theorem z0_mem_Bsub (t : μ3) : z0 t ∈ Bsub 0 := by
  refine ⟨fun i => if i = 2 then t else 1, MonoidHom.mem_ker.2 ?_, rfl⟩
  rw [eqChar_apply, entryChar_apply, entryChar_apply]
  have h1 : (0 : Fin 3).succ = Fin.castSucc (1 : Fin 3) := rfl
  rw [h1, torusSnoc_castSucc, torusSnoc_castSucc]
  simp

theorem ent_z0 (t : μ3) : ent (z0 t) 0 0 = 1 ∧ ent (z0 t) 1 1 = 1 ∧ ent (z0 t) 2 2 = (t : Kˣ) ∧
    ent (z0 t) 3 3 = ((t : Kˣ)⁻¹ : Kˣ) := by
  have h3 : ent (z0 t) 3 3 = ((((∏ i : Fin 3, ((if i = 2 then t else 1 : μ3) : Kˣ))⁻¹ : Kˣ)) : K) :=
    ent_torus_last (fun i : Fin 3 => if i = 2 then t else 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ent_torus_castSucc (fun i : Fin 3 => if i = 2 then t else 1) 0
    simpa [z0] using this
  · have := ent_torus_castSucc (fun i : Fin 3 => if i = 2 then t else 1) 1
    simpa [z0] using this
  · have := ent_torus_castSucc (fun i : Fin 3 => if i = 2 then t else 1) 2
    simpa [z0] using this
  · rw [h3]; simp [Fin.prod_univ_three]

theorem ent_mul_z0 (g : SU4) (t : μ3) (i j : Fin 4) :
    ent (g * z0 t) i j = ent g i j * ent (z0 t) j j :=
  ent_mul_torus g (fun i : Fin 3 => if i = 2 then t else 1) i j

theorem ent_z0_mul (g : SU4) (t : μ3) (i j : Fin 4) :
    ent (z0 t * g) i j = ent (z0 t) i i * ent g i j :=
  ent_torus_mul g (fun i : Fin 3 => if i = 2 then t else 1) i j

theorem exists_smul_single_two {g : SU4} {t : μ3} (ht : (t : Kˣ) ≠ 1) (hg : g * z0 t = z0 t * g) :
    ∃ c : K, g • (Pi.single 2 1 : Fin 4 → K) = c • (Pi.single 2 1 : Fin 4 → K) := by
  have ht' : ((t : Kˣ) : K) ≠ 1 := fun h => ht (Units.ext h)
  have ht3 : ((t : Kˣ) : K) ^ 3 = 1 := by
    have h3 : ((t : Kˣ)) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp t.2
    exact congrArg (fun u : Kˣ => (u : K)) h3
  have ht2 : ((t : Kˣ) : K) ^ 2 - 1 ≠ 0 := by
    intro h
    apply ht'
    have h2 : ((t : Kˣ) : K) ^ 2 = 1 := by linear_combination h
    calc ((t : Kˣ) : K) = ((t : Kˣ) : K) * ((t : Kˣ) : K) ^ 2 := by rw [h2, mul_one]
      _ = ((t : Kˣ) : K) ^ 3 := by ring
      _ = 1 := ht3
  have hsub : ((t : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr ht'
  obtain ⟨e0, e1, e2, e3⟩ := ent_z0 t
  have key : ∀ i : Fin 4, i ≠ 2 → ent g i 2 = 0 := by
    intro i hi
    have h := congrArg (fun z : SU4 => ent z i 2) hg
    simp only [ent_mul_z0, ent_z0_mul, e2] at h
    have hcases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hcases i with rfl | rfl | rfl | rfl
    · simp only [e0] at h
      have : ent g 0 2 * (((t : Kˣ) : K) - 1) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_right hsub
    · simp only [e1] at h
      have : ent g 1 2 * (((t : Kˣ) : K) - 1) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_right hsub
    · exact absurd rfl hi
    · simp only [e3] at h
      have hti : ((((t : Kˣ)⁻¹ : Kˣ)) : K) * ((t : Kˣ) : K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel]; rfl
      have : ent g 3 2 * (((t : Kˣ) : K) ^ 2 - 1) = 0 := by
        calc ent g 3 2 * (((t : Kˣ) : K) ^ 2 - 1) =
            ent g 3 2 * ((t : Kˣ) : K) * ((t : Kˣ) : K) - ent g 3 2 := by ring
          _ = ((((t : Kˣ)⁻¹ : Kˣ)) : K) * ent g 3 2 * ((t : Kˣ) : K) - ent g 3 2 := by rw [h]
          _ = 0 := by
            have : ((((t : Kˣ)⁻¹ : Kˣ)) : K) * ent g 3 2 * ((t : Kˣ) : K) =
              ent g 3 2 * (((((t : Kˣ)⁻¹ : Kˣ)) : K) * ((t : Kˣ) : K)) := by ring
            rw [this, hti]; ring
      exact (mul_eq_zero.mp this).resolve_right ht2
  refine ⟨ent g 2 2, ?_⟩
  funext a
  rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one]
  show ent g a 2 = ent g 2 2 * (Pi.single 2 1 : Fin 4 → K) a
  by_cases ha : a = 2
  · subst ha; simp
  · simp [Pi.single_apply, ha, key a ha]

theorem forward_W0 {t : μ3} (ht : (t : Kˣ) ≠ 1) {g : SU4} (hgJ : g ∈ Jblk)
    (hcomm : g * z0 t = z0 t * g) {h : SU4} (hh : h ∈ W0) : g * h * g⁻¹ ∈ W0 := by
  rw [mem_W0_iff] at hh ⊢
  obtain ⟨h2, h3⟩ := hh
  have hg3 : g • (Pi.single 3 1 : Fin 4 → K) = Pi.single 3 1 := (mem_Jblk_iff g).1 hgJ
  have hginv3 : g⁻¹ • (Pi.single 3 1 : Fin 4 → K) = Pi.single 3 1 := by
    rw [inv_smul_eq_iff]; exact hg3.symm
  have hcomm' : g⁻¹ * z0 t = z0 t * g⁻¹ := (show Commute g (z0 t) from hcomm).inv_left.eq
  obtain ⟨c, hc⟩ := exists_smul_single_two ht hcomm'
  constructor
  · rw [mul_smul, mul_smul, hc]
    have h1 : h • (c • (Pi.single 2 1 : Fin 4 → K)) = c • (Pi.single 2 1 : Fin 4 → K) := by
      rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_smul,
        ← CFSG.ClassicalGroups.Unitary.smul_def, h2]
    rw [h1, ← hc, smul_inv_smul]
  · rw [mul_smul, mul_smul, hginv3, h3, hg3]

theorem normalizes_W0 {t : μ3} (ht : (t : Kˣ) ≠ 1) {g : SU4} (hgJ : g ∈ Jblk)
    (hcomm : ∀ b ∈ Bsub 0, g * b = b * g) : g ∈ Subgroup.normalizer (W0 : Set SU4) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hz := hcomm _ (z0_mem_Bsub t)
  have hz' : g⁻¹ * z0 t = z0 t * g⁻¹ := (show Commute g (z0 t) from hz).inv_left.eq
  constructor
  · exact forward_W0 ht hgJ hz
  · intro hu
    have := forward_W0 ht (Jblk.inv_mem hgJ) hz' hu
    simpa [mul_assoc] using this

theorem W0_le_Jblk : W0 ≤ Jblk := fun x hx => (mem_Jblk_iff x).2 ((mem_W0_iff x).1 hx).2

theorem W0_comm_Bsub {b : SU4} (hb : b ∈ Bsub 0) {w : SU4} (hw : w ∈ W0) : b * w = w * b := by
  obtain ⟨X, rfl⟩ := hw
  exact mem_Bsub_comm_block 0 hb X

theorem exists_ne_one_mu3 : ∃ t : μ3, (t : Kˣ) ≠ 1 := by
  have h3 : 1 < Nat.card μ3 := by rw [card_μ3]; norm_num
  haveI : Nontrivial μ3 := Finite.one_lt_card_iff_nontrivial.1 h3
  obtain ⟨t, ht⟩ := exists_ne (1 : μ3)
  exact ⟨t, fun h => ht (Subtype.ext h)⟩

theorem yStd_mem_Bsub (t : μ3) : yStd t ∈ Bsub 0 := by
  refine ⟨fun _ => t, MonoidHom.mem_ker.2 ?_, rfl⟩
  rw [eqChar_apply, entryChar_apply, entryChar_apply]
  have h1 : (0 : Fin 3).succ = Fin.castSucc (1 : Fin 3) := rfl
  rw [h1, torusSnoc_castSucc, torusSnoc_castSucc]
  simp

theorem yStd_ne_one {t : μ3} (ht : (t : Kˣ) ≠ 1) : yStd t ≠ 1 := by
  intro h
  have h0 := congrArg (fun z : SU4 => ent z (Fin.castSucc 0) (Fin.castSucc 0)) h
  have := ent_torus_castSucc (fun _ : Fin 3 => t) 0
  simp only [ent] at h0 this
  apply ht
  apply Units.ext
  have h00 : ((((yStd t : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc 0)
      (Fin.castSucc 0)) = (((1 : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        (Fin.castSucc 0) (Fin.castSucc 0) := h0
  rw [yStd, this] at h00
  simpa using h00

theorem card_Bsub_zero : Nat.card (Bsub 0) = 9 := by
  obtain ⟨t, ht⟩ := exists_ne_one_mu3
  have hge := card_Bsub 0
  have hle : Bsub 0 ≤ Dstd := Bsub_le_Dstd 0
  have hne : Bsub 0 ≠ Dstd := by
    intro heq
    have hd : torusSU4 (fun i => if i = 0 then t else 1) ∈ Bsub 0 := by
      rw [heq]; exact ⟨_, rfl⟩
    obtain ⟨a, ha, hae⟩ := hd
    have : a = fun i => if i = 0 then t else 1 := torusSU4_injective hae
    rw [this] at ha
    have ha' := MonoidHom.mem_ker.1 ha
    rw [eqChar_apply, entryChar_apply, entryChar_apply] at ha'
    have h1 : (0 : Fin 3).succ = Fin.castSucc (1 : Fin 3) := rfl
    rw [h1, torusSnoc_castSucc, torusSnoc_castSucc] at ha'
    simp at ha'
    exact ht (by simpa using ha')
  have hdvd : Nat.card (Bsub 0) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_Dstd] at this
  have hlt' : Nat.card (Bsub 0) < 27 := by
    have h1 := Subgroup.card_le_of_le hle
    rw [card_Dstd] at h1
    exact lt_of_le_of_ne h1 (fun h => hne (Subgroup.eq_of_le_of_card_ge hle (by rw [card_Dstd]; omega)))
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hc] at hge hlt' ⊢
  interval_cases i <;> simp_all

variable {G : Type} [Group G] [Finite G]

theorem layer_third (f : SU4 →* G) (hf : Function.Injective f) (J : Subgroup G)
    (hJ : J = Jblk.map f) : GLAPLayer 3 (J ⊓ Subgroup.centralizer (((Bsub 0).map f : Subgroup G) :
      Set G)) ≠ ⊥ := by
  obtain ⟨t, ht⟩ := exists_ne_one_mu3
  set W : Subgroup G := W0.map f with hW
  have hWJ : W ≤ J := by
    rw [hJ]; exact Subgroup.map_mono W0_le_Jblk
  have hWc : W ≤ Subgroup.centralizer (((Bsub 0).map f : Subgroup G) : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, W0_comm_Bsub hb hw]
  have hWY : W ≤ J ⊓ Subgroup.centralizer (((Bsub 0).map f : Subgroup G) : Set G) :=
    le_inf hWJ hWc
  have hnorm : (J ⊓ Subgroup.centralizer (((Bsub 0).map f : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (W : Set G) := by
    intro j hj
    have hjJ : j ∈ J := hj.1
    have hjc : j ∈ Subgroup.centralizer (((Bsub 0).map f : Subgroup G) : Set G) := hj.2
    rw [hJ] at hjJ
    obtain ⟨g, hg, rfl⟩ := hjJ
    have hcomm : ∀ b ∈ Bsub 0, g * b = b * g := by
      intro b hb
      have := Subgroup.mem_centralizer_iff.1 hjc (f b) ⟨b, hb, rfl⟩
      apply hf
      rw [map_mul, map_mul]
      exact this.symm
    have hgn := normalizes_W0 ht hg hcomm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgn w).1 hw, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨u, hu, hue⟩
      have hgn' : g⁻¹ ∈ Subgroup.normalizer (W0 : Set SU4) := Subgroup.inv_mem _ hgn
      refine ⟨g⁻¹ * u * g, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 hgn' u).1 hu
        simpa using this
      · rw [map_mul, map_mul, map_inv, hue]
        group
  have hn : (W.subgroupOf (J ⊓ Subgroup.centralizer (((Bsub 0).map f : Subgroup G) : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).2 hnorm
  haveI : IsSimpleGroup ↥W := by
    haveI := isSimpleGroup_W0
    exact (Subgroup.equivMapOfInjective W0 f hf).symm.isSimpleGroup
  have hna : ¬ IsMulCommutative ↥W := by
    intro hc
    apply not_isMulCommutative_W0
    exact ⟨⟨fun a b => by
      have := hc.is_comm.comm ((Subgroup.equivMapOfInjective W0 f hf) a)
        ((Subgroup.equivMapOfInjective W0 f hf) b)
      exact (Subgroup.equivMapOfInjective W0 f hf).injective (by simpa using this)⟩⟩
  have h3 : 3 ∣ Nat.card ↥W := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective W0 f hf).toEquiv]
    exact three_dvd_W0
  exact layer_ne_bot_of_normal_simple hWY hn hna h3

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
