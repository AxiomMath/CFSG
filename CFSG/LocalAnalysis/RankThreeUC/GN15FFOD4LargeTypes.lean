module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4TensorModel
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeLevi
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeRank
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Types

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section General

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem isChevType_congr_chi {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {ρ : Representation k (adjointGroup τ K) W} {y : W} {χ χ' : adjointGroup τ K → k}
    {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    (h : ∀ x ∈ (chevDatum τ K 2 hw).H, χ x = χ' x) : IsChevType τ K 2 hw ρ y χ' J := by
  refine ⟨ht.1, ht.2.1, fun x hx => ?_, fun i => ?_⟩
  · rw [ht.2.2.1 x hx, h x hx]
  · rw [ht.2.2.2 i]
    exact and_congr (forall_congr' fun t => by rw [h _ (dC_mem_H i t)]) Iff.rfl

private theorem H_eq_closure_dC :
    (chevDatum τ K 2 hw).H =
      Subgroup.closure (Set.range fun p : Fin τ.rank × Kˣ => dC τ K p.1 p.2) := by
  rw [show (chevDatum τ K 2 hw).H = (torusGroup τ K).subgroupOf (adjointGroup τ K) from rfl]
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : (x : ModGL τ K) ∈
        Subgroup.closure (Set.range fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) := hx
    have hex : ∃ y ∈ Subgroup.closure (Set.range fun p : Fin τ.rank × Kˣ => dC τ K p.1 p.2),
        (y : ModGL τ K) = (x : ModGL τ K) := by
      refine Subgroup.closure_induction (p := fun h _ =>
        ∃ y ∈ Subgroup.closure (Set.range fun p : Fin τ.rank × Kˣ => dC τ K p.1 p.2),
          (y : ModGL τ K) = h) ?_ ?_ ?_ ?_ hx'
      · rintro _ ⟨⟨i, t⟩, rfl⟩
        exact ⟨dC τ K i t, Subgroup.subset_closure ⟨(i, t), rfl⟩, rfl⟩
      · exact ⟨1, Subgroup.one_mem _, rfl⟩
      · rintro a b ha hb ⟨ya, hya, rfl⟩ ⟨yb, hyb, rfl⟩
        exact ⟨ya * yb, mul_mem hya hyb, rfl⟩
      · rintro a ha ⟨ya, hya, rfl⟩
        exact ⟨ya⁻¹, inv_mem hya, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hex
    rwa [show y = x from Subtype.ext hxy] at hy
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact dC_mem_H (hw := hw) i t

theorem chi_eq_of_dC {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [AddCommGroup W']
    [Module k W'] {ρ : Representation k (adjointGroup τ K) W}
    {ρ' : Representation k (adjointGroup τ K) W'} {y : W} {y' : W'}
    {χ χ' : adjointGroup τ K → k} {J J' : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (ht' : IsChevType τ K 2 hw ρ' y' χ' J')
    (hd : ∀ (i : Fin τ.rank) (z : Kˣ), χ (dC τ K i z) = χ' (dC τ K i z)) :
    ∀ x ∈ (chevDatum τ K 2 hw).H, χ x = χ' x := by
  have hχ1 : χ 1 = 1 := by
    have h1 : ρ (1 : adjointGroup τ K) y = χ 1 • y := ht.2.2.1 1 (Subgroup.one_mem _)
    rw [map_one, Module.End.one_apply] at h1
    have h2 : (1 : k) • y = χ 1 • y := by rw [one_smul, ← h1]
    exact (smul_left_injective k ht.2.1 h2).symm
  have hχ1' : χ' 1 = 1 := by
    have h1 : ρ' (1 : adjointGroup τ K) y' = χ' 1 • y' := ht'.2.2.1 1 (Subgroup.one_mem _)
    rw [map_one, Module.End.one_apply] at h1
    have h2 : (1 : k) • y' = χ' 1 • y' := by rw [one_smul, ← h1]
    exact (smul_left_injective k ht'.2.1 h2).symm
  have hχmul : ∀ a ∈ (chevDatum τ K 2 hw).H, ∀ b ∈ (chevDatum τ K 2 hw).H,
      χ (a * b) = χ a * χ b := by
    intro a ha b hb
    have h1 : ρ (a * b) y = χ (a * b) • y := ht.2.2.1 _ (mul_mem ha hb)
    have h2 : ρ (a * b) y = (χ a * χ b) • y := by
      rw [map_mul, Module.End.mul_apply, ht.2.2.1 b hb, map_smul,
        ht.2.2.1 a ha, smul_smul, mul_comm]
    exact smul_left_injective k ht.2.1 (h1.symm.trans h2)
  have hχmul' : ∀ a ∈ (chevDatum τ K 2 hw).H, ∀ b ∈ (chevDatum τ K 2 hw).H,
      χ' (a * b) = χ' a * χ' b := by
    intro a ha b hb
    have h1 : ρ' (a * b) y' = χ' (a * b) • y' := ht'.2.2.1 _ (mul_mem ha hb)
    have h2 : ρ' (a * b) y' = (χ' a * χ' b) • y' := by
      rw [map_mul, Module.End.mul_apply, ht'.2.2.1 b hb, map_smul,
        ht'.2.2.1 a ha, smul_smul, mul_comm]
    exact smul_left_injective k ht'.2.1 (h1.symm.trans h2)
  have hχinv : ∀ a ∈ (chevDatum τ K 2 hw).H, χ a⁻¹ = (χ a)⁻¹ := by
    intro a ha
    have h := hχmul a⁻¹ (inv_mem ha) a ha
    rw [inv_mul_cancel, hχ1] at h
    exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h.symm)
  have hχinv' : ∀ a ∈ (chevDatum τ K 2 hw).H, χ' a⁻¹ = (χ' a)⁻¹ := by
    intro a ha
    have h := hχmul' a⁻¹ (inv_mem ha) a ha
    rw [inv_mul_cancel, hχ1'] at h
    exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h.symm)
  have hHcl := H_eq_closure_dC (τ := τ) (K := K) (hw := hw)
  intro x hx
  rw [hHcl] at hx
  refine Subgroup.closure_induction (p := fun x _ => χ x = χ' x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨i, t⟩, rfl⟩
    exact hd i t
  · exact hχ1.trans hχ1'.symm
  · intro a b ha hb iha ihb
    rw [← hHcl] at ha hb
    rw [hχmul a ha b hb, hχmul' a ha b hb, iha, ihb]
  · intro a ha iha
    rw [← hHcl] at ha
    rw [hχinv a ha, hχinv' a ha, iha]

private theorem chi_eq_one_of_dC {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {ρ : Representation k (adjointGroup τ K) W} {y : W} {χ : adjointGroup τ K → k}
    {J : Finset (Fin τ.rank)} (ht : IsChevType τ K 2 hw ρ y χ J)
    (hd : ∀ (i : Fin τ.rank) (z : Kˣ), χ (dC τ K i z) = 1) :
    ∀ x ∈ (chevDatum τ K 2 hw).H, χ x = 1 := by
  have hχ1 : χ 1 = 1 := by
    have h1 : ρ (1 : adjointGroup τ K) y = χ 1 • y := ht.2.2.1 1 (Subgroup.one_mem _)
    rw [map_one, Module.End.one_apply] at h1
    have h2 : (1 : k) • y = χ 1 • y := by rw [one_smul, ← h1]
    exact (smul_left_injective k ht.2.1 h2).symm
  have hχmul : ∀ a ∈ (chevDatum τ K 2 hw).H, ∀ b ∈ (chevDatum τ K 2 hw).H,
      χ (a * b) = χ a * χ b := by
    intro a ha b hb
    have h1 : ρ (a * b) y = χ (a * b) • y := ht.2.2.1 _ (mul_mem ha hb)
    have h2 : ρ (a * b) y = (χ a * χ b) • y := by
      rw [map_mul, Module.End.mul_apply, ht.2.2.1 b hb, map_smul,
        ht.2.2.1 a ha, smul_smul, mul_comm]
    exact smul_left_injective k ht.2.1 (h1.symm.trans h2)
  have hχinv : ∀ a ∈ (chevDatum τ K 2 hw).H, χ a⁻¹ = (χ a)⁻¹ := by
    intro a ha
    have h := hχmul a⁻¹ (inv_mem ha) a ha
    rw [inv_mul_cancel, hχ1] at h
    exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h.symm)
  have hHcl := H_eq_closure_dC (τ := τ) (K := K) (hw := hw)
  intro x hx
  rw [hHcl] at hx
  refine Subgroup.closure_induction (p := fun x _ => χ x = 1) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨i, t⟩, rfl⟩
    exact hd i t
  · exact hχ1
  · intro a b ha hb iha ihb
    rw [← hHcl] at ha hb
    rw [hχmul a ha b hb, iha, ihb, mul_one]
  · intro a ha iha
    rw [← hHcl] at ha
    rw [hχinv a ha, iha, inv_one]

private theorem isChevType_trivial_charTwo [inst : Fintype K] {k : Type*} [Field k]
    [Algebra K k] [CharP k 2] :
    IsChevType τ K 2 hw (Representation.trivial k (adjointGroup τ K) k) 1 (fun _ => 1)
      Finset.univ := by
  let ρ₀ : Representation k (adjointGroup τ K) k := Representation.trivial k (adjointGroup τ K) k
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  set m : ℕ := (n : ℕ) with hm
  have hcard : Fintype.card K = 2 ^ m := by simpa using hn
  have hm1 : 1 ≤ m := by
    have := n.pos
    omega
  refine ⟨?_, one_ne_zero, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u _
    rfl
  · intro h _
    show (1 : k) = (1 : k) • (1 : k)
    rw [one_smul]
  · intro i
    refine iff_of_true (Finset.mem_univ i) ⟨fun _ => rfl, ?_⟩
    have hterm : ∀ c : K, (ρ₀ (xC τ K i c * nC τ K i)) (1 : k) = 1 := fun c => rfl
    rw [heckeT_chevDatum]
    calc ∑ c : K, (ρ₀ (xC τ K i c * nC τ K i)) (1 : k)
        = ∑ _c : K, (1 : k) := Finset.sum_congr rfl fun c _ => hterm c
      _ = (Finset.univ : Finset K).card • (1 : k) := Finset.sum_const _
      _ = 0 := by
          rw [Finset.card_univ, hcard]
          have h0 : ((2 ^ m : ℕ) : k) = 0 := by
            rw [Nat.cast_pow, CharP.cast_eq_zero k 2, zero_pow (by omega)]
          rw [show (2 ^ m : ℕ) • (1 : k) = ((2 ^ m : ℕ) : k) • (1 : k) by
            rw [Nat.cast_smul_eq_nsmul]]
          rw [h0, zero_smul]

theorem eq_of_isChevType_univ_of_charTwo {k W : Type*} [Field k] [Algebra K k] [CharP k 2]
    [AddCommGroup W] [Module k W] {ρ : Representation k (adjointGroup τ K) W}
    (hρ : IsSimpleRep ρ) {y : W} {χ : adjointGroup τ K → k}
    (ht : IsChevType τ K 2 hw ρ y χ Finset.univ) (g : adjointGroup τ K) (w : W) : ρ g w = w := by
  classical
  let fK : Fintype K := Fintype.ofFinite K
  let ρ₀ : Representation k (adjointGroup τ K) k := Representation.trivial k (adjointGroup τ K) k
  have hρ₀ : IsSimpleRep ρ₀ := by
    refine ⟨inferInstance, fun W' _ => ?_⟩
    by_cases hbot : W' = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    refine eq_top_iff.mpr fun z _ => ?_
    have hz : z = (z / x) • x := by rw [smul_eq_mul, div_mul_cancel₀ z hx0]
    rw [hz]
    exact W'.smul_mem (z / x) hxW
  have ht₀ : IsChevType τ K 2 hw ρ₀ 1 (fun _ => 1) Finset.univ :=
    isChevType_trivial_charTwo (inst := fK)
  have hd : ∀ (i : Fin τ.rank) (z : Kˣ), χ (dC τ K i z) = 1 :=
    fun i z => ht.subset (Finset.mem_univ i) z
  have hχ : ∀ x ∈ (chevDatum τ K 2 hw).H, χ x = (fun _ => (1 : k)) x :=
    chi_eq_one_of_dC ht hd
  have ht1 : IsChevType τ K 2 hw ρ y (fun _ => 1) Finset.univ :=
    isChevType_congr_chi ht hχ
  obtain ⟨β, hβ⟩ := iso_of_isChevType (p := 2) hρ hρ₀ ht1 ht₀
  have hb : β (ρ g w) = β w := by
    rw [hβ g w]
    simp [ρ₀, Representation.trivial]
  exact β.injective hb

end General

section D4

private instance : OfNat (Fin Tag.D4.rank) 0 := ⟨(0 : Fin 4)⟩
private instance : OfNat (Fin Tag.D4.rank) 1 := ⟨(1 : Fin 4)⟩
private instance : OfNat (Fin Tag.D4.rank) 3 := ⟨(3 : Fin 4)⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
  {k V : Type} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V] [Module k V]

private theorem triality_dC (i : Fin Tag.D4.rank) (t : Kˣ) :
    triality K (dC .D4 K i t) = dC .D4 K (TwistTag.D4.perm i) t := by
  have h1 : triality K (dC .D4 K i t) =
      twistC TwistTag.D4 K (RingHom.id K) (torusElement TwistTag.D4.tag K i t) := rfl
  rw [h1]
  rw [twistC_torusElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i t]
  rfl

omit [CharP K 2] in
private theorem triality_xC_mul_nC (i : Fin Tag.D4.rank) (c : K) :
    triality K (xC .D4 K i c * nC .D4 K i) =
      xC .D4 K (TwistTag.D4.perm i) c * nC .D4 K (TwistTag.D4.perm i) := by
  rw [map_mul]
  congr 1
  · simp only [triality]
    exact twistC_xElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i c
  · simp only [triality]
    exact twistC_weylElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i

private theorem heckeT_comp_triality {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {ρ : Representation k (adjointGroup .D4 K) W} (i : Fin Tag.D4.rank) (y : W) :
    (chevDatum .D4 K 2 hw).heckeT (ρ.comp (triality K).toMonoidHom) i y
      = (chevDatum .D4 K 2 hw).heckeT ρ (TwistTag.D4.perm i) y := by
  have : Fintype K := Fintype.ofFinite K
  rw [heckeT_chevDatum (V := W) (ρ := ρ.comp (triality K).toMonoidHom) (i := i) (v := y),
    heckeT_chevDatum (V := W) (ρ := ρ) (i := TwistTag.D4.perm i) (v := y)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← triality_xC_mul_nC i c]
  rfl

private abbrev trialityPerm : Equiv.Perm (Fin Tag.D4.rank) := TwistTag.D4.perm

private theorem triality_xC_mul_nC_perm (i : Fin Tag.D4.rank) (c : K) :
    triality K (xC .D4 K i c * nC .D4 K i) =
      xC .D4 K (trialityPerm i) c * nC .D4 K (trialityPerm i) := by
  rw [map_mul]
  congr 1
  · simp only [triality]
    exact twistC_xElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i c
  · simp only [triality]
    exact twistC_weylElement (t := TwistTag.D4) (K := K) (σ := RingHom.id K) i

private theorem heckeT_comp_triality_perm {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {ρ : Representation k (adjointGroup .D4 K) W} (i : Fin Tag.D4.rank) (y : W) :
    (chevDatum .D4 K 2 hw).heckeT (ρ.comp (triality K).toMonoidHom) i y
      = (chevDatum .D4 K 2 hw).heckeT ρ (trialityPerm i) y := by
  have : Fintype K := Fintype.ofFinite K
  rw [heckeT_chevDatum (V := W) (ρ := ρ.comp (triality K).toMonoidHom) (i := i) (v := y),
    heckeT_chevDatum (V := W) (ρ := ρ) (i := trialityPerm i) (v := y)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← triality_xC_mul_nC_perm i c]
  rfl

private theorem isChevType_comp_triality_chi_perm' {ρ : Representation k (adjointGroup .D4 K) V}
    {y : V} {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)}
    (ht : IsChevType .D4 K 2 hw ρ y χ J) :
    IsChevType .D4 K 2 hw (ρ.comp (triality K).toMonoidHom) y (fun x => χ (triality K x))
      (J.map trialityPerm.symm.toEmbedding) := by
  have hσ : Function.Surjective (RingHom.id K) := fun x => ⟨x, rfl⟩
  refine ⟨?_, ht.2.1, ?_, fun i => ?_⟩
  · intro u hu
    have hFu : (triality K) u ∈ (chevDatum .D4 K 2 hw).U := by
      show (twistHom TwistTag.D4 K (RingHom.id K) (u : ModGL .D4 K)) ∈ posUnipotent .D4 K
      exact twistHom_mem_posUnipotent (t := TwistTag.D4) (K := K) (σ := RingHom.id K) hσ hu
    have h1 := ht.1 _ hFu
    simpa using h1
  · intro h hh
    have hFh : (triality K) h ∈ (chevDatum .D4 K 2 hw).H := by
      show (twistHom TwistTag.D4 K (RingHom.id K) (h : ModGL .D4 K)) ∈ torusGroup .D4 K
      exact twistHom_mem_torusGroup (t := TwistTag.D4) (K := K) (σ := RingHom.id K) hh
    have h1 := ht.2.2.1 _ hFh
    simpa using h1
  · have hmem : i ∈ J.map trialityPerm.symm.toEmbedding ↔ trialityPerm i ∈ J :=
      Finset.mem_map_equiv
    refine hmem.trans ?_
    refine (ht.2.2.2 (trialityPerm i)).trans ?_
    refine and_congr ?_ ?_
    · refine forall_congr' fun t => ?_
      exact (iff_of_eq (congrArg (fun x => χ x = 1) (triality_dC i t))).symm
    · rw [heckeT_comp_triality_perm]

private theorem isChevType_comp_triality_chi_erase {ρ : Representation k (adjointGroup .D4 K) V}
    {y : V} {χ : adjointGroup .D4 K → k} {a b : Fin Tag.D4.rank}
    (ht : IsChevType .D4 K 2 hw ρ y χ (Finset.univ.erase a))
    (h : trialityPerm.symm a = b) :
    IsChevType .D4 K 2 hw (ρ.comp (triality K).toMonoidHom) y
      (fun x => χ (triality K x)) (Finset.univ.erase b) := by
  have hbase := isChevType_comp_triality_chi_perm' ht
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, fun i => ?_⟩
  have hmemiff : (i ∈ (Finset.univ : Finset (Fin Tag.D4.rank)).erase b) ↔
      (trialityPerm i ∈ (Finset.univ : Finset (Fin Tag.D4.rank)).erase a) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hi hpi
      apply hi
      rw [← h, ← hpi]
      exact (Equiv.symm_apply_apply trialityPerm i).symm
    · intro hpi hi
      apply hpi
      rw [hi, ← h]
      exact Equiv.apply_symm_apply trialityPerm a
  have hmap : trialityPerm i ∈ (Finset.univ : Finset (Fin Tag.D4.rank)).erase a ↔
      ((∀ t : Kˣ, (fun x => χ (triality K x)) (dC .D4 K i t) = 1) ∧
        (chevDatum .D4 K 2 hw).heckeT (ρ.comp (triality K).toMonoidHom) i y = 0) :=
    (Finset.mem_map_equiv).symm.trans (hbase.2.2.2 i)
  exact hmemiff.trans hmap

private theorem exists_iso_of_dC_match {S : Finset ℕ}
    {ρ : Representation k (adjointGroup .D4 K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup .D4 K → k} {e : Fin Tag.D4.rank}
    (ht : IsChevType .D4 K 2 hw ρ y χ (Finset.univ.erase e))
    {ρ' : Representation k (adjointGroup .D4 K) ((S → Fin 4 ⊕ Fin 4) → k)}
    (hρ' : IsSimpleRep ρ')
    {χ' : adjointGroup .D4 K → k}
    (ht' : IsChevType .D4 K 2 hw ρ' (hwVec k S) χ' (Finset.univ.erase e))
    (hd : ∀ (i : Fin Tag.D4.rank) (z : Kˣ), χ (dC .D4 K i z) = χ' (dC .D4 K i z)) :
    ∃ β : V ≃ₗ[k] ((S → Fin 4 ⊕ Fin 4) → k), ∀ (x : adjointGroup .D4 K) (w : V),
      β (ρ x w) = ρ' x (β w) := by
  have hχeq := chi_eq_of_dC (hw := hw) ht ht' hd
  have ht1 := isChevType_congr_chi (hw := hw) ht hχeq
  exact iso_of_isChevType (p := 2) hρ hρ' ht1 ht'

private theorem exists_iso_tensorD4_of_end' {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .D4 K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup .D4 K → k} {e : Fin Tag.D4.rank}
    (he : e = (0 : Fin 4) ∨ e = (3 : Fin 4) ∨ e = (1 : Fin 4))
    (ht : IsChevType .D4 K 2 hw ρ y χ (Finset.univ.erase e)) :
    ∃ (S : Finset ℕ) (σ : adjointGroup .D4 K ≃* adjointGroup .D4 K)
      (β : V ≃ₗ[k] ((S → Fin 4 ⊕ Fin 4) → k)),
      S.Nonempty ∧ (∀ b ∈ S, b < n) ∧
      (∀ z : Kˣ, χ (dC .D4 K e z) = (algebraMap K k (z : K)) ^ (∑ b ∈ S, 2 ^ b)) ∧
      ∀ (x : adjointGroup .D4 K) (w : V), β (ρ x w) = tensorD4 (K := K) k S (σ x) (β w) := by
  classical
  obtain ⟨S, hS, hχe, -, hJ0, -⟩ := string_of_highest (hw := hw) hK hρ ht e
  have hSne : S.Nonempty := string_nonempty (s := e) (J' := S) hn hK ht (by simp) hχe hJ0
  have htS : IsChevType .D4 K 2 hw (tensorD4 (K := K) k S) (hwVec k S)
      (chiT (K := K) k S) (Finset.univ.erase (0 : Fin Tag.D4.rank)) :=
    isChevType_tensorD4 k (hw := hw) hK S hS hSne
  rcases he with h0 | h3 | h1
  · subst e
    have hd : ∀ (i : Fin Tag.D4.rank) (z : Kˣ),
        χ (dC .D4 K i z) = chiT (K := K) k S (dC .D4 K i z) := by
      intro i z
      by_cases hi : i = 0
      · rw [hi]
        exact (hχe z).trans (chiT_dC_zero (K := K) k S z).symm
      · have hmem : i ∈ Finset.univ.erase (0 : Fin Tag.D4.rank) := by
          rw [Finset.mem_erase]
          exact ⟨hi, Finset.mem_univ i⟩
        exact (ht.subset hmem z).trans (chiT_dC_of_ne (K := K) k S hi z).symm
    let h := exists_iso_of_dC_match (S := S) hρ (y := y) ht
      (ρ' := tensorD4 (K := K) k S) (isSimpleRep_tensorD4 k hK S hS) htS hd
    exact ⟨S, MulEquiv.refl _, Classical.choose h, hSne, hS, hχe,
      fun x w => by rw [Classical.choose_spec h x w]; rfl⟩
  · subst e
    have hπ : trialityPerm 3 = 0 := by decide +kernel
    have h1 : trialityPerm.symm 0 = 3 := by decide +kernel
    have ht1 := isChevType_comp_triality_chi_erase (K := K) (hw := hw)
      (ρ := tensorD4 (K := K) k S) (y := hwVec k S) (χ := chiT (K := K) k S)
      (a := (0 : Fin Tag.D4.rank)) (b := (3 : Fin Tag.D4.rank)) htS h1
    have hd : ∀ (i : Fin Tag.D4.rank) (z : Kˣ),
        χ (dC .D4 K i z) = chiT (K := K) k S ((triality K) (dC .D4 K i z)) := by
      intro i z
      by_cases hi : i = 3
      · have hx : (triality K) (dC .D4 K 3 z) = dC .D4 K 0 z :=
          (triality_dC 3 z).trans (congrArg (fun w => dC .D4 K w z) hπ)
        rw [hi]
        exact (hχe z).trans
          (((chiT_dC_zero (K := K) k S z).symm).trans (congrArg (chiT (K := K) k S) hx).symm)
      · have hmem : i ∈ Finset.univ.erase (3 : Fin Tag.D4.rank) := by
          rw [Finset.mem_erase]
          exact ⟨hi, Finset.mem_univ i⟩
        have hx : (triality K) (dC .D4 K i z) = dC .D4 K (trialityPerm i) z :=
          triality_dC i z
        have hpi : trialityPerm i ≠ 0 := by
          intro h0
          apply hi
          have h3 : i = trialityPerm.symm 0 := by
            rw [← h0, Equiv.symm_apply_apply]
          rwa [h1] at h3
        exact (ht.subset hmem z).trans
          (((hx.symm ▸ chiT_dC_of_ne (K := K) k S (i := trialityPerm i) hpi z)).symm)
    let h := exists_iso_of_dC_match (S := S) hρ (y := y) ht
      (ρ' := (tensorD4 (K := K) k S).comp (triality K).toMonoidHom)
      (isSimpleRep_comp (isSimpleRep_tensorD4 k hK S hS) (triality K)) ht1 hd
    exact ⟨S, triality K, Classical.choose h, hSne, hS, hχe,
      fun x w => by rw [Classical.choose_spec h x w]; rfl⟩
  · subst e
    have hπ1 : trialityPerm 1 = 3 := by decide +kernel
    have hπ3 : trialityPerm 3 = 0 := by decide +kernel
    have h1 : trialityPerm.symm 0 = 3 := by decide +kernel
    have h2 : trialityPerm.symm 3 = 1 := by decide +kernel
    have ht1 := isChevType_comp_triality_chi_erase (K := K) (hw := hw)
      (ρ := tensorD4 (K := K) k S) (y := hwVec k S) (χ := chiT (K := K) k S)
      (a := (0 : Fin Tag.D4.rank)) (b := (3 : Fin Tag.D4.rank)) htS h1
    have ht2 := isChevType_comp_triality_chi_erase (K := K) (hw := hw)
      (ρ := (tensorD4 (K := K) k S).comp (triality K).toMonoidHom)
      (y := hwVec k S) (χ := fun x => chiT (K := K) k S (triality K x))
      (a := (3 : Fin Tag.D4.rank)) (b := (1 : Fin Tag.D4.rank)) ht1 h2
    have hd : ∀ (i : Fin Tag.D4.rank) (z : Kˣ),
        χ (dC .D4 K i z) =
          chiT (K := K) k S ((triality K) ((triality K) (dC .D4 K i z))) := by
      intro i z
      by_cases hi : i = 1
      · have hx1 : (triality K) (dC .D4 K 1 z) = dC .D4 K (trialityPerm 1) z :=
          triality_dC 1 z
        have hx2 : (triality K) (dC .D4 K (trialityPerm 1) z) =
            dC .D4 K (trialityPerm (trialityPerm 1)) z := triality_dC (trialityPerm 1) z
        have hx3 : trialityPerm (trialityPerm 1) = 0 := by rw [hπ1, hπ3]
        have hx : (triality K) ((triality K) (dC .D4 K 1 z)) = dC .D4 K 0 z :=
          (congrArg (triality K) hx1).trans (hx2.trans (congrArg (fun w => dC .D4 K w z) hx3))
        rw [hi]
        exact (hχe z).trans
          (((chiT_dC_zero (K := K) k S z).symm).trans (congrArg (chiT (K := K) k S) hx).symm)
      · have hmem : i ∈ Finset.univ.erase (1 : Fin Tag.D4.rank) := by
          rw [Finset.mem_erase]
          exact ⟨hi, Finset.mem_univ i⟩
        have hx1 : (triality K) (dC .D4 K i z) = dC .D4 K (trialityPerm i) z :=
          triality_dC i z
        have hx2 : (triality K) (dC .D4 K (trialityPerm i) z) =
            dC .D4 K (trialityPerm (trialityPerm i)) z := triality_dC (trialityPerm i) z
        have hx : (triality K) ((triality K) (dC .D4 K i z)) =
            dC .D4 K (trialityPerm (trialityPerm i)) z :=
          (congrArg (triality K) hx1).trans hx2
        have hpi : trialityPerm (trialityPerm i) ≠ 0 := by
          intro h0
          apply hi
          have h3 : trialityPerm i = 3 := by
            have hh := h0.trans hπ3.symm
            exact trialityPerm.injective hh
          have h4 : i = 1 := by
            have hh : trialityPerm i = trialityPerm 1 := by rw [h3, hπ1]
            exact trialityPerm.injective hh
          exact h4
        exact (ht.subset hmem z).trans
          (((hx.symm ▸ chiT_dC_of_ne (K := K) k S (i := trialityPerm (trialityPerm i)) hpi z)).symm)
    let h := exists_iso_of_dC_match (S := S) hρ (y := y) ht
      (ρ' := ((tensorD4 (K := K) k S).comp (triality K).toMonoidHom).comp
        (triality K).toMonoidHom)
      (isSimpleRep_comp (isSimpleRep_comp (isSimpleRep_tensorD4 k hK S hS) (triality K))
        (triality K)) ht2 hd
    exact ⟨S, (triality K).trans (triality K), Classical.choose h, hSne, hS, hχe,
      fun x w => by rw [Classical.choose_spec h x w]; rfl⟩

theorem exists_iso_tensorD4_of_end {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .D4 K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup .D4 K → k} {e : Fin 4} (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (ht : IsChevType .D4 K 2 hw ρ y χ (Finset.univ.erase e)) :
    ∃ (S : Finset ℕ) (σ : adjointGroup .D4 K ≃* adjointGroup .D4 K)
      (β : V ≃ₗ[k] ((S → Fin 4 ⊕ Fin 4) → k)),
      S.Nonempty ∧ (∀ b ∈ S, b < n) ∧
      (∀ z : Kˣ, χ (dC .D4 K e z) = (algebraMap K k (z : K)) ^ (∑ b ∈ S, 2 ^ b)) ∧
      ∀ (x : adjointGroup .D4 K) (w : V), β (ρ x w) = tensorD4 (K := K) k S (σ x) (β w) := by
  have he' : (e : Fin 4) = 0 ∨ (e : Fin 4) = 1 ∨ (e : Fin 4) = 3 := by simpa using he
  have hcases : (e : Fin Tag.D4.rank) = (0 : Fin 4) ∨ (e : Fin Tag.D4.rank) = (3 : Fin 4) ∨
      (e : Fin Tag.D4.rank) = (1 : Fin 4) := by
    rcases he' with h | h | h
    · left; rw [h]
    · right; right; rw [h]
    · right; left; rw [h]
  exact exists_iso_tensorD4_of_end' (K := K) hn hK hρ hcases ht

private theorem pow_eight_ge (s : ℕ) (hs : 2 ≤ s) : 28 * s + 2 ≤ 8 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      rw [pow_succ]
      nlinarith [ih]

private theorem le_of_four (t : ℕ) (ht : 4 ≤ t) : 28 * t + 2 ≤ 8 * 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ]
      nlinarith [ih]

private theorem le_of_two (t : ℕ) (ht : 2 ≤ t) : 28 * t + 2 ≤ 4 * (2 ^ t * 2 ^ t) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ]
      nlinarith [ih, Nat.one_le_two_pow (n := t)]

private theorem le_192_of_two_three (t : ℕ) (h2 : 2 ≤ t) (h3 : t ≤ 3) : 28 * t + 2 ≤ 192 := by
  interval_cases t <;> norm_num

private theorem two_not_mem_ends : (2 : Fin 4) ∉ ({0, 1, 3} : Finset (Fin 4)) := by
  decide +kernel

private theorem ne_two_mem_ends' : ∀ s' : Fin 4,
    s' ≠ (2 : Fin 4) → s' ∈ ({0, 1, 3} : Finset (Fin 4)) := by
  decide +kernel

private theorem d4_bound_of_two_not_mem [Module.Finite k V] {n g : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup .D4 K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)}
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ (i : Fin 4) (z : Kˣ), χ (dC .D4 K i z) ^ (2 ^ g) = χ (dC .D4 K i z))
    (h2 : (2 : Fin 4) ∉ J) (ht2 : 2 ≤ n / g) :
    28 * (n / g) + 2 ≤ Module.finrank k V ∨
      (2 ≤ n / g ∧ ∀ x : adjointGroup .D4 K, x * x = 1 → x ≠ 1 →
        7 * (n / g) + 3 ≤ Module.finrank k (LinearMap.range (ρ x - 1))) := by
  by_cases ht4 : 4 ≤ n / g
  · refine Or.inl ?_
    have hcop := copies_center_finrank hn hK hρ ht h2 hg hgn (hper 2)
    have harith := le_of_four (n / g) ht4
    omega
  · have ht23 : n / g = 2 ∨ n / g = 3 := by omega
    by_cases hJ3 : J = ({0, 1, 3} : Finset (Fin 4))
    · refine Or.inl ?_
      have hJ' : ∀ s' : Fin Tag.D4.rank, s' ≠ (2 : Fin 4) → s' ∈ J := by
        intro s' hs'
        rw [hJ3]
        exact ne_two_mem_ends' s' hs'
      have hnode := node_center_finrank hn hK hρ ht hJ' h2 hg hgn (by omega) (hper 2)
      have harith := le_192_of_two_three (n / g) ht2 (by omega)
      omega
    · refine Or.inr ⟨ht2, fun x hx2 hx1 => ?_⟩
      have hJends : J ⊆ ({0, 1, 3} : Finset (Fin 4)) := fun s' hs' =>
        ne_two_mem_ends' s' (by rintro rfl; exact h2 hs')
      have hex : ∃ e ∈ ({0, 1, 3} : Finset (Fin 4)), e ∉ J := by
        by_contra hcon
        push Not at hcon
        apply hJ3
        refine Finset.Subset.antisymm hJends ?_
        intro s' hs'
        exact hcon s' hs'
      obtain ⟨e, he, heJ⟩ := hex
      rcases ht23 with ht2' | ht3'
      · have h17 := seventeen_le_finrank_range_of_two_ends hρ ht he h2 heJ x hx2 hx1
        omega
      · have h24 := twentyfour_le_finrank_range_of_two_ends hn hK hρ ht he h2 heJ hg hgn
          (by omega) (hper 2) x hx2 hx1
        omega

theorem d4_type_bound [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .D4 K) V} (hρ : IsSimpleRep ρ)
    (hinj : Function.Injective ρ) {y : V} {χ : adjointGroup .D4 K → k}
    {J : Finset (Fin Tag.D4.rank)} (ht : IsChevType .D4 K 2 hw ρ y χ J) {g : ℕ} (hg : 1 ≤ g)
    (hgn : g ∣ n) (hper : ∀ (i : Fin 4) (z : Kˣ), χ (dC .D4 K i z) ^ (2 ^ g) = χ (dC .D4 K i z)) :
    (n / g = 1 ∧ ∃ (b : ℕ) (σ : adjointGroup .D4 K ≃* adjointGroup .D4 K)
        (β : V ≃ₗ[k] (Fin 4 ⊕ Fin 4 → k)), b < n ∧
        ∀ (x : adjointGroup .D4 K) (w : V), β (ρ x w) = frobNatRep (K := K) k b (σ x) (β w)) ∨
      28 * (n / g) + 2 ≤ Module.finrank k V ∨
      (n / g = 1 ∧ ∀ x : adjointGroup .D4 K, x * x = 1 → x ≠ 1 →
        9 ≤ Module.finrank k (LinearMap.range (ρ x - 1))) ∨
      (2 ≤ n / g ∧ ∀ x : adjointGroup .D4 K, x * x = 1 → x ≠ 1 →
        7 * (n / g) + 3 ≤ Module.finrank k (LinearMap.range (ρ x - 1))) := by
  classical
  have htpos : 1 ≤ n / g := by
    have hgle : g ≤ n := Nat.le_of_dvd (by omega) hgn
    exact (Nat.one_le_div_iff (by omega : 0 < g)).mpr hgle
  by_cases hJu : J = Finset.univ
  · exfalso
    have htriv := eq_of_isChevType_univ_of_charTwo (hw := hw) hρ (hJu ▸ ht)
    have hne : xC .D4 K (0 : Fin 4) (1 : Kˣ) ≠ 1 := xC_ne_one (τ := .D4) (0 : Fin 4) 1
    refine hne (hinj ?_)
    ext w
    rw [map_one, Module.End.one_apply, htriv]
  by_cases hJe : ∃ e ∈ ({0, 1, 3} : Finset (Fin 4)), J = Finset.univ.erase e
  · obtain ⟨e, he, hJ⟩ := hJe
    have htJ : IsChevType .D4 K 2 hw ρ y χ (Finset.univ.erase e) := hJ ▸ ht
    obtain ⟨S, σ, β, hSne, hS, hχe, hβ⟩ :=
      exists_iso_tensorD4_of_end hn hK hρ he htJ
    have ht_le : n / g ≤ S.card := by
      have hdvd := periodic_dvd (τ := .D4) (K := K) hK
        (s := (e : Fin Tag.D4.rank)) hχe (hper e)
      exact card_ge_of_periodic hg hgn hS hSne hdvd
    by_cases hScard : S.card = 1
    · obtain ⟨b, hSb⟩ := Finset.card_eq_one.mp hScard
      have ht1 : n / g = 1 := by omega
      subst hSb
      obtain ⟨ε, hε⟩ := exists_equiv_frobNatRep (K := K) (k := k) b
      refine Or.inl ⟨ht1, b, σ, β.trans ε, ?_, ?_⟩
      · have : b < n := hS b (Finset.mem_singleton_self b)
        exact this
      · intro x w
        simp only [LinearEquiv.trans_apply]
        rw [hβ x w, hε]
    · refine Or.inr (Or.inl ?_)
      have h2 : 2 ≤ S.card := by omega
      have hfr : Module.finrank k V = 8 ^ S.card := by
        rw [LinearEquiv.finrank_eq β, finrank_tensorD4 k S]
      rw [hfr]
      have harith := pow_eight_ge S.card h2
      have hle : 28 * (n / g) + 2 ≤ 28 * S.card + 2 := by
        have : n / g ≤ S.card := ht_le
        omega
      omega
  · push Not at hJe
    by_cases ht1 : n / g = 1
    · refine Or.inr (Or.inr (Or.inl ⟨ht1, fun x hx2 hx1 => ?_⟩))
      exact nine_le_finrank_range_of_sq_eq_one hρ ht hJu hJe x hx2 hx1
    · have ht2 : 2 ≤ n / g := by omega
      rcases subset_ends_or_subset_center_end (J := J) hJu hJe with hJends | ⟨e, he, hJce⟩
      · have h2not : (2 : Fin 4) ∉ J := by
          intro h
          exact two_not_mem_ends (hJends h)
        rcases d4_bound_of_two_not_mem hn hK hρ ht hg hgn hper h2not ht2 with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
      · by_cases h2in : (2 : Fin 4) ∈ J
        · refine Or.inr (Or.inl ?_)
          have hlevi := levi_ends_finrank hn hK hρ ht he hJce hg hgn hper
          have harith := le_of_two (n / g) ht2
          omega
        · have h2not : (2 : Fin 4) ∉ J := h2in
          rcases d4_bound_of_two_not_mem hn hK hρ ht hg hgn hper h2not ht2 with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h))

end D4

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

end
