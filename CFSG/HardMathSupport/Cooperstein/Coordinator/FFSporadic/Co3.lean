module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.RankThree.PartOne.MultRes.Co3
public import CFSG.Sporadic.SmallOddCore.Co3Classes
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.Sporadic.Bridge.Co3Surj
public import Certificates.Certificate129004
public import Certificates.Certificate129005

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

noncomputable def co3Tau (c : ℕ) : Equiv.Perm (Fin 276) := if c = 0 then co3Z else co3Tt

noncomputable def co3X (c : ℕ) : Equiv.Perm (Fin 276) := tp 276 (co3HeisTbl (2 * c))

noncomputable def co3Y (c : ℕ) : Equiv.Perm (Fin 276) := tp 276 (co3HeisTbl (2 * c + 1))

noncomputable def co3W (c : ℕ) : Equiv.Perm (Fin 276) := (co3X c)⁻¹ * (co3Y c)⁻¹ * co3X c * co3Y c

theorem rep_co3HeisTau (c : ℕ) :
    Rep 276 (co3HeisTau c) (co3Tau c) := by
  unfold co3HeisTau co3Tau
  split_ifs
  · exact rep_co3ZTbl
  · exact rep_co3TtTbl

theorem co3Tau_mul_self
    (c : ℕ) : co3Tau c * co3Tau c = 1 := by
  unfold co3Tau
  split_ifs
  · exact co3Z_mul_self
  · exact co3Tt_mul_self

theorem co3Heis_parts {c : ℕ} (hc : c = 0 ∨ c = 1) :
    co3HeisOK c = true := by
  have h := Certificates.certificate129004
  unfold co3HeisCheck at h
  rw [Bool.and_eq_true] at h
  rcases hc with rfl | rfl
  · exact h.1
  · exact h.2

theorem co3Heis_facts
    {c : ℕ} (hc : c = 0 ∨ c = 1) :
    co3X c ∈ co3P ∧ co3Y c ∈ co3P ∧ co3X c ^ 5 = 1 ∧ co3Y c ^ 5 = 1 ∧ co3W c ^ 5 = 1 ∧
      co3W c ≠ 1 ∧ co3X c * co3W c = co3W c * co3X c ∧ co3Y c * co3W c = co3W c * co3Y c ∧
      co3Tau c * co3X c * co3Tau c = (co3X c)⁻¹ := by
  have h := co3Heis_parts hc
  simp only [co3HeisOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpX, hpY⟩, hiX⟩, hiY⟩, hsX⟩, hsY⟩, h5X⟩, h5Y⟩, h5W⟩, hW1⟩, hcX⟩, hcY⟩,
    hτ⟩ := h
  have hn : 276 < 2 ^ 32 := by norm_num
  have rX : Rep 276 (co3HeisTbl (2 * c)) (co3X c) := rep_tp hpX
  have rY : Rep 276 (co3HeisTbl (2 * c + 1)) (co3Y c) := rep_tp hpY
  have rXi := rep_invT rX hiX
  have rYi := rep_invT rY hiY
  have rW : Rep 276 (co3HeisW c) (co3W c) := ((rXi.compT rYi).compT rX).compT rY
  refine ⟨mem_co3P_of_co3Sift rX hsX, mem_co3P_of_co3Sift rY hsY,
    (tblEq_idT_iff hn (rX.powT hn 5)).1 h5X, (tblEq_idT_iff hn (rY.powT hn 5)).1 h5Y,
    (tblEq_idT_iff hn (rW.powT hn 5)).1 h5W, fun h1 => ?_,
    (tblEq_iff_eq (rX.compT rW) (rW.compT rX)).1 hcX,
    (tblEq_iff_eq (rY.compT rW) (rW.compT rY)).1 hcY,
    (tblEq_iff_eq (((rep_co3HeisTau c).compT rX).compT (rep_co3HeisTau c)) rXi).1 hτ⟩
  rw [(tblEq_idT_iff hn rW).2 h1] at hW1
  exact Bool.noConfusion hW1

theorem co3HeisCfg_perm
    {c : ℕ} (hc : c = 0 ∨ c = 1) :
    HeisCfg 5 1 (fun _ => co3X c) (fun _ => co3Y c) (co3W c) := by
  obtain ⟨-, -, hX5, -, hW5, hW1, hXW, hYW, -⟩ := co3Heis_facts hc
  exact
    { xp := fun _ => hX5
      zp := hW5
      zx := fun _ => hXW
      zy := fun _ => hYW
      yx := fun _ => by unfold co3W; group
      xx := fun _ _ => rfl
      yy := fun i j hij => absurd (Subsingleton.elim i j) hij
      xy := fun i j hij => absurd (Subsingleton.elim i j) hij
      z1 := hW1 }

theorem co3_heisP
    {c : ℕ} (hc : c = 0 ∨ c = 1) {g : Equiv.Perm (Fin 276)} (hg : g ∈ co3P) :
    ∃ X' Y' W' : co3P, HeisCfg 5 1 (fun _ => X') (fun _ => Y') W' ∧ Y' ^ 5 = 1 ∧
      g * co3Tau c * g⁻¹ * (X' : Equiv.Perm (Fin 276)) * (g * co3Tau c * g⁻¹)⁻¹ =
        (X' : Equiv.Perm (Fin 276))⁻¹ := by
  obtain ⟨hXP, hYP, hX5, hY5, hW5, hW1, hXW, hYW, hτX⟩ := co3Heis_facts hc
  have hWP : co3W c ∈ co3P := by
    unfold co3W
    exact co3P.mul_mem (co3P.mul_mem (co3P.mul_mem (co3P.inv_mem hXP) (co3P.inv_mem hYP)) hXP) hYP
  have hc' : ∀ {a : Equiv.Perm (Fin 276)}, a ∈ co3P → g * a * g⁻¹ ∈ co3P := fun ha =>
    co3P.mul_mem (co3P.mul_mem hg ha) (co3P.inv_mem hg)
  refine ⟨⟨g * co3X c * g⁻¹, hc' hXP⟩, ⟨g * co3Y c * g⁻¹, hc' hYP⟩, ⟨g * co3W c * g⁻¹, hc' hWP⟩,
    ?_, ?_, ?_⟩
  · have h := co3HeisCfg_perm hc
    exact
      { xp := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, h.xp 0]; group)
        zp := Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, h.zp]; group)
        zx := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          calc g * co3X c * g⁻¹ * (g * co3W c * g⁻¹) = g * (co3X c * co3W c) * g⁻¹ := by group
            _ = g * (co3W c * co3X c) * g⁻¹ := by rw [hXW]
            _ = g * co3W c * g⁻¹ * (g * co3X c * g⁻¹) := by group)
        zy := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          calc g * co3Y c * g⁻¹ * (g * co3W c * g⁻¹) = g * (co3Y c * co3W c) * g⁻¹ := by group
            _ = g * (co3W c * co3Y c) * g⁻¹ := by rw [hYW]
            _ = g * co3W c * g⁻¹ * (g * co3Y c * g⁻¹) := by group)
        yx := fun _ => Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          unfold co3W
          group)
        xx := fun _ _ => rfl
        yy := fun i j hij => absurd (Subsingleton.elim i j) hij
        xy := fun i j hij => absurd (Subsingleton.elim i j) hij
        z1 := fun h1 => hW1 (by
          have h2 := congrArg (fun x : co3P => g⁻¹ * (x : Equiv.Perm (Fin 276)) * g) h1
          simpa [mul_assoc] using h2) }
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, conj_pow, hY5]
    group
  · have hτi : (co3Tau c)⁻¹ = co3Tau c := inv_eq_of_mul_eq_one_right (co3Tau_mul_self c)
    calc g * co3Tau c * g⁻¹ * (g * co3X c * g⁻¹) * (g * co3Tau c * g⁻¹)⁻¹
        = g * (co3Tau c * co3X c * (co3Tau c)⁻¹) * g⁻¹ := by group
      _ = g * (co3X c)⁻¹ * g⁻¹ := by rw [hτi, hτX]
      _ = (g * co3X c * g⁻¹)⁻¹ := by group

theorem co3_conj_tau
    {v : Equiv.Perm (Fin 276)}
    (hv : v ∈ co3P) (hv2 : orderOf v = 2) :
    ∃ c : ℕ, (c = 0 ∨ c = 1) ∧ ∃ g ∈ co3P, v = g * co3Tau c * g⁻¹ := by
  have hcl := ctuc_co3_complete_inner_involution_classes.2.2.2.1 v hv hv2
  by_cases hz : ∃ g ∈ co3P, v = g * co3Z * g⁻¹
  · obtain ⟨g, hg, h⟩ := hz
    exact ⟨0, Or.inl rfl, g, hg, by simpa [co3Tau] using h⟩
  · have ht : ∃ g ∈ co3P, v = g * co3Tt * g⁻¹ := by
      by_contra hnt
      exact hz (hcl.2 hnt)
    obtain ⟨g, hg, h⟩ := ht
    exact ⟨1, Or.inr rfl, g, hg, by simpa [co3Tau] using h⟩

theorem co3_heisGen :
    ∀ u : NativeSporadic.Co3, u * u = 1 → u ≠ 1 →
      ∃ (x y : Fin (0 + 1) → NativeSporadic.Co3) (z : NativeSporadic.Co3),
        HeisCfg 5 (0 + 1) x y z ∧ (∀ i, y i ^ 5 = 1) ∧ u * x 0 * u⁻¹ = (x 0)⁻¹ := by
  intro u hu2 hu1
  have hvv : co3PermEquiv u * co3PermEquiv u = 1 := by rw [← map_mul, hu2, map_one]
  have hv1 : co3PermEquiv u ≠ 1 := fun h => hu1 (co3PermEquiv.injective (by rw [h, map_one]))
  have hv2 : orderOf ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276)) = 2 := by
    refine orderOf_eq_prime ?_ fun h => hv1 (Subtype.ext h)
    rw [sq, ← Subgroup.coe_mul, hvv]
    rfl
  obtain ⟨c, hc, g, hg, hvg⟩ := co3_conj_tau (co3PermEquiv u).2 hv2
  obtain ⟨X', Y', W', hP, hY5, hinv⟩ := co3_heisP hc hg
  have hW'1 : co3PermEquiv.symm W' ≠ 1 := fun h1 =>
    hP.z1 (by rw [← co3PermEquiv.apply_symm_apply W', h1, map_one])
  refine ⟨fun _ => co3PermEquiv.symm X', fun _ => co3PermEquiv.symm Y', co3PermEquiv.symm W',
    ?_, fun _ => ?_, ?_⟩
  · exact
      { xp := fun _ => co3PermEquiv.injective (by
          rw [map_pow, MulEquiv.apply_symm_apply, map_one]; exact hP.xp 0)
        zp := co3PermEquiv.injective (by
          rw [map_pow, MulEquiv.apply_symm_apply, map_one]; exact hP.zp)
        zx := fun _ => co3PermEquiv.injective (by
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
          exact hP.zx 0)
        zy := fun _ => co3PermEquiv.injective (by
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
          exact hP.zy 0)
        yx := fun _ => co3PermEquiv.injective (by
          rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
            MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
          exact hP.yx 0)
        xx := fun _ _ => rfl
        yy := fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij
        xy := fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij
        z1 := hW'1 }
  · apply co3PermEquiv.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact hY5
  · apply co3PermEquiv.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hvg]
    exact hinv

theorem co3_card_le_of_t_mem
    {B : Subgroup (Equiv.Perm (Fin 276))} (hBP : B ≤ co3P)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) (ht : co3Tt ∈ B) :
    Nat.card B ≤ 2 ^ 4 := by
  have hBM : B ≤ co3M1 := by
    intro b hb
    rw [co3M1_eq_centralizer]
    exact ⟨hBP hb, Subgroup.mem_centralizer_singleton_iff.2 (hcomm b hb co3Tt ht)⟩
  set B₁ : Subgroup co3M1 := B.subgroupOf co3M1 with hB₁
  have hcard : Nat.card B₁ = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  set φ : ↥B₁ →* Equiv.Perm (Fin 12) := co3Kappa1.comp B₁.subtype with hφ
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map B₁.subtype ≤ Subgroup.zpowers co3TtM1 := by
      rw [← co3Kappa1_ker]
      rintro _ ⟨k, hk, rfl⟩
      exact hk
    calc Nat.card φ.ker = Nat.card (φ.ker.map B₁.subtype) :=
          (Subgroup.card_map_of_injective B₁.subtype_injective).symm
      _ ≤ Nat.card (Subgroup.zpowers co3TtM1) := Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, orderOf_co3TtM1]
  have hrange : Nat.card φ.range ≤ 2 ^ 3 := by
    have hle : φ.range ≤ NativeSporadic.M12 := by
      rintro _ ⟨k, rfl⟩
      rw [← co3Kappa1_range]
      exact ⟨_, rfl⟩
    have hR : Nat.card (φ.range.subgroupOf NativeSporadic.M12) = Nat.card φ.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [← hR]
    refine QuasithinUnique.Setup.X1.m12_rank_le _ (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hx
      obtain ⟨b, hb⟩ := Subgroup.mem_subgroupOf.1 hy
      have hab : a * b = b * a := Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 a.2)
        _ (Subgroup.mem_subgroupOf.1 b.2)))
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hab]
    · obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hx
      have haa : a * a = 1 := Subtype.ext (Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.1 a.2)))
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← ha, ← map_mul, haa, map_one]
      rfl
  calc Nat.card B = Nat.card B₁ := hcard.symm
    _ = Nat.card φ.range * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    _ ≤ 2 ^ 3 * 2 := Nat.mul_le_mul hrange hker
    _ = 2 ^ 4 := by norm_num

def co3IsA (x : Equiv.Perm (Fin 276)) : Prop := orderOf x = 2 ∧ ∃ g ∈ co3P, x = g * co3Z * g⁻¹

theorem co3AEnt_iff
    {k : ℕ} (hk : k < (mulClosureH 276 co3TTbls 2000).1.size) :
    co3AEnt (mulClosureH 276 co3TTbls 2000).1[k]! = true ↔
      co3IsA (tablePerm 276 (mulClosureH 276 co3TTbls 2000).1[k]!) := by
  set E := (mulClosureH 276 co3TTbls 2000).1
  have hn : 276 < 2 ^ 32 := by norm_num
  have hr : Rep 276 E[k]! (tablePerm 276 E[k]!) := (co3_T_enum.1 k hk).1
  obtain ⟨-, -, -, -, -, -, -, -, hcov, -, -⟩ := co3_fusion_parts
  unfold co3AEnt co3IsA
  rw [Bool.and_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hinv, w, hw, hb⟩
    rw [Bool.and_eq_true] at hb
    obtain ⟨g, hg, he⟩ := co3_fusesTo_spec hr hw hb.2
    rw [hb.1] at he
    exact ⟨orderOf_eq_two_of_involOK hn hr hinv, g, hg, by simpa using he⟩
  · rintro ⟨hord, g, hg, he⟩
    have hinv := involOK_of_orderOf hn hr hord
    refine ⟨hinv, ?_⟩
    have hmem : E[k]! ∈ E.filter (involOK 276) := by
      rw [Array.mem_filter]
      exact ⟨getElem!_mem_array hk, hinv⟩
    obtain ⟨w, hw, hb⟩ := hcov _ hmem
    refine ⟨w, hw, ?_⟩
    cases hw2 : w.2
    · exfalso
      obtain ⟨h, hh, he'⟩ := co3_fusesTo_spec hr hw hb
      rw [hw2] at he'
      apply co3_z_not_conj_t
      refine ⟨h⁻¹ * g, co3P.mul_mem (co3P.inv_mem hh) hg, ?_⟩
      have : co3Tt = h⁻¹ * (tablePerm 276 E[k]!) * h := by
        rw [he']
        simp only [Bool.false_eq_true, ↓reduceIte]
        group
      rw [this, he]
      group
    · simpa [hw2] using hb

noncomputable def co3DegA (x : Equiv.Perm (Fin 276)) : ℕ :=
  {y | y ∈ co3T ∧ co3IsA y ∧ x * y = y * x}.ncard

theorem co3Rank_check :
    {x | x ∈ co3T ∧ (co3IsA x ∧ 31 ≤ co3DegA x)}.ncard ≤ 30 := by
  set E := (mulClosureH 276 co3TTbls 2000).1
  have h := Certificates.certificate129005
  unfold co3RankCheck at h
  rw [decide_eq_true_eq] at h
  have hE := co3_T_enum.1
  have hdeg : ∀ k < E.size, ((E.filter co3AEnt).filter fun s' => commTT 276 E[k]! s').size =
      co3DegA (tablePerm 276 E[k]!) := by
    intro k hk
    rw [Array.filter_filter, co3DegA]
    refine (co3_count_filter _ _ fun k' hk' => ?_).symm
    rw [Bool.and_eq_true, co3AEnt_iff hk', and_comm]
    exact and_congr Iff.rfl (tblEq_iff_eq ((hE k hk).1.compT (hE k' hk').1)
      ((hE k' hk').1.compT (hE k hk).1))
  have hcount := co3_count_filter
    (fun s => decide (31 ≤ ((E.filter co3AEnt).filter fun s' => commTT 276 s s').size) && co3AEnt s)
    (fun x => co3IsA x ∧ 31 ≤ co3DegA x) fun k hk => by
      rw [Bool.and_eq_true, co3AEnt_iff hk, decide_eq_true_eq, hdeg k hk, and_comm]
  rw [hcount, ← Array.filter_filter]
  exact h

theorem co3_card_le_of_pureA
    {B : Subgroup (Equiv.Perm (Fin 276))} (hBT : B ≤ co3T)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hA : ∀ x ∈ B, x ≠ 1 → co3IsA x) :
    Nat.card B ≤ 31 := by
  by_contra hgt
  push Not at hgt
  set B' : Set (Equiv.Perm (Fin 276)) := (B : Set (Equiv.Perm (Fin 276))) \ {1} with hB'
  have hB'card : 31 ≤ B'.ncard := by
    have h1 : B'.ncard = (B : Set (Equiv.Perm (Fin 276))).ncard - 1 := by
      rw [hB', Set.ncard_sdiff_singleton_of_mem (by exact B.one_mem)]
    rw [h1, ← Nat.card_coe_set_eq]
    change 31 ≤ Nat.card B - 1
    omega
  have hsub : B' ⊆ {x | x ∈ co3T ∧ (co3IsA x ∧ 31 ≤ co3DegA x)} := by
    rintro b ⟨hb, hb1⟩
    have hb1' : b ≠ 1 := hb1
    refine ⟨hBT hb, hA b hb hb1', hB'card.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))⟩
    rintro y ⟨hy, hy1⟩
    exact ⟨hBT hy, hA y hy hy1, hcomm b hb y hy⟩
  have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans co3Rank_check
  omega

theorem co3_exists_conj_le_T
    {B : Subgroup (Equiv.Perm (Fin 276))} (hBP : B ≤ co3P)
    (hsq : ∀ x ∈ B, x * x = 1) : ∃ g ∈ co3P, ∀ x ∈ B, g⁻¹ * x * g ∈ co3T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Nat.card (co3T.subgroupOf co3P) = 2 ^ (Nat.card co3P).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3T_le_P).toEquiv, card_co3T, card_co3P,
      show (495766656000 : ℕ) = 2 ^ 10 * 484147125 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  let S' : Sylow 2 co3P := Sylow.ofCard (co3T.subgroupOf co3P) hT
  have hB2 : IsPGroup 2 (B.subgroupOf co3P) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa [sq] using hsq _ (Subgroup.mem_subgroupOf.1 x.2)
  obtain ⟨T, hTle⟩ := hB2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq co3P S' T
  refine ⟨x, x.2, fun b hb => ?_⟩
  have hbT : (⟨b, hBP hb⟩ : co3P) ∈ (T : Subgroup co3P) :=
    hTle (Subgroup.mem_subgroupOf.2 hb)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbT
  obtain ⟨s, hs, hst⟩ := hbT
  have hsS : (s : Equiv.Perm (Fin 276)) ∈ co3T := by
    have : s ∈ co3T.subgroupOf co3P := by
      rwa [show ((S' : Subgroup co3P)) = co3T.subgroupOf co3P from Sylow.coe_ofCard _ _] at hs
    exact Subgroup.mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨b, hBP hb⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem co3P_elemAbelian_le
    {B : Subgroup (Equiv.Perm (Fin 276))} (hBP : B ≤ co3P)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 4 := by
  have hconj : ∀ g ∈ co3P, Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card B ∧
      B.map (MulAut.conj g⁻¹).toMonoidHom ≤ co3P ∧
      (∀ x ∈ B.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ B.map (MulAut.conj g⁻¹).toMonoidHom,
        x * y = y * x) ∧
      (∀ x ∈ B.map (MulAut.conj g⁻¹).toMonoidHom, x * x = 1) := by
    intro g hg
    refine ⟨Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, ?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact co3P.mul_mem (co3P.mul_mem (co3P.inv_mem hg) (hBP hb)) hg
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
        _ = g⁻¹ * (b * a) * g := by rw [hcomm a ha b hb]
        _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [hsq a ha]; group
  by_cases hB : ∃ b ∈ B, b ≠ 1 ∧ ∃ g ∈ co3P, b = g * co3Tt * g⁻¹
  · obtain ⟨b, hb, -, g, hg, hbg⟩ := hB
    obtain ⟨hc, hP, hcomm', hsq'⟩ := hconj g hg
    rw [← hc]
    refine co3_card_le_of_t_mem hP hcomm' hsq' ⟨b, hb, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hbg]
    group
  · push Not at hB
    have hA : ∀ x ∈ B, x ≠ 1 → co3IsA x := by
      intro x hx hx1
      have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hsq x hx) hx1
      refine ⟨hord, ?_⟩
      have hcl := ctuc_co3_complete_inner_involution_classes.2.2.2.1 x (hBP hx) hord
      by_contra hz
      exact hz (hcl.2 fun ⟨g, hg, h⟩ => hB x hx hx1 g hg h)
    obtain ⟨g, hg, hgT⟩ := co3_exists_conj_le_T hBP hsq
    obtain ⟨hc, -, hcomm', hsq'⟩ := hconj g hg
    have hBT : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ co3T := by
      rintro _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hgT b hb
    have hA' : ∀ x ∈ B.map (MulAut.conj g⁻¹).toMonoidHom, x ≠ 1 → co3IsA x := by
      rintro _ ⟨b, hb, rfl⟩ hb1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hb1 ⊢
      have hb1' : b ≠ 1 := fun h => hb1 (by rw [h]; group)
      obtain ⟨hord, h, hh, hbh⟩ := hA b hb hb1'
      refine ⟨by rw [show g⁻¹ * b * g = MulAut.conj g⁻¹ b by simp,
        MulEquiv.orderOf_eq, hord], g⁻¹ * h, co3P.mul_mem (co3P.inv_mem hg) hh, ?_⟩
      rw [hbh]
      group
    have h31 := co3_card_le_of_pureA hBT hcomm' hA'
    rw [hc] at h31
    have hp : IsPGroup 2 B := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      simpa [sq] using hsq x x.2
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk] at h31 ⊢
    exact Nat.pow_le_pow_right (by norm_num) (by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega)

theorem not_dvd_card_center_of_kernelTrivialAt {X : Type} [Group X] {p : ℕ} [hp : Fact p.Prime]
    (h : CFSG.AGLEmbedding.KernelTrivialAt X p) {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (e : L ⧸ Subgroup.center L ≃* X) :
    ¬ p ∣ Nat.card (Subgroup.center L) := by
  intro hdvd
  classical
  set Z := Subgroup.center L with hZ
  set m := ordCompl[p] (Nat.card Z) with hm
  have hZcomm : ∀ a ∈ Z, ∀ b : L, a * b = b * a := fun a ha b =>
    (Subgroup.mem_center_iff.1 ha b).symm
  let Q : Subgroup L :=
    { carrier := {x | x ∈ Z ∧ x ^ m = 1}
      mul_mem' := fun {a b} ha hb => ⟨Z.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hZcomm a ha.1 b)), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨Z.one_mem, one_pow m⟩
      inv_mem' := fun {a} ha => ⟨Z.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hQZ : Q ≤ Z := fun x hx => hx.1
  have hQn : Q.Normal := ⟨fun n hn g => by
    rw [← hZcomm n hn.1 g, mul_inv_cancel_right]
    exact hn⟩
  have : Group.IsPerfect (L ⧸ Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  let π : L ⧸ Q →* X := e.toMonoidHom.comp (QuotientGroup.map Q Z (MonoidHom.id L) hQZ)
  have hπ : ∀ x : L, π (x : L ⧸ Q) = e (x : L ⧸ Z) := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨x, rfl⟩
  have hker : ∀ y : L ⧸ Q, π y = 1 → ∃ x ∈ Z, y = (x : L ⧸ Q) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff] at hy
    exact ⟨x, hy, rfl⟩
  have hcen : π.ker ≤ Subgroup.center (L ⧸ Q) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hker y hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hZcomm x hx w]
  have hpk : IsPGroup p π.ker := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hker y y.2
    refine ⟨(Nat.card Z).factorization p, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hxy, ← QuotientGroup.mk_pow, Subgroup.coe_one,
      QuotientGroup.eq_one_iff]
    refine ⟨Z.pow_mem hx _, ?_⟩
    rw [← pow_mul, hm, Nat.ordProj_mul_ordCompl_eq_self]
    have h2 : (⟨x, hx⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
    exact h3
  have hbot := h (L ⧸ Q) π hπs hcen hpk
  obtain ⟨zz, hzz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzQ : ((zz : L) : L ⧸ Q) ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
    exact zz.2
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzQ
  have hdm : p ∣ m := by
    have h1 : orderOf (zz : L) ∣ m := orderOf_dvd_of_pow_eq_one hzQ.2
    rwa [Subgroup.orderOf_coe, hzz] at h1
  have hcop := Nat.coprime_ordCompl hp.out (Nat.card_pos (α := Z)).ne'
  rw [← hm] at hcop
  exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdm)

@[expose] noncomputable def co3ImgP
    (B : Subgroup NativeSporadic.Co3) : Subgroup (Equiv.Perm (Fin 276)) where
  carrier := (fun u => ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276))) '' (B : Set NativeSporadic.Co3)
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, B.mul_mem hx hy, by simp only [map_mul, Subgroup.coe_mul]⟩
  one_mem' := ⟨1, B.one_mem, by simp only [map_one, Subgroup.coe_one]⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, B.inv_mem hx, by simp only [map_inv, Subgroup.coe_inv]⟩

theorem co3_elemAbelian_le :
    ∀ B : Subgroup NativeSporadic.Co3, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 4 := by
  intro B hcomm hsq
  have hP : co3ImgP B ≤ co3P := by
    rintro _ ⟨x, -, rfl⟩
    exact (co3PermEquiv x).2
  have hcomm' : ∀ x ∈ co3ImgP B, ∀ y ∈ co3ImgP B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := congrArg (fun u => ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276))) (hcomm x hx y hy)
    simpa only [map_mul, Subgroup.coe_mul] using h
  have hsq' : ∀ x ∈ co3ImgP B, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg (fun u => ((co3PermEquiv u : co3P) : Equiv.Perm (Fin 276))) (hsq x hx)
    simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using h
  have h := co3P_elemAbelian_le hP hcomm' hsq'
  have hc : Nat.card (co3ImgP B) = Nat.card B :=
    Nat.card_image_of_injective (fun a b hab => co3PermEquiv.injective (Subtype.ext hab)) _
  rwa [hc] at h

theorem co3_autInner :
    ∀ φ : NativeSporadic.Co3 ≃* NativeSporadic.Co3, ∃ s : NativeSporadic.Co3,
      ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  obtain ⟨g, hg⟩ := co3_allInner φ
  exact ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩

theorem orderOf_two_zmod_five_co3 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem sporadicExclusion_Co3 :
    QuasithinUnique.Setup.X1.SporadicExclusion .Co3 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Group.IsPerfect ↥L := hq.1
  have hkt : CFSG.AGLEmbedding.KernelTrivialAt (NativeSporadic.Carrier .Co3) 5 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.kernelTrivialAt_carrier_of_sporadicKernelTrivial
      CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_co3_five
  have hZ : ¬ 5 ∣ Nat.card (Subgroup.center ↥L) := not_dvd_card_center_of_kernelTrivialAt hkt e
  exact QuasithinUnique.Setup.X1.exclusion_of_autInner hW hq.1 hirr hE hEne hEel e co3_autInner
    (r := 4) (ρ := 8) (by norm_num) co3_elemAbelian_le
    (rank_of_heisCfg hW hirr e (ρ := 8) (p := 5) (n := 0) (by norm_num) hZ
      (by rw [orderOf_two_zmod_five_co3]; norm_num) co3_heisGen)

theorem noIrrFFOffender_Co3 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Co3).Group :=
  Proving.noIrrFFOffender_of_exclusion sporadicExclusion_Co3
    CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Co3 :
    GF2NoFFSporadicFor .Co3 :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Co3

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
