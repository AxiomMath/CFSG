module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmWit
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BRankSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentKey

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_minusPair_of_minus_dim_two {W : Submodule (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp W.subtype))
    (hdim : finrank (ZMod 2) W = 2) :
    ∃ a ∈ W, ∃ b ∈ W, Q a = 1 ∧ Q b = 1 ∧ polar Q a b = 1 := by
  classical
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨a, haW, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have haW0 : (⟨a, haW⟩ : W) ≠ 0 := fun h => ha0 (Subtype.ext_iff.1 h)
  have hQa : Q a = 1 := by
    rcases zmod_two_cases (Q a) with h0 | h1
    · exfalso
      apply hminus
      refine ⟨Submodule.span (ZMod 2) {(⟨a, haW⟩ : W)}, ?_, ?_⟩
      · rw [finrank_span_singleton haW0, hdim]
      · rintro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        rw [QuadraticMap.map_smul]
        rw [show (Q.comp W.subtype) (⟨a, haW⟩ : W) = 0 from h0, smul_zero]
    · exact h1
  have hex : ∃ b ∈ W, polar Q a b = 1 := by
    by_contra h
    push_neg at h
    have hzero : ∀ y ∈ W, polar Q a y = 0 := by
      intro y hy
      rcases zmod_two_cases (polar Q a y) with h0 | h1
      · exact h0
      · exact absurd h1 (h y hy)
    exact ha0 (congrArg Subtype.val (hQ.1 ⟨a, haW⟩ (fun y => hzero y y.2)))
  obtain ⟨b, hbW, hab⟩ := hex
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hab
    exact zero_ne_one hab
  have hbW0 : (⟨b, hbW⟩ : W) ≠ 0 := fun h => hb0 (Subtype.ext_iff.1 h)
  have hQb : Q b = 1 := by
    rcases zmod_two_cases (Q b) with h0 | h1
    · exfalso
      apply hminus
      refine ⟨Submodule.span (ZMod 2) {(⟨b, hbW⟩ : W)}, ?_, ?_⟩
      · rw [finrank_span_singleton hbW0, hdim]
      · rintro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        rw [QuadraticMap.map_smul]
        rw [show (Q.comp W.subtype) (⟨b, hbW⟩ : W) = 0 from h0, smul_zero]
    · exact h1
  exact ⟨a, haW, b, hbW, hQa, hQb, hab⟩

theorem exists_frame_six (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 6) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ l : List (V × V), IsFrame Q l ∧ l.length = 6 := by
  obtain ⟨l, hl, hlen5, hpdim⟩ := exists_frame_five hQ hdim (by norm_num : 6 ≤ 6)
  have hWminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpL Q l).subtype) :=
    not_isPlusType_perpL_five_of_plus hQ hdim (by norm_num) hplus hl hlen5
  have hWdim : finrank (ZMod 2) (perpL Q l) = 2 := by
    rw [hpdim]
  have hWnd : (QuadraticMap.polarBilin (Q.comp (perpL Q l).subtype)).Nondegenerate :=
    nondeg_comp_subtype (hl.perpL_nondeg hQ)
  obtain ⟨a, haW, b, hbW, hQa, hQb, hB⟩ :=
    exists_minusPair_of_minus_dim_two hWnd hWminus hWdim
  have hperp : ∀ q ∈ l, PairPerp Q (a, b) q := by
    intro q hq
    obtain ⟨h1, h2⟩ := (mem_perpL_iff l a).1 haW q hq
    obtain ⟨h3, h4⟩ := (mem_perpL_iff l b).1 hbW q hq
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_comm]; exact h1
    · rw [polar_comm]; exact h2
    · rw [polar_comm]; exact h3
    · rw [polar_comm]; exact h4
  have hp : MinusPair Q a b := ⟨hQa, hQb, hB⟩
  exact ⟨(a, b) :: l, IsFrame.cons hp hperp hl, by simp [hlen5]⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem eichler_swap_add {u v : V} (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 0) :
    eichler Q v (u + v) = eichler Q u v := by
  have h1 : Q (u + v) = 0 := by
    rw [map_add_polar, hu, hv, huv]
    decide
  have h2 : polar Q v (u + v) = 0 := by
    rw [polar_add_right, polar_comm, huv, polar_self_zero]
    simp
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hv h2, eichler_apply hu huv]
  simp only [h1, hv, zero_mul, add_zero, QuadraticMap.map_zero]
  rw [polar_add_right]
  rw [sub_eq_add_neg, sub_eq_add_neg, ZModModule.neg_eq_self, ZModModule.neg_eq_self]
  linear_combination (norm := module) (polar Q x v) • (vec_add_self v)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem rot_fixes_of_pairPerp {p q : V × V} (hp : MinusPair Q p.1 p.2) (h : PairPerp Q p q) :
    rot Q p.1 p.2 q.1 = q.1 ∧ rot Q p.1 p.2 q.2 = q.2 := by
  refine ⟨rot_apply_of_perp hp ?_ ?_, rot_apply_of_perp hp ?_ ?_⟩
  · rw [polar_comm]; exact h.1
  · rw [polar_comm]; exact h.2.2.1
  · rw [polar_comm]; exact h.2.1
  · rw [polar_comm]; exact h.2.2.2

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

set_option maxHeartbeats 800000 in
theorem exists_twoLocal_three_pow_five_six (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 6) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ E : Subgroup ↥(orthDerived Q), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧ TwoLocal E := by
  obtain ⟨l, hl, hlen⟩ := exists_frame_six hQ hdim hplus
  obtain ⟨a, b, hp, hperp, horth⟩ := exists_family_of_isFrame hl hlen
  let u : V := a 0 + a 1
  let v : V := b 0 + b 1
  have h01 : PairPerp Q (a 0, b 0) (a 1, b 1) := hperp 0 1 (by decide)
  have huQ : Q u = 0 := by
    dsimp only [u]
    rw [map_add_polar, (hp 0).qa, (hp 1).qa, h01.1]
    decide
  have hvQ : Q v = 0 := by
    dsimp only [v]
    rw [map_add_polar, (hp 0).qb, (hp 1).qb, h01.2.2.2]
    decide
  have huv : polar Q u v = 0 := by
    have h10 : polar Q (a 1) (b 0) = 0 := by rw [polar_comm]; exact h01.2.2.1
    dsimp only [u, v]
    simp only [polar_add_left, polar_add_right, (hp 0).ab, h01.2.1, h10, (hp 1).ab]
    decide
  let s : V ≃ₗ[ZMod 2] V := eichler Q u v
  have hss : s * s = 1 := by
    dsimp only [s]
    rw [eichler_mul huv huv, vec_add_self, eichler_zero_right]
  have hsa0 : s (a 0) = a 1 := by
    dsimp only [s]
    rw [eichler_apply huQ huv]
    have h1 : polar Q (a 0) u = 0 := by
      dsimp only [u]
      rw [polar_add_right, polar_self_zero, h01.1, add_zero]
    have h2 : polar Q (a 0) v = 1 := by
      dsimp only [v]
      rw [polar_add_right, (hp 0).ab, h01.2.1, add_zero]
    simp only [h1, h2, hvQ, zero_mul, add_zero, zero_smul, zero_add, one_smul]
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
    dsimp only [u]
    linear_combination (norm := module) (vec_add_self (a 0))
  have ha01 : a 0 ≠ a 1 := by
    intro h
    have h1 : polar Q (a 0) (b 1) = 1 := by rw [h, (hp 1).ab]
    rw [h01.2.1] at h1
    exact zero_ne_one h1
  have hs_ne_one : s ≠ 1 := by
    intro h
    apply ha01
    have h1 := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (a 0)) h
    rw [hsa0] at h1
    simpa using h1.symm
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    eichler_mem_orthogonalGroup Q u v
  have hsΩ : s ∈ orthDerived Q :=
    rootGroup_le_orthDerived hQ (by omega) huQ (eichler_mem_rootGroup huv)
  let S : ↥(orthDerived Q) := ⟨s, hsΩ⟩
  have hSord : orderOf S = 2 :=
    orderOf_eq_prime (Subtype.ext (by dsimp only [S]; rw [pow_two]; exact hss))
      (fun h => hs_ne_one (congrArg Subtype.val h))
  let P : Subgroup ↥(orthDerived Q) := Subgroup.zpowers S
  have hPcard : Nat.card P = 2 := by rw [Nat.card_zpowers, hSord]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    omega
  let gen : Fin 5 → ↥(orthDerived Q) := fun i =>
    if h : i = 0 then rotOrthDerived Q (hp 0) * rotOrthDerived Q (hp 1)
    else rotOrthDerived Q (hp (Fin.succ i))
  let pt : Fin 5 → V := fun i => if h : i = 0 then u else a (Fin.succ i)
  let T : Subgroup ↥(orthDerived Q) :=
    Subgroup.closure (Set.range fun i : Fin 6 => rotOrthDerived Q (hp i))
  have hT : IsElemAbelian 3 T := by
    simpa [T] using (isElemAbelian_card_closure_rotOrthDerived hp hperp).1
  have hgenT : ∀ i, gen i ∈ T := by
    intro i
    dsimp only [gen]
    split_ifs with hi
    · exact T.mul_mem (Subgroup.subset_closure (Set.mem_range_self 0))
        (Subgroup.subset_closure (Set.mem_range_self 1))
    · exact Subgroup.subset_closure (Set.mem_range_self (Fin.succ i))
  have hcomm : ∀ i j, Commute (gen i) (gen j) := by
    intro i j
    exact congrArg Subtype.val (hT.1.is_comm.comm ⟨gen i, hgenT i⟩ ⟨gen j, hgenT j⟩)
  have hg0u : ((gen 0 : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) u = v := by
    dsimp only [gen, u, v]
    rw [dif_pos rfl, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have h0 : (rotOrthDerived Q (hp 0) : V ≃ₗ[ZMod 2] V) = rot Q (a 0) (b 0) := rfl
    have h1 : (rotOrthDerived Q (hp 1) : V ≃ₗ[ZMod 2] V) = rot Q (a 1) (b 1) := rfl
    rw [h0, h1]
    have hfix0 : rot Q (a 1) (b 1) (a 0) = a 0 :=
      (rot_fixes_of_pairPerp (hp 1) h01.symm).1
    have hmov1 : rot Q (a 1) (b 1) (a 1) = b 1 := rot_apply_left (hp 1)
    have hmov0 : rot Q (a 0) (b 0) (a 0) = b 0 := rot_apply_left (hp 0)
    have hfix1 : rot Q (a 0) (b 0) (b 1) = b 1 :=
      (rot_fixes_of_pairPerp (hp 0) h01).2
    rw [map_add, hfix0, hmov1, map_add, hmov0, hfix1]
  have hg0v : ((gen 0 : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v = u + v := by
    dsimp only [gen, u, v]
    rw [dif_pos rfl, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have h0 : (rotOrthDerived Q (hp 0) : V ≃ₗ[ZMod 2] V) = rot Q (a 0) (b 0) := rfl
    have h1 : (rotOrthDerived Q (hp 1) : V ≃ₗ[ZMod 2] V) = rot Q (a 1) (b 1) := rfl
    rw [h0, h1]
    have hfix0 : rot Q (a 1) (b 1) (b 0) = b 0 :=
      (rot_fixes_of_pairPerp (hp 1) h01.symm).2
    have hmov1 : rot Q (a 1) (b 1) (b 1) = a 1 + b 1 := rot_apply_right (hp 1)
    have hmov0 : rot Q (a 0) (b 0) (b 0) = a 0 + b 0 := rot_apply_right (hp 0)
    have hfix1 : rot Q (a 0) (b 0) (a 1 + b 1) = a 1 + b 1 := by
      rw [map_add]
      exact congrArg₂ (· + ·) (rot_fixes_of_pairPerp (hp 0) h01).1
        (rot_fixes_of_pairPerp (hp 0) h01).2
    rw [map_add, hfix0, hmov1, map_add, hmov0, hfix1]
    module
  have hvu : v ≠ u := by
    intro h
    have h1 : polar Q (a 0) u = 0 := by
      dsimp only [u]
      rw [polar_add_right, polar_self_zero, h01.1, add_zero]
    have h2 : polar Q (a 0) v = 1 := by
      dsimp only [v]
      rw [polar_add_right, (hp 0).ab, h01.2.1, add_zero]
    rw [h] at h2
    rw [h1] at h2
    exact zero_ne_one h2
  have hgen_ne_one : ∀ i, gen i ≠ 1 := by
    intro i
    by_cases hi : i = 0
    · subst hi
      intro h
      have h1 := hg0u
      rw [h] at h1
      exact hvu h1.symm
    · have hgi : gen i = rotOrthDerived Q (hp (Fin.succ i)) := by
        dsimp only [gen]
        rw [dif_neg hi]
      rw [hgi]
      intro h
      have h' : rot Q (a (Fin.succ i)) (b (Fin.succ i)) = 1 := by
        simpa [rotOrthDerived] using congrArg Subtype.val h
      exact rot_ne_one (Q := Q) (p := (a (Fin.succ i), b (Fin.succ i))) (hp (Fin.succ i)) h'
  have hord : ∀ i, orderOf (gen i) = 3 := by
    intro i
    refine orderOf_eq_prime ?_ (hgen_ne_one i)
    have h := hT.2 (gen i) (hgenT i)
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have hpt0 : pt 0 = u := by dsimp only [pt]; rw [dif_pos rfl]
  have hgen0 : gen 0 = rotOrthDerived Q (hp 0) * rotOrthDerived Q (hp 1) := by
    dsimp only [gen]; rw [dif_pos rfl]
  have hpt_succ : ∀ i : Fin 5, i ≠ 0 → pt i = a (Fin.succ i) := by
    intro i hi; dsimp only [pt]; rw [dif_neg hi]
  have hgen_succ : ∀ i : Fin 5, i ≠ 0 → gen i = rotOrthDerived Q (hp (Fin.succ i)) := by
    intro i hi; dsimp only [gen]; rw [dif_neg hi]
  have hmove : ∀ i, ((gen i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) (pt i) ≠ pt i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [hpt0, hg0u]
      exact hvu
    · rw [hpt_succ i hi, hgen_succ i hi]
      have h' : (rotOrthDerived Q (hp (Fin.succ i)) : V ≃ₗ[ZMod 2] V) (a (Fin.succ i)) =
          b (Fin.succ i) := by
        dsimp only [rotOrthDerived]; exact rot_apply_left (hp (Fin.succ i))
      rw [h']
      exact Ne.symm (hp (Fin.succ i)).ne
  have hrot_fix_u : ∀ j : Fin 5, j ≠ 0 →
      ((rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V)) u = u := by
    intro j hj
    have hfix0 : (rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V) (a 0) = a 0 := by
      dsimp only [rotOrthDerived]
      exact (rot_fixes_of_pairPerp (hp (Fin.succ j))
        (hperp (Fin.succ j) 0 (Fin.succ_ne_zero j))).1
    have hfix1 : (rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V) (a 1) = a 1 := by
      have hne : Fin.succ j ≠ (1 : Fin 6) := by
        intro h
        apply hj
        have h' : Fin.succ j = Fin.succ (0 : Fin 5) := by simpa using h
        exact Fin.succ_injective _ h'
      dsimp only [rotOrthDerived]
      exact (rot_fixes_of_pairPerp (hp (Fin.succ j)) (hperp (Fin.succ j) 1 hne)).1
    dsimp only [u]
    rw [map_add, hfix0, hfix1]
  have hrot_fix_v : ∀ j : Fin 5, j ≠ 0 →
      ((rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V)) v = v := by
    intro j hj
    have hfix0 : (rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V) (b 0) = b 0 := by
      dsimp only [rotOrthDerived]
      exact (rot_fixes_of_pairPerp (Q := Q) (p := (a (Fin.succ j), b (Fin.succ j)))
        (hp (Fin.succ j)) (hperp (Fin.succ j) 0 (Fin.succ_ne_zero j))).2
    have hfix1 : (rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V) (b 1) = b 1 := by
      have hne : Fin.succ j ≠ (1 : Fin 6) := by
        intro h
        apply hj
        have h' : Fin.succ j = Fin.succ (0 : Fin 5) := by simpa using h
        exact Fin.succ_injective _ h'
      dsimp only [rotOrthDerived]
      exact (rot_fixes_of_pairPerp (Q := Q) (p := (a (Fin.succ j), b (Fin.succ j)))
        (hp (Fin.succ j)) (hperp (Fin.succ j) 1 hne)).2
    dsimp only [v]
    rw [map_add, hfix0, hfix1]
  have hrot01_fix_a : ∀ i : Fin 5, i ≠ 0 →
      ((gen 0 : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) (a (Fin.succ i)) = a (Fin.succ i) := by
    intro i hi
    rw [hgen0, Subgroup.coe_mul, LinearEquiv.mul_apply]
    have h0 : (rotOrthDerived Q (hp 0) : V ≃ₗ[ZMod 2] V) = rot Q (a 0) (b 0) := rfl
    have h1 : (rotOrthDerived Q (hp 1) : V ≃ₗ[ZMod 2] V) = rot Q (a 1) (b 1) := rfl
    rw [h0, h1]
    have hne1 : Fin.succ i ≠ (1 : Fin 6) := by
      intro h
      apply hi
      have h' : Fin.succ i = Fin.succ (0 : Fin 5) := by simpa using h
      exact Fin.succ_injective _ h'
    have hfix1 : rot Q (a 1) (b 1) (a (Fin.succ i)) = a (Fin.succ i) :=
      (rot_fixes_of_pairPerp (hp 1) (hperp 1 (Fin.succ i) hne1.symm)).1
    have hfix0 : rot Q (a 0) (b 0) (a (Fin.succ i)) = a (Fin.succ i) :=
      (rot_fixes_of_pairPerp (hp 0) (hperp 0 (Fin.succ i) (Fin.succ_ne_zero i).symm)).1
    rw [hfix1, hfix0]
  have hrot_fix_a : ∀ i j : Fin 5, i ≠ j →
      ((rotOrthDerived Q (hp (Fin.succ j)) : V ≃ₗ[ZMod 2] V)) (a (Fin.succ i)) =
        a (Fin.succ i) := by
    intro i j hij
    have hne : Fin.succ i ≠ Fin.succ j := fun h => hij (Fin.succ_injective _ h)
    exact (rot_fixes_of_pairPerp (Q := Q) (p := (a (Fin.succ j), b (Fin.succ j)))
      (hp (Fin.succ j)) (hperp (Fin.succ i) (Fin.succ j) hne).symm).1
  have hfix : ∀ i j, i ≠ j →
      ((gen j : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) (pt i) = pt i := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      rw [hpt0]
      by_cases hj : j = 0
      · exact absurd hj.symm hij
      · rw [hgen_succ j hj]
        exact hrot_fix_u j hj
    · rw [hpt_succ i hi]
      by_cases hj : j = 0
      · subst hj
        rw [hgen0]
        exact hrot01_fix_a i hi
      · rw [hgen_succ j hj]
        exact hrot_fix_a i j hij
  have hindep : ∀ i, gen i ∉ Subgroup.closure (gen '' {j | j ≠ i}) :=
    not_mem_closure_image_of_smul_ne (φ := (orthDerived Q).subtype) (e := gen) (x := pt)
      hmove hfix
  have hE := isElemAbelian_card_closure_range (p := 3) gen hcomm hord hindep
  let E : Subgroup ↥(orthDerived Q) := Subgroup.closure (Set.range gen)
  have hEel : IsElemAbelian 3 E := by simpa [E] using hE.1
  have hEcard : Nat.card E = 3 ^ 5 := by simpa [E] using hE.2
  have hgen_cent : ∀ i, gen i ∈ Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    by_cases hi : i = 0
    · subst hi
      have hO : ((gen 0 : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup (gen 0).2
      have hconj := eichler_conj hO u v
      rw [hg0u, hg0v, eichler_swap_add huQ hvQ huv] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj
    · have hgi : gen i = rotOrthDerived Q (hp (Fin.succ i)) := hgen_succ i hi
      have hO : ((gen i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈
          TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup (gen i).2
      have hgu : ((gen i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) u = u := by
        rw [hgi]; exact hrot_fix_u i hi
      have hgv : ((gen i : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v = v := by
        rw [hgi]; exact hrot_fix_v i hi
      have hconj := eichler_conj hO u v
      rw [hgu, hgv] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj
  have hEcent : E ≤ Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) := by
    dsimp only [E]
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen_cent i
  have hcentP : Subgroup.centralizer ({S} : Set ↥(orthDerived Q)) ≤
      Subgroup.centralizer (P : Set ↥(orthDerived Q)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : Commute S g := hg S (Set.mem_singleton S)
    exact (hc.zpow_left k).eq
  have hEnorm : E ≤ Subgroup.normalizer (P : Set ↥(orthDerived Q)) :=
    hEcent.trans (hcentP.trans (Subgroup.centralizer_le_normalizer (P : Set ↥(orthDerived Q))))
  exact ⟨E, hEel, hEcard, ⟨P, hP2, hPne, hEnorm⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent CFSG.LocalAnalysis.GLTheoremA.S172B.Rank
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem noSmallModel_plus_six (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 6) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    NoSmallModel ↥(orthDerived Q) := by
  intro Bb h
  obtain ⟨E, hEel, hEcard, hEtwo⟩ := exists_twoLocal_three_pow_five_six hQ hdim hplus
  have hle := h.max E hEel hEtwo
  rw [hEcard] at hle
  have hle' : Nat.card Bb ≤ 3 ^ 4 := by simpa using h.card_le
  have hcontra : (3 ^ 5 : ℕ) ≤ 3 ^ 4 := hle.trans hle'
  norm_num at hcontra

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
