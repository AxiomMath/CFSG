module

public import CFSG.CGT.PushingUpLit.SolK.Length
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.LocalAnalysis.ComponentInitial (alternating_perfect_central_two_kernel_order_at_most_two)
open scoped commutatorElement

abbrev zOf {G : Type} [Group G] (M X : Subgroup G) : Subgroup G := pCoreOf 2 X ⊓ rOf M X

theorem eq_of_card_le_two {H : Type*} [Group H] [Finite H] (h : Nat.card H ≤ 2) {a b : H}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Fintype H := Fintype.ofFinite H
  have h3 : 3 ≤ Nat.card H := by
    rw [Nat.card_eq_fintype_card]
    calc 3 = ({1, a, b} : Finset H).card := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm ha, Ne.symm hb⟩
      _ ≤ Fintype.card H := Finset.card_le_univ _
  omega

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

open Classical in
noncomputable def SolCfg.bW {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}
    (S : SolCfg G M X n) (g : G) : ↥(coreMod (2 * n + 1)) :=
  if h : g ∈ S.D.W then S.D.β ⟨g, h⟩ else 1

namespace SolCfg

include S

theorem exists_mul_zOf {y : G} (hy : y ∈ pCoreOf 2 X) :
    ∃ w ∈ S.D.W, ∃ z ∈ zOf M X, y = w * z := by
  obtain ⟨w, hw, r, hr, e⟩ := S.q_eq y (S.xnorm.Y_le_Q hy)
  refine ⟨w, hw, r, ⟨?_, hr⟩, e⟩
  have : r = w⁻¹ * y := by rw [e]; group
  rw [this]
  exact Subgroup.mul_mem _ ((pCoreOf 2 X).inv_mem (ModData.W_le_Y S.D hw)) hy

theorem perfect_X : Group.IsPerfect ↥X := by
  classical
  rw [Group.isPerfect_def]
  have hn : 2 ≤ n := S.hyp.two_le
  set c : Subgroup ↥X := commutator ↥X with hc
  let A : Subgroup (Perm (Fin (2 * n + 1))) := alternatingGroup (Fin (2 * n + 1))
  let ρ' : ↥X →* ↥A := S.D.ρ.codRestrict _ S.D.ρ_alt
  have hρ's : Function.Surjective ρ' := fun a => by
    obtain ⟨x, hx⟩ := S.D.ρ_surj a a.2
    exact ⟨x, Subtype.ext hx⟩
  have hAtop : commutator ↥A = ⊤ :=
    commutator_alternatingGroup_eq_top (by simpa using (by omega : 5 ≤ 2 * n + 1))
  have hmap : c.map ρ' = ⊤ := by
    rw [hc, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 hρ's, ← commutator_def, hAtop]
  have hXY : ∀ x : ↥X, ∃ c' ∈ c, ∃ y : ↥X, (y : G) ∈ pCoreOf 2 X ∧ x = c' * y := by
    intro x
    have hx : ρ' x ∈ c.map ρ' := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨c', hc', hcx⟩ := Subgroup.mem_map.1 hx
    refine ⟨c', hc', c'⁻¹ * x, ?_, by group⟩
    rw [← S.D.ker]
    have h1 : ρ' (c'⁻¹ * x) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
    simpa [ρ'] using congrArg Subtype.val h1
  have hP : IsPGroup 2 (↥X ⧸ c) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨c', hc', y, hy, rfl⟩ := hXY x
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' X ⟨y, hy⟩
    refine ⟨j, ?_⟩
    have hyj : y ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      exact Subtype.ext (by simpa using this)
    have hcy : (QuotientGroup.mk (c' * y) : ↥X ⧸ c) = QuotientGroup.mk y := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c').2 hc', one_mul]
    rw [hcy, ← QuotientGroup.mk_pow, hyj]
    rfl
  have hf := hom_eq_one_of_oResidual S.res hP (QuotientGroup.mk' c)
  rw [eq_top_iff]
  intro x _
  have := DFunLike.congr_fun hf x
  exact (QuotientGroup.eq_one_iff x).1 (by simpa using this)

theorem card_zOf_le_two : Nat.card ↥(zOf M X) ≤ 2 := by
  classical
  have hn : 2 ≤ n := S.hyp.two_le
  have h5 : 5 ≤ 2 * n + 1 := by omega
  let W' : Subgroup ↥X := S.D.W.subgroupOf X
  have hW'n : W'.Normal := ⟨fun w hw x => by
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact S.W_normalized (S.hyp.le x.2) hw⟩
  let ρ' : ↥X →* ↥(alternatingGroup (Fin (2 * n + 1))) := S.D.ρ.codRestrict _ S.D.ρ_alt
  have hρ's : Function.Surjective ρ' := fun a => by
    obtain ⟨x, hx⟩ := S.D.ρ_surj a a.2
    exact ⟨x, Subtype.ext hx⟩
  have hρ'ker : ∀ x : ↥X, ρ' x = 1 ↔ (x : G) ∈ pCoreOf 2 X := fun x => by
    rw [← S.D.ker]
    constructor
    · intro h; simpa [ρ'] using congrArg Subtype.val h
    · intro h; exact Subtype.ext (by simpa [ρ'] using h)
  have hW'le : W' ≤ ρ'.ker := fun w hw => by
    rw [MonoidHom.mem_ker, hρ'ker]
    exact ModData.W_le_Y S.D hw
  let η : (↥X ⧸ W') →* ↥(alternatingGroup (Fin (2 * n + 1))) := QuotientGroup.lift W' ρ' hW'le
  have hηs : Function.Surjective η := fun a => by
    obtain ⟨x, hx⟩ := hρ's a
    exact ⟨QuotientGroup.mk x, by simpa [η] using hx⟩
  have : Group.IsPerfect (↥X ⧸ W') := by
    have := S.perfect_X
    infer_instance
  have hηker : ∀ g : ↥X ⧸ W', g ∈ η.ker → ∃ x : ↥X, g = QuotientGroup.mk x ∧
      (x : G) ∈ pCoreOf 2 X := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨x, rfl, ?_⟩
    rw [← hρ'ker]
    simpa [η] using hg
  have hcenter : η.ker ≤ Subgroup.center (↥X ⧸ W') := by
    intro g hg
    obtain ⟨x, rfl, hxY⟩ := hηker g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective g'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    have hxinv : ((x⁻¹ : ↥X) : G) ∈ pCoreOf 2 X := by
      have : ((x : ↥X) : G)⁻¹ ∈ pCoreOf 2 X := (pCoreOf 2 X).inv_mem hxY
      simpa using this
    have hmem : ⁅((x⁻¹ : ↥X) : G), ((x'⁻¹ : ↥X) : G)⁆ ∈ S.D.W := by
      rw [S.D.W_eq]
      exact Subgroup.commutator_mem_commutator hxinv (x'⁻¹).2
    have e : ((x' * x)⁻¹ * (x * x') : ↥X) = ⁅x⁻¹, x'⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    simpa [commutatorElement_def] using hmem
  have hker2 : IsPGroup 2 η.ker := by
    intro g
    obtain ⟨x, hg, hxY⟩ := hηker g g.2
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' X ⟨x, hxY⟩
    refine ⟨j, Subtype.ext ?_⟩
    have hxj : x ^ (2 ^ j) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
    show (g : ↥X ⧸ W') ^ (2 ^ j) = 1
    rw [hg, ← QuotientGroup.mk_pow, hxj]
    rfl
  have hle := alternating_perfect_central_two_kernel_order_at_most_two h5 η hηs hcenter hker2
  have hZX : ∀ z : ↥(zOf M X), (z : G) ∈ X := fun z => pCoreOf_le_self X z.2.1
  let f : ↥(zOf M X) → ↥η.ker := fun z => ⟨QuotientGroup.mk ⟨z, hZX z⟩, by
    rw [MonoidHom.mem_ker]
    show ρ' ⟨z, hZX z⟩ = 1
    rw [hρ'ker]
    exact z.2.1⟩
  have hf : Function.Injective f := by
    intro z z' h
    have h1 := congrArg Subtype.val h
    simp only [f] at h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 : ((z : G))⁻¹ * z' ∈ S.D.W := by simpa using h1
    have h3 : ((z : G))⁻¹ * z' ∈ rOf M X :=
      (rOf M X).mul_mem ((rOf M X).inv_mem z.2.2) z'.2.2
    have h4 : ((z : G))⁻¹ * z' = 1 := S.W_inf_R h2 h3
    refine Subtype.ext ?_
    have h5 := congrArg (fun t => (z : G) * t) h4
    exact (by simpa [mul_assoc] using h5 : (z' : G) = z).symm
  exact (Nat.card_le_card_of_injective f hf).trans hle

theorem bW_of_mem {g : G} (h : g ∈ S.D.W) : S.bW g = S.D.β ⟨g, h⟩ := by
  simp [SolCfg.bW, h]

theorem bW_mul {g g' : G} (hg : g ∈ S.D.W) (hg' : g' ∈ S.D.W) :
    S.bW (g * g') = S.bW g * S.bW g' := by
  rw [S.bW_of_mem hg, S.bW_of_mem hg', S.bW_of_mem (S.D.W.mul_mem hg hg'), ← map_mul]
  rfl

theorem bW_inv {g : G} (hg : g ∈ S.D.W) : S.bW g⁻¹ = (S.bW g)⁻¹ := by
  rw [S.bW_of_mem hg, S.bW_of_mem (S.D.W.inv_mem hg)]
  exact map_inv S.D.β ⟨g, hg⟩

theorem bW_conj {g : G} (hg : g ∈ S.D.W) (x : ↥X) :
    S.bW ((x : G) * g * (x : G)⁻¹) = coreAct (2 * n + 1) (S.D.ρ x) (S.bW g) := by
  have hg' : (x : G) * g * (x : G)⁻¹ ∈ S.D.W := S.W_normalized (S.hyp.le x.2) hg
  rw [S.bW_of_mem hg, S.bW_of_mem hg']
  exact S.D.equivar x ⟨g, hg⟩ hg'

theorem bW_eq_one {g : G} (hg : g ∈ S.D.W) (h : S.bW g = 1) : g = 1 := by
  rw [S.bW_of_mem hg] at h
  have := S.D.β.injective (h.trans (map_one S.D.β).symm)
  exact congrArg Subtype.val this

theorem ker_centralizes_Y (m : ↥M) (hm : S.θ m = 1) {y : G} (hy : y ∈ pCoreOf 2 X) :
    (m : G) * y * (m : G)⁻¹ = y := by
  obtain ⟨w, hw, z, hz, rfl⟩ := S.exists_mul_zOf hy
  have hmW : (m : G) * w * (m : G)⁻¹ = w :=
    (theta_eq_one_iff S.D S.xnorm S.hyp.two_le m).1 hm w hw
  have hmz : (m : G) * z * (m : G)⁻¹ = z := by
    by_cases hz1 : z = 1
    · rw [hz1]; group
    · have hmzmem : (m : G) * z * (m : G)⁻¹ ∈ zOf M X :=
        ⟨S.xnorm.Y_normalized m.2 hz.1, S.R_normalized m.2 hz.2⟩
      have hne : (⟨(m : G) * z * (m : G)⁻¹, hmzmem⟩ : ↥(zOf M X)) ≠ 1 := fun h => hz1 (by
        have h1 : (m : G) * z * (m : G)⁻¹ = 1 := congrArg Subtype.val h
        have h2 := congrArg (fun t => (m : G)⁻¹ * t * (m : G)) h1
        simpa [mul_assoc] using h2)
      have hne' : (⟨z, hz⟩ : ↥(zOf M X)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
      exact congrArg Subtype.val (eq_of_card_le_two S.card_zOf_le_two hne hne')
  calc (m : G) * (w * z) * (m : G)⁻¹ = ((m : G) * w * (m : G)⁻¹) * ((m : G) * z * (m : G)⁻¹) := by
        group
    _ = w * z := by rw [hmW, hmz]

theorem exists_mul_ker_centralizes (m : ↥M) (hm : S.θ m = 1) :
    ∃ w ∈ S.D.W, w * (m : G) ∈ Subgroup.centralizer (X : Set G) := by
  classical
  have hn : 2 ≤ n := S.hyp.two_le
  have hcomm_mem : ∀ x : ↥X, ⁅(m : G), (x : G)⁆ ∈ pCoreOf 2 X := by
    intro x
    have hx' : (m : G) * x * (m : G)⁻¹ ∈ X := S.xnorm.normal m m.2 x x.2
    let x' : ↥X := ⟨(m : G) * x * (m : G)⁻¹, hx'⟩
    have hρ : S.D.ρ x' = S.D.ρ x := by
      have h1 : S.θ ⟨(x' : G), S.hyp.le x'.2⟩ =
          S.θ m * S.θ ⟨(x : G), S.hyp.le x.2⟩ * (S.θ m)⁻¹ := by
        have : (⟨(x' : G), S.hyp.le x'.2⟩ : ↥M) = m * ⟨(x : G), S.hyp.le x.2⟩ * m⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv]
      rw [S.θ_X x', hm, S.θ_X x] at h1
      simpa using h1
    have hy0 : ((x' * x⁻¹ : ↥X) : G) ∈ pCoreOf 2 X := by
      rw [← S.D.ker, map_mul, map_inv, hρ, mul_inv_cancel]
    have e : ((x' * x⁻¹ : ↥X) : G) = ⁅(m : G), (x : G)⁆ := by
      simp only [x', commutatorElement_def]
      simp
    rwa [e] at hy0
  have hdec : ∀ x : ↥X, ∃ w ∈ S.D.W, ∃ z ∈ zOf M X, ⁅(m : G), (x : G)⁆ = w * z :=
    fun x => S.exists_mul_zOf (hcomm_mem x)
  choose w hwW z hzZ hwz using hdec
  have hzmul : ∀ x x' : ↥X, z (x * x') = z x * z x' := by
    intro x x'
    have h1 : ⁅(m : G), ((x * x' : ↥X) : G)⁆ =
        (w x * z x) * ((x : G) * (w x' * z x') * (x : G)⁻¹) := by
      rw [Subgroup.coe_mul, commutator_mul_right, hwz x, hwz x']
    have hxz : (x : G) * z x' * (x : G)⁻¹ = z x' := by
      have := Subgroup.mem_centralizer_iff.1 (hzZ x').2.2 (x : G) x.2
      rw [this, mul_inv_cancel_right]
    have hcw : z x * ((x : G) * w x' * (x : G)⁻¹) = ((x : G) * w x' * (x : G)⁻¹) * z x :=
      (S.W_comm_R (S.W_normalized (S.hyp.le x.2) (hwW x')) (hzZ x).2).symm
    have h2 : (w x * z x) * ((x : G) * (w x' * z x') * (x : G)⁻¹) =
        (w x * ((x : G) * w x' * (x : G)⁻¹)) * (z x * z x') := by
      have e : (x : G) * (w x' * z x') * (x : G)⁻¹ =
          ((x : G) * w x' * (x : G)⁻¹) * ((x : G) * z x' * (x : G)⁻¹) := by group
      rw [e, hxz]
      calc w x * z x * ((x : G) * w x' * (x : G)⁻¹ * z x') =
          w x * (z x * ((x : G) * w x' * (x : G)⁻¹)) * z x' := by group
        _ = w x * (((x : G) * w x' * (x : G)⁻¹) * z x) * z x' := by rw [hcw]
        _ = (w x * ((x : G) * w x' * (x : G)⁻¹)) * (z x * z x') := by group
    have h3 : w (x * x') * z (x * x') =
        (w x * ((x : G) * w x' * (x : G)⁻¹)) * (z x * z x') := by
      rw [← hwz (x * x'), h1, h2]
    have hW1 : w (x * x') ∈ S.D.W := hwW _
    have hW2 : w x * ((x : G) * w x' * (x : G)⁻¹) ∈ S.D.W :=
      S.D.W.mul_mem (hwW x) (S.W_normalized (S.hyp.le x.2) (hwW x'))
    exact (S.decomp_unique hW1 hW2 (hzZ _).2 ((rOf M X).mul_mem (hzZ x).2 (hzZ x').2) h3).2
  have hz1 : ∀ x : ↥X, z x = 1 := by
    have hZX : ∀ x : ↥X, z x ∈ X := fun x => pCoreOf_le_self X (hzZ x).1
    let B : Subgroup ↥X := (zOf M X).subgroupOf X
    have hB2 : IsPGroup 2 ↥B := by
      intro b
      have hbY : ((b : ↥X) : G) ∈ pCoreOf 2 X := b.2.1
      obtain ⟨j, hj⟩ := isPGroup_pCoreOf' X ⟨((b : ↥X) : G), hbY⟩
      refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hj
      simpa using this
    intro x
    have := forall_eq_one_of_mul (L := ↥X) (B := B) S.res hB2 (fun x => ⟨z x, hZX x⟩)
      (fun x => hzZ x) (fun a b => Subtype.ext (hzmul a b)) x
    exact congrArg Subtype.val this
  have hwx : ∀ x : ↥X, ⁅(m : G), (x : G)⁆ = w x := fun x => by rw [hwz x, hz1 x, mul_one]
  let c : ↥X → ↥(coreMod (2 * n + 1)) := fun x => S.bW (w x)
  have hwmul : ∀ x x' : ↥X, w (x * x') = w x * ((x : G) * w x' * (x : G)⁻¹) := by
    intro x x'
    have := hwx (x * x')
    rw [Subgroup.coe_mul, commutator_mul_right, hwx x, hwx x'] at this
    exact this.symm
  have hc : ∀ x x', c (x * x') = c x * coreAct (2 * n + 1) (S.D.ρ x) (c x') := by
    intro x x'
    show S.bW (w (x * x')) = S.bW (w x) * coreAct (2 * n + 1) (S.D.ρ x) (S.bW (w x'))
    rw [hwmul, S.bW_mul (hwW x) (S.W_normalized (S.hyp.le x.2) (hwW x')), S.bW_conj (hwW x') x]
  have hker : ∀ x : ↥X, S.D.ρ x = 1 → c x = 1 := by
    intro x hx
    have hxY : (x : G) ∈ pCoreOf 2 X := (S.D.ker x).1 hx
    have h1 := S.ker_centralizes_Y m hm hxY
    have h2 : w x = 1 := by
      rw [← hwx x, commutatorElement_def]
      have : (m : G) * x * (m : G)⁻¹ = x := h1
      rw [this]
      group
    show S.bW (w x) = 1
    rw [h2]
    rw [S.bW_of_mem S.D.W.one_mem]
    exact map_one S.D.β
  obtain ⟨u, hu⟩ := cocycle_coboundary_of_surj (n := 2 * n + 1) (odd_two_mul_add_one n)
    (by omega) S.D.ρ S.D.ρ_alt S.D.ρ_surj c hc hker
  set w₀ : ↥S.D.W := S.D.β.symm u with hw₀
  have hbw₀ : S.bW (w₀ : G) = u := by
    rw [S.bW_of_mem w₀.2]
    simp [hw₀]
  refine ⟨(w₀ : G), w₀.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let x₁ : ↥X := ⟨x, hx⟩
  have hx1 : (x₁ : G) = x := rfl
  have hmx : (m : G) * x * (m : G)⁻¹ = w x₁ * x := by
    rw [← hwx x₁, commutatorElement_def, hx1]
    group
  have ht : (w₀ : G) * w x₁ * ((x : G) * (w₀ : G)⁻¹ * (x : G)⁻¹) = 1 := by
    have hW : (w₀ : G) * w x₁ * ((x : G) * (w₀ : G)⁻¹ * (x : G)⁻¹) ∈ S.D.W :=
      S.D.W.mul_mem (S.D.W.mul_mem w₀.2 (hwW x₁))
        (S.W_normalized (S.hyp.le hx) (S.D.W.inv_mem w₀.2))
    refine S.bW_eq_one hW ?_
    rw [S.bW_mul (S.D.W.mul_mem w₀.2 (hwW x₁))
        (S.W_normalized (S.hyp.le hx) (S.D.W.inv_mem w₀.2)),
      S.bW_mul w₀.2 (hwW x₁), S.bW_conj (S.D.W.inv_mem w₀.2) x₁, S.bW_inv w₀.2, hbw₀]
    have h1 : S.bW (w x₁) = u * coreAct (2 * n + 1) (S.D.ρ x₁) u := hu x₁
    rw [h1]
    refine vcoord_ext fun i => ?_
    simp only [vcoord_mul, vcoord_inv, vcoord_coreAct, vcoord_one]
    generalize vcoord u i = a
    generalize vcoord u ((S.D.ρ x₁)⁻¹ i) = b
    revert a b
    decide
  show x * ((w₀ : G) * (m : G)) = ((w₀ : G) * (m : G)) * x
  have e1 : (w₀ : G) * (m : G) * x = (w₀ : G) * ((m : G) * x * (m : G)⁻¹) * (m : G) := by group
  rw [e1, hmx]
  have e2 : (w₀ : G) * (w x₁ * x) * (m : G) =
      ((w₀ : G) * w x₁ * ((x : G) * (w₀ : G)⁻¹ * (x : G)⁻¹)) * (x * (w₀ : G)) * (m : G) := by
    group
  rw [e2, ht, one_mul]
  group

theorem abelian_of_R_abelian (hR : ∀ r ∈ rOf M X, ∀ r' ∈ rOf M X, r * r' = r' * r) :
    ∀ q ∈ pCoreOf 2 M, ∀ q' ∈ pCoreOf 2 M, q * q' = q' * q := by
  intro q hq q' hq'
  obtain ⟨w, hw, r, hr, rfl⟩ := S.q_eq q hq
  obtain ⟨w', hw', r', hr', rfl⟩ := S.q_eq q' hq'
  have h1 : r * w' = w' * r := (S.W_comm_R hw' hr).symm
  have h2 : r' * w = w * r' := (S.W_comm_R hw hr').symm
  calc w * r * (w' * r') = w * (r * w') * r' := by group
    _ = (w * w') * (r * r') := by rw [h1]; group
    _ = (w' * w) * (r' * r) := by rw [S.D.comm hw hw', hR r hr r' hr']
    _ = w' * (w * r') * r := by group
    _ = w' * r' * (w * r) := by rw [← h2]; group

theorem ker_two_of_sylow
    (hC2 : ∀ c ∈ M ⊓ Subgroup.centralizer (X : Set G), (∃ j : ℕ, c ^ (2 ^ j) = 1) →
      c ∈ rOf M X)
    (m : ↥M) (hm : S.θ m = 1) (h2 : ∃ j : ℕ, (m : G) ^ (2 ^ j) = 1) :
    (m : G) ∈ pCoreOf 2 M := by
  obtain ⟨w, hw, hc⟩ := S.exists_mul_ker_centralizes m hm
  have hmw : (m : G) * w * (m : G)⁻¹ = w := (theta_eq_one_iff S.D S.xnorm S.hyp.two_le m).1 hm w hw
  have hcomm : Commute w (m : G) := by
    have : w * (m : G) = (m : G) * w := (comm_of_conj_eq hmw).symm
    exact this
  obtain ⟨j, hj⟩ := h2
  have hw2 : w ^ 2 = 1 := S.D.sq hw
  have hwQ : w ∈ pCoreOf 2 M := S.W_le_Q hw
  have hcM : w * (m : G) ∈ M := M.mul_mem (pCoreOf_le_self M hwQ) m.2
  have hc2 : ∃ j : ℕ, (w * (m : G)) ^ (2 ^ j) = 1 := by
    refine ⟨j + 1, ?_⟩
    have e1 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
    have e2 : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := by ring
    have hwp : w ^ (2 ^ (j + 1)) = 1 := by rw [e1, pow_mul, hw2, one_pow]
    have hmp : (m : G) ^ (2 ^ (j + 1)) = 1 := by rw [e2, pow_mul, hj, one_pow]
    rw [hcomm.mul_pow, hwp, hmp, one_mul]
  have hcR : w * (m : G) ∈ rOf M X := hC2 _ ⟨hcM, hc⟩ hc2
  have : (m : G) = w⁻¹ * (w * (m : G)) := by group
  rw [this]
  exact Subgroup.mul_mem _ ((pCoreOf 2 M).inv_mem hwQ) hcR.1

end SolCfg

theorem tightData_of_cor28
    (hR : ∀ r ∈ rOf M X, ∀ r' ∈ rOf M X, r * r' = r' * r)
    (hC2 : ∀ c ∈ M ⊓ Subgroup.centralizer (X : Set G), (∃ j : ℕ, c ^ (2 ^ j) = 1) →
      c ∈ rOf M X) : TightData S :=
  ⟨S.abelian_of_R_abelian hR, fun m hm h2 => S.ker_two_of_sylow hC2 m hm h2⟩

end CFSG.CGT.PushingUpLit.SolK
