module

public import CFSG.LargeExtraspecial.S8CBFA5Lin
public import CFSG.LargeExtraspecial.S8CBFA5Core
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise commutatorElement

@[expose] noncomputable def g2Beta (K : Type*) [Field K] :
    (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun v w => v 0 * w 3 + w 0 * v 3 + v 1 * w 2 + w 1 * v 2)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem g2Beta_apply {K : Type*} [Field K] (v w : Fin 4 → K) :
    g2Beta K v w = v 0 * w 3 + w 0 * v 3 + v 1 * w 2 + w 1 * v 2 := rfl

variable {K : Type} [Field K] [CharP K 2]


theorem g2N_zero_commutator (B C D E F B' C' D' E' F' : K) :
    ⁅g2N 0 B C D E F, g2N 0 B' C' D' E' F'⁆ =
      g2N 0 0 0 0 0 (B * E' + B' * E + C * D' + C' * D) := by
  rw [commutatorElement_def, g2N_zero_inv, g2N_zero_inv, g2N_zero_mul_g2N_zero,
    g2N_zero_mul_g2N_zero, g2N_zero_mul_g2N_zero]
  refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem relA5At_G2_long [Finite K] :
    RelA5At (adjointGroup .G2 K) (pinnedX .G2 K g2c 1) := by
  obtain ⟨-, -, -, hC, hset, hLN, hQL, ⟨ρ, -, -, hρ, hρi⟩, hXc, ⟨π, hπker, -, hπ⟩, -, -⟩ :=
    even_G2_highest_long_root_centralizer K
  intro R N hNR hR hperf hnorm hN2 hZ hCm
  have hQn := normalizes_of_mul_eq hset hLN
  have hNQ : N ≤ g2LongRadical K :=
    le_of_perfect_of_semidirect_sl2 hset (hC ▸ le_sup_right) hQn hQL ρ hρ hρi hR hperf hNR
      hnorm hN2
  have hz : pinnedX .G2 K g2c 1 = g2N 0 0 0 0 0 1 := pinnedX_c_eq_g2N 1
  have hcoord : ∀ q : g2LongRadical K, ∃ B C D E F : K, (q : ModGL .G2 K) = g2N 0 B C D E F ∧
      π q = Multiplicative.ofAdd ![B, C, D, E] := by
    intro q
    obtain ⟨B, C, D, E, F, hq⟩ := q.2
    refine ⟨B, C, D, E, F, hq, ?_⟩
    have : q = ⟨g2N 0 B C D E F, hq ▸ q.2⟩ := Subtype.ext hq
    rw [this, hπ]
  have hval : ∀ F : K, g2N 0 0 0 0 0 F = 1 ∨ g2N 0 0 0 0 0 F = pinnedX .G2 K g2c 1 →
      F = 0 ∨ F = 1 := by
    rintro F (h | h)
    · left
      rw [← g2N_zero] at h
      exact (g2N_injective h).2.2.2.2.2
    · right
      rw [hz] at h
      exact (g2N_injective h).2.2.2.2.2
  let N' : Subgroup (g2LongRadical K) := N.subgroupOf (g2LongRadical K)
  let φ : N' →* Multiplicative (Fin 4 → K) := π.comp N'.subtype
  have hz1 : pinnedX .G2 K g2c 1 ≠ 1 := by
    intro h
    rw [hz, ← g2N_zero] at h
    exact one_ne_zero (g2N_injective h).2.2.2.2.2
  have hrange : Nat.card φ.range ≤ 2 ^ 4 := by
    refine card_le_of_bilinear φ.range (g2Beta K) ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      obtain ⟨B, C, D, E, F, hx, hπx⟩ := hcoord (x : g2LongRadical K)
      obtain ⟨B', C', D', E', F', hx', hπx'⟩ := hcoord (x' : g2LongRadical K)
      have h1 := hCm _ (mem_subgroupOf.mp x.2) _ (mem_subgroupOf.mp x'.2)
      rw [hx, hx', g2N_zero_commutator] at h1
      have e1 : φ x = Multiplicative.ofAdd ![B, C, D, E] := hπx
      have e2 : φ x' = Multiplicative.ofAdd ![B', C', D', E'] := hπx'
      rw [e1, e2, toAdd_ofAdd, toAdd_ofAdd, g2Beta_apply]
      simpa using hval _ h1
    · rintro _ ⟨x, rfl⟩ hx0
      obtain ⟨B, C, D, E, F, hx, hπx⟩ := hcoord (x : g2LongRadical K)
      have hcen : ∀ y ∈ N, ((x : g2LongRadical K) : ModGL .G2 K) * y = y * x := by
        intro y hy
        let y' : N' := ⟨⟨y, hNQ hy⟩, mem_subgroupOf.mpr hy⟩
        obtain ⟨B', C', D', E', F', hy', hπy'⟩ := hcoord (y' : g2LongRadical K)
        have h2 := hx0 (φ y') ⟨y', rfl⟩
        have e1 : φ x = Multiplicative.ofAdd ![B, C, D, E] := hπx
        have e2 : φ y' = Multiplicative.ofAdd ![B', C', D', E'] := hπy'
        rw [e1, e2, toAdd_ofAdd, toAdd_ofAdd, g2Beta_apply] at h2
        have h4 : B * E' + B' * E + C * D' + C' * D = 0 := by simpa using h2
        have h3 : ⁅((x : g2LongRadical K) : ModGL .G2 K), y⁆ = 1 := by
          have hy'' : y = g2N 0 B' C' D' E' F' := hy'
          rw [hx, hy'', g2N_zero_commutator, h4, g2N_zero]
        exact commutatorElement_eq_one_iff_mul_comm.mp h3
      rcases hZ _ (mem_subgroupOf.mp x.2) hcen with h | h
      · have hx1 : x = 1 := Subtype.ext (Subtype.ext h)
        rw [hx1, map_one]
      · have hxz : (x : g2LongRadical K) = ⟨g2N 0 0 0 0 0 1, hz ▸ h ▸ (x : g2LongRadical K).2⟩ :=
          Subtype.ext (h.trans hz)
        change π (x : g2LongRadical K) = 1
        rw [hxz, hπ, ofAdd_eq_one]
        funext i
        fin_cases i <;> rfl
  have hker : Nat.card φ.ker ≤ 2 := by
    classical
    have hmem : ∀ x : φ.ker, (((x : N') : g2LongRadical K) : ModGL .G2 K) = 1 ∨
        (((x : N') : g2LongRadical K) : ModGL .G2 K) = pinnedX .G2 K g2c 1 := by
      intro x
      have hxk : ((x : N') : g2LongRadical K) ∈ π.ker := x.2
      rw [hπker, mem_subgroupOf, Blueprint.Chevalley.mem_rootSubgroup] at hxk
      obtain ⟨c, hc⟩ := hxk
      refine hZ _ (mem_subgroupOf.mp (x : N').2) fun y hy => ?_
      rw [← hc]
      exact ((hXc c).2 y (hNQ hy)).eq
    let g : φ.ker → Bool := fun x => decide ((((x : N') : g2LongRadical K) : ModGL .G2 K) = 1)
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      have hgv : ∀ w : φ.ker, (((w : N') : g2LongRadical K) : ModGL .G2 K) = 1 → g w = true :=
        fun w hw => by
          change decide ((((w : N') : g2LongRadical K) : ModGL .G2 K) = 1) = true
          rw [hw]
          exact decide_eq_true rfl
      have hgv' : ∀ w : φ.ker, (((w : N') : g2LongRadical K) : ModGL .G2 K) =
          pinnedX .G2 K g2c 1 → g w = false := fun w hw => by
        change decide ((((w : N') : g2LongRadical K) : ModGL .G2 K) = 1) = false
        rw [hw]
        exact decide_eq_false hz1
      rcases hmem x with hx | hx <;> rcases hmem y with hy | hy
      · rw [hx, hy]
      · rw [hgv x hx, hgv' y hy] at hxy
        exact absurd hxy Bool.noConfusion
      · rw [hgv' x hx, hgv y hy] at hxy
        exact absurd hxy Bool.noConfusion
      · rw [hx, hy]
    calc Nat.card φ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective g hg
      _ = 2 := by simp
  have hN' : Nat.card N = Nat.card N' := Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv.symm
  have hsplit : Nat.card N' = Nat.card φ.range * Nat.card φ.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  rw [hN', hsplit]
  calc Nat.card φ.range * Nat.card φ.ker ≤ 2 ^ 4 * 2 := Nat.mul_le_mul hrange hker
    _ = 2 ^ 5 := by norm_num

theorem relA5At_G2_short [Finite K] :
    RelA5At (adjointGroup .G2 K) (pinnedX .G2 K g2v 1) := by
  classical
  obtain ⟨-, -, hEA, hC, hset, hLN, hQL, ⟨ρ, -, -, hρ, hρi⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  intro R N hNR hR hperf hnorm hN2 hZ hCm
  have hQn := normalizes_of_mul_eq hset hLN
  have hNA : N ≤ g2ShortRadical K :=
    le_of_perfect_of_semidirect_sl2 hset (hC ▸ le_sup_right) hQn hQL ρ hρ hρi hR hperf hNR
      hnorm hN2
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm ⟨x, hNA hx⟩ ⟨y, hNA hy⟩)
  have hmem : ∀ x : N, (x : ModGL .G2 K) = 1 ∨ (x : ModGL .G2 K) = pinnedX .G2 K g2v 1 :=
    fun x => hZ x x.2 (hcomm x x.2)
  have hv1 : pinnedX .G2 K g2v 1 ≠ 1 := by
    intro h
    rw [pinnedX_v_eq_g2N, ← g2N_zero] at h
    exact one_ne_zero (g2N_injective h).2.2.2.1
  let g : N → Bool := fun x => decide ((x : ModGL .G2 K) = 1)
  have hgv : ∀ w : N, (w : ModGL .G2 K) = 1 → g w = true := fun w hw => by
    change decide ((w : ModGL .G2 K) = 1) = true
    rw [hw]
    exact decide_eq_true rfl
  have hgv' : ∀ w : N, (w : ModGL .G2 K) = pinnedX .G2 K g2v 1 → g w = false := fun w hw => by
    change decide ((w : ModGL .G2 K) = 1) = false
    rw [hw]
    exact decide_eq_false hv1
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    rcases hmem x with hx | hx <;> rcases hmem y with hy | hy
    · rw [hx, hy]
    · rw [hgv x hx, hgv' y hy] at hxy
      exact absurd hxy Bool.noConfusion
    · rw [hgv' x hx, hgv y hy] at hxy
      exact absurd hxy Bool.noConfusion
    · rw [hx, hy]
  calc Nat.card N ≤ Nat.card Bool := Nat.card_le_card_of_injective g hg
    _ ≤ 2 ^ 5 := by simp

theorem a5At_G2 [Finite K] {s : adjointGroup .G2 K} (hs : orderOf s = 2) : A5At s := by
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) s hs with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine A5At.of_mulEquiv (MulAut.conj c) ?_
    rw [MulAut.conj_apply, hc]
    exact a5At_of_rel relA5At_G2_long
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine A5At.of_mulEquiv (MulAut.conj c) ?_
    rw [MulAut.conj_apply, hc]
    exact a5At_of_rel relA5At_G2_short

theorem a5At_of_lieModel_G2 {Y : Type} [Group Y] {f : ℕ} (h : LieModel Y .G2 0 2 f) {y : Y}
    (hy : orderOf y = 2) : A5At y := by
  have hce : ChevalleyExceptionalModel Y .G2 2 f := by
    rcases h with ⟨hcl, -⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hsz (by decide)
  obtain ⟨⟨-, hf, -⟩, hU⟩ := hce
  obtain ⟨K', _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hU
  have : CharP K' 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  exact A5At.of_mulEquiv e (a5At_G2 (by rw [MulEquiv.orderOf_eq, hy]))

end CFSG.LargeExtraspecial.S8
