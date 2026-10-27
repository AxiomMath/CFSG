module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Core

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutatorElement_mul_of_commute {z n z' n' : G} (h1 : Commute z n) (h2 : Commute z n')
    (h3 : Commute z z') (h4 : Commute z' n) (h5 : Commute z' n') :
    ⁅z * n, z' * n'⁆ = ⁅n, n'⁆ := by
  have hY : Commute z (n * z' * n' * n⁻¹) :=
    ((h1.mul_right h3).mul_right h2).mul_right h1.inv_right
  have hZ : Commute z' (n * n' * n⁻¹ * n'⁻¹) :=
    ((h4.mul_right h5).mul_right h4.inv_right).mul_right h5.inv_right
  rw [commutatorElement_def, commutatorElement_def]
  calc z * n * (z' * n') * (z * n)⁻¹ * (z' * n')⁻¹ =
      z * (n * z' * n' * n⁻¹) * z⁻¹ * n'⁻¹ * z'⁻¹ := by group
    _ = n * z' * n' * n⁻¹ * n'⁻¹ * z'⁻¹ := by rw [hY.eq, mul_inv_cancel_right]
    _ = z' * (n * n' * n⁻¹ * n'⁻¹) * z'⁻¹ := by rw [← h4.eq]; group
    _ = n * n' * n⁻¹ * n'⁻¹ := by rw [hZ.eq, mul_inv_cancel_right]

end Group

section C

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem g2N_v_split'
    (D E F : K) :
    g2N 0 0 0 D E F = pinnedX .G2 K g2v D * g2N 0 0 0 0 E F := by
  rw [pinnedX_v_eq_g2N, g2N_zero_mul_g2N_zero]
  exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)

theorem bcLevi_le_shortCent :
    g2BCGroup K ⊔ g2RankOne K g2ia ≤ g2ShortCent K :=
  sup_le (fun _ hw => g2ShortRadical_le_shortCent (g2BCGroup_le hw)) g2RankOne_le_shortCent

theorem commutator_shortCent_le :
    ⁅g2ShortCent K, g2ShortCent K⁆ ≤ g2BCGroup K ⊔ g2RankOne K g2ia := by
  obtain ⟨-, -, -, -, hset, -⟩ := even_G2_highest_short_root_centralizer K
  have hdec : ∀ s ∈ g2ShortCent K, ∃ D : K, ∃ n ∈ g2BCGroup K ⊔ g2RankOne K g2ia,
      s = pinnedX .G2 K g2v D * n := by
    intro s hs
    have hs' : s ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hs
    rw [hset] at hs'
    obtain ⟨q, ⟨D, E, F, rfl⟩, l, hl, rfl⟩ := hs'
    refine ⟨D, g2N 0 0 0 0 E F * l, mul_mem (mem_sup_left ⟨E, F, rfl⟩) (mem_sup_right hl), ?_⟩
    rw [← mul_assoc, ← g2N_v_split']
  have hz : ∀ s ∈ g2ShortCent K, ∀ x : K, Commute (pinnedX .G2 K g2v x) s :=
    fun s hs x => (g2_commute_v_of_mem hs x).symm
  rw [commutator_le]
  intro s hs t ht
  obtain ⟨D, n, hn, rfl⟩ := hdec s hs
  obtain ⟨D', n', hn', rfl⟩ := hdec t ht
  have hnS := bcLevi_le_shortCent hn
  have hn'S := bcLevi_le_shortCent hn'
  have hvv : Commute (pinnedX .G2 K g2v D) (pinnedX .G2 K g2v D') := by
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  rw [commutatorElement_mul_of_commute (hz n hnS D) (hz n' hn'S D) hvv (hz n hnS D')
    (hz n' hn'S D')]
  exact RankTwoL3Even.commutatorElement_mem' hn hn'

theorem commutator_shortCent_eq
    (hK4 : 4 ≤ Nat.card K) :
    ⁅g2ShortCent K, g2ShortCent K⁆ = g2BCGroup K ⊔ g2RankOne K g2ia :=
  le_antisymm commutator_shortCent_le
    (sup_le g2BCGroup_le_commutator (g2RankOne_le_commutator hK4))

omit [Finite K] in
theorem g2BCGroup_le_commutator_of
    {H : Subgroup (ModGL .G2 K)}
    (hLa : g2RankOne K g2ia ≤ H) (hBC : g2BCGroup K ≤ H) : g2BCGroup K ≤ ⁅H, H⁆ := by
  have hXa : pinnedX .G2 K g2a 1 ∈ H := by
    refine hLa ?_
    rw [g2RankOne_a_eq]
    exact subset_closure (Or.inl ⟨1, rfl⟩)
  have hXna : pinnedX .G2 K g2na 1 ∈ H := by
    refine hLa ?_
    rw [g2RankOne_a_eq]
    exact subset_closure (Or.inr ⟨1, rfl⟩)
  have hA : ∀ y z : K, g2N 0 0 0 0 y z ∈ H := fun y z => hBC ⟨y, z, rfl⟩
  have hc : ∀ y : K, g2N 0 0 0 0 0 y ∈ ⁅H, H⁆ := by
    intro y
    have h1 := commutator_mem_commutator hXa (hA y 0)
    have e : ⁅pinnedX .G2 K g2a 1, g2N 0 0 0 0 y 0⁆ = g2N 0 0 0 0 0 y := by
      rw [commutatorElement_def]
      obtain ⟨-, -, h⟩ := actsOnShort_pinnedX_a (K := K) 1
      have h2 := h ![y, 0]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [h2, g2N_zero_inv, g2N_zero_mul_g2N_zero]
      refine g2N_eq_g2N rfl (by ring) (by ring) (by ring) ?_ ?_
      · simp [shMa, CharTwo.add_self_eq_zero]
      · simp [shMa, CharTwo.add_self_eq_zero]
    rw [e] at h1
    exact h1
  have hb : ∀ z : K, g2N 0 0 0 0 z 0 ∈ ⁅H, H⁆ := by
    intro z
    have h1 := commutator_mem_commutator hXna (hA 0 z)
    have e : ⁅pinnedX .G2 K g2na 1, g2N 0 0 0 0 0 z⁆ = g2N 0 0 0 0 z 0 := by
      rw [commutatorElement_def]
      obtain ⟨-, -, h⟩ := actsOnShort_pinnedX_na (K := K) 1
      have h2 := h ![0, z]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [h2, g2N_zero_inv, g2N_zero_mul_g2N_zero]
      refine g2N_eq_g2N rfl (by ring) (by ring) (by ring) ?_ ?_
      · simp [shMa, shSwap]
      · simp [shMa, shSwap, CharTwo.add_self_eq_zero]
    rw [e] at h1
    exact h1
  rintro _ ⟨y, z, rfl⟩
  have e : g2N 0 0 0 0 y z = g2N 0 0 0 0 y 0 * g2N 0 0 0 0 0 z := by
    rw [g2N_zero_mul_g2N_zero]
    exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)
  rw [e]
  exact mul_mem (hb y) (hc z)

theorem commutator_shortCent_perfect
    (hK4 : 4 ≤ Nat.card K) :
    ⁅⁅g2ShortCent K, g2ShortCent K⁆, ⁅g2ShortCent K, g2ShortCent K⁆⁆ =
      ⁅g2ShortCent K, g2ShortCent K⁆ := by
  rw [commutator_shortCent_eq hK4]
  refine le_antisymm ((commutator_le).2 fun a ha b hb =>
    RankTwoL3Even.commutatorElement_mem' ha hb) (sup_le ?_ ?_)
  · exact g2BCGroup_le_commutator_of le_sup_right le_sup_left
  · calc g2RankOne K g2ia = ⁅g2RankOne K g2ia, g2RankOne K g2ia⁆ :=
          (g2RankOne_commutator hK4).symm
      _ ≤ _ := commutator_mono le_sup_right le_sup_right

end C

section Inv

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem conj_na_one_g2N
    (C D F : K) :
    pinnedX .G2 K g2na 1 * g2N 0 0 C D 0 F * (pinnedX .G2 K g2na 1)⁻¹ =
      g2N C 0 C (D + C ^ 2) (C ^ 3 + F) F := by
  rw [pinnedX_na_eq,
    show weylElt .G2 K g2ia 1 * pinnedX .G2 K g2a 1 * (weylElt .G2 K g2ia 1)⁻¹ * g2N 0 0 C D 0 F *
        (weylElt .G2 K g2ia 1 * pinnedX .G2 K g2a 1 * (weylElt .G2 K g2ia 1)⁻¹)⁻¹ =
      weylElt .G2 K g2ia 1 * (pinnedX .G2 K g2a 1 * ((weylElt .G2 K g2ia 1)⁻¹ * g2N 0 0 C D 0 F *
        weylElt .G2 K g2ia 1) * (pinnedX .G2 K g2a 1)⁻¹) * (weylElt .G2 K g2ia 1)⁻¹ by group,
    show (weylElt .G2 K g2ia 1)⁻¹ * g2N 0 0 C D 0 F * weylElt .G2 K g2ia 1 =
      weylElt .G2 K g2ia 1 * g2N 0 0 C D 0 F * (weylElt .G2 K g2ia 1)⁻¹ by
        rw [UnbalancedCatalog.weylElt_inv],
    weylElt_a_conj_g2N, pinnedX_inv_eq, conj_a, weylElt_a_conj_g2N]
  exact g2N_eq_g2N (by ring) rfl (by ring) (by ring) (by ring) (by char2_ring)

theorem radAction_eq_of_commute
    {q l : ModGL .G2 K} (hq : q ∈ g2LongRadical K)
    (hl : l ∈ g2RankOne K g2ir) (v : Fin 4 → K)
    (hcomm : q * l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 =
      g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * (q * l)) :
    radAction ⟨l, hl⟩ v = v := by
  obtain ⟨-, -, -, -, -, hLN, -, -, -, ⟨π, -, -, hπ⟩, -, -⟩ :=
    even_G2_highest_long_root_centralizer K
  obtain ⟨F', hF'⟩ := (radAction_spec ⟨l, hl⟩).2 v 0
  have hy := g2N_mem_g2LongRadical (v 0) (v 1) (v 2) (v 3) (0 : K)
  have hy' : l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹ ∈ g2LongRadical K :=
    (mem_normalizer_iff.1 (hLN hl) _).1 hy
  have h2 : q * (l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹) * q⁻¹ =
      g2N 0 (v 0) (v 1) (v 2) (v 3) 0 := by
    calc q * (l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹) * q⁻¹ =
        q * l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * (q * l)⁻¹ := by group
      _ = g2N 0 (v 0) (v 1) (v 2) (v 3) 0 := by rw [hcomm, mul_inv_cancel_right]
  have h3 : π ⟨q * (l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹) * q⁻¹,
      mul_mem (mul_mem hq hy') (inv_mem hq)⟩ =
        π ⟨l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹, hy'⟩ := by
    have e : (⟨q * (l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹) * q⁻¹,
        mul_mem (mul_mem hq hy') (inv_mem hq)⟩ : g2LongRadical K) =
          ⟨q, hq⟩ * ⟨_, hy'⟩ * (⟨q, hq⟩ : g2LongRadical K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm (π ⟨q, hq⟩), mul_assoc, mul_inv_cancel, mul_one]
  have e1 : (⟨q * (l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹) * q⁻¹,
      mul_mem (mul_mem hq hy') (inv_mem hq)⟩ : g2LongRadical K) = ⟨_, hy⟩ := Subtype.ext h2
  have e2 : (⟨l * g2N 0 (v 0) (v 1) (v 2) (v 3) 0 * l⁻¹, hy'⟩ : g2LongRadical K) =
      ⟨_, g2N_mem_g2LongRadical _ _ _ _ F'⟩ := Subtype.ext hF'
  rw [e1, e2, hπ, hπ] at h3
  have h4 := congrArg Multiplicative.toAdd h3
  simp only [toAdd_ofAdd] at h4
  funext i
  fin_cases i
  · exact (congrFun h4 0).symm
  · exact (congrFun h4 1).symm
  · exact (congrFun h4 2).symm
  · exact (congrFun h4 3).symm

theorem mem_rootSubgroup_v_of_centralizes
    {x : ModGL .G2 K}
    (hxC : x ∈ adjointGroup .G2 K)
    (hx : ∀ y ∈ g2BCGroup K ⊔ g2RankOne K g2ia, x * y = y * x) (hx2 : x ^ 2 = 1) :
    x ∈ rootSubgroup .G2 K g2v := by
  obtain ⟨-, -, -, -, hset, hLN, hQL, -⟩ := even_G2_highest_long_root_centralizer K
  have hXa : pinnedX .G2 K g2a 1 ∈ g2BCGroup K ⊔ g2RankOne K g2ia := by
    refine mem_sup_right ?_
    rw [g2RankOne_a_eq]
    exact subset_closure (Or.inl ⟨1, rfl⟩)
  have hXna : pinnedX .G2 K g2na 1 ∈ g2BCGroup K ⊔ g2RankOne K g2ia := by
    refine mem_sup_right ?_
    rw [g2RankOne_a_eq]
    exact subset_closure (Or.inr ⟨1, rfl⟩)
  have hXb : pinnedX .G2 K g2b 1 ∈ g2BCGroup K ⊔ g2RankOne K g2ia :=
    mem_sup_left ⟨1, 0, by rw [pinnedX_b_eq_g2N]⟩
  have hXc : pinnedX .G2 K g2c 1 ∈ g2BCGroup K ⊔ g2RankOne K g2ia :=
    mem_sup_left ⟨0, 1, by rw [pinnedX_c_eq_g2N]⟩
  have hxL : x ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) :=
    mem_inf.2 ⟨hxC, mem_centralizer_singleton_iff.2 (hx _ hXc)⟩
  rw [hset] at hxL
  obtain ⟨q, hq, l, hl, hql⟩ := hxL
  beta_reduce at hql
  subst hql
  have hlq : l * q * l⁻¹ ∈ g2LongRadical K := (mem_normalizer_iff.1 (hLN hl) q).1 hq
  have hl2 : l * l = 1 := by
    have h1 : q * (l * q * l⁻¹) * (l * l) = 1 := by
      rw [← hx2, sq]
      group
    have h3 : l * l ∈ g2LongRadical K ⊓ g2RankOne K g2ir := by
      refine mem_inf.2 ⟨?_, mul_mem hl hl⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (mul_mem hq hlq)
    rwa [hQL, mem_bot] at h3
  have hT := radAction_spec ⟨l, hl⟩
  have hfa : radAction ⟨l, hl⟩ ![1, 0, 0, 0] = ![1, 0, 0, 0] := by
    refine radAction_eq_of_commute hq hl _ ?_
    have h := hx _ hXa
    rwa [pinnedX_a_eq_g2N] at h
  have hfb : radAction ⟨l, hl⟩ ![0, 0, 0, 1] = ![0, 0, 0, 1] := by
    refine radAction_eq_of_commute hq hl _ ?_
    have h := hx _ hXb
    rwa [pinnedX_b_eq_g2N] at h
  have hl1 : l = 1 := by
    obtain ⟨ρ, -, -, -, -, hrange, -, hcell0, hcell⟩ := g2_rank_one (K := K) g2ir
    have hl' := hl
    rw [← hrange] at hl'
    obtain ⟨g, hg⟩ := hl'
    by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · obtain ⟨t, b, e⟩ : ∃ (t : Kˣ) (b : K),
          ρ g = torusElt .G2 K g2ir t * pinnedX .G2 K g2r b :=
        ⟨_, _, by rw [hcell0 g hc, xUnit_g2ir]⟩
      have hact : ActsOnRadical l (radDiag t ∘ₗ radMr b) := by
        rw [← hg, e]
        exact (actsOnRadical_torusElt_r t).mul (actsOnRadical_pinnedX_r b)
      have he := hact.unique hT
      have h0 := congrArg (fun T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T' ![1, 0, 0, 0] 0) he
      have h1 := congrArg (fun T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T' ![1, 0, 0, 0] 1) he
      simp only [hfa] at h0 h1
      simp [radDiag, radMr] at h0 h1
      have hb0 : b = 0 := h1
      have ht3 : t ^ 3 = 1 := Units.ext (by simpa using h0)
      have hl'' : l = LieType.Chevalley.torusEltHom .G2 K g2ir t := by
        rw [← hg, e, hb0, pinnedX_zero, mul_one]
        rfl
      have ht2 : t * t = 1 := by
        have h4 : LieType.Chevalley.torusEltHom .G2 K g2ir (t * t) = 1 := by
          rw [map_mul, ← hl'', hl2]
        have h5 := torus_r_v (K := K) (t * t) 1
        have h6 : torusElt .G2 K g2ir (t * t) = 1 := h4
        rw [h6, one_mul, inv_one, mul_one, mul_one] at h5
        exact Units.ext ((pinnedX_injective .G2 K g2v h5).symm)
      have ht1 : t = 1 := by
        calc t = t ^ 3 * (t * t)⁻¹ := by group
          _ = 1 := by rw [ht3, ht2, inv_one, mul_one]
      rw [hl'', ht1, map_one]
    · exfalso
      obtain ⟨c₁, t, c₂, e⟩ : ∃ (c₁ : K) (t : Kˣ) (c₂ : K), ρ g = pinnedX .G2 K g2r c₁ *
          torusElt .G2 K g2ir t * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2r c₂ :=
        ⟨_, _, _, by rw [hcell g hc, xUnit_g2ir, xUnit_g2ir]⟩
      have hact : ActsOnRadical l
          (((radMr c₁ ∘ₗ radDiag t) ∘ₗ radSwap) ∘ₗ radMr c₂) := by
        rw [← hg, e]
        exact (((actsOnRadical_pinnedX_r _).mul (actsOnRadical_torusElt_r _)).mul
          actsOnRadical_weylElt_r).mul (actsOnRadical_pinnedX_r _)
      have he := hact.unique hT
      have h0 := congrArg (fun T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T' ![0, 0, 0, 1] 0) he
      simp only [hfb] at h0
      simp [radDiag, radMr, radSwap] at h0
  subst hl1
  rw [mul_one] at hx ⊢
  obtain ⟨B, C, D, E, F, rfl⟩ := hq
  have hinvol : ∀ y : ModGL .G2 K, y * y = 1 → g2N 0 B C D E F * y = y * g2N 0 B C D E F →
      y * g2N 0 B C D E F * y = g2N 0 B C D E F := by
    intro y hyy hcomm
    rw [← hcomm, mul_assoc, hyy, mul_one]
  have hE : E = 0 := by
    have h := hinvol _ (pinnedX_mul_self g2a 1) (hx _ hXa)
    rw [conj_a] at h
    obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective h
    simpa using h6
  subst hE
  have hB : B = 0 := by
    have h := hinvol _ (pinnedX_mul_self g2b 1) (hx _ hXb)
    rw [conj_b] at h
    obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective h
    simpa using h6
  subst hB
  have h : pinnedX .G2 K g2na 1 * g2N 0 0 C D 0 F * (pinnedX .G2 K g2na 1)⁻¹ =
      g2N 0 0 C D 0 F := by
    rw [pinnedX_inv_eq]
    exact hinvol _ (pinnedX_mul_self g2na 1) (hx _ hXna)
  rw [conj_na_one_g2N] at h
  obtain ⟨h1, -, -, -, h5, -⟩ := g2N_injective h
  subst h1
  have hF : F = 0 := by simpa using h5
  subst hF
  exact mem_rootSubgroup.2 ⟨D, pinnedX_v_eq_g2N D⟩

theorem g2Centr184s
    : G2Centr184s := by
  intro K _ _ _ hK4
  refine ⟨commutator_shortCent_perfect hK4, fun y hy => ?_, fun x hx hx2 => ?_⟩
  · obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hy
    refine mem_inf.2 ⟨pinnedX_mem_adjointGroup g2v s, mem_centralizer_iff.2 fun z hz => ?_⟩
    exact g2_commute_v_of_mem
      (commutator_le.2 (fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hz) s
  · obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
    rw [commutator_shortCent_eq hK4] at hxc
    exact mem_rootSubgroup_v_of_centralizes hxC
      (fun y hy => (mem_centralizer_iff.1 hxc y hy).symm) hx2

end Inv

section Long

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2RankOne_r_commutator
    (hK4 : 4 ≤ Nat.card K) :
    ⁅g2RankOne K g2ir, g2RankOne K g2ir⁆ = g2RankOne K g2ir := by
  obtain ⟨-, -, -, -, -, -, -, ⟨ρ, -, -, hrange, hinj⟩, -⟩ :=
    even_G2_highest_long_root_centralizer K
  have := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hK4
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 2) le_rfl (Or.inr h4)
  let e₁ := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)
  let e₂ : LieType.Chevalley.SL2 K ≃* ↥(g2RankOne K g2ir) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let e := e₁.trans e₂
  have := hperf
  have : Group.IsPerfect ↥(g2RankOne K g2ir) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.commutator_eq_self

theorem g2LongCent_eq_sup
    : g2LongCent K = g2LongRadical K ⊔ g2RankOne K g2ir :=
  (even_G2_highest_long_root_centralizer K).2.2.2.1

omit [Finite K] in
theorem comm_torus_r_u
    (t : Kˣ) (x : K) :
    ⁅torusElt .G2 K g2ir t, pinnedX .G2 K g2u x⁆ = pinnedX .G2 K g2u (((t : K)⁻¹ + 1) * x) := by
  rw [commutatorElement_def, root_torus_conjugation g2ir isRoot_g2u t x, pinnedX_inv_eq,
    ← pinnedX_add]
  have h : ∑ j, Tag.G2.cartan g2ir j * g2u j = -1 := by decide
  rw [h, zpow_neg, zpow_one, Units.val_inv_eq_inv_val]
  congr 1
  ring

omit [Finite K] in
theorem comm_torus_r_v
    (t : Kˣ) (x : K) :
    ⁅torusElt .G2 K g2ir t, pinnedX .G2 K g2v x⁆ = pinnedX .G2 K g2v (((t : K) + 1) * x) := by
  rw [commutatorElement_def, torus_r_v, pinnedX_inv_eq, ← pinnedX_add]
  congr 1
  ring

theorem g2LongCent_commutator
    (hK4 : 4 ≤ Nat.card K) :
    ⁅g2LongCent K, g2LongCent K⁆ = g2LongCent K := by
  classical
  have hLC := g2LongCent_eq_sup (K := K)
  have hQ : g2LongRadical K ≤ g2LongCent K := hLC ▸ le_sup_left
  have hL : g2RankOne K g2ir ≤ g2LongCent K := hLC ▸ le_sup_right
  have ha : ∀ s : K, pinnedX .G2 K g2a s ∈ g2LongCent K := fun s => by
    rw [pinnedX_a_eq_g2N]
    exact hQ (g2N_mem_g2LongRadical _ _ _ _ _)
  have hu : ∀ s : K, pinnedX .G2 K g2u s ∈ g2LongCent K := fun s => by
    rw [pinnedX_u_eq_g2N]
    exact hQ (g2N_mem_g2LongRadical _ _ _ _ _)
  have hv : ∀ s : K, pinnedX .G2 K g2v s ∈ g2LongCent K := fun s => by
    rw [pinnedX_v_eq_g2N]
    exact hQ (g2N_mem_g2LongRadical _ _ _ _ _)
  have hb : ∀ s : K, pinnedX .G2 K g2b s ∈ g2LongCent K := fun s => by
    rw [pinnedX_b_eq_g2N]
    exact hQ (g2N_mem_g2LongRadical _ _ _ _ _)
  have hr : ∀ s : K, pinnedX .G2 K g2r s ∈ g2LongCent K := fun s => hL (by
    rw [g2RankOne_r_eq]
    exact subset_closure (Or.inl ⟨s, rfl⟩))
  have hnr : ∀ s : K, pinnedX .G2 K g2nr s ∈ g2LongCent K := fun s => hL (by
    rw [g2RankOne_r_eq]
    exact subset_closure (Or.inr ⟨s, rfl⟩))
  have hNc : ∀ y : K, pinnedX .G2 K g2c y ∈ ⁅g2LongCent K, g2LongCent K⁆ := fun y => by
    have h := commutator_mem_commutator (ha 1) (hb y)
    rwa [comm_a_b, one_mul] at h
  have hNb : ∀ y : K, pinnedX .G2 K g2b y ∈ ⁅g2LongCent K, g2LongCent K⁆ := fun y => by
    have h := commutator_mem_commutator (hr 1) (hv y)
    rwa [comm_r_v, one_mul] at h
  have hNa : ∀ y : K, pinnedX .G2 K g2a y ∈ ⁅g2LongCent K, g2LongCent K⁆ := fun y => by
    have h := commutator_mem_commutator (hv y) (hnr 1)
    simp only [comm_v_nr, one_pow, mul_one] at h
    have h' := mul_mem h (inv_mem (hNc (y ^ 2)))
    rwa [mul_inv_cancel_right] at h'
  obtain ⟨s, hs0, hs1⟩ : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
    by_contra hne
    have hne' : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h1 => hne ⟨x, hx, h1⟩
    have hs : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hne' x hx]⟩
    have h2 := Nat.card_le_card_of_surjective _ hs
    rw [show Nat.card Bool = 2 by simp] at h2
    omega
  have hwu : s⁻¹ + 1 ≠ 0 := fun h => hs1 (by
    have h' := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq, inv_eq_one] at h')
  have hwv : s + 1 ≠ 0 := fun h => hs1 (by rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq])
  have hNu : ∀ y : K, pinnedX .G2 K g2u y ∈ ⁅g2LongCent K, g2LongCent K⁆ := fun y => by
    have h := commutator_mem_commutator (hL (torusElt_mem_g2RankOne g2ir (Units.mk0 s hs0)))
      (hu ((s⁻¹ + 1)⁻¹ * y))
    rwa [comm_torus_r_u, Units.val_mk0, mul_inv_cancel_left₀ hwu] at h
  have hNv : ∀ y : K, pinnedX .G2 K g2v y ∈ ⁅g2LongCent K, g2LongCent K⁆ := fun y => by
    have h := commutator_mem_commutator (hL (torusElt_mem_g2RankOne g2ir (Units.mk0 s hs0)))
      (hv ((s + 1)⁻¹ * y))
    rwa [comm_torus_r_v, Units.val_mk0, mul_inv_cancel_left₀ hwv] at h
  have hQN : g2LongRadical K ≤ ⁅g2LongCent K, g2LongCent K⁆ := by
    rintro _ ⟨B, C, D, E, F, rfl⟩
    have e : g2N 0 B C D E F = pinnedX .G2 K g2a B * pinnedX .G2 K g2u C *
        pinnedX .G2 K g2v D * pinnedX .G2 K g2b E * pinnedX .G2 K g2c F := by
      simp only [g2N, pinnedX_zero, one_mul]
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hNa B) (hNu C)) (hNv D)) (hNb E)) (hNc F)
  have hLN : g2RankOne K g2ir ≤ ⁅g2LongCent K, g2LongCent K⁆ := calc
    g2RankOne K g2ir = ⁅g2RankOne K g2ir, g2RankOne K g2ir⁆ := (g2RankOne_r_commutator hK4).symm
    _ ≤ _ := commutator_mono hL hL
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  calc g2LongCent K = g2LongRadical K ⊔ g2RankOne K g2ir := hLC
    _ ≤ _ := sup_le hQN hLN

theorem g2Centralizer_g2LongCent :
    g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) = rootSubgroup .G2 K g2c := by
  obtain ⟨-, -, -, -, hset, -, -, -, hXc, -, -, hLc⟩ :=
    even_G2_highest_long_root_centralizer K
  have hQ : g2LongRadical K ≤ g2LongCent K := g2LongCent_eq_sup (K := K) ▸ le_sup_left
  refine le_antisymm (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
    have hx' : ∀ z ∈ g2LongCent K, x * z = z * x := fun z hz =>
      (mem_centralizer_iff.1 hxc z hz).symm
    have hmem : ∀ (B C D E F : K), g2N 0 B C D E F ∈ g2LongCent K := fun B C D E F =>
      hQ (g2N_mem_g2LongRadical B C D E F)
    have hxL : x ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := by
      refine mem_inf.2 ⟨hxC, mem_centralizer_singleton_iff.2 (hx' _ ?_)⟩
      rw [pinnedX_c_eq_g2N]
      exact hmem 0 0 0 0 1
    rw [hset] at hxL
    obtain ⟨q, hq, l, hl, hql⟩ := hxL
    beta_reduce at hql
    subst hql
    have hid : radActionHom ⟨l, hl⟩ = 1 := by
      refine Units.ext (LinearMap.ext fun v => ?_)
      rw [coe_radActionHom, Units.val_one, Module.End.one_apply]
      exact radAction_eq_of_commute hq hl v (hx' _ (hmem _ _ _ _ _))
    have hl1 : l = 1 := by
      have h := congrArg Subtype.val (radActionHom_injective (hid.trans (map_one _).symm))
      simpa using h
    subst hl1
    simp only [mul_one] at hx' ⊢
    obtain ⟨B, C, D, E, F, rfl⟩ := hq
    have hcomm : ∀ y : ModGL .G2 K, y ∈ g2LongCent K → y * y = 1 →
        y * g2N 0 B C D E F * y = g2N 0 B C D E F := fun y hy hyy => by
      rw [mul_assoc, hx' y hy, ← mul_assoc, hyy, one_mul]
    have hE := hcomm _ (by rw [pinnedX_a_eq_g2N]; exact hmem _ _ _ _ _)
      (pinnedX_mul_self g2a 1)
    rw [conj_a] at hE
    have hB := hcomm _ (by rw [pinnedX_b_eq_g2N]; exact hmem _ _ _ _ _)
      (pinnedX_mul_self g2b 1)
    rw [conj_b] at hB
    have hD := hcomm _ (by rw [pinnedX_u_eq_g2N]; exact hmem _ _ _ _ _)
      (pinnedX_mul_self g2u 1)
    rw [conj_u] at hD
    have hC := hcomm _ (by rw [pinnedX_v_eq_g2N]; exact hmem _ _ _ _ _)
      (pinnedX_mul_self g2v 1)
    rw [conj_v] at hC
    obtain ⟨-, -, -, -, -, hE'⟩ := g2N_injective hE
    obtain ⟨-, -, -, -, -, hB'⟩ := g2N_injective hB
    obtain ⟨-, -, -, -, -, hD'⟩ := g2N_injective hD
    obtain ⟨-, -, -, -, -, hC'⟩ := g2N_injective hC
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero,
      mul_one, add_eq_left] at hE' hB' hD' hC'
    subst hE' hB' hD' hC'
    exact mem_rootSubgroup.2 ⟨F, pinnedX_c_eq_g2N F⟩
  · obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hy
    refine mem_inf.2 ⟨pinnedX_mem_adjointGroup g2c s, mem_centralizer_iff.2 fun z hz => ?_⟩
    have hz' : z ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hz
    rw [hset] at hz'
    obtain ⟨q, hq, l, hl, hql⟩ := hz'
    beta_reduce at hql
    subst hql
    exact (((hXc s).2 q hq).symm.mul_left (hLc l hl s)).eq

theorem g2Centr184
    : G2Centr184 := fun _ _ _ _ hK4 =>
  ⟨g2LongCent_commutator hK4, g2Centralizer_g2LongCent⟩

end Long

end CFSG.ComponentClassification.RankTwoExceptional
