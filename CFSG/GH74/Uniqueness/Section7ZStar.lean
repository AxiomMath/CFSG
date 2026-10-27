module

public import CFSG.GH74.Uniqueness.Section6Basic
public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.isZStarIn_centralizer_sup_aux
    (S : ZDSetup X Z M) {z : X} (hz : z ∈ Z)
    (hzM : z ∈ M) {W : Subgroup X} (hWne : W ≠ ⊥) (hWM : W ≤ M)
    (hWz : z ∈ normalizer (W : Set X)) {K : Set X} (hKz : ∀ k ∈ K, z * k * z⁻¹ = k⁻¹)
    (hKinv : ∀ k ∈ K, k⁻¹ ∈ K) (hcl : Subgroup.closure K = W) (hWodd : Odd (Nat.card W))
    (hCM : ¬ centralizer K ≤ M) : IsZStarIn (centralizer K ⊔ zpowers z) z := by
  have hZ := S.invariant
  have h := S.prodDisc
  have hz2 : orderOf z = 2 := hZ.1 z hz
  have hzz : z * z = 1 := hZ.mul_self_eq_one hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hKW : K ⊆ (W : Set X) := by
    rw [← hcl]
    exact Subgroup.subset_closure
  have hzC : ∀ c ∈ centralizer K, z * c * z⁻¹ ∈ centralizer K := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have e : z⁻¹ * k * z = k⁻¹ := by
      have := hKz k hk
      rw [hzi] at this ⊢
      exact this
    have hk' : z⁻¹ * k * z ∈ K := by
      rw [e]
      exact hKinv k hk
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hk'
    calc k * (z * c * z⁻¹) = z * ((z⁻¹ * k * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * k * z)) * z⁻¹ := by rw [hcomm]
      _ = (z * c * z⁻¹) * k := by group
  have hzN : z ∈ normalizer ((centralizer K : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hzC x, fun hx => ?_⟩
    have h1 := hzC _ hx
    have e : z * (z * x * z⁻¹) * z⁻¹ = x := by
      rw [hzi]
      calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz]; group
    rwa [e] at h1
  have hzHs : z ∈ centralizer K ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hCHs : centralizer K ≤ centralizer K ⊔ zpowers z := le_sup_left
  have hHsN : centralizer K ⊔ zpowers z ≤ normalizer ((centralizer K : Subgroup X) : Set X) :=
    sup_le Subgroup.le_normalizer (by rw [Subgroup.zpowers_le]; exact hzN)
  have hsup : ((centralizer K ⊔ zpowers z : Subgroup X) : Set X) =
      ((centralizer K : Subgroup X) : Set X) * (zpowers z : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (centralizer K) (zpowers z)
      (by rw [Subgroup.zpowers_le]; exact hzN)
  have hconj : ∀ g ∈ centralizer K ⊔ zpowers z, ∃ c ∈ centralizer K,
      g * z * g⁻¹ = c * z * c⁻¹ := by
    intro g hg
    have hg' : g ∈ ((centralizer K : Subgroup X) : Set X) * (zpowers z : Set X) := by
      rw [← hsup]
      exact hg
    obtain ⟨c, hc, w, hw, rfl⟩ := Set.mem_mul.mp hg'
    refine ⟨c, hc, ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : z ^ n * z = z * z ^ n := (Commute.zpow_left (Commute.refl z) n).eq
    calc c * z ^ n * z * (c * z ^ n)⁻¹ = c * (z ^ n * z * (z ^ n)⁻¹) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [hcomm]; group
  have hznC : z ∉ centralizer K := by
    intro hzC'
    apply hWne
    rw [← hcl, Subgroup.closure_eq_bot_iff]
    intro k hk
    have hcomm : k * z = z * k := Subgroup.mem_centralizer_iff.mp hzC' k hk
    have e1 : z * k * z⁻¹ = k := by rw [← hcomm]; group
    have e2 := hKz k hk
    rw [e1] at e2
    have hk2 : k ^ 2 = 1 := by
      calc k ^ 2 = k * k⁻¹ := by rw [sq]; nth_rewrite 2 [e2]; rfl
        _ = 1 := mul_inv_cancel k
    have hkodd : Odd (orderOf k) := Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W (hKW hk))
    have hkdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hk2
    rcases (Nat.dvd_prime Nat.prime_two).mp hkdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · rw [h2] at hkodd
      exact absurd hkodd (by decide)
  have hCW : centralizer K ≤ normalizer (W : Set X) := by
    intro c hc
    have h1 := Subgroup.centralizer_closure K
    rw [hcl] at h1
    exact Subgroup.centralizer_le_normalizer _ (h1 ▸ hc)
  have hHsW : centralizer K ⊔ zpowers z ≤ normalizer (W : Set X) :=
    sup_le hCW (by rw [Subgroup.zpowers_le]; exact hWz)
  obtain ⟨hsimple, hSZ, -, -⟩ := S.theorem1_unconditional
  have hHsM : ¬ (centralizer K ⊔ zpowers z ≤ M) := fun hle => hCM (hCHs.trans hle)
  have hHstop : centralizer K ⊔ zpowers z ≠ ⊤ := by
    intro htop
    have hnorm : normalizer (W : Set X) = ⊤ := top_unique (htop ▸ hHsW)
    have : W.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hb | ht
    · exact hWne hb
    · exact h.1 (top_unique (ht ▸ hWM))
  have hne : (Z ∩ (((centralizer K ⊔ zpowers z) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨z, hz, Subgroup.mem_inf.mpr ⟨hzHs, hzM⟩⟩
  have hSE := hSZ.2.2.2.2 _ hHstop hne hHsM
  have hzH0 : z ∈ zHull Z (centralizer K ⊔ zpowers z) :=
    Subgroup.subset_closure ⟨hz, hzHs⟩
  have hH0Hs : zHull Z (centralizer K ⊔ zpowers z) ≤ centralizer K ⊔ zpowers z :=
    (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hinvconj : ∀ y ∈ zHull Z (centralizer K ⊔ zpowers z), orderOf y = 2 →
      ∃ g ∈ zHull Z (centralizer K ⊔ zpowers z), g⁻¹ * z * g = y := by
    intro y hy hy2
    have hz2' : orderOf (⟨z, hzH0⟩ : zHull Z (centralizer K ⊔ zpowers z)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hz2
    have hy2' : orderOf (⟨y, hy⟩ : zHull Z (centralizer K ⊔ zpowers z)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hy2
    obtain ⟨g, hg⟩ := Simple.exists_conj_of_isStronglyEmbedded hSE hz2' hy2'
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  have hNodd : Odd (Nat.card ↥(zHull Z (centralizer K ⊔ zpowers z) ⊓ centralizer K)) := by
    by_contra hnot
    have h2 : 2 ∣ Nat.card ↥(zHull Z (centralizer K ⊔ zpowers z) ⊓ centralizer K) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(zHull Z (centralizer K ⊔ zpowers z) ⊓ centralizer K)) 2 h2
    have hy2 : orderOf (y : X) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hy
    obtain ⟨g, hg, hgy⟩ := hinvconj y y.2.1 hy2
    have hgN : g⁻¹ ∈ normalizer ((centralizer K : Subgroup X) : Set X) :=
      (normalizer ((centralizer K : Subgroup X) : Set X)).inv_mem (hHsN (hH0Hs hg))
    have h1 : g⁻¹ * z * g⁻¹⁻¹ ∈ centralizer K := by
      rw [inv_inv, hgy]
      exact y.2.2
    exact hznC ((Subgroup.mem_normalizer_iff.mp hgN z).mpr h1)
  have hNHs : zHull Z (centralizer K ⊔ zpowers z) ⊓ centralizer K ≤
      centralizer K ⊔ zpowers z := inf_le_left.trans hH0Hs
  have hNnormal : ((zHull Z (centralizer K ⊔ zpowers z) ⊓ centralizer K).subgroupOf
      (centralizer K ⊔ zpowers z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNHs]
    intro g hg
    exact mem_normalizer_inf (le_normalizer_zHull hZ _ hg) (hHsN hg)
  refine ⟨hzHs, zHull Z (centralizer K ⊔ zpowers z) ⊓ centralizer K, hNHs, hNnormal, hNodd, ?_⟩
  intro g hg
  obtain ⟨c, hc, hgz⟩ := hconj g hg
  have hy : g * z * g⁻¹ ∈ Z := by
    have := hZ.2 z hz g⁻¹
    rwa [inv_inv] at this
  have hyHs : g * z * g⁻¹ ∈ centralizer K ⊔ zpowers z :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hzHs) (Subgroup.inv_mem _ hg)
  have hyH0 : g * z * g⁻¹ ∈ zHull Z (centralizer K ⊔ zpowers z) :=
    Subgroup.subset_closure ⟨hy, hyHs⟩
  refine ⟨Subgroup.mul_mem _ hyH0 (Subgroup.inv_mem _ hzH0), ?_⟩
  rw [hgz]
  have e : c * z * c⁻¹ * z⁻¹ = c * (z * c⁻¹ * z⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hc (hzC _ (Subgroup.inv_mem _ hc))

theorem ZDSetup.isZStarIn_centralizer_sup
    (S : ZDSetup X Z M) {z : X} {p : ℕ} {W : Subgroup X}
    (hW : T4Cand Z M z p W)
    (hCM : ¬ centralizer (CFSG.OddInversion.invertedSet W z : Set X) ≤ M) :
    IsZStarIn (centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊔ zpowers z) z :=
  S.isZStarIn_centralizer_sup_aux hW.mem_Z hW.mem_M hW.ne_bot hW.le_M hW.normalizes
    (fun _ hk => hk.2) (fun _ hk => CFSG.OddInversion.invertedSet_inv hk)
    (hW.closure_invertedSet S.invariant) hW.odd_card hCM

end CFSG.GH74.Uniqueness
