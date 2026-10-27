module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApi
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAp
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

private theorem cbg_inv_conj_mem {g : MulAut V} (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ y ∈ X, g⁻¹ * y * g ∈ X := by
  let φ : ↥X → ↥X := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h : g * (x : MulAut V) * g⁻¹ = g * (y : MulAut V) * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h)
  intro y hy
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hφ ⟨y, hy⟩
  have h : g * (x : MulAut V) * g⁻¹ = y := congrArg Subtype.val hx
  have h' : g⁻¹ * y * g = x := by rw [← h]; group
  rw [h']
  exact x.2

omit [Finite V] in
private theorem cbg_even_case {k : ℕ} (θ : ↥X ≃* alternatingGroup (Fin k)) {n : MulAut V}
    (hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X) {σ : Perm (Fin k)}
    (hσ : ∀ (y : MulAut V) (hy : y ∈ X),
      (θ ⟨n * y * n⁻¹, hn y hy⟩ : Perm (Fin k)) = σ * (θ ⟨y, hy⟩ : Perm (Fin k)) * σ⁻¹)
    (hev : σ ∈ alternatingGroup (Fin k)) :
    ∃ x ∈ X, ∃ q ∈ Subgroup.centralizer (X : Set (MulAut V)), n = x * q := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥X, θ x₀ = ⟨σ, hev⟩ := θ.surjective ⟨σ, hev⟩
  have hθx₀ : (θ x₀ : Perm (Fin k)) = σ := congrArg Subtype.val hx₀
  refine ⟨(x₀ : MulAut V), x₀.2, (x₀ : MulAut V)⁻¹ * n, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hu : x₀⁻¹ * (⟨n * y * n⁻¹, hn y hy⟩ : ↥X) * x₀ = ⟨y, hy⟩ := by
    apply θ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hθx₀, hσ y hy]
    group
  have h2 : (x₀ : MulAut V)⁻¹ * (n * y * n⁻¹) * (x₀ : MulAut V) = y := congrArg Subtype.val hu
  calc y * ((x₀ : MulAut V)⁻¹ * n)
      = ((x₀ : MulAut V)⁻¹ * (n * y * n⁻¹) * (x₀ : MulAut V)) * ((x₀ : MulAut V)⁻¹ * n) := by
        rw [h2]
    _ = (x₀ : MulAut V)⁻¹ * n * y := by group

namespace CbData

variable (D : CbData Y t m X)

include D in
theorem normalizer_decomp (hm : 7 ≤ m) {n : MulAut V} (hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X) :
    ∃ (x q : MulAut V) (e : ℕ), x ∈ X ∧ q ∈ Subgroup.centralizer (X : Set (MulAut V)) ∧ e < 2 ∧
      n = x * q * t ^ e := by
  obtain ⟨σ, hσ⟩ :=
    exists_perm_of_normalizes (by omega : 5 ≤ m + 2) (by omega : m + 2 ≠ 6) D.θ hn
  by_cases hev : σ ∈ alternatingGroup (Fin (m + 2))
  · obtain ⟨x, hx, q, hq, rfl⟩ := cbg_even_case D.θ hn hσ hev
    exact ⟨x, q, 0, hx, hq, by norm_num, by simp⟩
  · have hti : ∀ y ∈ X, t⁻¹ * y * t ∈ X := cbg_inv_conj_mem D.hn
    have hn' : ∀ x ∈ X, (n * t⁻¹) * x * (n * t⁻¹)⁻¹ ∈ X := by
      intro x hx
      have e : (n * t⁻¹) * x * (n * t⁻¹)⁻¹ = n * (t⁻¹ * x * t) * n⁻¹ := by group
      rw [e]
      exact hn _ (hti x hx)
    have hss : Equiv.swap D.a D.b * Equiv.swap D.a D.b = 1 := Equiv.swap_mul_self _ _
    have hsw : ∀ (y : MulAut V) (hy : y ∈ X),
        (D.θ ⟨t⁻¹ * y * t, hti y hy⟩ : Perm (Fin (m + 2))) =
          Equiv.swap D.a D.b * (D.θ ⟨y, hy⟩ : Perm (Fin (m + 2))) * Equiv.swap D.a D.b := by
      intro y hy
      have h1 := D.hconj (t⁻¹ * y * t) (hti y hy)
      have e : (⟨t * (t⁻¹ * y * t) * t⁻¹, D.hn _ (hti y hy)⟩ : ↥X) = ⟨y, hy⟩ :=
        Subtype.ext (by group)
      rw [e, Equiv.swap_inv] at h1
      rw [h1]
      have e2 : Equiv.swap D.a D.b * (Equiv.swap D.a D.b *
          (D.θ ⟨t⁻¹ * y * t, hti y hy⟩ : Perm (Fin (m + 2))) * Equiv.swap D.a D.b) *
            Equiv.swap D.a D.b =
          (Equiv.swap D.a D.b * Equiv.swap D.a D.b) *
            (D.θ ⟨t⁻¹ * y * t, hti y hy⟩ : Perm (Fin (m + 2))) *
              (Equiv.swap D.a D.b * Equiv.swap D.a D.b) := by group
      rw [e2, hss, one_mul, mul_one]
    have hσ' : ∀ (y : MulAut V) (hy : y ∈ X),
        (D.θ ⟨(n * t⁻¹) * y * (n * t⁻¹)⁻¹, hn' y hy⟩ : Perm (Fin (m + 2))) =
          (σ * Equiv.swap D.a D.b) * (D.θ ⟨y, hy⟩ : Perm (Fin (m + 2))) *
            (σ * Equiv.swap D.a D.b)⁻¹ := by
      intro y hy
      have e : (⟨(n * t⁻¹) * y * (n * t⁻¹)⁻¹, hn' y hy⟩ : ↥X) =
          ⟨n * (t⁻¹ * y * t) * n⁻¹, hn _ (hti y hy)⟩ := Subtype.ext (by group)
      rw [e, hσ (t⁻¹ * y * t) (hti y hy), hsw y hy, mul_inv_rev, Equiv.swap_inv]
      group
    have hev' : σ * Equiv.swap D.a D.b ∈ alternatingGroup (Fin (m + 2)) := by
      rw [Perm.mem_alternatingGroup] at hev ⊢
      rw [map_mul, Perm.sign_swap D.hab]
      rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
      · exact absurd h1 hev
      · rw [h1]
        decide
    obtain ⟨x, hx, q, hq, hxq⟩ := cbg_even_case D.θ hn' hσ' hev'
    refine ⟨x, q, 1, hx, hq, by norm_num, ?_⟩
    rw [pow_one, ← hxq]
    group

end CbData

theorem EndCfg4.not_involution_centralizer {G T : Subgroup (MulAut V)} (h : EndCfg4 G T Y)
    {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) (hXG : X ≤ G)
    (hX : CbAlg Y t m X) {q : MulAut V} (hqG : q ∈ G)
    (hqX : q ∈ Subgroup.centralizer (X : Set (MulAut V))) (hq2 : q ^ 2 = 1) : q = 1 := by
  have _ := hodd
  by_contra hq1
  obtain ⟨ε⟩ := hY
  obtain ⟨θ, -⟩ := hX.alt
  have hYX : Y ≤ X := hX.Y_le
  have hqY : q ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff] at hqX ⊢
    exact fun y hy => hqX y (hYX hy)
  have hcent := h.cent q ⟨hqG, hqY⟩ hq1 hq2
  have hXle : X ≤ G ⊓ Subgroup.centralizer ({q} : Set (MulAut V)) := by
    intro x hx
    refine ⟨hXG hx, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (Subgroup.mem_centralizer_iff.mp hqX x hx).symm
  have hsub : (Y.subgroupOf X).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hXle hcent
  have hsimple : IsSimpleGroup ↥X := by
    have : IsSimpleGroup (alternatingGroup (Fin (m + 2))) :=
      alternatingGroup.isSimpleGroup (by simp; omega)
    exact θ.isSimpleGroup
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hsub with hbot | htop
  · have hYnt : Nontrivial ↥Y := by
      have : Nontrivial (alternatingGroup (Fin m)) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
      exact ε.toEquiv.nontrivial
    obtain ⟨y₀, hy₀⟩ : ∃ y : ↥Y, y ≠ 1 := exists_ne 1
    have hmem : (⟨(y₀ : MulAut V), hYX y₀.2⟩ : ↥X) ∈ Y.subgroupOf X := y₀.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 : (y₀ : MulAut V) = 1 := congrArg Subtype.val hmem
    exact hy₀ (Subtype.ext h2)
  · have hXY : X ≤ Y := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥X) ∈ Y.subgroupOf X := by
        rw [htop]
        trivial
      exact hmem
    have hcardX : Nat.card ↥X = (m + 2).factorial / 2 := by
      have : Nontrivial (Fin (m + 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hcardY : Nat.card ↥Y = m.factorial / 2 := by
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr ε.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h1 := Subgroup.card_le_of_le hXY
    rw [hcardX, hcardY] at h1
    have h2m : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2m2 : 2 ∣ (m + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : m.factorial < (m + 2).factorial := (Nat.factorial_lt (by omega)).mpr (by omega)
    omega

theorem EndCfg4.odd_card_centralizer {G T : Subgroup (MulAut V)} (h : EndCfg4 G T Y)
    {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) (hXG : X ≤ G)
    (hX : CbAlg Y t m X) :
    Odd (Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut V)))) := by
  by_contra hno
  have h2 : 2 ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut V))) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hno)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut V)))) 2 h2
  have hc2 : (c : MulAut V) ^ 2 = 1 := by
    have h3 := pow_orderOf_eq_one c
    rw [hc] at h3
    exact congrArg Subtype.val h3
  have hc1 : (c : MulAut V) = 1 :=
    h.not_involution_centralizer hm hodd hY hXG hX (Subgroup.mem_inf.mp c.2).1
      (Subgroup.mem_inf.mp c.2).2 hc2
  have hc3 : c = 1 := Subtype.ext hc1
  rw [hc3, orderOf_one] at hc
  omega

end CFSG.CGT.PushingUpLit.CGT6
