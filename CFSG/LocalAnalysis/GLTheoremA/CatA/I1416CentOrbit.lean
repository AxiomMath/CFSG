module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows.CentOrbit

open MulAction

variable {G : Type*} [Group G] [Finite G] {w : G} {F : Set G}

@[expose, reducible] def conjAct
    (hF : ∀ g ∈ Subgroup.centralizer ({w} : Set G), ∀ x ∈ F, g * x * g⁻¹ ∈ F) :
    MulAction ↥(Subgroup.centralizer ({w} : Set G)) ↥F where
  smul g x := ⟨(g : G) * x * (g : G)⁻¹, hF g g.2 x x.2⟩
  one_smul x := Subtype.ext (by
    show ((1 : ↥(Subgroup.centralizer ({w} : Set G))) : G) * (x : G) *
      ((1 : ↥(Subgroup.centralizer ({w} : Set G))) : G)⁻¹ = x
    simp)
  mul_smul g h x := Subtype.ext (by
    show ((g * h : ↥(Subgroup.centralizer ({w} : Set G))) : G) * (x : G) *
      ((g * h : ↥(Subgroup.centralizer ({w} : Set G))) : G)⁻¹ =
      (g : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (g : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem conjAct_smul_val (hF : ∀ g ∈ Subgroup.centralizer ({w} : Set G), ∀ x ∈ F, g * x * g⁻¹ ∈ F)
    (g : ↥(Subgroup.centralizer ({w} : Set G))) (x : ↥F) :
    ((@HSMul.hSMul _ _ _ (@instHSMul _ _ (conjAct hF).toSMul) g x : ↥F) : G) =
      (g : G) * x * (g : G)⁻¹ := rfl

theorem card_centralizer_eq_mul_orbit
    (hF : ∀ g ∈ Subgroup.centralizer ({w} : Set G), ∀ x ∈ F, g * x * g⁻¹ ∈ F)
    {x₀ : G} (hx₀ : x₀ ∈ F) {N : ℕ}
    (hN : Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x₀} : Set G)) = N) :
    ∃ m, Nat.card ↥(Subgroup.centralizer ({w} : Set G)) = N * m ∧ m ≤ F.ncard := by
  classical
  letI := conjAct hF
  set S := stabilizer ↥(Subgroup.centralizer ({w} : Set G)) (⟨x₀, hx₀⟩ : ↥F)
  have hS : Nat.card S = N := by
    rw [← hN]
    refine Nat.card_congr (Equiv.ofBijective
      (fun s => ⟨((s : ↥(Subgroup.centralizer ({w} : Set G))) : G), ?_⟩) ⟨?_, ?_⟩)
    · refine Subgroup.mem_inf.2 ⟨(s : ↥(Subgroup.centralizer ({w} : Set G))).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg Subtype.val (mem_stabilizer_iff.1 s.2)
      rw [conjAct_smul_val hF] at h
      calc (s : G) * x₀ = (s : G) * x₀ * (s : G)⁻¹ * (s : G) := by group
        _ = x₀ * (s : G) := by rw [h]
    · intro a b hab
      have h := congrArg Subtype.val hab
      simp only at h
      exact Subtype.ext (Subtype.ext h)
    · rintro ⟨y, hy⟩
      obtain ⟨hyw, hyx⟩ := Subgroup.mem_inf.1 hy
      refine ⟨⟨⟨y, hyw⟩, ?_⟩, rfl⟩
      rw [mem_stabilizer_iff]
      apply Subtype.ext
      rw [conjAct_smul_val hF]
      show y * x₀ * y⁻¹ = x₀
      rw [Subgroup.mem_centralizer_singleton_iff.1 hyx]
      group
  refine ⟨S.index, ?_, ?_⟩
  · rw [← S.index_mul_card, hS, mul_comm]
  · rw [index_stabilizer]
    calc (orbit ↥(Subgroup.centralizer ({w} : Set G)) (⟨x₀, hx₀⟩ : ↥F)).ncard ≤ (Set.univ : Set ↥F).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = F.ncard := by rw [Set.ncard_univ, Nat.card_coe_set_eq]

theorem prime_dvd_card_of_dvd_centralizer
    (hF : ∀ g ∈ Subgroup.centralizer ({w} : Set G), ∀ x ∈ F, g * x * g⁻¹ ∈ F) {N : ℕ}
    (hN : ∀ x ∈ F, Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) = N)
    {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set G)))
    (hrN : ¬ r ∣ N) : r ∣ F.ncard := by
  classical
  letI := conjAct hF
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({w} : Set G))) r hrC
  set P := Subgroup.zpowers g
  have hP : IsPGroup r ↥P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  haveI : Fintype ↥F := Fintype.ofFinite _
  haveI : Fintype (fixedPoints ↥P ↥F) := Fintype.ofFinite _
  have hfix : IsEmpty (fixedPoints ↥P ↥F) := by
    constructor
    rintro ⟨x, hx⟩
    have hgx := hx ⟨g, Subgroup.mem_zpowers g⟩
    have hgx' : (g : G) * x * (g : G)⁻¹ = x := by
      have h := congrArg Subtype.val hgx
      rw [Subgroup.smul_def, conjAct_smul_val hF] at h
      exact h
    have hmem : (g : G) ∈ Subgroup.centralizer ({w} : Set G) ⊓
        Subgroup.centralizer ({(x : G)} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨g.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * (g : G) := by group
        _ = x * (g : G) := by rw [hgx']
    have hd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_coe, hg, hN x x.2] at hd
    exact hrN hd
  have hmod := hP.card_modEq_card_fixedPoints ↥F
  rw [@Nat.card_of_isEmpty _ hfix] at hmod
  have h0 : Nat.card ↥F % r = 0 := hmod
  rw [← Nat.card_coe_set_eq]
  exact Nat.dvd_of_mod_eq_zero h0

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows.CentOrbit
