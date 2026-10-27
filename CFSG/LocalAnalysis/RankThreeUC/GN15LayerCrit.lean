module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Constr

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

variable {G : Type} [Group G] [Finite G]

private theorem eq_bot_of_commutator_eq_self {Q : Type*} [Group Q] [hQ : Group.IsSolvable Q]
    {R : Subgroup Q} (h : ⁅R, R⁆ = R) : R = ⊥ := by
  obtain ⟨n, hn⟩ := hQ.solvable
  have : ∀ m, R ≤ derivedSeries Q m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
      rw [derivedSeries_succ]
      calc R = ⁅R, R⁆ := h.symm
        _ ≤ ⁅derivedSeries Q m, derivedSeries Q m⁆ := Subgroup.commutator_mono ih ih
  exact le_bot_iff.mp (hn ▸ this n)

theorem isPConstrained_three_of_two_quotient {N F : Subgroup G} [hN : N.Normal] [hFn : F.Normal]
    (hF3 : IsPGroup 3 F) (hGN : IsPGroup 2 (G ⧸ N))
    (hab : ∀ x ∈ N ⊓ Subgroup.centralizer (F : Set G), ∀ y ∈ N ⊓ Subgroup.centralizer (F : Set G),
      x * y = y * x) :
    CFSG.ABGLocalTools.IsPConstrained 3 G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnot
  obtain ⟨L, hL⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Sylow155T51.exists_isComponent_of_not_isPConstrained hnot
  set O : Subgroup G := CFSG.pPrimeCore 3 G with hO
  set π : G →* G ⧸ O := QuotientGroup.mk' O with hπ
  haveI hNπ : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective O)
  set g : (G ⧸ O) →* ((G ⧸ O) ⧸ N.map π) := QuotientGroup.mk' (N.map π) with hg
  have hQ2 : IsPGroup 2 ((G ⧸ O) ⧸ N.map π) := by
    intro q
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x'
    obtain ⟨k, hk⟩ := hGN (QuotientGroup.mk x)
    refine ⟨k, ?_⟩
    have hx : x ^ 2 ^ k ∈ N :=
      (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hk)
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 ⟨x ^ 2 ^ k, hx, rfl⟩
  haveI : Group.IsNilpotent ((G ⧸ O) ⧸ N.map π) := hQ2.isNilpotent
  haveI : Group.IsSolvable ((G ⧸ O) ⧸ N.map π) := inferInstance
  have hLperf : ⁅L, L⁆ = L := by
    haveI := hL.1.1
    exact Subgroup.commutator_eq_self
  have hLN : L ≤ N.map π := by
    have h1 : L.map g = ⊥ := eq_bot_of_commutator_eq_self (by
      rw [← Subgroup.map_commutator, hLperf])
    rw [Subgroup.map_eq_bot_iff, hg, QuotientGroup.ker_mk'] at h1
    exact h1
  have hfit : F.map π ≤ fittingSubgroup (G ⧸ O) :=
    (le_sSup ⟨hFn.map π (QuotientGroup.mk'_surjective O), hF3.map π⟩ :
      F.map π ≤ CFSG.pCore 3 (G ⧸ O)).trans (CFSG.pCore_le_fitting _ 3)
  have hcomm : fittingSubgroup (G ⧸ O) ≤ Subgroup.centralizer ((layer (G ⧸ O) : Subgroup _) : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute
  have hLlayer : L ≤ layer (G ⧸ O) := CFSG.LocalCores.component_le_layer hL
  have key : ∀ n ∈ N, π n ∈ L → n ∈ Subgroup.centralizer (F : Set G) := by
    intro n hn hnL
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hc : π n * π f = π f * π n :=
      Subgroup.mem_centralizer_iff.1 (hcomm (hfit ⟨f, hf, rfl⟩)) (π n) (hLlayer hnL)
    have h1 : π (n * f * n⁻¹ * f⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have hzO : n * f * n⁻¹ * f⁻¹ ∈ O := (QuotientGroup.eq_one_iff _).1 h1
    have hzF : n * f * n⁻¹ * f⁻¹ ∈ F :=
      F.mul_mem (hFn.conj_mem f hf n) (F.inv_mem hf)
    obtain ⟨a, ha⟩ := hF3 ⟨_, hzF⟩
    have ha' : (n * f * n⁻¹ * f⁻¹) ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hord1 : orderOf (n * f * n⁻¹ * f⁻¹) ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha'
    have hord2 : orderOf (n * f * n⁻¹ * f⁻¹) ∣ Nat.card O := by
      simpa using Subgroup.orderOf_dvd_natCard O hzO
    have hcop : Nat.Coprime (3 ^ a) (Nat.card O) := CFSG.pPrimeCore_coprime_card.pow_left a
    have h1' : orderOf (n * f * n⁻¹ * f⁻¹) = 1 :=
      (Nat.Coprime.coprime_dvd_left hord1 hcop).eq_one_of_dvd hord2
    have hz1 : n * f * n⁻¹ * f⁻¹ = 1 := orderOf_eq_one_iff.mp h1'
    calc f * n = (n * f * n⁻¹ * f⁻¹) * (f * n) := by rw [hz1, one_mul]
      _ = n * f := by group
  have hLabel : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ * l₂ = l₂ * l₁ := by
    intro l₁ h₁ l₂ h₂
    obtain ⟨n₁, hn₁, rfl⟩ := hLN h₁
    obtain ⟨n₂, hn₂, rfl⟩ := hLN h₂
    have := hab n₁ ⟨hn₁, key n₁ hn₁ h₁⟩ n₂ ⟨hn₂, key n₂ hn₂ h₂⟩
    rw [← map_mul, ← map_mul, this]
  obtain ⟨a, b, hab'⟩ := hL.1.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hLabel a' a'.2 b' b'.2)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
