module

public import CFSG.ClassicalInvolution.AschTight.S1911FusD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [Finite G] [IsSimpleGroup G] in
abbrev perfectCoreIn (K : Subgroup G) (a : G) : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))).subgroupOf
    (Subgroup.centralizer ({a} : Set G))

omit [Finite G] [IsSimpleGroup G] in
theorem conjSub_perfectCore_eq {a c₁ c₂ : G} (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G)) (h : conjSub c₁ K = conjSub c₂ K) :
    conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) =
      conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
  have hnK : conjSub (c₂⁻¹ * c₁) K = K := by
    rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hnA : c₂⁻¹ * c₁ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₂) hc₁
  have hnN : c₂⁻¹ * c₁ ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj (c₂⁻¹ * c₁)).injective]
    change conjSub (c₂⁻¹ * c₁) K ⊓ conjSub (c₂⁻¹ * c₁) (Subgroup.centralizer ({a} : Set G)) = _
    rw [hnK, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnA)]
  have hnKa := conjSub_eq_of_mem_normalizer (perfectResidualOf_normalizer_contains _ hnN)
  calc conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
      = conjSub (c₂ * (c₂⁻¹ * c₁))
          (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
        rw [mul_inv_cancel_left]
    _ = conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
        rw [conjSub_mul, hnKa]

theorem false_of_le_normalizer_conjSub (hd : Sec19Data p f K z S W) {a : G}
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) {c₁ c₂ : G}
    (hc₁ : c₁ ∈ Subgroup.centralizer ({a} : Set G)) (hc₂ : c₂ ∈ Subgroup.centralizer ({a} : Set G))
    (hne : conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≠
      conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x)
    (hR8 : 2 < Nat.card R)
    (hRle : R ≤ conjSub c₂ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))))
    (hRN : R ≤ Subgroup.normalizer
      ((conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) : Subgroup G) :
        Set G)) : False := by
  have htb := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hΩ := hypOmegaMod_of_tightD hd.tight
  have hKaK : perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K :=
    (perfectResidualOf_le _).trans inf_le_left
  have hJ₁ : conjSub c₁ K ∈ CoreAssembly.conjClass K := ⟨c₁, rfl⟩
  have hJ₂ : conjSub c₂ K ∈ CoreAssembly.conjClass K := ⟨c₂, rfl⟩
  have hI₁ := hI.conj c₁
  have hI₂ := hI.conj c₂
  have hJne : conjSub c₁ K ≠ conjSub c₂ K := fun h => hne (conjSub_perfectCore_eq hc₁ hc₂ h)
  have hRz : R ≤ Subgroup.centralizer ({c₁ * z * c₁⁻¹} : Set G) := by
    intro x hx
    have h1 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈
        conjSub c₁ (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) :=
      (Subgroup.mem_normalizer_iff.mp (hRN hx) _).mp (conj_mem_conjSub hzKa)
    have h2 : x * (c₁ * z * c₁⁻¹) * x⁻¹ ∈ conjSub c₁ K := Subgroup.map_mono hKaK h1
    have h3 : x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) = 1 := by
      calc x * (c₁ * z * c₁⁻¹) * x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) =
          x * ((c₁ * z * c₁⁻¹) * (c₁ * z * c₁⁻¹)) * x⁻¹ := by group
        _ = 1 := by rw [hI₁.sq]; group
    rcases hI₁.unique _ h2 h3 with h | h
    · exfalso
      apply hI₁.ne_one
      calc c₁ * z * c₁⁻¹ = x⁻¹ * (x * (c₁ * z * c₁⁻¹) * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (c₁ * z * c₁⁻¹) = x * (c₁ * z * c₁⁻¹) * x⁻¹ * x := by group
        _ = c₁ * z * c₁⁻¹ * x := by rw [h]
  have hRJ₂ : R ≤ conjSub c₂ K := hRle.trans (Subgroup.map_mono hKaK)
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRJ₂ hRz)
  have hz₂V : c₂ * z * c₂⁻¹ ∈ V := hRV (mem_of_le_member hI₂ hRJ₂ hR2 (by omega))
  have htwin : conjSub c₂ K ∉ twinSet (CoreAssembly.conjClass K) (conjSub c₁ K) := by
    rintro ⟨-, u, hu₁, hu₂⟩
    exact hJne (eq_of_isUniqueInvolution_member htb hJ₁ hJ₂ hu₁ hu₂)
  have hcard : Nat.card R ≤ Nat.card V := Subgroup.card_le_of_le hRV
  rcases Asc77.l6_2 p f hd.tight.branch.odd hd.tight.branch.five G _ hΩ _ hJ₁ _ hI₁ _ hJ₂ htwin _
    hI₂ V hV hz₂V with ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact hI₂.sq)
      hI₂.ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · exact not_le_normalizer_of_mem_rSet hd.tight.edgeless hJ₂ hJ₁ hJne.symm hV4
      (hV.1.trans inf_le_left)
      ((hV.1.trans inf_le_right).trans (centralizer_le_normalizer_member htb hJ₁ hI₁))

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
