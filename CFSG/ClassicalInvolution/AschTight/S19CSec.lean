module

public import CFSG.ClassicalInvolution.AschTight.S19CTop
public import CFSG.ClassicalInvolution.AschTight.S1911SecF
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.AschTight.S19CWit

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem sectionLieType_fieldInvolution' (hd : Sec19DataT p f K z S W L t V) (h9 : p ^ f ≠ 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K)
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : (∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({a} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩ ∧
      (SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .PSL 3 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .PSU 3 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .G2 0 ∨
        SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a))
          .trialityD4 0) := by
  have hd0 := hd.toSec19Data
  obtain ⟨e₀, hf, h5, hzA, hmem, hΩ, hDE, hlt, hIH, -⟩ :=
    sectionData_fieldInvolution hd0 h9 haS ha2 haX
  obtain ⟨c, hca, hczt⟩ := exists_conj_eq_t hd haS ha2 hat hk hu huo hact
  have hcA : c ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hca
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  have hne : c * z * c⁻¹ ≠ z := by
    rw [hczt]
    exact hd.ne
  have hcomm : c * z * c⁻¹ * z = z * (c * z * c⁻¹) := by
    rw [hczt]
    exact S1911.comm_of_mem hd0 t (S1911.mem_W hd) z (Hall196.mem_W_of_sec19DataT hd)
  have hTop := top_not_mem_secFamily hd0 hzA hzKa ⟨c, hcA⟩ hne hcomm
  exact ⟨e₀, hf, h5, hzA, hmem, sectionThm6 hd.tight.branch.odd h5 (ih8SmallEdge p) hIH hlt hΩ
    ⟨_, ⟨1, conjSub_one _⟩⟩ hDE hTop⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
