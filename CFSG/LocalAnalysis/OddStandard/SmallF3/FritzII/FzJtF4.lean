module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtMod
public import Certificates.Data.FzJtCheck

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36 Certificates.FzFus
  Certificates.FzJt

variable {G : Type} [Group G]

theorem fzJt_exists_zs4 {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}
    {π : Model →* G} (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) {ε : G}
    (hε : ε ∈ fourGrp x₁ x₂) : ∃ z ∈ zs4 (), π z = ε := by
  have hz1 := (hd.isInvM_iff z1M).mp label_facts.2.1
  have hz3 := (hd.isInvM_iff z3M).mp label_facts.2.2.1
  have hcomm : π z1M * π z3M = π z3M * π z1M := by
    rw [← map_mul, ← map_mul, z1M_z3M_comm]
  rw [hd.z1M_eq] at hz1 hcomm
  rw [hd.z3M_eq] at hz3 hcomm
  rcases fzfus_mem_four hz1.1 hz3.1 hcomm hε with h | h | h | h
  · exact ⟨1, by simp [zs4], by rw [h, map_one]⟩
  · exact ⟨z1M, by simp [zs4], by rw [h, hd.z1M_eq]⟩
  · exact ⟨z3M, by simp [zs4], by rw [h, hd.z3M_eq]⟩
  · exact ⟨z1M * z3M, by simp [zs4], by rw [h, map_mul, hd.z1M_eq, hd.z3M_eq]⟩

theorem fzJtWitness_of_model (h : F4Fact) : FzJtWitness := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset u hu hu2 huR3 hnot
  obtain ⟨ht2, h1, h2, -⟩ := fzFus_rels hset
  obtain ⟨π, hd, hπ3⟩ := fzJt_dict hset.shape ht2 h1 h2
  obtain ⟨n, rfl⟩ := hd.mem_T₂_iff.mp hu
  have hsq : KEq (n * n) z3M := by
    refine (hd.eq_iff _ _).mp ?_
    rw [map_mul, hd.z3M_eq, ← pow_two]
    exact hu2
  have hR3 : ∀ q : Q8, ¬ KEq n (mkE 1 1 q) := fun q hk =>
    huR3 ((fzJt_mem_fzR3_iff hset.shape hπ3).mpr ⟨q, ((hd.eq_iff _ _).mpr hk).symm⟩)
  have hRZ : n.right = 1 → ∃ q : Q8, ∃ z ∈ zs4 (), KEq n (mkE 1 1 q * z) := by
    intro hr
    have hn : n = (⟨n.left, 1⟩ : Model) := by ext <;> simp [hr]
    have hmem : π n ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ :=
      hd.mem_fzR6_iff.mpr ⟨n.left, (congrArg π hn).symm⟩
    by_contra hno
    refine hnot ⟨hmem, ?_⟩
    rintro ⟨r, hr3, ε, hε, hrε⟩
    obtain ⟨q, rfl⟩ := (fzJt_mem_fzR3_iff hset.shape hπ3).mp hr3
    obtain ⟨z, hz, rfl⟩ := fzJt_exists_zs4 hd hε
    refine hno ⟨q, z, hz, (hd.eq_iff _ _).mp ?_⟩
    rw [map_mul]
    exact hrε
  obtain ⟨mv, mw, hvc, hwc, hIv, hIw, hne, hcomm, hnZv, hnZw, hnZvw⟩ := h n hsq hR3 hRZ
  refine ⟨π mv, ⟨fzJt_pi_mem hd mv, ?_⟩, π mw, ⟨fzJt_pi_mem hd mw, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul]
    exact (hd.eq_iff _ _).mpr hvc
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul]
    exact (hd.eq_iff _ _).mpr hwc
  · rw [pow_two]
    exact ((hd.isInvM_iff mv).mp hIv).1
  · rw [pow_two]
    exact ((hd.isInvM_iff mw).mp hIw).1
  · exact ((hd.isInvM_iff mv).mp hIv).2
  · exact ((hd.isInvM_iff mw).mp hIw).2
  · exact fun hk => hne ((hd.eq_iff _ _).mp hk)
  · rw [← map_mul, ← map_mul]
    exact (hd.eq_iff _ _).mpr hcomm
  · exact fun hz => hnZv ((fzJt_mem_calZ_iff hd mv).mp hz)
  · exact fun hz => hnZw ((fzJt_mem_calZ_iff hd mw).mp hz)
  · rw [← map_mul]
    exact fun hz => hnZvw ((fzJt_mem_calZ_iff hd (mv * mw)).mp hz)

end CFSG.OddStandard.SmallF3.FritzII
