module

public import CFSG.ClassicalInvolution.Asc77.AscIHLie
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryThree
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem comap_le_center_of_normal_pGroup {M G : Type*} [Group M] [Group G] [Finite G]
    (hM : CFSG.Open.IsQuasisimple M) (φ : M →* G) (hker : φ.ker ≤ Subgroup.center M)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup 2 N) : N.comap φ ≤ Subgroup.center M := by
  obtain ⟨hperf, hsimple⟩ := hM
  set N' := N.comap φ with hN'
  have : N'.Normal := Subgroup.Normal.comap inferInstance φ
  by_contra hnot
  have himg : N'.map (QuotientGroup.mk' (Subgroup.center M)) = ⊤ := by
    have hnm : (N'.map (QuotientGroup.mk' (Subgroup.center M))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hsimple.eq_bot_or_eq_top_of_normal (N'.map (QuotientGroup.mk' (Subgroup.center M)))
      with h | h
    · exfalso
      apply hnot
      intro x hx
      have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center M)) hx
      rw [h, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff x).mp h1
    · exact h
  have hsup : N' ⊔ Subgroup.center M = ⊤ := by
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center M)) N'
    rw [himg, QuotientGroup.ker_mk', Subgroup.comap_top] at h1
    exact h1.symm
  have hcomm : commutator M ≤ N' := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    have ha : a ∈ N' ⊔ Subgroup.center M := by rw [hsup]; trivial
    have hb : b ∈ N' ⊔ Subgroup.center M := by rw [hsup]; trivial
    obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    have hc : ∀ (u z : M), z ∈ Subgroup.center M →
        QuotientGroup.mk' N' z * QuotientGroup.mk' N' u = QuotientGroup.mk' N' u *
          QuotientGroup.mk' N' z := fun u z hz => by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz u).symm]
    have h1 : QuotientGroup.mk' N' y₁ = 1 := (QuotientGroup.eq_one_iff y₁).mpr hy₁
    have h2 : QuotientGroup.mk' N' y₂ = 1 := (QuotientGroup.eq_one_iff y₂).mpr hy₂
    have e1 : QuotientGroup.mk' N' (y₁ * z₁) = QuotientGroup.mk' N' z₁ := by
      rw [map_mul, h1, one_mul]
    have e2 : QuotientGroup.mk' N' (y₂ * z₂) = QuotientGroup.mk' N' z₂ := by
      rw [map_mul, h2, one_mul]
    rw [← QuotientGroup.ker_mk' N', MonoidHom.mem_ker, map_commutatorElement, e1, e2]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc z₂ z₁ hz₁)
  have hN'top : N' = ⊤ := top_le_iff.mp (hperf ▸ hcomm)
  have hle : φ.range ≤ N := by
    rintro _ ⟨m, rfl⟩
    have : m ∈ N' := hN'top ▸ Subgroup.mem_top m
    exact this
  have h2 : IsPGroup 2 ↥φ.range := hN.to_le hle
  have : Group.IsNilpotent ↥φ.range := IsPGroup.isNilpotent h2
  have : Group.IsSolvable ↥φ.range := inferInstance
  have hsolv : Group.IsSolvable M :=
    Group.isSolvable_of_ker_le_range (Subgroup.center M).subtype φ.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
      exact hker)
  have : Nontrivial M := (QuotientGroup.mk'_surjective (Subgroup.center M)).nontrivial
  have : Group.IsPerfect M := ⟨hperf⟩
  exact Group.IsPerfect.not_isSolvable M hsolv

theorem commutes_range_of_normal_pGroup {M G : Type*} [Group M] [Group G] [Finite G]
    (hM : CFSG.Open.IsQuasisimple M) (φ : M →* G) (hker : φ.ker ≤ Subgroup.center M)
    (hQ : φ.range.Normal) {N : Subgroup G} [N.Normal] (hN : IsPGroup 2 N) :
    Commutes φ.range N := by
  have hN' := comap_le_center_of_normal_pGroup hM φ hker hN
  have hZ : N ⊓ φ.range ≤ Subgroup.centralizer (φ.range : Set G) := by
    rintro y ⟨hyN, m, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨m', rfl⟩
    have hm : m ∈ Subgroup.center M := hN' hyN
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hm m']
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    have h1 : (⊤ : Subgroup M).map φ = φ.range := Subgroup.map_top φ
    have h2 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup M)) (H₂ := ⊤) φ
    rw [h1, ← commutator_def, hM.1, Subgroup.map_top] at h2
    exact h2.symm
  have hQN : ⁅φ.range, N⁆ ≤ N ⊓ φ.range := by
    have := Subgroup.commutator_le_inf (H₁ := φ.range) (H₂ := N)
    rwa [inf_comm] at this
  have h1 : ⁅⁅φ.range, N⁆, φ.range⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hQN.trans hZ)
  have h2 : ⁅⁅N, φ.range⁆, φ.range⁆ = ⊥ := by
    rw [Subgroup.commutator_comm N φ.range]
    exact h1
  have h3 : ⁅⁅φ.range, φ.range⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hperf] at h3
  intro a ha b hb
  have hle : φ.range ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

theorem isFundTag_modelFacts {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (h : CFSG.ClassicalInvolution.Generic.IsFundTag t) :
    CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
  cases t <;> trivial

theorem thm2Below_of_citBelow {n : ℕ} (hn : CITBelowU p f n) : Thm2Below p f n := by
  intro _ _ G _ _ hG Ω hΩ hO hgen K hK _ z hz hN
  obtain ⟨N, hNn, hN2, hzN⟩ := hN
  have : N.Normal := hNn
  obtain ⟨D⟩ := exists_omegaLie hn hΩ ⟨K, hK⟩ hO hG
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  have hgen' : omegaGen Ω = ⊤ := hgen
  have hQ : (D.hom i).range.Normal :=
    ⟨fun x hx g => D.mem_comp_conj (hgen' ▸ Subgroup.mem_top g) hx⟩
  have hquasi : CFSG.Open.IsQuasisimple (D.model i).K :=
    isQuasisimple_modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out
      (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i)
  have hcomm := commutes_range_of_normal_pGroup hquasi (D.hom i) (D.ker_le_center i) hQ hN2
  obtain ⟨r, hrR, hrz⟩ := Subgroup.mem_map.mp (hKR ▸ hz.mem)
  have hzc : ∀ y : (D.model i).K, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (D.model i).K := by
    intro y
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker]
    have h := hcomm (D.hom i y) ⟨y, rfl⟩ z hzN
    simp only [map_mul, map_inv, hrz]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h.symm
  by_cases hne : D.tag i = .PSL ∧ D.rank i = 2
  · have hR' : R = ⊤ :=
      (fundamentalIsWhole_modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out
        (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i)).1 hne R hR
    have hK' : K = (D.hom i).range := by rw [hKR, hR', Subgroup.map_top]
    exact hK' ▸ hQ
  · exfalso
    have hr1 := fundNoncentral_generic p (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i)
      (D.admissible i) hne R hR r hrR hzc
    apply hz.ne_one
    rw [← hrz, hr1, map_one]

end CFSG.ClassicalInvolution.Asc77
