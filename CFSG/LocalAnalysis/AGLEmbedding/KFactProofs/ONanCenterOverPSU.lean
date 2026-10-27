module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCenterOverUnital
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution

public section

namespace CFSG.AGLEmbedding.CenterOver

open CFSG.UnitaryThreeRecognition CFSG.UnitaryThreeRecognition.Model
  CFSG.BenderSuzuki.MatrixGroups CFSG.AGLEmbedding.UnitaryModel

theorem eq_top_of_conj_mem {P : Type*} [Group P] [IsSimpleGroup P] {Z Y : Subgroup P}
    (hZ : Z ≠ ⊥) (h : ∀ g : P, ∀ z ∈ Z, g * z * g⁻¹ ∈ Y) : Y = ⊤ := by
  have hle : Subgroup.normalClosure (Z : Set P) ≤ Y := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxz
    exact h c z hz
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (Z : Set P)) with
    h0 | h1
  · exact absurd (le_bot_iff.mp (h0 ▸ Subgroup.le_normalClosure)) hZ
  · exact top_le_iff.mp (h1 ▸ hle)

theorem not_dvd_div_sq_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ¬ p ∣ ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3 := by
  intro h
  have hg : Nat.gcd (p ^ f + 1) 3 ∣ (p ^ f) ^ 2 - 1 :=
    (Nat.gcd_dvd_left _ _).trans (succ_dvd_sq_sub_one _)
  have h1 : p ∣ (p ^ f) ^ 2 - 1 := h.trans (Nat.div_dvd_of_dvd hg)
  have hq1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos f)
  have h2 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
  have h3 : p ∣ (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) := Nat.dvd_sub h2 h1
  rw [show (p ^ f) ^ 2 - ((p ^ f) ^ 2 - 1) = 1 by omega] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

omit hfix in
theorem two_ne_zero_of_card [Fact p.Prime] (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have : CharP K p := charP_of_card Fact.out hK
  intro h
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((CharP.cast_eq_zero_iff K p 2).mp this))

theorem unitalData_psu [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    UnitalData p f (rootGroup J hJ)
      (rootGroup J hJ ⊓ Subgroup.centralizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
      (pinf J hJ) (pzero J hJ) (invol J hJ) := by
  have h2 := two_ne_zero_of_card hK hp2
  have hZeq := rootGroup_inf_centralizer_invol J hJ hK hfix h2
  have hpair := stabilizer_pinf_inf_stabilizer_pzero J hJ (p ^ f) hK hfix
  have hZcard : Nat.card (rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = p ^ f := by
    rw [← hZeq]
    exact card_inf_centralizer_invol J hJ hK hfix h2
  exact
    { two := fun {x y z w} hxy hzw =>
        (MulAction.is_two_pretransitive_iff.mp
          (isMultiplyPretransitive_two J hJ (p ^ f) hK hfix)) hxy hzw
      root := ⟨rootGroup_le_stabilizer J hJ, fun g hg x hx =>
        conj_mem_rootGroup_of_smul_pinf J hJ (p ^ f) hK hfix hg hx, rootGroup_regular J hJ⟩
      ne := (pinf_ne_pzero J hJ).symm
      mem := ⟨torus_smul_pinf J hJ (-1), torus_smul_pzero J hJ (-1)⟩
      sq := invol_mul_self J hJ
      ne_one := invol_ne_one J hJ h2
      uniq := fun t ht hs => by
        have ht' : t ∈ torusGroup J hJ := by
          rw [← hpair]
          exact ht
        exact eq_one_or_eq_invol J hJ hK hfix h2 ht' hs
      cent := hZeq
      normQ := fun r hr z hz => by
        have := Subgroup.mem_centralizer_iff.mp hz.2 r hr
        rw [this]
        simpa using hz
      normZ := fun g hg z hz => by
        have hgz : g * z * g⁻¹ ∈ rootGroup J hJ :=
          conj_mem_rootGroup_of_smul_pinf J hJ (p ^ f) hK hfix hg hz.1
        refine ⟨hgz, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
        have hginv : g⁻¹ • pinf J hJ = pinf J hJ := by rw [inv_smul_eq_iff, hg]
        have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ rootGroup J hJ :=
          conj_mem_rootGroup_of_smul_pinf J hJ (p ^ f) hK hfix hginv hr
        have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hr'
        calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
          _ = g * z * g⁻¹ * r := by group
      card := by rw [hZcard, card_rootGroup J hJ (p ^ f) hK hfix]
      pf := hZcard
      coprime := by
        change ¬ p ∣ Nat.card (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
          (pinf J hJ) ⊓ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
            (pzero J hJ) : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
        rw [hpair, card_torusGroup J hJ (p ^ f) hK hfix]
        exact not_dvd_div_sq_sub_one Fact.out hf }

theorem overgroup_psu [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 2 < p ^ f)
    (Y : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hZY : rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ Y)
    (hY : ¬ Group.IsSolvable Y) :
    Y = ⊤ ∨ ∀ S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), S ≤ Y → IsPGroup p S →
      Nat.card S ≤ p ^ f := by
  have D := unitalData_psu J hJ hK hfix hp2 hf
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    isSimpleGroup_psu J (p ^ f) hK hfix hq
  have hnle : ¬ Y ≤ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
    intro hle
    have := isSolvable_stabilizer_pinf J hJ hK hfix
    exact hY (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  rcases D.dichotomy hf Y hZY hnle with h | h
  · left
    refine eq_top_of_conj_mem ?_ h
    intro hbot
    have hc := D.pf
    rw [hbot, Subgroup.card_bot] at hc
    have : 1 < p ^ f := by omega
    omega
  · exact Or.inr fun S hS hSp => (h S hS hSp).trans_eq D.pf

end Model

end CFSG.AGLEmbedding.CenterOver
