module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4Fam
public import CFSG.ClassicalInvolution.Q3.Q3TJD4Out
public import CFSG.ClassicalInvolution.Q3.Q3TJPSU
public import CFSG.ClassicalInvolution.Q3.Q3SBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

theorem exists_mulEquiv_apply_eq {S X Y : Type*} [Group S] [Group X] [Group Y] (f : S →* X)
    (hf : Function.Surjective f) (g : S →* Y) (hg : Function.Surjective g) (h : f.ker = g.ker) :
    ∃ e : X ≃* Y, ∀ s, e (f s) = g s := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)), fun s => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f s) = (s : S ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

theorem exists_eq_conj_of_centralizes_d4 {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (f : spinGroup (quadPlus 4 (GaloisField 3 1)) →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))))
    {z : X} {K : Subgroup X} (hKz : K ≤ Subgroup.centralizer ({z} : Set X)) (hzK : z ∈ K)
    {g : spinGroup (quadPlus 4 (GaloisField 3 1))}
    (hKR : K = (Generic.conjSub g (d4R0 (GaloisField 3 1))).map f)
    (α : MulAut X) (hodd : Odd (orderOf α))
    (hcent : ∀ c ∈ Subgroup.centralizer ({z} : Set X), α c = c) :
    ∃ x : X, α = MulAut.conj x := by
  have hker' : f.ker = Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) :=
    le_antisymm hker (ModelFacts.ChevAut.center_le_ker_of_surjective hf hZ)
  obtain ⟨e, he⟩ := exists_mulEquiv_apply_eq f hf (d4Proj (GaloisField 3 1))
    (spinToStatedProj_quadPlus three_le_four).1
    (hker'.trans (spinToStatedProj_quadPlus three_le_four).2.2.symm)
  obtain ⟨r, hrR, hrz⟩ : ∃ r ∈ Generic.conjSub g (d4R0 (GaloisField 3 1)), f r = z := by
    rw [hKR] at hzK
    exact hzK
  have hmem : ∀ i, f (g * d4Six (GaloisField 3 1) i * g⁻¹) ∈
      Subgroup.centralizer ({z} : Set X) := by
    intro i
    by_cases hi : i = .inl false
    · subst hi
      refine hKz ?_
      rw [hKR]
      exact Subgroup.mem_map_of_mem f (Generic.conj_mem_conjSub d4Six_inl_false_mem)
    · have hr₀ : g⁻¹ * r * g ∈ d4R0 (GaloisField 3 1) := Generic.mem_conjSub_iff.mp hrR
      have hc := (d4Six_commute i hi _ hr₀).eq
      have hcomm : g * d4Six (GaloisField 3 1) i * g⁻¹ * r =
          r * (g * d4Six (GaloisField 3 1) i * g⁻¹) := by
        calc g * d4Six (GaloisField 3 1) i * g⁻¹ * r =
            g * (d4Six (GaloisField 3 1) i * (g⁻¹ * r * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * r * g) * d4Six (GaloisField 3 1) i) * g⁻¹ := by rw [hc]
          _ = r * (g * d4Six (GaloisField 3 1) i * g⁻¹) := by group
      rw [Subgroup.mem_centralizer_singleton_iff, ← hrz, ← map_mul, ← map_mul, hcomm]
  have hβ : ∀ i, MulAut.congr e α (d4Proj (GaloisField 3 1) g *
      d4Proj (GaloisField 3 1) (d4Six (GaloisField 3 1) i) * (d4Proj (GaloisField 3 1) g)⁻¹) =
      d4Proj (GaloisField 3 1) g * d4Proj (GaloisField 3 1) (d4Six (GaloisField 3 1) i) *
        (d4Proj (GaloisField 3 1) g)⁻¹ := by
    intro i
    rw [← map_inv, ← map_mul, ← map_mul, ← he]
    change e (α (e.symm (e _))) = _
    rw [MulEquiv.symm_apply_apply, hcent _ (hmem i)]
  have hF := smul_statedPointFamily_eq_of_fix (MulAut.congr e α) (d4Proj (GaloisField 3 1) g) hβ
  obtain ⟨y, hy⟩ := exists_eq_conj_of_smul_statedPointFamily (MulAut.congr e α) hF
    (by rwa [MulEquiv.orderOf_eq])
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

theorem d4OddAutInner3_proved : D4OddAutInner3 := by
  intro X _ _ hX hZ f hf hker z K hKz α hodd hfix
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hz2 := hKz.orderOf_eq_two
  have hOC : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ :=
    oddCentralizerFreeTag_POmegaPlus 4 Nat.prime_three trivial hadm X f hf hker z hz2
  have hcent : ∀ c ∈ Subgroup.centralizer ({z} : Set X), α c = c := by
    intro c hc
    have h := hfix c hc
    rw [hOC, Subgroup.mem_bot] at h
    calc α c = c * (c⁻¹ * α c) := by group
      _ = c := by rw [h, mul_one]
  obtain ⟨⟨R, hR, hKR⟩, -⟩ := classicalIsFundamental3_proved .POmegaPlus 4 Nat.prime_three
    trivial hadm X f hf hker K z hKz
  have hR₀ : d4R0 (GaloisField 3 1) ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D :=
    RouteD.rankOne_mem_fundamentalSubgroups_plusDatum three_le_four 0
  obtain ⟨g, hg⟩ := ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Nat.prime_three trivial
    hadm (by decide) (by decide) _ hR₀ R hR
  exact exists_eq_conj_of_centralizes_d4 hZ f hf hker hKz.le_centralizer hKz.mem
    (g := g) (hKR.trans (congrArg (Subgroup.map f) hg)) α hodd hcent

theorem modelOddAutRigid_proved : ModelOddAutRigid :=
  modelOddAutRigid_of_D4 d4OddAutInner3_proved

end CFSG.ClassicalInvolution.Q3.Q3T
