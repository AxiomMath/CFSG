module

public import CFSG.ClassicalInvolution.AschTight.S1911P3i
public import CFSG.ClassicalInvolution.AschTight.S19MFactM0
public import CFSG.ClassicalInvolution.AschTight.S19MFactM2
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem fusion_of_sectionType' (hM1 : FactM1) (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ}
    (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩)
    (hΩ : HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)))
    (hDE : Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)))
    (hsec : SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a))
        .PSL 3 ∨ SectionLieType p e₀ (conjFamily (perfectCoreIn K a))
          (conjGen (perfectCoreIn K a)) .PSU 3 ∨ SectionLieType p e₀
            (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) .G2 0 ∨
              SectionLieType p e₀ (conjFamily (perfectCoreIn K a))
                (conjGen (perfectCoreIn K a)) .trialityD4 0)
    (hL3 : (SectionLieType p e₀ (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a))
        .PSL 3 ∨ SectionLieType p e₀ (conjFamily (perfectCoreIn K a))
          (conjGen (perfectCoreIn K a)) .PSU 3) →
      ∀ s : ↥(Subgroup.centralizer ({a} : Set G)), (∃ g : G, (s : G) = g * z * g⁻¹) →
        (s : G) * z = z * (s : G) →
        ∃ y ∈ conjGen (perfectCoreIn K a), ∀ x ∈ conjGen (perfectCoreIn K a),
          (s * y⁻¹) * x * (s * y⁻¹)⁻¹ * x⁻¹ ∈ oddCoreOf (conjGen (perfectCoreIn K a)))
    (s : ↥(Subgroup.centralizer ({a} : Set G))) (hs : ∃ g : G, (s : G) = g * z * g⁻¹) :
    ∃ c : ↥(Subgroup.centralizer ({a} : Set G)), s = c * ⟨z, hzA⟩ * c⁻¹ := by
  have hp2 : p ≠ 2 := hd.tight.branch.odd
  have := conjGen_normal (perfectCoreIn K a)
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  have hLY : perfectCoreIn K a ≤ conjGen (perfectCoreIn K a) := le_conjGen ⟨1, conjSub_one _⟩
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hs2 : s * s = 1 := by
    obtain ⟨g, hg⟩ := hs
    apply Subtype.ext
    rw [Subgroup.coe_mul, hg, Subgroup.coe_one]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  obtain ⟨t, k, htag, hsecT⟩ : ∃ t k, IsT6Tag t k ∧ SectionLieType p e₀
      (conjFamily (perfectCoreIn K a)) (conjGen (perfectCoreIn K a)) t k := by
    rcases hsec with h | h | h | h
    · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, h⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl⟩), h⟩
    · exact ⟨_, _, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h⟩
    · exact ⟨_, _, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), h⟩
  obtain ⟨D, hcard, i, hti, hki⟩ := hsecT
  have htag' : IsT6Tag (D.tag i) (D.rank i) := by rw [hti, hki]; exact htag
  have hconj := conjInvariant_oddQuotientFamily (inClass_restrict_conjugates hmem).conjInvariant
  have hO := CFSG.ComponentClassification.OddCore.quotient_corefree ↥(conjGen (perfectCoreIn K a))
  have hu1 := isUniqueInvolution_secImg hd hzA hzKa 1
  have : Nontrivial (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a))) := ⟨⟨_, 1, hu1.ne_one⟩⟩
  have hsimple := isSimpleGroup_of_lieSystemData S19M.factM3 hp2 D hcard i htag' hO
  have M := ih8Model_of_lieSystemData D hcard i hconj
  have hΦne : (oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K a))
      (conjGen (perfectCoreIn K a)))).Nonempty :=
    ⟨_, (mem_secFamily_iff _ _).mpr ⟨1, rfl⟩⟩
  have hcen : Subgroup.center (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a))) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥(conjGen
      (perfectCoreIn K a)) ⧸ classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))) with h | h
    · exact h
    · exfalso
      obtain ⟨x, -, y, -, hxy⟩ := exists_noncomm_secImg hd h5 hzA hmem
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hDEΦ := (section_facts hp2 h5 hΩ ⟨_, ⟨1, conjSub_one _⟩⟩ hDE).2.2.2.1
  obtain ⟨X, hX, hXφ⟩ := S19M.factM0' p e₀ hp2 h5 _ _ _ _ _ htag' ⟨M⟩ hΦne hDEΦ
    (secAct (conjGen (perfectCoreIn K a)) s) (by rw [← map_mul, hs2, map_one])
    (secAct_preserves _ s)
  obtain ⟨c, rfl⟩ := (mem_secFamily_iff _ X).mp hX
  obtain ⟨v, -, hv⟩ := exists_conj_comm_of_secAct hd hzA hzKa hs2 hXφ
  set d := v * c with hd'
  set s₁ := d⁻¹ * s * d with hs₁
  suffices h : ∃ c₁ : ↥(Subgroup.centralizer ({a} : Set G)), s₁ = c₁ * ⟨z, hzA⟩ * c₁⁻¹ by
    obtain ⟨c₁, hc₁⟩ := h
    refine ⟨d * c₁, ?_⟩
    calc s = d * s₁ * d⁻¹ := by rw [hs₁]; group
      _ = d * c₁ * ⟨z, hzA⟩ * (d * c₁)⁻¹ := by rw [hc₁]; group
  have hs₁g : ∃ g : G, (s₁ : G) = g * z * g⁻¹ := by
    obtain ⟨g, hg⟩ := hs
    refine ⟨(d : G)⁻¹ * g, ?_⟩
    rw [hs₁, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group
  have hs₁z : (s₁ : G) * z = z * (s₁ : G) := congrArg Subtype.val hv
  have hs₁2 : s₁ * s₁ = 1 := by
    rw [hs₁]
    calc d⁻¹ * s * d * (d⁻¹ * s * d) = d⁻¹ * (s * s) * d := by group
      _ = 1 := by rw [hs2]; group
  by_cases hs₁e : (s₁ : G) = z
  · exact ⟨1, Subtype.ext (by rw [hs₁e]; simp)⟩
  have hφ2 : secAct (conjGen (perfectCoreIn K a)) s₁ * secAct (conjGen (perfectCoreIn K a)) s₁ =
      1 := by rw [← map_mul, hs₁2, map_one]
  obtain ⟨ē, hē⟩ : ∃ ē, secAct (conjGen (perfectCoreIn K a)) s₁ = MulAut.conj ē := by
    rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨y, hy, hyx⟩ := hL3 (Or.inl ⟨D, hcard, i, hti, hki⟩) s₁ hs₁g hs₁z
      exact ⟨_, secAct_eq_conj_of_residual hy hyx⟩
    · obtain ⟨y, hy, hyx⟩ := hL3 (Or.inr ⟨D, hcard, i, hti, hki⟩) s₁ hs₁g hs₁z
      exact ⟨_, secAct_eq_conj_of_residual hy hyx⟩
    all_goals
      have hLΦ := (mem_secFamily_iff (perfectCoreIn K a) _).mpr ⟨1, rfl⟩
      rw [conjSub_one] at hLΦ
      have hnorm : (secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a)).map
          (secAct (conjGen (perfectCoreIn K a)) s₁).toMonoidHom =
            secImg (conjGen (perfectCoreIn K a)) (perfectCoreIn K a) := by
        rw [secAct_secImg _ s₁ hLY,
          conjSub_eq_of_mem_normalizer (mem_normalizer_perfectCoreIn hd hs₁z)]
      refine hM1 p e₀ hp2 h5 _ _ _ _ _ (by rw [hti, hki]; simp) ⟨M⟩ _ hφ2
        (secAct_preserves _ s₁) _ hLΦ hnorm ?_
      intro P hP2 hPL hfix
      by_contra hne
      push Not at hne
      obtain ⟨x, hx, y, hy, hxy⟩ := hne
      exact false_of_fixes_nonabelian hd hs₁g hs₁z hs₁2 hs₁e hP2 hPL hfix ⟨x, hx, y, hy, hxy⟩
  have hē2 : ē * ē = 1 := by
    have h1 : MulAut.conj (ē * ē) = 1 := by rw [map_mul, ← hē, hφ2]
    have h2 : ē * ē ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut _ => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * (ē * ē) = ē * ē * g * (ē * ē)⁻¹ * (ē * ē) := by rw [this]
        _ = ē * ē * g := by group
    rw [hcen, Subgroup.mem_bot] at h2
    exact h2
  by_cases hē1 : ē = 1
  · exfalso
    rw [hē1, map_one] at hē
    exact hs₁e (eq_of_secAct_fixes hd h5 hzA hmem hs₁g hs₁z hs₁2 (fun x _ => by rw [hē]; rfl))
  obtain ⟨X', hX', hX'u⟩ := S19M.factM2 p e₀ hp2 h5 _ _ _ _ _ htag' ⟨M⟩ hΦne ē hē2 hē1
  obtain ⟨c', rfl⟩ := (mem_secFamily_iff _ X').mp hX'
  have hē' := (isUniqueInvolution_secImg hd hzA hzKa c').eq hX'u
  have huY : c' * ⟨z, hzA⟩ * c'⁻¹ ∈ conjGen (perfectCoreIn K a) :=
    le_conjGen ⟨c', rfl⟩ (isUniqueInvolution_conjSub_perfectCoreIn hd hzA hzKa c').mem
  refine exists_conj_eq_of_secAct_eq hd h5 hzA hmem hs₁g hs₁2 (c' := c') ?_
  rw [hē, ← hē', secAct_of_mem _ huY]
  rfl


end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
