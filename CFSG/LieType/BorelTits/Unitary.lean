module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.BorelTits.Anisotropic
public import CFSG.LieType.BorelTits.IsotropicKernel
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem holds_statedSU (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    Holds (StatedSU n (p ^ f) K) p := by
  set F := unitaryForm p f hK n with hF
  set ρ := natRep (StatedSU n (p ^ f) K) with hρdef
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSU hK n
  have hinj : Function.Injective ρ := natRep_injective _
  have hσ : ∀ c, F.σ c = unitaryInvolution K p f c := fun _ => rfl
  have htrans : ∀ x : Fin n → K, F.β x x = 0 → ∀ c : K, unitaryInvolution K p f c = -c →
      ∃ h, ∀ v, ρ h v = v + (c * F.β x v) • x := by
    intro x hx c hc
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_transvection hK hx hc
    exact ⟨⟨A, hA⟩, fun v => by rw [natRep_apply]; exact hAv v⟩
  have heich : ∀ x y : Fin n → K, F.β x x = 0 → F.β x y = 0 → ∀ c : K,
      c + unitaryInvolution K p f c = -F.β y y →
      ∃ h, ∀ v, ρ h v = v + F.β x v • (y + c • x) - F.β y v • x := by
    intro x y hx hxy c hc
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_eichler hK hx hxy hc
    exact ⟨⟨A, hA⟩, fun v => by rw [natRep_apply]; exact hAv v⟩
  obtain ⟨c₀, hc₀, hc₀σ⟩ := exists_unitaryInvolution_eq_neg hK
  have hββ : ∀ u, unitaryInvolution K p f (F.β u u) = F.β u u := fun u =>
    (unitaryForm_symm hK u u).symm
  refine holds_of_isoFlags F ρ p hρ hinj ?_ ?_
  ·
    intro W hW hWiso
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨u, hu⟩ : ∃ u, F.β w u = 1 := by
      by_contra! h
      apply hw0
      refine F.nondeg w fun v => ?_
      by_contra hv
      apply h ((F.β w v)⁻¹ • v)
      rw [F.smul_right, inv_mul_cancel₀ hv]
    obtain ⟨l, hl⟩ := exists_add_unitaryInvolution_eq hK
      (a := -F.β u u) (by rw [map_neg, hββ])
    set e := u + l • w with he
    have hww : F.β w w = 0 := hWiso hwW w hwW
    have hwu' : F.β u w = 1 := by rw [unitaryForm_symm hK w u, hu, map_one]
    have hee : F.β e e = 0 := by
      rw [he, ReflForm.β_add_smul_add_smul, hww, hwu', hu, hσ]
      linear_combination hl
    have hwe : F.β w e = 1 := by
      rw [he, F.add_right, F.smul_right, hww, mul_zero, add_zero, hu]
    have hew : F.β e w = 1 := by rw [unitaryForm_symm hK w e, hwe, map_one]
    obtain ⟨h, hh⟩ := htrans e hee c₀ hc₀σ
    refine ⟨h, w, hwW, fun hmem => ?_⟩
    rw [hh, hew, mul_one] at hmem
    have hc : c₀ • e ∈ W := by simpa using sub_mem hmem hwW
    have heW : e ∈ W := (Submodule.smul_mem_iff W hc₀).mp hc
    have : F.β w e = 0 := hWiso heW w hwW
    rw [hwe] at this
    exact one_ne_zero this
  ·
    intro R _ _
    obtain ⟨X, m, hX0, hXmono, hXiso, hXrank, hXstable, hrefine, hmax⟩ :=
      exists_isotropicChain_refining F (isoSeq F ρ R) (isoSeq_zero F ρ R) (isoSeq_mono F ρ R)
        (isoSeq_isTotallyIsotropic F ρ R)
    have hU'p : IsPGroup p (flagKernel ρ (isoCompletion F X m)) :=
      isPGroup_flagKernel ρ p hinj (isoCompletion_zero hX0 m) (isoCompletion_top hX0 m)
    refine exists_sylow_normalizer_le_of_isotropicChain F ρ p hρ R X m m le_rfl hX0 hXmono
      hXiso hXrank hXstable hrefine (flagKernel ρ (isoCompletion F X m)) hU'p ?_ ?_ ?_ ?_
    · refine (flagKernel_le_flagStab ρ _).trans (flagStab_le_flagStab ρ fun k => ?_)
      refine ⟨min k m, ?_⟩
      rw [isoCompletion_of_le (min_le_right k m)]
      rcases le_total k m with hkm | hkm
      · rw [min_eq_left hkm]
      · rw [min_eq_right hkm, hXstable k hkm]
    ·
      intro k hk v hv hfix
      by_contra hvX
      have hlt : X k < X (k + 1) := by
        refine lt_of_le_of_ne (hXmono (Nat.le_succ k)) fun h => ?_
        have := hXrank (k + 1) (by omega)
        rw [← h, hXrank k (by omega)] at this
        omega
      obtain ⟨x, hx, hxk⟩ := IsConcreteLE.exists_of_lt hlt
      have hxx : F.β x x = 0 := hXiso (k + 1) hx x hx
      have hXk1 : X (k + 1) = X k ⊔ K ∙ x := by
        refine (Submodule.eq_of_le_of_finrank_eq
          (sup_le (hXmono (Nat.le_succ k)) ((Submodule.span_singleton_le_iff_mem _ _).mpr hx))
          ?_).symm
        rw [Submodule.finrank_sup_span_singleton hxk, hXrank k (by omega),
          hXrank (k + 1) (by omega)]
      by_cases hxv : F.β x v = 0
      ·
        have hvperp : v ∈ F.perp (X (k + 1)) := by
          rw [hXk1, F.perp_sup]
          exact ⟨hv, (F.mem_perp_span_singleton).mpr hxv⟩
        obtain ⟨y, hy, hyv⟩ : ∃ y ∈ F.perp (X (k + 1)), F.β y v ≠ 0 := by
          by_contra! h
          apply hvX
          have hpp : v ∈ F.perp (F.perp (X (k + 1))) := fun y hy => h y hy
          rwa [F.perp_perp] at hpp
        have hxy : F.β x y = 0 := hy x hx
        obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hK (a := -F.β y y)
          (by rw [map_neg, hββ])
        obtain ⟨h, hh⟩ := heich x y hxx hxy c hc
        have hmem : h ∈ flagKernel ρ (isoCompletion F X m) := by
          refine mem_flagKernel_isoCompletion ρ hXmono hXiso hk hx hy
            (a := y + c • x) ?_ (-1) fun w => ?_
          · exact add_mem hy (Submodule.smul_mem _ _ (hXiso (k + 1) hx))
          · rw [hh]
            simp only [neg_one_mul, neg_smul, sub_eq_add_neg]
        have := hfix h hmem
        rw [hh, hxv, zero_smul, add_zero, sub_sub_cancel_left] at this
        rw [← neg_smul, Submodule.smul_mem_iff _ (neg_ne_zero.mpr hyv)] at this
        exact hxk this
      ·
        obtain ⟨h, hh⟩ := htrans x hxx c₀ hc₀σ
        have hmem : h ∈ flagKernel ρ (isoCompletion F X m) := by
          refine mem_flagKernel_isoCompletion ρ hXmono hXiso hk hx (hXiso (k + 1) hx)
            (a := c₀ • x) (Submodule.smul_mem _ _ (hXiso (k + 1) hx)) 0 fun w => ?_
          rw [hh, zero_mul, zero_smul, add_zero, smul_smul, mul_comm]
        have := hfix h hmem
        rw [hh, add_sub_cancel_left,
          Submodule.smul_mem_iff _ (mul_ne_zero hc₀ hxv)] at this
        exact hxk this
    ·
      intro S hS hSstab g hg v hv
      exact triv_of_anisotropic F ρ p hρ (hXiso m) hmax S hS
        (fun g hg w hw => (hSstab hg 0 w hw).1) g hg v hv
    · intro S _ k hk1 hk2
      omega

theorem holds_statedProj_statedSU (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    Holds (StatedProj (StatedSU n (p ^ f) K)) p :=
  Holds.statedProj _ (holds_statedSU hK n)

end CFSG.LieType.BorelTits
