module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.G2PlusEven

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.SEITZ3 CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartOne.SEITZ11.G2Seven

theorem padicValNat_ordG2_of_dvd_add_one {p q : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : p ∣ q + 1) : padicValNat p (CFSG.Open.ordG2 q) = 2 * padicValNat p (q + 1) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hA : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hq1, hq2]
    ring
  have hB : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
    zify [hq2, hq6]
    ring
  have n6 : q ^ 6 ≠ 0 := pow_ne_zero _ (by omega)
  have n2 : q ^ 2 - 1 ≠ 0 := by
    have h4 : 4 ≤ q ^ 2 := by nlinarith
    omega
  have n4 : q ^ 4 + q ^ 2 + 1 ≠ 0 := by positivity
  have hpq1 : ¬ p ∣ q - 1 := by
    intro h
    have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq h
    have : (q + 1) - (q - 1) = 2 := by omega
    rw [this] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hpq0 : ¬ p ∣ q := by
    intro h
    have h2 : p ∣ (q + 1) - q := Nat.dvd_sub hpq h
    have : (q + 1) - q = 1 := by omega
    rw [this] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hquart : ¬ p ∣ q ^ 4 + q ^ 2 + 1 := by
    intro h
    have hq2d : p ∣ q ^ 2 - 1 := by
      rw [hA]; exact Dvd.dvd.mul_right hpq _
    have hid : q ^ 4 + q ^ 2 + 1 = (q ^ 2 - 1) * (q ^ 2 + 2) + 3 := by
      zify [hq2]
      ring
    have h3 : p ∣ 3 := by
      have h' : p ∣ (q ^ 2 - 1) * (q ^ 2 + 2) + 3 := hid ▸ h
      exact (Nat.dvd_add_right (Dvd.dvd.mul_right hq2d _)).1 h'
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have v_six : padicValNat p (q ^ 6) = 0 := by
    rw [padicValNat.pow q 6, padicValNat.eq_zero_of_not_dvd hpq0, mul_zero]
  have v_sub : padicValNat p (q ^ 2 - 1) = padicValNat p (q + 1) := by
    rw [hA, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd hpq1, add_zero]
  have v_quart : padicValNat p (q ^ 4 + q ^ 2 + 1) = 0 := padicValNat.eq_zero_of_not_dvd hquart
  have nB : (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) ≠ 0 := mul_ne_zero n2 n4
  rw [CFSG.Open.ordG2, hB, padicValNat.mul (mul_ne_zero n6 nB) n2,
    padicValNat.mul n6 nB, padicValNat.mul n2 n4, v_six, v_sub, v_quart]
  ring

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem finite_adjointGroup_G2' : Finite (adjointGroup .G2 K) := by
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  infer_instance

theorem QPlusModel.natCard_torusG (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    Nat.card ((torusTorsion K₂ (Nat.card K + 1)).comap (twistEmb (K := K) M.g)) =
      (Nat.card K + 1) ^ 2 := by
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd : Nat.card K + 1 ∣ Nat.card K₂ - 1 := ⟨Nat.card K - 1, by
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring⟩
  have hT : torusTorsion K₂ (Nat.card K + 1) ≤ M.gamma := by
    intro t ht
    have := ht
    rw [← M.torus_inf_gamma hσ] at this
    exact this.2
  have hmap : ((torusTorsion K₂ (Nat.card K + 1)).comap (twistEmb (K := K) M.g)).map
      (twistEmb (K := K) M.g) = torusTorsion K₂ (Nat.card K + 1) := by
    rw [Subgroup.map_comap_eq]
    apply inf_eq_right.2
    intro t ht
    obtain ⟨x, hx⟩ := M.exists_twistEmb_eq (hT ht)
    exact ⟨x, hx⟩
  rw [← Subgroup.card_map_of_injective (twistEmb_injective (K := K) M.g), hmap]
  exact natCard_torusTorsion hdvd

theorem QPlusModel.exists_sylow_le_torus (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (hK : 3 ≤ Nat.card K) :
    ∃ P₀ : Sylow p (adjointGroup .G2 K), (P₀ : Subgroup (adjointGroup .G2 K)) ≤
      (torusTorsion K₂ (Nat.card K + 1)).comap (twistEmb (K := K) M.g) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (adjointGroup .G2 K) := finite_adjointGroup_G2'
  set TG := (torusTorsion K₂ (Nat.card K + 1)).comap (twistEmb (K := K) M.g) with hTG
  have hG : Nat.card (adjointGroup .G2 K) =
      Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) :=
    (exact_G2_finite_order K rfl).2.1
  have hv : (Nat.card (adjointGroup .G2 K)).factorization p = 2 * padicValNat p (Nat.card K + 1) := by
    rw [Nat.factorization_def _ hp, hG]
    exact padicValNat_ordG2_of_dvd_add_one hp5 (by omega) hpq
  have hTc : (Nat.card TG).factorization p = 2 * padicValNat p (Nat.card K + 1) := by
    rw [hTG, M.natCard_torusG hdeg hσ, Nat.factorization_def _ hp, padicValNat.pow (Nat.card K + 1) 2]
  have hQ : Nonempty (Sylow p TG) := inferInstance
  obtain ⟨Q⟩ := hQ
  have hQc := Sylow.card_eq_multiplicity Q
  set H : Subgroup (adjointGroup .G2 K) := (Q : Subgroup TG).map TG.subtype with hH
  have hHc : Nat.card H = p ^ (Nat.card (adjointGroup .G2 K)).factorization p := by
    rw [hH, Subgroup.card_map_of_injective TG.subtype_injective, hQc, hTc, hv]
  refine ⟨Sylow.ofCard H hHc, ?_⟩
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_subtype_le _

theorem QPlusModel.closure_cenGen_torsion_eq_top (M : QPlusModel K σ)
    (hdeg : Module.finrank K K₂ = 2) (hσ : ∀ c, σ c = c ^ Nat.card K) (hX : M.X = M.gamma)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    Subgroup.closure (cenGen ((torusTorsion K₂ p).comap (twistEmb (K := K) M.g))) = ⊤ := by
  classical
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have : NeZero p := ⟨hp.ne_zero⟩
  have hTp : torusTorsion K₂ p ≤ M.gamma := by
    intro t ht
    have := torusTorsion_mono hpq ht
    rw [← M.torus_inf_gamma hσ] at this
    exact this.2
  have hcardE : Nat.card (torusTorsion K₂ p) = p ^ 2 := natCard_torusTorsion hdvd
  have hmap : (torsionParams K₂ p).map (rootDiagUnitHom .G2 K₂) = torusTorsion K₂ p := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (rootDiagUnit_mem_torusTorsion_iff p a).2 (funext fun i => by
        simpa using mem_torsionParams.1 ha i)
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (torusTorsion_le_torusGroup p hx)
      refine ⟨a, mem_torsionParams.2 fun i => ?_, rfl⟩
      have := (rootDiagUnit_mem_torusTorsion_iff p a).1 hx
      simpa using congrFun this i
  have hcardA : Nat.card (torsionParams K₂ p) = p ^ 2 := by
    rw [← hcardE, ← hmap]
    exact (Subgroup.card_map_of_injective rootDiagUnit_injective).symm
  set C := Subgroup.closure (cenGen ((torusTorsion K₂ p).comap (twistEmb (K := K) M.g))) with hC
  have hR : ∀ β, IsRoot .G2 β → M.R β ≤ C.map (twistEmb (K := K) M.g) := by
    intro β hβ r hr
    obtain ⟨a, haT, ha1, hachar⟩ := exists_ker hp hcardA β
    have hxT : rootDiagUnit .G2 a ∈ torusTorsion K₂ p := hmap ▸ ⟨a, haT, rfl⟩
    obtain ⟨x, hx⟩ := M.exists_twistEmb_eq (hTp hxT)
    obtain ⟨k, hk⟩ := M.exists_twistEmb_eq (hr.2)
    have hxE : x ∈ (torusTorsion K₂ p).comap (twistEmb (K := K) M.g) := by
      show twistEmb (K := K) M.g x ∈ torusTorsion K₂ p
      rw [hx]; exact hxT
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply ha1
      apply rootDiagUnit_injective (τ := .G2) (K := K₂)
      rw [← hx, map_one, rootDiagUnit_one]
    have hcomm := (M.R_le_centralizer hβ hachar hr).2
    have hkx : k * x = x * k := by
      apply twistEmb_injective (K := K) M.g
      rw [map_mul, map_mul, hk, hx]
      exact Subgroup.mem_centralizer_singleton_iff.1 hcomm
    exact ⟨k, Subgroup.subset_closure ⟨x, hxE, hx1, hkx⟩, hk⟩
  have hXle : M.X ≤ C.map (twistEmb (K := K) M.g) := iSup₂_le fun β hβ => hR β hβ
  rw [eq_top_iff]
  intro g _
  have hg : twistEmb (K := K) M.g g ∈ C.map (twistEmb (K := K) M.g) := by
    apply hXle
    rw [hX]
    exact M.twistEmb_mem_gamma g
  obtain ⟨c, hc, hcg⟩ := hg
  have : c = g := twistEmb_injective (K := K) M.g hcg
  exact this ▸ hc

theorem g2_plane_cenGen_eq_top_even (hmax : MaxSL2SL2G2) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (E₁ : Subgroup (adjointGroup .G2 K)) (hE₁p : ∀ x ∈ E₁, x ^ p = 1) (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (adjointGroup .G2 K) := finite_adjointGroup_G2'
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := K)
  obtain ⟨M⟩ := QPlusModel.nonempty_of_charTwo (K := K) (σ := σ) hdeg hσ
  have hXΓ : M.X = M.gamma := M.X_eq_gamma_of_charTwo' hmax hdeg hσ hK
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd' : Nat.card K + 1 ∣ Nat.card K₂ - 1 := ⟨Nat.card K - 1, by
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring⟩
  set E : Subgroup (adjointGroup .G2 K) :=
    (torusTorsion K₂ p).comap (twistEmb (K := K) M.g) with hE
  have hTp : torusTorsion K₂ p ≤ M.gamma := by
    intro t ht
    have := torusTorsion_mono hpq ht
    rw [← M.torus_inf_gamma hσ] at this
    exact this.2
  have hEc : Nat.card E = p ^ 2 := by
    have hmap : E.map (twistEmb (K := K) M.g) = torusTorsion K₂ p := by
      rw [hE, Subgroup.map_comap_eq]
      apply inf_eq_right.2
      intro t ht
      obtain ⟨x, hx⟩ := M.exists_twistEmb_eq (hTp ht)
      exact ⟨x, hx⟩
    rw [← Subgroup.card_map_of_injective (twistEmb_injective (K := K) M.g), hmap]
    exact natCard_torusTorsion hdvd
  obtain ⟨P₀, hP₀⟩ := M.exists_sylow_le_torus hdeg hσ hp hp5 hpq (by omega)
  obtain ⟨h, hh⟩ := plane_conj P₀ hP₀ (E := E) (fun x hxT hxp => by
    have h1 : twistEmb (K := K) M.g x ∈ torusTorsion K₂ (Nat.card K + 1) := hxT
    have h2 : (twistEmb (K := K) M.g x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
    exact (mem_torusTorsion_iff.2 ⟨(mem_torusTorsion_iff.1 h1).1, h2⟩)) hEc hE₁p hE₁c
  rw [hh, closure_cenGen_cj, M.closure_cenGen_torsion_eq_top hdeg hσ hXΓ hp hpq,
    Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
