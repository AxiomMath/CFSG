module

public import CFSG.ClassicalInvolution.RouteD.TriageSU4Torus
public import CFSG.ClassicalInvolution.RouteD.AllA1

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_norm_one_pow_four (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    ∃ l : K, unitaryInvolution K p f l * l = 1 ∧ l ^ 4 ≠ 1 := by
  obtain ⟨l, hl, hord⟩ := exists_norm_one_orderOf_eq (F := K) (p := p) (f := f) hK
  refine ⟨l, hl, fun h => ?_⟩
  have h1 : (l : Kˣ) ^ 4 = 1 := Units.ext (by simpa using h)
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem su4TorusElt_comm_blockEmb (l : K) (hl : unitaryInvolution K p f l * l = 1)
    (A : Su K p f 2) :
    blockEmb K p f 4 2 0 (by omega) A * su4TorusElt K p f l hl =
      su4TorusElt K p f l hl * blockEmb K p f 4 2 0 (by omega) A := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_su4TorusElt, suMat_blockEmb, blockMat_zero_eq_BD, BD_mul,
    BD_mul]
  simp

theorem su4TorusElt_comm_of_comm_block (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (l : K) (hl : unitaryInvolution K p f l * l = 1) (g : Su K p f 4)
    (hg : ∀ A : Su K p f 2, g * blockEmb K p f 4 2 0 (by omega) A =
      blockEmb K p f 4 2 0 (by omega) A * g) :
    g * su4TorusElt K p f l hl = su4TorusElt K p f l hl * g := by
  apply suMat_injective
  have h := commutant_blockSu2 hK hp2 hq (suMat g) fun A => by
    have := congrArg suMat (hg A)
    rw [suMat_mul, suMat_mul, suMat_blockEmb] at this
    exact this
  rw [suMat_mul, suMat_mul, suMat_su4TorusElt, h, BD_mul, BD_mul]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem exists_blockEmb_not_central (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) :
    ∃ A : Su K p f 2, blockEmb K p f 4 2 0 (by omega) A ∉ Subgroup.center (Su K p f 4) := by
  obtain ⟨u, hu, hne⟩ := exists_norm_one_ne hK hp2 hq
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hu' : u * σ u = 1 := by rw [mul_comm]; exact hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    simp
  have hdet1 : (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp [hu']
  have hiso1 : conjTr σ (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) *
      (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσσ, hu, hu']
  refine ⟨mkSU K p f _ hdet1 hiso1, fun hc => ?_⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨s, hs⟩ : ∃ s : K, suMat (blockEmb K p f 4 2 0 (by omega) (mkSU K p f _ hdet1 hiso1)) =
      s • (1 : Matrix (Fin 4) (Fin 4) K) := by
    refine eq_smul_one_of_commute hUF hp2 (by norm_num : 3 ≤ 4) _ fun y hy => ?_
    have hy' : y ∈ SUid σ 4 := by rw [SUid_eq_statedSU hK]; exact hy
    have h6 := congrArg suMat (Subgroup.mem_center_iff.mp hc ⟨y, hy'⟩)
    rw [suMat_mul, suMat_mul] at h6
    exact h6.symm
  have e00 := congrFun (congrFun hs 0) 0
  have e33 := congrFun (congrFun hs 3) 3
  rw [suMat_blockEmb, suMat_mkSU] at e00 e33
  simp [blockMat_apply] at e00 e33
  exact hu1 (e00.trans e33.symm)

end Torus

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_torus_lift {a : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {z : G} (hP1 : LocalOddCentral Ω {z})
    (Λ : SuLayer p f a Ω z) {K₂ : Subgroup G}
    {g₁ : Su (GaloisField p (2 * f)) p f 4}
    (hg₁ : locImg Ω z K₂ = ((rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map
      (MulAut.conj g₁).toMonoidHom).map (Λ.ψ hp2))
    (l : GaloisField p (2 * f))
    (hl : unitaryInvolution (GaloisField p (2 * f)) p f l * l = 1) (y : ↥(locLayer Ω z))
    (hy : locMk Ω z y = Λ.ψ hp2 (g₁ * su4TorusElt (GaloisField p (2 * f)) p f l hl * g₁⁻¹))
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z}) (hNK₂ : N = K₂ ∨ Commutes N K₂) :
    N ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
  have hK := card_galoisField_two_mul_eq (p := p) hq
  have h4 : 4 ≤ Nat.card (fixedSubfield (GaloisField p (2 * f)) p f) := by
    rw [card_fixedSubfield hK]; omega
  set ψ := Λ.ψ hp2 with hψ
  have hker := (Λ.ψ_spec hp2).1
  have hrange := (Λ.ψ_spec hp2).2.1
  set T := su4TorusElt (GaloisField p (2 * f)) p f l hl with hT
  rw [le_centralizer_iff_locImg hΩ hP1 hN y, hy]
  obtain ⟨m, hm⟩ := exists_range_of_mem Λ.D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  by_cases hmi : m = Λ.i₁
  · subst hmi
    obtain ⟨R, hR, hNR⟩ := Λ.exists_longRoot_of_mem hp2 hΩ hP1 hN hm
    obtain ⟨i, hi⟩ := hR
    have hperfR : Group.IsPerfect ↥R := (hi.isClassicalSL2 hK hp2).isPerfect h4
    set R₀' := (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map
      (MulAut.conj g₁).toMonoidHom with hR₀'
    have hls : IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) R₀'
        (g₁ * rootInvSU (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4) * g₁⁻¹) :=
      ⟨g₁, rfl, rfl⟩
    have hperfR₀' : Group.IsPerfect ↥R₀' := (hls.isClassicalSL2 hK hp2).isPerfect h4
    have hcomm : ∀ r ∈ R, r * (g₁ * T * g₁⁻¹) = (g₁ * T * g₁⁻¹) * r := by
      intro r hr
      have key : (g₁⁻¹ * r * g₁) * T = T * (g₁⁻¹ * r * g₁) := by
        rcases hNK₂ with rfl | hc
        · have hRR : R = R₀' := by
            apply eq_of_map_eq_of_central ψ hker (Subgroup.isPerfect_iff.mp hperfR).ge
              (Subgroup.isPerfect_iff.mp hperfR₀').ge
            rw [← hNR, hg₁]
          rw [hRR] at hr
          obtain ⟨s, hs, rfl⟩ := hr
          obtain ⟨A, rfl⟩ := hs
          have e : g₁⁻¹ * (MulAut.conj g₁).toMonoidHom (blockEmb (GaloisField p (2 * f)) p f 4 2 0
              (by omega) A) * g₁ = blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by omega) A := by
            simp [MulAut.conj_apply]
            group
          rw [e]
          exact su4TorusElt_comm_blockEmb l hl A
        · apply su4TorusElt_comm_of_comm_block hK hp2 hq l hl
          intro A
          have hc' : Commutes (locImg Ω z N) (locImg Ω z K₂) := commutes_locImg_of_commutes hc
          rw [hNR, hg₁] at hc'
          have hcR : Commutes R R₀' :=
            commutes_of_commutes_map ψ hker hperfR hc'
          have hs : (MulAut.conj g₁).toMonoidHom (blockEmb (GaloisField p (2 * f)) p f 4 2 0
              (by omega) A) ∈ R₀' := ⟨_, ⟨A, rfl⟩, rfl⟩
          have h1 := hcR r hr _ hs
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
          calc (g₁⁻¹ * r * g₁) * blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by omega) A
              = g₁⁻¹ * (r * (g₁ * blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by omega) A *
                  g₁⁻¹)) * g₁ := by group
            _ = g₁⁻¹ * ((g₁ * blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by omega) A *
                  g₁⁻¹) * r) * g₁ := by rw [h1]
            _ = blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by omega) A * (g₁⁻¹ * r * g₁) := by
                group
      calc r * (g₁ * T * g₁⁻¹) = g₁ * ((g₁⁻¹ * r * g₁) * T) * g₁⁻¹ := by group
        _ = g₁ * (T * (g₁⁻¹ * r * g₁)) * g₁⁻¹ := by rw [key]
        _ = (g₁ * T * g₁⁻¹) * r := by group
    rw [hNR]
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcomm r hr]
  · intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : ψ (g₁ * T * g₁⁻¹) ∈ (Λ.D.hom Λ.i₁).range := by
      rw [← hrange]; exact ⟨_, rfl⟩
    exact range_commute_of_ne Λ.D hmi _ (hm ha) _ hmem

section Twin

variable {Ω : Set (Subgroup G)} {x : G}

theorem exists_twin_su (hΩ : InClass p f Ω) (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (Λ : SuLayer p f 2 Ω x) {B : Subgroup G} (hB : B ∈ Ω)
    (hz : IsClassicalMember p f B x) :
    ∃ T ∈ centralizingMembers Ω {x}, T ≠ B ∧
      (∀ N ∈ centralizingMembers Ω {x}, N ≠ T → Commutes T N) ∧
      ∃ j, j ≠ Λ.i₁ ∧ locImg Ω x T ≤ (Λ.D.hom j).range := by
  have hBx : B ∈ centralizingMembers Ω {x} := ⟨hB, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨j₀, hj₀, hBj₀⟩ := Λ.exists_other_of_self hp2 hq hB hz
  obtain ⟨a₀, a₂, h0, h2, h02, hall⟩ := exists_three_indices (c := Λ.D.card) Λ.card_eq Λ.i₁
  obtain ⟨j', hj'₁, hj'₀⟩ : ∃ j', j' ≠ Λ.i₁ ∧ j' ≠ j₀ := by
    rcases hall j₀ with h | h | h
    · exact ⟨a₂, h2, fun e => h02 (h.symm.trans e.symm)⟩
    · exact absurd h hj₀
    · exact ⟨a₀, h0, fun e => h02 (e.trans h)⟩
  obtain ⟨hj'tag, hj'rank⟩ := Λ.rest j' hj'₁
  obtain ⟨T, hT, hTimg⟩ := mem_locFamily_iff.mp (range_mem_of_A1 Λ.D j' hj'tag hj'rank)
  have hTj' : locImg Ω x T ≤ (Λ.D.hom j').range := hTimg.le
  have hTB : T ≠ B := by
    rintro rfl
    exact hj'₀ (eq_of_locImg_le_range hΩ hex Λ.D hT hTj' hBj₀)
  refine ⟨T, hT, hTB, ?_, j', hj'₁, hTj'⟩
  intro N hN hNT
  obtain ⟨m, hm⟩ := exists_range_of_mem Λ.D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  by_cases hmj : m = j'
  · subst hmj
    exfalso
    apply hNT
    have e1 : locImg Ω x N = (Λ.D.hom m).range :=
      Subgroup.eq_of_le_of_card_ge hm (by
        rw [card_locImg hΩ hex hN]
        exact card_range_le_of_psl_two Λ.D m hj'tag hj'rank)
    exact locImg_injOn hΩ hP1 hN hT (e1.trans hTimg.symm)
  · exact commutes_of_ne_comp hΩ hP1 Λ.D (Ne.symm hmj) ⟨hT, hTj'⟩ ⟨hN, hm⟩

end Twin

end Layer

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
