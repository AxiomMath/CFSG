module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpStruct
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Class
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneMinus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpTwist
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpAlg
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem mp_det_d4PermMat_add (q : ℤ) :
    Matrix.det !![q, 0, 0, 1; 1, q, 0, 0; 0, 0, q + 1, 0; 0, 1, 0, q] =
      (q + 1) * (q ^ 3 + 1) := by
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem mp_d4PermMat_add_det_ne_zero {q : ℕ} (hq : 1 ≤ q) :
    ((q : ℤ) • (1 : D4Mat) - -d4PermMat).det ≠ 0 := by
  have hM : ((q : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) -
      -!![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]) =
      !![(q : ℤ), 0, 0, 1; 1, q, 0, 0; 0, 0, q + 1, 0; 0, 1, 0, q] := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply]
    fin_cases i <;> fin_cases j <;> simp
  have hdet : ((q : ℤ) • (1 : D4Mat) - -d4PermMat).det = ((q : ℤ) + 1) * ((q : ℤ) ^ 3 + 1) := by
    rw [← mp_det_d4PermMat_add (q : ℤ), ← hM]
    rfl
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have h1 : (0 : ℤ) < (q : ℤ) + 1 := by omega
  have h2 : (0 : ℤ) < (q : ℤ) ^ 3 + 1 := by positivity
  rw [hdet]
  exact (mul_pos h1 h2).ne'

theorem mp_class_witness {W w₀ : WeylGroup TwistTag.D4.tag}
    (hw₀ : ∀ x : Fin TwistTag.D4.tag.rank → ℤ, w₀ • x = -x)
    (hW : (∀ x, W • x = d4MatThreeA *ᵥ x) ∨ (∀ x, W • x = d4MatThreeB *ᵥ x)) :
    ∃ u : WeylGroup TwistTag.D4.tag, ∀ x,
      (u * (W⁻¹ * w₀) * (weylTwist TwistTag.D4 u)⁻¹) • x =
        d4T36M (-1) *ᵥ permLattice TwistTag.D4.perm.symm x := by
  obtain ⟨u, hu⟩ := q1_class_witness hW
  refine ⟨u, fun x => ?_⟩
  have h1 : (u * (W⁻¹ * w₀) * (weylTwist TwistTag.D4 u)⁻¹) • x =
      -((u * W⁻¹ * (weylTwist TwistTag.D4 u)⁻¹) • x) := by
    simp only [mul_smul, hw₀, smul_neg]
  rw [h1, hu x]
  have h2 : d4T36M (-1) = -d4T36M 1 := by simp [d4T36M]
  rw [h2, Matrix.neg_mulVec]

theorem mp_torus_of_toral_zeta {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L p] {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {y₁ ζ : ModGL TwistTag.D4.tag L} (hy₁ : y₁ ∈ adjointGroup TwistTag.D4.tag L)
    (hζdef : ζ = trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) y₁ *
      (trialityOpposition L)⁻¹ * y₁⁻¹)
    (hyE : ∀ e ∈ E', y₁ * d4MinusPsi σ L g₀ e * y₁⁻¹ ∈ torusGroup TwistTag.D4.tag L)
    (hζ : ζ ∈ torusGroup TwistTag.D4.tag L) :
    ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ e ∈ E',
      d4MinusPsi σ L g₀ (c * e * c⁻¹) ∈ twistedTorusOf (trialityOpposition L)
        (twistHom TwistTag.D4 L (iterateFrobenius L p f)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hg₀' := hg₀
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := hg₀'
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  set F := twistHom TwistTag.D4 L Fr with hF
  set z₀ : ModGL TwistTag.D4.tag L := trialityOpposition L with hz₀
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  have hM : ∀ x, weylQuotientHom TwistTag.D4.tag L
      ⟨z₀, trialityOpposition_mem_monomialSubgroup⟩ • x =
        (-d4PermMat) *ᵥ permLattice TwistTag.D4.perm.symm x := by
    intro x
    rw [weylQuotientHom_trialityOpposition_smul, permLattice_symm_d4_eq, Matrix.mulVec_mulVec,
      Matrix.neg_mul, d4PermMat_mul, Matrix.neg_mulVec, Matrix.one_mulVec]
  obtain ⟨s, hs, hsF⟩ := d4_torus_adjust Fr hFr trialityOpposition_mem_monomialSubgroup
    (-d4PermMat) hM
    (mp_d4PermMat_add_det_ne_zero (q := p ^ f) (Nat.one_le_pow _ _ hp.pos)) (inv_mem hζ)
  have hy₂F : z₀ * F (s * y₁) * z₀⁻¹ = s * y₁ := by
    have h1 : z₀ * F y₁ * z₀⁻¹ = ζ * y₁ := by
      rw [hζdef]
      group
    calc z₀ * F (s * y₁) * z₀⁻¹ = (z₀ * F s * z₀⁻¹) * (z₀ * F y₁ * z₀⁻¹) := by
          rw [map_mul]
          group
      _ = (s * ζ⁻¹) * (ζ * y₁) := by rw [hsF, h1]
      _ = s * y₁ := by group
  have hsC : s ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' (torusGroup_le_monomialSubgroup hs)
  obtain ⟨c, hc⟩ := (hrange (s * y₁)).2 ⟨mul_mem hsC hy₁, hy₂F⟩
  refine ⟨c, fun e he => ?_⟩
  have hψc : ψ (c * e * c⁻¹) = s * (y₁ * ψ e * y₁⁻¹) * s⁻¹ := by
    rw [map_mul, map_mul, map_inv, hc]
    group
  have hfix : z₀ * F (ψ (c * e * c⁻¹)) * z₀⁻¹ = ψ (c * e * c⁻¹) :=
    ((hrange _).1 ⟨_, rfl⟩).2
  refine mem_twistedTorusOf.2 ⟨?_, hfix⟩
  rw [hψc]
  exact mul_mem (mul_mem hs (hyE e he)) (inv_mem hs)

theorem mp_toral_data {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgen : ∀ x ∈ E', ∃ i j : ℤ, x = v ^ i * n ^ j)
    (hv : d4MinusPsi σ L g₀ v ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1) (hn3 : n ^ 3 = 1) (hnv : n * v = v * n)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L) :
    ∃ y₁ ζ : ModGL TwistTag.D4.tag L, y₁ ∈ rootSpan TwistTag.D4.tag L d4LongA2 ∧
      ζ = trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) y₁ *
        (trialityOpposition L)⁻¹ * y₁⁻¹ ∧
      (∀ e ∈ E', y₁ * d4MinusPsi σ L g₀ e * y₁⁻¹ ∈ torusGroup TwistTag.D4.tag L) ∧
      ∃ hζ : ζ ∈ monomialSubgroup TwistTag.D4.tag L,
        (weylQuotientHom TwistTag.D4.tag L ⟨ζ, hζ⟩ = 1 ∧ ζ ∈ torusGroup TwistTag.D4.tag L) ∨
        (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hζ⟩ • x = d4MatThreeA *ᵥ x) ∨
        ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hζ⟩ • x = d4MatThreeB *ᵥ x := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : PerfectRing L p := IsAlgClosed.perfectRing L p
  have hg₀' := hg₀
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := hg₀'
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  obtain ⟨A, hA3, hA1, hψv⟩ := d4Minus_fixed_line_inner hp hp2 hp3 hf hq K hK σ hσ L hg₀ v n hv
    hv1 hv3 hnM hnT hn3 (by rw [hnv]; group)
  set d : ModGL TwistTag.D4.tag L :=
    rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) with hd
  have hνC : ψ n ∈ adjointGroup TwistTag.D4.tag L := d4MinusPsi_mem_adjointGroup hg₀C n
  have hν3 : (ψ n) ^ 3 = 1 := by rw [← map_pow, hn3, map_one]
  have hcommν : ψ n * d = d * ψ n := by
    rw [← hψv, ← map_mul, ← map_mul, hnv]
  obtain ⟨Y, hY, a, hYa, hreg⟩ := d4_toral_conj_A2 hA3 hA1 hnM hνC hν3 hnT hcommν
  set y₁ : ModGL TwistTag.D4.tag L := Y⁻¹ with hydef
  have hy₁ : y₁ ∈ rootSpan TwistTag.D4.tag L d4LongA2 := inv_mem hY
  have hya : y₁ * ψ n * y₁⁻¹ = rootDiagUnit TwistTag.D4.tag a := by
    rw [hydef, inv_inv]
    exact hYa
  have hFν : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n := ((hrange (ψ n)).1 ⟨n, rfl⟩).2
  obtain ⟨b, hζmem, hζb, hsame⟩ := mp_F2_data hq hy₁ hya (fun α hα => (hreg α hα).2) hFν
  obtain ⟨hζM, hcls, hztor⟩ := d4_A2_conj_monomial _ hζmem a b hreg hsame hζb
  have hcent : y₁ * d = d * y₁ := by
    have h := rootSpan_le_centralizer (τ := TwistTag.D4.tag) (K := L)
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) (S := d4LongA2)
      (fun α hα => (d4Minus_rootCharKernel hA3 hA1 α).2 hα) hy₁
    exact Subgroup.mem_centralizer_singleton_iff.1 h
  have hconjd : y₁ * d * y₁⁻¹ = d := by
    rw [hcent]
    group
  have hyE : ∀ e ∈ E', y₁ * ψ e * y₁⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    intro e he
    obtain ⟨i, j, rfl⟩ := hgen e he
    have h1 : y₁ * ψ (v ^ i * n ^ j) * y₁⁻¹ =
        (y₁ * d * y₁⁻¹) ^ i * (y₁ * ψ n * y₁⁻¹) ^ j := by
      have := map_mul (MulAut.conj y₁) (d ^ i) (ψ n ^ j)
      rw [map_zpow, map_zpow] at this
      simp only [MulAut.conj_apply] at this
      rw [map_mul, map_zpow, map_zpow, hψv]
      exact this
    rw [h1, hconjd, hya]
    exact mul_mem (zpow_mem (rootDiagUnit_mem_torusGroup _) i)
      (zpow_mem (rootDiagUnit_mem_torusGroup _) j)
  refine ⟨y₁, _, hy₁, rfl, hyE, hζM, ?_⟩
  rcases hcls with h1 | hA | hB
  · exact Or.inl ⟨h1, hztor.2 h1⟩
  · exact Or.inr (Or.inl hA)
  · exact Or.inr (Or.inr hB)

theorem mp_frames_of_data {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE'3 : ∀ e ∈ E', e ^ 3 = 1)
    {g₀ y₁ ζ : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hg₀F : twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f)
      g₀ = g₀ * trialityOpposition (AlgebraicClosure K))
    (hy₁C : y₁ ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hζdef : ζ = trialityOpposition (AlgebraicClosure K) *
      twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f) y₁ *
        (trialityOpposition (AlgebraicClosure K))⁻¹ * y₁⁻¹)
    (hζM : ζ ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K))
    (hyE : ∀ e ∈ E', y₁ * d4MinusPsi σ (AlgebraicClosure K) g₀ e * y₁⁻¹ ∈
      torusGroup TwistTag.D4.tag (AlgebraicClosure K))
    (hW : (∀ x, weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨ζ, hζM⟩ • x =
        d4MatThreeA *ᵥ x) ∨
      ∀ x, weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨ζ, hζM⟩ • x =
        d4MatThreeB *ᵥ x) :
    (∃ F : D4PhiFrame K σ (p ^ f) (-1), F.Contains E') ∧
      ∃ F : D4SteinbergFrame K σ (p ^ f) (-1), F.Contains E' := by
  classical
  have hz₀M : trialityOpposition (AlgebraicClosure K) ∈
      monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K) :=
    trialityOpposition_mem_monomialSubgroup
  have hyC : y₁ * g₀⁻¹ ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) :=
    mul_mem hy₁C (inv_mem hg₀C)
  have hzM : (trialityOpposition (AlgebraicClosure K))⁻¹ * ζ ∈
      monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K) := mul_mem (inv_mem hz₀M) hζM
  have hFy : twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f)
      (y₁ * g₀⁻¹) = (trialityOpposition (AlgebraicClosure K))⁻¹ * ζ * (y₁ * g₀⁻¹) := by
    rw [hζdef, map_mul, map_inv, hg₀F]
    group
  have hyE' : ∀ e ∈ E', y₁ * g₀⁻¹ * triEmb K σ (AlgebraicClosure K) e * (y₁ * g₀⁻¹)⁻¹ ∈
      torusGroup TwistTag.D4.tag (AlgebraicClosure K) := by
    intro e he
    have h := hyE e he
    rw [d4MinusPsi_apply] at h
    have e1 : y₁ * g₀⁻¹ * triEmb K σ (AlgebraicClosure K) e * (y₁ * g₀⁻¹)⁻¹ =
        y₁ * (g₀⁻¹ * triEmb K σ (AlgebraicClosure K) e * g₀) * y₁⁻¹ := by group
    rw [e1]
    exact h
  have hπ : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)
      ⟨((trialityOpposition (AlgebraicClosure K))⁻¹ * ζ)⁻¹, inv_mem hzM⟩ =
        (weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨ζ, hζM⟩)⁻¹ *
          weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)
            ⟨trialityOpposition (AlgebraicClosure K), hz₀M⟩ := by
    have e : (⟨((trialityOpposition (AlgebraicClosure K))⁻¹ * ζ)⁻¹, inv_mem hzM⟩ :
        monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)) =
        (⟨ζ, hζM⟩ : monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K))⁻¹ *
          ⟨trialityOpposition (AlgebraicClosure K), hz₀M⟩ := by
      apply Subtype.ext
      change ((trialityOpposition (AlgebraicClosure K))⁻¹ * ζ)⁻¹ =
        ζ⁻¹ * trialityOpposition (AlgebraicClosure K)
      rw [mul_inv_rev, inv_inv]
    rw [e, map_mul, map_inv]
  obtain ⟨u, hu⟩ := mp_class_witness
    (W := weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨ζ, hζM⟩)
    (w₀ := weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)
      ⟨trialityOpposition (AlgebraicClosure K), hz₀M⟩)
    (fun x => weylQuotientHom_trialityOpposition_smul x) hW
  have hu' : ∀ x, (u * weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K)
      ⟨((trialityOpposition (AlgebraicClosure K))⁻¹ * ζ)⁻¹, inv_mem hzM⟩ *
        (weylTwist TwistTag.D4 u)⁻¹) • x =
          d4T36M (-1) *ᵥ permLattice TwistTag.D4.perm.symm x := fun x => by
    rw [hπ]
    exact hu x
  exact ⟨d4PhiFrame_of_toral hf K hK σ hσ E' hyC hzM hFy hyE' u hu',
    d4SteinbergFrame_of_toral K σ hσ (Or.inr rfl) E' hE'3 hyC hzM hFy hyE' u hu'⟩

theorem d4Minus_plane_dichotomy {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2) :
    D4PlaneInTorusMinus p f hp K σ E ∨
      ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (∃ F : D4PhiFrame K σ (p ^ f) (-1), F.Contains (E.map (β⁻¹).toMonoidHom)) ∧
        ∃ F : D4SteinbergFrame K σ (p ^ f) (-1), F.Contains (E.map (β⁻¹).toMonoidHom) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := by
    have : Fintype K := Fintype.ofFinite K
    have h : Fintype.card K = p ^ (f * 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
    exact charP_of_card_eq_prime_pow h
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨g₀, hg₀C, hg₀P, hg₀F⟩ := d4Minus_exists_frame (L := AlgebraicClosure K) p hp2 hf
  have hg₀ : D4MinusFrame p f (AlgebraicClosure K) g₀ := ⟨hg₀C, hg₀P, hg₀F⟩
  have hinTorus : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ e ∈ E, d4MinusPsi σ (AlgebraicClosure K) g₀ (β⁻¹ e) ∈
        twistedTorusOf (trialityOpposition (AlgebraicClosure K))
          (twistHom TwistTag.D4 (AlgebraicClosure K)
            (iterateFrobenius (AlgebraicClosure K) p f))) → D4PlaneInTorusMinus p f hp K σ E := by
    intro β hβ
    refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, inferInstance, g₀, hg₀,
      β, fun e he => ?_⟩
    have h := hβ e he
    rwa [d4MinusPsi_apply] at h
  rcases mp_plane_data_or hf hq K hK σ hσ (AlgebraicClosure K) hg₀ E hE hEcard with
    ⟨β, hβ⟩ | ⟨β, v, n, hgen, hv, hv1, hv3, hn3, hnv, hnM, hnT⟩
  · exact Or.inl (hinTorus β hβ)
  · have := hE
    have hE'ea : IsElementaryAbelian 3 (E.map (β⁻¹).toMonoidHom) :=
      IsElementaryAbelian.map (β⁻¹).toMonoidHom
    have hE'3 : ∀ e ∈ E.map (β⁻¹).toMonoidHom, e ^ 3 = 1 := fun e he =>
      elemPow_eq_one_of_isElementaryAbelian e he
    obtain ⟨y₁, ζ, hy₁, hζdef, hyE, hζM, hcase⟩ := mp_toral_data hp hp2 hp3 hf hq K hK σ hσ
      (AlgebraicClosure K) hg₀ (E.map (β⁻¹).toMonoidHom) v n hgen hv hv1 hv3 hn3 hnv hnM hnT
    have hy₁C : y₁ ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) :=
      rootSpan_le_adjointGroup _ d4LongA2 hy₁
    rcases hcase with ⟨-, hζT⟩ | hW
    · left
      obtain ⟨c, hc⟩ := mp_torus_of_toral_zeta hp hf K hK σ hσ (AlgebraicClosure K) hg₀
        (E.map (β⁻¹).toMonoidHom) hy₁C hζdef hyE hζT
      refine hinTorus (MulAut.conj c * β⁻¹)⁻¹ (fun e he => ?_)
      rw [inv_inv, MulAut.mul_apply, MulAut.conj_apply]
      exact hc _ ⟨e, he, rfl⟩
    · right
      exact ⟨β, mp_frames_of_data hf K hK σ hσ _ hE'3 hg₀C hg₀F hy₁C hζdef hζM hyE hW⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
