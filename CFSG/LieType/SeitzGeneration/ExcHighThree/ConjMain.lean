module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjCore
public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjClass
public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFin
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagLiftConv
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagRegular

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree

section Main


theorem three_dvd_inv_smul_of_fix (w : WeylGroup Tag.E6) (κ : Fin Tag.E6.rank → ℕ)
    (hκ : ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
      (∑ i, (κ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (κ t : ℤ))
    (u : Fin Tag.E6.rank → ℤ) :
    (3 : ℤ) ∣ (∑ i, (κ i : ℤ) * (w⁻¹ • u) i) - ∑ i, (κ i : ℤ) * u i := by
  have hy : ∀ y : Fin Tag.E6.rank → ℤ,
      (3 : ℤ) ∣ (∑ i, (κ i : ℤ) * (w • y) i) - ∑ i, (κ i : ℤ) * y i := by
    intro y
    have e1 : ∑ i, (κ i : ℤ) * (w • y) i =
        ∑ t, y t * ∑ i, (κ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i := by
      simp only [rf_smul_apply w y, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (κ i : ℤ) * y i = ∑ t, y t * (κ t : ℤ) :=
      Finset.sum_congr rfl fun t _ => by ring
    rw [e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun t _ => by
      rw [← mul_sub]
      exact Dvd.dvd.mul_left (hκ t) _
  have h := hy (w⁻¹ • u)
  rw [smul_inv_smul] at h
  omega

@[expose] def E6Pmat (L : Type) [Field L] : ModGL Tag.E6 L := diagramMap TwistTag.E6 L

@[expose] def graphFixed6 (L : Type) [Field L] : Subgroup (ModGL Tag.E6 L) :=
  adjointGroup Tag.E6 L ⊓ Subgroup.centralizer {E6Pmat L}

theorem mem_graphFixed6_iff {L : Type} [Field L] (y : ModGL Tag.E6 L) :
    y ∈ graphFixed6 L ↔ y ∈ adjointGroup Tag.E6 L ∧ E6Pmat L * y * (E6Pmat L)⁻¹ = y := by
  unfold graphFixed6
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff_conj_eq]

theorem diagramMap_conj_diag_of_invFixed {L : Type} [Field L] (ω : Lˣ) (hω3 : ω ^ 3 = 1)
    (v : WeylGroup TwistTag.E6.tag) (k : Fin TwistTag.E6.tag.rank → ℕ)
    (hk : InvFixedZ v (fun j => (k j : ℤ))) :
    diagramMap TwistTag.E6 L *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
          rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) *
        (diagramMap TwistTag.E6 L)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        rootDiagUnit TwistTag.E6.tag (fun i => ω ^ k i) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ := by
  rw [canonicalRep_conj_rootDiagUnit]
  have h1 := diagramMap_mul_rootDiagUnit (t := TwistTag.E6) (K := L)
    (weylTuple v fun i => ω ^ k i)
  rw [h1, mul_inv_cancel_right]
  congr 1
  funext i
  have hinv : ∀ c : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm (TwistTag.E6.perm c) = c := by
    intro c
    revert c
    decide
  have hs : TwistTag.E6.perm.symm i = TwistTag.E6.perm i := by
    rw [Equiv.symm_apply_eq, hinv]
  simp only [weylTuple]
  rw [hs]
  have e1 := rootChar_pow_exp (L := L) ω k
    (v⁻¹ • (Pi.single (TwistTag.E6.perm i) 1 : Fin TwistTag.E6.tag.rank → ℤ))
  have e2 := rootChar_pow_exp (L := L) ω k
    (v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
  exact e1.trans ((zpow_eq_zpow_of_dvd hω3 (hk i)).trans e2.symm)

theorem rootDiagUnit_comm' {τ : Tag} {L : Type} [Field L] (a b : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a * rootDiagUnit τ b = rootDiagUnit τ b * rootDiagUnit τ a := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem mem_graphFixed6_of_baseChange {K L : Type} [Field K] [Field L] (f : K →+* L)
    {y : ModGL Tag.E6 K} (hy : y ∈ adjointGroup Tag.E6 K)
    (hL : baseChangeGL f y ∈ graphFixed6 L) : y ∈ graphFixed6 K := by
  rw [mem_graphFixed6_iff] at hL ⊢
  refine ⟨hy, ?_⟩
  apply baseChangeGL_injective f
  rw [map_mul, map_mul, map_inv]
  have hP : baseChangeGL f (E6Pmat K) = E6Pmat L := baseChangeGL_diagramMap f TwistTag.E6
  rw [hP]
  exact hL.2

theorem exists_fixed_conj_into_graphFixed6 {L : Type} [Field L] [IsAlgClosed L] (p : ℕ)
    [Fact p.Prime] [CharP L p] (e : ℕ) (he : 1 ≤ e) (w v : WeylGroup Tag.E6)
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L p e)) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) L w)
    (hw : weylTwist TwistTag.E6 (v * w * v⁻¹) = v * w * v⁻¹)
    {ι : Type} (d : ι → ModGL Tag.E6 L) (hd : ∀ s, d s ∈ torusGroup Tag.E6 L)
    (hv : ∀ s, E6Pmat L * (canonicalRep (coxeterSystem Tag.E6) L v * d s *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) * (E6Pmat L)⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) L v * d s *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) :
    ∃ h ∈ adjointGroup Tag.E6 L,
      Units.map (entrywiseHom (iterateFrobenius L p e)) h = h ∧
      ∀ s, h⁻¹ * (g0 * d s * g0⁻¹) * h ∈ graphFixed6 L :=
  exists_fixed_conj_into_graphFixed p e he w v g0 hg0C hg0 hw d hd hv

theorem E6Pmat_conj_diag_of_invFixed {L : Type} [Field L] (ω : Lˣ) (hω3 : ω ^ 3 = 1)
    (v : WeylGroup Tag.E6) (k : Fin Tag.E6.rank → ℕ)
    (hk : InvFixedZ v (fun j => (k j : ℤ))) :
    E6Pmat L * (canonicalRep (coxeterSystem Tag.E6) L v * rootDiagUnit Tag.E6 (fun i => ω ^ k i) *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) * (E6Pmat L)⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) L v * rootDiagUnit Tag.E6 (fun i => ω ^ k i) *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ :=
  diagramMap_conj_diag_of_invFixed ω hω3 v k hk

theorem exists_inn_conj_into_graphFixed {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 1) {A : Subgroup (ModGL Tag.E6 K)} (hA : A ≤ adjointGroup Tag.E6 K)
    (D : LangGLData Tag.E6 K A) (hc1 : D.c = 1) (ω : (AlgebraicClosure K)ˣ)
    (hω : IsPrimitiveRoot (ω : AlgebraicClosure K) 3) {x₁ x₂ : ModGL Tag.E6 K}
    (hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL Tag.E6 K)) = A)
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (k₁ k₂ : Fin Tag.E6.rank → ℕ)
    (ha₁ : rootDiagUnit Tag.E6 (fun i => ω ^ k₁ i) = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x₁ * D.c⁻¹) * D.g0)
    (ha₂ : rootDiagUnit Tag.E6 (fun i => ω ^ k₂ i) = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x₂ * D.c⁻¹) * D.g0)
    (hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)))
    (hnf : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 →
      ¬ ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (D.w • v) i = ∑ i, l i * v i) :
    ∃ g ∈ adjointGroup Tag.E6 K, ∀ a ∈ A,
      g * a * g⁻¹ ∈ graphFixed6 K := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK4 : 4 ≤ Nat.card K := by omega
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hfix : ∀ (y : ModGL Tag.E6 K) (k : Fin Tag.E6.rank → ℕ),
      rootDiagUnit Tag.E6 (fun i => ω ^ k i) = D.g0⁻¹ * baseChangeGL ι (D.c * y * D.c⁻¹) * D.g0 →
      ∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
        (∑ i, (k i : ℤ) * (D.w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k t : ℤ) := by
    intro y k hy t
    have h := langGL_fix_exp hq D ω hω k hy (Pi.single t 1)
    simpa [Pi.single_apply] using h
  have hfix₁ := hfix x₁ k₁ ha₁
  have hfix₂ := hfix x₂ k₂ ha₂
  rcases e6_regular_elliptic_conj D.w k₁ k₂ hreg hfix₁ hfix₂ with
    ⟨l, hl, hlfix⟩ | ⟨ωw, hI₁, hI₂, hwT, m, k₀, hm, hk₀, hwm⟩
  · exact absurd hlfix (hnf l hl)
  set v : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd ωw with hv
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI hpf : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap ι.injective _
  have hFrEq : D.Fr = iterateFrobenius L (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hg0F : Units.map (entrywiseHom (iterateFrobenius L (ringChar K) e)) D.g0 =
      D.g0 * canonicalRep (coxeterSystem Tag.E6) L D.w := by
    rw [← hFrEq]
    exact D.hg0
  obtain ⟨h, hhC, hhF, hh⟩ := exists_fixed_conj_into_graphFixed6 (L := L) (ringChar K) e he D.w v
    D.g0 D.hg0C hg0F hwT
    (d := fun s : Fin 2 => rootDiagUnit Tag.E6 (fun i => ω ^ (![k₁, k₂] s i)))
    (fun s => rootDiagUnit_mem_torusGroup _)
    (fun s => by
      fin_cases s
      · exact E6Pmat_conj_diag_of_invFixed ω hω3 v k₁ hI₁
      · exact E6Pmat_conj_diag_of_invFixed ω hω3 v k₂ hI₂)
  have hhF' : Units.map (entrywiseHom D.Fr) h = h := by rw [hFrEq]; exact hhF
  obtain ⟨b, u, hu, hbu⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.E6 D.Fr D.hFr hhC hhF'
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨hK, hKdef⟩ : ∃ hK : ModGL Tag.E6 K, hK = rootDiagUnit Tag.E6 b * j := ⟨_, rfl⟩
  have hKmem : hK ∈ e6InndiagGL K := by
    rw [hKdef]
    exact mul_mem (rootDiagUnit_mem_e6InndiagGL b) (adjointGroup_le_e6InndiagGL K hj)
  have hhK : h = baseChangeGL ι hK := by
    rw [hKdef, map_mul]
    exact hbu
  have hnorm : ∀ y ∈ adjointGroup Tag.E6 K, hK⁻¹ * y * hK ∈ adjointGroup Tag.E6 K := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.1
      (inv_mem (e6InndiagGL_le_normalizer K hKmem)) y).1 hy
    simpa using this
  have hgenΓ : ∀ (y : ModGL Tag.E6 K) (k : Fin Tag.E6.rank → ℕ) (s : Fin 2), y ∈ A →
      rootDiagUnit Tag.E6 (fun i => ω ^ k i) = D.g0⁻¹ * baseChangeGL ι (D.c * y * D.c⁻¹) * D.g0 →
      (fun i => ω ^ (![k₁, k₂] s i)) = (fun i => ω ^ k i) →
      hK⁻¹ * y * hK ∈ graphFixed6 K := by
    intro y k s hy hyk hsk
    refine mem_graphFixed6_of_baseChange ι (hnorm y (hA hy)) ?_
    have h1 := hh s
    rw [hsk, hyk, hc1] at h1
    rw [hhK] at h1
    have e : baseChangeGL ι (hK⁻¹ * y * hK) =
        (baseChangeGL ι hK)⁻¹ * (D.g0 * (D.g0⁻¹ * baseChangeGL ι (1 * y * 1⁻¹) * D.g0) *
          D.g0⁻¹) * baseChangeGL ι hK := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e]
    exact h1
  have hS : A ≤ (graphFixed6 K).comap (MulAut.conj hK⁻¹).toMonoidHom := by
    rw [← hgen, Subgroup.closure_le]
    rintro y (hy | hy)
    · rw [hy]
      refine Subgroup.mem_comap.2 ?_
      simpa [MulAut.conj_apply] using hgenΓ x₁ k₁ 0 hx₁ ha₁ rfl
    · rw [hy]
      refine Subgroup.mem_comap.2 ?_
      simpa [MulAut.conj_apply] using hgenΓ x₂ k₂ 1 hx₂ ha₂ rfl
  set t0 : ModGL Tag.E6 L := rootDiagUnit Tag.E6 (fun i => ω ^ k₀ i) with ht0
  set c0L : ModGL Tag.E6 L := D.g0 * t0 * D.g0⁻¹ with hc0L
  have hc0Lad : c0L ∈ adjointGroup Tag.E6 L :=
    mul_mem (mul_mem D.hg0C (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)))
      (inv_mem D.hg0C)
  have hωF : Units.map D.Fr.toMonoidHom ω = ω := by
    apply Units.ext
    obtain ⟨t', ht'⟩ : ∃ t', Nat.card K = 3 * t' + 1 := ⟨Nat.card K / 3, by omega⟩
    have h1 : ((Units.map D.Fr.toMonoidHom ω : Lˣ) : L) = ((ω : Lˣ) : L) ^ Nat.card K := by
      simp [D.hFr]
    rw [h1, ht', pow_succ, pow_mul]
    have h3 : ((ω : Lˣ) : L) ^ 3 = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) hω3
      simpa using this
    rw [h3, one_pow, one_mul]
  have hFt0 : Units.map (entrywiseHom D.Fr) t0 = t0 := by
    rw [ht0, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
    congr 1
    funext i
    simp only [map_zpow, map_pow, hωF]
  have hwt0 : canonicalRep (coxeterSystem Tag.E6) L D.w * t0 *
      (canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹ = t0 := by
    rw [ht0, canonicalRep_conj_rootDiagUnit]
    congr 1
    funext i
    simp only [weylTuple]
    have e1 := rootChar_pow_exp (L := L) ω k₀ (D.w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
    have e2 := rootChar_pow_exp (L := L) ω k₀ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
    have hd := three_dvd_inv_smul_of_fix D.w k₀ hk₀ (Pi.single i 1)
    have h3 := zpow_eq_zpow_of_dvd hω3 hd
    have hr : rootChar (fun i => ω ^ k₀ i) (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = ω ^ k₀ i := by
      simp [rootChar, Pi.single_apply]
    exact e1.trans (h3.trans (e2.symm.trans hr))
  have hc0LF : Units.map (entrywiseHom D.Fr) c0L = c0L := by
    rw [hc0L, map_mul, map_mul, map_inv, hFt0, D.hg0]
    calc D.g0 * canonicalRep (coxeterSystem Tag.E6) L D.w * t0 *
          (D.g0 * canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹
        = D.g0 * (canonicalRep (coxeterSystem Tag.E6) L D.w * t0 *
            (canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹) * D.g0⁻¹ := by group
      _ = D.g0 * t0 * D.g0⁻¹ := by rw [hwt0]
  obtain ⟨b₀, u₀, hu₀, hbu₀⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed Tag.E6 D.Fr D.hFr hc0Lad hc0LF
  obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hu₀
  obtain ⟨c0K, hc0K⟩ : ∃ c0K : ModGL Tag.E6 K, c0K = rootDiagUnit Tag.E6 b₀ * j₀ :=
    ⟨_, rfl⟩
  have hc0Kmem : c0K ∈ e6InndiagGL K := by
    rw [hc0K]
    exact mul_mem (rootDiagUnit_mem_e6InndiagGL b₀) (adjointGroup_le_e6InndiagGL K hj₀)
  have hc0KL : baseChangeGL ι c0K = c0L := by
    rw [hc0K, map_mul]
    exact hbu₀.symm
  have hnot : c0K ∉ adjointGroup Tag.E6 K :=
    not_mem_adjointGroup_of_not_fixed hq D.w D.Fr D.hFr D.g0 D.hg0C D.hg0 ω hω k₀ m hm hwm
      (y := c0K) (by rw [hc0KL, hc0L])
  have hcent : ∀ a ∈ A, Commute c0K a := by
    have hle : A ≤ Subgroup.centralizer ({c0K} : Set (ModGL Tag.E6 K)) := by
      rw [← hgen, Subgroup.closure_le]
      have hgenC : ∀ (y : ModGL Tag.E6 K) (k : Fin Tag.E6.rank → ℕ),
          rootDiagUnit Tag.E6 (fun i => ω ^ k i) = D.g0⁻¹ *
            baseChangeGL ι (D.c * y * D.c⁻¹) * D.g0 →
          y ∈ Subgroup.centralizer ({c0K} : Set (ModGL Tag.E6 K)) := by
        intro y k hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply baseChangeGL_injective ι
        rw [map_mul, map_mul, hc0KL, hc0L]
        have hyL : baseChangeGL ι y = D.g0 * rootDiagUnit Tag.E6 (fun i => ω ^ k i) * D.g0⁻¹ := by
          rw [hy, hc1]
          simp only [one_mul, inv_one, mul_one]
          group
        rw [hyL, ht0]
        calc D.g0 * rootDiagUnit Tag.E6 (fun i => ω ^ k i) * D.g0⁻¹ *
              (D.g0 * rootDiagUnit Tag.E6 (fun i => ω ^ k₀ i) * D.g0⁻¹)
            = D.g0 * (rootDiagUnit Tag.E6 (fun i => ω ^ k i) *
                rootDiagUnit Tag.E6 (fun i => ω ^ k₀ i)) * D.g0⁻¹ := by group
          _ = D.g0 * (rootDiagUnit Tag.E6 (fun i => ω ^ k₀ i) *
                rootDiagUnit Tag.E6 (fun i => ω ^ k i)) * D.g0⁻¹ := by
            rw [rootDiagUnit_comm']
          _ = D.g0 * rootDiagUnit Tag.E6 (fun i => ω ^ k₀ i) * D.g0⁻¹ *
              (D.g0 * rootDiagUnit Tag.E6 (fun i => ω ^ k i) * D.g0⁻¹) := by group
      rintro y (rfl | rfl)
      · exact hgenC _ k₁ ha₁
      · exact hgenC _ k₂ ha₂
    intro a ha
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ha)).symm
  obtain ⟨j', hj'⟩ := exists_zpow_mul_mem_adjointGroup hK4 hc0Kmem hnot (a := hK⁻¹)
    (inv_mem hKmem)
  refine ⟨hK⁻¹ * c0K ^ j', hj', fun a ha => ?_⟩
  have hcomm : c0K ^ j' * a = a * c0K ^ j' := ((hcent a ha).zpow_left j').eq
  have hmem := Subgroup.mem_comap.1 (hS ha)
  have hfin : hK⁻¹ * c0K ^ j' * a * (hK⁻¹ * c0K ^ j')⁻¹ = hK⁻¹ * a * hK := by
    calc hK⁻¹ * c0K ^ j' * a * (hK⁻¹ * c0K ^ j')⁻¹
        = hK⁻¹ * (c0K ^ j' * a) * (c0K ^ j')⁻¹ * hK := by group
      _ = hK⁻¹ * a * hK := by rw [hcomm]; group
  rw [hfin]
  simpa [MulAut.conj_apply] using hmem

end Main

end CFSG.LieType.SeitzGeneration.ExcHighThree
