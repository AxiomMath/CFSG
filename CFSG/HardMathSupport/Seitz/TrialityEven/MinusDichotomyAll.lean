module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpMain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCharFree

set_option linter.unusedSectionVars false

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG
open scoped Matrix

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.GH74.GLS.Stage2.Bender.Thm1


theorem d4Minus_fixed_line_inner_all {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hv : d4MinusPsi σ L g₀ v ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L)
    (hn3 : n ^ 3 = 1) (hnv : n * v * n⁻¹ = v) :
    ∃ A : Lˣ, A ^ 3 = 1 ∧ A ≠ 1 ∧
      d4MinusPsi σ L g₀ v = rootDiagUnit TwistTag.D4.tag ![A, A, 1, A] := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  obtain ⟨hg₀C, -, hg₀F⟩ := hg₀
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hinj : Function.Injective ψ := d4MinusPsi_injective g₀
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  rw [d4Q_twistedTorus Fr] at hv
  obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.1 hv
  have hψv : ψ v = rootDiagUnit TwistTag.D4.tag b := hbv.symm
  have hcube : ∀ i, b i ^ 3 = 1 := by
    intro i
    have h : ψ (v ^ 3) = 1 := by rw [hv3, map_one]
    rw [map_pow, hψv, rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)] at h
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  obtain ⟨hb1, hb3⟩ := d4Q_eq_of_pow_eq_one hFr (p := 3) (by omega) hb hcube
  have h10 : b (1 : Fin 4) = b (0 : Fin 4) := hb1
  have h30 : b (3 : Fin 4) = b (0 : Fin 4) := hb3
  have hxv : ψ n * rootDiagUnit TwistTag.D4.tag b * (ψ n)⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
    rw [← hψv, ← map_inv, ← map_mul, ← map_mul, hnv]
  obtain ⟨w, k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hnM
  have hxF : trialityOpposition L * twistHom TwistTag.D4 L Fr (ψ n) *
      (trialityOpposition L)⁻¹ = ψ n := ((hrange (ψ n)).1 ⟨n, rfl⟩).2
  have hwrel : w ∈ relWeylTwist TwistTag.D4 := d4MnFL_relWeylTwist_of_fixed Fr hk hxk hxF
  have hxW : MapsRootLines (ψ n) w := hxk ▸ mapsRootLines_mul_canonicalRep hk w
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hnT
    rw [hxk, canonicalRep_one, mul_one]
    exact hk
  have hw3 : w ^ 3 = 1 := by
    have h3 : ψ n * ψ n * ψ n = 1 := by
      have h := congrArg ψ hn3
      rw [map_pow, map_one, pow_three'] at h
      exact h
    have h := (hxW.mul hxW).mul hxW
    rw [h3] at h
    rw [pow_three']
    exact h.unique mapsRootLines_one
  have hdbk : rootDiagUnit TwistTag.D4.tag b * k = k * rootDiagUnit TwistTag.D4.tag b :=
    rootDiagUnit_mul_comm_of_mem_torusGroup b hk
  have hconj : rootDiagUnit TwistTag.D4.tag b =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w * rootDiagUnit TwistTag.D4.tag b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by
    set nw := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hnw
    set db := rootDiagUnit TwistTag.D4.tag b with hdb
    rw [hxk] at hxv
    have h1 : k * (nw * db * nw⁻¹) * k⁻¹ = db := by
      calc k * (nw * db * nw⁻¹) * k⁻¹ = k * nw * db * (k * nw)⁻¹ := by group
        _ = db := hxv
    have h2 : nw * db * nw⁻¹ = k⁻¹ * db * k := by
      calc nw * db * nw⁻¹ = k⁻¹ * (k * (nw * db * nw⁻¹) * k⁻¹) * k := by group
        _ = k⁻¹ * db * k := by rw [h1]
    rw [h2, mul_assoc, hdbk, inv_mul_cancel_left]
  have hchar : ∀ u, rootChar b (w • u) = rootChar b u :=
    (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 hconj
  have hb2 : b (2 : Fin 4) = 1 := by
    have h0 := hchar (d4LatVec 1 0 0 0)
    rcases d4_order_three_smul_single_zero hwrel hw1 hw3 with hk | hk
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      exact h0
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      rw [h10, h30] at h0
      have h2 : (b (2 : Fin 4))⁻¹ = 1 := by
        calc (b (2 : Fin 4))⁻¹ = b (0 : Fin 4) * ((b (0 : Fin 4))⁻¹ * (b (2 : Fin 4))⁻¹ *
              (b (0 : Fin 4))⁻¹) * b (0 : Fin 4) := by group
          _ = b (0 : Fin 4) * b (0 : Fin 4) * b (0 : Fin 4) := by rw [h0]
          _ = b (0 : Fin 4) ^ 3 := (pow_three' _).symm
          _ = 1 := hcube _
      exact inv_eq_one.1 h2
  have hA1 : b (0 : Fin 4) ≠ 1 := by
    intro h0
    apply hv1
    apply hinj
    have h1 : b = 1 := by
      funext i
      fin_cases i
      · exact h0
      · exact h10.trans h0
      · exact hb2
      · exact h30.trans h0
    rw [hψv, h1, rootDiagUnit_one, map_one]
  refine ⟨b (0 : Fin 4), hcube _, hA1, ?_⟩
  rw [hψv]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h10
  · exact hb2
  · exact h30

theorem mp_toral_data_all {p f : ℕ} [Fact p.Prime] (hp : p.Prime)
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
  obtain ⟨A, hA3, hA1, hψv⟩ := d4Minus_fixed_line_inner_all hp hf hq K hK σ hσ L hg₀ v n hv
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

theorem d4Minus_plane_dichotomy_all {p f : ℕ} (hp : p.Prime)
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
  obtain ⟨g₀, hg₀C, hg₀P, hg₀F⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.d4Minus_exists_frame_all (L := AlgebraicClosure K)
      p hf
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
    obtain ⟨y₁, ζ, hy₁, hζdef, hyE, hζM, hcase⟩ := mp_toral_data_all hp hf hq K hK σ hσ
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

end CFSG.HardMathSupport.Seitz.TrialityEven
