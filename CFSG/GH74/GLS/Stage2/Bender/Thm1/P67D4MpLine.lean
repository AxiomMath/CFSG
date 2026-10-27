module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFixedLine

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut

section Main

theorem d4Minus_fixed_line_inner {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (_hp2 : p ≠ 2)
    (_hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
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
  classical
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

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
