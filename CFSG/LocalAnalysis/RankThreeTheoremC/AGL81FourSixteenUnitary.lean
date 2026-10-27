module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open scoped Pointwise commutatorElement

theorem exists_uniCover_std_of
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (f t s ε : ℕ) (h : UnitaryFieldData 2 f K)
      (ρ : hypSU h (t + s) ε →* ↥L) (I : Finset ℕ),
      ε ≤ 1 ∧ IsTopCut I t ∧
        (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f ∧ r₀ + 1 = 2 * (t + s) + ε) ∧
        Function.Surjective ρ ∧
        (∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) ∧
        (P.subgroupOf L).comap ρ = flagStabilizer h (t + s) ε ↑I := by
  obtain ⟨K, hK, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hd e
  have hmem : ∀ y : hypSU h (t + s) ε, y ∈ (P.subgroupOf L).comap ρ ↔
      g⁻¹ * y * g ∈ flagStabilizer h (t + s) ε ↑I := by
    intro y
    rw [hJ, mem_flagStabilizer]
    refine forall₂_congr fun i _ => ?_
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  refine ⟨K, hK, f, t, s, ε, h, ρ.comp (MulAut.conj g).toMonoidHom, I, hε, hI, hq,
    hρ.comp (MulAut.conj g).surjective, fun y => ?_, ?_⟩
  · rw [MonoidHom.comp_apply]
    change ρ (MulAut.conj g y) ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε
    rw [hZ]
    constructor
    · intro hy
      have := (inferInstance : (hypScalars h (t + s) ε).Normal).conj_mem _ hy g⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro hy
      have := (inferInstance : (hypScalars h (t + s) ε).Normal).conj_mem _ hy g
      simpa [MulAut.conj_apply] using this
  · ext y
    have h1 : y ∈ (P.subgroupOf L).comap (ρ.comp (MulAut.conj g).toMonoidHom) ↔
        (MulAut.conj g y : hypSU h (t + s) ε) ∈ (P.subgroupOf L).comap ρ := Iff.rfl
    rw [h1, hmem]
    have : g⁻¹ * (MulAut.conj g y : hypSU h (t + s) ε) * g = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]

theorem false_of_twistedA_card_four (p : ℕ) [OddPrime p]
    {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) {r₀ : ℕ}
    {q : TauCeti.PrimePower} (hdq : d.1 = .twistedA r₀ q) (hr₀ : 2 ≤ r₀) (hq4 : q.card = 4)
    (hrank : ∀ q' : ℕ, q'.Prime → q' ≠ 2 → Open.pRank q' L ≤ 3)
    (hrk : Open.pRank p (wPre P) ≤ 1) {a : Y} (ha3 : IsPGroup p (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hout : ¬ ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P) : False := by
  classical
  have hqp : q.p = 2 := by
    have h1 : q.p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = q.card from hq4.symm, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)
  have hd : IdxTwistedA d.1 := by rw [hdq]; exact hqp
  obtain ⟨K, hK, f, t, s, ε, h, ρ, I, hε, hI, hq, hρs, hZ, hcomap⟩ :=
    exists_uniCover_std_of hCP d hd e
  obtain ⟨hqc, hn⟩ := hq r₀ q hdq
  have hf : f = 2 := by
    have h2 : 2 ^ f = 2 ^ 2 := by rw [← hqc, hq4]; norm_num
    exact Nat.pow_right_injective le_rfl h2
  subst hf
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hr : 1 ≤ t + s := by omega
  have hn3 : 3 ≤ 2 * (t + s) + ε := by omega
  have hnq : ¬(2 * (t + s) + ε = 3 ∧ 2 ^ 2 = 2) := fun h' => by omega
  obtain ⟨θ, hθ⟩ : ∃ θ : hypPSU h (t + s) ε ≃* ↥L ⧸ Subgroup.center ↥L,
      ∀ y, θ (hypProj h (t + s) ε y) = (QuotientGroup.mk (ρ y) : ↥L ⧸ Subgroup.center ↥L) :=
    ⟨uniCoverEquiv ρ hρs hZ, uniCoverEquiv_hypProj ρ hρs hZ⟩
  let ψ : ↥(semilinearSimilitudes h (t + s) ε) →* (K ≃+* K) :=
    (SemidirectProduct.rightHom).comp (semilinearSimilitudes h (t + s) ε).subtype
  have hΦs : Function.Surjective (semilinearAutHom h hr hε) :=
    semilinearAutHom_surjective_of_admissible h hr hε hn3 hnq
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  set β : MulAut (hypPSU h (t + s) ε) := MulAut.congr θ.symm (convAut L a) with hβ
  have hmem : β ∈ ψ.ker.map (semilinearAutHom h hr hε) := by
    obtain ⟨x, hx⟩ := hΦs β
    have hcK : Nat.card (K ≃+* K) = 2 * 2 :=
      (card_ringAut_and_isCyclic Nat.prime_two K h.card).1
    haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcK]; norm_num)
    have hx4 : x ^ 4 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      have := pow_card_eq_one' (G := K ≃+* K) (x := ψ x)
      rwa [hcK] at this
    have hβ4 : β ^ 4 ∈ ψ.ker.map (semilinearAutHom h hr hε) :=
      ⟨x ^ 4, hx4, by rw [map_pow, hx]⟩
    have hβp : β ^ p ^ k = 1 := by
      rw [hβ, ← map_pow, ← map_pow, hak, map_one, map_one]
    have hco : Nat.Coprime 4 (orderOf β) := by
      have h4 : Nat.Coprime 4 (p ^ k) := by
        have h2p : Nat.Coprime 2 p :=
          (Nat.coprime_primes Nat.prime_two OddPrime.prime).2 (OddPrime.ne_two p).symm
        have := Nat.Coprime.pow 2 k h2p
        norm_num at this
        exact this
      exact h4.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hβp)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
    rw [← hm]
    exact Subgroup.pow_mem _ hβ4 m
  obtain ⟨x₀, hx₀k, hx₀⟩ := Subgroup.mem_map.1 hmem
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep h hr hε hn3 x₀
  have hA : (x : SemiGL (HypIndex (t + s) ε) K).left ∈ hypUnitary h (t + s) ε := hxU
  have hr0 : (x₀ : SemiGL (HypIndex (t + s) ε) K).right = 1 := by
    have := MonoidHom.mem_ker.1 hx₀k
    simpa [ψ] using this
  have hxr1 : (x : SemiGL (HypIndex (t + s) ε) K).right = 1 := hxr.trans hr0
  have hcm : ∀ y : hypSU h (t + s) ε, (MulAut.conjNormal a : MulAut ↥L) (ρ y) *
      (ρ (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y))⁻¹ ∈
        Subgroup.center ↥L := by
    intro y
    have h1 : semilinearAutHom h hr hε x (hypProj h (t + s) ε y) =
        hypProj h (t + s) ε (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y) := by
      rw [semilinearAutHom_apply]
      congr 1
      apply Subtype.ext
      change (x : SemiGL (HypIndex (t + s) ε) K).left *
        glAut (x : SemiGL (HypIndex (t + s) ε) K).right (y : GL (HypIndex (t + s) ε) K) *
          (x : SemiGL (HypIndex (t + s) ε) K).left⁻¹ =
        (x : SemiGL (HypIndex (t + s) ε) K).left * (y : GL (HypIndex (t + s) ε) K) *
          (x : SemiGL (HypIndex (t + s) ε) K).left⁻¹
      rw [hxr1, map_one]
      rfl
    have h2 : semilinearAutHom h hr hε x (hypProj h (t + s) ε y) =
        θ.symm (convAut L a (θ (hypProj h (t + s) ε y))) := by
      rw [hxΦ, hx₀]
      rfl
    have h4 : θ (hypProj h (t + s) ε
        (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y)) =
          convAut L a (QuotientGroup.mk (ρ y)) := by
      rw [← h1, h2, θ.apply_symm_apply, hθ]
    rw [hθ] at h4
    have h5 : (QuotientGroup.mk (ρ (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y)) :
        ↥L ⧸ Subgroup.center ↥L) =
          QuotientGroup.mk ((MulAut.conjNormal a : MulAut ↥L) (ρ y)) := h4
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.1 h5.symm
  exact hout (uniActsInnerlyW_of_compatP hCP h hε hI ρ hρs hZ hcomap
    (hrank p OddPrime.prime (OddPrime.ne_two p)) hA haN hcm
    ⟨k, fun w _ => by rw [hak, one_mul, mul_one]⟩ hrk)

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
