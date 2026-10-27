module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.AGLEmbedding
open scoped MatrixGroups

theorem psl2_isElemAbelian_of_map {p : ℕ} {Q K : Type} [Group Q] [Group K] (e : Q ≃* K)
    (H : Subgroup Q) (h : IsElemAbelian p (H.map e.toMonoidHom)) : IsElemAbelian p H := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := congrArg Subtype.val (h.1.is_comm.comm ⟨e a, a, a.2, rfl⟩ ⟨e b, b, b.2, rfl⟩)
    change e a * e b = e b * e a at h1
    apply Subtype.ext
    apply e.injective
    simpa using h1
  · have := h.2 (e x) ⟨x, hx, rfl⟩
    apply e.injective
    simpa using this

theorem psl2_mem_normalizer_map {Q K : Type} [Group Q] [Group K] (e : Q ≃* K) (H : Subgroup Q)
    (n : Q) :
    e n ∈ normalizer ((H.map e.toMonoidHom : Subgroup K) : Set K) ↔ n ∈ normalizer (H : Set Q) := by
  have key : ∀ x : Q, e x ∈ H.map e.toMonoidHom ↔ x ∈ H := fun x =>
    Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
  have hc : ∀ x : Q, e (n * x * n⁻¹) = e n * e x * (e n)⁻¹ := fun x => by simp
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have h1 := h (e x)
    rwa [← hc x, key, key] at h1
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hc x, key, key]
    exact h x

theorem psl2_sylowIsPlane_of_equiv {p : ℕ} [Fact p.Prime] {Q K : Type} [Group Q] [Finite Q]
    [Group K] [Finite K] (e : Q ≃* K) (h : SylowIsPlane p K) : SylowIsPlane p Q := by
  intro S
  have hS := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have h1 := h (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S)
  rw [hS] at h1
  refine ⟨psl2_isElemAbelian_of_map e _ h1.1, ?_⟩
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact h1.2

theorem psl2_planeMoves_of_equiv {p : ℕ} [Fact p.Prime] {Q K : Type} [Group Q]
    [Finite Q] [Group K] [Finite K] (e : Q ≃* K) (h : NormalizerMovesLines p K) :
    NormalizerMovesLines p Q := by
  intro S t ht ht1
  have hS := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  obtain ⟨n', hn', hnt⟩ := h (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S) (e t)
    (by rw [hS]; exact ⟨t, ht, rfl⟩) (by simpa using ht1)
  refine ⟨e.symm n', ?_, fun hmem => hnt ?_⟩
  · rw [← psl2_mem_normalizer_map e, MulEquiv.apply_symm_apply]
    rwa [hS] at hn'
  · have h2 : e (e.symm n' * t * (e.symm n')⁻¹) ∈ (zpowers t).map e.toMonoidHom :=
      ⟨_, hmem, rfl⟩
    rw [MonoidHom.map_zpowers] at h2
    simpa using h2

theorem psl2_sylowIsPlane (p : ℕ) [Fact p.Prime] :
    SylowIsPlane p (PSL(2, GaloisField p 2)) :=
  fun S => psl2GF_sylow p 2 (by norm_num) S

theorem psl2_planeMoves {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    NormalizerMovesLines p (PSL(2, GaloisField p 2)) := by
  intro S t ht ht1
  by_contra hcon
  push Not at hcon
  have hV : zpowers t = (S : Subgroup (PSL(2, GaloisField p 2))) := by
    refine psl2GF_invariant hp2 S (zpowers t) ((Subgroup.zpowers_le).2 ht)
      (by rwa [Ne, Subgroup.zpowers_eq_bot]) fun n hn => ?_
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : n * t ^ k * n⁻¹ = (n * t * n⁻¹) ^ k := (conj_zpow).symm
    rw [this]
    exact Subgroup.zpow_mem _ (hcon n hn) k
  obtain ⟨⟨-, hx⟩, hcard⟩ := psl2GF_sylow p 2 (by norm_num) S
  have h1 : orderOf t = p ^ 2 := by
    rw [← Nat.card_zpowers, hV]
    exact hcard
  have h2 : orderOf t ∣ p := orderOf_dvd_of_pow_eq_one (hx t ht)
  have h3 := Nat.le_of_dvd (Fact.out : p.Prime).pos h2
  rw [h1] at h3
  have hp := (Fact.out : p.Prime).two_le
  nlinarith

theorem psl2_autBound {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* PSL(2, GaloisField p 2)) :
    ∀ (S : Sylow p Q) (A : Subgroup (MulAut Q)), IsPGroup p A →
      Nat.card A ∣ Nat.card (S : Subgroup Q) := by
  intro S A hA
  rw [(psl2_sylowIsPlane_of_equiv e (psl2_sylowIsPlane p) S).2]
  have hA' : IsPGroup p (A.map (MulAut.congr e).toMonoidHom) :=
    hA.map (MulAut.congr e).toMonoidHom
  have h1 := kFactL2AutPCard p 2 hp2 (by norm_num) _ hA'
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hA
  rw [hk] at h1 ⊢
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hp2)
  exact hcop.dvd_of_dvd_mul_right h1

theorem secondPointFacts_psl2 {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {Q : Type} [Group Q] [Finite Q]
    (e : Nonempty (Q ≃* PSL(2, GaloisField p 2))) (hz : Subgroup.center Q = ⊥) :
    SecondPointFacts p Q := by
  obtain ⟨e⟩ := e
  have hp2 : p ≠ 2 := by omega
  exact ⟨psl2_autBound hp2 e, Or.inl ⟨psl2_sylowIsPlane_of_equiv e (psl2_sylowIsPlane p),
    psl2_planeMoves_of_equiv e (psl2_planeMoves hp2)⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
