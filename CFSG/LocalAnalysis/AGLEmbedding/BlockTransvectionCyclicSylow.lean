module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLevi
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ParabAutIrr

namespace TransvectionCyclic

variable {X : Type*} [Group X] [Finite X]

theorem isCyclic_of_not_sq_dvd_card {p : ℕ} (hp : p.Prime) {A : Subgroup X}
    (hA : IsPGroup p A) (h : ¬ p ^ 2 ∣ Nat.card A) : IsCyclic A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rcases k with _ | _ | k
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (by simpa using hk)
  · exact (h (hk ▸ pow_dvd_pow p (by omega))).elim

theorem le_perfectJoin_of_quotient_perfect {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J : Subgroup X} {Q : Type*} [Group Q] (φ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q)
    (hQ : commutator Q = ⊤) {A : Subgroup X} (hAJ : A ≤ J) (hA : IsPGroup p A) :
    A ≤ perfectJoin J := by
  set O : Subgroup ↥J := CFSG.pCore 2 ↥J
  have : O.Normal := CFSG.pCore_normal
  set ψ : ↥J →* Q := φ.toMonoidHom.comp (QuotientGroup.mk' O)
  have hψ : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hQp : Group.IsPerfect (⊤ : Subgroup Q) := by
    apply Subgroup.isPerfect_iff.mpr
    rw [← commutator_def, hQ]
  have hR := finite_canonical_perfect_preimage_image_eq ψ hψ ⊤ hQp
  set R₀ := perfectResidualOf (Subgroup.comap ψ ⊤)
  have hR₀p : ⁅R₀, R₀⁆ = R₀ := Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect _)
  have hRJ : R₀.map J.subtype ≤ perfectJoin J :=
    le_perfectJoin (Subgroup.map_subtype_le _) (by rw [← Subgroup.map_commutator, hR₀p])
  have hO2 : IsPGroup 2 (O.map J.subtype) := (CFSG.pCore_isPGroup).map _
  refine pSubgroup_le_perfectJoin hp hp2 hO2 (Subgroup.map_subtype_le _) ?_ hA
  intro a ha
  have haJ := hAJ ha
  have hmem : ψ ⟨a, haJ⟩ ∈ R₀.map ψ := by rw [hR]; trivial
  obtain ⟨r, hr, hre⟩ := hmem
  have hker : r⁻¹ * ⟨a, haJ⟩ ∈ O := by
    have h1 : ψ (r⁻¹ * ⟨a, haJ⟩) = 1 := by rw [map_mul, map_inv, hre, inv_mul_cancel]
    have h2 : QuotientGroup.mk' O (r⁻¹ * ⟨a, haJ⟩) = 1 := φ.injective (by simpa [ψ] using h1)
    exact (QuotientGroup.eq_one_iff _).mp h2
  have : a = (r : X) * ((r⁻¹ * ⟨a, haJ⟩ : ↥J) : X) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup (hRJ ⟨r, hr, rfl⟩) ⟨_, hker, rfl⟩

omit [Finite X] in
theorem isCyclic_of_mulEquiv_perm_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup X}
    (e : ↥J ≃* Equiv.Perm (Fin 6)) (hperf : PerfectCyclicSylow p J) {A : Subgroup X}
    (hAJ : A ≤ J) (hA : IsPGroup p A) : IsCyclic A := by
  set V : Subgroup ↥J := (alternatingGroup (Fin 6)).comap e.toMonoidHom
  have h6 : 5 ≤ Nat.card (Fin 6) := by simp
  have hA6 := commutator_alternatingGroup_eq_self h6
  have hVeq : V = (alternatingGroup (Fin 6)).map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm e _
  have hVp' : ⁅V, V⁆ = V := by rw [hVeq, ← Subgroup.map_commutator, hA6]
  have hVp : ⁅V.map J.subtype, V.map J.subtype⁆ = V.map J.subtype := by
    rw [← Subgroup.map_commutator, hVp']
  refine hperf _ (Subgroup.map_subtype_le _) hVp A ?_ hA
  intro a ha
  refine ⟨⟨a, hAJ ha⟩, ?_, rfl⟩
  show Equiv.Perm.sign (e ⟨a, hAJ ha⟩) = 1
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  have hk' : (e ⟨a, hAJ ha⟩) ^ p ^ k = 1 := by
    rw [← map_pow]
    have : (⟨a, hAJ ha⟩ : ↥J) ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hs : (Equiv.Perm.sign (e ⟨a, hAJ ha⟩)) ^ p ^ k = 1 := by rw [← map_pow, hk', map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e ⟨a, hAJ ha⟩)) with h | h
  · exact h
  · rw [h] at hs
    have hodd : Odd (p ^ k) := Odd.pow (hp.odd_of_ne_two hp2)
    rw [hodd.neg_one_pow] at hs
    exact absurd hs (by decide)

end TransvectionCyclic

open TransvectionCyclic

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem isCyclic_of_le_blockPL (hTPLT : CitedBlockTransvectionPLType)
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h3 : NineThreeThree M S L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hperf : PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hAP : A ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L)) (hAp : IsPGroup p A) :
    IsCyclic A := by
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hTPLT G M S L hK hA hL hX hS h3
  have hval : ∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      (d.1 = .D m q ∨ d.1 = .twistedD m q) → 4 ≤ m := by
    intro m d q hd
    have h := d.2
    rcases hd with hd | hd <;> rw [hd] at h <;>
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
  have hsp : ∀ (m : ℕ) (d' : TauCeti.ValidLieTypeIndex), 4 ≤ m →
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B (m - 1) q) →
      Nonempty (↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃*
        (TauCeti.CFSGIndex.lie d').Group) → IsCyclic A := by
    rintro m d' hm hd' ⟨φ⟩
    have hQ := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds (m - 1) d' (by omega) hd'
    exact hperf _ (perfectJoin_le _) (perfectJoin_perfect _) A
      (le_perfectJoin_of_quotient_perfect hp hp2 φ hQ hAP hAp) hAp
  have hsmall : ∀ n : ℕ, (n = 3 ∨ n = 4) →
      Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin n)) → IsCyclic A := by
    rintro n hn ⟨e⟩
    refine isCyclic_of_not_sq_dvd_card hp hAp fun h => ?_
    have hc : Nat.card A ∣ n.factorial := by
      have := Subgroup.card_dvd_of_le hAP
      rw [Nat.card_congr e.toEquiv, Nat.card_perm] at this
      simpa using this
    have h2 := h.trans hc
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rcases hn with rfl | rfl
    · have hle := Nat.le_of_dvd (by decide) h2
      have h6 : p ^ 2 ≤ 6 := by simpa [Nat.factorial] using hle
      nlinarith
    · have hle := Nat.le_of_dvd (by decide) h2
      have h25 : p ^ 2 ≤ 24 := by simpa [Nat.factorial] using hle
      have hp4 : p ≤ 4 := by nlinarith
      interval_cases p
      · exact absurd h2 (by decide)
      · exact absurd hp (by decide)
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', hd', hφ⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      exact hsp m d' (hval m d q (Or.inl hd)) hd' hφ
    · obtain ⟨d', hd', hφ⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      exact hsp m d' (hval m d q (Or.inr hd)) hd' hφ
    · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
      exact isCyclic_of_mulEquiv_perm_six hp hp2 e6 hperf hAP hAp
  · rcases hn with rfl | rfl | rfl
    · exact hsmall 3 (Or.inl rfl) (hA5 ⟨e⟩)
    · exact hsmall 4 (Or.inr rfl) (hA6 ⟨e⟩)
    · obtain ⟨e6⟩ := hA8 ⟨e⟩
      exact isCyclic_of_mulEquiv_perm_six hp hp2 e6 hperf hAP hAp

end CFSG.AGLEmbedding
