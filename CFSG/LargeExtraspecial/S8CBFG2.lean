module

public import CFSG.LargeExtraspecial.S8CBFSL2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LargeExtraspecial.S8CBFCrit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

theorem relNormalTwoDatum_of_semidirect_sl2 {G : Type*} [Group G] {H Q L : Subgroup G} {z : G}
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hset : ((H ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) = (Q : Set G) * (L : Set G))
    (hLC : L ≤ H ⊓ centralizer ({z} : Set G)) (hLN : L ≤ normalizer (Q : Set G))
    (hQL : Q ⊓ L = ⊥) (hQ2 : IsPGroup 2 Q) (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hρ : ρ.range = L) (hρi : Function.Injective ρ) : RelNormalTwoDatum H z := by
  have hQC : Q ≤ H ⊓ centralizer ({z} : Set G) := by
    intro q hq
    have : q ∈ (Q : Set G) * (L : Set G) := ⟨q, hq, 1, L.one_mem, mul_one q⟩
    rw [← hset] at this
    exact this
  have hQn : ∀ c ∈ H ⊓ centralizer ({z} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    have hc' : c ∈ (Q : Set G) * (L : Set G) := by
      rw [← hset]
      exact hc
    obtain ⟨q₀, hq₀, l, hl, rfl⟩ := hc'
    have hlq : l * q * l⁻¹ ∈ Q := (mem_normalizer_iff.mp (hLN hl) q).mp hq
    have : q₀ * l * q * (q₀ * l)⁻¹ = q₀ * (l * q * l⁻¹) * q₀⁻¹ := by group
    rw [this]
    exact Q.mul_mem (Q.mul_mem hq₀ hlq) (Q.inv_mem hq₀)
  refine ⟨Q, hQC, hQn, hQ2, fun P hP hP2 => commutator_le_of_mul_eq hset hLC hQn hQL ?_ hP hP2⟩
  intro A hAL hA2 a ha b hb
  have hA' : IsPGroup 2 (A.comap ρ) := hA2.comap_of_injective ρ hρi
  have hAL' : ∀ x ∈ A, ∃ y ∈ A.comap ρ, ρ y = x := fun x hx => by
    obtain ⟨y, hy⟩ := (hρ ▸ hAL hx : x ∈ ρ.range)
    exact ⟨y, by rw [mem_comap, hy]; exact hx, hy⟩
  obtain ⟨a', ha', rfl⟩ := hAL' a ha
  obtain ⟨b', hb', rfl⟩ := hAL' b hb
  rw [← map_mul, ← map_mul, sl2_comm_of_isPGroup (A.comap ρ) hA' a' ha' b' hb']


theorem relNormalTwoDatum_G2_long (K : Type) [Field K] [Finite K] [CharP K 2] :
    RelNormalTwoDatum (adjointGroup .G2 K) (pinnedX .G2 K g2c 1) := by
  obtain ⟨-, -, hQ2, hC, hset, hLN, hQL, ⟨ρ, -, -, hρ, hρi⟩, -⟩ :=
    even_G2_highest_long_root_centralizer K
  exact relNormalTwoDatum_of_semidirect_sl2 hset (hC ▸ le_sup_right) hLN hQL hQ2 ρ hρ hρi

theorem relNormalTwoDatum_G2_short (K : Type) [Field K] [Finite K] [CharP K 2] :
    RelNormalTwoDatum (adjointGroup .G2 K) (pinnedX .G2 K g2v 1) := by
  obtain ⟨-, -, hEA, hC, hset, hLN, hQL, ⟨ρ, -, -, hρ, hρi⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  exact relNormalTwoDatum_of_semidirect_sl2 hset (hC ▸ le_sup_right) hLN hQL
    (@IsElementaryAbelian.isPGroup 2 _ _ hEA) ρ hρ hρi

theorem normalTwoDatum_G2 (K : Type) [Field K] [Finite K] [CharP K 2]
    {s : adjointGroup .G2 K} (hs : orderOf s = 2) : NormalTwoDatum s := by
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) s hs with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine NormalTwoDatum.of_mulEquiv (MulAut.conj c) ?_
    rw [MulAut.conj_apply, hc]
    exact normalTwoDatum_of_rel (relNormalTwoDatum_G2_long K)
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine NormalTwoDatum.of_mulEquiv (MulAut.conj c) ?_
    rw [MulAut.conj_apply, hc]
    exact normalTwoDatum_of_rel (relNormalTwoDatum_G2_short K)

theorem invCentSectAbelianSylow_of_lieModel_G2 {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : LieModel Y .G2 0 2 f) : InvCentSectAbelianSylow Y := by
  have hce : ChevalleyExceptionalModel Y .G2 2 f := by
    rcases h with ⟨hcl, -⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hsz (by decide)
  obtain ⟨⟨-, hf, -⟩, hU⟩ := hce
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hU
  have : CharP K 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hK
  refine invCentSectAbelianSylow_of_normalTwoDatum fun y hy => NormalTwoDatum.of_mulEquiv e ?_
  exact normalTwoDatum_G2 K (by rw [MulEquiv.orderOf_eq, hy])

end CFSG.LargeExtraspecial.S8
