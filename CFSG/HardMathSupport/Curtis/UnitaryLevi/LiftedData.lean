module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransportNB
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAbstract
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorTransport

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.UnitaryLevi
open scoped commutatorElement


theorem exists_unitaryCover_succ {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hcomp : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hpar : IsParabolicTwo L J) (hne : J ≠ L) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    ∃ (n : ℕ), n = r + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ f ∧ 3 ≤ n ∧ Nat.card K = (2 ^ f) ^ 2 ∧
      ∃ (ρ : StatedSU n (2 ^ f) K →* ↥L)
        (e' : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ f) K)),
        Function.Surjective ρ ∧
        (∀ g, e' (QuotientGroup.mk (ρ g)) =
          (QuotientGroup.mk g : StatedProj (StatedSU n (2 ^ f) K))) ∧
        (∀ g, ρ g ∈ Subgroup.center ↥L ↔
          ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K)) ∧
        ∃ S₀ : Sylow 2 (StatedSU n (2 ^ f) K),
          Subgroup.normalizer ((S₀ : Subgroup (StatedSU n (2 ^ f) K)) :
            Set (StatedSU n (2 ^ f) K)) ≤ (J.subgroupOf L).comap ρ ∧
          (J.subgroupOf L).comap ρ ≠ ⊤ := by
  subst hfq
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hd] at hm
  obtain ⟨⟨-, hf, hn, hq⟩, K, hF, hFfin, hcard, ⟨e'⟩⟩ := hm
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := q.exponent * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul])
  refine ⟨r + 1, rfl, K, hF, hFfin, hchar, hf, hn, hcard, ?_⟩
  obtain ⟨ρ, hρs, -, hρe⟩ := kFactCoverUnitary Y L hcomp hodd (r + 1) (2 ^ q.exponent) K hcard
    hn hq e'
  refine ⟨ρ, e', hρs, hρe, fun g => ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e'.toMonoidHom e'.injective,
      MulEquiv.coe_toMonoidHom, hρe g, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · obtain ⟨T, hT⟩ := exists_sylow_normalizer_le_of_parabolic hpar
    obtain ⟨S₀, hS₀⟩ := exists_sylow_normalizer_le_comap hρs T hT
    refine ⟨S₀, hS₀, fun htop => hne (le_antisymm hpar.1 fun y hy => ?_)⟩
    obtain ⟨g, hg⟩ := hρs ⟨y, hy⟩
    have := htop ▸ Subgroup.mem_top g
    rw [Subgroup.mem_comap, hg, Subgroup.mem_subgroupOf] at this
    exact this

theorem exists_lifted_data {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hcomp : IsComponentOf Lb ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hpar : IsParabolicTwo Lb Pb) (hne : Pb ≠ Lb) (r : ℕ) (hr : 3 ≤ r) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥) :
    ∃ (r' ε : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      ε ≤ 1 ∧ 1 ≤ r' ∧ 4 ≤ 2 * r' + ε ∧ Nat.card K = (2 ^ f) ^ 2 ∧ 1 ≤ f ∧
      ∃ (ρ : StatedSU (2 * r' + ε) (2 ^ f) K →* ↥Lb)
        (e' : ↥Lb ⧸ Subgroup.center ↥Lb ≃* StatedProj (StatedSU (2 * r' + ε) (2 ^ f) K))
        (S₀ : Sylow 2 (StatedSU (2 * r' + ε) (2 ^ f) K))
        (Dt : Subgroup (StatedSU (2 * r' + ε) (2 ^ f) K))
        (d : StatedSU (2 * r' + ε) (2 ^ f) K),
        Function.Surjective ρ ∧
        (∀ g, e' (QuotientGroup.mk (ρ g)) =
          (QuotientGroup.mk g : StatedProj (StatedSU (2 * r' + ε) (2 ^ f) K))) ∧
        (∀ g, ρ g ∈ Subgroup.center ↥Lb ↔
          ((g : GL (Fin (2 * r' + ε)) K) ∈ StatedScalars (Fin (2 * r' + ε)) K)) ∧
        Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r' + ε) (2 ^ f) K)) :
          Set (StatedSU (2 * r' + ε) (2 ^ f) K)) ≤ (Pb.subgroupOf Lb).comap ρ ∧
        (Pb.subgroupOf Lb).comap ρ ≠ ⊤ ∧
        Dt ≤ (Pb.subgroupOf Lb).comap ρ ∧ ⁅Dt, Dt⁆ = Dt ∧ d ∈ Dt ∧
        (d : GL (Fin (2 * r' + ε)) K) ∉ StatedScalars (Fin (2 * r' + ε)) K ∧
        (d : GL (Fin (2 * r' + ε)) K) ^ 3 ∈ StatedScalars (Fin (2 * r' + ε)) K ∧
        (∀ H : Subgroup (StatedSU (2 * r' + ε) (2 ^ f) K), ⁅H, H⁆ = H →
          (∀ w ∈ H, Commute w d) → H = ⊥) ∧
        (∀ V : Subgroup (StatedSU (2 * r' + ε) (2 ^ f) K), V ≤ (Pb.subgroupOf Lb).comap ρ →
          ⁅V, V⁆ = V → ∀ A : Subgroup (StatedSU (2 * r' + ε) (2 ^ f) K), A ≤ V → IsPGroup 3 A →
          IsCyclic (A.map (QuotientGroup.mk'
            (Subgroup.center (StatedSU (2 * r' + ε) (2 ^ f) K))))) ∧
        (∀ A : Subgroup (StatedSU (2 * r' + ε) (2 ^ f) K), A ≤ (Pb.subgroupOf Lb).comap ρ →
          CFSG.Open.IsElemAbelian 3 A →
          A ⊓ (StatedScalars (Fin (2 * r' + ε)) K).subgroupOf
            (StatedSU (2 * r' + ε) (2 ^ f) K) = ⊥ →
          ∀ j : ℕ, Nat.card A = 3 ^ j → j ≤ 3) ∧
        (∀ u : Y, u ∈ Subgroup.normalizer (Lb : Set Y) → u ∈ Subgroup.centralizer (D : Set Y) →
          ∀ g ∈ Dt, u * (ρ g : Y) * u⁻¹ = ρ g) := by
  obtain ⟨n, hnr, K, hF, hFin, hchar, hf, hn3, hcard, ρ, e', hρs, hρe, hcen, S₀, hNJ, hJ⟩ :=
    exists_unitaryCover_succ hcomp hodd hpar hne r q hv hd f hfq e
  have hn4 : 4 ≤ n := by omega
  obtain ⟨r', ε, hε, rfl⟩ : ∃ r' ε : ℕ, ε ≤ 1 ∧ n = 2 * r' + ε :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hcenter := center_statedSU_eq_scalars (f := f) hcard hn4
  have hPL : Pb ≤ Lb := hpar.1
  let ρ' : StatedSU (2 * r' + ε) (2 ^ f) K →* Y := Lb.subtype.comp ρ
  have hcY : ∀ g, ρ' g ∈ Lift.ZL Lb ↔ g ∈ Subgroup.center (StatedSU (2 * r' + ε) (2 ^ f) K) := by
    intro g
    rw [hcenter, Subgroup.mem_subgroupOf, ← hcen g, Subgroup.mem_center_iff, Lift.mem_ZL]
    constructor
    · rintro ⟨-, h⟩ m
      exact Subtype.ext (h m m.2)
    · intro h
      exact ⟨(ρ g).2, fun m hm => congrArg Subtype.val (h ⟨m, hm⟩)⟩
  obtain ⟨Dt, hDtJ, hDt, d, hd, hds, hd3, hfree, hcyc, hrank, hfix⟩ :=
    Lift.exists_lifted_abstract ρ' hPL (fun g => (ρ g).2)
      (fun l hl => by obtain ⟨g, hg⟩ := hρs ⟨l, hl⟩; exact ⟨g, congrArg Subtype.val hg⟩) hcY
      hrank3 hcycY hDperf hDle hx hx3 hxC hfreeY
  refine ⟨r', ε, K, hF, hFin, hchar, hε, by omega, hn4, hcard, by omega, ρ, e', S₀, Dt, d, hρs, hρe,
    hcen, hNJ, hJ, hDtJ, hDt, hd, ?_, ?_, hfree, hcyc, ?_, hfix⟩
  · intro h
    exact hds (by rw [hcenter]; exact h)
  · have := hd3
    rw [hcenter] at this
    exact this
  · rw [← hcenter]; exact hrank

end CFSG.HardMathSupport.Curtis.UnitaryLevi
