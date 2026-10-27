module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.RankOneFlag
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransportNB
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftAbstract

public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.UnitaryLevi
open scoped commutatorElement

theorem center_statedSU_eq_scalars_of_ne {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hne : (n, 2 ^ f) ≠ (3, 2)) :
    Subgroup.center (StatedSU n (2 ^ f) K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f) hK hn hne).2


theorem exists_unitaryCover_succ_ne {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hcomp : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (hpar : IsParabolicTwo L J) (hne : J ≠ L) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    ∃ (n : ℕ), n = r + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ f ∧ 3 ≤ n ∧ (n, 2 ^ f) ≠ (3, 2) ∧ Nat.card K = (2 ^ f) ^ 2 ∧
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
  refine ⟨r + 1, rfl, K, hF, hFfin, hchar, hf, hn, hq, hcard, ?_⟩
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

theorem rank_two_false {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hcomp : IsComponentOf Lb ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hpar : IsParabolicTwo Lb Pb) (hne : Pb ≠ Lb) (r : ℕ) (hr : r = 2) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥) : False := by
  obtain ⟨n, hnr, K, hF, hFin, hchar, hf, hn3, hnq, hcard, ρ, e', hρs, hρe, hcen, S₀, hNJ, hJ⟩ :=
    exists_unitaryCover_succ_ne hcomp hodd hpar hne r q hv hd f hfq e
  obtain ⟨r', ε, hε, rfl⟩ : ∃ r' ε : ℕ, ε ≤ 1 ∧ n = 2 * r' + ε :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hcenter := center_statedSU_eq_scalars_of_ne (f := f) hcard hn3 hnq
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
  obtain ⟨Dt, hDtJ, hDt, d, hd', hds, -⟩ :=
    Lift.exists_lifted_abstract ρ' hPL (fun g => (ρ g).2)
      (fun l hl => by obtain ⟨g, hg⟩ := hρs ⟨l, hl⟩; exact ⟨g, congrArg Subtype.val hg⟩) hcY
      hrank3 hcycY hDperf hDle hx hx3 hxC hfreeY
  have h1 : r' = 1 := by omega
  have h2 : ε = 1 := by omega
  have hbot := no_perfect_in_rank_one_flag h1 h2 hcard (by omega) _ S₀ hNJ hJ Dt hDtJ hDt
  rw [hbot, Subgroup.mem_bot] at hd'
  exact hds (hd' ▸ Subgroup.one_mem _)

theorem hBA_twistedA_rank_two {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hcomp : IsComponentOf Lb ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hpar : IsParabolicTwo Lb Pb) (hne : Pb ≠ Lb) (r : ℕ) (hr : r = 2) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥)
    (U : Subgroup Y) (hUL : U ≤ Subgroup.normalizer (Lb : Set Y))
    (hUP : U ≤ Subgroup.normalizer (Pb : Set Y)) (hUD : U ≤ Subgroup.centralizer (D : Set Y))
    (hU3 : IsPGroup 3 U) :
    ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y) :=
  (rank_two_false hcomp hodd hpar hne r hr q hv hd f hfq e hrank3 hcycY hDperf hDle hx hx3 hxC
    hfreeY).elim

theorem hBR_twistedA_rank_two {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hcomp : IsComponentOf Lb ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hpar : IsParabolicTwo Lb Pb) (hne : Pb ≠ Lb) (r : ℕ) (hr : r = 2) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥)
    (E : Subgroup Y) (hEL : E ≤ Subgroup.normalizer (Lb : Set Y))
    (hEP : E ≤ Subgroup.normalizer (Pb : Set Y)) (hED : E ≤ Subgroup.centralizer (D : Set Y))
    (hEab : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 3 ^ 2)
    (t : Y) (ht : t ∈ Subgroup.normalizer (Lb : Set Y))
    (htE : t ∈ Subgroup.normalizer (E : Set Y))
    (htF : ∀ F : Subgroup Y, F ≤ E → Nat.card F = 3 →
      t ∉ Subgroup.normalizer (F : Set Y)) :
    E ⊓ Subgroup.centralizer (Lb : Set Y) ≠ ⊥ :=
  (rank_two_false hcomp hodd hpar hne r hr q hv hd f hfq e hrank3 hcycY hDperf hDle hx hx3 hxC
    hfreeY).elim

end CFSG.HardMathSupport.Curtis.UnitaryLevi
