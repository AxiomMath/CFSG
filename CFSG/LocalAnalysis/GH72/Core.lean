module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups

@[expose] def IsDDShape (S : Type*) [Group S] : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 3 ≤ a + b ∧
    Nonempty (S ≃* DihedralGroup (2 ^ a) × DihedralGroup (2 ^ b))

@[expose] def IsAStarFactor {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
    (∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 5 ≤ p ^ k ∧
      Nonempty (L ≃* PSL(2, GaloisField p k))) ∨
    IsKleinFour L

@[expose] def AStarHyp (G : Type*) [Group G] [Finite G] : Prop :=
  CFSG.Open.classicalInvolutionOddCore G = ⊥ ∧
    (∀ N : Subgroup G, N.Normal → N.index ≠ 2) ∧
    ∃ S : Sylow 2 G, IsDDShape (S : Subgroup G)

@[expose] def AStarConclusion (G : Type*) [Group G] : Prop :=
  ∃ L₁ L₂ : Subgroup G, L₁.Normal ∧ L₂.Normal ∧ L₁ ⊓ L₂ = ⊥ ∧ Odd (L₁ ⊔ L₂).index ∧
    IsAStarFactor L₁ ∧ IsAStarFactor L₂

@[expose] def AStarStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], AStarHyp G → AStarConclusion G

@[expose] def HDDStatement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
    CFSG.Open.classicalInvolutionOddCore Y = ⊥ →
    ∀ (P : Sylow 2 Y) (m : ℕ), 2 ≤ m →
      Nonempty ((P : Subgroup Y) ≃* DihedralGroup (2 ^ m) × DihedralGroup (2 ^ m)) →
      ∃ L₁ L₂ : Subgroup Y, L₁.Normal ∧ L₂.Normal ∧ L₁ ⊓ L₂ = ⊥ ∧ L₁ ⊔ L₂ = ⊤ ∧
        ∀ L ∈ ({L₁, L₂} : Set (Subgroup Y)), Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
          ∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 5 ≤ p ^ k ∧
            Nonempty (L ≃* PSL(2, GaloisField p k))

section Derivation

variable {Y : Type*} [Group Y]

theorem index_ne_two_of_commutator_eq_top (hperf : commutator Y = ⊤) (N : Subgroup Y)
    [hN : N.Normal] : N.index ≠ 2 := by
  intro h2
  have hp : Nat.Prime (Nat.card (Y ⧸ N)) := by
    rw [← Subgroup.index, h2]
    exact Nat.prime_two
  haveI : Fact (Nat.card (Y ⧸ N)).Prime := ⟨hp⟩
  haveI : IsCyclic (Y ⧸ N) := isCyclic_of_prime_card rfl
  letI : CommGroup (Y ⧸ N) := IsCyclic.commGroup
  have hle : commutator Y ≤ (QuotientGroup.mk' N).ker :=
    Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [hperf, QuotientGroup.ker_mk', top_le_iff] at hle
  rw [hle, Subgroup.index_top] at h2
  exact absurd h2 (by norm_num)

theorem commutator_eq_top_of_inf_eq_bot_of_sup_eq_top' (hperf : commutator Y = ⊤)
    {L₁ L₂ : Subgroup Y} [L₂.Normal] (hinf : L₁ ⊓ L₂ = ⊥) (hsup : L₁ ⊔ L₂ = ⊤) :
    commutator L₁ = ⊤ := by
  let ρ : L₁ →* Y ⧸ L₂ := (QuotientGroup.mk' L₂).comp L₁.subtype
  have hρi : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have : (x : Y) ∈ L₁ ⊓ L₂ := ⟨x.2, hx⟩
    rw [hinf, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective L₂ y
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup_of_normal_right.1 (hsup ▸ mem_top a :
      a ∈ L₁ ⊔ L₂)
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk' L₂) b = (QuotientGroup.mk' L₂) (b * c)
    rw [map_mul, show QuotientGroup.mk' L₂ c = 1 from (QuotientGroup.eq_one_iff c).2 hc,
      mul_one]
  let e : L₁ ≃* Y ⧸ L₂ := MulEquiv.ofBijective ρ ⟨hρi, hρs⟩
  have hq : commutator (Y ⧸ L₂) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective L₂ y
    have ha : a ∈ commutator Y := hperf ▸ mem_top a
    rw [_root_.commutator_def] at ha ⊢
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' L₂) ha
    rwa [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective L₂)] at this
  rw [eq_top_iff]
  rintro x -
  have hx : e x ∈ commutator (Y ⧸ L₂) := hq ▸ mem_top _
  rw [_root_.commutator_def] at hx ⊢
  have := Subgroup.mem_map_of_mem e.symm.toMonoidHom hx
  rw [map_commutator, map_top_of_surjective _ e.symm.surjective] at this
  simpa using this

theorem not_isKleinFour_of_commutator_eq_top {L : Type*} [Group L]
    (h : commutator L = ⊤) : ¬ IsKleinFour L := by
  intro hK
  have hbot : commutator L = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact mul_comm_of_exponent_two hK.exponent_two y x
  have hcard : Nat.card L = 4 := IsKleinFour.card_four
  have : (⊤ : Subgroup L) = ⊥ := h.symm.trans hbot
  have h1 : Nat.card (⊤ : Subgroup L) = 1 := by rw [this, Subgroup.card_bot]
  rw [Subgroup.card_top, hcard] at h1
  exact absurd h1 (by norm_num)

end Derivation

theorem eq_top_of_odd_index_of_perfect {Y : Type*} [Group Y] [Finite Y]
    (hperf : commutator Y = ⊤) (N : Subgroup Y) [N.Normal] (hodd : Odd N.index) : N = ⊤ := by
  have hQ : Odd (Nat.card (Y ⧸ N)) := hodd
  have hsolv : Group.IsSolvable (Y ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQ
  have hperfQ : commutator (Y ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N y
    have ha : a ∈ commutator Y := hperf ▸ mem_top a
    rw [_root_.commutator_def] at ha ⊢
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) ha
    rwa [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at this
  have hds : ∀ n, derivedSeries (Y ⧸ N) n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hperfQ]
  obtain ⟨n, hn⟩ := hsolv.solvable
  have htb : (⊤ : Subgroup (Y ⧸ N)) = ⊥ := (hds n).symm.trans hn
  have h1 : N.index = 1 := by
    change Nat.card (Y ⧸ N) = 1
    rw [← Subgroup.card_top (G := Y ⧸ N), htb, Subgroup.card_bot]
  exact Subgroup.index_eq_one.mp h1

theorem hDD_of_aStar (h : AStarStatement) : HDDStatement := by
  intro Y _ _ hperf hO P m hm hP
  have hhyp : AStarHyp Y :=
    ⟨hO, fun N hN => @index_ne_two_of_commutator_eq_top Y _ hperf N hN,
      P, m, m, by omega, by omega, by omega, hP⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, hinf, hodd, hF₁, hF₂⟩ := h Y hhyp
  have hsup : L₁ ⊔ L₂ = ⊤ := by
    haveI : (L₁ ⊔ L₂).Normal := Subgroup.sup_normal L₁ L₂
    exact eq_top_of_odd_index_of_perfect hperf _ hodd
  refine ⟨L₁, L₂, hL₁, hL₂, hinf, hsup, ?_⟩
  have hp₁ : commutator L₁ = ⊤ := commutator_eq_top_of_inf_eq_bot_of_sup_eq_top' hperf hinf hsup
  have hp₂ : commutator L₂ = ⊤ :=
    commutator_eq_top_of_inf_eq_bot_of_sup_eq_top' hperf (by rw [inf_comm, hinf])
      (by rw [sup_comm, hsup])
  have key : ∀ L : Subgroup Y, IsAStarFactor L → commutator L = ⊤ →
      Nonempty (L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 5 ≤ p ^ k ∧
          Nonempty (L ≃* PSL(2, GaloisField p k)) := by
    intro L hF hp
    rcases hF with h7 | hpsl | hK
    · exact Or.inl h7
    · exact Or.inr hpsl
    · exact absurd hK (not_isKleinFour_of_commutator_eq_top hp)
  intro L hL
  rcases hL with rfl | hL
  · exact key _ hF₁ hp₁
  · rw [Set.mem_singleton_iff] at hL
    subst hL
    exact key _ hF₂ hp₂

structure MinimalCounterexample (G : Type) [Group G] [Finite G] : Prop where
  hyp : AStarHyp G
  not_concl : ¬ AStarConclusion G
  ih : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → AStarHyp H →
    AStarConclusion H

theorem aStar_of_not_minimalCounterexample
    (h : ∀ (G : Type) [Group G] [Finite G], ¬ MinimalCounterexample G) : AStarStatement := by
  suffices H : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → AStarHyp G →
      AStarConclusion G by
    intro G _ _ hG
    exact H _ G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn hG
    by_contra hc
    exact h G ⟨hG, hc, fun H _ _ hlt hH => ih _ (hn ▸ hlt) H rfl hH⟩

end CFSG.GH72
