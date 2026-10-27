module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerS3Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem cyclic_comm {X : Type*} [Group X] {H : Subgroup X} (hH : IsCyclic H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  intro x hx y hy
  have := (IsCyclic.commGroup (α := ↥H)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem family_comm [Finite V] {L : Subgroup (V ≃ₗ[k] V)} {ι : Type*} [Fintype ι]
    {g : ι → V ≃ₗ[k] V} (hk : Nat.card k = 2) (hL3 : Nat.card L = 3)
    (hI2 : Module.finrank k (commGL L ⊤) = 2)
    (hinj : Function.Injective fun i => conjR (g i) L)
    (hP : IsPGroup 3 (⨆ i, conjR (g i) L : Subgroup (V ≃ₗ[k] V))) :
    ∀ x ∈ (⨆ i, conjR (g i) L : Subgroup (V ≃ₗ[k] V)),
      ∀ y ∈ (⨆ i, conjR (g i) L : Subgroup (V ≃ₗ[k] V)), x * y = y * x := by
  classical
  have : Module.Finite k V := Module.Finite.of_finite
  have hcard : ∀ i, Nat.card (conjR (g i) L) = 3 := fun i => by
    unfold conjR
    rw [natCard_conjSub]
    exact hL3
  have hcyc : ∀ i, IsCyclic (conjR (g i) L) := fun i => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card (hcard i)
  have hrk : ∀ i, Module.finrank k (commGL (conjR (g i) L) ⊤) = 2 := fun i => by
    have e := commGL_conjSub (g i)⁻¹ L
    show Module.finrank k (commGL (conjSub (g i)⁻¹ L) ⊤) = 2
    rw [e, finrank_map_linearEquiv]
    exact hI2
  obtain ⟨c1, -⟩ := binary_three_group_rank_two_generators_disjoint_natural_planes hk
    (fun i => conjR (g i) L) hinj hcyc hcard hP hrk
  exact iSup_comm_of_pairwise (fun i => conjR (g i) L)
    (fun i => cyclic_comm (hcyc i)) c1

theorem exists_abelian_closure [Finite V] {G A L : Subgroup (V ≃ₗ[k] V)} (hLG : L ≤ G)
    (hAG : A ≤ G) (hk : Nat.card k = 2) (hL3 : Nat.card L = 3)
    (hI2 : Module.finrank k (commGL L ⊤) = 2) (hLperf : ⁅L, A⁆ = L)
    (hLsub : (L.subgroupOf G).IsSubnormal) (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A) :
    ∃ D : Subgroup (V ≃ₗ[k] V), L ≤ D ∧ (∀ x ∈ G, conjSub x L ≤ D) ∧
      OddAbelianSetting G D A ∧ ⁅D, A⁆ = L ∧
      D = ⨆ x ∈ G, conjR x L := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have : CharP k 2 := charP_two_of_card_two k hk
  obtain ⟨P, hPG, hP3, hPn, hLP⟩ := exists_threeGroup hLG hL3 hLsub
  obtain ⟨ι, hfin, g, hg, hinj, hall⟩ := exists_conj_family G L
  let D : Subgroup (V ≃ₗ[k] V) := ⨆ i, conjR (g i) L
  have hDP : D ≤ P := iSup_le fun i => by
    have : conjR (g i) L ≤ conjSub (g i)⁻¹ P := (conjSub (g i)⁻¹).monotone hLP
    exact this.trans (hPn _ (G.inv_mem (hg i)))
  have hD3 : IsPGroup 3 D := hP3.to_le hDP
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := family_comm hk hL3 hI2 hinj hD3
  have hDG : D ≤ G := hDP.trans hPG
  have hDn : ∀ y ∈ G, conjSub y D ≤ D := by
    intro y hy
    have e : conjSub y D = ⨆ i, conjSub y (conjR (g i) L) := by
      simp only [D, OrderIso.map_iSup]
    rw [e]
    refine iSup_le fun i => ?_
    obtain ⟨j, hj⟩ := exists_conj_natL hg hall hy i
    rw [hj]
    exact le_iSup (fun i => conjR (g i) L) j
  have hLD : L ≤ D := by
    obtain ⟨i, hi⟩ := hall 1 G.one_mem
    rw [conjR_one] at hi
    rw [hi]
    exact le_iSup (fun i => conjR (g i) L) i
  have hDeq : D = ⨆ x ∈ G, conjR x L := by
    apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (g i) (hg i) le_rfl
    · refine iSup₂_le fun x hx => ?_
      obtain ⟨i, hi⟩ := hall x hx
      rw [hi]
      exact le_iSup (fun i => conjR (g i) L) i
  have hset : OddAbelianSetting G D A :=
    { N_le := hDG
      N_normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDG).2 fun y hy =>
        mem_normalizer_of_conjSub_le (hDn y hy) (hDn y⁻¹ (G.inv_mem hy))
      N_abelian := fun x y => Subtype.ext (hcomm x x.2 y y.2)
      N_odd := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hD3
        rw [hn]
        exact Odd.pow (by decide)
      A_le := hAG
      A_elem := hAel
      A_ne := hAne
      offender := hoff
      strict := hstrict
      comm_ne := by
        intro hbot
        have h1 : ⁅L, A⁆ ≤ ⁅D, A⁆ := Subgroup.commutator_mono hLD le_rfl
        rw [hLperf, hbot] at h1
        have h2 : L = ⊥ := le_bot_iff.1 h1
        have h3 : Nat.card L = 1 := by rw [h2]; exact Subgroup.card_bot
        omega }
  refine ⟨D, hLD, fun x hx => ?_, hset, ?_, hDeq⟩
  · have e : conjSub x L = conjR x⁻¹ L := by
      unfold conjR
      rw [inv_inv]
    rw [e, hDeq]
    exact le_iSup₂_of_le x⁻¹ (G.inv_mem hx) le_rfl
  · obtain ⟨I0, hI0⟩ := hset.planeData (L := ⁅D, A⁆) rfl
    have h1 : L ≤ ⁅D, A⁆ := by
      have := Subgroup.commutator_mono hLD (le_refl A)
      rwa [hLperf] at this
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hI0.card_L, hL3])).symm

end CFSG.QuasithinUnique.Setup.Layer
