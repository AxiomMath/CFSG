module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Aux

private theorem conjugate_map_equiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (L : Subgroup Y) (s : Y) :
    conjugate (L.map e.toMonoidHom) (e s) = (conjugate L s).map e.toMonoidHom := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem normal_le_center_or_sup_center {G : Type*} [Group G]
    (hs : IsSimpleGroup (G ⧸ center G)) {N : Subgroup G} (hN : N.Normal) :
    N ≤ center G ∨ N ⊔ center G = ⊤ := by
  have := hN.map (QuotientGroup.mk' (center G)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center G))) with
    h0 | h1
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
  · right
    have := Subgroup.comap_map_eq (QuotientGroup.mk' (center G)) N
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm

private theorem false_of_commuting_pair {G : Type*} [Group G] (hs : IsSimpleGroup (G ⧸ center G))
    {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : ¬ A ≤ center G)
    (hB : ¬ B ≤ center G) (hN : (A ⊔ B).Normal) : False := by
  have hAc : A ≤ centralizer (B : Set G) := fun a ha b hb => (hAB a ha b hb).symm
  rcases normal_le_center_or_sup_center hs hN with h1 | h1
  · exact hA (le_sup_left.trans h1)
  · have hAn : A.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      refine top_unique ?_
      rw [← h1]
      refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
      · exact (Subgroup.le_centralizer_iff.mp hAc).trans (Subgroup.centralizer_le_normalizer _)
      · exact (Subgroup.center_le_centralizer _).trans (Subgroup.centralizer_le_normalizer _)
    rcases normal_le_center_or_sup_center hs hAn with h2 | h2
    · exact hA h2
    · refine hB fun b hb => ?_
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ A ⊔ center G := h2 ▸ Subgroup.mem_top g
      have hle : A ⊔ center G ≤ centralizer (B : Set G) :=
        sup_le hAc (Subgroup.center_le_centralizer _)
      exact (Subgroup.mem_centralizer_iff.mp (hle hg) b hb).symm

private theorem exists_noncomm_of_isQuasisimple {Y : Type*} [Group Y] {L : Subgroup Y}
    (hL : IsQuasisimple ↥L) : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hL
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, a.2, b, b.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

private theorem not_subgroupOf_le_center {Y : Type*} [Group Y] {K L : Subgroup Y} (hLK : L ≤ K)
    (hL : IsQuasisimple ↥L) : ¬ L.subgroupOf K ≤ center ↥K := by
  intro hle
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isQuasisimple hL
  have h1 : (⟨a, hLK ha⟩ : ↥K) ∈ center ↥K := hle ha
  have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨b, hLK hb⟩)
  exact hab h2.symm

end Aux

theorem PairData.of_equiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (h : PairData Y) (e : Y ≃* Y') : PairData Y' := by
  obtain ⟨L₁, L₂, hne, hcomps, hcomm, s, hs1, hs2⟩ := h.exists_pair
  refine ⟨?_, ?_, L₁.map e.toMonoidHom, L₂.map e.toMonoidHom, ?_, ?_, ?_, e s, ?_, ?_⟩
  · rw [← pPrimeCore_map_iso 2 e, h.oddCore, Subgroup.map_bot]
  · rw [← CFSG.QuasithinUnique.Setup.Layer.Actor.generalizedFitting_map e,
      ← CFSG.QuasithinUnique.Setup.Layer.Actor.layer_map e, h.fs_eq]
  · exact fun h' => hne (Subgroup.map_injective e.injective h')
  · rw [← (CFSG.LocalCores.component_isomorphism e).2.image_eq, hcomps, Set.image_pair]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [← map_mul, hcomm a ha b hb]
  · rw [conjugate_map_equiv, hs1]
  · rw [conjugate_map_equiv, hs2]

section

variable {Y : Type} [Group Y] [Finite Y]

theorem PairData.odd_mem_fitting (h : PairData Y) {x : Y} (hx : x ∈ fittingSubgroup Y)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hnil, hnorm, -⟩ := CFSG.LocalCores.fitting_nilpotent (G := Y)
  have hP : IsPGroup 2 (fittingSubgroup Y) := isPGroup_of_nilpotent_normal _ hnorm hnil h.oddCore
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem PairData.comm_layer_ne_bot (h : PairData Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup Y} (hXp : IsPGroup p ↥X) (hX : X ≠ ⊥) : ⁅layer Y, X⁆ ≠ ⊥ := by
  intro hcomm
  have : Fact p.Prime := ⟨hp⟩
  have h1 : X ≤ centralizer ((generalizedFitting Y : Subgroup Y) : Set Y) := by
    rw [h.fs_eq]
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have h2 : X ≤ fittingSubgroup Y :=
    h1.trans (CFSG.GH74.GLS.Stage2.Bender.Thm1.centralizer_generalizedFitting_le_fitting' Y)
  have hnt : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX
  obtain ⟨n, hn0, hn⟩ := hXp.nontrivial_iff_card.mp hnt
  have hdvd : p ∣ Nat.card ↥X := hn ▸ dvd_pow_self p hn0.ne'
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hg1 : g = 1 := Subtype.ext (h.odd_mem_fitting (h2 g.2) (by
    rw [Subgroup.orderOf_coe, hg]
    exact hp.odd_of_ne_two hp2))
  rw [hg1, orderOf_one] at hg
  exact hp.ne_one hg.symm

theorem PairData.false_of_normal_simple (h : PairData Y) {K : Subgroup Y} (hK : K.Normal)
    {x : Y} (hxK : x ∈ K) (hx1 : x ≠ 1) (hxodd : Odd (orderOf x))
    (hsimple : IsSimpleGroup (↥K ⧸ center ↥K)) : False := by
  obtain ⟨L₁, L₂, -, hcomps, hcomm, s, hs1, hs2⟩ := h.exists_pair
  have hc₁ : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup Y | IsComponent K} := by
      rw [hcomps]
      exact Set.mem_insert _ _
    exact this
  have hc₂ : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup Y | IsComponent K} := by
      rw [hcomps]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact this
  have hlayer : layer Y = L₁ ⊔ L₂ := by
    simp only [CFSG.layer.eq_sSup]
    rw [hcomps, sSup_pair]
  have hconj : ∀ A B : Subgroup Y, conjugate A s = B → A ≤ K → B ≤ K := by
    intro A B hAB hAK y hy
    rw [← hAB] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    simpa using hK.conj_mem a (hAK ha) s⁻¹
  have hE : L₁ ⊔ L₂ ≤ K := by
    rcases CFSG.LocalCores.component_normal_subgroup hc₁ hK with h1 | h1
    · exact sup_le h1 (hconj L₁ L₂ hs1 h1)
    · rcases CFSG.LocalCores.component_normal_subgroup hc₂ hK with h2 | h2
      · exact sup_le (hconj L₂ L₁ hs2 h2) h2
      · exfalso
        have hKc : K ≤ centralizer ((generalizedFitting Y : Subgroup Y) : Set Y) := by
          rw [h.fs_eq, hlayer, ← Subgroup.le_centralizer_iff]
          exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2)
        exact hx1 (h.odd_mem_fitting
          (CFSG.GH74.GLS.Stage2.Bender.Thm1.centralizer_generalizedFitting_le_fitting' Y (hKc hxK))
          hxodd)
  refine false_of_commuting_pair hsimple (A := L₁.subgroupOf K) (B := L₂.subgroupOf K)
    (fun a ha b hb => Subtype.ext (hcomm a ha b hb))
    (not_subgroupOf_le_center (le_sup_left.trans hE) hc₁.1)
    (not_subgroupOf_le_center (le_sup_right.trans hE) hc₂.1) ?_
  rw [← Subgroup.subgroupOf_sup (le_sup_left.trans hE) (le_sup_right.trans hE), ← hlayer]
  have := CFSG.LocalCores.layer_characteristic (G := Y)
  exact (inferInstance : (layer Y).Normal).subgroupOf K

end

end CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOver
