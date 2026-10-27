module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeSigma
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.AbelianTransfer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

@[expose] def I294Large.CommOrRank (r : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  (∀ S : Sylow r G, IsMulCommutative (S : Subgroup G)) ∨
    r ≤ CFSG.Open.pRank r (⊤ : Subgroup G)

namespace I294Large

variable {r : ℕ}

theorem CommOrRank.of_sylow_sigmaModel (hr : r.Prime) {G : Type} [Group G] [Finite G]
    {e a N : ℕ} (ha : 1 ≤ a) (h : ∀ P : Sylow r G, Nonempty (P ≃* sigmaModel r e a N)) :
    CommOrRank r G := by
  by_cases hN : N / e < r
  · exact Or.inl (sylow_isMulCommutative_of_sigmaModel_of_lt hr hN h)
  · exact Or.inr (I294CrossLarge.le_pRank_of_sylow_sigmaModel hr ha (by omega) h)

theorem CommOrRank.of_mulEquiv (hr : r.Prime) {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (h : CommOrRank r G) : CommOrRank r H := by
  haveI : Fact r.Prime := ⟨hr⟩
  rcases h with h | h
  · exact Or.inl (sylow_comm_of_surjective e.toMonoidHom e.surjective h)
  · exact Or.inr (by rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e])

theorem le_of_isPGroup_of_not_dvd_index (hr : r.Prime) {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : ¬ r ∣ N.index) {U : Subgroup G} (hU : IsPGroup r U) :
    U ≤ N := by
  intro u hu
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have hk' : u ^ (r ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk (s := N) u) ∣ r ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk (s := N) u) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (r ^ k) N.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hN)
  have h3 : orderOf (QuotientGroup.mk (s := N) u) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff u).1 h3

theorem CommOrRank.of_normal_coprime_index (hr : r.Prime) {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : ¬ r ∣ N.index) (h : CommOrRank r G) :
    CommOrRank r N := by
  haveI : Fact r.Prime := ⟨hr⟩
  rcases h with h | h
  · exact Or.inl (sylow_comm_of_subgroup N h)
  · right
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt (⊤ : Subgroup G)
    have hEp : IsPGroup r E := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hE.2 g g.2⟩
    have hEN : E ≤ N := le_of_isPGroup_of_not_dvd_index hr N hN hEp
    have hmap : (E.comap N.subtype).map N.subtype = E :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hEN)
    have hEc' : IsElemAbelian r (E.comap N.subtype) :=
      (isElemAbelian_map_iff_of_injective N.subtype N.subtype_injective _).1 (by rw [hmap]; exact hE)
    have hcard : Nat.card (E.comap N.subtype) = r ^ CFSG.Open.pRank r (⊤ : Subgroup G) := by
      rw [← Subgroup.card_map_of_injective N.subtype_injective, hmap]
      exact hEc
    exact h.trans (CFSG.SectionRank.le_pRank hr.one_lt (le_top : E.comap N.subtype ≤ ⊤) hEc' hcard)

theorem injOn_of_isPGroup_of_not_dvd_ker (hr : r.Prime) {G K : Type} [Group G] [Finite G] [Group K]
    (π : G →* K) (hker : ¬ r ∣ Nat.card π.ker) {U : Subgroup G} (hU : IsPGroup r U) :
    Set.InjOn π (U : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hU
  have hcop : Nat.Coprime (Nat.card U) (Nat.card π.ker) := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hr).2 hker)
  have hdis : Disjoint U π.ker := Subgroup.disjoint_of_coprime_natCard hcop
  intro a ha b hb hab
  have h1 : a⁻¹ * b = 1 := by
    refine Subgroup.disjoint_def.1 hdis (U.mul_mem (U.inv_mem ha) hb) ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  exact inv_mul_eq_one.1 h1

theorem CommOrRank.of_surjective_coprime_ker (hr : r.Prime) {G K : Type} [Group G] [Finite G]
    [Group K] [Finite K] (π : G →* K) (hπ : Function.Surjective π) (hker : ¬ r ∣ Nat.card π.ker)
    (h : CommOrRank r G) : CommOrRank r K := by
  haveI : Fact r.Prime := ⟨hr⟩
  rcases h with h | h
  · exact Or.inl (sylow_comm_of_surjective π hπ h)
  · right
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt (⊤ : Subgroup G)
    have hEp : IsPGroup r E := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hE.2 g g.2⟩
    have hinj : Set.InjOn π (E : Set G) := injOn_of_isPGroup_of_not_dvd_ker hr π hker hEp
    have hcard : Nat.card (E.map π) = r ^ CFSG.Open.pRank r (⊤ : Subgroup G) :=
      (Nat.card_image_of_injOn hinj).trans hEc
    exact h.trans (CFSG.SectionRank.le_pRank hr.one_lt (le_top : E.map π ≤ ⊤)
      (CFSG.Open.IsElemAbelian.map hE π) hcard)

end I294Large

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
