module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem actor_inf_centralizer_eq_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    B ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  have uc54_pRank_le_one_of_cyclic {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
      (P : Subgroup X) (hP : IsCyclic P) : CFSG.Open.pRank p P ≤ 1 := by
    classical
    unfold CFSG.Open.pRank
    apply csSup_le'
    rintro k ⟨E, hEP, ⟨-, hexp⟩, hcard⟩
    have hEc : IsCyclic (E.subgroupOf P) := Subgroup.isCyclic _
    have hcardE : Nat.card (E.subgroupOf P) = p ^ k := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
    haveI : Fintype (E.subgroupOf P) := Fintype.ofFinite _
    have hle := IsCyclic.card_pow_eq_one_le (α := E.subgroupOf P) (n := p) hp.pos
    have hall : (Finset.univ.filter fun x : E.subgroupOf P => x ^ p = 1) = Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      apply Subtype.ext
      apply Subtype.ext
      simpa using hexp (x : X) (Subgroup.mem_subgroupOf.1 x.2)
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardE] at hle
    by_contra hk
    have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    have h3 : p ^ 2 ≤ p := le_trans h2 hle
    have := hp.two_le
    nlinarith
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hBb, hCb⟩ := Subgroup.mem_inf.1 hb
  rw [Subgroup.mem_bot]
  by_contra hb1
  have hc := h51.cyclic_centralizer b hBb hb1
  have hPle : P ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hCb ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hCb x hx).symm
  rw [inf_eq_left.2 hPle] at hc
  have h1 := uc54_pRank_le_one_of_cyclic h51.setting.prime P hc
  have h2 := h53.rank_gt
  omega

end Section5

end CFSG.LocalAnalysis.RankThreeUC
