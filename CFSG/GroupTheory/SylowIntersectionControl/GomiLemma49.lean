module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.PermSylowTwo.Alt
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltInner

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def GomiLemma49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (IsChevTwo G ∨ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) →
    ∀ (S : Sylow 2 G) (α : MulAut G), Odd (orderOf α) →
      (∀ s ∈ (S : Subgroup G), α s = s) → α = 1

private theorem isSylowTwoOf_top_of_sylow_aux {G : Type} [Group G] [Finite G] (S : Sylow 2 G) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup G) ⊤ := by
  refine ⟨le_top, S.isPGroup', ?_⟩
  rw [show ((S : Subgroup G).subgroupOf ⊤).index = (S : Subgroup G).index from
    Subgroup.relIndex_top_right _]
  exact S.not_dvd_index

private theorem pow_apply_eq_of_fix {G : Type} [Group G] {T : Set G} {α : MulAut G}
    (hfix : ∀ s ∈ T, α s = s) (m : ℕ) : ∀ s ∈ T, (α ^ m) s = s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s hs
    rw [pow_succ, MulAut.mul_apply, hfix s hs]
    exact ih s hs

private theorem eq_one_of_alt {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 6 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) (S : Sylow 2 G) (α : MulAut G) (hodd : Odd (orderOf α))
    (hfix : ∀ s ∈ (S : Subgroup G), α s = s) : α = 1 := by
  by_contra hα
  have hne : orderOf α ≠ 1 := fun h => hα (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨c, hc⟩ := hpd
    omega
  set β : MulAut G := α ^ (orderOf α / p)
  have hβord : orderOf β = p := orderOf_pow_orderOf_div hodd.pos.ne' hpd
  have hβfix : ∀ s ∈ (S : Subgroup G), β s = s := pow_apply_eq_of_fix hfix _
  have hβp : MulAut.congr e β ^ p = 1 := by
    rw [← map_pow, ← hβord, pow_orderOf_eq_one, map_one]
  obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Inner.exists_unique_inner hp hp2
    (by omega) hβp
  have hβy : ∀ g, β g = e.symm x * g * (e.symm x)⁻¹ := by
    intro g
    apply e.injective
    have h := DFunLike.congr_fun hx (e g)
    simpa using h
  have hcent : e.symm x ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := hβy s
    rw [hβfix s hs] at h
    calc s * e.symm x = e.symm x * s * (e.symm x)⁻¹ * e.symm x := by rw [← h]
      _ = e.symm x * s := by group
  have hyS : e.symm x ∈ (S : Subgroup G) :=
    PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt hn (Subgroup.topEquiv.trans e)
      (isSylowTwoOf_top_of_sylow_aux S)
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, Subgroup.centralizer_le_normalizer _ hcent⟩)
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨e.symm x, hyS⟩
  have hyk : e.symm x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hβconj : β = MulAut.conj (e.symm x) := by
    ext g
    exact hβy g
  have hβk : β ^ 2 ^ k = 1 := by
    rw [hβconj, ← map_pow, hyk, map_one]
  have hpk : p ∣ 2 ^ k := hβord ▸ orderOf_dvd_of_pow_eq_one hβk
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpk))

theorem gomiLemma49_of_chev (h : GomiLemma49Chev) : GomiLemma49 := by
  intro G _ _ hG hcase S α hodd hfix
  rcases hcase with hchev | ⟨n, hn, ⟨e⟩⟩
  · exact h G hG hchev S α hodd hfix
  · rcases Nat.lt_or_ge n 6 with hn6 | hn6
    · obtain rfl : n = 5 := by omega
      exact h G hG (Or.inr (Or.inl ⟨5, Or.inl rfl, ⟨e⟩⟩)) S α hodd hfix
    · exact eq_one_of_alt hn6 e S α hodd hfix

end CFSG.GroupTheory
