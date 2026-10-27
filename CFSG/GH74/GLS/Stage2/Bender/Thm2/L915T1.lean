module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915T0
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915C8

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1

@[expose] def Prop9_5Tail2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ), Ctx9 G z k S M p →
    ∀ (J : Subgroup G) (n : ℕ), IsQuasisimple ↥J → z ∈ J →
      (∀ c ∈ J, (∀ g ∈ J, c * g = g * c) → c * c = 1 → c = 1) → 2 ≤ n →
      LieModel (↥J ⧸ center ↥J) .PSL 3 p n → Op p M ≤ J → IsElementaryAbelian p ↥(Op p M) →
      Nat.card ↥(Op p M) = p ^ (2 * n) → Op p M ⊓ Cen z = ⊥ →
      (∀ x ∈ Op p M, x ≠ 1 → ∀ y ∈ Op p M, y ≠ 1 → ∃ c ∈ J ⊓ Cen z, c * x * c⁻¹ = y) →
      M ≤ normalizer (J : Set G)

namespace L915

section N1

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem exists_elemAbelian_of_three_le_pRank {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (hB : 3 ≤ CFSG.pRank 2 ↥B) : ∃ E : Subgroup ↥B, IsElementaryAbelian 2 ↥E ∧ 2 ^ 3 ≤ Nat.card ↥E := by
  by_contra h
  have h' : ∀ E : Subgroup ↥B, IsElementaryAbelian 2 ↥E → Nat.card ↥E < 2 ^ 3 :=
    fun E hE => lt_of_not_ge fun h3 => h ⟨E, hE, h3⟩
  have hne : {r : ℕ | ∃ E : Subgroup ↥B, IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 2 ^ r}.Nonempty :=
    ⟨0, ⊥, { toIsMulCommutative := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
             exponent_dvd_p := by rw [Monoid.exp_eq_one_of_subsingleton]; exact one_dvd 2 },
      by rw [Subgroup.card_bot, pow_zero]⟩
  have hle : CFSG.pRank 2 ↥B ≤ 2 := by
    refine csSup_le hne ?_
    rintro r ⟨E, hE, hcard⟩
    by_contra hr
    have := h' E hE
    rw [hcard] at this
    exact absurd (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2) |>.1 this) (by omega)
  omega

theorem Ctx9.cent_Op_le (hC : Ctx9 G z k S M p) {e : G} (heM : e ∈ M)
    (hcent : ∀ x ∈ Op p M, e * x * e⁻¹ = x) : e ∈ Op p M := by
  have hF : generalizedFitting ↥M = pCore p ↥M := by
    have h1 := hC.fstar
    rw [Fs_def, Op_eq_map] at h1
    exact Subgroup.map_injective M.subtype_injective h1
  have hmem : (⟨e, heM⟩ : ↥M) ∈ centralizer (generalizedFitting ↥M : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hF] at hg
    have hgO : (g : G) ∈ Op p M := by
      rw [Op_eq_map]
      exact ⟨g, hg, rfl⟩
    have := hcent g hgO
    apply Subtype.ext
    show (g : G) * e = e * (g : G)
    have h2 : e * (g : G) * e⁻¹ = g := this
    calc (g : G) * e = (e * (g : G) * e⁻¹) * e := by rw [h2]
      _ = e * (g : G) := by group
  have h3 := centralizer_generalizedFitting_le ↥M hmem
  rw [hF] at h3
  rw [Op_eq_map]
  exact ⟨⟨e, heM⟩, h3, rfl⟩

theorem false_of_n_one (hC : Ctx9 G z k S M p) (hel : IsElementaryAbelian p ↥(Op p M))
    (hcard : Nat.card ↥(Op p M) = p ^ 2) (hPz : Op p M ⊓ Cen z = ⊥) : False := by
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 3 ≤ CFSG.pRank 2 ↥S := Final.Thm4.three_le_pRank_S hC.ctx
  obtain ⟨E₀, hE₀, hcard8⟩ :=
    exists_elemAbelian_of_three_le_pRank h3
  have hEel : IsElementaryAbelian 2 ↥(E₀.map S.subtype) := IsElementaryAbelian.map_subtype
  set E : Subgroup G := E₀.map S.subtype with hE
  have hES : E ≤ S := Subgroup.map_subtype_le _
  have hcardE : Nat.card ↥E = Nat.card ↥E₀ :=
    Subgroup.card_map_of_injective S.subtype_injective
  have hEM : ∀ e ∈ E, e ∈ M := fun e he => hC.S_le_M (hES he)
  have hsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e he
    rwa [pow_two] at this
  have hnorm : ∀ e ∈ E, ∀ x ∈ Op p M, e * x * e⁻¹ ∈ Op p M := fun e he x hx =>
    (mem_normalizer_iff.mp (le_normalizer_Op' p M (hEM e he)) x).mp hx
  have hfaith : ∀ e ∈ E, (∀ x ∈ Op p M, e * x * e⁻¹ = x) → e = 1 := by
    intro e he hcent
    have h1 : e ∈ Op p M := Ctx9.cent_Op_le hC (hEM e he) hcent
    have h2 : e ∈ Cen z := hC.ctx.S_le_Cen (hES he)
    have h3 : e ∈ Op p M ⊓ Cen z := ⟨h1, h2⟩
    rw [hPz, Subgroup.mem_bot] at h3
    exact h3
  have := card_le_four_of_faithful_p_sq hp hp2 (P := Op p M) (E := E) hcard hnorm hsq hfaith
  have h8 : 2 ^ 3 ≤ Nat.card ↥E₀ := hcard8
  omega

end N1

end L915

theorem prop9_5Tail_of_tail2 (h : Prop9_5Tail2) : Prop9_5Tail := by
  intro G _ _ z k S M p hC J n hJ hzJ hnoc hn hLie hPJ hel hcard hPz htr
  by_cases h2 : 2 ≤ n
  · exact h G z k S M p hC J n hJ hzJ hnoc h2 hLie hPJ hel hcard hPz htr
  · have hn1 : n = 1 := by omega
    subst hn1
    exact (L915.false_of_n_one hC hel (by simpa using hcard) hPz).elim

theorem lemma9_15_of_leaves'' (h43E : Prop4_3E) (h34 : Leaf_Prop34) (hTail : Prop9_5Tail2)
    (h911 : Prop9_11Core) : Lemma9_15 :=
  lemma9_15_of_leaves' h43E h34 (prop9_5Tail_of_tail2 hTail) h911

end CFSG.GH74.GLS.Stage2.Bender.Thm2
