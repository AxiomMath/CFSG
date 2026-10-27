module

public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.Steps.G3bJR

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

namespace G3b

theorem eq_of_stronglyClosed {L : Type*} [Group L] {A T : Subgroup L} (hAT : A ≤ T)
    (hA : A ≠ ⊥) (hcl : IsStronglyClosedIn A T ⊤) (hexp : ∀ x ∈ T, x ^ 2 = 1)
    (hconj : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y) : A = T := by
  refine le_antisymm hAT fun t ht => ?_
  by_cases ht1 : t = 1
  · rw [ht1]
    exact A.one_mem
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha2 : orderOf (a : L) = 2 :=
    orderOf_eq_prime (hexp a (hAT a.2)) (fun h => ha1 (Subtype.ext h))
  have ht2 : orderOf t = 2 := orderOf_eq_prime (hexp t ht) ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj _ _ ha2 ht2)
  have h := hcl a a.2 c⁻¹ (Subgroup.mem_top _) (by rwa [inv_inv, hc])
  rwa [inv_inv, hc] at h

noncomputable def quotientCenterEquiv {L : Type*} [Group L] (hZ : Subgroup.center L = ⊥) :
    L ⧸ Subgroup.center L ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

end G3b

open G3b

theorem G34
    : S_G34 := by
  intro L _ _ _ hII A hA hA1
  classical
  have hall : Subgroup.center L = ⊤ → ∀ x : L ⧸ Subgroup.center L, x = 1 := by
    intro h x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.eq_one_iff, h]
    exact Subgroup.mem_top y
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      rcases hII.2 with ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e0⟩⟩ | hJRq
      · obtain ⟨a, b, hab⟩ := psl2_exists_mul_ne_mul (GaloisField p f)
          (by rw [GaloisField.card p f hf.ne']; omega)
        apply hab
        have ha : a = 1 := by rw [← e0.apply_symm_apply a, hall h (e0.symm a), map_one]
        have hb : b = 1 := by rw [← e0.apply_symm_apply b, hall h (e0.symm b), map_one]
        rw [ha, hb]
      · have : IsSimpleGroup (L ⧸ Subgroup.center L) := hJRq.1
        obtain ⟨x, y, hxy⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
        exact hxy ((hall h x).trans (hall h y).symm)
  have hnonab : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro g
      exact h g x
    obtain ⟨x, y, hxy⟩ := exists_pair_ne L
    have h1 : ∀ z : L, z = 1 := fun z => by
      have hz : z ∈ Subgroup.center L := htop ▸ Subgroup.mem_top z
      rwa [hZ, Subgroup.mem_bot] at hz
    exact hxy ((h1 x).trans (h1 y).symm)
  set eZ := quotientCenterEquiv hZ with heZ
  have hL2e : IsGoldL2 L → ∃ p f : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f)) := by
    rintro ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e0⟩⟩
    exact ⟨p, f, hp, hpodd, hf, h5, h8, ⟨eZ.symm.trans e0⟩⟩
  have hJRe : IsGoldJR L → IsTypeJR L := fun h => IsTypeJR.of_mulEquiv eZ h
  obtain ⟨-, hAab, T, hT, hAT, hcl, -⟩ := hA
  let TS : Sylow 2 L :=
    { toSubgroup := T
      isPGroup' := hT.2.1
      is_maximal' := fun {Q} hQ hTQ => hT.2.2 Q le_top hQ hTQ }
  have hTS : (TS : Subgroup L) = T := rfl
  have hgen : (∀ x ∈ T, x ^ 2 = 1) ∧
      ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
    rcases hII.2 with hL2 | hJRq
    · obtain ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩ := hL2e hL2
      have hK := sylow_isKleinFour_of_mulEquiv e hpodd hf h8 TS
      refine ⟨fun x hx => ?_, isConj_of_mulEquiv' e hpodd hf⟩
      have h := @IsKleinFour.mul_self _ _ hK ⟨x, hx⟩
      rw [pow_two]
      exact congrArg Subtype.val h
    · have hJR := hJRe hJRq
      obtain ⟨hel, -⟩ := hJR.sylow_two_of_nonabelian hnonab TS
      exact ⟨fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := T) x hx,
        fun x y hx hy => hJR.isConj_of_orderOf_eq_two hx hy⟩
  have hAT' : A = T := eq_of_stronglyClosed hAT hA1 hcl hgen.1 hgen.2
  subst hAT'
  have hord : ∀ a ∈ A, a ≠ 1 → orderOf a = 2 := fun a ha ha1 =>
    orderOf_eq_prime (hgen.1 a ha) ha1
  refine ⟨hT, ?_, ?_, ?_⟩
  ·
    intro hL2
    obtain ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩ := hL2e hL2
    refine ⟨normalizer_sylow_mulEquiv_of_mulEquiv e hpodd hf h8 TS, ?_⟩
    intro p' f' _ hf' ⟨e'⟩ a ha ha1
    have hodd : (p' ^ f' % 4 = 1 ∨ p' ^ f' % 4 = 3) → Odd p' := by
      intro h4
      rcases Nat.even_or_odd p' with hev | hodd
      · exfalso
        have h2 : 2 ∣ p' ^ f' := dvd_trans (even_iff_two_dvd.mp hev) (dvd_pow_self p' hf'.ne')
        omega
      · exact hodd
    exact ⟨fun h4 => (centralizer_dihedral_of_mulEquiv e' (hodd (Or.inl h4)) hf'
        (hord a ha ha1)).1 h4,
      fun h4 => (centralizer_dihedral_of_mulEquiv e' (hodd (Or.inr h4)) hf'
        (hord a ha ha1)).2 h4⟩
  ·
    intro hJRq
    obtain ⟨h21, hnab, heq, hcyc⟩ := jr_normalizer_facts (hJRe hJRq) hnonab TS
    exact ⟨heq, hcyc, h21, hnab⟩
  ·
    intro a ha ha1
    rcases hII.2 with hL2 | hJRq
    · obtain ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩ := hL2e hL2
      by_cases h11 : 11 ≤ p ^ f
      · exact Or.inl (centralizer_isCoatom_of_mulEquiv e hpodd hf h11 h8 (hord a ha ha1))
      · have hq5 : p ^ f = 5 := by omega
        exact Or.inr (five_facts_of_mulEquiv e hpodd hf hq5 TS ha ha1)
    · exact Or.inl ((hJRe hJRq).2.2 a (hord a ha ha1)).1

end CFSG.Goldschmidt
