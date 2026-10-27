module

public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingIsolated

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem quaternionGroup_eq_of_sq_eq_one {n : ℕ} (hn : 1 ≤ n) {g : QuaternionGroup n}
    (hg : g ^ 2 = 1) : g = 1 ∨ g = QuaternionGroup.a n := by
  have : NeZero n := ⟨by omega⟩
  rcases g with i | i
  · rw [pow_two, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero] at hg
    have hi : i + i = 0 := QuaternionGroup.a.inj hg
    have hval : (2 * i.val) % (2 * n) = 0 := by
      have h := congrArg ZMod.val hi
      rw [ZMod.val_add, ZMod.val_zero] at h
      rw [two_mul]
      exact h
    have hlt : i.val < 2 * n := ZMod.val_lt i
    have hcases : i.val = 0 ∨ i.val = n := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact Or.inl h
      · right
        have h2 : 2 * i.val < 2 * (2 * n) := by omega
        have h3 : 2 * i.val = 2 * n := by
          obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hval
          have hc1 : c = 1 := by
            rcases c with _ | _ | c
            · omega
            · rfl
            · nlinarith
          rw [hc1, mul_one] at hc
          exact hc
        omega
    rcases hcases with h | h
    · left
      rw [← QuaternionGroup.a_zero]
      congr 1
      exact (ZMod.val_eq_zero i).mp h
    · right
      congr 1
      rw [← ZMod.natCast_zmod_val i, h]
  · exfalso
    rw [QuaternionGroup.xa_sq] at hg
    rw [← QuaternionGroup.a_zero] at hg
    have h := QuaternionGroup.a.inj hg
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at h2
    omega

variable {X : Type*} [Group X]

theorem commuting_involutions_eq_of_cyclic_or_quaternion [Finite X]
    (hS : ∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))))
    {a b : X} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : Commute a b) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have haa : a * a = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ha).1
  have hbb : b * b = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hb).1
  have ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha).2
  have hb1 : b ≠ 1 := (orderOf_eq_prime_iff.mp hb).2
  let E := commutingPairSubgroup a b haa hbb hab
  have hEsq : ∀ x : E, x ^ 2 = 1 := fun x => Subtype.ext (commutingPairSubgroup_sq x.property)
  have hE2 : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact hEsq x⟩
  obtain ⟨S, hES⟩ := hE2.exists_le_sylow
  have haE : a ∈ E := mem_commutingPairSubgroup.mpr (Or.inr (Or.inl rfl))
  have hbE : b ∈ E := mem_commutingPairSubgroup.mpr (Or.inr (Or.inr (Or.inl rfl)))
  rcases hS S with hcyc | ⟨r, hr, ⟨e⟩⟩
  · let E' : Subgroup (S : Subgroup X) := E.subgroupOf (S : Subgroup X)
    have hcard : Nat.card E' = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv,
        commutingPairSubgroup_card ha1 hb1 hne]
      norm_num
    have hexp : Monoid.exponent E' ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact commutingPairSubgroup_sq (show ((x : (S : Subgroup X)) : X) ∈ E from x.property)
    rw [IsCyclic.exponent_eq_card, hcard] at hexp
    exact absurd hexp (by decide)
  · have hn : 1 ≤ 2 ^ (r - 2) := Nat.one_le_two_pow
    let a' : (S : Subgroup X) := ⟨a, hES haE⟩
    let b' : (S : Subgroup X) := ⟨b, hES hbE⟩
    have hsq : ∀ y : (S : Subgroup X), (y : X) ^ 2 = 1 → (y : X) ≠ 1 →
        e y = QuaternionGroup.a (2 ^ (r - 2) : ℕ) := by
      intro y hy hy1
      rcases quaternionGroup_eq_of_sq_eq_one hn (g := e y) (by
        rw [← map_pow, show y ^ 2 = 1 from Subtype.ext hy, map_one]) with h | h
      · exact absurd (Subtype.ext_iff.mp (e.injective (h.trans (map_one e).symm))) hy1
      · exact h
    have hea := hsq a' (by rw [pow_two]; exact haa) ha1
    have heb := hsq b' (by rw [pow_two]; exact hbb) hb1
    exact hne (congrArg Subtype.val (e.injective (hea.trans heb.symm)))

theorem exists_noncommuting_of_stronglyEmbedded {M : Subgroup X}
    (hM : fusionStronglyEmbedded M) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  have hc : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra h
    exact hcomm ⟨a, b, h⟩
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ M := by
    by_contra h
    exact hM.1 (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
  have hodd := hM.2.2 g hg
  have hmap : M.map (MulAut.conj g⁻¹).toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * y * g⁻¹⁻¹ ∈ M
      rw [inv_inv, hc g⁻¹ y, mul_assoc, inv_mul_cancel, mul_one]
      exact hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hc g⁻¹ x, mul_assoc, inv_mul_cancel, mul_one]
  rw [hmap, inf_idem] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hM.2.1

theorem commutator_eq_top_of_bender [Finite X] (hB : fusionIsBenderGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : commutator X = ⊤ := by
  have hsimple := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hab (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top a)) b
      (Subgroup.mem_top b)).symm
  · exact h

theorem fusionIsBenderGroup_of_stronglyEmbedded [Finite X] (hO : CFSG.oddCore X = ⊥)
    (hgen : ∀ N : Subgroup X, N.Normal → Odd N.index → N = ⊤)
    {M : Subgroup X} (hM : fusionStronglyEmbedded M)
    {a b : X} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : Commute a b) (hne : a ≠ b) :
    fusionIsBenderGroup X := by
  rcases CFSG.Open.bender_strongly_embedded_normal_series X M hM with
    h1 | ⟨M₀, N, hM₀, hN, hsub, -, hodd, hidx, hB⟩
  · exact absurd (commuting_involutions_eq_of_cyclic_or_quaternion h1 ha hb hab) hne
  · have hM₀bot : M₀ = ⊥ := by
      have hle : M₀ ≤ CFSG.oddCore X := le_sSup ⟨hM₀, hodd⟩
      rw [hO] at hle
      exact le_bot_iff.mp hle
    have hNtop : N = ⊤ := hgen N hN hidx
    subst hM₀bot
    subst hNtop
    exact CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)) hB

end CFSG.ComponentClassification.AschbacherStrongEmbedding
