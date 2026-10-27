module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE8
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Weyl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.StandardType.NoOffRest

local instance y6FactFiveFix : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem card_centralizer_lt_sq_of_automizer
    {C : Type*} [Group C] {lam : ZMod 5} (hlam : lam * lam = -1)
    (ι : Multiplicative (eigE8 5 lam) →* C) (hι : Function.Injective ι) {a : C}
    (hu : ∃ u : centE8W, ∀ s : eigE8 5 lam,
      a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd (eigPerm 5 lam u s)))
    (ha5 : a ^ 5 = 1) (hnc : ∃ x ∈ ι.range, a * x ≠ x * a) :
    Nat.card {x : ι.range // a * (x : C) = (x : C) * a} < 5 ^ 2 := by
  classical
  obtain ⟨u, hu⟩ := hu
  have hiter : ∀ k : ℕ, ∀ s : eigE8 5 lam,
      ι (Multiplicative.ofAdd (((eigPerm 5 lam u) ^ k) s)) =
        a ^ k * ι (Multiplicative.ofAdd s) * (a ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
        intro s
        rw [pow_succ', Equiv.Perm.mul_apply, ← hu (((eigPerm 5 lam u) ^ k) s), ih s, pow_succ']
        group
  have hρ5 : (eigPerm 5 lam u) ^ 5 = 1 := by
    refine Equiv.ext fun s => ?_
    have h := hiter 5 s
    rw [ha5] at h
    simp at h
    simpa using hι h
  have hu5 : u ^ 5 = 1 := by
    apply eigPerm_injective hlam
    rw [map_pow, hρ5, map_one]
  have hu1 : u ≠ 1 := by
    intro hu1
    obtain ⟨x, hxmem, hxnc⟩ := hnc
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hxmem
    refine hxnc ?_
    rw [← hs]
    have h := hu (Multiplicative.toAdd s)
    rw [hu1] at h
    simp only [map_one, Equiv.Perm.one_apply, ofAdd_toAdd] at h
    exact (mul_inv_eq_iff_eq_mul).mp h
  have hfix_lt : Nat.card {v : eigE8 5 lam // ∀ b ∈ Subgroup.zpowers u, eigPerm 5 lam b v = v} <
      5 ^ 2 := by
    refine lt_of_le_of_lt (card_fix_eigPerm_le (Subgroup.mem_zpowers u)) ?_
    have h1 := finrank_eig_fix_le_one hlam u.2 (by simpa using congrArg Subtype.val hu5)
      (fun h => hu1 (Subtype.ext h))
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) h1) (by norm_num)
  let f : {x : ι.range // a * (x : C) = (x : C) * a} →
      {v : eigE8 5 lam // ∀ b ∈ Subgroup.zpowers u, eigPerm 5 lam b v = v} :=
    fun x =>
      let s := Classical.choose (MonoidHom.mem_range.mp x.1.2)
      have hs : ι s = (x.1 : C) := Classical.choose_spec (MonoidHom.mem_range.mp x.1.2)
      ⟨Multiplicative.toAdd s, by
        have hcomm : a * ι (Multiplicative.ofAdd (Multiplicative.toAdd s)) =
            ι (Multiplicative.ofAdd (Multiplicative.toAdd s)) * a := by
          rw [ofAdd_toAdd, hs]
          exact x.2
        have hρ : eigPerm 5 lam u (Multiplicative.toAdd s) = Multiplicative.toAdd s := by
          have h := hu (Multiplicative.toAdd s)
          have h1 : ι (Multiplicative.ofAdd (eigPerm 5 lam u (Multiplicative.toAdd s))) =
              ι (Multiplicative.ofAdd (Multiplicative.toAdd s)) := by
            rw [← h, hcomm]
            group
          exact hι h1
        intro b hb
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [map_zpow]
        exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hρ k⟩
  haveI : Finite ι.range := (Set.finite_range ι).to_subtype
  have hf_inj : Function.Injective f := by
    intro x x' hxx
    have hs : Classical.choose (MonoidHom.mem_range.mp x.1.2) =
        Classical.choose (MonoidHom.mem_range.mp x'.1.2) := by
      have hval := congrArg Subtype.val hxx
      exact Multiplicative.toAdd.injective hval
    apply Subtype.ext
    apply Subtype.ext
    rw [← Classical.choose_spec (MonoidHom.mem_range.mp x.1.2),
      ← Classical.choose_spec (MonoidHom.mem_range.mp x'.1.2), hs]
  exact lt_of_le_of_lt (Nat.card_le_card_of_injective f hf_inj) hfix_lt

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
