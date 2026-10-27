module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

namespace LinEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}

theorem card_sup_zpowers_eq_prime_sq {G : Type} [Group G] [Finite G] (hp : p.Prime)
    {a b : G} (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x)
    (hba : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLa : Nat.card ↥(Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  have hLb : Nat.card ↥(Subgroup.zpowers b) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb hb1
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ p := by
      have hle : Subgroup.zpowers a ⊓ Subgroup.zpowers b ≤ Subgroup.zpowers a := inf_le_left
      have := Subgroup.card_dvd_of_le hle
      rwa [hLa] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hcardinf : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) =
          Nat.card ↥(Subgroup.zpowers a) := by rw [hp', hLa]
      have hLi : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardinf])
      have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := hLi ▸ inf_le_right
      have hR : Subgroup.zpowers b = Subgroup.zpowers a :=
        (Subgroup.eq_of_le_of_card_ge hle (by rw [hLb, hLa])).symm
      exact hba (hR ▸ Subgroup.mem_zpowers b)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers a) (Subgroup.zpowers b) hcomm).1
  rw [hinf, hLa, hLb, Subgroup.card_bot, mul_one] at hprod
  rw [pow_two]
  exact hprod

theorem eq_one_of_mem_center_of_fixed {g : SpecialLinearGroup F V}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup F V)) {v : V} (hv : v ≠ 0)
    (hfix : (g : V ≃ₗ[F] V) v = v) : g = 1 := by
  haveI : Module.Free F V := Module.Free.of_divisionRing F V
  rw [SpecialLinearGroup.mem_center_iff] at hg
  obtain ⟨r, -, hr⟩ := hg
  have hrv : (g : V ≃ₗ[F] V) v = r • v := by
    have h := congrArg (fun f : V →ₗ[F] V => f v) hr
    simpa using h
  have hr1 : r = 1 := by
    have h0 : (r - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hrv, hfix, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  change ((g : V ≃ₗ[F] V) : V →ₗ[F] V) u = u
  have hu : ((g : V ≃ₗ[F] V) : V →ₗ[F] V) u = r • u := by
    have h := congrArg (fun f : V →ₗ[F] V => f u) hr
    simpa using h
  rw [hu, hr1, one_smul]

theorem blockEnd_notMem_zpowers (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E : HypBlocks.Hyperplane A p} (hDE : D ≠ E)
    (hE : HypBlocks.blockSpace A E.1 ≠ ⊥) :
    HypBlocks.blockEnd A hp hpF hA t ht E ∉
      Subgroup.zpowers (HypBlocks.blockEnd A hp hpF hA t ht D) := by
  intro hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
  have hfixD : (HypBlocks.blockEnd A hp hpF hA t ht D : V ≃ₗ[F] V) v = v :=
    HypBlocks.blockEnd_apply_of_mem_block A hp hpF hA t ht (D := D) (E := E) (Ne.symm hDE) hv
  have hpow : ∀ k : ℕ, ((HypBlocks.blockEnd A hp hpF hA t ht D) ^ k) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, hfixD]
  have hzpow : ((HypBlocks.blockEnd A hp hpF hA t ht D) ^ j) v = v := by
    rw [zpow_eq_zpow_emod j (show (HypBlocks.blockEnd A hp hpF hA t ht D) ^ ((p : ℤ)) = 1 by
      rw [zpow_natCast]
      exact HypBlocks.blockEnd_pow A hp hpF hA t ht D)]
    rw [← Int.toNat_of_nonneg (Int.emod_nonneg j (by exact_mod_cast hp.ne_zero)), zpow_natCast]
    exact hpow _
  have h2 : (t E : V ≃ₗ[F] V) v = v := by
    have h := HypBlocks.blockEnd_apply_mem A hp hpF hA t ht E hv
    rw [← hj, hzpow] at h
    exact h.symm
  exact hv0 (HypBlocks.eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht E) hv h2)

theorem inf_center_eq_bot_of_le_Jsub (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D : HypBlocks.Hyperplane A p} (hD : HypBlocks.blockSpace A D.1 ≠ ⊥)
    {Q : Subgroup (SpecialLinearGroup F V)} (hQ : Q ≤ Jsub A hp hpF hA t ht D) :
    Q ⊓ Subgroup.center (SpecialLinearGroup F V) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgQ, hgc⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_bot]
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hfix : (g : V ≃ₗ[F] V) v = v := (mem_Jsub.mp (hQ hgQ)).1 v hv
  exact eq_one_of_mem_center_of_fixed hgc hv0 hfix

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
