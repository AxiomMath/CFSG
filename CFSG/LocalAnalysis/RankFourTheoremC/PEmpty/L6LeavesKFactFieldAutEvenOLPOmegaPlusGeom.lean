module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPOmegaPlusAniso
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.LieType.BorelTits.OrthogonalSingular
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.LieType.BorelTits
open CFSG.Open (StatedProj StatedScalars StatedOmega StatedQuadPlus)

section Abstract

variable {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [Module.Finite F V] (Φ : QuadForm F V) {H : Type*} [Group H] (ρ : H →* Module.End F V)

theorem omegaPlus_eq_bot_of_normalizes_ppd (hinj : Function.Injective ρ)
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (hstar : NoQuotientReflection Φ ρ) {r e : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (he : 3 ≤ e)
    (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m) (hdim : Module.finrank F V = e + 2)
    (hS : Nat.card {v : V // Φ.Q v = 0} ≡ 1 [MOD r]) {g : H} (hgr : g ^ r = 1) (hg1 : g ≠ 1)
    {R : Subgroup H} (hR : IsPGroup 2 R) (hgR : g ∈ Subgroup.normalizer (R : Set H)) :
    R = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite V := Module.finite_of_finite F
  have hflag := le_flagKernel_singFlag 2 hQ hstar R hR
  have hZ0 : singSeq Φ ρ R (Module.finrank F V) ≠ ⊥ := by
    intro h0
    refine hne ((Subgroup.eq_bot_iff_forall R).mpr fun x hx => hinj ?_)
    ext v
    have := (hflag hx).2 (Module.finrank F V) v
      (by rw [singFlag_finrank_succ, h0, Φ.polar.perp_bot]; trivial)
    rw [singFlag_finrank, h0, Submodule.mem_bot, sub_eq_zero] at this
    rw [this, map_one, Module.End.one_apply]
  obtain ⟨z, hzZ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
  have hsing := isTotallySingular_singSeq Φ ρ R (Module.finrank F V)
  have hinv : ∀ v ∈ singSeq Φ ρ R (Module.finrank F V),
      ρ g v ∈ singSeq Φ ρ R (Module.finrank F V) :=
    fun v hv => apply_mem_singSeq hQ R _ hgR hv
  have hfin := hsing.two_mul_finrank_le
  have hgpow : (ρ g) ^ r = 1 := by rw [← map_pow, hgr, map_one]
  have hρg1 : ρ g ≠ 1 := fun h => hg1 (hinj (by rw [h, map_one]))
  have hle := omegaPlus_le_ker_of_finrank_lt hr (ρ g) hgpow (by omega) hord _ hinv (by omega)
  have hgz : ρ g z = z := by
    have := hle hzZ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  exact omegaPlus_not_exists_fixed_singular Φ hr hr2 (ρ g) hgpow he hord hdim hρg1 (hQ g) hS hz0
    (hsing z hzZ) hgz

end Abstract

section Model

open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.Timmesfeld.ClassicalOrders (card_quadPlus)

theorem card_singular_quadPlus_modEq {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {r : ℕ} (hrq : r ∣ Nat.card F ^ (n - 1) + 1) :
    Nat.card {v : Fin n ⊕ Fin n → F // StatedQuadPlus n F v = 0} ≡ 1 [MOD r] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (card_quadPlus (K := F) m).1
  have hcongr : Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → F // quadPlus (m + 1) F v = 0} =
      Nat.card {v : Fin (m + 1) ⊕ Fin (m + 1) → F // StatedQuadPlus (m + 1) F v = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [coe_quadPlus])
  rw [hcongr] at h
  rw [Nat.modEq_iff_dvd]
  have hdvd : (r : ℤ) ∣ ((Nat.card F : ℤ) ^ m + 1) := by
    have : ((r : ℕ) : ℤ) ∣ (((Nat.card F ^ m + 1 : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 (by
      simpa using hrq)
    simpa using this
  rw [h, Nat.cast_one]
  have : (1 : ℤ) - (1 + ((Nat.card F : ℤ) ^ (m + 1) - 1) * ((Nat.card F : ℤ) ^ m + 1)) =
      -(((Nat.card F : ℤ) ^ (m + 1) - 1) * ((Nat.card F : ℤ) ^ m + 1)) := by ring
  rw [this, dvd_neg]
  exact Dvd.dvd.mul_left hdvd _

theorem not_dvd_card_normalizer_omegaPlus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ 2 * (n - 1) ∣ m)
    (R : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) :
    ¬ r ∣ Nat.card (Subgroup.normalizer
      (R : Set (StatedProj (StatedOmega (StatedQuadPlus n F))))) := by
  intro hrN
  haveI : Fact r.Prime := ⟨hr⟩
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hA : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow _ _ hq
  have hrA : r ∣ Nat.card F ^ (n - 1) + 1 := by
    have h1 : r ∣ Nat.card F ^ (2 * (n - 1)) - 1 := (hord _).2 dvd_rfl
    have h2 : Nat.card F ^ (2 * (n - 1)) - 1 =
        (Nat.card F ^ (n - 1) - 1) * (Nat.card F ^ (n - 1) + 1) := by
      rw [sub_one_mul_add_one hA, ← sq, ← pow_mul]
      congr 2
      ring
    rw [h2] at h1
    rcases (Nat.Prime.dvd_mul hr).1 h1 with h | h
    · have := Nat.le_of_dvd (by omega) ((hord (n - 1)).1 h)
      omega
    · exact h
  have hS := card_singular_quadPlus_modEq (by omega : 1 ≤ n) hrA
  have hdim : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨hZc, hZcard⟩ := scalars_subgroupOf_facts (Fin n ⊕ Fin n) F
    (StatedOmega (StatedQuadPlus n F))
  have hrZ : ¬ r ∣ Nat.card ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
      (StatedOmega (StatedQuadPlus n F))) := fun h => by
    have h1 : r ∣ Nat.card F ^ 1 - 1 := by simpa using h.trans hZcard
    have := Nat.le_of_dvd one_pos ((hord 1).1 h1)
    omega
  obtain ⟨g, R', hgord, hR'2, hR'1, hgR'⟩ :=
    exists_lift_normalizing ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
      (StatedOmega (StatedQuadPlus n F))) hZc hr hrZ R hR2 hR1 hrN
  have hgr : g ^ r = 1 := hgord ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgord
    exact hr.one_lt.ne hgord
  have hgnorm : g ∈ Subgroup.normalizer (R' : Set (StatedOmega (StatedQuadPlus n F))) :=
    Subgroup.mem_normalizer_iff.2 hgR'
  refine hR'1 (omegaPlus_eq_bot_of_normalizes_ppd (quadPlusForm n F)
    (natRep (StatedOmega (StatedQuadPlus n F))) (natRep_injective _) (fun h v => ?_) ?_ hr hr2
    (by omega) hord hdim ?_ hgr hg1 hR'2 hgnorm)
  · rw [natRep_apply]
    exact orthGroup_preserves (StatedQuadPlus n F) (statedOmega_le_orthGroup _ h.2) v
  · intro h Z hZ a ha hQa
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega (quadPlusForm n F) h.2 hZ ha hQa
  · exact hS

end Model

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
