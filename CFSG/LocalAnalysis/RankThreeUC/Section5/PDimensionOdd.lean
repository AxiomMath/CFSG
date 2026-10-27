module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.PFixedLineDimension
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeB
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActorInversion
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ReciprocalOddOrderFixedParity.ReciprocalOddOrderFixedParity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.PDimensionOdd

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

@[expose] noncomputable def tau (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    MulAut ↥P →* (Space hc ≃ₗ[ZMod p] Space hc) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Space hc)).toMonoidHom.comp
    (sigma hc).toHomUnits

theorem tau_apply (hc : BinaryActionRankCounterexample G p P T B e ρ) (φ : MulAut ↥P) (v : Space hc) :
    tau hc φ v = sigma hc φ v := rfl

theorem odd (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1)) :
    Odd (Module.finrank (ZMod p) (Space hc)) := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  obtain ⟨hcard, hrp, -, -⟩ := PrimeB.prime_order hc hr
  set r := Nat.card B with hrdef
  have hrodd : Odd r := hc.oddPrimeClassTwoAction.setting.oddOrder
  have hpodd : Odd p := hc.oddPrimeClassTwoAction.setting.odd
  have hrp' : r ≠ p := by
    intro h
    apply (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
    rw [hc.oddPrimeClassTwoAction.pi_eq]
    refine ⟨Fact.out, ?_⟩
    rw [← hcard, h]
  have hrF : (r : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hrp' ((Nat.prime_dvd_prime_iff_eq Fact.out hrp).mp h).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'
    subst this
    exact absurd hpodd (by decide)
  obtain ⟨x, hx⟩ := ActorInversion.inverted hc
  have hcyc : IsCyclic B := (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.2.1
  obtain ⟨b, hb⟩ := hcyc.exists_generator
  have hN := hc.faithfulBinaryIrreducibleAction.normal
  set t := tau hc (conjOnP P hN (b : G)) with ht
  set j := tau hc (conjOnP P hN x) with hj
  have htr : t ^ r = 1 := by
    rw [ht, ← map_pow, ← map_pow]
    have : (b : G) ^ r = 1 := by
      have h := pow_card_eq_one' (G := B) (x := b)
      rw [hrdef, ← Subgroup.coe_pow, h]
      rfl
    rw [this, map_one, map_one]
  have hjt : j * t * j⁻¹ = t⁻¹ := by
    have hcc : conjOnP P hN x * conjOnP P hN (b : G) * (conjOnP P hN x)⁻¹ =
        conjOnP P hN ((b : G)⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul, hx (b : G) b.2]
    calc j * t * j⁻¹ = tau hc (conjOnP P hN x * conjOnP P hN (b : G) * (conjOnP P hN x)⁻¹) := by
          simp [hj, ht, map_mul, map_inv]
      _ = tau hc (conjOnP P hN ((b : G)⁻¹)) := by rw [hcc]
      _ = t⁻¹ := by simp [ht, map_inv]
  have inj : ∀ a a' : Space hc, a.val = a'.val → a = a' := fun a a' h => Additive.toMul.injective h
  have htv : ∀ v : Space hc, ((t v).val : G) = (b : G) * (v.val : G) * (b : G)⁻¹ := by
    intro v
    rw [ht, tau_apply, sigma_apply, conjOnP_apply]
  have hker : LinearMap.ker (t.toLinearMap - LinearMap.id) = Qline hc := by
    ext v
    rw [LinearMap.mem_ker, PFixedLineDimension.mem_Qline_iff hc v,
      Subgroup.mem_centralizer_iff]
    have key : (t.toLinearMap - LinearMap.id : Space hc →ₗ[ZMod p] Space hc) v = 0 ↔ t v = v := by
      simp [sub_eq_zero]
    rw [key]
    constructor
    · intro h c hcB
      have h1 : (b : G) * (v.val : G) * (b : G)⁻¹ = v.val := by rw [← htv, h]
      have h2 : Commute (b : G) (v.val : G) := by
        have := mul_inv_eq_iff_eq_mul.mp h1
        exact this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hb ⟨c, hcB⟩)
      have hk' : (b : G) ^ k = c := by simpa using congrArg Subtype.val hk
      rw [← hk']
      exact (h2.zpow_left k).eq
    · intro h
      apply inj
      apply Subtype.ext
      rw [htv]
      have := h (b : G) b.2
      rw [mul_inv_eq_iff_eq_mul]
      exact this
  have hfr := PFixedLineDimension.finrank_eq_one hc
  have hev := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ReciprocalOddOrderFixedParity.even_moved h2 r hrodd hrF t htr j hjt
  rw [hker, hfr] at hev
  have hle : Module.finrank (ZMod p) (Qline hc) ≤ Module.finrank (ZMod p) (Space hc) :=
    Submodule.finrank_le _
  rw [hfr] at hle
  obtain ⟨k, hk⟩ := hev
  exact ⟨k, by omega⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.PDimensionOdd
