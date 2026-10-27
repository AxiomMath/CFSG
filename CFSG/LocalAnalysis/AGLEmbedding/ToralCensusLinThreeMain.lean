module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeCore
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeCenter

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem even_of_three_dvd_two_pow_pred {f : ℕ} (h : 3 ∣ 2 ^ f - 1) : Even f := by
  by_contra hf
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hf
  have h4 : (2 * 4 ^ k) % 3 = 2 := by
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2] at h
  omega

theorem card_center_sl_three_le (K : Type) [Field K] :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) ≤ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  have h : max (Fintype.card (Fin 3)) 1 = 3 := by simp
  rw [h]
  exact card_rootsOfUnity K 3

theorem injective_of_card_center_le {L : Type} [Group L] {n : ℕ} {K : Type} [Field K]
    [Finite K] {ρ : SpecialLinearGroup (Fin n) K →* L}
    {e : L ⧸ Subgroup.center L ≃* projectiveSL n K} (hs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hρ : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g)
    (hc : Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) K)) ≤
      Nat.card (Subgroup.center L)) :
    Function.Injective ρ := by
  have hZ : ∀ g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K),
      ρ g ∈ Subgroup.center L := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨x, rfl⟩ := hs l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg x]
  let φ : Subgroup.center (SpecialLinearGroup (Fin n) K) → Subgroup.center L :=
    fun g => ⟨ρ g, hZ g g.2⟩
  have hφs : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, rfl⟩ := hs z
    have hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center, ← proj_eq_one_iff, ← hρ, (QuotientGroup.eq_one_iff _).mpr hz,
        map_one]
    exact ⟨⟨g, hg⟩, rfl⟩
  have hφi := (hφs.bijective_of_nat_card_le hc).1
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have h1 : φ ⟨g, hker hg⟩ = φ 1 := Subtype.ext (by simpa [φ] using hg)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hφi h1))

end ToralCensus

open ToralCensus CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem fixThreeA
    (hGA : CFSG.Open.GriessAllModelsStatement) : FixThreeA := by
  intro Y _ _ L J u hd hA
  obtain ⟨n, f, ρ, e, I, t, hS, hjoin⟩ := exists_naturalSetup hGA hd.parab hA hd.cyc
    (Subgroup.mem_sup_left hd.mem) hd.pow hd.not_mem hd.fix
  obtain ⟨hn3, hq4⟩ := eq_three_of_threeCensus hS.cuts hS.nonempty (hjoin hd.join) hS.pow_mem
    hS.centralizer_le hS.cyc
  subst hn3
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by have := hS.one_le; omega)
  refine ⟨f, ?_, ⟨e⟩⟩
  by_contra hf
  have hf1 : f = 1 := by have := hS.one_le; omega
  rw [hcard, hf1] at hq4
  norm_num at hq4

open ToralCensus CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem fixCensusCenterA
    (hGA : CFSG.Open.GriessAllModelsStatement) : FixCensusCenterA := by
  intro Y _ _ L J u hd hA
  obtain ⟨n, f, ρ, e, I, t, hS, -⟩ := exists_naturalSetup hGA hd.parab hA hd.cyc hd.mem hd.pow
    hd.not_mem hd.fix
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card 2 f (by have := hS.one_le; omega)
  have hZ := oddCenterLinear_of_griess hGA Y L hd.parab.comp hd.parab.odd n (GaloisField 2 f)
    ⟨e⟩
  rw [← Nat.card_eq_fintype_card, hcard] at hZ
  have h3 : 3 ∣ Nat.gcd n (2 ^ f - 1) := hd.three_dvd.trans hZ
  have h3n : 3 ∣ n := h3.trans (Nat.gcd_dvd_left _ _)
  have h3q : 3 ∣ 2 ^ f - 1 := h3.trans (Nat.gcd_dvd_right _ _)
  have hn5 := le_five_of_centerCensus hS.cuts hS.nonempty hS.ne_borel (by rw [hcard]; exact h3q)
    hS.pow_mem hS.centralizer_le hS.cyc
  have hn : n = 3 := by have := hS.three_le; omega
  subst hn
  have hZ3 : Nat.card (Subgroup.center ↥L) = 3 := by
    rw [Nat.gcd_eq_left h3q] at hZ
    exact Nat.dvd_antisymm hZ hd.three_dvd
  have hinj := injective_of_card_center_le hS.surj hS.ker_le hS.compat
    (by rw [hZ3]; exact card_center_sl_three_le _)
  have hev := even_of_three_dvd_two_pow_pred h3q
  refine ⟨f, hev, ?_, ⟨(MulEquiv.ofBijective ρ ⟨hinj, hS.surj⟩).symm⟩⟩
  obtain ⟨k, hk⟩ := hev
  have := hS.one_le
  omega

end CFSG.AGLEmbedding
