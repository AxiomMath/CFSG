module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Sylow
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.LieType.BorelTits.HeldFlagSU
public import CFSG.LieType.SeitzGeneration.HeisSmallModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem eq_one_of_pow_two_three {G : Type} [Group G] {t : G} {j k : ℕ}
    (h2 : t ^ (2 ^ j) = 1) (h3 : t ^ (3 ^ k) = 1) : t = 1 := by
  have d : orderOf t ∣ Nat.gcd (2 ^ j) (3 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow j k (by norm_num))] at d
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp d)

theorem pow_three_of_mem_center {Q : Type} [Group Q] (hZ : IsPGroup 3 (Subgroup.center Q))
    {a : Q} (ha : a ∈ Subgroup.center Q) : ∃ k : ℕ, a ^ (3 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hZ ⟨a, ha⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB
  CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

theorem i1431YU4Eight_holds : I1431YU4Eight := by
  intro Q _ _ σ A I T hQ hZ hU5 _ _ hA6 _ _ hT0 hT2 _ hAN
  obtain ⟨A₀, S, hSg, f, hA₀A, hSc, hf⟩ := hA6
  obtain ⟨hSsimp, hS360⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5.isA6_isSimpleGroup hSc
  haveI : IsSimpleGroup S := hSsimp
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hS360]; norm_num)
  obtain ⟨e⟩ := u4_eight_equiv_statedSU hU5
  let ι : Q →* StatedSU 4 8 K64 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  let ρ : A₀ →* StatedSU 4 8 K64 := ι.comp A₀.subtype
  have hmemZ : ∀ b ∈ ρ.ker, (b : Q) ∈ Subgroup.center Q := by
    intro b hb
    have h1 : e (QuotientGroup.mk (b : Q)) = 1 := MonoidHom.mem_ker.mp hb
    have h2 : (QuotientGroup.mk (b : Q) : Q ⧸ Subgroup.center Q) = 1 := by
      exact (map_eq_one_iff e e.injective).mp h1
    exact (QuotientGroup.eq_one_iff (b : Q)).mp h2
  have hker : ρ.ker ≤ f.ker := by
    have hnorm : (ρ.ker.map f).Normal := Subgroup.Normal.map inferInstance f hf
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map f) with hbot | htop
    · intro a ha
      have hmem : f a ∈ ρ.ker.map f := Subgroup.mem_map_of_mem f ha
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 5 (by rw [hS360]; norm_num)
      have hsmem : s ∈ ρ.ker.map f := by
        rw [htop]
        exact Subgroup.mem_top s
      obtain ⟨b, hb, hfb⟩ := Subgroup.mem_map.mp hsmem
      obtain ⟨k, hk⟩ := pow_three_of_mem_center hZ (hmemZ b hb)
      have hbk : b ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
      have hsk : s ^ (3 ^ k) = 1 := by
        rw [← hfb, ← map_pow, hbk, map_one]
      have h5 : orderOf s ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hsk
      rw [hs] at h5
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)
  let φh : ρ.range →* S :=
    (QuotientGroup.lift ρ.ker f hker).comp (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
  have hφh : Function.Surjective φh := by
    intro s
    obtain ⟨a, ha⟩ := hf s
    refine ⟨(QuotientGroup.quotientKerEquivRange ρ) (QuotientGroup.mk a), ?_⟩
    show QuotientGroup.lift ρ.ker f hker
      (((QuotientGroup.quotientKerEquivRange ρ).symm)
        ((QuotientGroup.quotientKerEquivRange ρ) (QuotientGroup.mk a))) = s
    rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk, ha]
  let T' : Subgroup (StatedSU 4 8 K64) := T.map ι
  have hT'0 : T' ≠ ⊥ := by
    obtain ⟨⟨t, htT⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT0
    have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
    intro hbot
    have htι : ι t ∈ T' := Subgroup.mem_map_of_mem ι htT
    rw [hbot, Subgroup.mem_bot] at htι
    apply ht1
    obtain ⟨j, hj⟩ := hT2 ⟨t, htT⟩
    have htZ : t ∈ Subgroup.center Q := by
      have h1 : e (QuotientGroup.mk t) = 1 := htι
      exact (QuotientGroup.eq_one_iff t).mp ((map_eq_one_iff e e.injective).mp h1)
    obtain ⟨k, hk⟩ := pow_three_of_mem_center hZ htZ
    exact eq_one_of_pow_two_three (by simpa using congrArg Subtype.val hj) hk
  have hT'2 : IsPGroup 2 T' := by
    intro x
    obtain ⟨t, htT, hteq⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨j, hj⟩ := hT2 ⟨t, htT⟩
    refine ⟨j, Subtype.ext ?_⟩
    have ht : t ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hteq, ← map_pow, ht, map_one]
  have hXN : ρ.range ≤ Subgroup.normalizer (T' : Set (StatedSU 4 8 K64)) := by
    rintro _ ⟨a, rfl⟩
    have haN : (a : Q) ∈ Subgroup.normalizer (T : Set Q) := hAN (hA₀A a.2)
    have hρa : ρ a = ι (a : Q) := rfl
    rw [hρa, Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp (show n ∈ T' from hn)
      rw [← hteq]
      have key : ι (a : Q) * ι t * (ι (a : Q))⁻¹ = ι ((a : Q) * t * (a : Q)⁻¹) := by
        simp [map_mul, map_inv]
      rw [key]
      exact Subgroup.mem_map_of_mem ι ((Subgroup.mem_normalizer_iff.mp haN t).mp ht)
    · intro hn
      obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp (show ι (a : Q) * n * (ι (a : Q))⁻¹ ∈ T' from hn)
      have ht : (a : Q)⁻¹ * s * (a : Q) ∈ T := by
        apply (Subgroup.mem_normalizer_iff.mp haN ((a : Q)⁻¹ * s * (a : Q))).mpr
        simpa [mul_assoc] using hs
      have hnmap : n = ι ((a : Q)⁻¹ * s * (a : Q)) := by
        rw [map_mul, map_mul, map_inv, hseq]
        group
      show n ∈ T'
      rw [hnmap]
      exact Subgroup.mem_map_of_mem ι ht
  obtain ⟨W, hW0, hWiso, hN⟩ := CFSG.LieType.BorelTits.heldFlagSU (q := 8) (by rw [K64_card]; norm_num) T' hT'0 hT'2
  exact core_stated4 K64_card W hW0 hWiso ρ.range (fun y hy w hw => hN y (hXN hy) w hw) S hS360
    (not_all_sylow_three_cyclic_of_isA6 hSc)
    ⟨φh, hφh⟩

end CFSG.LocalAnalysis.GLTheoremA.I1431Y

end
