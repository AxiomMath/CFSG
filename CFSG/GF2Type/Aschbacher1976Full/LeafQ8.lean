module

public import CFSG.GF2Type.Aschbacher1976Full.LeafQ8Sylow
import CFSG.Milestones.LR_Brauer_Suzuki_central_involution
import CFSG.Milestones.LR_semidihedral_simple_recognition

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint CFSG.Semidihedral.Principal

namespace LeafQ8

theorem eq_three_one {p f c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hc : c ∣ 48)
    (hv : padicValNat p c = f) : p = 3 ∧ f = 1 := by
  have hpf : p ^ f ∣ c := hv ▸ pow_padicValNat_dvd
  have hpc : p ∣ 48 := (dvd_pow_self p (by omega)).trans (hpf.trans hc)
  have hp3 : p = 3 := by
    rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hpc
    rcases (Nat.Prime.dvd_mul hp).mp hpc with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  subst hp3
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h9 : 3 ^ 2 ∣ 3 ^ f := pow_dvd_pow 3 (by omega)
  have := h9.trans (hpf.trans hc)
  norm_num at this

theorem false_of_quaternion_sylow {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) (S : Sylow 2 G)
    (hzS : z ∈ (S : Subgroup G)) {n : ℕ} (hn : 3 ≤ n)
    (hq : Nonempty (↥(S : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2)))) : False := by
  have hmem := CFSG.Milestones.brauer_suzuki n hn S hq z hzS hz
  have hodd : oddCore G = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun N ⟨hN, hNodd⟩ => ?_)
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h.le
    · subst h
      rw [Subgroup.card_top] at hNodd
      obtain ⟨m, hm⟩ := hNodd
      obtain ⟨c, hc⟩ := (hz ▸ orderOf_dvd_natCard z : 2 ∣ Nat.card G)
      omega
  have hcomm : ∀ g : G, g * z = z * g := by
    intro g
    have h1 := Subgroup.mem_center_iff.mp hmem (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
      Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact (hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h) a b)).elim
  have hz1 : z = 1 := by
    have : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hcomm
    rwa [hcenter, Subgroup.mem_bot] at this
  rw [hz1, orderOf_one] at hz
  omega

theorem isSporadic_M11 {X : Type} [Group X] (e : X ≃* Assembly.LowTwoRank.StatedM11) :
    NativeSporadic.IsSporadic X .M11 :=
  ⟨e.trans (MulEquiv.subgroupCongr
    CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)⟩

end LeafQ8

theorem leafQ8_holds :
    Asc76LeafQ8 := by
  intro G _ _ z hS he
  obtain ⟨e⟩ := he
  obtain ⟨hsimp, hnab, hz, hsymp⟩ := hS
  haveI : IsSimpleGroup G := hsimp
  obtain ⟨S, hzS, ⟨n, hn, hsd⟩ | ⟨n, hn, hq⟩⟩ := LeafQ8.exists_sylow_shape hz hsymp.1 e
  · have hcard := LeafQ8.card_Hz_dvd hz e
    rcases CFSG.Milestones.lr_semidihedral_simple_recognition_1 G hnab ⟨S, n, hn, hsd⟩ with
      ⟨p, f, hp, hp2, hf, -, hmodel⟩ | ⟨p, f, hp, hp2, hf, hmod, hmodel⟩ | he'
    · obtain ⟨-, -, hC, -⟩ := degree_three_model_characteristic_valuation_regularity .PSL
        (Or.inl rfl) p f hp (hp.odd_of_ne_two hp2) hf hmodel
      obtain ⟨rfl, rfl⟩ := LeafQ8.eq_three_one hp hp2 hf hcard (hC z hz)
      exact Or.inr (Or.inl ⟨by decide, hmodel⟩)
    · obtain ⟨-, -, hC, -⟩ := degree_three_model_characteristic_valuation_regularity .PSU
        (Or.inr rfl) p f hp (hp.odd_of_ne_two hp2) hf hmodel
      obtain ⟨rfl, rfl⟩ := LeafQ8.eq_three_one hp hp2 hf hcard (hC z hz)
      norm_num at hmod
    · obtain ⟨e'⟩ := he'
      exact Or.inl (LeafQ8.isSporadic_M11 e')
  · exact (LeafQ8.false_of_quaternion_sylow hnab hz S hzS hn hq).elim

end CFSG.GF2Type.Aschbacher1976Full
