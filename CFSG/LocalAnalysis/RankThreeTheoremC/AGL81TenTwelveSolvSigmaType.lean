module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JZeroTwoHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.GH74.QTGen4.Leaves.F112
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape

variable {G : Type} [Group G] [Finite G]

theorem heis3Rel_map_mulEquiv {X Y : Type*} [Group X] [Group Y] {S D Z : X}
    (h : Heis3Rel S D Z) (f : X ≃* Y) : Heis3Rel (f S) (f D) (f Z) where
  central x := by
    obtain ⟨y, rfl⟩ := f.surjective x
    rw [← map_mul, ← map_mul, h.central y]
  Z_cube := by rw [← map_pow, h.Z_cube, map_one]
  S_cube := by rw [← map_pow, h.S_cube, map_one]
  D_cube := by rw [← map_pow, h.D_cube, map_one]
  S_D := by simp only [← map_mul, ← map_pow, h.S_D]

theorem heis3_commutator {X : Type*} [Group X] {S D Z : X} (h : Heis3Rel S D Z) (k j : ℕ) :
    S ^ k * D ^ j * (S ^ k)⁻¹ * (D ^ j)⁻¹ = Z ^ (2 * (k * j)) := by
  rw [h.S_pow_mul_D_pow]
  group

theorem orderOf_pow_of_heis3 {X : Type*} [Group X] {Z : X} (hZ3 : Z ^ 3 = 1) (hZ1 : Z ≠ 1)
    {k j : ℕ} (hk : ¬ 3 ∣ k) (hj : ¬ 3 ∣ j) : orderOf (Z ^ (2 * (k * j))) = 3 := by
  have hZord : orderOf Z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hZ3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hZ1
    · exact h
  have hcube : (Z ^ (2 * (k * j))) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * (k * j) * 3 = 3 * (2 * (k * j)) by ring, pow_mul, hZ3, one_pow]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hcube) with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    have h3 : 3 ∣ 2 * (k * j) := by
      have := orderOf_dvd_of_pow_eq_one h
      rwa [hZord] at this
    rcases (Nat.prime_three.dvd_mul).mp h3 with h' | h'
    · exact (by decide : ¬ 3 ∣ 2) h'
    · rcases (Nat.prime_three.dvd_mul).mp h' with h'' | h''
      · exact hk h''
      · exact hj h''
  · exact h

theorem card_dvd_three_of_symThree {H I₀ : Subgroup G} (hI₀H : I₀ ≤ H)
    (hb : Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)))
    {J : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hJ : J = ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hJ3 : IsPGroup 3 J) : Nat.card J ∣ 3 := by
  classical
  obtain ⟨e⟩ := hb
  have hJI : Nat.card J ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I₀) := by
    have hsub : Nat.card ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H) =
        Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I₀) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((oUpperTwo_le_self I₀).trans hI₀H)).toEquiv
    rw [hJ, ← hsub]
    exact Subgroup.card_map_dvd _ _
  have hII₀ : Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I₀) ∣ Nat.card ↥I₀ :=
    Subgroup.card_dvd_of_le (oUpperTwo_le_self I₀)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥I₀))
  have hQ6 : Nat.card (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcard : Nat.card ↥I₀ = 2 ^ a * 6 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I₀), hQ6, ha]
    ring
  obtain ⟨b, hb3⟩ := IsPGroup.iff_card.mp hJ3
  have hdvd : 3 ^ b ∣ Nat.card ↥I₀ := by
    rw [← hb3]
    exact hJI.trans hII₀
  rw [hcard] at hdvd
  have h3 : 3 ^ b ∣ 3 := by
    have hcop : Nat.Coprime (3 ^ b) (2 ^ (a + 1)) :=
      Nat.Coprime.pow b (a + 1) (by decide)
    have heq : (2 : ℕ) ^ a * 6 = 2 ^ (a + 1) * 3 := by rw [pow_succ]; ring
    rw [heq] at hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd
  rwa [hb3]

theorem not_comm_of_suThreeTwo {H I₀ : Subgroup G} (hI₀H : I₀ ≤ H)
    (hb : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* ↥(StatedSU 3 2 F)))
    {J : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hJ : J = ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3))) :
    ¬ ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
  classical
  intro hcomm
  obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := hb
  obtain ⟨ω, hω, h2⟩ := exists_omega hcard
  let o : OmegaData F := ⟨ω, hω, h2⟩
  have hrelSU : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  set O : Subgroup ↥I₀ := CFSG.pCore 2 ↥I₀ with hO
  set S : ↥I₀ ⧸ O := e.symm (OmegaData.sS o) with hS
  set D : ↥I₀ ⧸ O := e.symm (OmegaData.sD o) with hD
  set Z : ↥I₀ ⧸ O := e.symm (sZ o) with hZ
  have hrel : Heis3Rel S D Z := heis3Rel_map_mulEquiv hrelSU e.symm
  have hZne : Z ≠ 1 := by
    rw [hZ]
    intro h1
    exact sZ_ne_one o (e.symm.injective (h1.trans (map_one e.symm).symm))
  obtain ⟨s₁, hs₁⟩ := QuotientGroup.mk'_surjective O S
  obtain ⟨d₁, hd₁⟩ := QuotientGroup.mk'_surjective O D
  obtain ⟨a, ha⟩ := exists_two_pow_mem_oUpperTwo (I := I₀) (y := (s₁ : G)) s₁.2
  obtain ⟨b, hb₂⟩ := exists_two_pow_mem_oUpperTwo (I := I₀) (y := (d₁ : G)) d₁.2
  set s : ↥I₀ := s₁ ^ 2 ^ a with hs
  set d : ↥I₀ := d₁ ^ 2 ^ b with hd
  have hsU : ((s : ↥I₀) : G) ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ := by
    rw [hs, Subgroup.coe_pow]
    exact ha
  have hdU : ((d : ↥I₀) : G) ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ := by
    rw [hd, Subgroup.coe_pow]
    exact hb₂
  have hπs : QuotientGroup.mk' O s = S ^ 2 ^ a := by rw [hs, map_pow, hs₁]
  have hπd : QuotientGroup.mk' O d = D ^ 2 ^ b := by rw [hd, map_pow, hd₁]
  set c : ↥I₀ := s * d * s⁻¹ * d⁻¹ with hc
  have hπc : QuotientGroup.mk' O c = Z ^ (2 * (2 ^ a * 2 ^ b)) := by
    rw [hc]
    simp only [map_mul, map_inv, hπs, hπd]
    exact heis3_commutator hrel (2 ^ a) (2 ^ b)
  have hk3 : ¬ 3 ∣ 2 ^ a := fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by decide)
  have hj3 : ¬ 3 ∣ 2 ^ b := fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by decide)
  have hc3 : 3 ∣ orderOf c := by
    have h1 : orderOf (QuotientGroup.mk' O c) ∣ orderOf c := orderOf_map_dvd _ c
    rw [hπc, orderOf_pow_of_heis3 hrel.Z_cube hZne hk3 hj3] at h1
    exact h1
  have hcH : ((c : ↥I₀) : G) ∈ H := hI₀H c.2
  set cH : H := ⟨(c : G), hcH⟩ with hcHh
  have hordc : orderOf cH = orderOf c := by
    rw [hcHh, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
  have hnotmem : cH ∉ primeComplementCore (G := H) 3 := by
    intro hmem
    have hdvd : orderOf c ∣ Nat.card (primeComplementCore (G := H) 3) := by
      rw [← hordc]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    have hcop : Nat.Coprime 3 (orderOf c) :=
      (primeComplementCore_coprime 3).coprime_dvd_right hdvd
    have h1 : 3 ∣ Nat.gcd 3 (orderOf c) := Nat.dvd_gcd dvd_rfl hc3
    rw [hcop.gcd_eq_one] at h1
    exact absurd h1 (by decide)
  have hsH : ((s : ↥I₀) : G) ∈ H := hI₀H s.2
  have hdH : ((d : ↥I₀) : G) ∈ H := hI₀H d.2
  set sH : H := ⟨(s : G), hsH⟩ with hsHh
  set dH : H := ⟨(d : G), hdH⟩ with hdHh
  have hsJ : QuotientGroup.mk' (primeComplementCore (G := H) 3) sH ∈ J := by
    rw [hJ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsU)
  have hdJ : QuotientGroup.mk' (primeComplementCore (G := H) 3) dH ∈ J := by
    rw [hJ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hdU)
  have hcH_eq : cH = sH * dH * sH⁻¹ * dH⁻¹ := by
    apply Subtype.ext
    simp [hcHh, hsHh, hdHh, hc]
  have hone : QuotientGroup.mk' (primeComplementCore (G := H) 3) cH = 1 := by
    rw [hcH_eq]
    simp only [map_mul, map_inv]
    rw [hcomm _ hsJ _ hdJ]
    group
  refine hnotmem ((QuotientGroup.eq_one_iff cH).mp ?_)
  rwa [← QuotientGroup.mk'_apply]

theorem card_eq_three_of_comm {H I₀ : Subgroup G} (hI₀H : I₀ ≤ H)
    (hb : IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀))
    {J : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hJ : J = ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hJ3 : IsPGroup 3 J) (hJne : J ≠ ⊥) (hab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) :
    Nat.card J = 3 := by
  rcases hb with hb | hb
  · have hd := card_dvd_three_of_symThree hI₀H hb hJ hJ3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd ((Subgroup.card_eq_one).mp h1) hJne
    · exact h3
  · exact absurd hab (not_comm_of_suThreeTwo hI₀H hb hJ)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
