module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGraphInv

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem card_T0_inf_le_eight
    {r : Equiv.Perm (Fin 42)} (hrR : r ∈ R) (hr2 : r * r = 1) (hrS : r ∉ S) :
    Nat.card ↥(T0 ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42)))) ≤ 8 := by
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hrS ?_
    · simp only [OneMemClass.coe_one, pow_two]
      exact hr2
    · have h' : r = 1 := congrArg Subtype.val h
      rw [h']
      exact S.one_mem
  have hC : Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 168 ∨
      Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 60 ∨
      Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
    · exact absurd (mem_S_of_isConj₁ h) hrS
    · left
      rw [card_centralizer_S_of_isConj h]
      exact card_C₂
    · right; left
      rw [card_centralizer_S_of_isConj h]
      exact card_C₃
    · right; right
      rw [card_centralizer_S_of_isConj h]
      exact card_C₄
  have hle : T0 ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42))) ≤
      centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S :=
    fun t ht => ⟨ht.2, T0_le_S ht.1⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T0 := IsPGroup.of_card (n := 6) (by rw [card_T0]; norm_num)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp (hT2.to_le inf_le_left))
  rw [hk] at hdvd ⊢
  by_contra hgt
  have hk4 : 4 ≤ k := by
    by_contra hk4
    interval_cases k <;> simp_all
  have h16 : 16 ∣ Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) :=
    (pow_dvd_pow 2 hk4).trans hdvd
  rcases hC with h | h | h <;> rw [h] at h16 <;> norm_num at h16

variable {G : Type} [Group G]

theorem outerInvolutionCentralizer :
    ∀ (G : Type) [Group G] [Finite G] (K R P : Subgroup G) (w : G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K → P ≤ R → IsPGroup 2 R →
      R ≤ normalizer (K : Set G) → w ∈ R → w * w = 1 → w ∉ withKernel K →
      4 * Nat.card ↥(R ⊓ centralizer ({w} : Set G)) ≤ Nat.card R := by
  intro G _ _ K R P w hK hL hP hPR _ hRN hwR hw2 hwK
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨r, hrR, hr2, hrS, hr⟩ :=
    exists_involution_realization hK (hRN hwR) hw2 hwK hqS hqsurj hqker
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  set C : Subgroup G := centralizer ({w} : Set G) with hCd
  set φ : ↥(P ⊓ C) →* Equiv.Perm (Fin 42) :=
    (q.comp (jq K)).comp (Subgroup.inclusion (inf_le_left.trans hP.1)) with hφ
  have hφy : ∀ y : ↥(P ⊓ C), φ y = q (jq K ⟨y, hP.1 y.2.1⟩) := fun y => rfl
  have hrange : φ.range ≤ T0 ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42))) := by
    rintro _ ⟨y, rfl⟩
    rw [hφy]
    refine ⟨(hT _).2 ⟨y, y.2.1, _, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have hyw : (y : G) * w = w * y := mem_centralizer_singleton_iff.mp y.2.2
    have hfix : w⁻¹ * y * w = y := by
      calc w⁻¹ * y * w = w⁻¹ * (y * w) := by group
        _ = w⁻¹ * (w * y) := by rw [hyw]
        _ = y := by group
    have h1 := hr (jq K ⟨y, hP.1 y.2.1⟩)
    rw [betaHat_jq, show conjJ K (hRN hwR) ⟨y, hP.1 y.2.1⟩ = ⟨y, hP.1 y.2.1⟩ from
      Subtype.ext hfix] at h1
    calc q (jq K ⟨y, hP.1 y.2.1⟩) * r = r * q (jq K ⟨y, hP.1 y.2.1⟩) * r⁻¹ * r := by
          rw [← h1]
      _ = r * q (jq K ⟨y, hP.1 y.2.1⟩) := by group
  have hker : Nat.card φ.ker ≤ Nat.card ↥(P ⊓ zStarIn K) := by
    have hmem : ∀ y : φ.ker, ((y : ↥(P ⊓ C)) : G) ∈ P ⊓ zStarIn K := by
      intro y
      refine ⟨y.1.2.1, (mem_zStarIn_iff (hP.1 y.1.2.1)).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker, ← hφy]
      exact y.2
    refine Nat.card_le_card_of_injective (fun y : φ.ker => (⟨_, hmem y⟩ : ↥(P ⊓ zStarIn K)))
      fun a b hab => ?_
    have h1 := congrArg (fun x : ↥(P ⊓ zStarIn K) => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hcardPC : Nat.card ↥(P ⊓ C) ≤ Nat.card ↥(P ⊓ zStarIn K) * 8 := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
    exact Nat.mul_le_mul hker ((Subgroup.card_le_of_le hrange).trans
      (card_T0_inf_le_eight hrR hr2 hrS))
  have hcardP : Nat.card P = 64 * Nat.card ↥(P ⊓ zStarIn K) := by
    have hPP : pullP K P hP.1 (T0.comap q) = P := by
      ext y
      rw [mem_pullP]
      exact ⟨fun ⟨hy, _⟩ => hy, fun hy => ⟨hy, (hT _).2 ⟨y, hy, _, rfl⟩⟩⟩
    calc Nat.card P = Nat.card (pullP K P hP.1 (T0.comap q)) := by rw [hPP]
      _ = 64 * Nat.card ↥(P ⊓ zStarIn K) := by
        rw [card_pullP hP2 hT le_rfl,
          card_comap_eq q T0 (fun t ht => hqsurj t (T0_le_S ht)), card_T0,
          Nat.card_congr ζ.toEquiv]
  have hZpos : 0 < Nat.card ↥(P ⊓ zStarIn K) := Nat.card_pos
  have hPpos : 0 < Nat.card ↥(P ⊓ C) := Nat.card_pos
  have hiP := Subgroup.relIndex_mul_card (H := C) (K := P)
  have hiR := Subgroup.relIndex_mul_card (H := C) (K := R)
  rw [inf_comm] at hiP hiR
  have hiR0 : C.relIndex R ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hiR
    exact (Nat.card_pos (α := R)).ne' hiR.symm
  have hle := Subgroup.relIndex_le_of_le_right hPR hiR0
  have h8 : 8 ≤ C.relIndex P := by
    by_contra hlt
    rw [not_le] at hlt
    have : Nat.card P ≤ 7 * Nat.card ↥(P ⊓ C) := by
      rw [← hiP]
      exact Nat.mul_le_mul_right _ (by omega)
    nlinarith
  calc 4 * Nat.card ↥(R ⊓ C) ≤ C.relIndex R * Nat.card ↥(R ⊓ C) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = Nat.card R := hiR

end CFSG.ComponentClassification.GrSLit.L34Facts
