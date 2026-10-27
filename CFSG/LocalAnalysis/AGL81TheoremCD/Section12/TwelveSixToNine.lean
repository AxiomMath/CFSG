module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_oPPrimeHull {M : Subgroup G} {d : ℕ} (hd : d.Prime)
    (hdvd : d ∣ Nat.card M) : d ∣ Nat.card (oPPrimeHull d M) := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) d hdvd
  have hxM : (x : G) ∈ M := x.2
  have hxordG : orderOf (x : G) = d := by
    rw [Subgroup.orderOf_coe, hxord]
  have hxmem : (x : G) ∈ oPPrimeHull d M :=
    Subgroup.subset_closure ⟨hxM, 1, by simpa using hxordG⟩
  have hle : Subgroup.zpowers (x : G) ≤ oPPrimeHull d M := Subgroup.zpowers_le.mpr hxmem
  have hdvd' : d ∣ Nat.card (Subgroup.zpowers (x : G)) := by
    rw [Nat.card_zpowers, hxordG]
  exact hdvd'.trans (Subgroup.card_dvd_of_le hle)

theorem TwelveSix.part_one_left {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) :
    ∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₁ → Subgroup.centralizer (W : Set G) ≤ M :=
  (h hdata).1

theorem TwelveSix.part_one_middle {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) :
    ∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₂ → Subgroup.centralizer (W : Set G) ≤ M :=
  (h hdata).2.1

theorem TwelveSix.part_one_right {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) :
    ∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₃ → Subgroup.centralizer (W : Set G) ≤ M :=
  (h hdata).2.2.1

theorem TwelveSix.n₁_eq_one {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) : n₁ = 1 :=
  (h hdata).2.2.2.1

theorem TwelveSix.n₂_eq_one {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) : n₂ = 1 :=
  (h hdata).2.2.2.2.1

theorem TwelveSix.n₃_eq_one {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) : n₃ = 1 :=
  (h hdata).2.2.2.2.2.1

theorem TwelveSix.p_eq_three {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) : p = 3 :=
  (h hdata).2.2.2.2.2.2.2.1

theorem TwelveSix.part_five {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) :
    CFSG.Blueprint.LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)) :=
  (h hdata).2.2.2.2.2.2.2.2.1

theorem TwelveSix.part_six {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ} (hdata : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃) :
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M) →
      kSub p M H ⊓ M =
        (kSub p M H ⊓ normalizer (thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H) :=
  (h hdata).2.2.2.2.2.2.2.2.2

theorem twelveSix_of_parts {M H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G}
    {n₁ n₂ n₃ : ℕ}
    (h1₁ : ∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₁ →
      Subgroup.centralizer (W : Set G) ≤ M)
    (h1₂ : ∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₂ →
      Subgroup.centralizer (W : Set G) ≤ M)
    (h1₃ : ∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₃ →
      Subgroup.centralizer (W : Set G) ≤ M)
    (h2₁ : n₁ = 1) (h2₂ : n₂ = 1) (h2₃ : n₃ = 1)
    (h3 : sigmaSet G M = {7}) (h4 : p = 3)
    (h5 : CFSG.Blueprint.LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)))
    (h6 : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M) →
      kSub p M H ⊓ M =
        (kSub p M H ⊓ normalizer (thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H)) :
    TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃ :=
  fun _ => ⟨h1₁, h1₂, h1₃, h2₁, h2₂, h2₃, h3, h4, h5, h6⟩

theorem normalizer_le_normalizer_centerIn (D : Subgroup G) :
    normalizer (D : Set G) ≤ normalizer (CFSG.centerIn D : Set G) := by
  have hstep : ∀ y ∈ normalizer (D : Set G), ∀ w ∈ CFSG.centerIn D,
      y * w * y⁻¹ ∈ CFSG.centerIn D := by
    intro y hy w hw
    obtain ⟨hwD, hwC⟩ := hw
    have hwC' : w ∈ Subgroup.centralizer (D : Set G) := hwC
    rw [Subgroup.mem_centralizer_iff] at hwC'
    refine ⟨(Subgroup.mem_normalizer_iff.mp hy w).1 hwD, ?_⟩
    change y * w * y⁻¹ ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hyinv : y⁻¹ ∈ normalizer (D : Set G) := (normalizer (D : Set G)).inv_mem hy
    have hd' : y⁻¹ * d * y ∈ D := by
      simpa using (Subgroup.mem_normalizer_iff.mp hyinv d).1 hd
    have h := hwC' (y⁻¹ * d * y) hd'
    calc d * (y * w * y⁻¹) = y * ((y⁻¹ * d * y) * w) * y⁻¹ := by group
      _ = y * (w * (y⁻¹ * d * y)) * y⁻¹ := by rw [h]
      _ = (y * w * y⁻¹) * d := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro z
  constructor
  · exact hstep x hx z
  · intro hz
    have hxinv : x⁻¹ ∈ normalizer (D : Set G) := (normalizer (D : Set G)).inv_mem hx
    have h := hstep x⁻¹ hxinv (x * z * x⁻¹) hz
    have hz' : x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ = z := by group
    rwa [hz'] at h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
