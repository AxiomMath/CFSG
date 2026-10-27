module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusTwoElt
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusFactors
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusTransport
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

variable {W : Type} [Group W]

theorem central_of_not_twoSet_le {F X : Subgroup W} (hF : QFacts F)
    (hFX : F ≤ normalizer (X : Set W)) (h : ¬ twoSet F ⊆ X) :
    ∀ d ∈ F ⊓ X, ∀ g ∈ F, g * d = d * g := by
  by_contra hne
  push Not at hne
  obtain ⟨d, hd, g, hg, hgne⟩ := hne
  apply h
  intro q hq
  obtain ⟨a, ha, b, hb, hqab⟩ := hF.normal_dich d hd.1 ⟨g, hg, hgne⟩ q hq.1 hq.2
  rw [hqab]
  exact X.mul_mem (commutator_mem_of_normalizes (A := X) (B := F) hFX hd.2 ha)
    (commutator_mem_of_normalizes (A := X) (B := F) hFX hd.2 hb)

theorem QFacts.pow_four_of_twoElt {F : Subgroup W} (hF : QFacts F) {q : W} (hq : q ∈ F)
    (h2 : TwoElt q) : q ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := h2
  have h12 : orderOf q ∣ 12 := orderOf_dvd_of_pow_eq_one (hF.exp_dvd q hq)
  have h2k : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2k
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hj] at this
    have h8 := this.trans h12
    omega
  have : orderOf q ∣ 4 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj2 : 2 ^ j ∣ 2 ^ 2)
  exact orderOf_dvd_iff_pow_eq_one.mp this

variable {S : Finset (Subgroup W)}

theorem pow_four_of_twoElt_commProd (hQ : ∀ A ∈ S, QFacts A) (hc : PComm S) :
    ∀ x ∈ S.sup id, TwoElt x → x ^ 4 = 1 := by
  refine commProd_induction (fun _ => True)
    (fun N => ∀ x ∈ N, TwoElt x → x ^ 4 = 1) ?_ ?_ S hQ (fun _ _ => trivial) hc
  · intro x hx _
    rw [Subgroup.mem_bot] at hx
    subst hx
    simp
  · intro F N hF _ hFN ihN x hx hx2
    obtain ⟨f, hf, n, hn, rfl⟩ := (mem_sup_of_commutator_eq_bot hFN).mp hx
    obtain ⟨k, hk⟩ := hx2
    have hcm : Commute f n := commute_of_commutator_eq_bot hFN hf hn
    rw [hcm.mul_pow] at hk
    have hfN : f ^ (2 ^ k) ∈ N := by
      have : f ^ (2 ^ k) = (n ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [this]
      exact N.inv_mem (N.pow_mem hn _)
    have hcen : ∀ g ∈ F, g * f ^ (2 ^ k) = f ^ (2 ^ k) * g := fun g hg =>
      (commute_of_commutator_eq_bot hFN hg hfN).eq
    have hsq := hF.center_sq (f ^ (2 ^ k)) (F.pow_mem hf _) hcen
    have hf2 : TwoElt f := ⟨k + 1, by rw [pow_succ, pow_mul, sq]; exact hsq⟩
    have hf4 : f ^ 4 = 1 := hF.pow_four_of_twoElt hf hf2
    have hn2 : TwoElt n := by
      refine ⟨k + 2, ?_⟩
      have hnk : n ^ (2 ^ k) = (f ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk
      have h4 : (f ^ (2 ^ k)) ^ 4 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hf4, one_pow]
      calc n ^ (2 ^ (k + 2)) = n ^ (2 ^ k * 4) := by rw [show 2 ^ (k + 2) = 2 ^ k * 4 by ring]
        _ = (n ^ (2 ^ k)) ^ 4 := pow_mul n _ 4
        _ = 1 := by rw [hnk, inv_pow, h4, inv_one]
    have hn4 : n ^ 4 = 1 := ihN n hn hn2
    rw [hcm.mul_pow, hf4, hn4, one_mul]


variable {Q : Type} [Group Q]

theorem exists_split [Finite W] (hQ : GoodQ Q) (hS : ∀ F ∈ S, Nonempty (↥F ≃* Q))
    (hc : PComm S) (X : Subgroup W) :
    ∃ S0 S1 : Finset (Subgroup W), S0 ⊆ S ∧ S1 ⊆ S ∧ (∀ F ∈ S, F ∈ S0 ∨ F ∈ S1) ∧
      (∀ F ∈ S0, twoSet F ⊆ (X : Set W)) ∧ (∀ F ∈ S1, ¬ twoSet F ⊆ (X : Set W)) ∧
      ∀ φ : W ≃* W, (S.sup id).map φ.toMonoidHom = S.sup id → X.map φ.toMonoidHom = X →
        (S0.sup id).map φ.toMonoidHom = S0.sup id ∧ (S1.sup id).map φ.toMonoidHom = S1.sup id := by
  classical
  refine ⟨S.filter (fun F => twoSet F ⊆ (X : Set W)), S.filter (fun F => ¬ twoSet F ⊆ (X : Set W)),
    Finset.filter_subset _ _, Finset.filter_subset _ _, ?_,
    fun F hF => (Finset.mem_filter.mp hF).2, fun F hF => (Finset.mem_filter.mp hF).2, ?_⟩
  · intro F hF
    by_cases h : twoSet F ⊆ (X : Set W)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hF, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hF, h⟩)
  intro φ hφN hφX
  have hperm : ∀ F ∈ S, F.map φ.toMonoidHom ∈ S := fun F hF =>
    map_mem_of_map_eq hQ hS hc φ hφN hF
  have hinjmap : Function.Injective (Subgroup.map φ.toMonoidHom) :=
    Subgroup.map_injective φ.injective
  have hXiff : ∀ x : W, φ x ∈ X ↔ x ∈ X := by
    intro x
    constructor
    · intro h
      rw [← hφX] at h
      obtain ⟨y, hy, hyx⟩ := h
      have : y = x := φ.injective hyx
      rwa [← this]
    · intro h
      have : φ x ∈ X.map φ.toMonoidHom := Subgroup.mem_map.mpr ⟨x, h, rfl⟩
      rwa [hφX] at this
  have hP : ∀ F : Subgroup W, twoSet (F.map φ.toMonoidHom) ⊆ (X : Set W) ↔
      twoSet F ⊆ (X : Set W) := by
    intro F
    constructor
    · intro h x hx
      have : φ x ∈ twoSet (F.map φ.toMonoidHom) :=
        ⟨Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩, by
          have := congrArg φ.toMonoidHom hx.2
          simpa [map_pow] using this⟩
      exact (hXiff x).mp (h this)
    · intro h y hy
      obtain ⟨⟨x, hxF, rfl⟩, hy4⟩ := hy
      have hx4 : x ^ 4 = 1 := by
        have h1 : φ.toMonoidHom (x ^ 4) = 1 := by rw [map_pow]; exact hy4
        exact (map_eq_one_iff φ.toMonoidHom φ.injective).mp h1
      exact (hXiff x).mpr (h ⟨hxF, hx4⟩)
  have key : ∀ T : Finset (Subgroup W), (∀ F ∈ T, F.map φ.toMonoidHom ∈ T) →
      (T.sup id).map φ.toMonoidHom = T.sup id := by
    intro T hT
    rw [map_finset_sup]
    have : T.image (Subgroup.map φ.toMonoidHom) = T :=
      Finset.eq_of_subset_of_card_le
        (fun F hF => by
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hF
          exact hT A hA)
        (by rw [Finset.card_image_of_injective _ hinjmap])
    rw [this]
  refine ⟨key _ fun F hF => ?_, key _ fun F hF => ?_⟩
  · obtain ⟨hFS, hFP⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_filter.mpr ⟨hperm F hFS, (hP F).mpr hFP⟩
  · obtain ⟨hFS, hFP⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_filter.mpr ⟨hperm F hFS, fun h => hFP ((hP F).mp h)⟩

theorem bcore_one [Finite W] (hQ : GoodQ Q) (hS : ∀ F ∈ S, Nonempty (↥F ≃* Q)) (hc : PComm S)
    (X : Subgroup W) [X.Normal] (𝒜 : Set (W ≃* W))
    (hN : ∀ φ ∈ 𝒜, (S.sup id).map φ.toMonoidHom = S.sup id)
    (hX : ∀ φ ∈ 𝒜, X.map φ.toMonoidHom = X)
    (hcomm : ∀ φ ∈ 𝒜, ∀ n ∈ S.sup id, n⁻¹ * φ n ∈ X) :
    ∃ N0 N1 : Subgroup W, S.sup id = N0 ⊔ N1 ∧ IsCommProd Q N0 ∧ IsCommProd Q N1 ∧
      (∀ x ∈ N0, TwoElt x → x ∈ X) ∧ (∀ φ ∈ 𝒜, ∀ n ∈ N1, φ n = n) ∧
      ∀ ψ : W ≃* W, (S.sup id).map ψ.toMonoidHom = S.sup id → X.map ψ.toMonoidHom = X →
        N0.map ψ.toMonoidHom = N0 ∧ N1.map ψ.toMonoidHom = N1 := by
  classical
  obtain ⟨S0, S1, hS0, hS1, hcov, h0, h1, hinv⟩ := exists_split hQ hS hc X
  have hq : ∀ A ∈ S, QFacts A := fun A hA => hQ.qFacts (hS A hA).some
  have hc0 : PComm S0 := hc.mono hS0
  have hc1 : PComm S1 := hc.mono hS1
  have hq0 : ∀ A ∈ S0, QFacts A := fun A hA => hq A (hS0 hA)
  have hq1 : ∀ A ∈ S1, QFacts A := fun A hA => hq A (hS1 hA)
  refine ⟨S0.sup id, S1.sup id, ?_, ⟨S0, fun F hF => hS F (hS0 hF), hc0, rfl⟩,
    ⟨S1, fun F hF => hS F (hS1 hF), hc1, rfl⟩, ?_, ?_, hinv⟩
  · apply le_antisymm
    · refine Finset.sup_le fun F hF => ?_
      rcases hcov F hF with h | h
      · exact le_sup_of_le_left (le_sup_of_mem h)
      · exact le_sup_of_le_right (le_sup_of_mem h)
    · exact sup_le (Finset.sup_mono hS0) (Finset.sup_mono hS1)
  · intro x hx h2
    refine two_mem_of_commProd hq0 hc0 (fun A hA f hf hf4 => h0 A hA ⟨hf, hf4⟩) x hx ?_
    exact pow_four_of_twoElt_commProd hq0 hc0 x hx h2
  · intro φ hφ
    have hN1inv : (S1.sup id).map φ.toMonoidHom = S1.sup id := (hinv φ (hN φ hφ) (hX φ hφ)).2
    have h3 : ∀ x ∈ S1.sup id, x ^ 3 = 1 → φ x = x := by
      intro x hx hx3
      set d := x⁻¹ * φ x with hd
      have hdN1 : d ∈ S1.sup id := by
        refine (S1.sup id).mul_mem ((S1.sup id).inv_mem hx) ?_
        have : φ x ∈ (S1.sup id).map φ.toMonoidHom := ⟨x, hx, rfl⟩
        rwa [hN1inv] at this
      have hdX : d ∈ X := hcomm φ hφ x ((Finset.sup_mono (f := id) hS1) hx)
      have hcenF : ∀ F ∈ S1, ∀ f ∈ F, d * f = f * d := by
        intro F hF f hf
        have hFX : F ≤ normalizer (X : Set W) := Subgroup.le_normalizer_of_normal
        have hFN1 : F ≤ S1.sup id := le_sup_of_mem hF
        have hnotF : ¬ twoSet F ⊆ (X : Set W) := h1 F hF
        have hFT : F ≤ normalizer ((X ⊓ S1.sup id : Subgroup W) : Set W) := by
          intro g hg
          rw [mem_normalizer_iff]
          intro y
          have h1' := mem_normalizer_iff.mp (hFX hg) y
          have h2' := mem_normalizer_iff.mp (Subgroup.le_normalizer (hFN1 hg)) y
          simp only [Subgroup.mem_inf]
          rw [h1', h2']
        have hTF : (X ⊓ S1.sup id : Subgroup W) ≤ normalizer (F : Set W) :=
          inf_le_right.trans (sup_le_normalizer_of_mem hc1 hF)
        have hcen : ∀ e ∈ F ⊓ (X ⊓ S1.sup id), ∀ g ∈ F, g * e = e * g := fun e he g hg =>
          central_of_not_twoSet_le (hq1 F hF) hFX hnotF e ⟨he.1, he.2.1⟩ g hg
        exact commute_of_inf_central (hq1 F hF) hFT hTF hcen d ⟨hdX, hdN1⟩ f hf
      have hcen : ∀ n ∈ S1.sup id, n * d = d * n := by
        intro n hn
        have hle : S1.sup id ≤ centralizer ({d} : Set W) :=
          Finset.sup_le fun F hF f hf => by
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            rw [Set.mem_singleton_iff] at hh
            subst hh
            exact hcenF F hF f hf
        have := Subgroup.mem_centralizer_iff.mp (hle hn) d rfl
        exact this.symm
      have hd2 : d * d = 1 := center_sq_of_commProd hq1 hc1 d hdN1 hcen
      have hcm : Commute x d := hcen x hx
      have hd3 : d ^ 3 = d := by
        calc d ^ 3 = d * d * d := pow_three' d
          _ = d := by rw [hd2, one_mul]
      have hxd : x * d = φ x := by rw [hd]; group
      have hφ3 : (φ x) ^ 3 = 1 := by
        rw [← map_pow]
        have : (φ : W →* W) (x ^ 3) = 1 := by rw [hx3, map_one]
        exact this
      have : d = 1 := by
        calc d = x ^ 3 * d ^ 3 := by rw [hx3, one_mul, hd3]
          _ = (x * d) ^ 3 := (hcm.mul_pow 3).symm
          _ = 1 := by rw [hxd]; exact hφ3
      rw [this, mul_one] at hxd
      exact hxd.symm
    have hle : S1.sup id ≤ MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id W) :=
      le_of_three_of_commProd hq1 hc1 fun x hx hx3 => h3 x hx hx3
    intro n hn
    exact hle hn

end CFSG.OddStandard.Solomon75
