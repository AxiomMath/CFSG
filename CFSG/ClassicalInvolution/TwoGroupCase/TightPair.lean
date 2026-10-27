module

public import CFSG.ClassicalInvolution.TwoGroupCase.CommutingFamily
public import CFSG.ClassicalInvolution.TwoGroupCase.SylowOf

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

section Normalizer

variable {K' R S : Subgroup G}

theorem commute_of_mem_normalizer_inf (hR : R ≤ Subgroup.normalizer (K' : Set G))
    (hRK : K' ⊓ R = ⊥) {s : G} (hsK : s ∈ K') (hsN : s ∈ Subgroup.normalizer (R : Set G)) :
    ∀ r ∈ R, s * r = r * s := by
  intro r hr
  have h1 : s * r * s⁻¹ * r⁻¹ ∈ R :=
    R.mul_mem ((Subgroup.mem_normalizer_iff.mp hsN r).mp hr) (R.inv_mem hr)
  have h2 : s * r * s⁻¹ * r⁻¹ ∈ K' := by
    have hr' : r * s⁻¹ * r⁻¹ ∈ K' :=
      (Subgroup.mem_normalizer_iff.mp (hR hr) s⁻¹).mp (K'.inv_mem hsK)
    have e : s * r * s⁻¹ * r⁻¹ = s * (r * s⁻¹ * r⁻¹) := by group
    rw [e]
    exact K'.mul_mem hsK hr'
  have h3 : s * r * s⁻¹ * r⁻¹ ∈ K' ⊓ R := ⟨h2, h1⟩
  rw [hRK, Subgroup.mem_bot] at h3
  calc s * r = (s * r * s⁻¹ * r⁻¹) * (r * s) := by group
    _ = r * s := by rw [h3, one_mul]

theorem normalizer_eq_centralizer_inf (hR : R ≤ Subgroup.normalizer (K' : Set G))
    (hRK : K' ⊓ R = ⊥) :
    S ⊓ K' ⊓ Subgroup.normalizer (R : Set G) = S ⊓ K' ⊓ Subgroup.centralizer (R : Set G) := by
  ext s
  constructor
  · intro hs
    refine ⟨hs.1, ?_⟩
    show s ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (commute_of_mem_normalizer_inf hR hRK hs.1.2 hs.2 r hr).symm
  · intro hs
    exact ⟨hs.1, Subgroup.centralizer_le_normalizer _ hs.2⟩

theorem exists_mul_of_mem_normalizer (hR : R ≤ Subgroup.normalizer (K' : Set G))
    (hRS : R ≤ S) (hS : S ≤ K' ⊔ R) {n : G} (hnS : n ∈ S)
    (hnN : n ∈ Subgroup.normalizer (R : Set G)) :
    ∃ s ∈ S ⊓ K' ⊓ Subgroup.normalizer (R : Set G), ∃ r ∈ R, n = s * r := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K' R hR
  have hn : n ∈ ((K' ⊔ R : Subgroup G) : Set G) := hS hnS
  rw [hmul] at hn
  obtain ⟨k, hk, r, hr, rfl⟩ := hn
  refine ⟨k, ⟨⟨?_, hk⟩, ?_⟩, r, hr, rfl⟩
  · have : k = k * r * r⁻¹ := by group
    rw [this]
    exact S.mul_mem hnS (S.inv_mem (hRS hr))
  · have : k = (k * r) * r⁻¹ := by group
    rw [this]
    exact (Subgroup.normalizer (R : Set G)).mul_mem hnN
      ((Subgroup.normalizer (R : Set G)).inv_mem (Subgroup.le_normalizer hr))

theorem exists_mul_of_mem (hR : R ≤ Subgroup.normalizer (K' : Set G))
    (hRS : R ≤ S) (hS : S ≤ K' ⊔ R) {n : G} (hnS : n ∈ S) :
    ∃ s ∈ S ⊓ K', ∃ r ∈ R, n = s * r := by
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K' R hR
  have hn : n ∈ ((K' ⊔ R : Subgroup G) : Set G) := hS hnS
  rw [hmul] at hn
  obtain ⟨k, hk, r, hr, rfl⟩ := hn
  refine ⟨k, ⟨?_, hk⟩, r, hr, rfl⟩
  have : k = k * r * r⁻¹ := by group
  rw [this]
  exact S.mul_mem hnS (S.inv_mem (hRS hr))

theorem natCard_normalizer_eq (hR : R ≤ Subgroup.normalizer (K' : Set G))
    (hRK : K' ⊓ R = ⊥) (hRS : R ≤ S) (hS : S ≤ K' ⊔ R) :
    Nat.card (S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) =
      Nat.card (S ⊓ K' ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) * Nat.card R := by
  refine natCard_eq_mul_of_inf_eq_bot (fun x hx => ⟨hx.1.1, hx.2⟩)
    (fun x hx => ⟨hRS hx, Subgroup.le_normalizer hx⟩) ?_ fun m hm => ?_
  · refine le_bot_iff.mp ?_
    rw [← hRK]
    exact inf_le_inf (inf_le_left.trans inf_le_right) le_rfl
  · obtain ⟨s, hs, r, hr, rfl⟩ := exists_mul_of_mem_normalizer hR hRS hS hm.1 hm.2
    exact ⟨s, hs, r, hr, rfl⟩

end Normalizer

theorem two_pow_factorization_mul {n k : ℕ} (hn : n ≠ 0) :
    2 ^ (n * 2 ^ k).factorization 2 = 2 ^ n.factorization 2 * 2 ^ k := by
  rw [Nat.factorization_mul hn (pow_ne_zero k two_ne_zero)]
  simp [pow_add, Nat.Prime.factorization_self Nat.prime_two]

structure PairData (K : Subgroup G) (g : G) (R S : Subgroup G) : Prop where
  tight : classicalInvolutionTightlyEmbedded K
  not_normal : g ∉ Subgroup.normalizer (K : Set G)
  sylowR : IsSylow2Of R (K ⊓ Subgroup.normalizer (conjSubgroup g K : Set G))
  sylowS : IsSylow2Of S (conjSubgroup g K ⊔ R)
  le : R ≤ S

namespace PairData

variable [Finite G] {K : Subgroup G} {g : G} {R S : Subgroup G} (d : PairData K g R S)
include d

omit [Finite G] in
theorem R_le_K : R ≤ K := d.sylowR.1.trans inf_le_left

omit [Finite G] in
theorem R_le_normalizer : R ≤ Subgroup.normalizer (conjSubgroup g K : Set G) :=
  d.sylowR.1.trans inf_le_right

omit [Finite G] in
theorem R_two : IsPGroup 2 R := d.sylowR.2.1

omit [Finite G] in
theorem S_two : IsPGroup 2 S := d.sylowS.2.1

omit [Finite G] in
theorem S_le : S ≤ conjSubgroup g K ⊔ R := d.sylowS.1

theorem inf_eq_bot : conjSubgroup g K ⊓ R = ⊥ := by
  by_contra h
  apply d.not_normal
  have := conjSubgroup_eq_of_tight_of_two_group_le d.tight (g := g)
    (d.R_two.to_le inf_le_right) h (inf_le_right.trans d.R_le_K) inf_le_left
  exact conjSubgroup_eq_self_iff.mp this

omit [Finite G] in
theorem le_normalizer_sup : conjSubgroup g K ⊔ R ≤ Subgroup.normalizer (conjSubgroup g K : Set G) :=
  sup_le Subgroup.le_normalizer d.R_le_normalizer

omit [Finite G] in
theorem tightData (hR1 : R ≠ ⊥) : TightData K (conjSubgroup g K ⊔ R) R S := by
  refine ⟨d.tight, ⟨le_inf le_sup_right d.R_le_K, d.R_two, fun P' hP'A hP'2 hle => ?_⟩, hR1,
    d.S_two, d.S_le, d.le⟩
  exact d.sylowR.2.2 P' (fun x hx => ⟨hP'A hx |>.2, d.le_normalizer_sup (hP'A hx).1⟩) hP'2 hle

theorem natCard_S : Nat.card S = Nat.card (S ⊓ conjSubgroup g K : Subgroup G) * Nat.card R :=
  natCard_eq_mul_of_inf_eq_bot (inf_le_left) d.le
    (le_bot_iff.mp (d.inf_eq_bot ▸ inf_le_inf inf_le_right le_rfl))
    fun m hm => by
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem d.R_le_normalizer d.le d.S_le hm
      exact ⟨a, ha, b, hb, rfl⟩

theorem natCard_sup : Nat.card (conjSubgroup g K ⊔ R : Subgroup G) =
    Nat.card (conjSubgroup g K) * Nat.card R := by
  refine natCard_eq_mul_of_inf_eq_bot le_sup_left le_sup_right d.inf_eq_bot fun m hm => ?_
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (conjSubgroup g K) R d.R_le_normalizer
  have : m ∈ ((conjSubgroup g K ⊔ R : Subgroup G) : Set G) := hm
  rw [hmul] at this
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩

theorem natCard_S₀ : Nat.card (S ⊓ conjSubgroup g K : Subgroup G) =
    2 ^ (Nat.card (conjSubgroup g K)).factorization 2 := by
  obtain ⟨k, hk⟩ := d.R_two.exists_card_eq
  have h1 := d.sylowS.card_eq
  rw [d.natCard_sup, hk, two_pow_factorization_mul Nat.card_pos.ne'] at h1
  have h2 := d.natCard_S
  rw [hk, h1] at h2
  have : 0 < 2 ^ k := by positivity
  exact (Nat.eq_of_mul_eq_mul_right this h2.symm)

theorem S₁_le (hR1 : R ≠ ⊥) :
    S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ≤
      conjSubgroup g K ⊓ Subgroup.normalizer (K : Set G) := by
  intro s hs
  refine ⟨hs.1.2, ?_⟩
  show s ∈ Subgroup.normalizer (K : Set G)
  rw [← conjSubgroup_eq_self_iff]
  refine conjSubgroup_eq_of_tight_of_two_group_le d.tight d.R_two hR1 d.R_le_K ?_
  have h := conjSubgroup_mono (g := s) d.R_le_K
  rwa [conjSubgroup_eq_self_iff.mpr hs.2] at h

theorem card_R_le_card_S₁_of_not_le (hR1 : R ≠ ⊥) (hne : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    Nat.card R ≤
      Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) := by
  have h1 := (d.tightData hR1).card_sq_le_card_normalizer hne
  rw [natCard_normalizer_eq d.R_le_normalizer d.inf_eq_bot d.le d.S_le] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem card_R_le_card_S₁ (hR1 : R ≠ ⊥) :
    Nat.card R ≤
      Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) := by
  by_cases hS : S ≤ Subgroup.normalizer (R : Set G)
  · have h : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) = S ⊓ conjSubgroup g K :=
      inf_eq_left.mpr (inf_le_left.trans hS)
    rw [h, d.natCard_S₀]
    have h2 := card_le_of_isPGroup_le d.R_two d.R_le_K
    rwa [← card_conjSubgroup g K] at h2
  · exact d.card_R_le_card_S₁_of_not_le hR1 hS

theorem card_R_le (hR1 : R ≠ ⊥) :
    Nat.card R ≤ 2 ^ (Nat.card (conjSubgroup g K ⊓
      Subgroup.normalizer (K : Set G) : Subgroup G)).factorization 2 :=
  (d.card_R_le_card_S₁ hR1).trans <| card_le_of_isPGroup_le
    (d.S_two.to_le (inf_le_left.trans inf_le_left)) (d.S₁_le hR1)

end PairData

@[expose] noncomputable def twoPartN (K : Subgroup G) (g : G) : ℕ :=
  2 ^ (Nat.card (K ⊓ Subgroup.normalizer (conjSubgroup g K : Set G) : Subgroup G)).factorization 2

theorem card_inf_normalizer_conjSubgroup (K : Subgroup G) (g : G) :
    Nat.card (conjSubgroup g K ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) =
      Nat.card (K ⊓ Subgroup.normalizer (conjSubgroup g⁻¹ K : Set G) : Subgroup G) := by
  have h : conjSubgroup g⁻¹ (conjSubgroup g K ⊓ Subgroup.normalizer (K : Set G)) =
      K ⊓ Subgroup.normalizer (conjSubgroup g⁻¹ K : Set G) := by
    rw [conjSubgroup_inf, conjSubgroup_inv_conjSubgroup]
    congr 1
    ext x
    rw [mem_conjSubgroup_iff, mem_normalizer_conjSubgroup_iff]
  rw [← card_conjSubgroup g⁻¹, h]

theorem exists_pairData {K : Subgroup G} (hK : classicalInvolutionTightlyEmbedded K) {g : G}
    (hg : g ∉ Subgroup.normalizer (K : Set G)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPA : P ≤ K ⊓ Subgroup.normalizer (conjSubgroup g K : Set G)) :
    ∃ R S : Subgroup G, P ≤ R ∧ PairData K g R S := by
  obtain ⟨R, hR, hPR⟩ := exists_isSylow2Of_ge hP hPA
  obtain ⟨S, hS, hRS⟩ := exists_isSylow2Of_ge (P := R) (A := conjSubgroup g K ⊔ R) hR.2.1
    le_sup_right
  exact ⟨R, S, hPR, ⟨hK, hg, hR, hS, hRS⟩⟩

theorem twoPartN_le [Finite G] {K : Subgroup G} (hK : classicalInvolutionTightlyEmbedded K) {g : G}
    (hg : g ∉ Subgroup.normalizer (K : Set G)) : twoPartN K g ≤ twoPartN K g⁻¹ := by
  obtain ⟨R, S, -, d⟩ := exists_pairData hK hg (P := ⊥) IsPGroup.of_bot bot_le
  have hcard : twoPartN K g = Nat.card R := d.sylowR.card_eq.symm
  by_cases hR1 : R = ⊥
  · rw [hcard, hR1, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  · rw [hcard, twoPartN, ← card_inf_normalizer_conjSubgroup]
    exact d.card_R_le hR1

theorem twoPartN_inv [Finite G] {K : Subgroup G} (hK : classicalInvolutionTightlyEmbedded K) {g : G}
    (hg : g ∉ Subgroup.normalizer (K : Set G)) : twoPartN K g⁻¹ = twoPartN K g := by
  refine le_antisymm ?_ (twoPartN_le hK hg)
  have hg' : g⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hg (by simpa using (Subgroup.normalizer (K : Set G)).inv_mem h)
  have := twoPartN_le hK hg'
  rwa [inv_inv] at this

namespace PairData

variable [Finite G] {K : Subgroup G} {g : G} {R S : Subgroup G} (d : PairData K g R S)
include d

theorem card_R_eq : Nat.card R = 2 ^ (Nat.card (conjSubgroup g K ⊓
    Subgroup.normalizer (K : Set G) : Subgroup G)).factorization 2 := by
  have h := twoPartN_inv d.tight d.not_normal
  have h1 : twoPartN K g = Nat.card R := d.sylowR.card_eq.symm
  rw [← h1, ← h, twoPartN, ← card_inf_normalizer_conjSubgroup]

theorem card_S₁ (hR1 : R ≠ ⊥) :
    Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) =
      Nat.card R := by
  refine le_antisymm ?_ (d.card_R_le_card_S₁ hR1)
  rw [d.card_R_eq]
  exact card_le_of_isPGroup_le (d.S_two.to_le (inf_le_left.trans inf_le_left)) (d.S₁_le hR1)

theorem sylow_S₁ (hR1 : R ≠ ⊥) :
    IsSylow2Of (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G))
      (conjSubgroup g K ⊓ Subgroup.normalizer (K : Set G)) :=
  isSylow2Of_of_card (d.S₁_le hR1) (d.S_two.to_le (inf_le_left.trans inf_le_left))
    (by rw [d.card_S₁ hR1, d.card_R_eq])

omit [Finite G] in
theorem normalizer_eq_sup :
    S ⊓ Subgroup.normalizer (R : Set G) =
      (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)) ⊔ R := by
  refine le_antisymm (fun n hn => ?_)
    (sup_le (fun x hx => ⟨hx.1.1, hx.2⟩)
      (fun x hx => ⟨d.le hx, Subgroup.le_normalizer hx⟩))
  obtain ⟨s, hs, r, hr, rfl⟩ :=
    exists_mul_of_mem_normalizer d.R_le_normalizer d.le d.S_le hn.1 hn.2
  exact Subgroup.mul_mem_sup hs hr

theorem S₁_inf_R :
    S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ⊓ R = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [← d.inf_eq_bot]
  exact inf_le_inf (inf_le_left.trans inf_le_right) le_rfl

theorem S₁_commute :
    ∀ s ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G), ∀ r ∈ R, s * r = r * s :=
  fun _ hs _ hr => commute_of_mem_normalizer_inf d.R_le_normalizer d.inf_eq_bot hs.1.2 hs.2 _ hr

theorem S₁_eq_centralizer :
    S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) =
      S ⊓ conjSubgroup g K ⊓ Subgroup.centralizer (R : Set G) :=
  normalizer_eq_centralizer_inf d.R_le_normalizer d.inf_eq_bot

theorem exists_complement (hR1 : R ≠ ⊥) (hne : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    ∃ x ∈ S, conjSubgroup x R ≠ R ∧ conjSubgroup x R ≤ S ⊓ Subgroup.normalizer (R : Set G) ∧
      R ⊓ conjSubgroup x R = ⊥ ∧ (∀ a ∈ R, ∀ b ∈ conjSubgroup x R, a * b = b * a) ∧
      S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ⊓ conjSubgroup x R = ⊥ := by
  have hd := d.tightData hR1
  have hMS : S ⊓ Subgroup.normalizer (R : Set G) ≤ S := inf_le_left
  have hMne : S ⊓ Subgroup.normalizer (R : Set G) ≠ S := fun e => hne (e ▸ inf_le_right)
  obtain ⟨x, hxS, hxM, hxnot⟩ := exists_mem_normalizer_not_mem d.S_two hMS hMne
  have hxR : conjSubgroup x R ≠ R := fun e => hxnot ⟨hxS, conjSubgroup_eq_self_iff.mp e⟩
  have hle : conjSubgroup x R ≤ S ⊓ Subgroup.normalizer (R : Set G) := by
    rw [← conjSubgroup_eq_self_iff.mpr hxM]
    exact conjSubgroup_mono (fun r hr => ⟨d.le hr, Subgroup.le_normalizer hr⟩)
  have hxH : x ∈ conjSubgroup g K ⊔ R := d.S_le hxS
  obtain ⟨hbot, hcomm⟩ := hd.commute_of_le_normalizer hxH hxR hle
  refine ⟨x, hxS, hxR, hle, hbot, hcomm, ?_⟩
  by_contra hS1
  have hP2 : IsPGroup 2
      (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ⊓ conjSubgroup x R : Subgroup G) :=
    d.S_two.to_le (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hRx : conjSubgroup x R = S ⊓ conjSubgroup x K := (hd.conj hxH (hle.trans inf_le_left)).eq_inf
  have hPx : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ⊓ conjSubgroup x R ≤
      conjSubgroup x K := inf_le_right.trans (hRx.le.trans inf_le_right)
  have hPg : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) ⊓ conjSubgroup x R ≤
      conjSubgroup (g * x⁻¹) (conjSubgroup x K) := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    exact inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hKK := conjSubgroup_eq_of_tight_of_two_group_le (tightlyEmbedded_conjSubgroup d.tight x)
    hP2 hS1 hPx hPg
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right] at hKK
  apply hne
  have hS₀ : S ⊓ conjSubgroup g K ≤ Subgroup.normalizer (R : Set G) := by
    intro y hy
    have : y ∈ conjSubgroup x R := by
      rw [hRx, ← hKK]
      exact hy
    exact (hle this).2
  intro n hn
  obtain ⟨s, hs, r, hr, rfl⟩ := exists_mul_of_mem d.R_le_normalizer d.le d.S_le hn
  exact (Subgroup.normalizer (R : Set G)).mul_mem (hS₀ hs) (Subgroup.le_normalizer hr)

theorem nonempty_mulEquiv_S₁ (hR1 : R ≠ ⊥) :
    Nonempty ((S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ≃* R) := by
  by_cases hS : S ≤ Subgroup.normalizer (R : Set G)
  · have h : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) = S ⊓ conjSubgroup g K :=
      inf_eq_left.mpr (inf_le_left.trans hS)
    have hc : Nat.card R = 2 ^ (Nat.card K).factorization 2 := by
      rw [← d.card_S₁ hR1, h, d.natCard_S₀, card_conjSubgroup]
    have hRK : IsSylow2Of R K := isSylow2Of_of_card d.R_le_K d.R_two hc.ge
    have hS₀ : IsSylow2Of (S ⊓ conjSubgroup g K) (conjSubgroup g K) :=
      isSylow2Of_of_card inf_le_right (d.S_two.to_le inf_le_left) d.natCard_S₀.ge
    have hS₀' : IsSylow2Of (conjSubgroup g⁻¹ (S ⊓ conjSubgroup g K)) K := by
      have := hS₀.conj g⁻¹
      rwa [conjSubgroup_inv_conjSubgroup] at this
    rw [h]
    obtain ⟨e₁⟩ := nonempty_mulEquiv_conjSubgroup g⁻¹ (S ⊓ conjSubgroup g K)
    obtain ⟨e₂⟩ := hS₀'.nonempty_mulEquiv hRK
    exact ⟨e₁.trans e₂⟩
  · obtain ⟨x, hxS, hxR, hle, hbot, hcomm, hS1x⟩ := d.exists_complement hR1 hS
    have hA := natCard_normalizer_eq d.R_le_normalizer d.inf_eq_bot d.le d.S_le
    obtain ⟨e₁⟩ := nonempty_mulEquiv_of_complements (M := S ⊓ Subgroup.normalizer (R : Set G))
      (A := S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G))
      (B := R) (C := conjSubgroup x R) (fun y hy => ⟨hy.1.1, hy.2⟩)
      (fun y hy => ⟨d.le hy, Subgroup.le_normalizer hy⟩) hle inf_le_right d.S₁_inf_R
      (by rw [inf_comm]; exact hbot) hA
      (by rw [hA, card_conjSubgroup, d.card_S₁ hR1])
    obtain ⟨e₂⟩ := nonempty_mulEquiv_conjSubgroup x R
    exact ⟨e₁.trans e₂.symm⟩

theorem commute_of_S₁_lt (hR1 : R ≠ ⊥)
    (h : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  have hS : ¬ S ≤ Subgroup.normalizer (R : Set G) := fun hS =>
    h.ne (inf_eq_left.mpr (inf_le_left.trans hS))
  obtain ⟨x, hxS, hxR, hle, hbot, hcomm, hS1x⟩ := d.exists_complement hR1 hS
  have hA := natCard_normalizer_eq d.R_le_normalizer d.inf_eq_bot d.le d.S_le
  have hM := exists_mul_of_natCard_eq (M := S ⊓ Subgroup.normalizer (R : Set G))
    (A := S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G))
    (fun y hy => ⟨hy.1.1, hy.2⟩) hle hS1x
    (by rw [hA, card_conjSubgroup, d.card_S₁ hR1])
  intro a ha b hb
  obtain ⟨s, hs, c, hc, hbsc⟩ := hM b ⟨d.le hb, Subgroup.le_normalizer hb⟩
  have h1 : s * a = a * s := d.S₁_commute s hs a ha
  have h2 : a * c = c * a := hcomm a ha c hc
  rw [hbsc]
  calc a * (s * c) = (a * s) * c := by rw [mul_assoc]
    _ = (s * a) * c := by rw [h1]
    _ = s * (a * c) := by rw [mul_assoc]
    _ = s * (c * a) := by rw [h2]
    _ = s * c * a := by rw [mul_assoc]

theorem exists_conj_mul (hR1 : R ≠ ⊥) (hne : ¬ S ≤ Subgroup.normalizer (R : Set G)) :
    ∃ x ∈ S, (∀ a ∈ R, ∀ b ∈ conjSubgroup x R, a * b = b * a) ∧
      ∀ m ∈ S ⊓ Subgroup.normalizer (R : Set G),
        ∃ a ∈ R, ∃ b ∈ conjSubgroup x R, m = a * b := by
  obtain ⟨x, hxS, hxR, hle, hbot, hcomm, -⟩ := d.exists_complement hR1 hne
  have hA := natCard_normalizer_eq d.R_le_normalizer d.inf_eq_bot d.le d.S_le
  refine ⟨x, hxS, hcomm, exists_mul_of_natCard_eq
    (fun y hy => ⟨d.le hy, Subgroup.le_normalizer hy⟩) hle hbot ?_⟩
  rw [hA, card_conjSubgroup, d.card_S₁ hR1]

theorem conj_commute (hR1 : R ≠ ⊥) (hΦ : ∃ r ∈ R, r * r ≠ 1)
    (h : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K)
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) :
    ∀ y ∈ conjSubgroup s R, ∀ z ∈ conjSubgroup t R, y * z = z * y := by
  have hd := d.tightData hR1
  by_cases hst : conjSubgroup s R = conjSubgroup t R
  · have hab := d.commute_of_S₁_lt hR1 h
    intro y hy z hz
    rw [hst] at hy
    rw [mem_conjSubgroup_iff] at hy hz
    have h1 := hab _ hy _ hz
    calc y * z = t * ((t⁻¹ * y * t) * (t⁻¹ * z * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * z * t) * (t⁻¹ * y * t)) * t⁻¹ := by rw [h1]
      _ = z * y := by group
  · have hconjS : ∀ {s : G}, s ∈ S → conjSubgroup s R ≤ S := fun {s} hs => by
      have := conjSubgroup_mono (g := s) d.le
      rwa [conjSubgroup_eq_self_of_mem hs] at this
    exact (hd.commute_conj hΦ (d.S_le hs) (d.S_le ht) (hconjS hs) (hconjS ht) hst).2

omit [Finite G] in
theorem S₁_eq_S₀_iff :
    S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) = S ⊓ conjSubgroup g K ↔
      S ≤ Subgroup.normalizer (R : Set G) := by
  constructor
  · intro h n hn
    obtain ⟨s, hs, r, hr, rfl⟩ := exists_mul_of_mem d.R_le_normalizer d.le d.S_le hn
    have : s ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) := by
      rw [h]
      exact hs
    exact (Subgroup.normalizer (R : Set G)).mul_mem this.2 (Subgroup.le_normalizer hr)
  · intro hS
    exact inf_eq_left.mpr (inf_le_left.trans hS)

omit [Finite G] in
theorem S₁_lt_iff :
    S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K ↔
      ¬ S ≤ Subgroup.normalizer (R : Set G) := by
  rw [lt_iff_le_not_ge, ← d.S₁_eq_S₀_iff]
  constructor
  · rintro ⟨-, h⟩ h'
    exact h h'.symm.le
  · intro h
    exact ⟨inf_le_left, fun h' => h (le_antisymm inf_le_left h')⟩

theorem S₁_normal_of_not_elementary (hR1 : R ≠ ⊥) (hΦ : ∃ r ∈ R, r * r ≠ 1) :
    S ⊓ conjSubgroup g K ≤
      Subgroup.normalizer
        ((S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
  by_cases hS : S ≤ Subgroup.normalizer (R : Set G)
  · rw [d.S₁_eq_S₀_iff.mpr hS]
    exact Subgroup.le_normalizer
  have hlt := d.S₁_lt_iff.mpr hS
  obtain ⟨x, hxS, hcomm, hM⟩ := d.exists_conj_mul hR1 hS
  have hconj : ∀ t ∈ S, ∀ y ∈ conjSubgroup x R, ∀ z ∈ conjSubgroup t R, y * z = z * y :=
    fun t ht => d.conj_commute hR1 hΦ hlt hxS ht
  have hconj' : ∀ t ∈ S, ∀ y ∈ R, ∀ z ∈ conjSubgroup t R, y * z = z * y := by
    intro t ht y hy z hz
    have hy' : y ∈ conjSubgroup 1 R := by rwa [conjSubgroup_one]
    exact d.conj_commute hR1 hΦ hlt S.one_mem ht y hy' z hz
  refine le_normalizer_of_conj_mem fun t ht u hu => ?_
  have htS : t ∈ S := ht.1
  have huM : u ∈ S ⊓ Subgroup.normalizer (R : Set G) := ⟨hu.1.1, hu.2⟩
  obtain ⟨a, ha, c, hc, rfl⟩ := hM u huM
  refine ⟨⟨S.mul_mem (S.mul_mem htS hu.1.1) (S.inv_mem htS),
    ((S ⊓ conjSubgroup g K).mul_mem ((S ⊓ conjSubgroup g K).mul_mem ht hu.1)
      ((S ⊓ conjSubgroup g K).inv_mem ht)).2⟩, ?_⟩
  refine Subgroup.centralizer_le_normalizer (R : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hwu : ∀ w ∈ conjSubgroup t⁻¹ R, w * (a * c) = (a * c) * w := by
    intro w hw
    have h1 : a * w = w * a := hconj' t⁻¹ (S.inv_mem htS) a ha w hw
    have h2 : c * w = w * c := hconj t⁻¹ (S.inv_mem htS) c hc w hw
    calc w * (a * c) = (w * a) * c := (mul_assoc _ _ _).symm
      _ = (a * w) * c := by rw [h1]
      _ = a * (w * c) := mul_assoc _ _ _
      _ = a * (c * w) := by rw [h2]
      _ = (a * c) * w := (mul_assoc _ _ _).symm
  have hw : t⁻¹ * r * t ∈ conjSubgroup t⁻¹ R := by
    have e : (t⁻¹)⁻¹ * (t⁻¹ * r * t) * t⁻¹ = r := by group
    rw [mem_conjSubgroup_iff, e]
    exact hr
  exact mul_conj_comm_of_commute (hwu _ hw)

theorem normalClosure_eq_normalizer (hR1 : R ≠ ⊥) (hΦ : ∃ r ∈ R, r * r ≠ 1)
    (hlt : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K) :
    (⨆ s ∈ S, conjSubgroup s R) = S ⊓ Subgroup.normalizer (R : Set G) ∧
      Nonempty ((S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ≃* R × R) := by
  have hS : ¬ S ≤ Subgroup.normalizer (R : Set G) := d.S₁_lt_iff.mp hlt
  obtain ⟨x, hxS, hcomm, hM⟩ := d.exists_conj_mul hR1 hS
  have hRW : R ≤ ⨆ s ∈ S, conjSubgroup s R := by
    have := le_iSup₂ (f := fun s (_ : s ∈ S) => conjSubgroup s R) 1 S.one_mem
    rwa [conjSubgroup_one] at this
  have hxW : conjSubgroup x R ≤ ⨆ s ∈ S, conjSubgroup s R :=
    le_iSup₂ (f := fun s (_ : s ∈ S) => conjSubgroup s R) x hxS
  have hW : (⨆ s ∈ S, conjSubgroup s R) = S ⊓ Subgroup.normalizer (R : Set G) := by
    refine le_antisymm (iSup₂_le fun s hs => ?_) fun m hm => ?_
    · intro y hy
      refine ⟨?_, ?_⟩
      · have := conjSubgroup_mono (g := s) d.le
        rw [conjSubgroup_eq_self_of_mem hs] at this
        exact this hy
      · refine Subgroup.centralizer_le_normalizer (R : Set G) ?_
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hr' : r ∈ conjSubgroup 1 R := by rwa [conjSubgroup_one]
        exact d.conj_commute hR1 hΦ hlt S.one_mem hs r hr' y hy
    · obtain ⟨a, ha, b, hb, rfl⟩ := hM m hm
      exact (⨆ s ∈ S, conjSubgroup s R).mul_mem (hRW ha) (hxW hb)
  refine ⟨hW, ?_⟩
  obtain ⟨e₁⟩ := nonempty_mulEquiv_prod (M := S ⊓ Subgroup.normalizer (R : Set G))
    (A := S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G)) (B := R)
    (fun y hy => ⟨hy.1.1, hy.2⟩) (fun y hy => ⟨d.le hy, Subgroup.le_normalizer hy⟩)
    d.S₁_inf_R d.S₁_commute fun m hm =>
      exists_mul_of_mem_normalizer d.R_le_normalizer d.le d.S_le hm.1 hm.2
  obtain ⟨e₂⟩ := d.nonempty_mulEquiv_S₁ hR1
  exact ⟨e₁.trans (MulEquiv.prodCongr e₂ (MulEquiv.refl R))⟩

theorem exists_central_of_card_two (hR1 : R ≠ ⊥) (hR2 : Nat.card R = 2) :
    ∃ z ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G), z ≠ 1 ∧ ∀ s ∈ S, z * s = s * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀S : S ⊓ conjSubgroup g K ≤ S := inf_le_left
  have hS₁2 : Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 2 := by
    rw [d.card_S₁ hR1, hR2]
  have hcardX : Nat.card ((S ⊓ conjSubgroup g K).subgroupOf S) =
      Nat.card (S ⊓ conjSubgroup g K : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀S).toEquiv
  have hidx : ((S ⊓ conjSubgroup g K).subgroupOf S).index = 2 := by
    have h1 := Subgroup.card_mul_index ((S ⊓ conjSubgroup g K).subgroupOf S)
    rw [hcardX, d.natCard_S, hR2] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have : ((S ⊓ conjSubgroup g K).subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hidx
  have : Group.IsNilpotent S := d.S_two.isNilpotent
  have hX : (S ⊓ conjSubgroup g K).subgroupOf S ≠ ⊥ := by
    intro h
    have h1 : Nat.card ((S ⊓ conjSubgroup g K).subgroupOf S) = 1 := by
      rw [h]
      exact Subgroup.card_bot
    have h2 : Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ≤
        Nat.card (S ⊓ conjSubgroup g K : Subgroup G) := Subgroup.card_le_of_le inf_le_left
    omega
  obtain ⟨z', hz'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hX)
  have hz'S₀ : ((z' : S) : G) ∈ S ⊓ conjSubgroup g K := z'.2.1
  have hzc : ∀ s ∈ S, ((z' : S) : G) * s = s * ((z' : S) : G) := by
    intro s hs
    have := Subgroup.mem_center_iff.mp z'.2.2 ⟨s, hs⟩
    exact congrArg Subtype.val this.symm
  have hcent : ((z' : S) : G) ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hzc r (d.le hr)).symm
  exact ⟨((z' : S) : G), ⟨hz'S₀, Subgroup.centralizer_le_normalizer (R : Set G) hcent⟩,
    fun h => hz' (Subtype.ext (Subtype.ext h)), hzc⟩

theorem card_two_structure (hR1 : R ≠ ⊥) (hR2 : Nat.card R = 2) :
    Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 2 ∧
      Nat.card (S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 4 ∧
      (∀ y ∈ S ⊓ Subgroup.normalizer (R : Set G), y * y = 1) ∧
      S ⊓ Subgroup.centralizer (R : Set G) = S ⊓ Subgroup.normalizer (R : Set G) ∧
      ∃ z ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G), z ≠ 1 ∧
        (∀ s ∈ S, z * s = s * z) ∧
        ∀ y ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G), y = 1 ∨ y = z := by
  have hS₁2 : Nat.card (S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 2 := by
    rw [d.card_S₁ hR1, hR2]
  have hRcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun r hr r' hr' =>
    commute_of_mul_self_eq_one (mul_self_eq_one_of_natCard_eq_two hR2 r hr)
      (mul_self_eq_one_of_natCard_eq_two hR2 r' hr')
      (mul_self_eq_one_of_natCard_eq_two hR2 (r * r') (R.mul_mem hr hr'))
  refine ⟨hS₁2, ?_, ?_, ?_, ?_⟩
  · rw [natCard_normalizer_eq d.R_le_normalizer d.inf_eq_bot d.le d.S_le, hS₁2, hR2]
  · intro y hy
    obtain ⟨s, hs, r, hr, rfl⟩ :=
      exists_mul_of_mem_normalizer d.R_le_normalizer d.le d.S_le hy.1 hy.2
    have hcomm : s * r = r * s := d.S₁_commute s hs r hr
    have hss := mul_self_eq_one_of_natCard_eq_two hS₁2 s hs
    have hrr := mul_self_eq_one_of_natCard_eq_two hR2 r hr
    calc (s * r) * (s * r) = s * (r * s) * r := by group
      _ = s * (s * r) * r := by rw [← hcomm]
      _ = (s * s) * (r * r) := by group
      _ = 1 := by rw [hss, hrr, one_mul]
  · refine le_antisymm (fun y hy => ⟨hy.1, Subgroup.centralizer_le_normalizer _ hy.2⟩) ?_
    intro y hy
    obtain ⟨s, hs, r, hr, rfl⟩ :=
      exists_mul_of_mem_normalizer d.R_le_normalizer d.le d.S_le hy.1 hy.2
    refine ⟨hy.1, ?_⟩
    show s * r ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r' hr'
    have hcomm : s * r' = r' * s := d.S₁_commute s hs r' hr'
    calc r' * (s * r) = (r' * s) * r := by rw [mul_assoc]
      _ = (s * r') * r := by rw [← hcomm]
      _ = s * (r' * r) := by rw [mul_assoc]
      _ = s * (r * r') := by rw [hRcomm r' hr' r hr]
      _ = (s * r) * r' := by rw [mul_assoc]
  · obtain ⟨z, hz, hz1, hzc⟩ := d.exists_central_of_card_two hR1 hR2
    refine ⟨z, hz, hz1, hzc, fun y hy => ?_⟩
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : (S ⊓ conjSubgroup g K ⊓
      Subgroup.normalizer (R : Set G) : Subgroup G))).mp hS₁2
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have h1 := hw ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
      have h2 := hw ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)

theorem S₁_normal (hR1 : R ≠ ⊥) (hR : (∃ r ∈ R, r * r ≠ 1) ∨ Nat.card R = 2) :
    S ⊓ conjSubgroup g K ≤
      Subgroup.normalizer
        ((S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := by
  rcases hR with hΦ | hR2
  · exact d.S₁_normal_of_not_elementary hR1 hΦ
  · obtain ⟨-, -, -, -, z, hz, -, hzc, hS₁⟩ := d.card_two_structure hR1 hR2
    refine le_normalizer_of_conj_mem fun t ht u hu => ?_
    rcases hS₁ u hu with rfl | rfl
    · simp
    · have : t * u * t⁻¹ = u := by
        rw [← hzc t ht.1]
        group
      rw [this]
      exact hu

theorem S₁_normal_of_unique_involution (hR1 : R ≠ ⊥)
    (hU : ∀ x ∈ R, ∀ y ∈ R, orderOf x = 2 → orderOf y = 2 → x = y) :
    S ⊓ conjSubgroup g K ≤
      Subgroup.normalizer
        ((S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) :=
  d.S₁_normal hR1 (exists_mul_self_ne_one_or_natCard_eq_two hR1 hU)

theorem five_of_unique_involution (hR1 : R ≠ ⊥)
    (hU : ∀ x ∈ R, ∀ y ∈ R, orderOf x = 2 → orderOf y = 2 → x = y)
    (hlt : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K) :
    (Nat.card R = 2 ∧ Nat.card (S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 4 ∧
        (∀ y ∈ S ⊓ Subgroup.normalizer (R : Set G), y * y = 1) ∧
        S ⊓ Subgroup.centralizer (R : Set G) = S ⊓ Subgroup.normalizer (R : Set G)) ∨
      ((⨆ s ∈ S, conjSubgroup s R) = S ⊓ Subgroup.normalizer (R : Set G) ∧
        Nonempty ((S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ≃* R × R)) := by
  rcases exists_mul_self_ne_one_or_natCard_eq_two hR1 hU with hΦ | hR2
  · exact Or.inr (d.normalClosure_eq_normalizer hR1 hΦ hlt)
  · obtain ⟨-, h4, hexp, hcen, -⟩ := d.card_two_structure hR1 hR2
    exact Or.inl ⟨hR2, h4, hexp, hcen⟩

end PairData

end CFSG.ClassicalInvolution
