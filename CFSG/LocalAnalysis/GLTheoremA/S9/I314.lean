module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement

private theorem i314_prime_mul_card_le {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {B B' : Subgroup G} (hB' : CFSG.Open.IsElemAbelian q B') (hBB : B < B') :
    q * Nat.card B ≤ Nat.card B' := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hB : CFSG.Open.IsElemAbelian q B := hB'.mono hBB.le
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hB.isPGroup
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp hB'.isPGroup
  have hlt : Nat.card B < Nat.card B' := Subgroup.card_lt_of_lt hBB
  rw [hs, ht] at hlt ⊢
  have hst : s < t := (Nat.pow_lt_pow_iff_right hq.one_lt).1 hlt
  calc q * q ^ s = q ^ (s + 1) := (pow_succ' q s).symm
    _ ≤ q ^ t := Nat.pow_le_pow_right hq.pos hst

private theorem i314_commutator_mul {G : Type} [Group G] {R D : Subgroup G}
    (hDc : ∀ d ∈ D, ∀ x ∈ R, d * x = x * d) (hDcomm : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ D)
    (hDR : D ≤ R) {a x y : G} (ha : a ∈ R) (hx : x ∈ R) (hy : y ∈ R) :
    ⁅x * y, a⁆ = ⁅x, a⁆ * ⁅y, a⁆ := by
  have hc : ⁅y, a⁆ ∈ D := hDcomm y hy a ha
  have he : ⁅x, a⁆ ∈ D := hDcomm x hx a ha
  have hcR : ⁅y, a⁆ ∈ R := hDR hc
  have hxc : x * ⁅y, a⁆ = ⁅y, a⁆ * x := (hDc _ hc x hx).symm
  have hec : ⁅x, a⁆ * ⁅y, a⁆ = ⁅y, a⁆ * ⁅x, a⁆ := hDc _ he _ hcR
  have hyc : y * a * y⁻¹ = ⁅y, a⁆ * a := by
    rw [commutatorElement_def]
    group
  calc ⁅x * y, a⁆ = x * (y * a * y⁻¹) * x⁻¹ * a⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = x * (⁅y, a⁆ * a) * x⁻¹ * a⁻¹ := by rw [hyc]
    _ = (x * ⁅y, a⁆) * a * x⁻¹ * a⁻¹ := by group
    _ = (⁅y, a⁆ * x) * a * x⁻¹ * a⁻¹ := by rw [hxc]
    _ = ⁅y, a⁆ * (x * a * x⁻¹ * a⁻¹) := by group
    _ = ⁅y, a⁆ * ⁅x, a⁆ := by rw [commutatorElement_def x a]
    _ = ⁅x, a⁆ * ⁅y, a⁆ := hec.symm

private theorem i314_card_step {G : Type} [Group G] [Finite G] {R D : Subgroup G}
    (hDc : ∀ d ∈ D, ∀ x ∈ R, d * x = x * d) (hDcomm : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ D)
    (hDR : D ≤ R) {a : G} (ha : a ∈ R) (B : Subgroup G) :
    Nat.card ↥(R ⊓ Subgroup.centralizer (B : Set G)) ≤
      Nat.card ↥(R ⊓ Subgroup.centralizer ((B ⊔ Subgroup.zpowers a : Subgroup G) : Set G)) *
        Nat.card ↥D := by
  let φ : ↥(R ⊓ Subgroup.centralizer (B : Set G)) →* G :=
    { toFun := fun x => ⁅(x : G), a⁆
      map_one' := by simp
      map_mul' := fun x y => i314_commutator_mul hDc hDcomm hDR ha x.2.1 y.2.1 }
  have hker : φ.ker.map (R ⊓ Subgroup.centralizer (B : Set G)).subtype ≤
      R ⊓ Subgroup.centralizer ((B ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : ⁅(x : G), a⁆ = 1 := hx
    have hxa : (x : G) * a = a * x := commutatorElement_eq_one_iff_mul_comm.1 hx1
    have hxB : ∀ b ∈ B, b * (x : G) = (x : G) * b := Subgroup.mem_centralizer_iff.1 x.2.2
    have hle : B ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer {(x : G)} := by
      refine sup_le ?_ (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hxa.symm))
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxB b hb)
    refine ⟨x.2.1, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hrange : φ.range ≤ D := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    exact hDcomm _ x.2.1 a ha
  calc Nat.card ↥(R ⊓ Subgroup.centralizer (B : Set G))
      = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ((B ⊔ Subgroup.zpowers a : Subgroup G) : Set G)) *
          Nat.card ↥D := by
        apply Nat.mul_le_mul
        · calc Nat.card φ.ker
              = Nat.card (φ.ker.map (R ⊓ Subgroup.centralizer (B : Set G)).subtype) :=
                (Subgroup.card_map_of_injective (R ⊓ Subgroup.centralizer (B : Set G)).subtype_injective).symm
            _ ≤ _ := Subgroup.card_le_of_le hker
        · exact Subgroup.card_le_of_le hrange

private theorem i314_index_bound {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {R D A : Subgroup G}
    (hDc : ∀ d ∈ D, ∀ x ∈ R, d * x = x * d) (hDcomm : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ D)
    (hDR : D ≤ R) (hAR : A ≤ R) (hA : CFSG.Open.IsElemAbelian q A) (d : ℕ) :
    ∀ B : Subgroup G, B ≤ A → Nat.card ↥A ≤ q ^ d * Nat.card ↥B →
      Nat.card ↥(R ⊓ Subgroup.centralizer (B : Set G)) ≤
        Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥D ^ d := by
  induction d with
  | zero =>
    intro B hBA hcard
    have hBA' : B = A := Subgroup.eq_of_le_of_card_ge hBA (by simpa using hcard)
    subst hBA'
    simp
  | succ d ih =>
    intro B hBA hcard
    by_cases hBeq : B = A
    · subst hBeq
      have hpos : 0 < Nat.card ↥D ^ (d + 1) := pow_pos Nat.card_pos _
      exact Nat.le_mul_of_pos_right _ hpos
    · obtain ⟨a, haA, haB⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hBA hBeq)
      have hBB' : B < B ⊔ Subgroup.zpowers a :=
        SetLike.lt_iff_le_and_exists.2
          ⟨le_sup_left, a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a), haB⟩
      have hB'A : B ⊔ Subgroup.zpowers a ≤ A := sup_le hBA (Subgroup.zpowers_le.2 haA)
      have hq' : q * Nat.card ↥B ≤ Nat.card ↥(B ⊔ Subgroup.zpowers a : Subgroup G) :=
        i314_prime_mul_card_le hq (hA.mono hB'A) hBB'
      have hcard' : Nat.card ↥A ≤ q ^ d * Nat.card ↥(B ⊔ Subgroup.zpowers a : Subgroup G) := by
        calc Nat.card ↥A ≤ q ^ (d + 1) * Nat.card ↥B := hcard
          _ = q ^ d * (q * Nat.card ↥B) := by ring
          _ ≤ q ^ d * Nat.card ↥(B ⊔ Subgroup.zpowers a : Subgroup G) :=
              Nat.mul_le_mul_left _ hq'
      have h1 := ih (B ⊔ Subgroup.zpowers a) hB'A hcard'
      have h2 := i314_card_step hDc hDcomm hDR (hAR haA) B
      calc Nat.card ↥(R ⊓ Subgroup.centralizer (B : Set G))
          ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ((B ⊔ Subgroup.zpowers a : Subgroup G) : Set G)) *
              Nat.card ↥D := h2
        _ ≤ (Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥D ^ d) * Nat.card ↥D :=
            Nat.mul_le_mul_right _ h1
        _ = Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥D ^ (d + 1) := by ring

theorem i314At_holds : I314At := by
  intro G _ _ q k R N hq hexp hclass hDN hNR hk
  haveI : Fact q.Prime := ⟨hq⟩
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨A, hAR, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank hq1 R
  generalize hm : CFSG.Open.pRank q R = m at hAcard ⊢
  have hmax : ∀ E : Subgroup G, E ≤ R → CFSG.Open.IsElemAbelian q E → ∀ s : ℕ,
      Nat.card ↥E = q ^ s → s ≤ m := by
    intro E hER hE s hs
    rw [← hm]
    exact CFSG.SectionRank.le_pRank hq1 hER hE hs
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = (⁅R, R⁆ : Subgroup G) := ⟨_, rfl⟩
  have hDN' : D ≤ N := by
    rw [hD]
    exact hDN
  have hDR : D ≤ R := hDN'.trans hNR
  have hDcomm : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ D := by
    intro x hx y hy
    rw [hD]
    exact Subgroup.commutator_mem_commutator hx hy
  have hDc : ∀ d ∈ D, ∀ x ∈ R, d * x = x * d := by
    have hle : (⁅R, R⁆ : Subgroup G) ≤ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.commutator_le.2 fun u hu v hv => Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      exact (hclass u hu v hv w hw).symm
    intro d hd x hx
    have hd' : d ∈ (⁅R, R⁆ : Subgroup G) := by
      rw [← hD]
      exact hd
    exact (Subgroup.mem_centralizer_iff.1 (hle hd') x hx).symm
  have hCA : ∀ y ∈ R, (∀ a ∈ A, a * y = y * a) → y ∈ A := by
    intro y hyR hyc
    by_contra hyA
    have hyS : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hlt : A < A ⊔ Subgroup.zpowers y :=
      SetLike.lt_iff_le_and_exists.2 ⟨le_sup_left, y, hyS, hyA⟩
    have hyab : CFSG.Open.IsElemAbelian q (Subgroup.zpowers y) :=
      CFSG.Open.isElemAbelian_zpowers (hexp y hyR)
    have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact Commute.zpow_right (show Commute a y from hyc a ha) j
    have hS : CFSG.Open.IsElemAbelian q (A ⊔ Subgroup.zpowers y) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hA hyab hcomm
    have hSR : A ⊔ Subgroup.zpowers y ≤ R := sup_le hAR (Subgroup.zpowers_le.2 hyR)
    obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hS.isPGroup
    have hAS := Subgroup.card_lt_of_lt hlt
    rw [hAcard, hs] at hAS
    have hms : m < s := (Nat.pow_lt_pow_iff_right hq1).1 hAS
    have hsm := hmax _ hSR hS s hs
    omega
  have hDA : D ≤ A := by
    intro d hd
    refine hCA d (hDR hd) fun a ha => ?_
    exact (hDc d hd a (hAR ha)).symm
  have hdvd : Nat.card ↥D ∣ q ^ m := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le hDA
  obtain ⟨r, hrm, hDcard⟩ := (Nat.dvd_prime_pow hq).1 hdvd
  have hRD : R ⊓ Subgroup.centralizer (D : Set G) = R := by
    apply inf_eq_left.2
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun d hd => hDc d hd x hx
  have hbound := i314_index_bound hq hDc hDcomm hDR hAR hA (m - r) D hDA (by
    rw [hAcard, hDcard, ← pow_add, Nat.sub_add_cancel hrm])
  rw [hRD] at hbound
  have hCAle : Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card ↥A := by
    apply Subgroup.card_le_of_le
    intro y hy
    exact hCA y hy.1 fun a ha => Subgroup.mem_centralizer_iff.1 hy.2 a ha
  have hRle : Nat.card ↥R ≤ Nat.card ↥A * Nat.card ↥D ^ (m - r) :=
    le_trans hbound (Nat.mul_le_mul_right _ hCAle)
  rw [hAcard, hDcard] at hRle
  have hN : Nat.card ↥D ≤ Nat.card ↥N := Subgroup.card_le_of_le hDN'
  have hkey : q ^ (k + r) ≤ q ^ (m + r * (m - r)) := by
    calc q ^ (k + r) = q ^ k * q ^ r := pow_add q k r
      _ = q ^ k * Nat.card ↥D := by rw [hDcard]
      _ ≤ q ^ k * Nat.card ↥N := Nat.mul_le_mul_left _ hN
      _ ≤ Nat.card ↥R := hk
      _ ≤ q ^ m * (q ^ r) ^ (m - r) := hRle
      _ = q ^ (m + r * (m - r)) := by rw [pow_add, pow_mul]
  have hk2 : k + r ≤ m + r * (m - r) := (Nat.pow_le_pow_iff_right hq1).1 hkey
  obtain ⟨u, rfl⟩ : ∃ u, m = r + u := ⟨m - r, by omega⟩
  have hu : r + u - r = u := by omega
  rw [hu] at hk2
  have hk3 : k ≤ u + r * u := by linarith
  nlinarith [sq_nonneg ((u : ℤ) - (r : ℤ) - 1)]

end CFSG.LocalAnalysis.GLTheoremA
