module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73SL3
public import CFSG.LieType.HighestRoot.CentLinearBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PullBackSpin
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped MatrixGroups Pointwise

namespace F3L221

theorem sl23_cases : ∀ x : SL23, x = 1 ∨ x = -1 ∨ x ^ 2 = -1 ∨ x ^ 3 = -1 ∨ x ^ 3 = 1 := by
  decide +kernel

theorem sl23_pow_four_of_pow_eight : ∀ x : SL23, x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

theorem sl23_commutator_aux : ∀ q : SL23, q ^ 4 = 1 → ∃ a g : SL23, a ^ 4 = 1 ∧
    ((g ^ 3 = 1 ∧ q = a * g * a ^ 3 * g ^ 2) ∨ (g ^ 4 = 1 ∧ q = a * g * a ^ 3 * g ^ 3)) := by
  decide +kernel

theorem sl23_commutator {q : SL23} (hq : q ^ 4 = 1) :
    ∃ a g : SL23, a ^ 4 = 1 ∧ q = a * g * a⁻¹ * g⁻¹ := by
  obtain ⟨a, g, ha, h | h⟩ := sl23_commutator_aux q hq
  · refine ⟨a, g, ha, ?_⟩
    have ha' : a⁻¹ = a ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← ha]; group)
    have hg' : g⁻¹ = g ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← h.1]; group)
    rw [ha', hg']
    exact h.2
  · refine ⟨a, g, ha, ?_⟩
    have ha' : a⁻¹ = a ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← ha]; group)
    have hg' : g⁻¹ = g ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← h.1]; group)
    rw [ha', hg']
    exact h.2

theorem eq_one_of_mem_center_psl23 {x : PSL(2, ZMod 3)} (hx : x ∈ center (PSL(2, ZMod 3))) :
    x = 1 := by
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [mem_center_iff] at hx
  have key : ∀ g : SL23, g * Y = Y * g ∨ g * Y = -(Y * g) := by
    intro g
    have h1 := hx (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      mem_center_SL23_iff] at h1
    rcases h1 with h1 | h1
    · left
      calc g * Y = (g * Y) * ((g * Y)⁻¹ * (Y * g)) := by rw [h1, mul_one]
        _ = Y * g := by group
    · right
      have h2 : Y * g = -(g * Y) := by
        calc Y * g = (g * Y) * ((g * Y)⁻¹ * (Y * g)) := by group
          _ = -(g * Y) := by rw [h1, mul_neg_one]
      rw [h2, neg_neg]
  rw [QuotientGroup.eq_one_iff, mem_center_SL23_iff]
  exact eq_one_or_neg_one_of_commute_SL23 Y key

variable {Y : Type} [Group Y] [Finite Y]

theorem not_mem_pPrimeCore_of_orderOf {K : Subgroup Y} {z : Y} (hzK : z ∈ K)
    (hz : orderOf z = 2) : (⟨z, hzK⟩ : ↥K) ∉ pPrimeCore 2 ↥K := by
  intro h
  have h1 := orderOf_dvd_natCard (⟨⟨z, hzK⟩, h⟩ : ↥(pPrimeCore 2 ↥K))
  have h2 : orderOf (⟨⟨z, hzK⟩, h⟩ : ↥(pPrimeCore 2 ↥K)) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hz
  rw [h2] at h1
  exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two ↥K)) (even_iff_two_dvd.mpr h1)

theorem nonempty_sl23_of_central {K A : Subgroup Y} (hK : IsSolvableTwoComponentIn K A) {z : Y}
    (hzK : z ∈ K) (hz : orderOf z = 2) (hzc : ∀ k ∈ K, k * z = z * k) :
    Nonempty (↥K ⧸ pPrimeCore 2 ↥K ≃* SL(2, ZMod 3)) := by
  rcases hK.2.2.2 with h | h
  · exfalso
    obtain ⟨e⟩ := h
    have hc : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) ∈
        center (↥K ⧸ pPrimeCore 2 ↥K) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hzc g' g'.2)
    have h1 := eq_one_of_mem_center_psl23 ((mem_center_mulEquiv_iff e _).mpr hc)
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff] at h1
    exact not_mem_pPrimeCore_of_orderOf hzK hz h1
  · exact h

theorem le_pPrimeCore_of_not_mem {K N : Subgroup Y}
    (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* SL(2, ZMod 3)) {z : Y} (hzK : z ∈ K) (hz : orderOf z = 2)
    (hzc : ∀ k ∈ K, k * z = z * k) (hNK : N ≤ K) (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hzN : z ∉ N) : N ≤ (pPrimeCore 2 ↥K).map K.subtype := by
  set R := pPrimeCore 2 ↥K with hR
  set π := QuotientGroup.mk' R with hπ
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hez : e (π ⟨z, hzK⟩) = -1 := by
    have h1 : e (π ⟨z, hzK⟩) * e (π ⟨z, hzK⟩) = 1 := by
      rw [← map_mul, ← map_mul]
      have h2 : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := Subtype.ext hzz
      rw [h2, map_one, map_one]
    rcases eq_one_or_neg_one_of_mul_self_SL23 _ h1 with h | h
    · exfalso
      rw [map_eq_one_iff e e.injective, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h
      exact not_mem_pPrimeCore_of_orderOf hzK hz h
    · exact h
  have hz_of : ∀ n (hn : n ∈ N), e (π ⟨n, hNK hn⟩) = -1 → z ∈ N := by
    intro n hn hen
    have h1 : π ⟨n, hNK hn⟩ = π ⟨z, hzK⟩ := e.injective (hen.trans hez.symm)
    have h2 : (⟨n, hNK hn⟩ : ↥K)⁻¹ * ⟨z, hzK⟩ ∈ R := QuotientGroup.eq.mp h1
    have hm := odd_card_pPrimeCore_two ↥K
    have h3 : ((⟨n, hNK hn⟩ : ↥K)⁻¹ * ⟨z, hzK⟩) ^ Nat.card R = 1 := by
      have h4 := pow_card_eq_one' (G := ↥R) (x := ⟨_, h2⟩)
      have h5 := congrArg Subtype.val h4
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h5
    have h6 : (n⁻¹ * z) ^ Nat.card R = 1 := by
      have h7 := congrArg Subtype.val h3
      simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        using h7
    have hcomm : Commute n⁻¹ z := by
      have h8 : n * z = z * n := hzc n (hNK hn)
      exact (Commute.inv_left h8)
    rw [hcomm.mul_pow, inv_pow] at h6
    obtain ⟨m, hm'⟩ := hm
    have hzm : z ^ Nat.card R = z := by
      rw [hm', pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
    rw [hzm] at h6
    have h9 : z = n ^ Nat.card R := by
      calc z = (n ^ Nat.card R) * ((n ^ Nat.card R)⁻¹ * z) := by group
        _ = n ^ Nat.card R := by rw [h6, mul_one]
    rw [h9]
    exact pow_mem hn _
  intro n hn
  set n₀ : ↥K := ⟨n, hNK hn⟩ with hn₀
  refine ⟨n₀, ?_, rfl⟩
  by_contra hnR
  apply hzN
  have hs1 : e (π n₀) ≠ 1 := by
    rw [Ne, map_eq_one_iff e e.injective, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hnR
  rcases sl23_cases (e (π n₀)) with h | h | h | h | h
  · exact absurd h hs1
  · exact hz_of n hn h
  · refine hz_of (n ^ 2) (pow_mem hn 2) ?_
    rw [← h, ← map_pow, ← map_pow]
    rfl
  · refine hz_of (n ^ 3) (pow_mem hn 3) ?_
    rw [← h, ← map_pow, ← map_pow]
    rfl
  ·
    set Nb : Subgroup (↥K ⧸ R) := (N.subgroupOf K).map π with hNb
    have hNbn : Nb.Normal := by
      have : (N.subgroupOf K).Normal := ⟨fun x hx g => by
        rw [mem_subgroupOf] at hx ⊢
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hNn g g.2 x hx⟩
      exact Subgroup.Normal.map this π (QuotientGroup.mk'_surjective R)
    have hmem : π n₀ ∈ Nb := ⟨n₀, hn, rfl⟩
    have hx3 : π n₀ ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, h, map_one]
    have hx1 : π n₀ ≠ 1 := fun h1 => hs1 (by rw [h1, map_one])
    have htop := normal_eq_top_of_mem_sl23 e hNbn hmem hx3 hx1
    have hzb : π ⟨z, hzK⟩ ∈ Nb := htop ▸ mem_top _
    obtain ⟨n', hn', hn'z⟩ := hzb
    refine hz_of n' (mem_subgroupOf.mp hn') ?_
    rw [← hez, ← hn'z]

omit [Finite Y] in
theorem mem_of_mem_sup_of_odd {A N : Subgroup Y} (hN : N ≤ normalizer (A : Set Y))
    (hodd : Odd (Nat.card N)) {x : Y} (hx : x ∈ A ⊔ N) {n : ℕ} (hxn : x ^ 2 ^ n = 1) :
    x ∈ A := by
  have hxs : x ∈ ((A ⊔ N : Subgroup Y) : Set Y) := hx
  rw [coe_mul_of_right_le_normalizer_left A N hN] at hxs
  obtain ⟨a, ha, o, ho, hao⟩ := hxs
  have hx' : x = a * o := hao.symm
  subst hx'
  have hpow : ∀ j : ℕ, (a * o) ^ j * (o ^ j)⁻¹ ∈ A := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : o ^ j * a * (o ^ j)⁻¹ ∈ A :=
        (mem_normalizer_iff.mp (hN (pow_mem ho j)) a).mp ha
      have h3 : (a * o) ^ (j + 1) * (o ^ (j + 1))⁻¹ =
          ((a * o) ^ j * (o ^ j)⁻¹) * (o ^ j * a * (o ^ j)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [h3]
      exact mul_mem ih hc
  have ho1 : o ^ Nat.card N = 1 := by
    have h1 := pow_card_eq_one' (G := ↥N) (x := ⟨o, ho⟩)
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  have hxm : (a * o) ^ Nat.card N ∈ A := by
    have h1 := hpow (Nat.card N)
    rwa [ho1, inv_one, mul_one] at h1
  have hcop : Nat.Coprime (Nat.card N) (orderOf (a * o)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxn)
      ((Nat.coprime_two_right.mpr hodd).pow_right n)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact pow_mem hxm u

omit [Finite Y] in
theorem mem_sup_inf_of_isSubnormal {M A B K : Subgroup Y} (hBM : B ≤ M) (hKM : K ≤ M)
    (hAn : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B)
    {D : Set Y} (hDB : ∀ q ∈ D, q ∈ A ⊔ B)
    (hD : ∀ q ∈ D, ∃ a ∈ D, ∃ g ∈ K, q * (a * g * a⁻¹ * g⁻¹)⁻¹ ∈ A)
    (hKs : (K.subgroupOf M).IsSubnormal) : ∀ q ∈ D, q ∈ A ⊔ (K ⊓ B) := by
  suffices key : ∀ H : Subgroup ↥M, H.IsSubnormal → K.subgroupOf M ≤ H →
      ∀ q ∈ D, q ∈ A ⊔ (H.map M.subtype ⊓ B) by
    have h1 := key _ hKs le_rfl
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hKM] at h1
  intro H hH
  induction hH with
  | top =>
    intro _ q hq
    rw [← MonoidHom.range_eq_map, range_subtype, inf_eq_right.mpr hBM]
    exact hDB q hq
  | step H H' hle hH' hN ih =>
    intro hKH q hq
    obtain ⟨a, ha, g, hg, hqa⟩ := hD q hq
    have ha' := ih (hKH.trans hle) a ha
    have hSN : H'.map M.subtype ⊓ B ≤ normalizer (A : Set Y) := by
      intro x hx
      have hxM : x ∈ M := hBM (mem_inf.mp hx).2
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hAn x hxM y hy
      · intro hy
        have h1 := hAn x⁻¹ (inv_mem hxM) _ hy
        rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
    have ha's : a ∈ ((A ⊔ (H'.map M.subtype ⊓ B) : Subgroup Y) : Set Y) := ha'
    rw [coe_mul_of_right_le_normalizer_left A _ hSN] at ha's
    obtain ⟨a₁, ha₁, b, hb, hab⟩ := ha's
    have hab' : a = a₁ * b := hab.symm
    subst hab'
    obtain ⟨hbH', hbB⟩ := mem_inf.mp hb
    obtain ⟨b', hb'H', hb'⟩ := hbH'
    have hgM : g ∈ M := hKM hg
    have hgH : (⟨g, hgM⟩ : ↥M) ∈ H := hKH (by rw [mem_subgroupOf]; exact hg)
    have hbM : b ∈ M := hBM hbB
    have hbgH : b * g * b⁻¹ * g⁻¹ ∈ H.map M.subtype := by
      have h1 := hN.conj_mem ⟨⟨g, hgM⟩, hle hgH⟩ (by rw [mem_subgroupOf]; exact hgH)
        ⟨b', hb'H'⟩
      rw [mem_subgroupOf] at h1
      have h2 : ((⟨b', hb'H'⟩ * ⟨⟨g, hgM⟩, hle hgH⟩ * ⟨b', hb'H'⟩⁻¹ : ↥H') : ↥M) *
          (⟨g, hgM⟩ : ↥M)⁻¹ ∈ H := mul_mem h1 (inv_mem hgH)
      refine ⟨_, h2, ?_⟩
      have hb'' : (b' : Y) = b := hb'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_subtype]
      rw [hb'']
    have hbgB : b * g * b⁻¹ * g⁻¹ ∈ B := by
      have h1 := hKB g hg _ (inv_mem hbB)
      have h2 : b * g * b⁻¹ * g⁻¹ = b * (g * b⁻¹ * g⁻¹) := by group
      rw [h2]
      exact mul_mem hbB h1
    have hc : b * g * b⁻¹ ∈ M := mul_mem (mul_mem hbM hgM) (inv_mem hbM)
    have h1 : (a₁ * b) * g * (a₁ * b)⁻¹ * g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ ∈ A := by
      have h2 : (a₁ * b) * g * (a₁ * b)⁻¹ * g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ =
          a₁ * ((b * g * b⁻¹) * a₁⁻¹ * (b * g * b⁻¹)⁻¹) := by group
      rw [h2]
      exact mul_mem ha₁ (hAn _ hc _ (inv_mem ha₁))
    have h3 : q = (q * ((a₁ * b) * g * (a₁ * b)⁻¹ * g⁻¹)⁻¹) *
        ((a₁ * b) * g * (a₁ * b)⁻¹ * g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹) * (b * g * b⁻¹ * g⁻¹) := by
      group
    rw [h3]
    exact mul_mem (mul_mem (mem_sup_left hqa) (mem_sup_left h1))
      (mem_sup_right (mem_inf.mpr ⟨hbgH, hbgB⟩))

end F3L221

end CFSG.ComponentClassification.HarrisLit.T1
