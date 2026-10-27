module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporadic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
public import CFSG.RankThree.PartOne.Q1327S.Square
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem exists_pow_eq_one_not_mem [Fact p.Prime] {P A : Subgroup K}
    (hrank : 2 ≤ CFSG.Open.pRank p P) (hAP : A ≤ P) (hA : Nat.card A = p) :
    ∃ b ∈ P, b ^ p = 1 ∧ b ∉ A := by
  obtain ⟨E, hEP, hE, hEcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (Fact.out : p.Prime) hrank
  by_contra hcon
  push Not at hcon
  have hEA : E ≤ A := fun b hb => hcon b (hEP hb) (hE.2 b hb)
  have h1 : Nat.card E ≤ Nat.card A := Subgroup.card_le_of_le hEA
  rw [hEcard, hA] at h1
  have hp := (Fact.out : p.Prime).two_le
  have : p ^ 2 = p * p := by ring
  nlinarith

theorem WCOn.of_conj_order_p [Fact p.Prime]
    (h : ∀ A B : Subgroup K, Nat.card A = p → Nat.card B = p →
      ∃ g : K, A.map (MulAut.conj g).toMonoidHom = B) : WCOn p K := by
  intro P _ hrank A hAP hA
  obtain ⟨b, hbP, hbp, hbA⟩ := exists_pow_eq_one_not_mem hrank hAP hA
  have hb1 : b ≠ 1 := fun h1 => hbA (h1 ▸ A.one_mem)
  have hcardB : Nat.card (Subgroup.zpowers b) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hbp hb1]
  obtain ⟨g, hg⟩ := h A (Subgroup.zpowers b) hA hcardB
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact Subgroup.zpowers_le.2 hbP
  · rw [hg]
    intro hzb
    exact hbA (hzb ▸ Subgroup.mem_zpowers b)

theorem exists_zpowers_eq_of_card_eq [Fact p.Prime] {A : Subgroup K} (hA : Nat.card A = p) :
    ∃ x : K, orderOf x = p ∧ A = Subgroup.zpowers x := by
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  obtain ⟨⟨x, hxA⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAbot
  have hx1 : x ≠ 1 := fun h1 => hx1' (Subtype.ext h1)
  have hxp : x ^ p = 1 := by
    have := pow_card_eq_one' (G := A) (x := ⟨x, hxA⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  refine ⟨x, hord, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxA) ?_).symm⟩
  rw [hA, Nat.card_zpowers, hord]

theorem zpowers_eq_of_mem_ne_one [Fact p.Prime] {A : Subgroup K} (hA : Nat.card A = p) {u : K}
    (hu : u ∈ A) (hu1 : u ≠ 1) : A = Subgroup.zpowers u := by
  have hup : u ^ p = 1 := by
    have := pow_card_eq_one' (G := A) (x := ⟨u, hu⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  have hord : orderOf u = p := orderOf_eq_prime hup hu1
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu) (by
    rw [hA, Nat.card_zpowers, hord])).symm

theorem WCOn.of_sylow_lines [Fact p.Prime] (P₀ : Sylow p K)
    (h : ∀ A : Subgroup K, A ≤ (P₀ : Subgroup K) → Nat.card A = p →
      ∃ u ∈ A, u ≠ 1 ∧ ∃ g : K, g * u * g⁻¹ ∈ (P₀ : Subgroup K) ∧ g * u * g⁻¹ ∉ A) :
    WCOn p K := by
  refine WCOn.of_sylow P₀ fun _ _ A hAP hA => ?_
  obtain ⟨u, hu, hu1, g, hgP, hgA⟩ := h A hAP hA
  have hAu := zpowers_eq_of_mem_ne_one hA hu hu1
  refine ⟨g, ?_, fun heq => hgA ?_⟩
  · rw [hAu, MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hgP
  · rw [← heq]
    exact ⟨u, hu, by simp [MulAut.conj_apply]⟩

theorem not_isMulCommutative_of_order_count [Fact p.Prime] {P : Subgroup K} {k m : ℕ}
    (hP : Nat.card P = p ^ k) (hm : {y : K | y ∈ P ∧ orderOf y = p}.ncard = m)
    (hdvd : ¬ (m + 1) ∣ p ^ k) : ¬ IsMulCommutative P := by
  intro hc
  let T : Subgroup K :=
    { carrier := {y | y ∈ P ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨P.mul_mem ha.1 hb.1, by
        have hab : Commute a b := congrArg Subtype.val (hc.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
        rw [hab.mul_pow, ha.2, hb.2, mul_one]⟩
      one_mem' := ⟨P.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨P.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hTP : T ≤ P := fun y hy => hy.1
  have hTset : (T : Set K) = insert 1 {y : K | y ∈ P ∧ orderOf y = p} := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyP, hyp⟩
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr ⟨hyP, orderOf_eq_prime hyp hy1⟩
    · rintro (rfl | ⟨hyP, hyo⟩)
      · exact ⟨P.one_mem, one_pow p⟩
      · exact ⟨hyP, by rw [← hyo]; exact pow_orderOf_eq_one y⟩
  have hnot : (1 : K) ∉ {y : K | y ∈ P ∧ orderOf y = p} := by
    rintro ⟨-, h1⟩
    rw [orderOf_one] at h1
    exact (Fact.out : p.Prime).one_lt.ne h1
  have hcardT : Nat.card T = m + 1 := by
    have h1 : Nat.card T = (T : Set K).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [h1, hTset, Set.ncard_insert_of_notMem hnot, hm]
  have := Subgroup.card_dvd_of_le hTP
  rw [hcardT, hP] at this
  exact hdvd this

theorem WCOn.of_conj_elements [Fact p.Prime]
    (h : ∀ x y : K, orderOf x = p → orderOf y = p → ∃ k : K, k * x * k⁻¹ = y) : WCOn p K := by
  refine WCOn.of_conj_order_p fun A B hA hB => ?_
  obtain ⟨x, hx, rfl⟩ := exists_zpowers_eq_of_card_eq hA
  obtain ⟨y, hy, rfl⟩ := exists_zpowers_eq_of_card_eq hB
  obtain ⟨k, hk⟩ := h x y hx hy
  refine ⟨k, ?_⟩
  rw [MonoidHom.map_zpowers]
  congr 1

theorem WCOn.of_sylow_normalizer [Fact p.Prime] (P₀ : Sylow p K)
    (h : ∀ A : Subgroup K, A ≤ (P₀ : Subgroup K) → Nat.card A = p →
      ∃ g ∈ Subgroup.normalizer ((P₀ : Subgroup K) : Set K),
        A.map (MulAut.conj g).toMonoidHom ≠ A) : WCOn p K := by
  refine WCOn.of_sylow P₀ fun _ _ A hAP hA => ?_
  obtain ⟨g, hg, hne⟩ := h A hAP hA
  refine ⟨g, ?_, hne⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 hg a).1 (hAP ha)

theorem WCOn.of_normalizer_transitive [Fact p.Prime]
    (h : ∀ P : Sylow p K, ∀ a b : K, a ∈ (P : Subgroup K) → b ∈ (P : Subgroup K) → a ≠ 1 →
      b ≠ 1 → ∃ n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), n * a * n⁻¹ = b) :
    WCOn p K := by
  intro P _ hrank A hAP hA
  obtain ⟨b, hbP, hbp, hbA⟩ := exists_pow_eq_one_not_mem hrank hAP hA
  have hb1 : b ≠ 1 := fun h1 => hbA (h1 ▸ A.one_mem)
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  obtain ⟨⟨a, haA⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAbot
  have ha1 : a ≠ 1 := fun h1 => ha1' (Subtype.ext h1)
  obtain ⟨n, hn, hnab⟩ := h P a b (hAP haA) hbP ha1 hb1
  refine ⟨n, ?_, fun heq => hbA ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hn c).1 (hAP hc)
  · have hmem : b ∈ A.map (MulAut.conj n).toMonoidHom :=
      ⟨a, haA, by simpa [MulAut.conj_apply] using hnab⟩
    rw [heq] at hmem
    exact hmem

theorem WCOn.of_normalizer_irreducible [Fact p.Prime]
    (h : ∀ P : Sylow p K, ∀ C : Subgroup K, C ≤ (P : Subgroup K) →
      Subgroup.normalizer ((P : Subgroup K) : Set K) ≤ Subgroup.normalizer (C : Set K) →
        C = ⊥ ∨ C = (P : Subgroup K)) : WCOn p K := by
  intro P _ hrank A hAP hA
  obtain ⟨b, hbP, hbp, hbA⟩ := exists_pow_eq_one_not_mem hrank hAP hA
  by_contra hcon
  push Not at hcon
  have hN : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤ Subgroup.normalizer (A : Set K) := by
    intro n hn
    have hle : A.map (MulAut.conj n).toMonoidHom ≤ (P : Subgroup K) := by
      rintro _ ⟨c, hc, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hn c).1 (hAP hc)
    have heq : A.map (MulAut.conj n).toMonoidHom = A := hcon n hle
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have : n * c * n⁻¹ ∈ A.map (MulAut.conj n).toMonoidHom := ⟨c, hc, by simp [MulAut.conj_apply]⟩
      rwa [heq] at this
    · intro hc
      rw [← heq] at hc
      obtain ⟨c', hc', hcc⟩ := hc
      have : c' = c := by
        have := (MulAut.conj n).injective (a₁ := c') (a₂ := c)
          (by simpa [MulAut.conj_apply] using hcc)
        exact this
      exact this ▸ hc'
  rcases h P A hAP hN with h1 | h1
  · rw [h1, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  · exact hbA (h1 ▸ hbP)

theorem WCOn.of_normalizer_invariant [Fact p.Prime] (c : ℕ)
    (hP : ∀ P : Sylow p K, Nat.card (P : Subgroup K) = c + 1)
    (h : ∀ P : Sylow p K, ∀ O : Set K, O ⊆ ((P : Subgroup K) : Set K) \ {1} →
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) →
        O.ncard = 0 ∨ O.ncard = c) : WCOn p K := by
  refine WCOn.of_normalizer_irreducible fun P C hCP hN => ?_
  have hO := h P ((C : Set K) \ {1}) (Set.diff_subset_diff_left hCP) (by
    intro n hn t ht
    have hnC : ∀ y, y ∈ C ↔ n * y * n⁻¹ ∈ C := Subgroup.mem_normalizer_iff.1 (hN hn)
    refine ⟨(hnC t).1 ht.1, fun h1 => ht.2 ?_⟩
    have : t = 1 := by
      have := congrArg (fun z => n⁻¹ * z * n) h1
      simpa [mul_assoc] using this
    exact this)
  have hCfin : (C : Set K).ncard = Nat.card C := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h1 : (((C : Set K) \ {1}).ncard) = Nat.card C - 1 := by
    rw [Set.ncard_diff_singleton_of_mem C.one_mem, hCfin]
  have hpos : 0 < Nat.card C := Nat.card_pos
  rw [h1] at hO
  rcases hO with h0 | hc
  · left
    exact Subgroup.eq_bot_of_card_eq C (by omega)
  · right
    exact Subgroup.eq_of_le_of_card_ge hCP (by rw [hP P]; omega)

open CFSG.RankThree.PartOne.Q1327S in
theorem plane_exp_eq {x y : K} (hp : p.Prime) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) (hcard : Nat.card (Subgroup.closure ({x, y} : Set K)) = p ^ 2)
    {m n m' n' : ℕ} (h : x ^ m * y ^ n = x ^ m' * y ^ n') :
    (m : ZMod p) = m' ∧ (n : ZMod p) = n' := by
  have hinj := injective_of_card_sq hp hx hy hxy hcard
  rw [pow_eq_pow_mod m hx, pow_eq_pow_mod n hy, pow_eq_pow_mod m' hx,
    pow_eq_pow_mod n' hy] at h
  have key := @hinj (⟨m % p, Nat.mod_lt _ hp.pos⟩, ⟨n % p, Nat.mod_lt _ hp.pos⟩)
    (⟨m' % p, Nat.mod_lt _ hp.pos⟩, ⟨n' % p, Nat.mod_lt _ hp.pos⟩) h
  rw [Prod.mk.injEq, Fin.mk.injEq, Fin.mk.injEq] at key
  exact ⟨(ZMod.natCast_eq_natCast_iff' m m' p).2 key.1,
    (ZMod.natCast_eq_natCast_iff' n n' p).2 key.2⟩

open CFSG.RankThree.PartOne.Q1327S in
theorem WCOn.of_square_witness [Fact p.Prime] {x y h : K} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) (hcard : Nat.card (Subgroup.closure ({x, y} : Set K)) = p ^ 2)
    (h3 : ¬ p ^ 3 ∣ Nat.card K) {a b c d : ℕ}
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b) (hhy : h * y * h⁻¹ = x ^ c * y ^ d)
    (hirr : ∀ i j k : ZMod p, (i ≠ 0 ∨ j ≠ 0) → (a : ZMod p) * i + c * j = k * i →
      (b : ZMod p) * i + d * j = k * j → False) : WCOn p K := by
  classical
  have hp : p.Prime := Fact.out
  have hfac : (Nat.card K).factorization p = 2 := by
    have hdvd : p ^ 2 ∣ Nat.card K := hcard ▸ Subgroup.card_subgroup_dvd_card _
    have h1 := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
    have h4 : ¬ 3 ≤ (Nat.card K).factorization p := fun h =>
      h3 ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h)
    omega
  have hQ : Nat.card (Subgroup.closure ({x, y} : Set K)) =
      p ^ (Nat.card K).factorization p := by rw [hfac, hcard]
  let P₀ : Sylow p K := Sylow.ofCard _ hQ
  have hP₀ : (P₀ : Subgroup K) = Subgroup.closure ({x, y} : Set K) := Sylow.coe_ofCard _ _
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set K) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set K) := Subgroup.subset_closure (by simp)
  have hx' : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set K) := by
    rw [hhx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxQ _) (Subgroup.pow_mem _ hyQ _)
  have hy' : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set K) := by
    rw [hhy]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxQ _) (Subgroup.pow_mem _ hyQ _)
  have hnorm : h ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set K) : Set K) :=
    mem_normalizer_of_conj_le (conj_closure_le hx' hy')
  refine WCOn.of_sylow_normalizer P₀ fun A hAP hA => ?_
  rw [hP₀] at hAP
  refine ⟨h, by rw [hP₀]; exact hnorm, fun heq => ?_⟩
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hA
    exact hp.one_lt.ne hA
  obtain ⟨⟨t, htA⟩, ht1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAbot
  have ht1 : t ≠ 1 := fun h1 => ht1' (Subtype.ext h1)
  have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy
  obtain ⟨i, j, k, hi, hj, -, hij⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp.pos hx hy
    (by rw [hz]; exact Commute.one_left x) (by rw [hz]; exact Commute.one_left y) (hAP htA)
  rw [hz, one_pow, mul_one] at hij
  subst hij
  have hmem : h * (x ^ i * y ^ j) * h⁻¹ ∈ A := by
    have : h * (x ^ i * y ^ j) * h⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom :=
      ⟨x ^ i * y ^ j, htA, by simp [MulAut.conj_apply]⟩
    rwa [heq] at this
  have htp : (x ^ i * y ^ j) ^ p = 1 := by
    have := pow_card_eq_one' (G := A) (x := ⟨x ^ i * y ^ j, htA⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  have hord : orderOf (x ^ i * y ^ j) = p := orderOf_eq_prime htp ht1
  have hAeq : A = Subgroup.zpowers (x ^ i * y ^ j) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 htA) ?_).symm
    rw [hA, Nat.card_zpowers, hord]
  rw [hAeq, mem_zpowers_iff_mem_range_orderOf] at hmem
  obtain ⟨m, -, hm⟩ := Finset.mem_image.1 hmem
  have hc : Commute x y := hxy
  have hconj := conj_mul_pow hxy hhx hhy i j
  have htm : (x ^ i * y ^ j) ^ m = x ^ (i * m) * y ^ (j * m) := by
    rw [(hc.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul]
  rw [htm, hconj] at hm
  have hexp := plane_exp_eq hp hx hy hxy hcard hm.symm
  refine hirr (i : ZMod p) (j : ZMod p) (m : ZMod p) ?_ ?_ ?_
  · by_contra hcon
    push Not at hcon
    obtain ⟨h0i, h0j⟩ := hcon
    have hi0 : i = 0 := by
      have := (ZMod.natCast_eq_zero_iff i p).1 h0i
      exact Nat.eq_zero_of_dvd_of_lt this hi
    have hj0 : j = 0 := by
      have := (ZMod.natCast_eq_zero_iff j p).1 h0j
      exact Nat.eq_zero_of_dvd_of_lt this hj
    apply ht1
    rw [hi0, hj0]
    simp
  · have := hexp.1
    push_cast at this
    linear_combination this
  · have := hexp.2
    push_cast at this
    linear_combination this

theorem WCOn.of_cubic [Fact p.Prime] {x y : K} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : ⁅x, y⁆ ≠ 1) (hc : Nat.card (Subgroup.closure ({x, y} : Set K)) = p ^ 3) : WCOn p K :=
  WCOn.of_hasNoncommPair ⟨x, y, hx, hy, fun h => hz (commutatorElement_eq_one_iff_mul_comm.2 h),
    IsPGroup.of_card hc⟩

open CFSG.RankThree.PartOne.Q1327S in
theorem WCOn.of_plane_fusion [Fact p.Prime] {s t : K} (hs : s ^ p = 1) (ht : t ^ p = 1)
    (hst : s * t = t * s) (hcard : Nat.card (Subgroup.closure ({s, t} : Set K)) = p ^ 2)
    (h3 : ¬ p ^ 3 ∣ Nat.card K)
    (hS : ∃ (g : K) (a b : ℕ), g * s * g⁻¹ = s ^ a * t ^ b ∧ ((b : ZMod p) ≠ 0))
    (hT : ∀ c : ℕ, c < p → ∃ (g : K) (a b : ℕ), g * (s ^ c * t) * g⁻¹ = s ^ a * t ^ b ∧
      ((a : ZMod p) - b * c ≠ 0)) : WCOn p K := by
  classical
  have hp : p.Prime := Fact.out
  have hfac : (Nat.card K).factorization p = 2 := by
    have hdvd : p ^ 2 ∣ Nat.card K := hcard ▸ Subgroup.card_subgroup_dvd_card _
    have h1 := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
    have h4 : ¬ 3 ≤ (Nat.card K).factorization p := fun h =>
      h3 ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h)
    omega
  have hQ : Nat.card (Subgroup.closure ({s, t} : Set K)) =
      p ^ (Nat.card K).factorization p := by rw [hfac, hcard]
  let P₀ : Sylow p K := Sylow.ofCard _ hQ
  have hP₀ : (P₀ : Subgroup K) = Subgroup.closure ({s, t} : Set K) := Sylow.coe_ofCard _ _
  have hsQ : s ∈ Subgroup.closure ({s, t} : Set K) := Subgroup.subset_closure (by simp)
  have htQ : t ∈ Subgroup.closure ({s, t} : Set K) := Subgroup.subset_closure (by simp)
  have hexp := fun {m n m' n' : ℕ} (h : s ^ m * t ^ n = s ^ m' * t ^ n') =>
    plane_exp_eq hp hs ht hst hcard h
  have hs1 : s ≠ 1 := by
    intro h1
    have := (hexp (m := 1) (n := 0) (m' := 0) (n' := 0) (by rw [h1]; simp)).1
    simp at this
  have hos : orderOf s = p := orderOf_eq_prime hs hs1
  refine WCOn.of_sylow_lines P₀ fun A hAP hA => ?_
  rw [hP₀] at hAP
  rw [hP₀]
  obtain ⟨y, hyord, hAy⟩ := exists_zpowers_eq_of_card_eq hA
  have hyA : y ∈ A := hAy ▸ Subgroup.mem_zpowers y
  have hz : ⁅s, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hst
  obtain ⟨i, j, k, hi, hj, -, hij⟩ := CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp.pos hs
    ht (by rw [hz]; exact Commute.one_left s) (by rw [hz]; exact Commute.one_left t) (hAP hyA)
  rw [hz, one_pow, mul_one] at hij
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hyord; exact hp.one_lt.ne hyord
  by_cases hj0 : j = 0
  ·
    subst hj0
    have hsA : s ∈ A := by
      have hle : A ≤ Subgroup.zpowers s := by
        rw [hAy, Subgroup.zpowers_le, hij]
        simpa using (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) i)
      have heq : A = Subgroup.zpowers s :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hos, hA])
      rw [heq]
      exact Subgroup.mem_zpowers s
    obtain ⟨g, a, b, hg, hb⟩ := hS
    refine ⟨s, hsA, hs1, g, ?_, ?_⟩
    · rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hsQ _) (Subgroup.pow_mem _ htQ _)
    · intro hmem
      rw [hg, zpowers_eq_of_mem_ne_one hA hsA hs1, mem_zpowers_iff_mem_range_orderOf] at hmem
      obtain ⟨n, -, hn⟩ := Finset.mem_image.1 hmem
      have := (hexp (m := n) (n := 0) (m' := a) (n' := b) (by simpa using hn)).2
      exact hb (by simpa using this.symm)
  ·
    have hjne : (j : ZMod p) ≠ 0 := fun h0 =>
      hj0 (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff j p).1 h0) hj)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (j : ZMod p) * m = 1 :=
      ⟨((j : ZMod p)⁻¹).val, by rw [ZMod.natCast_zmod_val]; exact mul_inv_cancel₀ hjne⟩
    have hjm : (j * m) % p = 1 := by
      have h1 : ((j * m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact hm
      have := (ZMod.natCast_eq_natCast_iff' (j * m) 1 p).1 h1
      rwa [Nat.mod_eq_of_lt hp.one_lt] at this
    let c : ℕ := (i * m) % p
    have hcp : c < p := Nat.mod_lt _ hp.pos
    have hu : s ^ c * t = y ^ m := by
      rw [hij, (Commute.pow_pow hst i j).mul_pow, ← pow_mul, ← pow_mul,
        pow_eq_pow_mod (i * m) hs, pow_eq_pow_mod (j * m) ht, hjm, pow_one]
    have huA : s ^ c * t ∈ A := by
      rw [hu, hAy]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) m
    have hu1 : s ^ c * t ≠ 1 := by
      intro h1
      have := (hexp (m := c) (n := 1) (m' := 0) (n' := 0)
        (by rw [pow_one, pow_zero, pow_zero, mul_one]; exact h1)).2
      simp at this
    obtain ⟨g, a, b, hg, hab⟩ := hT c hcp
    refine ⟨s ^ c * t, huA, hu1, g, ?_, ?_⟩
    · rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hsQ _) (Subgroup.pow_mem _ htQ _)
    · intro hmem
      rw [hg, zpowers_eq_of_mem_ne_one hA huA hu1, mem_zpowers_iff_mem_range_orderOf] at hmem
      obtain ⟨n, -, hn⟩ := Finset.mem_image.1 hmem
      have hn' : (s ^ c * t) ^ n = s ^ (c * n) * t ^ n := by
        have := (Commute.pow_pow hst c 1).mul_pow n
        rw [pow_one] at this
        rw [this, ← pow_mul]
      rw [hn'] at hn
      obtain ⟨h1, h2⟩ := hexp hn
      apply hab
      push_cast at h1 h2
      rw [← h1, ← h2]
      ring

theorem card_closure_pair_sq {a b : K} (hp : p.Prime) (hab : a * b = b * a) (ha : a ^ p = 1)
    (hb : b ^ p = 1) (ha1 : a ≠ 1) (hba : ∀ k : ℕ, b ≠ a ^ k) :
    Nat.card (Subgroup.closure ({a, b} : Set K)) = p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := by simpa using hba 0
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hob : orderOf b = p := orderOf_eq_prime hb hb1
  have hdisj : ∀ x, x ∈ Subgroup.zpowers a → x ∈ Subgroup.zpowers b → x = 1 := by
    intro x hxa hxb
    by_contra hx1
    have hxp : x ^ p = 1 := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxa
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hxb' : Subgroup.zpowers x = Subgroup.zpowers b := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxb) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hob]
    have hbx : b ∈ Subgroup.zpowers x := hxb' ▸ Subgroup.mem_zpowers b
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.1 hbx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxa
    have hbA : b ∈ Subgroup.zpowers a :=
      Subgroup.mem_zpowers_iff.2 ⟨m * r, by rw [zpow_mul, hm, hr]⟩
    rw [mem_zpowers_iff_mem_range_orderOf] at hbA
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hbA
    exact hba k hk.symm
  refine CFSG.SectionRank.LocalWitness.card_closure_eq_sq hp.pos ha hb hab ?_
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ h
  simp only at h
  have key : (a ^ i')⁻¹ * a ^ i = b ^ j' * (b ^ j)⁻¹ := by
    calc (a ^ i')⁻¹ * a ^ i = (a ^ i')⁻¹ * (a ^ i * b ^ j) * (b ^ j)⁻¹ := by group
      _ = (a ^ i')⁻¹ * (a ^ i' * b ^ j') * (b ^ j)⁻¹ := by rw [h]
      _ = b ^ j' * (b ^ j)⁻¹ := by group
  have hu : (a ^ i')⁻¹ * a ^ i = 1 :=
    hdisj _ (mul_mem (inv_mem (pow_mem (Subgroup.mem_zpowers a) _))
        (pow_mem (Subgroup.mem_zpowers a) _))
      (key ▸ mul_mem (pow_mem (Subgroup.mem_zpowers b) _)
        (inv_mem (pow_mem (Subgroup.mem_zpowers b) _)))
  have hv : b ^ j' * (b ^ j)⁻¹ = 1 := key ▸ hu
  have e1 : a ^ i = a ^ i' := (inv_mul_eq_one.1 hu).symm
  have e2 : b ^ j' = b ^ j := mul_inv_eq_one.1 hv
  have hi2 : i = i' := by
    have := pow_eq_pow_iff_modEq.1 e1
    rw [hoa] at this
    exact Nat.ModEq.eq_of_lt_of_lt this hi hi'
  have hj2 : j = j' := by
    have := pow_eq_pow_iff_modEq.1 e2.symm
    rw [hob] at this
    exact Nat.ModEq.eq_of_lt_of_lt this hj hj'
  subst hi2
  subst hj2
  rfl

theorem WCOn.of_conj_pair [Fact p.Prime] {a b g : K} (ha1 : a ≠ 1) (ha : a ^ p = 1)
    (hab : a * b = b * a) (hga : g * a * g⁻¹ = b) {c d : ℕ}
    (hgb : g * b * g⁻¹ = a ^ c * b ^ d) (h3 : ¬ p ^ 3 ∣ Nat.card K)
    (hirr : ∀ i j k : ZMod p, (i ≠ 0 ∨ j ≠ 0) → ((0 : ℕ) : ZMod p) * i + c * j = k * i →
      ((1 : ℕ) : ZMod p) * i + d * j = k * j → False) : WCOn p K := by
  have hp : p.Prime := Fact.out
  have hbp : b ^ p = 1 := by
    rw [← hga, conj_pow, ha]
    simp
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hba : ∀ k : ℕ, b ≠ a ^ k := by
    intro k hk
    have e1 : g * b * g⁻¹ = a ^ (k * k) := by
      rw [hk, ← conj_pow, hga, hk, ← pow_mul]
    have e2 : g * b * g⁻¹ = a ^ (c + k * d) := by
      rw [hgb, hk, ← pow_mul, ← pow_add]
    have e3 : a ^ (k * k) = a ^ (c + k * d) := e1.symm.trans e2
    have e4 := pow_eq_pow_iff_modEq.1 e3
    rw [hoa] at e4
    have e5 : ((k * k : ℕ) : ZMod p) = ((c + k * d : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 e4
    push_cast at e5
    refine hirr ((k : ZMod p) - d) 1 k (Or.inr one_ne_zero) ?_ ?_
    · push_cast
      linear_combination -e5
    · push_cast
      ring
  exact WCOn.of_square_witness ha hbp hab (card_closure_pair_sq hp hab ha hbp ha1 hba) h3 (a := 0)
    (b := 1) (c := c) (d := d) (by simpa using hga) (by simpa using hgb) hirr

theorem WCOn.of_small_centralizer [Fact p.Prime] {y : K} (hy : y ^ p = 1) {f m : ℕ}
    (hf : (Nat.card K).factorization p = f)
    (hC : Nat.card (Subgroup.centralizer ({y} : Set K)) = m) (hm : ¬ p ^ f ∣ m) : WCOn p K := by
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨S, hS⟩ := hyp.exists_le_sylow
  refine WCOn.of_sylow S fun hcomm _ A _ _ => ?_
  exfalso
  have hyS : y ∈ (S : Subgroup K) := hS (Subgroup.mem_zpowers y)
  have hle : (S : Subgroup K) ≤ Subgroup.centralizer ({y} : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨z, hyS⟩)).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [S.card_eq_multiplicity, hf, hC] at hdvd
  exact hm hdvd

theorem WCOn.of_self_centralizing [Fact p.Prime] {D : Subgroup K} (hD : IsPGroup p D)
    (hC : ∀ x : K, (∀ d ∈ D, x * d = d * x) → x ∈ D) {f : ℕ}
    (hf : (Nat.card K).factorization p = f) (hcard : Nat.card D < p ^ f) : WCOn p K := by
  obtain ⟨S, hS⟩ := hD.exists_le_sylow
  refine WCOn.of_sylow S fun hcomm _ A _ _ => ?_
  exfalso
  have hle : (S : Subgroup K) ≤ D := fun x hx =>
    hC x fun d hd => congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨d, hS hd⟩)
  have := Subgroup.card_le_of_le hle
  rw [S.card_eq_multiplicity, hf] at this
  omega

theorem WCOn.of_selfcentralizing_in_sylow [Fact p.Prime] {D P : Subgroup K}
    (hP : Nat.card P = p ^ (Nat.card K).factorization p) (hDP : D ≤ P)
    (hC : ∀ x ∈ P, (∀ d ∈ D, x * d = d * x) → x ∈ D) (hlt : Nat.card D < Nat.card P) :
    WCOn p K := by
  let S : Sylow p K := Sylow.ofCard P hP
  have hS : (S : Subgroup K) = P := Sylow.coe_ofCard _ _
  refine WCOn.of_sylow S fun hcomm _ A _ _ => ?_
  exfalso
  rw [hS] at hcomm
  have hle : P ≤ D := fun x hx =>
    hC x hx fun d hd => congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨d, hDP hd⟩)
  exact absurd (Subgroup.card_le_of_le hle) (not_le.2 hlt)

theorem card_centralizer_subgroup {G' : Type*} [Group G'] (H : Subgroup G') (y : H) :
    Nat.card (Subgroup.centralizer ({y} : Set H)) =
      Nat.card ((Subgroup.centralizer ({(y : G')} : Set G') ⊓ H : Subgroup G') : Type _) := by
  have hmap : (Subgroup.centralizer ({y} : Set H)).map H.subtype =
      Subgroup.centralizer ({(y : G')} : Set G') ⊓ H := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, Subgroup.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨congrArg Subtype.val hw, w.2⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, hz2⟩, Subtype.ext hz1, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective]

theorem factorization_eq_of_dvd {N a : ℕ} (hp : p.Prime) (hN : N ≠ 0) (h2 : p ^ a ∣ N)
    (h3 : ¬ p ^ (a + 1) ∣ N) : N.factorization p = a := by
  have h1 := (hp.pow_dvd_iff_le_factorization hN).1 h2
  have h4 : ¬ a + 1 ≤ N.factorization p := fun h =>
    h3 ((hp.pow_dvd_iff_le_factorization hN).2 h)
  omega

theorem card_sylow_eq_pow {N a : ℕ} (hN : Nat.card K = N) (hp : p.Prime) (h2 : p ^ a ∣ N)
    (h3 : ¬ p ^ (a + 1) ∣ N) (P : Sylow p K) : Nat.card (P : Subgroup K) = p ^ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [P.card_eq_multiplicity, hN]
  congr 1
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 h2
  have h4 : ¬ a + 1 ≤ N.factorization p := fun h =>
    h3 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
  omega

theorem mem_of_sq_dvd {N : ℕ} (hN : N ≠ 0) {S : Finset ℕ} (hS : N.primeFactors = S) {q : ℕ}
    (hq : q.Prime) (h : q ^ 2 ∣ N) : q ∈ S := by
  rw [← hS]
  exact Nat.mem_primeFactors.2 ⟨hq, (dvd_pow_self q two_ne_zero).trans h, hN⟩

open CFSG.Blueprint.NativeSporadic in
theorem wcSporadicAt_of_card (s : TauCeti.SporadicName) [Finite (Carrier s)] {N : ℕ}
    (hN : Nat.card (Carrier s) = N)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ^ 2 ∣ N → WCOn q (Carrier s)) : WCSporadicAt s := by
  intro q hq hq2
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases hd : q ^ 2 ∣ N
  · exact h q hq hq2 hd
  · refine WCOn.of_factorization_le_one ?_
    by_contra hlt
    push Not at hlt
    exact hd (hN ▸ (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 hlt)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
