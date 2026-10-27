module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Setup
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Aux

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_rightConjugate {W : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 W) (g : G) :
    CFSG.Open.IsElemAbelian 2 (rightConjugate W g) := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    have hx' : g * x * g⁻¹ ∈ W := (mem_rightConjugate_iff W g x).1 hx
    have hy' : g * y * g⁻¹ ∈ W := (mem_rightConjugate_iff W g y).1 hy
    have h1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := by
      have := hc
      exact setLike_mul_comm hx' hy'
    show x * y = y * x
    have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (y * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · have hx' : g * x * g⁻¹ ∈ W := (mem_rightConjugate_iff W g x).1 hx
    have h1 := hp _ hx'
    rw [conj_pow] at h1
    calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem exists_involution_of_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ w ∈ T, w ≠ 1 ∧ w * w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card T := by
    rcases hT.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.eq_bot_iff_card T).2 h) hT1
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 h2
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  · have h3 : (x : G) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    simpa [pow_two] using h3

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem centralizer_blockU_le_normalizer (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀)
    {g w : G} (hg : g ∉ M) (hwE : w ∈ eSub J g) (hw1 : w ≠ 1) (hw2 : w * w = 1) {a : G}
    (haV : a ∈ blockU J) (haw : a * w = w * a) :
    a ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  have hVc : ∀ x ∈ blockU J, ∀ y ∈ blockU J, x * y = y * x := c.block.blockU_comm
  have hVs : ∀ x ∈ blockU J, x * x = 1 := c.block.blockU_sq_eq_one
  have hwN : w ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.1 hwE).2
  have hwV : ∀ x ∈ blockU J, w * x * w⁻¹ ∈ blockU J := fun x hx => conj_mem_blockU hwN hx
  have h4 := four_le_card_centralizer c.block.isPGroup_blockU c.block.eight_le_card_blockU hVc hVs
    hw2 hwV
  have haA : a ∈ blockU J ⊓ Subgroup.centralizer ({w} : Set G) :=
    ⟨haV, Subgroup.mem_centralizer_singleton_iff.2 haw⟩
  obtain ⟨W, hWA, haW, hW2, hW4⟩ := exists_fourGroup_of_card
    (fun x hx y hy => hVc x (Subgroup.mem_inf.1 hx).1 y (Subgroup.mem_inf.1 hy).1)
    (fun x hx => hVs x (Subgroup.mem_inf.1 hx).1) h4 haA ha1
  have hc' := c.transport g
  have hz' := hz.transport g
  have e : rightConjugate (rightConjugate J g) g⁻¹ = J := by
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hWle : W ≤ rightConjugate (rightConjugate J g) g⁻¹ ⊓ rightConjugate M g := by
    rw [e]
    refine le_inf (fun x hx => blockU_le J (Subgroup.mem_inf.1 (hWA hx)).1) ?_
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({w} : Set G) := (Subgroup.mem_inf.1 (hWA hx)).2
    exact c.centralizer_le_conj (Subgroup.mem_inf.1 hwE).1 ⟨1, by rw [pow_one, pow_two]; exact hw2⟩
      hw1 hxC
  have hgM : g⁻¹ ∉ rightConjugate M g := by
    intro h
    apply hg
    rw [mem_rightConjugate_iff] at h
    have h' : g⁻¹ ∈ M := by simpa using h
    simpa using M.inv_mem h'
  exact hc'.normalizes_of_le_conj hA hz' hgM hWle hW2 hW4 haW

theorem exists_mem_eSub_of_involution (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀)
    {g w : G} (hg : g ∉ M) (hwE : w ∈ eSub J g) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    ∃ b ∈ eSub J g, b * b = 1 ∧ ∃ k ∈ rightConjugate J g, b * k ≠ k * b := by
  have hJ := c.block
  have hwN : w ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.1 hwE).2
  obtain ⟨a, haV, haw, k, hkJ, hak⟩ := hA G J hJ w hwN ⟨1, by rw [pow_one, pow_two]; exact hw2⟩
    (by rw [hw2]; exact Subgroup.one_mem _)
  have haJ : a ∈ J := blockU_le J haV
  have ha1 : a ≠ 1 := fun h => hak (by rw [h]; simp)
  have ha2 : a * a = 1 := hJ.blockU_sq_eq_one a haV
  have haN := c.centralizer_blockU_le_normalizer hA hz hg hwE hw1 hw2 haV haw
  obtain ⟨b, hbV, hba, k', hk'J, hbk'⟩ := hA G (rightConjugate J g) (hJ.conj g) a haN
    ⟨1, by rw [pow_one, pow_two]; exact ha2⟩ (by rw [ha2]; exact Subgroup.one_mem _)
  have hbJg : b ∈ rightConjugate J g := blockU_le (rightConjugate J g) hbV
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hba
  have hbM : b ∈ M := c.centralizer_le_of_mem haJ ⟨1, by rw [pow_one, pow_two]; exact ha2⟩ ha1 hbC
  have hbN : b ∈ Subgroup.normalizer (J : Set G) :=
    c.mem_normalizer_of_centralizes hbM haJ hkJ hak hba
  exact ⟨b, Subgroup.mem_inf.2 ⟨hbJg, hbN⟩, (hJ.conj g).blockU_sq_eq_one b hbV, k', hk'J, hbk'⟩

theorem exists_noncentral (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G} (hg : g ∉ M)
    {T : Subgroup G} (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g)) (hT1 : T ≠ ⊥) :
    ∃ t ∈ T, ∃ k ∈ rightConjugate J g, t * k ≠ k * t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hwT, hw1, hw2⟩ := exists_involution_of_isPGroup hT.isPGroup hT1
  obtain ⟨b, hbE, hb2, k', hk', hbk'⟩ :=
    c.exists_mem_eSub_of_involution hA hz hg (hT.le hwT) hw1 hw2
  have hnorm : eSub J g ≤ Subgroup.normalizer (T : Set G) := by
    intro e he
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht => ?_)
    exact hcon t ht e (Subgroup.mem_inf.1 he).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := by
    have hbpow : b ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hb2
    have hord : orderOf b ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one hbpow
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hbT : b ∈ T :=
    le_of_normal_sylow hT hnorm (Subgroup.zpowers_le.2 hbE) hb2' (Subgroup.mem_zpowers b)
  exact hbk' (hcon b hbT k' hk')

theorem good_inv (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G}
    (hgood : Good56 M J g) : Good56 M J g⁻¹ := by
  obtain ⟨hg, W₀, hW₀, hW₀2, hW₀4⟩ := hgood
  have hVc : ∀ x ∈ blockU J, ∀ y ∈ blockU J, x * y = y * x := c.block.blockU_comm
  have hVs : ∀ x ∈ blockU J, x * x = 1 := c.block.blockU_sq_eq_one
  have hW₀1 : W₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW₀4
    omega
  have hW₀p : IsPGroup 2 W₀ := IsPGroup.of_card (n := 2) (by rw [hW₀4]; norm_num)
  obtain ⟨w, hwW, hw1, hw2⟩ := exists_involution_of_isPGroup hW₀p hW₀1
  have hwE : w ∈ eSub J g := hW₀ hwW
  have hwN : w ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.1 hwE).2
  have hwV : ∀ x ∈ blockU J, w * x * w⁻¹ ∈ blockU J := fun x hx => conj_mem_blockU hwN hx
  have h4 := four_le_card_centralizer c.block.isPGroup_blockU c.block.eight_le_card_blockU hVc hVs
    hw2 hwV
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ blockU J ⊓ Subgroup.centralizer ({w} : Set G), a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : blockU J ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at h4
    omega
  obtain ⟨W, hWA, -, hW2, hW4⟩ := exists_fourGroup_of_card
    (fun x hx y hy => hVc x (Subgroup.mem_inf.1 hx).1 y (Subgroup.mem_inf.1 hy).1)
    (fun x hx => hVs x (Subgroup.mem_inf.1 hx).1) h4 haA ha1
  have hWN : ∀ x ∈ W, x ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
    intro x hx
    have hxA := Subgroup.mem_inf.1 (hWA hx)
    exact c.centralizer_blockU_le_normalizer hA hz hg hwE hw1 hw2 hxA.1
      (Subgroup.mem_centralizer_singleton_iff.1 hxA.2)
  refine ⟨?_, rightConjugate W g⁻¹, ?_, isElemAbelian_rightConjugate hW2 g⁻¹, ?_⟩
  · intro h
    exact hg (by simpa using M.inv_mem h)
  · intro y hy
    rw [mem_rightConjugate_iff] at hy
    have hyW : g⁻¹ * y * g⁻¹⁻¹ ∈ W := hy
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      exact blockU_le J (Subgroup.mem_inf.1 (hWA hyW)).1
    · have := mem_normalizer_rightConjugate.1 (hWN _ hyW)
      have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
      rwa [e] at this
  · rw [rightConjugate_card, hW4]

theorem card_le_of_le_normalizer (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G}
    {T : Subgroup G} (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    {R : Subgroup G} (hRJ : R ≤ J)
    (hRN : R ≤ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G))
    (hR2 : IsPGroup 2 R) : Nat.card R ≤ Nat.card T := by
  have hinv := c.good_inv hA hz hgood
  have hle : rightConjugate R g⁻¹ ≤ eSub J g⁻¹ := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have hyR : g⁻¹ * y * g⁻¹⁻¹ ∈ R := hy
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      exact hRJ hyR
    · have := mem_normalizer_rightConjugate.1 (hRN hyR)
      have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
      rwa [e] at this
  have := card_le_of_max hT hmax hinv hle (hR2.map _)
  rwa [rightConjugate_card] at this

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
