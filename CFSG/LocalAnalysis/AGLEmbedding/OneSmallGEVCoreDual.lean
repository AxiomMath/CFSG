module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_comm_mem_fusionSet {R : Subgroup G} {z : G} (hzp : orderOf z = 3)
    (hstab : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z = z * y →
      (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ R)
    {s : G} (hsN : s ∈ Subgroup.normalizer (R : Set G)) (hs3 : ∃ k : ℕ, s ^ 3 ^ k = 1)
    {w : G} (hw : w ∈ fusionSet R z) (hsw : s * w = w * s) : s ∈ R := by
  obtain ⟨hw1, n, hn, hwn⟩ := hw
  have hnzo : orderOf (n * z * n⁻¹) = 3 := by
    rw [← hzp]
    exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
  have hzw := mem_zpowers_of_mem_zpowers_of_prime Nat.prime_three hnzo hwn hw1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzw
  have hc : s * (n * z * n⁻¹) = n * z * n⁻¹ * s := by
    rw [← hk]
    exact ((Commute.zpow_right (show Commute s w from hsw) k)).eq
  have hc' : n⁻¹ * s * n * z = z * (n⁻¹ * s * n) := by
    calc n⁻¹ * s * n * z = n⁻¹ * (s * (n * z * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * z * n⁻¹ * s) * n := by rw [hc]
      _ = z * (n⁻¹ * s * n) := by group
  have hN : n⁻¹ * s * n ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hsN) hn
  obtain ⟨j, hj⟩ := hs3
  have h3 : (n⁻¹ * s * n) ^ 3 ^ j = 1 := by
    have : (n⁻¹ * s * n) ^ 3 ^ j = n⁻¹ * s ^ 3 ^ j * n := by
      have h := map_pow (MulAut.conj n⁻¹) s (3 ^ j)
      simpa [MulAut.conj_apply] using h.symm
    rw [this, hj]
    group
  have hR := hstab _ hN hc' ⟨j, h3⟩
  have : s = n * (n⁻¹ * s * n) * n⁻¹ := by group
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp hn _).mp hR

def commutatorHomOfAbelian {R : Subgroup G} (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) {s : G}
    (hsN : s ∈ Subgroup.normalizer (R : Set G)) : R →* R where
  toFun r := ⟨r * (s * r⁻¹ * s⁻¹),
    R.mul_mem r.2 ((Subgroup.mem_normalizer_iff.mp hsN _).mp (R.inv_mem r.2))⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    have ha : s * (a : G)⁻¹ * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hsN _).mp (R.inv_mem a.2)
    have hb : s * (b : G)⁻¹ * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hsN _).mp (R.inv_mem b.2)
    have e1 : s * ((a : G) * b)⁻¹ * s⁻¹ = (s * (b : G)⁻¹ * s⁻¹) * (s * (a : G)⁻¹ * s⁻¹) := by
      group
    show ((a : G) * b) * (s * ((a : G) * b)⁻¹ * s⁻¹) =
      ((a : G) * (s * (a : G)⁻¹ * s⁻¹)) * ((b : G) * (s * (b : G)⁻¹ * s⁻¹))
    rw [e1]
    calc (a : G) * b * ((s * (b : G)⁻¹ * s⁻¹) * (s * (a : G)⁻¹ * s⁻¹))
        = a * (b * ((s * (b : G)⁻¹ * s⁻¹) * (s * (a : G)⁻¹ * s⁻¹))) := by group
      _ = a * (b * ((s * (a : G)⁻¹ * s⁻¹) * (s * (b : G)⁻¹ * s⁻¹))) := by
          rw [hRcomm _ hb _ ha]
      _ = a * ((b * (s * (a : G)⁻¹ * s⁻¹)) * (s * (b : G)⁻¹ * s⁻¹)) := by group
      _ = a * (((s * (a : G)⁻¹ * s⁻¹) * b) * (s * (b : G)⁻¹ * s⁻¹)) := by
          rw [hRcomm _ b.2 _ ha]
      _ = a * (s * (a : G)⁻¹ * s⁻¹) * (b * (s * (b : G)⁻¹ * s⁻¹)) := by group

theorem card_normalizer_le_of_dual {P R T : Subgroup G} {z : G} (hP : IsPGroup 3 P)
    (hRP : R ≤ P) (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRcard : Nat.card R = 27)
    (hTR : T ≤ R) (hTcard : Nat.card T = 9) (hzp : orderOf z = 3)
    (hstab : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z = z * y →
      (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ R)
    (hTZ : ∀ t ∈ T, t ≠ 1 → t ∈ fusionSet R z) :
    Nat.card (P ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ≤ 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := P ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hRN : R ≤ N := le_inf hRP Subgroup.le_normalizer
  have hNp : IsPGroup 3 N := hP.to_le inf_le_left
  have h3 : ∀ s ∈ N, ∃ k : ℕ, s ^ 3 ^ k = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hNp ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  by_contra hlt
  push Not at hlt
  have hRn : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr inf_le_right
  have hidx : 9 ≤ (R.subgroupOf N).index := by
    have hc := Subgroup.card_mul_index (R.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv, hRcard] at hc
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    have hk5 : 5 ≤ k := by
      by_contra h
      push Not at h
      have : 3 ^ k ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
    omega
  have hQp : IsPGroup 3 (↥N ⧸ R.subgroupOf N) := hNp.to_quotient _
  have hQnt : Nontrivial (↥N ⧸ R.subgroupOf N) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index_eq_card]
    omega
  have := hQp.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center (↥N ⧸ R.subgroupOf N))
  obtain ⟨s₁, hs₁⟩ := QuotientGroup.mk_surjective (c : ↥N ⧸ R.subgroupOf N)
  have hs₁R : (s₁ : G) ∉ R := by
    intro h
    apply hc1
    apply Subtype.ext
    rw [← hs₁, Subgroup.coe_one, QuotientGroup.eq_one_iff]
    exact h
  have hs₁c : ∀ s ∈ N, ∃ d ∈ R, s * s₁ * s⁻¹ = s₁ * d := by
    intro s hs
    have hcomm := Subgroup.mem_center_iff.mp c.2 (QuotientGroup.mk ⟨s, hs⟩)
    rw [← hs₁, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
    refine ⟨(s₁ : G)⁻¹ * (s * s₁ * s⁻¹), ?_, by group⟩
    have h1 : ((⟨s, hs⟩ : N) * s₁)⁻¹ * (s₁ * ⟨s, hs⟩) ∈ R.subgroupOf N := hcomm
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (s₁ : G)⁻¹ * (s * s₁ * s⁻¹) =
        s * ((((⟨s, hs⟩ : N) * s₁)⁻¹ * (s₁ * ⟨s, hs⟩) : N) : G)⁻¹ * s⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp hs.2 _).mp (R.inv_mem h1)
  set φ := commutatorHomOfAbelian hRcomm s₁.2.2 with hφ
  set L : Subgroup G := φ.range.map R.subtype with hL
  have hLR : L ≤ R := Subgroup.map_subtype_le _
  have hker : ∀ r : R, r ∈ φ.ker ↔ (r : G) * s₁ = s₁ * r := by
    intro r
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (r : G) * (s₁ * (r : G)⁻¹ * (s₁ : G)⁻¹) = 1 := congrArg Subtype.val h
      calc (r : G) * s₁ = (r : G) * (s₁ * (r : G)⁻¹ * (s₁ : G)⁻¹) * (s₁ * r) := by group
        _ = s₁ * r := by rw [h1, one_mul]
    · intro h
      apply Subtype.ext
      show (r : G) * (s₁ * (r : G)⁻¹ * (s₁ : G)⁻¹) = 1
      calc (r : G) * (s₁ * (r : G)⁻¹ * (s₁ : G)⁻¹) = (r * s₁) * (r : G)⁻¹ * (s₁ : G)⁻¹ := by
            group
        _ = 1 := by rw [h]; group
  have hkerT : φ.ker.map R.subtype ⊓ T = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun t ht => ?_
    obtain ⟨⟨r, hr⟩, hrk, rfl⟩ := ht.1
    by_contra ht1
    have hcomm := (hker ⟨r, hr⟩).mp hrk
    exact hs₁R (mem_of_comm_mem_fusionSet hzp hstab s₁.2.2 (h3 _ s₁.2)
      (hTZ r ht.2 ht1) hcomm.symm)
  have hkcard : Nat.card (φ.ker.map R.subtype) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective R.subtype_injective
  have hk3 : Nat.card φ.ker ≤ 3 := by
    have h1 := mul_card_le_of_inf_eq_bot (Subgroup.map_subtype_le _) hTR hkerT
    rw [hkcard, hTcard, hRcard] at h1
    omega
  have hk2 : 2 ≤ Nat.card φ.ker := by
    have : Group.IsNilpotent N := hNp.isNilpotent
    have hne : R.subgroupOf N ≠ ⊥ := by
      intro h
      have h1 : Nat.card (R.subgroupOf N) = Nat.card R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
      rw [h, Subgroup.card_bot, hRcard] at h1
      omega
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
    have hvR : (v : G) ∈ R := hv.1
    have hvk : (⟨(v : G), hvR⟩ : R) ∈ φ.ker := by
      rw [hker]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hv.2 s₁).symm
    have hne1 : (⟨(v : G), hvR⟩ : R) ≠ 1 := by
      intro h
      apply hv1
      have h' : (v : G) = 1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have h2 : 1 < Nat.card φ.ker := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨_, hvk⟩, 1, fun h => hne1 (congrArg Subtype.val h)⟩⟩
    omega
  have hLcard : Nat.card L = Nat.card φ.range := Subgroup.card_map_of_injective R.subtype_injective
  have hrk : Nat.card φ.ker * Nat.card φ.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hRcard]
  have hL9 : Nat.card L = 9 := by
    rw [hLcard]
    have hk : Nat.card φ.ker = 3 := by
      have hdvd : Nat.card φ.ker ∣ 27 := ⟨_, hrk.symm⟩
      have : Nat.card φ.ker ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    rw [hk] at hrk
    omega
  have hLinv : ∀ s ∈ N, ∀ l ∈ L, s * l * s⁻¹ ∈ L := by
    intro s hs l hl
    obtain ⟨_, ⟨r, rfl⟩, rfl⟩ := hl
    obtain ⟨d, hd, hsd⟩ := hs₁c s hs
    have hr' : s * (r : G) * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hs.2 _).mp r.2
    refine ⟨φ ⟨_, hr'⟩, ⟨_, rfl⟩, ?_⟩
    have hdr : (s * (r : G) * s⁻¹)⁻¹ * d = d * (s * (r : G) * s⁻¹)⁻¹ :=
      hRcomm _ (R.inv_mem hr') _ hd
    show s * (r : G) * s⁻¹ * ((s₁ : G) * (s * (r : G) * s⁻¹)⁻¹ * (s₁ : G)⁻¹) =
      s * ((r : G) * ((s₁ : G) * (r : G)⁻¹ * (s₁ : G)⁻¹)) * s⁻¹
    have hs₁' : (s₁ : G) = s⁻¹ * (s₁ * d) * s := by rw [← hsd]; group
    calc s * (r : G) * s⁻¹ * ((s₁ : G) * (s * (r : G) * s⁻¹)⁻¹ * (s₁ : G)⁻¹)
        = s * (r : G) * s⁻¹ * ((s₁ : G) * ((s * (r : G) * s⁻¹)⁻¹ * d) * d⁻¹ *
          (s₁ : G)⁻¹) := by group
      _ = s * (r : G) * s⁻¹ * ((s₁ : G) * (d * (s * (r : G) * s⁻¹)⁻¹) * d⁻¹ *
          (s₁ : G)⁻¹) := by rw [hdr]
      _ = s * ((r : G) * ((s⁻¹ * (s₁ * d) * s) * (r : G)⁻¹ * (s⁻¹ * (s₁ * d) * s)⁻¹)) * s⁻¹ := by
          group
      _ = s * ((r : G) * ((s₁ : G) * (r : G)⁻¹ * (s₁ : G)⁻¹)) * s⁻¹ := by rw [← hs₁']
  obtain ⟨y, ⟨hyL, hyT⟩, hy1⟩ : ∃ y ∈ L ⊓ T, y ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : L ⊓ T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    have h1 := mul_card_le_of_inf_eq_bot hLR hTR hbot
    rw [hL9, hTcard, hRcard] at h1
    omega
  have hyZ := hTZ y hyT hy1
  have hmem : ∀ s : N, (s : G) * y * (s : G)⁻¹ ∈ ((L : Set G) \ {1}) := fun s =>
    ⟨hLinv s s.2 y hyL, fun h => hy1 (by
      have h1 : (s : G) * y * (s : G)⁻¹ = 1 := h
      calc y = (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * s := by group
        _ = 1 := by rw [h1]; group)⟩
  let f : N ⧸ R.subgroupOf N → ((L : Set G) \ {1} : Set G) :=
    Quotient.lift (fun s : N => (⟨(s : G) * y * (s : G)⁻¹, hmem s⟩ : ((L : Set G) \ {1} : Set G)))
      (fun a b hab => by
        have h : a⁻¹ * b ∈ R.subgroupOf N := QuotientGroup.leftRel_apply.mp hab
        have hr : (a : G)⁻¹ * b ∈ R := by simpa [Subgroup.mem_subgroupOf] using h
        apply Subtype.ext
        have hc := hRcomm _ hr y (hTR hyT)
        show (a : G) * y * (a : G)⁻¹ = b * y * (b : G)⁻¹
        calc (a : G) * y * (a : G)⁻¹
            = a * (((a : G)⁻¹ * b) * y * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by
              rw [hc]; group
          _ = b * y * (b : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro x x'
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction x' using QuotientGroup.induction_on with | H b => ?_
    intro hab
    have h1 : (a : G) * y * (a : G)⁻¹ = b * y * (b : G)⁻¹ := congrArg Subtype.val hab
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    have hab' : ((a⁻¹ * b : N) : G) = (a : G)⁻¹ * b := by simp
    rw [hab']
    have hN' : (a : G)⁻¹ * b ∈ N := N.mul_mem (N.inv_mem a.2) b.2
    refine mem_of_comm_mem_fusionSet hzp hstab hN'.2 (h3 _ hN') hyZ ?_
    calc (a : G)⁻¹ * b * y = (a : G)⁻¹ * (b * y * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * (a * y * (a : G)⁻¹) * b := by rw [h1]
      _ = y * ((a : G)⁻¹ * b) := by group
  have hle : (R.subgroupOf N).index ≤ ((L : Set G) \ {1}).ncard := by
    rw [Subgroup.index, ← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective f hf
  have hL8 : ((L : Set G) \ {1}).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem L.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) hL9
  omega

end CFSG.AGLEmbedding
