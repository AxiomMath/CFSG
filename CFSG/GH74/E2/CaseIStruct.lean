module

public import CFSG.GH74.E2.OddRank
public import CFSG.GH74.E2.Shapes
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.GH74.E2

open Subgroup

theorem eq_one_of_fixed_ne_one {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 4)
    (σ : MulAut V) (hσ : σ ^ 3 = 1) {v : V} (hv : v ≠ 1) (hσv : σ v = v) : σ = 1 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : Equiv.Perm V := MulAut.toPerm V σ
  have hπ : π ^ 3 ^ 1 = 1 := by
    have : π ^ 3 = 1 := by
      calc π ^ 3 = MulAut.toPerm V (σ ^ 3) := (map_pow _ _ _).symm
        _ = 1 := by rw [hσ, map_one]
    simpa using this
  have hmod := Equiv.Perm.card_compl_support_modEq hπ
  have hcardV : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV
  rw [hcardV] at hmod
  have hsub : ({1, v} : Finset V) ⊆ π.supportᶜ := by
    intro y hy
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact map_one σ
    · rw [Finset.mem_singleton] at hy
      rw [hy]
      exact hσv
  have h2 : 2 ≤ (π.supportᶜ).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (Ne.symm hv)] at this
  have h4 : (π.supportᶜ).card ≤ 4 := hcardV ▸ Finset.card_le_univ _
  have h5 : (π.supportᶜ).card % 3 = 4 % 3 := hmod
  have h6 : (π.supportᶜ).card = 4 := by omega
  have h7 : π.supportᶜ = Finset.univ := Finset.eq_univ_of_card _ (by rw [h6, hcardV])
  ext y
  have : y ∈ π.supportᶜ := by rw [h7]; exact Finset.mem_univ y
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at this
  exact this

section Helpers

variable {C : Type} [Group C] [Finite C]

omit [Finite C] in
theorem exists_elemAb_range_of_localK {Q K : Subgroup C} (hL : LocalK C Q K) {p : ℕ}
    (hp : Odd p) {B : Subgroup C} (hB : ElemAb p B) :
    ∃ R : Subgroup (MulAut ↥K), ElemAb p R ∧
      Nat.card R = Nat.card ↥(B ⊓ centralizer (Q : Set C)) := by
  set BQ : Subgroup C := B ⊓ centralizer (Q : Set C) with hBQdef
  have hnormK : BQ ≤ normalizer (K : Set C) := by
    have := hL.K_normal
    exact Subgroup.le_normalizer_of_normal
  let φ : BQ →* MulAut ↥K := conjAction BQ K hnormK
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hcK : ∀ k ∈ K, (b : C) * k = k * b := by
      intro k hk
      have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : K) : C)) hb
      have h3 : ((φ b ⟨k, hk⟩ : K) : C) = (b : C) * k * (b : C)⁻¹ := rfl
      simp only [h3] at h2
      change (b : C) * k * (b : C)⁻¹ = k at h2
      calc (b : C) * k = ((b : C) * k * (b : C)⁻¹) * b := by group
        _ = k * b := by rw [h2]
    have hcQ : ∀ q ∈ Q, (b : C) * q = q * b := fun q hq =>
      (mem_centralizer_iff.1 b.2.2 q hq).symm
    have hbQ : (b : C) ∈ Q := hL.self_centralizing b hcQ hcK
    apply Subtype.ext
    exact eq_one_of_pgroup_of_pow hL.Q_pgroup hbQ hp (hB.2 b b.2.1)
  have hRel : ElemAb p φ.range := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hB.1 a a.2.1 b b.2.1)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hB.2 a a.2.1)
      rw [this, map_one]
  exact ⟨φ.range, hRel, (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm⟩

theorem rank_add_le_of_two_subgroup {Q K : Subgroup C} (hgen : Gen4 C) (hL : LocalK C Q K)
    {U : Subgroup ↥K} (hU : IsPGroup 2 U) :
    Group.rank Q + Group.rank U ≤ 4 + Group.rank ↥(Q ⊓ U.map K.subtype) ∧
      Nat.card ↥(Q ⊓ U.map K.subtype) ≤ Nat.card (center ↥K) := by
  let T' : Subgroup C := U.map K.subtype
  have hT'2 : IsPGroup 2 T' := hU.map K.subtype
  have hrankT' : Group.rank T' = Group.rank U :=
    (Group.rank_congr (U.equivMapOfInjective K.subtype K.subtype_injective)).symm
  have hcomm : ∀ q ∈ Q, ∀ t ∈ T', q * t = t * q := by
    rintro q hq _ ⟨t, -, rfl⟩
    exact hL.commute q hq t t.2
  refine ⟨?_, ?_⟩
  · have := gen4_rank_add_le hgen Q T' hL.Q_pgroup hT'2 hcomm
    rw [hrankT'] at this
    exact this
  · let f : ↥(Q ⊓ T') → center ↥K := fun x =>
      ⟨⟨x.1, by
        obtain ⟨y, -, hy⟩ := x.2.2
        rw [← hy]; exact y.2⟩, by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact (hL.commute x.1 x.2.1 k k.2).symm⟩
    refine Nat.card_le_card_of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z => ((z : ↥K) : C)) (Subtype.ext_iff.1 hxy)

omit [Finite C] in
theorem exists_inner_conj {K : Subgroup C} [K.Normal]
    (hinner : ∀ φ : MulAut ↥K, φ ^ 3 = 1 → ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹)
    {b : C} (hb : b ^ 3 = 1) :
    ∃ k : C, k ∈ K ∧ ∀ x ∈ K, b * x * b⁻¹ = k * x * k⁻¹ := by
  have hbN : b ∈ normalizer (K : Set C) :=
    (Subgroup.le_normalizer_of_normal : (⊤ : Subgroup C) ≤ normalizer (K : Set C))
      (Subgroup.mem_top b)
  let φ : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbN⟩
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨b, hbN⟩ : normalizer (K : Set C)) ^ 3 = 1 := Subtype.ext (by simpa using hb)
    calc φ ^ 3 = K.normalizerMonoidHom ((⟨b, hbN⟩ : normalizer (K : Set C)) ^ 3) :=
          (map_pow _ _ _).symm
      _ = 1 := by rw [h1, map_one]
  obtain ⟨k, hk⟩ := hinner φ hφ3
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h1 := congrArg Subtype.val (hk ⟨x, hx⟩)
  exact h1

omit [Finite C] in
theorem mem_of_pow_three_mem {K : Subgroup C} {q : C} {s : ℕ} (hs : q ^ (2 ^ s) = 1)
    (h3 : q ^ 3 ∈ K) : q ∈ K := by
  have h32 : IsCoprime (3 : ℤ) 2 := ⟨1, -1, by norm_num⟩
  obtain ⟨u, v, huv⟩ := h32.pow_right (n := s)
  have h2 : q ^ ((2 : ℤ) ^ s) = 1 := by
    have : ((2 : ℤ) ^ s) = ((2 ^ s : ℕ) : ℤ) := by push_cast; rfl
    rw [this, zpow_natCast]
    exact hs
  have h1 : q = (q ^ 3) ^ u := by
    calc q = q ^ (u * 3 + v * (2 ^ s : ℤ)) := by rw [huv, zpow_one]
      _ = (q ^ 3) ^ u := by
        rw [zpow_add, zpow_mul', zpow_mul' q v ((2 : ℤ) ^ s), h2, one_zpow, mul_one]
        norm_cast
  rw [h1]
  exact K.zpow_mem h3 u

omit [Finite C] in
theorem mem_K_of_pow_three {Q K : Subgroup C} (hL : LocalK C Q K)
    (hinner : ∀ φ : MulAut ↥K, φ ^ 3 = 1 → ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹)
    {b : C} (hb : b ^ 3 = 1) (hbQ : ∀ q ∈ Q, b * q = q * b) : b ∈ K := by
  have := hL.K_normal
  obtain ⟨k, hkK, hk⟩ := exists_inner_conj hinner hb
  have hcK : ∀ x ∈ K, (k⁻¹ * b) * x = x * (k⁻¹ * b) := by
    intro x hx
    have h1 := hk x hx
    calc k⁻¹ * b * x = k⁻¹ * (b * x * b⁻¹) * b := by group
      _ = k⁻¹ * (k * x * k⁻¹) * b := by rw [h1]
      _ = x * (k⁻¹ * b) := by group
  have hcQ : ∀ q ∈ Q, (k⁻¹ * b) * q = q * (k⁻¹ * b) := by
    intro q hq
    have h1 := hL.commute q hq k hkK
    have h2 : k⁻¹ * q = q * k⁻¹ := by
      calc k⁻¹ * q = k⁻¹ * (q * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * q) * k⁻¹ := by rw [h1]
        _ = q * k⁻¹ := by group
    calc k⁻¹ * b * q = k⁻¹ * (b * q) := by group
      _ = k⁻¹ * (q * b) := by rw [hbQ q hq]
      _ = (k⁻¹ * q) * b := by group
      _ = (q * k⁻¹) * b := by rw [h2]
      _ = q * (k⁻¹ * b) := by group
  have hqQ : k⁻¹ * b ∈ Q := hL.self_centralizing (k⁻¹ * b) hcQ hcK
  have hbq : b = k * (k⁻¹ * b) := by group
  have hcomm : Commute k (k⁻¹ * b) := (hL.commute _ hqQ k hkK).symm
  have hq3 : (k⁻¹ * b) ^ 3 ∈ K := by
    have h1 : (k * (k⁻¹ * b)) ^ 3 = k ^ 3 * (k⁻¹ * b) ^ 3 := hcomm.mul_pow 3
    rw [← hbq, hb] at h1
    have h2 : (k⁻¹ * b) ^ 3 = (k ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
    rw [h2]
    exact K.inv_mem (K.pow_mem hkK 3)
  obtain ⟨s, hs⟩ := hL.Q_pgroup ⟨k⁻¹ * b, hqQ⟩
  have hs' : (k⁻¹ * b) ^ (2 ^ s) = 1 := congrArg Subtype.val hs
  have hqK : k⁻¹ * b ∈ K := mem_of_pow_three_mem hs' hq3
  have := K.mul_mem hkK hqK
  rwa [← hbq] at this

theorem exists_centralizing_generator {Q K : Subgroup C} (hL : LocalK C Q K) (hD3 : K0Data3)
    (hshape : ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) {A B : Subgroup C} (hA : ElemAb 3 A)
    (hBA : B ≤ A) (hBK : B ≤ K) (hBcard : Nat.card B = 9) {c₀ : C} (hc₀ : c₀ ∈ A)
    (hc₀B : c₀ ∉ B) : ∃ c : C, c ∈ A ∧ c ∉ B ∧ ∀ k ∈ K, c * k = k * c := by
  have := hL.K_normal
  have hinner : ∀ φ : MulAut ↥K, φ ^ 3 = 1 → ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹ :=
    fun φ hφ => hD3.inner3 ↥K hshape φ hφ
  obtain ⟨k, hkK, hk⟩ := exists_inner_conj hinner (hA.2 c₀ hc₀)
  have hkB : ∀ b ∈ B, k * b = b * k := by
    intro b hb
    have h1 := hk b (hBK hb)
    have h2 : c₀ * b = b * c₀ := hA.1 c₀ hc₀ b (hBA hb)
    have h3 : c₀ * b * c₀⁻¹ = b := by rw [h2]; group
    rw [h3] at h1
    calc k * b = (k * b * k⁻¹) * k := by group
      _ = b * k := by rw [← h1]
  have hBel : ElemAb 3 (B.subgroupOf K) :=
    ⟨fun a ha b hb => Subtype.ext (hA.1 a (hBA ha) b (hBA hb)),
      fun a ha => Subtype.ext (hA.2 a (hBA ha))⟩
  have hBcard' : Nat.card (B.subgroupOf K) = 9 := by
    rw [← hBcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  have hkmem : (⟨k, hkK⟩ : ↥K) ∈ B.subgroupOf K :=
    hD3.centralizer3 ↥K hshape (B.subgroupOf K) hBel hBcard' ⟨k, hkK⟩
      (fun b hb => Subtype.ext (hkB (b : C) hb))
  have hkB' : k ∈ B := hkmem
  refine ⟨k⁻¹ * c₀, A.mul_mem (A.inv_mem (hBA hkB')) hc₀, fun h => hc₀B ?_, fun x hx => ?_⟩
  · have := B.mul_mem hkB' h
    simpa using this
  · have h1 := hk x hx
    calc k⁻¹ * c₀ * x = k⁻¹ * (c₀ * x * c₀⁻¹) * c₀ := by group
      _ = k⁻¹ * (k * x * k⁻¹) * c₀ := by rw [h1]
      _ = x * (k⁻¹ * c₀) := by group

open CFSG.OrderReductions.FrattiniAutomorphisms in
theorem exists_irreducible_aut {Q : Subgroup C} (hQ : IsPGroup 2 Q) (hQn : Q.Normal)
    (hrank : Group.rank Q = 2) {c : C} (hc3 : orderOf c = 3)
    (hcQ : ¬ ∀ q ∈ Q, c * q = q * c) {t : C} (htQ : t ∈ Q) (ht1 : t ≠ 1)
    (htc : c * t = t * c) :
    ∃ φ : MulAut ↥Q, (∀ x : ↥Q, ((φ x : ↥Q) : C) = c * x * c⁻¹) ∧ orderOf φ = 3 ∧
      (∀ x : ↥Q, φ x * x⁻¹ ∈ frattini ↥Q → x ∈ frattini ↥Q) ∧ ∃ x : ↥Q, x ≠ 1 ∧ φ x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : c ^ 3 = 1 := cube_eq_one_of_orderOf hc3
  have hcN : c ∈ normalizer (Q : Set C) :=
    (Subgroup.le_normalizer_of_normal : (⊤ : Subgroup C) ≤ normalizer (Q : Set C))
      (Subgroup.mem_top c)
  let φ : MulAut ↥Q := Q.normalizerMonoidHom ⟨c, hcN⟩
  have hφapp : ∀ x : ↥Q, ((φ x : ↥Q) : C) = c * x * c⁻¹ := fun x => rfl
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨c, hcN⟩ : normalizer (Q : Set C)) ^ 3 = 1 := Subtype.ext (by simpa using hc3')
    calc φ ^ 3 = Q.normalizerMonoidHom ((⟨c, hcN⟩ : normalizer (Q : Set C)) ^ 3) :=
          (map_pow _ _ _).symm
      _ = 1 := by rw [h1, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hcQ
    intro q hq
    have h2 := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : C)) h
    have h3 : c * q * c⁻¹ = q := h2
    calc c * q = (c * q * c⁻¹) * c := by group
      _ = q * c := by rw [h3]
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  refine ⟨φ, hφapp, hφord, ?_, ⟨t, htQ⟩, fun h => ht1 (congrArg Subtype.val h), ?_⟩
  · intro x hx
    by_contra hxF
    have hQ' : IsPGroup 2 ↥Q := hQ
    have hVcard : Nat.card (↥Q ⧸ frattini ↥Q) = 4 := by
      rw [card_frattini_quotient_eq_two_pow_rank hQ', hrank]
      norm_num
    obtain ⟨σ, hσdef⟩ : ∃ σ : MulAut (↥Q ⧸ frattini ↥Q),
        σ = quotientAutomorphism (frattini ↥Q) φ := ⟨_, rfl⟩
    have hσapp : ∀ y : ↥Q, σ (QuotientGroup.mk' (frattini ↥Q) y) =
        QuotientGroup.mk' (frattini ↥Q) (φ y) := fun y => by
      rw [hσdef]
      exact quotientAutomorphism_apply _ φ y
    have hσ3 : σ ^ 3 = 1 := by
      calc σ ^ 3 = quotientAutomorphism (frattini ↥Q) (φ ^ 3) := by
            rw [hσdef, map_pow]
        _ = 1 := by rw [hφ3, map_one]
    have hv1 : QuotientGroup.mk' (frattini ↥Q) x ≠ 1 := fun h =>
      hxF ((QuotientGroup.eq_one_iff x).mp h)
    have hσv : σ (QuotientGroup.mk' (frattini ↥Q) x) = QuotientGroup.mk' (frattini ↥Q) x := by
      rw [hσapp]
      exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hx)
    have hσ1 : σ = 1 := eq_one_of_fixed_ne_one hVcard σ hσ3 hv1 hσv
    have hker : φ ∈ (quotientAutomorphism (frattini ↥Q)).ker := by
      rw [mem_quotientAutomorphism_kernel]
      intro y
      rw [← hσapp y, hσ1]
      rfl
    have hcop : ¬ 3 ∣ Nat.card ↥Q := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ'
      rw [hn]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hdvd)
      omega
    exact hφ1 (prime_order_frattini_kernel_trivial 3 φ hφord hcop hker)
  · apply Subtype.ext
    show c * t * c⁻¹ = t
    rw [htc]
    group

end Helpers

theorem caseI_structure {C : Type} [Group C] [Finite C] (hgen : Gen4 C) {Q K : Subgroup C}
    (hL : LocalK C Q K) (hK : K0Shape ↥K) (hD : K0Data) (hD3 : K0Data3) {A : Subgroup C}
    (hA : ElemAb 3 A) (hAcard : Nat.card A = 27) {t : C} (htQ : t ∈ Q) (ht1 : t ≠ 1)
    (htA : ∀ a ∈ A, a * t = t * a) :
    Group.rank Q = 2 ∧ (∀ P : Subgroup C, P ≤ Q → Group.rank P ≤ 2) ∧
      (ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) ∧
      ∃ (B : Subgroup C) (c : C), B ≤ A ∧ B ≤ K ∧ Nat.card B = 9 ∧ c ∈ A ∧ orderOf c = 3 ∧
        (∀ k ∈ K, c * k = k * c) ∧ (∀ a ∈ A, ∃ (i : ℤ) (b : C), b ∈ B ∧ a = c ^ i * b) ∧
        ∃ φ : MulAut ↥Q, (∀ x : ↥Q, ((φ x : ↥Q) : C) = c * x * c⁻¹) ∧ orderOf φ = 3 ∧
          (∀ x : ↥Q, φ x * x⁻¹ ∈ frattini ↥Q → x ∈ frattini ↥Q) ∧
          ∃ x : ↥Q, x ≠ 1 ∧ φ x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn := hL.Q_normal
  have hrankP : ∀ P : Subgroup C, P ≤ Q → Group.rank P ≤ 2 := fun P hP =>
    rank_le_two_of_le_Q hgen hL (hD.center_card _ hK) (fun hc => hD.sylow_rank_simple _ hK hc)
      (fun hc => hD.sylow_rank_cover _ hK hc) hP
  have hrankQ : Group.rank Q ≤ 2 := hrankP Q le_rfl
  obtain ⟨r, hcard, hF1⟩ := exists_centralizer_index_pow hL.Q_pgroup
    (fun b _ x hx => hL.Q_normal.conj_mem x hx b) (p := 3) Nat.prime_three (by norm_num) hA
  rw [orderOf_two_zmod_three] at hF1
  have hr1 : r ≤ 1 := by omega
  obtain ⟨R, hRel, hRcard⟩ := exists_elemAb_range_of_localK hL (p := 3) (by decide) hA
  have hR9 : Nat.card R ≤ 9 := hD3.autRank3_le_two ↥K hK R hRel
  set BQ : Subgroup C := A ⊓ centralizer (Q : Set C) with hBQdef
  rw [hAcard] at hcard
  have hn9 : Nat.card BQ = 9 ∧ r = 1 := by
    interval_cases r
    · norm_num at hcard
      omega
    · norm_num at hcard
      omega
  obtain ⟨hn9, hr⟩ := hn9
  have hrankQ2 : Group.rank Q = 2 := by omega
  have hle1 : ¬ (ShapeA5 ↥K ∨ ShapeL27 ↥K ∨ ShapeL217 ↥K ∨ ShapeSz8 ↥K ∨ Shape2Sz8 ↥K) :=
    fun h => by
      have := hD3.autRank3_le_one ↥K h R hRel
      omega
  have hbad : ¬ (ShapeL28 ↥K ∨ ShapeU33 ↥K ∨ Shape2M12 ↥K) := by
    intro h
    by_cases hM : Shape2M12 ↥K
    · obtain ⟨U, hU, hUr⟩ := hD3.rank_ge4 ↥K hM
      obtain ⟨h1, h2⟩ := rank_add_le_of_two_subgroup hgen hL hU
      have h3 := rank_le_one_of_card_le_two (h2.trans (hD.center_card _ hK))
      omega
    · obtain ⟨U, hU, hUr⟩ := hD3.rank_ge3 ↥K h
      obtain ⟨h1, h2⟩ := rank_add_le_of_two_subgroup hgen hL hU
      have hcen : center ↥K = ⊥ := by
        refine hD3.center_bot ↥K ?_
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hM
      have h3 : Nat.card ↥(Q ⊓ U.map K.subtype) ≤ 1 := by
        calc Nat.card ↥(Q ⊓ U.map K.subtype) ≤ Nat.card (center ↥K) := h2
          _ = 1 := by rw [hcen, Subgroup.card_bot]
      have hsub : Subsingleton ↥(Q ⊓ U.map K.subtype) := by
        have := Nat.card_pos (α := ↥(Q ⊓ U.map K.subtype))
        exact (Nat.card_eq_one_iff_unique.1 (by omega)).1
      rw [Group.rank_eq_zero_iff.2 hsub] at h1
      omega
  have hshape3 : ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K := by
    rcases hK with h | h | h | h | h | h | h | h | h | h | h
    · exact absurd (Or.inl h) hle1
    · exact absurd (Or.inr (Or.inl h)) hle1
    · exact Or.inl h
    · exact absurd (Or.inr (Or.inr (Or.inl h))) hle1
    · exact absurd (Or.inl h) hbad
    · exact Or.inr (Or.inl h)
    · exact absurd (Or.inr (Or.inl h)) hbad
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hle1
    · exact Or.inr (Or.inr h)
    · exact absurd (Or.inr (Or.inr h)) hbad
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr h)))) hle1
  have hinner : ∀ φ : MulAut ↥K, φ ^ 3 = 1 → ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹ :=
    fun φ hφ => hD3.inner3 ↥K hshape3 φ hφ
  have hBQK : BQ ≤ K := fun b hb =>
    mem_K_of_pow_three hL hinner (hA.2 b hb.1) (fun q hq => (mem_centralizer_iff.1 hb.2 q hq).symm)
  obtain ⟨c₀, hc₀A, hc₀B⟩ : ∃ c₀ ∈ A, c₀ ∉ BQ := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ BQ := hcon
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨c, hcA, hcB, hcK⟩ := exists_centralizing_generator hL hD3 hshape3 hA
    (inf_le_left : BQ ≤ A) hBQK hn9 hc₀A hc₀B
  have hcne : c ≠ 1 := fun h => hcB (h ▸ BQ.one_mem)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.2 c hcA) hcne
  have hcQ : ¬ ∀ q ∈ Q, c * q = q * c := fun h =>
    hcB ⟨hcA, mem_centralizer_iff.2 (fun q hq => (h q hq).symm)⟩
  obtain ⟨φ, hφapp, hφord, hφirr, x, hx1, hφx⟩ :=
    exists_irreducible_aut hL.Q_pgroup hQn hrankQ2 hc3 hcQ htQ ht1 (htA c hcA)
  exact ⟨hrankQ2, hrankP, hshape3, BQ, c, inf_le_left, hBQK, hn9, hcA, hc3, hcK,
    eq_zpow_mul_of_mem hA.1 hAcard inf_le_left hn9 hcA hcB, φ, hφapp, hφord, hφirr, x, hx1, hφx⟩

end CFSG.GH74.E2
