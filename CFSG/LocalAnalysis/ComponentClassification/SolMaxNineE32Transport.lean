module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE32Syl

public section

namespace CFSG.ComponentClassification.SolMax.NineE32

open Equiv Subgroup
open scoped Pointwise

variable {X : Type} [Group X]

theorem exists_conj_le_of_card [Finite X] {P A B : Subgroup X} (hAP : A ≤ P)
    (hA : Nat.card A = 2 ^ (Nat.card P).factorization 2) (hBP : B ≤ P) (hB : IsPGroup 2 B) :
    ∃ c ∈ P, ∀ b ∈ B, c * b * c⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup P := A.subgroupOf P with hA'def
  have hA' : Nat.card A' = 2 ^ (Nat.card P).factorization 2 := by
    rw [← hA]
    exact Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv
  have hB' : IsPGroup 2 (B.subgroupOf P) := hB.of_equiv (subgroupOfEquivOfLe hBP).symm
  obtain ⟨S, hS⟩ := hB'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S (Sylow.ofCard A' hA')
  have h1 : MulAut.conj g • (S : Subgroup P) = A' := by
    rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_ofCard]
  refine ⟨g, g.2, fun b hb => ?_⟩
  have hbS : (⟨b, hBP hb⟩ : P) ∈ (S : Subgroup P) := hS (mem_subgroupOf.mpr hb)
  have h2 := smul_mem_pointwise_smul _ (MulAut.conj g) (S : Subgroup P) hbS
  rw [h1, MulAut.smul_def, MulAut.conj_apply, hA'def, mem_subgroupOf] at h2
  simpa using h2

theorem natCard_comap_of_surjective_aux {G K : Type*} [Group G] [Group K] [Finite G]
    (f : G →* K) (hf : Function.Surjective f) (N : Subgroup K) :
    Nat.card ↥(N.comap f) = Nat.card ↥f.ker * Nat.card ↥N := by
  have : Finite K := Finite.of_surjective f hf
  have h1 := (N.comap f).card_mul_index
  have h2 := N.card_mul_index
  have h3 : (N.comap f).index = N.index := Subgroup.index_comap_of_surjective N hf
  have h4 := card_ker_mul_card_of_surjective hf
  rw [h3] at h1
  have h5 : Nat.card ↥(N.comap f) * N.index = Nat.card ↥f.ker * Nat.card ↥N * N.index := by
    rw [h1, ← h4, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h5

theorem eq_one_of_mem_ker {H : Subgroup X} {φ : ↥H →* A9 × Multiplicative (ZMod 2)}
    (hodd : Odd (Nat.card φ.ker)) {y : ↥H} (hy : φ y = 1) {k : ℕ} (hk : y ^ 2 ^ k = 1) :
    y = 1 := by
  have hd1 : orderOf (⟨y, hy⟩ : φ.ker) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  have hd2 : orderOf (⟨y, hy⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card φ.ker) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  rw [orderOf_eq_one_iff] at h1
  exact congrArg Subtype.val h1

structure Frame (H : Subgroup X) (φ : ↥H →* A9 × Multiplicative (ZMod 2)) (t : X) where
  κ : Multiplicative W →* X
  inj : Function.Injective κ
  mem : ∀ v, κ v ∈ H
  phi : ∀ v, φ ⟨κ v, mem v⟩ = enc v
  ht : κ (Multiplicative.ofAdd tW) = t
  card : Nat.card κ.range = 2 ^ (Nat.card ((A₀.comap φ).map H.subtype)).factorization 2

namespace Frame

variable {H : Subgroup X} {φ : ↥H →* A9 × Multiplicative (ZMod 2)} {t : X} (F : Frame H φ t)
include F

omit F in
theorem mem_P_iff {y : X} : y ∈ (A₀.comap φ).map H.subtype ↔ ∃ hy : y ∈ H, φ ⟨y, hy⟩ ∈ A₀ := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨y'.2, hy'⟩
  · rintro ⟨hy, hφ⟩
    exact ⟨⟨y, hy⟩, hφ, rfl⟩

theorem range_le_P : F.κ.range ≤ (A₀.comap φ).map H.subtype := by
  rintro _ ⟨v, rfl⟩
  exact mem_P_iff.mpr ⟨F.mem v, by rw [F.phi]; exact ⟨v, rfl⟩⟩

theorem card_range : Nat.card F.κ.range = 32 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem exists_conj_mem [Finite X] {y : X} (hy : y ∈ (A₀.comap φ).map H.subtype) {k : ℕ}
    (hk : y ^ 2 ^ k = 1) : ∃ c ∈ (A₀.comap φ).map H.subtype, c * y * c⁻¹ ∈ F.κ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 (zpowers y) := by
    have hord : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨c, hc, hcB⟩ := exists_conj_le_of_card F.range_le_P F.card
    ((zpowers_le (G := X)).mpr hy) hB
  exact ⟨c, hc, hcB y (mem_zpowers y)⟩

theorem exists_conj_eq [Finite X] {B : Subgroup X} (hBP : B ≤ (A₀.comap φ).map H.subtype)
    (hB : Nat.card B = 32) :
    ∃ c ∈ (A₀.comap φ).map H.subtype, B.map (MulAut.conj c).toMonoidHom = F.κ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 5) (by rw [hB]; norm_num)
  obtain ⟨c, hc, hcB⟩ := exists_conj_le_of_card F.range_le_P F.card hBP hB2
  refine ⟨c, hc, eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact hcB b hb
  · rw [F.card_range, ← hB]
    exact le_of_eq (Nat.card_congr ((MulAut.conj c).subgroupMap B).toEquiv)

end Frame

theorem exists_frame [Finite X] {H : Subgroup X} {φ : ↥H →* A9 × Multiplicative (ZMod 2)}
    (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) {t : X} (htH : t ∈ H)
    (ht2 : t * t = 1) (hφt : φ ⟨t, htH⟩ = (1, Multiplicative.ofAdd 1)) :
    Nonempty (Frame H φ t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup X := (A₀.comap φ).map H.subtype with hP
  have htP : t ∈ P := Frame.mem_P_iff.mpr ⟨htH, by rw [hφt, ← enc_tW]; exact ⟨_, rfl⟩⟩
  have hcardP : Nat.card P = Nat.card φ.ker * 32 := by
    rw [hP, Nat.card_congr (equivMapOfInjective _ _ H.subtype_injective).toEquiv.symm,
      natCard_comap_of_surjective_aux φ hφ, card_A₀]
  have hfac : (Nat.card P).factorization 2 = 5 := by
    rw [hcardP, Nat.factorization_mul (by have := hodd.pos; omega) (by decide), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd),
      show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.factorization_pow_self Nat.prime_two]
  have ht : IsPGroup 2 (zpowers (⟨t, htP⟩ : P)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    have h1 : (⟨t, htP⟩ : P) ^ 2 = 1 := Subtype.ext (by simpa [sq] using ht2)
    have h2 : (⟨t, htP⟩ : P) ≠ 1 := by
      intro h
      have ht1 : t = 1 := congrArg Subtype.val h
      have h3 : φ ⟨t, htH⟩ = 1 := by
        rw [show (⟨t, htH⟩ : ↥H) = 1 from Subtype.ext ht1, map_one]
      rw [hφt] at h3
      exact absurd (congrArg Prod.snd h3) (by decide)
    rw [orderOf_eq_prime h1 h2, pow_one]
  obtain ⟨S, hS⟩ := ht.exists_le_sylow
  set A : Subgroup X := (S : Subgroup P).map P.subtype with hA
  have hAP : A ≤ P := map_subtype_le _
  have hcardA : Nat.card A = 32 := by
    rw [hA, Nat.card_congr (equivMapOfInjective _ _ P.subtype_injective).toEquiv.symm,
      Sylow.card_eq_multiplicity, hfac]
    norm_num
  have htA : t ∈ A := ⟨⟨t, htP⟩, hS (mem_zpowers _), rfl⟩
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 5) (by rw [hcardA]; norm_num)
  have hinj : ∀ a ∈ A, ∀ a' ∈ A, ∀ (ha : a ∈ H) (ha' : a' ∈ H),
      φ ⟨a, ha⟩ = φ ⟨a', ha'⟩ → a = a' := by
    intro a hA' a' hA'' ha ha' h
    have hm : a * a'⁻¹ ∈ A := mul_mem hA' (inv_mem hA'')
    obtain ⟨k, hk⟩ := hA2 ⟨_, hm⟩
    have hk' : (⟨a * a'⁻¹, mul_mem ha (inv_mem ha')⟩ : ↥H) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : φ ⟨a * a'⁻¹, mul_mem ha (inv_mem ha')⟩ = 1 := by
      rw [show (⟨a * a'⁻¹, mul_mem ha (inv_mem ha')⟩ : ↥H) = ⟨a, ha⟩ * ⟨a', ha'⟩⁻¹ from rfl,
        map_mul, map_inv, h, mul_inv_cancel]
    have := eq_one_of_mem_ker hodd h1 hk'
    have := congrArg Subtype.val this
    simp only [OneMemClass.coe_one] at this
    exact mul_inv_eq_one.mp this
  have hAH : ∀ a ∈ A, a ∈ H := fun a ha => (Frame.mem_P_iff.mp (hAP ha)).1
  have hAA₀ : ∀ a (ha : a ∈ A), φ ⟨a, hAH a ha⟩ ∈ A₀ := fun a ha =>
    (Frame.mem_P_iff.mp (hAP ha)).2
  have hsurj : ∀ v : Multiplicative W, ∃ a ∈ A, ∃ ha : a ∈ H, φ ⟨a, ha⟩ = enc v := by
    classical
    let g : A → A₀ := fun a => ⟨φ ⟨a, hAH a a.2⟩, hAA₀ a a.2⟩
    have hg : Function.Injective g := by
      intro a a' h
      exact Subtype.ext (hinj a a.2 a' a'.2 _ _ (congrArg Subtype.val h))
    have hg' : Function.Surjective g := by
      have : Fintype A := Fintype.ofFinite _
      have : Fintype A₀ := Fintype.ofFinite _
      refine ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, ?_⟩).2
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardA, card_A₀]
    intro v
    obtain ⟨a, ha⟩ := hg' ⟨enc v, ⟨v, rfl⟩⟩
    exact ⟨a, a.2, hAH a a.2, congrArg Subtype.val ha⟩
  choose κf hκA hκH hκφ using hsurj
  have hκmul : ∀ v w, κf (v * w) = κf v * κf w := by
    intro v w
    apply hinj _ (hκA _) _ (mul_mem (hκA v) (hκA w)) (hκH _) (mul_mem (hκH v) (hκH w))
    rw [hκφ, map_mul enc, show (⟨κf v * κf w, mul_mem (hκH v) (hκH w)⟩ : ↥H) =
      ⟨κf v, hκH v⟩ * ⟨κf w, hκH w⟩ from rfl, map_mul φ, hκφ, hκφ]
  let κ : Multiplicative W →* X :=
    { toFun := κf
      map_one' := by
        have h := hκmul 1 1
        rw [one_mul] at h
        exact (mul_eq_left.mp h.symm)
      map_mul' := hκmul }
  have hκinj : Function.Injective κ := by
    intro v w h
    apply enc_injective
    have h' : (⟨κf v, hκH v⟩ : ↥H) = ⟨κf w, hκH w⟩ := Subtype.ext h
    rw [← hκφ v, ← hκφ w, h']
  have hκt : κ (Multiplicative.ofAdd tW) = t := by
    apply hinj _ (hκA _) _ htA (hκH _) htH
    rw [hκφ, enc_tW, hφt]
  have hrange : κ.range = A := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact hκA v
    · rw [hcardA, ← Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv,
        Nat.card_eq_fintype_card]
      rfl
  have hcard : Nat.card κ.range = 2 ^ (Nat.card P).factorization 2 := by
    rw [hrange, hcardA, hfac]
    norm_num
  exact ⟨{ κ := κ, inj := hκinj, mem := hκH, phi := hκφ, ht := hκt, card := hcard }⟩

end CFSG.ComponentClassification.SolMax.NineE32
