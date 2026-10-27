module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

section Helpers

private theorem l94q_isElemAbelian_map {H K : Type} [Group H] [Group K] {p : ℕ} (f : H →* K)
    {E : Subgroup H} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
      isElemAbelian_commute hE hx hy]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hE.2 x hx, map_one]

private theorem l94q_isElemAbelian_of_map {H K : Type} [Group H] [Group K] {p : ℕ} {f : H →* K}
    {E : Subgroup H} (hf : ∀ x ∈ E, ∀ y ∈ E, f x = f y → x = y)
    (hE : IsElemAbelian p (E.map f)) : IsElemAbelian p E := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    apply hf _ (E.mul_mem ha hb) _ (E.mul_mem hb ha)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val
      (hE.1.1.comm ⟨f a, Subgroup.mem_map_of_mem f ha⟩ ⟨f b, Subgroup.mem_map_of_mem f hb⟩)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  apply hf _ (E.pow_mem hx p) _ E.one_mem
  rw [map_pow, map_one]
  exact hE.2 _ (Subgroup.mem_map_of_mem f hx)

private theorem l94q_card_comap {H K : Type} [Group H] [Group K] [Finite H] [Finite K]
    (f : H →* K) (hf : Function.Surjective f) (L : Subgroup K) :
    Nat.card (L.comap f) = Nat.card L * Nat.card f.ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.comap f)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h4 : Nat.card (H ⧸ f.ker) = Nat.card K :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have h5 : Nat.card (H ⧸ L.comap f) = Nat.card (K ⧸ L) :=
    Subgroup.index_comap_of_surjective L hf
  have hpos : 0 < Nat.card (K ⧸ L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card (K ⧸ L) * Nat.card (L.comap f)
      = Nat.card (H ⧸ L.comap f) * Nat.card (L.comap f) := by rw [h5]
    _ = Nat.card H := h1.symm
    _ = Nat.card (H ⧸ f.ker) * Nat.card f.ker := h3
    _ = Nat.card K * Nat.card f.ker := by rw [h4]
    _ = Nat.card (K ⧸ L) * Nat.card L * Nat.card f.ker := by rw [h2]
    _ = Nat.card (K ⧸ L) * (Nat.card L * Nat.card f.ker) := Nat.mul_assoc _ _ _

private theorem l94q_card_le_of_normalizes_coprime_even {G : Type} [Group G] [Finite G]
    {Q Y : Subgroup G} (hQ : IsElemAbelian 3 Q) (hQY : Q ≤ Subgroup.normalizer (Y : Set G))
    (hY3 : ¬ 3 ∣ Nat.card Y) (hY2 : 2 ∣ Nat.card Y) : Nat.card Q ≤ 3 ^ GLATwoLocalRank 3 G := by
  obtain ⟨R, ⟨S, rfl⟩, -, hQR⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := 3) (r := 2)
      Nat.prime_three Nat.prime_two (isPGroup_of_isElemAbelian hQ) hQY hY3 bot_le
      IsPGroup.of_bot (fun g _ => Subgroup.mem_normalizer_iff.2 fun h => by
        simp only [SetLike.mem_coe, Subgroup.mem_bot]
        constructor <;> intro hh <;> simp_all)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : (S : Subgroup Y) ≠ ⊥ := S.ne_bot_of_dvd_card hY2
  refine card_le_pow_glaTwoLocalRank Nat.prime_three hQ ?_ (S.isPGroup'.map _) hQR
  intro h
  exact hS ((Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 h)

private theorem l94q_core {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q] (π : X →* Q)
    (hπs : Function.Surjective π) (hO : Nat.Coprime 3 (Nat.card π.ker)) {P W : Subgroup Q}
    (hP : IsElemAbelian 3 P) (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hPW : P ≤ Subgroup.normalizer (W : Set Q)) :
    ∃ K Y : Subgroup X, IsElemAbelian 3 K ∧ Nat.card K = Nat.card P ∧
      K ≤ Subgroup.normalizer (Y : Set X) ∧ ¬ 3 ∣ Nat.card Y ∧ 2 ∣ Nat.card Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hW2
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hW (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have h2W : 2 ∣ Nat.card W := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h3W : ¬ 3 ∣ Nat.card W := by
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have h3O : ¬ 3 ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hO
  have hYc : Nat.card (W.comap π) = Nat.card W * Nat.card π.ker := l94q_card_comap π hπs W
  have hQc : Nat.card (P.comap π) = Nat.card P * Nat.card π.ker := l94q_card_comap π hπs P
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hP
  have hdvd : 3 ^ a ∣ Nat.card (P.comap π) := by
    rw [hQc, ha]
    exact dvd_mul_right _ _
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  obtain ⟨K, hKle, hKc⟩ : ∃ K : Subgroup X, K ≤ P.comap π ∧ Nat.card K = 3 ^ a :=
    ⟨K₀.map (P.comap π).subtype, Subgroup.map_subtype_le K₀, by
      rw [Subgroup.card_map_of_injective (P.comap π).subtype_injective, hK₀]⟩
  have hKP : K.map π ≤ P := Subgroup.map_le_iff_le_comap.2 hKle
  have hbot : K ⊓ π.ker = ⊥ := by
    have h1 : Nat.card (K ⊓ π.ker : Subgroup X) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left a hO)
        (by rw [← hKc]; exact Subgroup.card_dvd_of_le inf_le_left)
        (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.card_eq_one.1 h1
  have hinj : ∀ x ∈ K, ∀ y ∈ K, π x = π y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ K ⊓ π.ker := by
      refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem hx) hy, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.1 hmem
  have hKel : IsElemAbelian 3 K :=
    l94q_isElemAbelian_of_map hinj (isElemAbelian_mono hP hKP)
  refine ⟨K, W.comap π, hKel, by rw [hKc, ha], ?_, ?_, ?_⟩
  ·
    intro k hk
    have hkP : π k ∈ P := Subgroup.mem_comap.1 (hKle hk)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hh := Subgroup.mem_normalizer_iff.1 (hPW hkP) (π h)
    simp only [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv] at hh ⊢
    exact hh
  · rw [hYc, Nat.Prime.dvd_mul Nat.prime_three]
    rintro (h | h)
    · exact h3W h
    · exact h3O h
  · rw [hYc]
    exact Dvd.dvd.mul_right h2W _

end Helpers

theorem l94_card_le_of_quot {G : Type} [Group G] [Finite G] {C : Subgroup G}
    {P W : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)} (hP : IsElemAbelian 3 P) (hW2 : IsPGroup 2 W)
    (hW : W ≠ ⊥) (hPW : P ≤ Subgroup.normalizer (W : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))) :
    Nat.card P ≤ 3 ^ GLATwoLocalRank 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  obtain ⟨K, Y, hKel, hKc, hKY, hY3, hY2⟩ :=
    l94q_core (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) (QuotientGroup.mk'_surjective _) hO hP hW
      hW2 hPW
  have hι : Function.Injective C.subtype := C.subtype_injective
  have hK' : IsElemAbelian 3 (K.map C.subtype) := l94q_isElemAbelian_map C.subtype hKel
  have hKY' : K.map C.subtype ≤ Subgroup.normalizer ((Y.map C.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hKY).trans (Subgroup.le_normalizer_map C.subtype)
  have hcardK : Nat.card (K.map C.subtype) = Nat.card P := by
    rw [Subgroup.card_map_of_injective hι, hKc]
  have hcardY : Nat.card (Y.map C.subtype) = Nat.card Y := Subgroup.card_map_of_injective hι
  have key := l94q_card_le_of_normalizes_coprime_even hK' hKY'
    (by rw [hcardY]; exact hY3) (by rw [hcardY]; exact hY2)
  rw [hcardK] at key
  exact key

end CFSG.LocalAnalysis.GLTheoremA
