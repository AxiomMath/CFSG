module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbOdd
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.Foundations.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped MatrixGroups

section Klein

theorem gmq_klein_of_sylow {Γ : Type*} [Group Γ] [Finite Γ] (Q₀ : Sylow 2 Γ)
    (h4 : Nat.card (Q₀ : Subgroup Γ) = 4) (h2 : ∀ x ∈ (Q₀ : Subgroup Γ), x * x = 1)
    {c : Γ} (hcN : c ∈ normalizer ((Q₀ : Subgroup Γ) : Set Γ))
    (hc : ∀ x ∈ (Q₀ : Subgroup Γ), c * x * c⁻¹ = x → x = 1) (Q : Sylow 2 Γ) :
    Nat.card (Q : Subgroup Γ) = 4 ∧ (∀ x ∈ (Q : Subgroup Γ), x * x = 1) ∧
      ∃ c' ∈ normalizer ((Q : Subgroup Γ) : Set Γ),
        ∀ x ∈ (Q : Subgroup Γ), c' * x * c'⁻¹ = x → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Γ Q₀ Q
  have hmem : ∀ y, y ∈ ((g • Q₀ : Sylow 2 Γ) : Subgroup Γ) ↔
      g⁻¹ * y * g ∈ (Q₀ : Subgroup Γ) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
  refine ⟨?_, ?_, g * c * g⁻¹, ?_, ?_⟩
  · rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity Q₀, h4]
  · intro y hy
    have := h2 _ ((hmem y).mp hy)
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [mem_normalizer_iff]
    intro y
    rw [hmem, hmem, mem_normalizer_iff.mp hcN,
      show g⁻¹ * (g * c * g⁻¹ * y * (g * c * g⁻¹)⁻¹) * g = c * (g⁻¹ * y * g) * c⁻¹ by group]
  · intro y hy hfix
    have h1 := hc _ ((hmem y).mp hy) (by
      calc c * (g⁻¹ * y * g) * c⁻¹ = g⁻¹ * (g * c * g⁻¹ * y * (g * c * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * y * g := by rw [hfix])
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

variable {F : Type*} [Field F]

theorem gmq_pc_fix {x y : F} (h : x ^ 2 + y ^ 2 = -1) (h2 : (2 : F) ≠ 0) {z : PSL(2, F)}
    (hz : z ∈ gmbQ₀ h)
    (hfix : gmbPi F (gmbQc h h2) * z * (gmbPi F (gmbQc h h2))⁻¹ = z) : z = 1 := by
  rcases mem_gmbKlein.mp hz with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    rw [gmb_pc_conj_pa] at hfix
    exact gmb_pa_ne_pb h h2 hfix.symm
  · exfalso
    rw [gmb_pc_conj_pb] at hfix
    apply gmb_pa_ne_one (F := F)
    calc gmbPi F (gmbQa F) = gmbPi F (gmbQa F) * gmbPi F (gmbQb h) * (gmbPi F (gmbQb h))⁻¹ := by
          group
      _ = 1 := by rw [hfix, mul_inv_cancel]
  · exfalso
    have e : gmbPi F (gmbQc h h2) * (gmbPi F (gmbQa F) * gmbPi F (gmbQb h)) *
        (gmbPi F (gmbQc h h2))⁻¹ = gmbPi F (gmbQa F) := by
      rw [show gmbPi F (gmbQc h h2) * (gmbPi F (gmbQa F) * gmbPi F (gmbQb h)) *
            (gmbPi F (gmbQc h h2))⁻¹ =
          (gmbPi F (gmbQc h h2) * gmbPi F (gmbQa F) * (gmbPi F (gmbQc h h2))⁻¹) *
            (gmbPi F (gmbQc h h2) * gmbPi F (gmbQb h) * (gmbPi F (gmbQc h h2))⁻¹) by group,
        gmb_pc_conj_pa, gmb_pc_conj_pb, ← mul_assoc, ← gmb_pa_pb_comm h, mul_assoc,
        gmb_pb_mul_self h, mul_one]
    rw [e] at hfix
    apply gmb_pb_ne_one h h2
    calc gmbPi F (gmbQb h) = (gmbPi F (gmbQa F))⁻¹ * (gmbPi F (gmbQa F) * gmbPi F (gmbQb h)) := by
          group
      _ = 1 := by rw [← hfix, inv_mul_cancel]

theorem gmq_klein_psl2 [Finite F] (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (Q : Sylow 2 PSL(2, F)) :
    Nat.card (Q : Subgroup PSL(2, F)) = 4 ∧ (∀ z ∈ (Q : Subgroup PSL(2, F)), z * z = 1) ∧
      ∃ c ∈ normalizer ((Q : Subgroup PSL(2, F)) : Set PSL(2, F)),
        ∀ z ∈ (Q : Subgroup PSL(2, F)), c * z * c⁻¹ = z → z = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have := FiniteField.even_card_iff_char_two.mp hc
    rw [← hcard] at this
    omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have : NeZero (ringChar F) := ⟨hp.ne_zero⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have h : (a : F) ^ 2 + (b : F) ^ 2 = -1 := by
    rw [hab]
    simp
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨ringChar F, n, hp, hp.odd_of_ne_two hchar, n.pos, by rw [hcard, hn]⟩
  have hPSL := CFSG.GorensteinWalter.psl2_card_formula F hodd
  have hQp : IsPGroup 2 (gmbQ₀ h) :=
    IsPGroup.of_card (n := 2) (by rw [gmbQ₀_card h h2]; norm_num)
  have hQi : ¬ 2 ∣ (gmbQ₀ h).index := by
    apply gmb_not_two_dvd_of_mod_eight h8
    rw [← hPSL, ← gmbQ₀_card h h2]
    exact (gmbQ₀ h).card_mul_index
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine gmq_klein_of_sylow (hQp.toSylow hQi) ?_ ?_ (c := gmbPi F (gmbQc h h2)) ?_ ?_ Q
  · rw [IsPGroup.toSylow_coe]
    exact gmbQ₀_card h h2
  · rw [IsPGroup.toSylow_coe]
    exact fun z hz => gmbQ₀_mul_self h hz
  · rw [IsPGroup.toSylow_coe]
    exact gmb_pc_mem_normalizer h h2
  · rw [IsPGroup.toSylow_coe]
    exact fun z hz hfix => gmq_pc_fix h h2 hz hfix

end Klein

section Abstract

variable {G Γ : Type*} [Group G] [Finite G] [Group Γ] [Finite Γ]

theorem gmq_eq_one_of_comm [Group.IsPerfect G] (S : Sylow 2 G)
    (hS : ∀ a b : (S : Subgroup G), a * b = b * a) {z : G} (hz : z ∈ center G)
    (hz2 : ∃ n : ℕ, z ^ 2 ^ n = 1) : z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hz2
  have hpow := CFSG.RankThree.PartTwo.KFacts.KS14.pow_index_eq_one_of_isPerfect
    (S : Subgroup G) hS hz
  have hcop : Nat.Coprime (2 ^ n) (S : Subgroup G).index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn)
    (orderOf_dvd_of_pow_eq_one hpow))

theorem gmq_exists_of_klein [Group.IsPerfect G] (φ : G →* Γ) (hφ : Function.Surjective φ)
    (hker : φ.ker = center G) (hZ : IsPGroup 2 (center G)) (hZ1 : center G ≠ ⊥)
    (hΓ : ∀ Q : Sylow 2 Γ, Nat.card (Q : Subgroup Γ) = 4 ∧ (∀ x ∈ (Q : Subgroup Γ), x * x = 1) ∧
      ∃ c ∈ normalizer ((Q : Subgroup Γ) : Set Γ),
        ∀ x ∈ (Q : Subgroup Γ), c * x * c⁻¹ = x → x = 1)
    (S : Sylow 2 G) :
    ∃ u : G, (∀ x ∈ (S : Subgroup G), u * x * u⁻¹ ∈ (S : Subgroup G)) ∧
      ∀ k ∈ (S : Subgroup G), k ∉ center G → k * (u * k * u⁻¹) ≠ u * k * u⁻¹ * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS : center G ≤ (S : Subgroup G) := hZ.le_sylow_of_normal S
  have hpre : ∀ x, φ x ∈ (S : Subgroup G).map φ → x ∈ (S : Subgroup G) := by
    intro x hx
    have hx' : x ∈ ((S : Subgroup G).map φ).comap φ := hx
    rwa [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hZS] at hx'
  have hmemQ : ∀ x ∈ (S : Subgroup G), φ x ∈ (S : Subgroup G).map φ := fun x hx => ⟨x, hx, rfl⟩
  obtain ⟨h4, h2, c, hcN, hcfix⟩ := hΓ (S.mapSurjective hφ)
  rw [Sylow.coe_mapSurjective] at h4 h2 hcN hcfix
  obtain ⟨u, rfl⟩ := hφ c
  have hnorm : ∀ x ∈ (S : Subgroup G), u * x * u⁻¹ ∈ (S : Subgroup G) := by
    intro x hx
    apply hpre
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hcN _).mp (hmemQ x hx)
  refine ⟨u, hnorm, ?_⟩
  intro k hk hkZ hcomm
  set m := u * k * u⁻¹ with hm
  have hmS : m ∈ (S : Subgroup G) := hnorm k hk
  have hφm : φ m = φ u * φ k * (φ u)⁻¹ := by rw [hm, map_mul, map_mul, map_inv]
  have hk1 : φ k ≠ 1 := fun h => hkZ (hker ▸ (MonoidHom.mem_ker.mpr h))
  have hm1 : φ m ≠ 1 := by
    rw [hφm]
    intro h
    apply hk1
    calc φ k = (φ u)⁻¹ * (φ u * φ k * (φ u)⁻¹) * φ u := by group
      _ = 1 := by rw [h]; group
  have hkm : φ k ≠ φ m := fun h => hk1 (hcfix _ (hmemQ k hk) (by rw [← hφm]; exact h.symm))
  have hdec : ∀ t ∈ (S : Subgroup G), ∃ w : G, (w = 1 ∨ w = k ∨ w = m ∨ w = k * m) ∧
      w⁻¹ * t ∈ center G := by
    intro t ht
    have hz : ∀ w : G, φ t = φ w → w⁻¹ * t ∈ center G := fun w hw => by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hw, inv_mul_cancel]
    rcases gmb_mem_four h4 h2 (hmemQ k hk) (hmemQ m hmS) hk1 hm1 hkm (hmemQ t ht) with
      h | h | h | h
    · exact ⟨1, Or.inl rfl, hz 1 (by rw [h, map_one])⟩
    · exact ⟨k, Or.inr (Or.inl rfl), hz k h⟩
    · exact ⟨m, Or.inr (Or.inr (Or.inl rfl)), hz m h⟩
    · exact ⟨k * m, Or.inr (Or.inr (Or.inr rfl)), hz (k * m) (h.trans (map_mul φ k m).symm)⟩
  have hcomm' : Commute k m := hcomm
  have hW : ∀ w : G, (w = 1 ∨ w = k ∨ w = m ∨ w = k * m) → Commute w k ∧ Commute w m := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact ⟨Commute.one_left _, Commute.one_left _⟩
    · exact ⟨Commute.refl _, hcomm'⟩
    · exact ⟨hcomm'.symm, Commute.refl _⟩
    · exact ⟨(Commute.refl k).mul_left hcomm'.symm, hcomm'.mul_left (Commute.refl m)⟩
  have hWW : ∀ w w' : G, (w = 1 ∨ w = k ∨ w = m ∨ w = k * m) →
      (w' = 1 ∨ w' = k ∨ w' = m ∨ w' = k * m) → Commute w w' := by
    intro w w' hw hw'
    obtain ⟨hwk, hwm⟩ := hW w hw
    rcases hw' with rfl | rfl | rfl | rfl
    · exact Commute.one_right _
    · exact hwk
    · exact hwm
    · exact hwk.mul_right hwm
  have hcen : ∀ z ∈ center G, ∀ g : G, Commute g z := fun z hz g =>
    Subgroup.mem_center_iff.mp hz g
  have hSc : ∀ a b : (S : Subgroup G), a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    show a * b = b * a
    obtain ⟨w, hw, hwa⟩ := hdec a ha
    obtain ⟨w', hw', hwb⟩ := hdec b hb
    have ea : a = w * (w⁻¹ * a) := by group
    have eb : b = w' * (w'⁻¹ * b) := by group
    have hc : Commute (w * (w⁻¹ * a)) (w' * (w'⁻¹ * b)) :=
      Commute.mul_left (Commute.mul_right (hWW w w' hw hw') (hcen _ hwb w))
        (hcen _ hwa _).symm
    rw [← ea, ← eb] at hc
    exact hc
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ center G, z ≠ 1 := by
    rcases (center G).bot_or_exists_ne_one with h0 | h
    · exact absurd h0 hZ1
    · exact h
  obtain ⟨n, hn⟩ := hZ ⟨z, hzZ⟩
  exact hz1 (gmq_eq_one_of_comm S hSc hzZ ⟨n, by simpa using congrArg Subtype.val hn⟩)

end Abstract

theorem gmq_sl2_cover {Y : Type*} [Group Y] [Finite Y] (K : Subgroup Y)
    (hK : CFSG.IsQuasisimple K) (hZp : IsPGroup 2 (center K)) (hZ : center K ≠ ⊥) (p n : ℕ)
    [Fact p.Prime] (hn : 0 < n) (h8 : p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)
    (e : (K ⧸ center K) ≃* PSL(2, GaloisField p n)) (T : Subgroup Y) (hT : IsSylowOf 2 T K) :
    ∃ u ∈ K, (∀ x ∈ T, u * x * u⁻¹ ∈ T) ∧
      ∀ k ∈ T, (∃ y ∈ K, k * y ≠ y * k) → k * (u * k * u⁻¹) ≠ u * k * u⁻¹ * k := by
  have : Group.IsPerfect K := hK.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8' : Nat.card (GaloisField p n) % 8 = 3 ∨ Nat.card (GaloisField p n) % 8 = 5 := by
    rw [GaloisField.card p n hn.ne']
    exact h8
  let φ : K →* PSL(2, GaloisField p n) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = center K := by
    show (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).ker = center K
    rw [← MonoidHom.comap_ker, (MonoidHom.ker_eq_bot_iff _).mpr e.injective,
      MonoidHom.comap_bot, QuotientGroup.ker_mk']
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨u, hu, hu'⟩ := gmq_exists_of_klein φ hφ hker hZp hZ (gmq_klein_psl2 h8') S
  refine ⟨u, u.2, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨u * s * u⁻¹, hu s hs, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩ ⟨y, hy, hsy⟩ h
    have hsZ : s ∉ center K := fun hsZ => hsy
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hsZ ⟨y, hy⟩)).symm
    exact hu' s hs hsZ (Subtype.ext h)

end CFSG.SeitzReduction.RankOne
