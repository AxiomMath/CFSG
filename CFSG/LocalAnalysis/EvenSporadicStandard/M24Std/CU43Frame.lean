module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Tables
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Count

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Sporadic.SmallOddCore

theorem comm_of_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h2]

theorem arith_frame (m : ℕ) (h8 : m ∣ 8) (h : m * 720 ∣ 4320) : m ≤ 2 := by
  have : m ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  interval_cases m <;> omega

theorem card_inf_centralizer_conj_normal {X : Type*} [Group X] (E : Subgroup X) [E.Normal]
    (x t : X) :
    Nat.card ↥(E ⊓ centralizer ({x * t * x⁻¹} : Set X)) =
      Nat.card ↥(E ⊓ centralizer ({t} : Set X)) := by
  have h : E ⊓ centralizer ({x * t * x⁻¹} : Set X) =
      (E ⊓ centralizer ({t} : Set X)).map (MulAut.conj x).toMonoidHom := by
    ext y
    simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨hy, hyt⟩
      refine ⟨x⁻¹ * y * x, ⟨?_, ?_⟩, by group⟩
      · simpa using Normal.conj_mem inferInstance y hy x⁻¹
      · calc x⁻¹ * y * x * t = x⁻¹ * (y * (x * t * x⁻¹)) * x := by group
          _ = x⁻¹ * ((x * t * x⁻¹) * y) * x := by rw [hyt]
          _ = t * (x⁻¹ * y * x) := by group
    · rintro ⟨w, ⟨hw, hwt⟩, rfl⟩
      refine ⟨Normal.conj_mem inferInstance w hw x, ?_⟩
      calc x * w * x⁻¹ * (x * t * x⁻¹) = x * (w * t) * x⁻¹ := by group
        _ = x * (t * w) * x⁻¹ := by rw [hwt]
        _ = x * t * x⁻¹ * (x * w * x⁻¹) := by group
  rw [h]
  exact Subgroup.card_map_of_injective (MulAut.conj x).injective

section Frame

variable {X : Type*} [Group X] (E : Subgroup X) (θ : E ≃* P)

include θ in
theorem card_E : Nat.card E = 3265920 := by
  rw [Nat.card_congr θ.toEquiv, card_P]

include θ in
theorem frame_not_mem [Finite X] [E.Normal]
    (hC : centralizer (E : Set X) = ⊥) {ζ : X} (hζ : ζ * ζ = 1)
    (hdvd : Nat.card (centralizer ({ζ} : Set X)) ∣ 4320) : ζ ∉ E := by
  intro hζE
  have hE := card_E E θ
  by_cases hζ1 : ζ = 1
  · subst hζ1
    have hX : Nat.card (centralizer ({1} : Set X)) = Nat.card X := by
      have : centralizer ({1} : Set X) = ⊤ :=
        eq_top_iff.2 fun x _ => mem_centralizer_singleton_iff.2 (by simp)
      rw [this, Subgroup.card_top]
    rw [hX] at hdvd
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
    omega
  · have h1152 := card_inf_centralizer_inner E θ hC hζE hζ hζ1
    have h2 : Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) ∣ Nat.card (centralizer ({ζ} : Set X)) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [h1152] at h2
    have := h2.trans hdvd
    omega

include θ in
theorem frame_card [Finite X] [E.Normal]
    (hC : centralizer (E : Set X) = ⊥) {ζ : X} (hζ : ζ * ζ = 1)
    (hdvd : Nat.card (centralizer ({ζ} : Set X)) ∣ 4320) :
    Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) = 720 := by
  have hζE := frame_not_mem E θ hC hζ hdvd
  have h2 : Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) ∣ Nat.card (centralizer ({ζ} : Set X)) :=
    Subgroup.card_dvd_of_le inf_le_right
  have h3 := h2.trans hdvd
  rcases card_inf_centralizer_outer E θ hC hζE hζ with h | h | h | h <;> rw [h] at h3 <;> omega

include θ in
theorem frame_index [Finite X] [E.Normal]
    (hC : centralizer (E : Set X) = ⊥) {ζ : X} (hζ : ζ * ζ = 1)
    (hdvd : Nat.card (centralizer ({ζ} : Set X)) ∣ 4320) : E.index = 2 := by
  have hζE := frame_not_mem E θ hC hζ hdvd
  have h720 := frame_card E θ hC hζ hdvd
  have hnorm : ∀ p ∈ E, ζ * p * ζ⁻¹ ∈ E := fun p hp => Normal.conj_mem inferInstance p hp ζ
  have hu : ζ ^ 2 = 1 := by rw [sq]; exact hζ
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have hTcard : Nat.card ↥(E ⊔ zpowers ζ) = 2 * Nat.card E := card_sup_zpowers hu hnorm hζE
  have hTtop : E ⊔ zpowers ζ = ⊤ := by
    by_contra hne
    set T : Subgroup X := E ⊔ zpowers ζ with hT
    have hET : E ≤ T := le_sup_left
    have hQ8 := card_quotient_dvd_eight E θ hC
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card (X ⧸ E) ∣ 2 ^ 3 by simpa using hQ8)
    have hQp : IsPGroup 2 (X ⧸ E) := IsPGroup.of_card hk
    have : Group.IsNilpotent (X ⧸ E) := hQp.isNilpotent
    have hnc : NormalizerCondition (X ⧸ E) := Group.normalizerCondition_of_isNilpotent
    have hcomap : (T.map (QuotientGroup.mk' E)).comap (QuotientGroup.mk' E) = T := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hET]
    have hT'lt : T.map (QuotientGroup.mk' E) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hne
      rw [← hcomap, h, Subgroup.comap_top]
    obtain ⟨q, hqN, hqT⟩ := IsConcreteLE.exists_of_lt (hnc _ hT'lt)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxT : x ∉ T := fun h => hqT (mem_map_of_mem (QuotientGroup.mk' E) h)
    have hζ'T : x * ζ * x⁻¹ ∈ T := by
      have h1 := (mem_normalizer_iff.1 hqN (QuotientGroup.mk' E ζ)).1
        (mem_map_of_mem (QuotientGroup.mk' E) (mem_sup_right (mem_zpowers ζ)))
      have h2 : x * ζ * x⁻¹ ∈ (T.map (QuotientGroup.mk' E)).comap (QuotientGroup.mk' E) := by
        rw [Subgroup.mem_comap]
        simpa [map_mul, map_inv] using h1
      rwa [hcomap] at h2
    set ζ' := x * ζ * x⁻¹ with hζ'def
    have hζ'2 : ζ' * ζ' = 1 := by
      have : ζ' * ζ' = x * (ζ * ζ) * x⁻¹ := by simp only [hζ'def]; group
      rw [this, hζ]; group
    have hζ'E : ζ' ∉ E := by
      intro h
      apply hζE
      have := Normal.conj_mem inferInstance ζ' h x⁻¹
      have e : x⁻¹ * ζ' * x⁻¹⁻¹ = ζ := by simp only [hζ'def]; group
      rwa [e] at this
    have hcos : ζ' * ζ⁻¹ ∈ E := by
      rcases (mem_sup_zpowers_iff hu hnorm).1 hζ'T with h | h
      · exact absurd h hζ'E
      · rwa [hζinv]
    have h720' : Nat.card ↥(E ⊓ centralizer ({ζ'} : Set X)) = 720 := by
      rw [hζ'def, card_inf_centralizer_conj_normal E x ζ, h720]
    obtain ⟨c, hcE, hcζ⟩ := same_coset_conj' E θ hC hζE hζ hζ'2 hcos h720 h720'
    have hycent : c⁻¹ * x ∈ centralizer ({ζ} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : x * ζ = c * ζ * c⁻¹ * x := by
        calc x * ζ = (x * ζ * x⁻¹) * x := by group
          _ = c * ζ * c⁻¹ * x := by rw [← hζ'def, hcζ]
      calc c⁻¹ * x * ζ = c⁻¹ * (x * ζ) := by group
        _ = c⁻¹ * (c * ζ * c⁻¹ * x) := by rw [h1]
        _ = ζ * (c⁻¹ * x) := by group
    have hynot : c⁻¹ * x ∉ T := by
      intro h
      apply hxT
      have : x = c * (c⁻¹ * x) := by group
      rw [this]
      exact mul_mem (hET hcE) h
    set Cz := centralizer ({ζ} : Set X) with hCz
    have hup : Nat.card Cz ≤ 1440 := by
      have hmap := CResH4.natCard_map_mul_natCard_inf_ker (QuotientGroup.mk' E) Cz
      rw [QuotientGroup.ker_mk', inf_comm, h720] at hmap
      have hm8 : Nat.card (Cz.map (QuotientGroup.mk' E)) ∣ 8 :=
        (Subgroup.card_subgroup_dvd_card _).trans hQ8
      have hdvd' : Nat.card Cz ∣ 4320 := hdvd
      rw [← hmap] at hdvd' ⊢
      have := arith_frame _ hm8 hdvd'
      omega
    have hlow : 2880 ≤ Nat.card Cz := by
      have hEU : E ⊓ Cz ≤ Cz ⊓ T := le_inf inf_le_right (inf_le_left.trans hET)
      have hζU : ζ ∈ Cz ⊓ T :=
        mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, mem_sup_right (mem_zpowers ζ)⟩
      have h1 : 720 ∣ Nat.card ↥(Cz ⊓ T) := by
        rw [← h720]
        exact Subgroup.card_dvd_of_le hEU
      have h2 : Nat.card ↥(Cz ⊓ T) ≠ 720 := by
        intro h
        have := Subgroup.eq_of_le_of_card_ge hEU (by rw [h, h720])
        have hmem : ζ ∈ E ⊓ Cz := by rw [this]; exact hζU
        exact hζE (mem_inf.1 hmem).1
      have h3 : Nat.card ↥(Cz ⊓ T) ∣ Nat.card Cz := Subgroup.card_dvd_of_le inf_le_left
      have h4 : Nat.card ↥(Cz ⊓ T) ≠ Nat.card Cz := by
        intro h
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Cz ⊓ T ≤ Cz) h.ge
        apply hynot
        have hmem : c⁻¹ * x ∈ Cz ⊓ T := by rw [this]; exact hycent
        exact (mem_inf.1 hmem).2
      obtain ⟨j, hj⟩ := h3
      obtain ⟨i, hi⟩ := h1
      have hCzpos : 0 < Nat.card Cz := Nat.card_pos
      have hUpos : 0 < Nat.card ↥(Cz ⊓ T) := Nat.card_pos
      have hj2 : 2 ≤ j := by
        rcases j with _ | _ | j
        · omega
        · exact absurd (by simpa using hj.symm) h4
        · omega
      have hU : 1440 ≤ Nat.card ↥(Cz ⊓ T) := by omega
      calc 2880 = 2 * 1440 := by norm_num
        _ ≤ j * Nat.card ↥(Cz ⊓ T) := Nat.mul_le_mul hj2 hU
        _ = Nat.card Cz := by rw [hj, mul_comm]
    omega
  have hX : Nat.card X = 2 * Nat.card E := by rw [← hTcard, hTtop, Subgroup.card_top]
  have h := E.card_mul_index
  rw [hX] at h
  exact Nat.eq_of_mul_eq_mul_left hE0 (by rw [h, mul_comm])

include θ in
theorem card_le_sixteen_of_le [E.Normal]
    (hC : centralizer (E : Set X) = ⊥) {B : Subgroup X}
    (hBE : B ≤ E) (h2 : ∀ a ∈ B, a * a = 1) : Nat.card B ≤ 16 := by
  have hB'P : B.map (emb E θ) ≤ P := by
    rintro _ ⟨b, hb, rfl⟩
    have := emb_coe E θ ⟨b, hBE hb⟩
    exact this ▸ (θ ⟨b, hBE hb⟩).2
  have hcard : Nat.card (B.map (emb E θ)) = Nat.card B :=
    Subgroup.card_map_of_injective (emb_injective E θ hC)
  have h2' : ∀ a ∈ B.map (emb E θ), a * a = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, h2 b hb, map_one]
  have hab' : ∀ a ∈ B.map (emb E θ), ∀ b ∈ B.map (emb E θ), a * b = b * a := fun a ha b hb =>
    comm_of_sq_eq_one (h2' a ha) (h2' b hb) (h2' (a * b) (mul_mem ha hb))
  rw [← hcard]
  exact card_elemAb_le_sixteen _ hB'P hab' h2'

include θ in
theorem not_le_centralizer_of_outer [Finite X] [E.Normal]
    (hC : centralizer (E : Set X) = ⊥) (hidx : E.index = 2) {d : X}
    (hd : d ∉ E) (hd2 : d * d = 1) {S : Subgroup X} (hSodd : ¬ 2 ∣ S.index) :
    ¬ S ≤ centralizer ({d} : Set X) := by
  intro hSle
  have hE := card_E E θ
  have hX : Nat.card X = 2 * 3265920 := by
    have := E.card_mul_index
    rw [hidx, hE] at this
    omega
  have hSX := S.card_mul_index
  have hcop : Nat.Coprime 256 S.index := by
    have hodd : Odd S.index := by
      rcases Nat.even_or_odd S.index with h | h
      · exact absurd (even_iff_two_dvd.1 h) hSodd
      · exact h
    exact (Nat.coprime_two_left.2 hodd).pow_left 8
  have h256 : 256 ∣ Nat.card S := by
    apply hcop.dvd_of_dvd_mul_right
    rw [hSX, hX]
    norm_num
  have hdvdC : Nat.card S ∣ Nat.card (centralizer ({d} : Set X)) := Subgroup.card_dvd_of_le hSle
  have hrel : E.relIndex (centralizer ({d} : Set X)) ∣ 2 :=
    hidx ▸ Subgroup.relIndex_dvd_index_of_normal E (centralizer ({d} : Set X))
  have hCcard := Subgroup.relIndex_mul_card (H := E) (K := centralizer ({d} : Set X))
  have h256C : 256 ∣ Nat.card (centralizer ({d} : Set X)) := h256.trans hdvdC
  rw [← hCcard] at h256C
  rcases (Nat.dvd_prime Nat.prime_two).1 hrel with hr | hr <;>
    rcases card_inf_centralizer_outer E θ hC hd hd2 with hc | hc | hc | hc <;>
    rw [hr, hc] at h256C <;> omega

end Frame

end CFSG.EvenSporadicStandard.M24Std.CU43
