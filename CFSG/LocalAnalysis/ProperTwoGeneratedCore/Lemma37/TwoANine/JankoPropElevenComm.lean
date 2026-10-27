module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenOrbit

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar
open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem s₂_mem_P₂ : fr.s₂ ∈ fr.P₂ := fr.P₂_eq ▸ mem_zpowers _

theorem s₂_comm_t : fr.s₂ * fr.t = fr.t * fr.s₂ := by
  have h := fr.P₂_le_F₁ s₂_mem_P₂
  rw [fr.F₁_eq] at h
  exact mem_centralizer_singleton_iff.mp h.2

theorem s₂_pow_three : fr.s₂ ^ 3 = 1 := by
  rw [← fr.orderOf_s₂, pow_orderOf_eq_one]

theorem mem_centralizer_s₂_of_mem_ZN {x : G} (hx : x ∈ fr.ZN) :
    x ∈ centralizer ({fr.s₂} : Set G) :=
  mem_centralizer_singleton_iff.mpr (comm_of_mem_ZN hx (E_le_N s₂_mem_E)).symm

theorem s₂_mem_normalizer_At : fr.s₂ ∈ normalizer (fr.At : Set G) :=
  mem_normalizer_At (E_le_normalizer_M s₂_mem_E) s₂_comm_t

theorem At_inf_centralizer_s₂ [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.At ⊓ centralizer ({fr.s₂} : Set G) = fr.P3bar := by
  have hle : fr.P3bar ≤ fr.At ⊓ centralizer ({fr.s₂} : Set G) := fun x hx =>
    ⟨P3bar_le_At p10 hx, mem_centralizer_s₂_of_mem_ZN hx.1⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hdvd : Nat.card (fr.At ⊓ centralizer ({fr.s₂} : Set G) : Subgroup G) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← p10.card_At]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3 := Subgroup.card_le_of_le hle
  rw [card_P3bar p7 p10 hz] at h3 ⊢
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · rw [hk'] at h3; norm_num at h3
  · rw [hk']; norm_num
  · exfalso
    have heq : fr.At ⊓ centralizer ({fr.s₂} : Set G) = fr.At :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', p10.card_At]; norm_num)
    refine p10.not_At_le ?_
    rw [centralizer_P₂_eq, ← heq]
    exact inf_le_right

theorem mem_P3bar_iff [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {w : G} : w ∈ fr.P3bar ↔ ∃ a ∈ fr.At, ⁅a, fr.s₂⁆ = w := by
  have hcomm : ∀ a ∈ fr.At, ⁅a, fr.s₂⁆ ∈ fr.At := fun a ha => by
    have h : ⁅a, fr.s₂⁆ = a * (fr.s₂ * a⁻¹ * fr.s₂⁻¹) := by rw [commutatorElement_def]; group
    rw [h]
    exact mul_mem ha (conj_mem_of_mem_normalizer s₂_mem_normalizer_At (inv_mem ha))
  obtain ⟨W, hW, hcard⟩ := exists_commutator_subgroup (A := fr.At) (x := fr.s₂) fun a ha =>
    ⟨hcomm a ha, Subgroup.mem_centralizer_iff.mpr fun b hb => At_comm p10 b hb _ (hcomm a ha)⟩
  rw [At_inf_centralizer_s₂ p7 p10 hz, card_P3bar p7 p10 hz, p10.card_At] at hcard
  have hW3 : Nat.card W = 3 := by omega
  have hWAt : W ≤ fr.At := fun w hw => by
    obtain ⟨a, ha, rfl⟩ := (hW w).mp hw
    exact hcomm a ha
  have hWs : ∀ w ∈ W, fr.s₂ * w * fr.s₂⁻¹ ∈ W := fun w hw => by
    obtain ⟨a, ha, rfl⟩ := (hW w).mp hw
    refine (hW _).mpr ⟨fr.s₂ * a * fr.s₂⁻¹, conj_mem_of_mem_normalizer s₂_mem_normalizer_At ha,
      ?_⟩
    rw [conjugate_commutatorElement, mul_inv_cancel_right]
  have hWP : W ≤ fr.P3bar := by
    rw [← At_inf_centralizer_s₂ p7 p10 hz]
    exact fun w hw => ⟨hWAt hw, mem_centralizer_singleton_iff_conj.mpr
      (conj_eq_of_card_eq_three hW3 s₂_pow_three hWs hw)⟩
  have heq : W = fr.P3bar :=
    Subgroup.eq_of_le_of_card_ge hWP (by rw [hW3, card_P3bar p7 p10 hz])
  rw [← heq]
  exact hW w

theorem commutator_At_P₂_mem [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {a p : G} (ha : a ∈ fr.At) (hp : p ∈ fr.P₂) : ⁅a, p⁆ ∈ fr.P3bar := by
  rw [fr.P₂_eq, zpowers_eq_closure] at hp
  refine commutator_mem_of_mem_closure_right (fun x hx => ?_) (fun x hx => ?_) hp
  · rw [Set.mem_singleton_iff.mp hx]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp
      (mem_centralizer_s₂_of_mem_ZN hh.1)
  · rw [Set.mem_singleton_iff.mp hx]
    exact (mem_P3bar_iff p7 p10 hz).mpr ⟨a, ha, rfl⟩

theorem E_inf_centralizer_tz : fr.E ⊓ centralizer ({fr.t * z} : Set G) = fr.P₂ := by
  rw [← fr.E_inf_centralizer_t]
  ext e
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun he => ?_
  have hez : e * z = z * e := mem_centralizer_singleton_iff.mp (fr.E_le he)
  constructor
  · intro h
    calc e * fr.t = e * (fr.t * z) * z⁻¹ := by group
      _ = fr.t * (z * e) * z⁻¹ := by rw [h]; group
      _ = fr.t * e := by rw [← hez]; group
  · intro h
    calc e * (fr.t * z) = fr.t * e * z := by rw [← mul_assoc, h]
      _ = fr.t * z * e := by rw [mul_assoc, hez, ← mul_assoc]

theorem map_P₂ (hz : orderOf z = 2) : fr.P₂.map (MulAut.conj (fr.ℓ ^ 2)).toMonoidHom = fr.P₂ := by
  have h := map_conj_inf_centralizer (pow_mem (ℓ_mem_normalizer_E (fr := fr)) 2) fr.t
  rwa [ℓ_sq_conj_t hz, fr.E_inf_centralizer_t, E_inf_centralizer_tz] at h

theorem map_At (hz : orderOf z = 2) : fr.At.map (MulAut.conj (fr.ℓ ^ 2)).toMonoidHom = fr.Atz := by
  have h := map_conj_inf_centralizer (pow_mem (ℓ_mem_normalizer_M (fr := fr)) 2) fr.t
  rwa [ℓ_sq_conj_t hz] at h

theorem commutator_Atz_s₂_mem [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {b : G} (hb : b ∈ fr.Atz) : ⁅b, fr.s₂⁆ ∈ fr.P3bbar := by
  rw [← map_At hz] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hs : fr.s₂ ∈ fr.P₂.map (MulAut.conj (fr.ℓ ^ 2)).toMonoidHom := by
    rw [map_P₂ hz]; exact s₂_mem_P₂
  obtain ⟨p, hp, hps⟩ := hs
  rw [← hps, ← map_P3bar hz]
  refine ⟨⁅a, p⁆, commutator_At_P₂_mem p7 p10 hz ha hp, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conjugate_commutatorElement _ _ _

theorem ℓ_mem_normalizer_S [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.ℓ ∈ normalizer (fr.S : Set G) := by
  rw [S_eq p7 p10 hz]
  exact inf_mem_normalizer ℓ_mem_normalizer_ZN (ℓ_mem_normalizer_Mbar p7 p10 hz)

theorem mem_centralizer_S_of_mem_N {x : G} (hx : x ∈ fr.N) : x ∈ centralizer (fr.S : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hh => (comm_of_mem_ZN (S_le_ZN hh) hx).symm

theorem M_eq_closure (p10 : JankoProp10 fr) :
    fr.M = closure ((fr.P₁ : Set G) ∪ fr.At ∪ fr.Atz) := by
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
    Subgroup.closure_eq, p10.M_eq]

theorem commutator_M_s₂_mem [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {m : G} (hm : m ∈ fr.M) : ⁅m, fr.s₂⁆ ∈ fr.S := by
  rw [M_eq_closure p10] at hm
  refine commutator_mem_of_mem_closure (fun x hx => ?_) (fun x hx => ?_) hm
  · rcases hx with (hx | hx) | hx
    · exact mem_centralizer_S_of_mem_N (M_le_N (p10.P₁_le_M hx))
    · exact mem_centralizer_S_of_mem_N (M_le_N hx.1)
    · exact mem_centralizer_S_of_mem_N (M_le_N hx.1)
  · rcases hx with (hx | hx) | hx
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (fr.E_comm x (P₁_le_E hx) _ s₂_mem_E)]
      exact one_mem _
    · exact mem_sup_left ((mem_P3bar_iff p7 p10 hz).mpr ⟨x, hx, rfl⟩)
    · exact mem_sup_right (commutator_Atz_s₂_mem p7 p10 hz hx)

theorem commutator_mem_S [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {m e : G} (hm : m ∈ fr.M) (he : e ∈ fr.E) : ⁅m, e⁆ ∈ fr.S := by
  rw [fr.E_eq_closure] at he
  refine commutator_mem_of_mem_closure_right (fun x hx => ?_) (fun x hx => ?_) he
  · refine mem_centralizer_S_of_mem_N (E_le_N ?_)
    rcases hx with rfl | rfl | rfl
    · exact s₁_mem_E
    · exact s₂_mem_E
    · exact conj_s₂_mem_E
  · rcases hx with rfl | rfl | rfl
    · have hms : m * fr.s₁ = fr.s₁ * m := by
        have h := M_le_centralizer_P₁ hm
        rw [centralizer_P₁_eq] at h
        exact mem_centralizer_singleton_iff.mp h
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hms]
      exact one_mem _
    · exact commutator_M_s₂_mem p7 p10 hz hm
    · have hm' : fr.ℓ⁻¹ * m * fr.ℓ ∈ fr.M := inv_conj_mem_of_mem_normalizer ℓ_mem_normalizer_M hm
      have h := conj_mem_of_mem_normalizer (ℓ_mem_normalizer_S p7 p10 hz)
        (commutator_M_s₂_mem p7 p10 hz hm')
      rwa [conjugate_commutatorElement, show fr.ℓ * (fr.ℓ⁻¹ * m * fr.ℓ) * fr.ℓ⁻¹ = m by group]
        at h

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
