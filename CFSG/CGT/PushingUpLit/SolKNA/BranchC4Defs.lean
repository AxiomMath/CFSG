module

public import CFSG.CGT.PushingUpLit.SolKNA.PairFrameA
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic
import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.RankThree.GF2n (exists_mul_of_mem_sup mem_normalizer_inf)

set_option linter.unusedSectionVars false

variable {G : Type} [Group G]

namespace C4Aux

theorem comm_of_sq_eq_one {S : Subgroup G} (h : ∀ x ∈ S, x * x = 1) {a b : G} (ha : a ∈ S)
    (hb : b ∈ S) : a * b = b * a := by
  have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (h _ (S.mul_mem ha hb))
  rw [mul_inv_rev, e1, e2] at e3
  exact e3.symm

theorem le_normalizer_of_conj_mem {S P : Subgroup G}
    (h : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) : S ≤ Subgroup.normalizer (P : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => h s hs p hp, fun hp => ?_⟩
  have e : s⁻¹ * (s * p * s⁻¹) * s⁻¹⁻¹ = p := by group
  have := h s⁻¹ (S.inv_mem hs) _ hp
  rwa [e] at this

theorem sup_eq_of_index_two [Finite G] {H H' R : Subgroup G} (hHR : H ≤ R) (hH'R : H' ≤ R)
    (hcard : Nat.card ↥R = 2 * Nat.card ↥H) (hcard' : Nat.card ↥H' = Nat.card ↥H)
    (hne : H' ≠ H) : H ⊔ H' = R := by
  have hK : H ⊔ H' ≤ R := sup_le hHR hH'R
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le (le_sup_left : H ≤ H ⊔ H')
  have hdvd := Subgroup.card_dvd_of_le hK
  rw [ha, hcard, mul_comm 2] at hdvd
  have hpos : 0 < Nat.card ↥H := Nat.card_pos
  have ha2 : a ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp ha2 with h1 | h2
  · exfalso
    rw [h1, mul_one] at ha
    have hKH : H = H ⊔ H' := Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq ha)
    have hle : H' ≤ H := hKH ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard'.symm))
  · rw [h2, mul_comm, ← hcard] at ha
    exact Subgroup.eq_of_le_of_card_ge hK (le_of_eq ha.symm)

end C4Aux

open C4Aux

namespace AData

variable [Finite G] {R T W : Subgroup G} (A : AData R T W)
include A

theorem T_le_normalizer_N :
    T ≤ Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) :=
  fun _ ht => mem_normalizer_inf (A.T_norm ht)
    (Subgroup.le_normalizer (Subgroup.le_normalizer ht))

theorem exists_mul_NT {x : G}
    (hx : x ∈ (R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T) :
    ∃ n ∈ R ⊓ Subgroup.normalizer (T : Set G), ∃ t ∈ T, x = n * t :=
  exists_mul_of_mem_sup A.T_le_normalizer_N hx

theorem comm_mem_N {a b : G} (ha : a ∈ W) (hb : b ∈ W) :
    a * b * a⁻¹ * b⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have := A.Z_comm a ha b hb
  rwa [A.center_eq] at this

theorem sq_mem_N {a : G} (ha : a ∈ W) : a * a ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have := A.Z_sq a ha
  rwa [A.center_eq] at this

theorem W_le_normalizer_P :
    W ≤ Subgroup.normalizer
      (((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T : Subgroup G) : Set G) := by
  apply le_normalizer_of_conj_mem
  intro w hw p hp
  obtain ⟨n, hn, t, ht, rfl⟩ := A.exists_mul_NT hp
  have hcomm := A.comm_mem_N hw (A.T_le ht)
  have h1 : w * n * w⁻¹ = n := by
    have := A.N_central hn hw
    calc w * n * w⁻¹ = (n * w) * w⁻¹ := by rw [this]
      _ = n := by group
  have e : w * (n * t) * w⁻¹ = n * ((w * t * w⁻¹ * t⁻¹) * t) := by
    calc w * (n * t) * w⁻¹ = (w * n * w⁻¹) * (w * t * w⁻¹) := by group
      _ = n * ((w * t * w⁻¹ * t⁻¹) * t) := by rw [h1]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right ht))

theorem P_sq {p : G} (hp : p ∈ (R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T) : p * p = 1 := by
  obtain ⟨n, hn, t, ht, rfl⟩ := A.exists_mul_NT hp
  have hnt : n * t = t * n := A.N_comm hn ht
  calc n * t * (n * t) = n * (t * n) * t := by group
    _ = n * (n * t) * t := by rw [← hnt]
    _ = (n * n) * (t * t) := by group
    _ = 1 := by rw [A.elem_N hn, A.elem_T t ht, one_mul]

theorem card_P :
    Nat.card ↥((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T : Subgroup G) = Nat.card ↥T ^ 2 := by
  have hinf : (R ⊓ Subgroup.normalizer (T : Set G)) ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ T ⊓ R := ⟨hx.2, hx.1.1⟩
    rwa [A.inf_eq] at this
  rw [CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer
    A.T_le_normalizer_N hinf, A.card_N_eq, sq]

theorem not_R_le_normalizer_P :
    ¬ R ≤ Subgroup.normalizer
      (((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T : Subgroup G) : Set G) := by
  intro hR
  obtain ⟨x, hx, hxH⟩ := A.exists_not_mem_H
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    obtain ⟨⟨t, ht⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp A.T_ne
    exact ⟨t, ht, fun h => h1 (Subtype.ext h)⟩
  have hxt : x * t * x⁻¹ ∈ (R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T :=
    (Subgroup.mem_normalizer_iff.mp (hR hx) t).mp (Subgroup.mem_sup_right ht)
  obtain ⟨n, hn, t', ht', hnt⟩ := A.exists_mul_NT hxt
  have hnt' : n * t = t * n := A.N_comm hn ht
  have hcomm : t * x * t⁻¹ * x⁻¹ = n * (t * t') := by
    have h1 : t * x * t⁻¹ * x⁻¹ = t * (x * t * x⁻¹) := by rw [A.inv_eq_self ht]; group
    rw [h1, hnt]
    calc t * (n * t') = (t * n) * t' := by group
      _ = (n * t) * t' := by rw [hnt']
      _ = n * (t * t') := by group
  have htt' : t * t' ∈ T ⊓ R := by
    refine ⟨T.mul_mem ht ht', ?_⟩
    have h2 := (A.comm_mem_H hx ht).2
    rw [hcomm] at h2
    have := R.mul_mem (R.inv_mem hn.1) h2
    simpa using this
  rw [A.inf_eq, Subgroup.mem_bot] at htt'
  rw [htt', mul_one] at hcomm
  refine A.comm_not_mem hx hxH ht ht1 ?_
  rw [hcomm]
  exact hn

theorem cent_R_le {ζ t r : G} (hζ : ζ ∈ R ⊓ Subgroup.normalizer (T : Set G)) (ht : t ∈ T)
    (ht1 : t ≠ 1) (hr : r ∈ R) (hcomm : r * (ζ * t) = (ζ * t) * r) :
    r ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have hζ' : r * ζ * r⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := A.N_conj hr hζ
  have e1 : r * t * r⁻¹ = (r * ζ * r⁻¹)⁻¹ * (ζ * t) := by
    calc r * t * r⁻¹ = (r * ζ * r⁻¹)⁻¹ * (r * (ζ * t) * r⁻¹) := by group
      _ = (r * ζ * r⁻¹)⁻¹ * (ζ * t) := by rw [hcomm]; group
  have e2 : t * r * t⁻¹ * r⁻¹ = ζ⁻¹ * (r * ζ * r⁻¹) := by
    calc t * r * t⁻¹ * r⁻¹ = t * (r * t * r⁻¹)⁻¹ := by group
      _ = t * ((r * ζ * r⁻¹)⁻¹ * (ζ * t))⁻¹ := by rw [e1]
      _ = ζ⁻¹ * (r * ζ * r⁻¹) := by group
  have hrH : r ∈ W ⊓ R := by
    by_contra hrH
    refine A.comm_not_mem hr hrH ht ht1 ?_
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hζ) hζ'
  have hζr : r * ζ * r⁻¹ = ζ := by
    have := A.N_central hζ hrH.1
    calc r * ζ * r⁻¹ = (ζ * r) * r⁻¹ := by rw [this]
      _ = ζ := by group
  have hrt : r * t = t * r := by
    rw [hζr] at e1
    have : r * t * r⁻¹ = t := by rw [e1]; group
    calc r * t = (r * t * r⁻¹) * r := by group
      _ = t * r := by rw [this]
  exact A.mem_N_of_comm hr ht ht1 hrt

end AData

end CFSG.CGT.PushingUpLit.SolKNA
