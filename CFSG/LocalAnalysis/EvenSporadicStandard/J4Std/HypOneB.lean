module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTwoB
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.ComponentClassification.M12Cover

theorem noNormalFour_of_commutator {J : Type*} [Group J] [Finite J] (y : J) (E : Subgroup J)
    (hEc : ∀ x ∈ E, ∀ w ∈ E, x * w = w * x) (hEcard : Nat.card E = 2 ^ 11)
    (hEsq : ∀ e ∈ E, e * e = 1) (hEy : E ≤ centralizer ({y} : Set J))
    (hCn : ∀ c ∈ centralizer ({y} : Set J), ∀ e ∈ E, c * e * c⁻¹ ∈ E)
    (h128 : ∀ t ∈ centralizer ({y} : Set J), t ∉ E → t * t ∈ E →
      Nat.card ↥(E ⊓ centralizer ({t} : Set J)) ≤ 128) :
    NoNormalFour (centralizer ({y} : Set J)) := by
  have key : ∀ N : Subgroup (centralizer ({y} : Set J)), N.Normal →
      (∀ x ∈ N, ∀ w ∈ N, x * w = w * x) → Nat.card N ≤ 8 → (∀ n ∈ N, n ^ 4 = 1) →
      (∃ n ∈ N, n * n ≠ 1) → False := by
    intro N hN hab hcard h4 ⟨n0, hn0N, hn0⟩
    let M : Subgroup J := N.map (centralizer ({y} : Set J)).subtype
    have hMC : ∀ m ∈ M, m ∈ centralizer ({y} : Set J) := by
      rintro _ ⟨n, -, rfl⟩
      exact n.2
    have hMn : ∀ c ∈ centralizer ({y} : Set J), ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
      rintro c hc _ ⟨n, hn, rfl⟩
      exact ⟨⟨c, hc⟩ * n * ⟨c, hc⟩⁻¹, hN.conj_mem n hn ⟨c, hc⟩, rfl⟩
    have hMcard : Nat.card M ≤ 8 := by
      rw [Subgroup.card_map_of_injective (centralizer ({y} : Set J)).subtype_injective]
      exact hcard
    have hM4 : ∀ m ∈ M, m ^ 4 = 1 := by
      rintro _ ⟨n, hn, rfl⟩
      have := congrArg Subtype.val (h4 n hn)
      simpa using this
    have hME : ∀ m ∈ M, m ∈ E := by
      intro x hx
      by_contra hxE
      obtain ⟨t, htM, htE, htsq⟩ : ∃ t ∈ M, t ∉ E ∧ t * t ∈ E := by
        by_cases hx2 : x * x ∈ E
        · exact ⟨x, hx, hxE, hx2⟩
        · refine ⟨x * x, mul_mem hx hx, hx2, ?_⟩
          have : x * x * (x * x) = 1 := by
            have := hM4 x hx
            calc x * x * (x * x) = x ^ 4 := by
                  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
              _ = 1 := this
          rw [this]
          exact one_mem E
      have htC := hMC t htM
      have hle := ComponentClassification.RankTwoSporadic.J4Fink.card_le_card_inf_centralizer_mul
        (N := M ⊓ E) hEc (fun e he => hCn t htC e he)
        (fun e he => by
          refine mem_inf.mpr ⟨mul_mem (hMn e (hEy he) t htM) (inv_mem htM), ?_⟩
          have h1 := hCn t htC e⁻¹ (inv_mem he)
          have e1 : e * t * e⁻¹ * t⁻¹ = e * (t * e⁻¹ * t⁻¹) := by group
          rw [e1]
          exact mul_mem he h1)
      rw [hEcard] at hle
      have h128' := h128 t htC htE htsq
      have h8 : Nat.card ↥(M ⊓ E) ≤ 8 := (Subgroup.card_le_of_le inf_le_left).trans hMcard
      have h2 : 2 ^ 11 ≤ 128 * 8 := hle.trans (Nat.mul_le_mul h128' h8)
      norm_num at h2
    apply hn0
    have h1 : (n0 : J) * n0 = 1 := hEsq _ (hME _ ⟨n0, hn0N, rfl⟩)
    exact Subtype.ext (by simpa using h1)
  have key' : ∀ (N : Subgroup (centralizer ({y} : Set J))) (A : Type) [Group A],
      N.Normal → N ≃* A → (∀ a b : A, a * b = b * a) → Nat.card A ≤ 8 → (∀ a : A, a ^ 4 = 1) →
      (∃ a : A, a * a ≠ 1) → False := by
    intro N A _ hN e hab hcard h4 ⟨a0, ha0⟩
    refine key N hN ?_ ?_ ?_ ?_
    · intro x hx w hw
      have h : (⟨x, hx⟩ : N) * ⟨w, hw⟩ = ⟨w, hw⟩ * ⟨x, hx⟩ :=
        e.injective (by rw [map_mul, map_mul, hab])
      exact congrArg Subtype.val h
    · rw [Nat.card_congr e.toEquiv]; exact hcard
    · intro n hn
      have h : ((⟨n, hn⟩ : N) ^ 4 : N) = 1 := e.injective (by rw [map_pow, map_one]; exact h4 _)
      simpa using congrArg Subtype.val h
    · refine ⟨e.symm a0, (e.symm a0).2, fun h => ha0 ?_⟩
      have h' : e.symm a0 * e.symm a0 = 1 := Subtype.ext (by simpa using h)
      have := congrArg e h'
      rwa [map_mul, map_one, MulEquiv.apply_symm_apply] at this
  intro N hN
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩
  · exact key' N _ hN e (by decide) (by simp) (by decide) (by decide)
  · exact key' N _ hN e (by decide) (by simp) (by decide) (by decide)

open CFSG.ABGLocalTools CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink

theorem card_Eg_inf_centralizer_le_of_P0_sq
    {x : J} (hx : x ∈ P0)
    (hxE : x ∉ Eg uJ 11) (hsq : x * x ∈ Eg uJ 11) :
    Nat.card ↥(Eg uJ 11 ⊓ centralizer ({x} : Set J)) ≤ 128 := by
  have hF := j4Facts
  have hM := hF.mat
  obtain ⟨t, htL, hxt⟩ := table_of_mem hM x hx
  have h1 : compT t t = idT := by
    have h := hxt.mul hxt
    exact h.unique hM (Acts.of_mem_Eg hM hsq)
  have h2 : t ≠ idT := by
    intro ht
    subst ht
    apply hxE
    refine centralizer_Hj hM hF x (P0_le_Hj hx) (fun y hy => ?_)
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have := hxt.2 c hc
    rw [actT_idT hc] at this
    calc x * eta uJ 11 c = (x * eta uJ 11 c * x⁻¹) * x := by group
      _ = eta uJ 11 c * x := by rw [this]
  refine card_inf_le hM (fun y hy => ?_) hxt (fixCount_le t htL h1 h2)
  rw [mem_centralizer_singleton_iff] at hy
  exact hy.symm

theorem card_Eg_inf_centralizer_le_sq
    {x : J} (hx : x ∈ Hj) (hxE : x ∉ Eg uJ 11)
    (hsq : x * x ∈ Eg uJ 11) : Nat.card ↥(Eg uJ 11 ⊓ centralizer ({x} : Set J)) ≤ 128 := by
  have hM := j4Facts.mat
  have hp : IsPGroup 2 (zpowers x) := by
    have h4 : x ^ 4 = 1 := by
      have := Eg_sq (elem_uJ hM) hsq
      calc x ^ 4 = x * x * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
        _ = 1 := this
    have hord : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num; exact h4)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨k, hk, hconj⟩ := exists_conj_le_of_isSylowOf isSylowOf_P0_Hj hp (zpowers_le.mpr hx)
  have hx' : k⁻¹ * x * k ∈ P0 := hconj x (mem_zpowers x)
  have hxE' : k⁻¹ * x * k ∉ Eg uJ 11 := by
    intro hmem
    apply hxE
    have h := Hj_normalizes_Eg hM k hk _ hmem
    have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
    rwa [e] at h
  have hsq' : (k⁻¹ * x * k) * (k⁻¹ * x * k) ∈ Eg uJ 11 := by
    have e : (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
    rw [e]
    have := Hj_normalizes_Eg hM k⁻¹ (inv_mem hk) (x * x) hsq
    rwa [inv_inv] at this
  have hmap : ∀ e ∈ Eg uJ 11 ⊓ centralizer ({x} : Set J),
      k⁻¹ * e * k ∈ Eg uJ 11 ⊓ centralizer ({k⁻¹ * x * k} : Set J) := by
    intro e he
    rw [mem_inf] at he ⊢
    obtain ⟨heE, hec⟩ := he
    rw [mem_centralizer_singleton_iff] at hec ⊢
    refine ⟨?_, ?_⟩
    · have h := Hj_normalizes_Eg hM k⁻¹ (inv_mem hk) e heE
      rwa [inv_inv] at h
    · calc k⁻¹ * e * k * (k⁻¹ * x * k) = k⁻¹ * (e * x) * k := by group
        _ = k⁻¹ * (x * e) * k := by rw [hec]
        _ = k⁻¹ * x * k * (k⁻¹ * e * k) := by group
  calc Nat.card ↥(Eg uJ 11 ⊓ centralizer ({x} : Set J))
      ≤ Nat.card ↥(Eg uJ 11 ⊓ centralizer ({k⁻¹ * x * k} : Set J)) := by
        refine Nat.card_le_card_of_injective (fun e => ⟨k⁻¹ * e * k, hmap e e.2⟩) ?_
        intro a b hab
        have h := congrArg Subtype.val hab
        simp only at h
        exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
    _ ≤ 128 := card_Eg_inf_centralizer_le_of_P0_sq hx' hxE' hsq'

theorem noNormalFour_centralizer_eta_one :
    NoNormalFour (centralizer ({eta uJ 11 1} : Set J)) := by
  have hM := j4Facts.mat
  have hel := elem_uJ hM
  have hCH : ∀ c ∈ centralizer ({eta uJ 11 1} : Set J), c ∈ Hj := by
    intro c hc
    rw [mem_centralizer_singleton_iff] at hc
    exact centralizer_eta_one_le_Hj hc
  refine noNormalFour_of_commutator (eta uJ 11 1) (Eg uJ 11) (fun x hx w hw => Eg_comm hel hx hw)
    (card_Eg_uJ hM) (fun e he => Eg_sq hel he) (fun e he => ?_) (fun c hc e he => ?_)
    (fun t htC htE htsq => card_Eg_inf_centralizer_le_sq (hCH t htC) htE htsq)
  · rw [mem_centralizer_singleton_iff]
    exact Eg_comm hel he (eta_mem_Eg 11 le_rfl 1)
  · exact Hj_normalizes_Eg hM c (hCH c hc) e he

end CFSG.EvenSporadicStandard.J4Std
