module

public import CFSG.CGT.Timmesfeld75.Sec213

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG CFSG.Open
open scoped commutatorElement

section OddNormal

variable {K : Type*} [Group K] [Finite K]

theorem oddNormal_comm_of_le_normalizer {P : Subgroup K} (hP : IsElemAbelian 2 P)
    (h4 : 4 ≤ Nat.card P) (N : Subgroup K) (hPN : P ≤ Subgroup.normalizer (N : Set K))
    (hNodd : Odd (Nat.card N))
    (hdich : ∀ n ∈ N, ∀ u ∈ P, u ≠ 1 → u * n = n * u → ∀ y ∈ P, y * n = n * y) :
    ∀ n ∈ N, ∀ y ∈ P, y * n = n * y := by
  let _ : MulDistribMulAction P N :=
    MulDistribMulAction.compHom N (N.normalizerMonoidHom.comp (Subgroup.inclusion hPN))
  have : Fact (IsPGroup 2 P) := ⟨isPGroup_two_of_isElemAbelian hP⟩
  let _ : CommGroup P :=
    { (inferInstance : Group P) with mul_comm := fun a b => hP.1.is_comm.comm a b }
  have hncyc : ¬ IsCyclic P := by
    intro hcyc
    obtain ⟨c, hc⟩ := hcyc.exists_generator
    have h1 : orderOf c = Nat.card P := orderOf_eq_card_of_forall_mem_zpowers hc
    have h2 : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hP.2 c c.2))
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := N) (A := P) 2 (Nat.coprime_two_left.2 hNodd) hncyc
  intro n hn y hy
  have hmem : (⟨n, hn⟩ : N) ∈ ⨆ (a : P) (_ : a ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers a)) N := by
    rw [htop]
    exact Subgroup.mem_top _
  have hle : (⨆ (a : P) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) N) ≤
      (Subgroup.centralizer (P : Set K)).comap N.subtype := by
    refine iSup₂_le fun a ha1 m hm => ?_
    rw [FixedPoints.mem_subgroup] at hm
    have h2 : (a : K) * m * (a : K)⁻¹ = m := congrArg Subtype.val (hm ⟨a, Subgroup.mem_zpowers a⟩)
    rw [mul_inv_eq_iff_eq_mul] at h2
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro z hz
    exact hdich m m.2 a a.2 (fun h => ha1 (Subtype.ext h)) h2 z hz
  exact Subgroup.mem_centralizer_iff.1 (hle hmem) y hy

end OddNormal

section Weak

variable {K : Type*} [Group K] {A L : Subgroup K}

theorem comm_of_conj_comm_of_inf_eq_bot [A.Normal] (hL : IsWC L) (hAL : A ⊓ L = ⊥) {t : K}
    (ht : t ∈ L) (ht1 : t ≠ 1) {a : K} (ha : a ∈ A)
    (h : ∀ z ∈ L, z * (a * t * a⁻¹) = (a * t * a⁻¹) * z) : ∀ y ∈ L, a * y = y * a := by
  have hle : conjSubgroup a⁻¹ L ≤ Subgroup.centralizer ({t} : Set K) := by
    intro x hx
    rw [mem_conjSubgroup, inv_inv] at hx
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 := h _ hx
    calc x * t = a⁻¹ * ((a * x * a⁻¹) * (a * t * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * t * a⁻¹) * (a * x * a⁻¹)) * a := by rw [h1]
      _ = t * x := by group
  have hconj : conjSubgroup a⁻¹ L = L := (hL.2 t ht ht1).2 a⁻¹ hle
  intro y hy
  have hy' : a⁻¹ * y * a ∈ L := by
    have hmem : a⁻¹ * y * a ∈ conjSubgroup a⁻¹ L := by
      rw [mem_conjSubgroup]
      have e : (a⁻¹)⁻¹ * (a⁻¹ * y * a) * a⁻¹ = y := by group
      rw [e]
      exact hy
    rwa [hconj] at hmem
  have hwL : y⁻¹ * a⁻¹ * y * a ∈ L := by
    have := L.mul_mem (L.inv_mem hy) hy'
    simpa [mul_assoc] using this
  have hwA : y⁻¹ * a⁻¹ * y * a ∈ A := by
    have h1 : y⁻¹ * a⁻¹ * y⁻¹⁻¹ ∈ A := Subgroup.Normal.conj_mem inferInstance a⁻¹ (A.inv_mem ha) y⁻¹
    have := A.mul_mem h1 ha
    simpa [mul_assoc] using this
  have hw1 : y⁻¹ * a⁻¹ * y * a = 1 := by
    have hw : y⁻¹ * a⁻¹ * y * a ∈ A ⊓ L := ⟨hwA, hwL⟩
    rwa [hAL, Subgroup.mem_bot] at hw
  calc a * y = a * y * (y⁻¹ * a⁻¹ * y * a) := by rw [hw1, mul_one]
    _ = y * a := by group

end Weak

section Main

variable {K : Type} [Group K] [Finite K] {A L : Subgroup K}

theorem IsWC.comm_of_inf_eq_bot [A.Normal]
    (hL : IsWC L) (h4 : 4 ≤ Nat.card L) (hAL : A ⊓ L = ⊥) :
    ∀ a ∈ A, ∀ y ∈ L, a * y = y * a := by
  have hLc : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy => elemAbelian_mul_comm hL.1 hx hy
  have hLsq : ∀ y ∈ L, y * y = 1 := fun y hy => by simpa [pow_two] using hL.1.2 y hy
  have Ω : ∀ t ∈ L, t ≠ 1 → ∀ a ∈ A,
      (∀ z ∈ L, z * (a * t * a⁻¹) = (a * t * a⁻¹) * z) → ∀ y ∈ L, a * y = y * a :=
    fun t ht ht1 a ha h => comm_of_conj_comm_of_inf_eq_bot hL hAL ht ht1 ha h
  intro a ha y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    simp
  obtain ⟨R, hRA, -, hRodd, hRc⟩ := exists_odd_subgroup_commutators (M := A) inferInstance hy1
    (hLsq y hy) fun g hg hc => conj_eq_of_mem_sup_of_commute hL inferInstance hAL hy hy1 hg hc
  let N : Subgroup K := Subgroup.closure {r | ∃ m ∈ A, r = m * y * m⁻¹ * y⁻¹}
  have hNR : N ≤ R :=
    (Subgroup.closure_le R).2 (by rintro _ ⟨m, hm, rfl⟩; exact hRc m hm)
  have hNA : N ≤ A := hNR.trans hRA
  have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hNR)
  have hconjN : ∀ x ∈ L, ∀ r ∈ N, x * r * x⁻¹ ∈ N := by
    intro x hx r hr
    refine Subgroup.closure_induction (p := fun r _ => x * r * x⁻¹ ∈ N) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨m, hm, rfl⟩
      refine Subgroup.subset_closure ⟨x * m * x⁻¹, Subgroup.Normal.conj_mem inferInstance m hm x, ?_⟩
      have e1 : x * y * x⁻¹ = y := by rw [hLc x hx y hy]; group
      have e2 : x * y⁻¹ * x⁻¹ = y⁻¹ := by
        have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
        rw [this, e1]
      have e3 : x * m⁻¹ * x⁻¹ = (x * m * x⁻¹)⁻¹ := by group
      calc x * (m * y * m⁻¹ * y⁻¹) * x⁻¹
          = (x * m * x⁻¹) * (x * y * x⁻¹) * (x * m⁻¹ * x⁻¹) * (x * y⁻¹ * x⁻¹) := by group
        _ = (x * m * x⁻¹) * y * (x * m * x⁻¹)⁻¹ * y⁻¹ := by rw [e1, e2, e3]
    · simp
    · intro r₁ r₂ _ _ h₁ h₂
      have : x * (r₁ * r₂) * x⁻¹ = (x * r₁ * x⁻¹) * (x * r₂ * x⁻¹) := by group
      rw [this]
      exact N.mul_mem h₁ h₂
    · intro r _ h
      have : x * r⁻¹ * x⁻¹ = (x * r * x⁻¹)⁻¹ := by group
      rw [this]
      exact N.inv_mem h
  have hLN : L ≤ Subgroup.normalizer (N : Set K) := le_normalizer_of_forall_conj hconjN
  have hdich : ∀ n ∈ N, ∀ u ∈ L, u ≠ 1 → u * n = n * u → ∀ z ∈ L, z * n = n * z := by
    intro n hn u hu hu1 hun z hz
    have hnu : n * u * n⁻¹ = u := by
      calc n * u * n⁻¹ = (u * n) * n⁻¹ := by rw [hun]
        _ = u := by group
    exact ((Ω u hu hu1 n (hNA hn) (fun w hw => by rw [hnu]; exact hLc w hw u hu)) z hz).symm
  have hcomm := oddNormal_comm_of_le_normalizer hL.1 h4 N hLN hNodd hdich
  have hr : a * y * a⁻¹ * y⁻¹ ∈ N := Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hrz := hcomm _ hr
  obtain ⟨r, hrdef⟩ : ∃ r, r = a * y * a⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hrdef] at hrz
  refine (Ω y hy hy1 a ha (fun z hz => ?_)) y hy
  have e : a * y * a⁻¹ = r * y := by rw [hrdef]; group
  rw [e]
  calc z * (r * y) = (z * r) * y := (mul_assoc _ _ _).symm
    _ = (r * z) * y := by rw [hrz z hz]
    _ = r * (z * y) := mul_assoc _ _ _
    _ = r * (y * z) := by rw [hLc z hz y hy]
    _ = (r * y) * z := (mul_assoc _ _ _).symm

end Main

end CFSG.CGT.Timmesfeld75
