module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Simple

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem E_le_centralizer_e : E ≤ centralizer ({e} : Set Γ) := fun _ hx =>
  mem_centralizer_singleton_iff.2 (hS.comm_of_mem_E hx hS.mem)

theorem inf_centralizer_e_eq {N : Subgroup Γ} (hEN : E ≤ N) (h : N ⊓ H₁ = E ⊓ H₁) :
    N ⊓ centralizer ({e} : Set Γ) = E := by
  refine le_antisymm (fun x hx => ?_) (le_inf hEN hS.E_le_centralizer_e)
  have hxe := hx.2
  rw [hS.centralizer_e] at hxe
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer hS.zpowers_le_centralizer hxe
  have hbE : b ∈ E := zpowers_le.2 hS.mem hb
  have haN : a ∈ N ⊓ H₁ := ⟨by simpa using N.mul_mem hx.1 (N.inv_mem (hEN hbE)), ha⟩
  rw [h] at haN
  exact E.mul_mem haN.1 hbE

section Finite

variable [Finite Γ]

theorem eq_top_of_H₁_le {N : Subgroup Γ} [hN : N.Normal] (hEN : E ≤ N) (hH : H₁ ≤ N) :
    N = ⊤ := by
  have hC : centralizer ({e} : Set Γ) ≤ N := by
    rw [hS.centralizer_e]
    exact sup_le hH (zpowers_le.2 (hEN hS.mem))
  by_contra hne
  have hNC : N = centralizer ({e} : Set Γ) := by
    by_contra h
    exact hne (hS.eq_top_of_centralizer_le hC h)
  have hCΩ : centralizer ({e} : Set Γ) ≤ centralizer (omega e) := by
    intro c hc
    rw [mem_centralizer_iff]
    rintro _ ⟨γ, rfl⟩
    have hcN : c ∈ N := by
      rw [hNC]
      exact hc
    have hc' : γ⁻¹ * c * γ ∈ centralizer ({e} : Set Γ) := by
      rw [← hNC]
      exact hN.conj_mem' c hcN γ
    have h1 : γ⁻¹ * c * γ * e = e * (γ⁻¹ * c * γ) := mem_centralizer_singleton_iff.1 hc'
    calc γ * e * γ⁻¹ * c = γ * (e * (γ⁻¹ * c * γ)) * γ⁻¹ := by group
      _ = γ * ((γ⁻¹ * c * γ) * e) * γ⁻¹ := by rw [h1]
      _ = c * (γ * e * γ⁻¹) := by group
  rw [hS.centralizer_omega] at hCΩ
  have hle := Subgroup.card_le_of_le hCΩ
  rw [hS.card_centralizer_e, hS.card_H₁, hS.card] at hle
  omega

theorem eq_E_of_inf_eq {N : Subgroup Γ} [hN : N.Normal] (hEN : E ≤ N) (h : N ⊓ H₁ = E ⊓ H₁) :
    N = E := by
  have := hS.normal
  have hNC : N ⊓ centralizer ({e} : Set Γ) = E := hS.inf_centralizer_e_eq hEN h
  have hle : centralizer ({e} : Set Γ) ≤ N ⊔ centralizer ({e} : Set Γ) := le_sup_right
  by_cases hsup : N ⊔ centralizer ({e} : Set Γ) = centralizer ({e} : Set Γ)
  · refine le_antisymm (fun x hx => ?_) hEN
    have hxC : x ∈ centralizer ({e} : Set Γ) := by
      rw [← hsup]
      exact mem_sup_left hx
    rw [← hNC]
    exact ⟨hx, hxC⟩
  have htop := hS.eq_top_of_centralizer_le hle hsup
  have hΩ : ∀ γ : Γ, ∃ n ∈ N, γ * e * γ⁻¹ = n * e * n⁻¹ := by
    intro γ
    have hγ : γ ∈ N ⊔ centralizer ({e} : Set Γ) := by
      rw [htop]
      exact mem_top γ
    obtain ⟨n, hn, c, hc, rfl⟩ := mem_sup_of_normal_left.1 hγ
    refine ⟨n, hn, ?_⟩
    have hce : c * e = e * c := mem_centralizer_singleton_iff.1 hc
    calc n * c * e * (n * c)⁻¹ = n * (c * e) * c⁻¹ * n⁻¹ := by group
      _ = n * (e * c) * c⁻¹ * n⁻¹ := by rw [hce]
      _ = n * e * n⁻¹ := by group
  have horb : {y : Γ | ∃ a ∈ N, y = a * e * a⁻¹} = {x : Γ | ∃ h : Γ, x = h * e * h⁻¹} := by
    ext y
    constructor
    · rintro ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨γ, rfl⟩
      obtain ⟨n, hn, hnγ⟩ := hΩ γ
      exact ⟨n, hn, hnγ⟩
  have hrel : E.relIndex N = 24 := by
    have h1 := ncard_conj_orbit N e
    rw [horb, hS.orbit] at h1
    have h2 : (centralizer ({e} : Set Γ) ⊓ N).relIndex N =
        (centralizer ({e} : Set Γ)).relIndex N := Subgroup.inf_relIndex_right _ _
    rw [inf_comm, hNC] at h2
    exact h2.trans h1.symm
  have hQ : Nat.card (↥N ⧸ E.subgroupOf N) = 24 := by
    rw [← Subgroup.index_eq_card]
    exact hrel
  have hd2 : 2 ∣ Nat.card (↥N ⧸ E.subgroupOf N) := by
    rw [hQ]
    norm_num
  have hd3 : 3 ∣ Nat.card (↥N ⧸ E.subgroupOf N) := by
    rw [hQ]
    norm_num
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' 2 hd2
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' 3 hd3
  obtain ⟨n₂, rfl⟩ := QuotientGroup.mk_surjective x₂
  obtain ⟨n₃, rfl⟩ := QuotientGroup.mk_surjective x₃
  have hn₂E : (n₂ : Γ) ∉ E := by
    intro hmem
    have h1 : (QuotientGroup.mk n₂ : ↥N ⧸ E.subgroupOf N) = 1 :=
      (QuotientGroup.eq_one_iff n₂).2 (mem_subgroupOf.2 hmem)
    rw [h1, orderOf_one] at hx₂
    norm_num at hx₂
  have hn₃E : (n₃ : Γ) ∉ E := by
    intro hmem
    have h1 : (QuotientGroup.mk n₃ : ↥N ⧸ E.subgroupOf N) = 1 :=
      (QuotientGroup.eq_one_iff n₃).2 (mem_subgroupOf.2 hmem)
    rw [h1, orderOf_one] at hx₃
    norm_num at hx₃
  have hn₂sq : (n₂ : Γ) ^ 2 ∈ E := by
    have h1 : (QuotientGroup.mk (n₂ ^ 2) : ↥N ⧸ E.subgroupOf N) = 1 := by
      rw [QuotientGroup.mk_pow, ← hx₂]
      exact pow_orderOf_eq_one _
    have := (QuotientGroup.eq_one_iff (n₂ ^ 2)).1 h1
    simpa [mem_subgroupOf] using this
  have hn₃cube : (n₃ : Γ) ^ 3 ∈ E := by
    have h1 : (QuotientGroup.mk (n₃ ^ 3) : ↥N ⧸ E.subgroupOf N) = 1 := by
      rw [QuotientGroup.mk_pow, ← hx₃]
      exact pow_orderOf_eq_one _
    have := (QuotientGroup.eq_one_iff (n₃ ^ 3)).1 h1
    simpa [mem_subgroupOf] using this
  have hmove : ∀ m : ↥N, (m : Γ) ∉ E → (m : Γ) * e * (m : Γ)⁻¹ ≠ e := by
    intro m hm hcon
    apply hm
    have hmC : (m : Γ) ∈ centralizer ({e} : Set Γ) := by
      rw [mem_centralizer_singleton_iff]
      calc (m : Γ) * e = ((m : Γ) * e * (m : Γ)⁻¹) * m := by group
        _ = e * m := by rw [hcon]
    rw [← hNC]
    exact ⟨m.2, hmC⟩
  obtain ⟨p, hpH, hp⟩ := hS.transitive (ω := (n₂ : Γ) * e * (n₂ : Γ)⁻¹)
    (ω' := (n₃ : Γ) * e * (n₃ : Γ)⁻¹) ⟨n₂, rfl⟩ ⟨n₃, rfl⟩ (hmove n₂ hn₂E) (hmove n₃ hn₃E)
  have hpe : p⁻¹ * e * p = e := by
    have h1 := hS.commute_of_mem_H₁ hpH
    calc p⁻¹ * e * p = p⁻¹ * (e * p) := by group
      _ = p⁻¹ * (p * e) := by rw [h1]
      _ = e := by group
  have hmN : p * (n₂ : Γ) * p⁻¹ ∈ N := hN.conj_mem _ n₂.2 p
  have hm : (p * (n₂ : Γ) * p⁻¹) * e * (p * (n₂ : Γ) * p⁻¹)⁻¹ = (n₃ : Γ) * e * (n₃ : Γ)⁻¹ := by
    calc (p * (n₂ : Γ) * p⁻¹) * e * (p * (n₂ : Γ) * p⁻¹)⁻¹
        = p * (n₂ : Γ) * (p⁻¹ * e * p) * (n₂ : Γ)⁻¹ * p⁻¹ := by group
      _ = p * ((n₂ : Γ) * e * (n₂ : Γ)⁻¹) * p⁻¹ := by rw [hpe]; group
      _ = (n₃ : Γ) * e * (n₃ : Γ)⁻¹ := hp
  have hzc : (n₃ : Γ)⁻¹ * (p * (n₂ : Γ) * p⁻¹) * e = e * ((n₃ : Γ)⁻¹ * (p * (n₂ : Γ) * p⁻¹)) :=
    calc (n₃ : Γ)⁻¹ * (p * (n₂ : Γ) * p⁻¹) * e
        = (n₃ : Γ)⁻¹ * ((p * (n₂ : Γ) * p⁻¹) * e * (p * (n₂ : Γ) * p⁻¹)⁻¹) *
            (p * (n₂ : Γ) * p⁻¹) := by group
      _ = (n₃ : Γ)⁻¹ * ((n₃ : Γ) * e * (n₃ : Γ)⁻¹) * (p * (n₂ : Γ) * p⁻¹) := by rw [hm]
      _ = e * ((n₃ : Γ)⁻¹ * (p * (n₂ : Γ) * p⁻¹)) := by group
  have hz : (n₃ : Γ)⁻¹ * (p * (n₂ : Γ) * p⁻¹) ∈ E := by
    rw [← hNC]
    exact ⟨N.mul_mem (N.inv_mem n₃.2) hmN, mem_centralizer_singleton_iff.2 hzc⟩
  have hπ : (QuotientGroup.mk (n₃ : Γ) : Γ ⧸ E) = QuotientGroup.mk (p * (n₂ : Γ) * p⁻¹) :=
    QuotientGroup.eq.2 hz
  have hm2 : (QuotientGroup.mk ((p * (n₂ : Γ) * p⁻¹) ^ 2) : Γ ⧸ E) = 1 := by
    rw [QuotientGroup.eq_one_iff, conj_pow]
    exact hS.normal.conj_mem _ hn₂sq p
  have h2' : (QuotientGroup.mk (n₃ : Γ) : Γ ⧸ E) ^ 2 = 1 := by
    rw [hπ, ← QuotientGroup.mk_pow]
    exact hm2
  have h3' : (QuotientGroup.mk (n₃ : Γ) : Γ ⧸ E) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hn₃cube
  have h1' := pow_gcd_eq_one.2 ⟨h2', h3'⟩
  have hg : Nat.gcd 2 3 = 1 := by norm_num
  rw [hg, pow_one] at h1'
  exact absurd ((QuotientGroup.eq_one_iff _).1 h1') hn₃E

theorem normal_eq_or_eq_top {N : Subgroup Γ} [N.Normal] (hEN : E ≤ N) : N = E ∨ N = ⊤ := by
  have hnorm : ((N ⊓ H₁).subgroupOf H₁).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf
  rcases hS.eq_or_eq_of_normal_le inf_le_right hnorm (inf_le_inf_right _ hEN) with h | h
  · exact Or.inl (hS.eq_E_of_inf_eq hEN h)
  · exact Or.inr (hS.eq_top_of_H₁_le hEN (inf_eq_right.1 h))

theorem isSimpleGroup_quot [E.Normal] : IsSimpleGroup (Γ ⧸ E) := by
  have hnt : Nontrivial (Γ ⧸ E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hS.card_quot]
    norm_num
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := ?_ }
  intro T hT
  have hπ : Function.Surjective (QuotientGroup.mk' E) := QuotientGroup.mk'_surjective E
  have hEN : E ≤ T.comap (QuotientGroup.mk' E) := by
    intro x hx
    rw [mem_comap]
    have h1 : QuotientGroup.mk' E x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [h1]
    exact T.one_mem
  have : (T.comap (QuotientGroup.mk' E)).Normal := hT.comap _
  have hmc : (T.comap (QuotientGroup.mk' E)).map (QuotientGroup.mk' E) = T :=
    Subgroup.map_comap_eq_self_of_surjective hπ T
  rcases hS.normal_eq_or_eq_top hEN with h | h
  · left
    rw [← hmc, h]
    exact QuotientGroup.map_mk'_self E
  · right
    rw [← hmc, h]
    exact Subgroup.map_top_of_surjective _ hπ

end Finite

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance
