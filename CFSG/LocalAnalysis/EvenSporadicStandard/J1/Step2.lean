module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem relIndex_sup_right_of_le_normalizer {H K : Subgroup G}
    (hH : H ≤ normalizer (K : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hH
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hH).toEquiv.symm

theorem conj_coset_fixed {R S : Subgroup G} (hidx : S.relIndex R ≤ 6) {σ : G}
    (hσ7 : σ ^ 7 = 1) (hσR : σ ∈ normalizer (R : Set G)) (hσS : σ ∈ normalizer (S : Set G))
    {r : G} (hr : r ∈ R) : σ * r * σ⁻¹ * r⁻¹ ∈ S := by
  have hσ'7 : R.normalizerMonoidHom ⟨σ, hσR⟩ ^ 7 = 1 := by
    ext a
    have := normalizerMonoidHom_pow_apply hσR 7 a
    rw [hσ7] at this
    simpa using this
  have hS' : (S.subgroupOf R).map (R.normalizerMonoidHom ⟨σ, hσR⟩).toMonoidHom =
      S.subgroupOf R := by
    refine Subgroup.ext fun x => ?_
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      exact (mem_normalizer_iff.1 hσS (y : G)).1 hy
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hσR' : σ⁻¹ ∈ normalizer (R : Set G) := inv_mem hσR
      have hσS' : σ⁻¹ ∈ normalizer (S : Set G) := inv_mem hσS
      have hmemR : σ⁻¹ * x * σ ∈ R := by
        have := (mem_normalizer_iff.1 hσR' (x : G)).1 x.2
        simpa using this
      refine ⟨⟨σ⁻¹ * x * σ, hmemR⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        have := (mem_normalizer_iff.1 hσS' (x : G)).1 hx
        simpa using this
      · apply Subtype.ext
        show σ * (σ⁻¹ * x * σ) * σ⁻¹ = x
        group
  exact coset_fixed_of_small_index (S := S.subgroupOf R) hidx
    (R.normalizerMonoidHom ⟨σ, hσR⟩) hσ'7 hS' ⟨r, hr⟩

namespace Setting

@[expose] def RC (H : Setting G) (S : Subgroup G) : Subgroup G :=
  centralizer (H.E : Set G) ⊓ normalizer (S : Set G)

end Setting

namespace Stage

variable {H : Setting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem S_le_RC : S ≤ H.RC S := by
  intro s hs
  refine ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, le_normalizer hs⟩
  rcases h.cover s hs with hsΛ | hsz
  · exact h.comm (h.E_le he) hsΛ
  · obtain ⟨t, htΛ, rfl⟩ : ∃ t ∈ Λ, s = t * H.z :=
      ⟨s * H.z, hsz, by rw [mul_assoc, H.z_mul_self, mul_one]⟩
    calc e * (t * H.z) = (e * t) * H.z := by group
      _ = (t * e) * H.z := by rw [h.comm (h.E_le he) htΛ]
      _ = t * (e * H.z) := by group
      _ = t * (H.z * e) := by rw [H.z_comm_E he]
      _ = t * H.z * e := by group

include h in
theorem N_conj_E {n e : G} (hn : n ∈ normalizer (S : Set G)) (he : e ∈ H.E) :
    n * e * n⁻¹ ∈ H.E := by
  refine h.mem_E_of_sq (h.N_normalizes_Λ hn (h.E_le he)) ?_
  calc n * e * n⁻¹ * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
    _ = 1 := by rw [H.sq_E e he]; group

include h in
theorem N_conj_RC {n r : G} (hn : n ∈ normalizer (S : Set G)) (hr : r ∈ H.RC S) :
    n * r * n⁻¹ ∈ H.RC S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, ?_⟩
  · have h1 : n⁻¹ * e * n ∈ H.E := by
      have := h.N_conj_E (inv_mem hn) he
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr).1 _ h1
    calc e * (n * r * n⁻¹) = n * ((n⁻¹ * e * n) * r) * n⁻¹ := by group
      _ = n * (r * (n⁻¹ * e * n)) * n⁻¹ := by rw [h2]
      _ = n * r * n⁻¹ * e := by group
  · exact mul_mem (mul_mem hn (Subgroup.mem_inf.1 hr).2) (inv_mem hn)

include h in
theorem N_le_normalizer_RC :
    normalizer (S : Set G) ≤ normalizer ((H.RC S : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun r => ⟨fun hr => h.N_conj_RC hn hr, fun hr => ?_⟩
  have := h.N_conj_RC (inv_mem hn) hr
  simpa [mul_assoc] using this

include h in
theorem RC_inf_B : H.RC S ⊓ H.B = H.V := by
  refine le_antisymm (fun x ⟨hxR, hxB⟩ => ?_) (le_inf (h.V_le.trans h.S_le_RC) H.V_le_B)
  have hxz : x * H.z = H.z * x := mem_centralizer_singleton_iff.1 (H.B_le_centralizer hxB)
  rw [← H.centralizer_V]
  refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
  rcases H.mem_V_iff'.1 hv with hvE | ⟨e, he, rfl⟩
  · exact Subgroup.mem_centralizer_iff.1 hxR.1 v hvE
  · have h1 := Subgroup.mem_centralizer_iff.1 hxR.1 e he
    calc e * H.z * x = e * (H.z * x) := by group
      _ = e * (x * H.z) := by rw [hxz]
      _ = (e * x) * H.z := by group
      _ = (x * e) * H.z := by rw [h1]
      _ = x * (e * H.z) := by group

include h in
theorem mem_S_of_sigma_coset {σ r : G} (hσ : σ ∈ H.NL) (h7 : orderOf σ = 7) (hr : r ∈ H.RC S)
    (hcoset : σ * r * σ⁻¹ * r⁻¹ ∈ S) : r ∈ S := by
  have hrN : r ∈ normalizer (S : Set G) := (Subgroup.mem_inf.1 hr).2
  obtain ⟨φ, hφ7, hφfree, hφpow⟩ := h.exists_sigma_aut hσ h7
  have hσz : σ * H.z = H.z * σ := H.comm_z (H.mem_NL_iff.1 hσ).1
  have hσz' : σ * H.z * σ⁻¹ = H.z := by rw [hσz]; group
  have hσz'' : σ⁻¹ * H.z * σ = H.z := by
    calc σ⁻¹ * H.z * σ = σ⁻¹ * (H.z * σ) := by group
      _ = σ⁻¹ * (σ * H.z) := by rw [hσz]
      _ = H.z := by group
  obtain ⟨hxS, hxΛ⟩ := h.N_conj_z_mem hrN
  have hlΛ : H.z * (r * H.z * r⁻¹) ∈ Λ := h.z_mul_mem_Λ hxS hxΛ
  obtain ⟨l, hl⟩ : ∃ l : G, l = H.z * (r * H.z * r⁻¹) := ⟨_, rfl⟩
  have hxl : r * H.z * r⁻¹ = H.z * l := by
    rw [hl, ← mul_assoc, H.z_mul_self, one_mul]
  rw [← hl] at hlΛ
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : G, s₁ = σ * r * σ⁻¹ * r⁻¹ := ⟨_, rfl⟩
  rw [← hs₁] at hcoset
  have h1 : σ * (H.z * l) * σ⁻¹ = s₁ * (H.z * l) * s₁⁻¹ := by
    rw [← hxl, hs₁]
    calc σ * (r * H.z * r⁻¹) * σ⁻¹ = σ * r * (σ⁻¹ * H.z * σ) * r⁻¹ * σ⁻¹ := by
          rw [hσz'']; group
      _ = σ * r * σ⁻¹ * r⁻¹ * (r * H.z * r⁻¹) * (σ * r * σ⁻¹ * r⁻¹)⁻¹ := by group
  obtain ⟨m, hmΛ, hm⟩ := h.conj_zl hcoset hlΛ
  have h2 : σ * (H.z * l) * σ⁻¹ = H.z * (σ * l * σ⁻¹) := by
    calc σ * (H.z * l) * σ⁻¹ = (σ * H.z * σ⁻¹) * (σ * l * σ⁻¹) := by group
      _ = H.z * (σ * l * σ⁻¹) := by rw [hσz']
  have h3 : σ * l * σ⁻¹ = l * (m * m) :=
    mul_left_cancel (a := H.z) ((h2.symm.trans (h1.trans hm)).trans (mul_assoc _ _ _))
  have hφ1 : ∀ a : Λ, (φ a : G) = σ * a * σ⁻¹ := fun a => by simpa using hφpow 1 a
  have hsq : ∃ b : Λ, φ ⟨l, hlΛ⟩ * ⟨l, hlΛ⟩⁻¹ = b * b := by
    refine ⟨⟨m, hmΛ⟩, Subtype.ext ?_⟩
    show (φ ⟨l, hlΛ⟩ : G) * l⁻¹ = m * m
    rw [hφ1]
    show σ * l * σ⁻¹ * l⁻¹ = m * m
    rw [h3]
    calc l * (m * m) * l⁻¹ = (m * m) * l * l⁻¹ := by rw [h.comm hlΛ (mul_mem hmΛ hmΛ)]
      _ = m * m := by group
  obtain ⟨c, hc⟩ := mem_sq_of_sigma_fixed (fun a b => Subtype.ext (h.comm a.2 b.2)) φ hφ7
    hφfree hsq
  have hlc : l = c.1 * c.1 := congrArg Subtype.val hc
  obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl (one_mem Λ) c.2
  have hxs : r * H.z * r⁻¹ = s * H.z * s⁻¹ := by
    rw [hxl, hlc]
    simpa using hseq.symm
  have hu : s⁻¹ * r ∈ centralizer ({H.z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc s⁻¹ * r * H.z = s⁻¹ * (r * H.z * r⁻¹) * r := by group
      _ = s⁻¹ * (s * H.z * s⁻¹) * r := by rw [hxs]
      _ = H.z * (s⁻¹ * r) := by group
  have huN : s⁻¹ * r ∈ normalizer (S : Set G) := mul_mem (inv_mem (le_normalizer hs)) hrN
  have huB : s⁻¹ * r ∈ H.B := h.centralizer_N ▸ Subgroup.mem_inf.2 ⟨hu, huN⟩
  have huR : s⁻¹ * r ∈ H.RC S := mul_mem (inv_mem (h.S_le_RC hs)) hr
  have huV : s⁻¹ * r ∈ H.V := h.RC_inf_B ▸ Subgroup.mem_inf.2 ⟨huR, huB⟩
  have := mul_mem hs (h.V_le huV)
  simpa using this

include h in
theorem RC_cases (hS : 2 ∣ S.index) :
    Nat.card (H.RC S) = Nat.card S ∨ Nat.card (H.RC S) = 8 * Nat.card S := by
  have hSR : S ≤ H.RC S := h.S_le_RC
  have hRN : H.RC S ≤ normalizer (S : Set G) := inf_le_right
  have hBnorm : H.B ≤ normalizer ((H.RC S : Subgroup G) : Set G) := fun b hb =>
    h.N_le_normalizer_RC (h.B_S hb)
  have hrel : (H.RC S).relIndex H.B = 21 := by
    have h1 := Subgroup.relIndex_mul_card (H := H.RC S) (K := H.B)
    rw [h.RC_inf_B, H.card_V, H.card_B] at h1
    omega
  have hsup : 21 * Nat.card (H.RC S) = Nat.card ↥(H.B ⊔ H.RC S) := by
    have h1 := Subgroup.relIndex_mul_card (H := H.RC S) (K := H.B ⊔ H.RC S)
    rw [inf_eq_left.2 le_sup_right, relIndex_sup_right_of_le_normalizer hBnorm, hrel] at h1
    exact h1
  have hdvd : 21 * Nat.card (H.RC S) ∣ 21 * (8 * Nat.card S) := by
    have hS8 : 336 * Nat.card Λ = 21 * (8 * Nat.card S) := by
      have := h.card_S
      omega
    rw [hsup, ← hS8, ← h.card_N hS]
    exact Subgroup.card_dvd_of_le (sup_le h.B_S hRN)
  have hdvd' : Nat.card (H.RC S) ∣ 8 * Nat.card S :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  obtain ⟨m, hm⟩ : Nat.card S ∣ Nat.card (H.RC S) := Subgroup.card_dvd_of_le hSR
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hm8 : m ∣ 8 := by
    rw [hm, mul_comm 8] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left hSpos hdvd'
  have hrelS : S.relIndex (H.RC S) = m := by
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := H.RC S)
    rw [inf_eq_left.2 hSR, hm] at h1
    exact Nat.eq_of_mul_eq_mul_right hSpos (h1.trans (mul_comm _ _))
  by_cases hm6 : m ≤ 6
  · left
    obtain ⟨σ, hσ, h7⟩ := H.exists_sigma
    have hσ7 : σ ^ 7 = 1 := by rw [← h7]; exact pow_orderOf_eq_one σ
    have hσB : σ ∈ H.B := H.NL_le_B hσ
    have hRS : H.RC S ≤ S := fun r hr =>
      h.mem_S_of_sigma_coset hσ h7 hr
        (conj_coset_fixed (hrelS ▸ hm6) hσ7 (hBnorm hσB) (h.B_S hσB) hr)
    rw [le_antisymm hRS hSR]
  · right
    have h8 : m = 8 := by
      have := Nat.le_of_dvd (by norm_num) hm8
      rcases (by omega : m = 7 ∨ m = 8) with rfl | rfl
      · exact absurd hm8 (by norm_num)
      · rfl
    rw [hm, h8, mul_comm]

end Stage

end CFSG.EvenSporadicStandard.J1Std
