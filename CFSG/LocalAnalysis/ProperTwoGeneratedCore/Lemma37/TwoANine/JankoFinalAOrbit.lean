module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAComm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z}

theorem E_inf_M_le (h : Hyp fr) : fr.E ⊓ fr.M ≤ fr.P₁ := by
  rw [← h.p10.M_inf_centralizer_z, inf_comm]
  exact inf_le_inf_left _ fr.E_le

theorem E_inf_S (h : Hyp fr) : fr.E ⊓ fr.S = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hP : x ∈ fr.P₁ := E_inf_M_le h ⟨hx.1, h.S_le_M hx.2⟩
  exact (mem_bot).mpr (h.eq_one_of_mem_P₁_of_mem_Mbar hP (h.S_le_Mbar hx.2))

theorem N_le_normalizer_M (h : Hyp fr) : fr.N ≤ normalizer (fr.M : Set G) := fun _ hn =>
  h.normalizer_P₁_le_normalizer_M (le_normalizer_of_commute
    (fun _ hx y hy => ((mem_centralizer_iff.mp hx) y hy).symm) (h.N_le_centralizer_P₁ hn))

theorem ncard_orbit_le (h : Hyp fr) (p12 : JankoProp12 fr) {x : G} (hx : x ∈ fr.I) :
    {y | ∃ u ∈ fr.U, u * x * u⁻¹ = y}.ncard ≤ 9 := by
  have hsub : {y | ∃ u ∈ fr.U, u * x * u⁻¹ = y} ⊆ (fun s => s * x) '' (fr.S : Set G) := by
    rintro y ⟨u, hu, rfl⟩
    exact ⟨u * x * u⁻¹ * x⁻¹, comm_mem_S h p12 hx hu, by group⟩
  calc {y | ∃ u ∈ fr.U, u * x * u⁻¹ = y}.ncard
      ≤ ((fun s => s * x) '' (fr.S : Set G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (fr.S : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 9 := by rw [← Nat.card_coe_set_eq]; exact h.card_S

theorem le_card_U_inf_centralizer (h : Hyp fr) (p12 : JankoProp12 fr) {x : G} (hx : x ∈ fr.I) :
    3 ^ 7 ≤ Nat.card (fr.U ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have h1 := card_conj_orbit_mul fr.U x
  have h2 := ncard_orbit_le h p12 hx
  rw [p12.card_U] at h1
  have : 3 ^ 9 ≤ 9 * Nat.card (fr.U ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    rw [← h1]; exact Nat.mul_le_mul_right _ h2
  omega

theorem N_inf_centralizer_eq_I (h : Hyp fr) {e : G} (he : e ∈ fr.E) (heP : e ∉ fr.P₁) :
    fr.N ⊓ centralizer ({e} : Set G) = fr.I := by
  have heM : e ∉ fr.M := fun hm => heP (E_inf_M_le h ⟨he, hm⟩)
  have hCM := h.p11.M_inf_centralizer e (h.E_le_N he) heM
  have hIle : fr.I ≤ fr.N ⊓ centralizer ({e} : Set G) := le_inf h.I_le_N fun y hy =>
    mem_centralizer_singleton_iff.mpr (h.p11.I_comm y hy e (E_le_I he))
  refine (eq_of_le_of_card_ge hIle ?_).symm
  have hX : fr.N ⊓ centralizer ({e} : Set G) ≤ normalizer (fr.M : Set G) :=
    inf_le_left.trans (N_le_normalizer_M h)
  have h1 := card_sup_mul_card_inf hX
  have hinf : fr.N ⊓ centralizer ({e} : Set G) ⊓ fr.M = fr.ZN := by
    rw [← hCM, inf_comm, ← inf_assoc, inf_eq_left.mpr h.M_le_N]
  rw [hinf, h.p11.card_ZN, h.p10.card_M] at h1
  have h2 : Nat.card (fr.N ⊓ centralizer ({e} : Set G) ⊔ fr.M : Subgroup G) ≤ 3 ^ 7 := by
    rw [← h.p11.card_N]
    exact card_le_of_le (sup_le inf_le_left h.M_le_N)
  rw [h.p11.card_I]
  nlinarith

theorem card_U_inf_centralizer_E (h : Hyp fr) (p12 : JankoProp12 fr) {e : G} (he : e ∈ fr.E)
    (he1 : e ≠ 1) : Nat.card (fr.U ⊓ centralizer ({e} : Set G) : Subgroup G) = 3 ^ 7 := by
  refine le_antisymm ?_ (le_card_U_inf_centralizer h p12 (E_le_I he))
  by_cases heP : e ∈ fr.P₁
  · have heZ : e ∈ fr.ZN := by rw [h.p11.ZN_eq]; exact (le_sup_left : fr.P₁ ≤ _) heP
    have heS : e ∉ fr.S := fun hs => he1 (h.eq_one_of_mem_P₁_of_mem_Mbar heP (h.S_le_Mbar hs))
    rw [p12.U_inf_centralizer_ZN e heZ heS, h.p11.card_N]
  · have hY : fr.U ⊓ centralizer ({e} : Set G) ≤ normalizer (fr.N : Set G) :=
      inf_le_left.trans h.U_le_V
    have h1 := card_sup_mul_card_inf hY
    have hinf : fr.U ⊓ centralizer ({e} : Set G) ⊓ fr.N = fr.I := by
      rw [← N_inf_centralizer_eq_I h he heP, inf_comm, ← inf_assoc, inf_eq_left.mpr h.N_le_U]
    rw [hinf, h.p11.card_I, h.p11.card_N] at h1
    have h2 : Nat.card (fr.U ⊓ centralizer ({e} : Set G) ⊔ fr.N : Subgroup G) ≤ 3 ^ 9 := by
      rw [← p12.card_U]
      exact card_le_of_le (sup_le inf_le_left h.N_le_U)
    nlinarith

theorem exists_conj_eq_mul (h : Hyp fr) (p12 : JankoProp12 fr) {e s : G} (he : e ∈ fr.E)
    (he1 : e ≠ 1) (hs : s ∈ fr.S) : ∃ u ∈ fr.U, u * e * u⁻¹ = e * s := by
  have hsub : {y | ∃ u ∈ fr.U, u * e * u⁻¹ = y} ⊆ (fun s => s * e) '' (fr.S : Set G) := by
    rintro y ⟨u, hu, rfl⟩
    exact ⟨u * e * u⁻¹ * e⁻¹, comm_mem_S h p12 (E_le_I he) hu, by group⟩
  have h1 := card_conj_orbit_mul fr.U e
  rw [card_U_inf_centralizer_E h p12 he he1, p12.card_U] at h1
  have hcard : ((fun s => s * e) '' (fr.S : Set G)).ncard ≤
      {y | ∃ u ∈ fr.U, u * e * u⁻¹ = y}.ncard := by
    calc ((fun s => s * e) '' (fr.S : Set G)).ncard ≤ (fr.S : Set G).ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ = 9 := by rw [← Nat.card_coe_set_eq]; exact h.card_S
      _ = _ := by omega
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hmem : e * s ∈ (fun s => s * e) '' (fr.S : Set G) :=
    ⟨e * s * e⁻¹, (mem_normalizer_iff.mp (h.E_le_normalizer_S he) s).mp hs, by group⟩
  rw [← heq] at hmem
  exact hmem

theorem exists_conj_mem_E (h : Hyp fr) (p12 : JankoProp12 fr) {x : G} (hx : x ∈ fr.I)
    (hxS : x ∉ fr.S) : ∃ e ∈ fr.E, e ≠ 1 ∧ e⁻¹ * x ∈ fr.S ∧ ∃ u ∈ fr.U, u * x * u⁻¹ = e := by
  rw [h.I_eq_E_sup_S] at hx
  obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup h.E_le_normalizer_S hx
  have he1 : e ≠ 1 := by rintro rfl; exact hxS (by simpa using hs)
  obtain ⟨u, hu, hue⟩ := exists_conj_eq_mul h p12 he he1 hs
  refine ⟨e, he, he1, by simpa using hs, u⁻¹, inv_mem hu, ?_⟩
  rw [← hue]
  group

omit [Finite G] in
theorem ne_one_of_card_centralizer (fr : JankoFrame G z) {x : G}
    (hx : Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162) :
    x ≠ 1 := by
  rintro rfl
  have htop : centralizer ({(1 : G)} : Set G) = ⊤ := by
    ext g; simp [mem_centralizer_singleton_iff]
  rw [htop, top_inf_eq] at hx
  have := card_dvd_of_le fr.K_le
  rw [hx, fr.card_K] at this
  norm_num at this

theorem card_type_s₃_I (h : Hyp fr) (p12 : JankoProp12 fr) :
    Nat.card {x : G // x ∈ fr.I ∧ x ∉ fr.S ∧ IsConj x fr.s₃} = 72 := by
  have htype : ∀ e ∈ fr.E, (IsConj e fr.s₃ ↔ Nat.card (centralizer ({e} : Set G) ⊓
      centralizer ({z} : Set G) : Subgroup G) = 162) := fun e he =>
    h.p7.isConj_s₃_iff z h.set.orderOf_z e (fr.E_le he) (fr.E_pow_three e he)
  have hmk : ∀ e ∈ fr.E, Nat.card (centralizer ({e} : Set G) ⊓ centralizer ({z} : Set G) :
      Subgroup G) = 162 → ∀ s ∈ fr.S, e * s ∈ fr.I ∧ e * s ∉ fr.S ∧ IsConj (e * s) fr.s₃ := by
    intro e he h162 s hs
    have he1 := ne_one_of_card_centralizer fr h162
    refine ⟨mul_mem (E_le_I he) (S_le_I h hs), fun hes => he1 ?_, ?_⟩
    · have hmem : e ∈ fr.E ⊓ fr.S := ⟨he, by simpa using fr.S.mul_mem hes (fr.S.inv_mem hs)⟩
      rwa [E_inf_S h, mem_bot] at hmem
    · obtain ⟨u, hu, hue⟩ := exists_conj_eq_mul h p12 he he1 hs
      exact (isConj_iff.mpr ⟨u, hue⟩).symm.trans ((htype e he).mpr h162)
  let f : {e : G // e ∈ fr.E ∧ Nat.card (centralizer ({e} : Set G) ⊓ centralizer ({z} : Set G) :
      Subgroup G) = 162} × fr.S → {x : G // x ∈ fr.I ∧ x ∉ fr.S ∧ IsConj x fr.s₃} :=
    fun p => ⟨p.1.1 * p.2.1, hmk p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨e, he⟩, ⟨s, hs⟩⟩ ⟨⟨e', he'⟩, ⟨s', hs'⟩⟩ heq
    have hval : e * s = e' * s' := congrArg Subtype.val heq
    have hes : e'⁻¹ * e = s' * s⁻¹ := by
      calc e'⁻¹ * e = e'⁻¹ * (e * s) * s⁻¹ := by group
        _ = e'⁻¹ * (e' * s') * s⁻¹ := by rw [hval]
        _ = s' * s⁻¹ := by group
    have hmem : e'⁻¹ * e ∈ fr.E ⊓ fr.S :=
      mem_inf.mpr ⟨fr.E.mul_mem (fr.E.inv_mem he'.1) he.1, hes ▸ fr.S.mul_mem hs' (fr.S.inv_mem hs)⟩
    rw [E_inf_S h, mem_bot, inv_mul_eq_one] at hmem
    subst hmem
    obtain rfl : s = s' := mul_left_cancel hval
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hxI, hxS, hxc⟩
    rw [h.I_eq_E_sup_S] at hxI
    obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup h.E_le_normalizer_S hxI
    have he1 : e ≠ 1 := by rintro rfl; exact hxS (by simpa using hs)
    obtain ⟨u, hu, hue⟩ := exists_conj_eq_mul h p12 he he1 hs
    have hec : IsConj e fr.s₃ := (isConj_iff.mpr ⟨u, hue⟩).trans hxc
    exact ⟨(⟨e, he, (htype e he).mp hec⟩, ⟨s, hs⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, fr.card_type_s₃_E,
    h.card_S]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
