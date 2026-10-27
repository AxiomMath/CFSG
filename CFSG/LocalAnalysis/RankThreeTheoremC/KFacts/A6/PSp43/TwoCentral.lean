module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.Local

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

theorem pCoreOf_map_of_injective' {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) (p : ℕ) (X : Subgroup G) :
    CFSG.Open.pCoreOf p (X.map f) = (CFSG.Open.pCoreOf p X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have hcore : (CFSG.pCore p X).map e.toMonoidHom = CFSG.pCore p ↥(X.map f) :=
    CFSG.pCore_map_iso p e
  have hh : (X.map f).subtype.comp e.toMonoidHom = f.comp X.subtype :=
    MonoidHom.ext fun x => rfl
  unfold CFSG.Open.pCoreOf
  rw [← hcore, Subgroup.map_map, Subgroup.map_map, hh]

theorem eq_one_or_tau_of_rep_mem {g : Equiv.Perm (Fin 45)} {t : Tab} (hr : Rep g t)
    (h : [tid, tau0Tab].contains t = true) : g = 1 ∨ g = tauPerm 0 := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact Or.inl (rep_unique hr rep_one)
  · exact Or.inr (rep_unique hr (rep_tauPerm 0))

theorem eq_of_comm_gens {ws : List (List (Fin 45))} {elems : List Tab} {par : List (ℕ × ℕ)}
    {act : List (List ℕ)} (h : enumOK (ws.map wtab) elems par act = true)
    (hc : centerB (ws.map wtab) elems [tid, tau0Tab] = true) {g : Equiv.Perm (Fin 45)}
    (hg : g ∈ gen (ws.map wperm)) (hcomm : ∀ w ∈ ws, g * wperm w = wperm w * g) :
    g = 1 ∨ g = tauPerm 0 := by
  obtain ⟨t, ht, hr⟩ := exists_mem_tab h hg
  have h1 := List.all_eq_true.1 hc t ht
  have h2 : ((ws.map wtab).all fun s => tmul t s == tmul s t) = true := by
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hs
    rw [beq_iff_eq]
    exact rep_eq_tab (rep_mul hr (rep_wperm w)) (hcomm w hw ▸ rep_mul (rep_wperm w) hr)
  rw [h2, Bool.not_true, Bool.false_or] at h1
  exact eq_one_or_tau_of_rep_mem hr h1

theorem eq_of_mem_center_E {g : Equiv.Perm (Fin 45)} (hg : g ∈ E)
    (hcomm : ∀ h ∈ E, g * h = h * g) : g = 1 ∨ g = tauPerm 0 :=
  eq_of_comm_gens E_enumOK E_center hg fun w hw => hcomm _ (wperm_mem_gen hw)

theorem eq_of_mem_center_S0 {g : Equiv.Perm (Fin 45)} (hg : g ∈ S0)
    (hcomm : ∀ h ∈ S0, g * h = h * g) : g = 1 ∨ g = tauPerm 0 :=
  eq_of_comm_gens S0_enumOK S0_center hg fun w hw => hcomm _ (wperm_mem_gen hw)

theorem exists_noncomm_of_mem_E {a : Equiv.Perm (Fin 45)} (ha : a ∈ E) (ha1 : a ≠ 1)
    (ha0 : a ≠ tauPerm 0) :
    ∃ b ∈ E, ∃ c ∈ E, a * b = b * a ∧ a * c = c * a ∧ b * c ≠ c * b := by
  obtain ⟨i, hi, hr⟩ := (mem_gen_words E_enumOK a).1 ha
  have h1 := List.all_eq_true.1 E_wit i (List.mem_range.2 hi)
  have hz : [tid, tau0Tab].contains (Eelems.getD i []) = false := by
    by_contra hz
    rcases eq_one_or_tau_of_rep_mem hr (Bool.not_eq_false _ ▸ hz) with h | h
    · exact ha1 h
    · exact ha0 h
  rw [hz, Bool.false_or] at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
  obtain ⟨⟨⟨⟨hb, hc⟩, hab⟩, hac⟩, hbc⟩ := h1
  obtain ⟨b, hbE, hbr⟩ := exists_mem_rep_of_enumOK (length_words Egens) (rep_words Egens)
    E_enumOK _ hb
  obtain ⟨c, hcE, hcr⟩ := exists_mem_rep_of_enumOK (length_words Egens) (rep_words Egens)
    E_enumOK _ hc
  refine ⟨b, hbE, c, hcE, ?_, ?_, ?_⟩
  · exact rep_unique (rep_mul hr hbr)
      ((beq_iff_eq.1 hab).symm ▸ rep_mul hbr hr :)
  · exact rep_unique (rep_mul hr hcr)
      ((beq_iff_eq.1 hac).symm ▸ rep_mul hcr hr :)
  · intro hbc'
    have := rep_eq_tab (rep_mul hbr hcr) (hbc' ▸ rep_mul hcr hbr)
    unfold commB at hbc
    rw [this, beq_self_eq_true] at hbc
    exact Bool.noConfusion hbc

theorem card_le_eight_of_isMulCommutative {A : Subgroup (Equiv.Perm (Fin 45))} (hAE : A ≤ E)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 8 := by
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card A ∣ 32 := card_E ▸ Subgroup.card_dvd_of_le hAE
  obtain ⟨a, haA, ha1, ha0⟩ : ∃ a ∈ A, a ≠ 1 ∧ a ≠ tauPerm 0 := by
    by_contra hno
    push Not at hno
    have hsub : (A : Set (Equiv.Perm (Fin 45))) ⊆ {1, tauPerm 0} := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hno x hx hx1)
    have h2 : Nat.card A ≤ 2 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have e : Nat.card A = (A : Set (Equiv.Perm (Fin 45))).ncard := Nat.card_coe_set_eq _
      rw [e]
      exact this.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    omega
  set C := E ⊓ centralizer ({a} : Set (Equiv.Perm (Fin 45)))
  have hAC : A ≤ C := fun x hx =>
    ⟨hAE hx, mem_centralizer_singleton_iff.2 (hA a haA x hx).symm⟩
  obtain ⟨g, hgE, hga⟩ : ∃ g ∈ E, a * g ≠ g * a := by
    by_contra hno
    push Not at hno
    rcases eq_of_mem_center_E (hAE haA) hno with h | h
    · exact ha1 h
    · exact ha0 h
  have hgC : g ∉ C := fun hgC => hga (mem_centralizer_singleton_iff.1 hgC.2).symm
  have hCE : C ≤ E := inf_le_left
  have hCdvd : Nat.card C ∣ 32 := card_E ▸ Subgroup.card_dvd_of_le hCE
  have hCne : Nat.card C ≠ 32 := by
    intro h32
    have : C = E := Subgroup.eq_of_le_of_card_ge hCE (by rw [card_E, h32])
    exact hgC (this ▸ hgE)
  have hC16 : Nat.card C ≤ 16 := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    have : Nat.card C ∈ Nat.divisors 32 := Nat.mem_divisors.2 ⟨hCdvd, by norm_num⟩
    have hd : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hAC' : A = C := Subgroup.eq_of_le_of_card_ge hAC (by
    have hAcard : 16 ≤ Nat.card A := by
      have : Nat.card A ∈ Nat.divisors 32 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    omega)
  obtain ⟨b, hbE, c, hcE, hab, hac, hbc⟩ := exists_noncomm_of_mem_E (hAE haA) ha1 ha0
  have hbA : b ∈ A := hAC' ▸ ⟨hbE, mem_centralizer_singleton_iff.2 hab.symm⟩
  have hcA : c ∈ A := hAC' ▸ ⟨hcE, mem_centralizer_singleton_iff.2 hac.symm⟩
  exact hbc (hA b hbA c hcA)

theorem S0_le_P : S0 ≤ P := gen_words_le_P S0gens

theorem card_S0_eq_P : Nat.card S0 = 2 ^ (Nat.card P).factorization 2 := by
  rw [card_S0, card_P, factorization_two_25920]
  norm_num

theorem exists_conj_eq_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H S T : Subgroup G} (hSH : S ≤ H) (hTH : T ≤ H)
    (hS : Nat.card S = p ^ (Nat.card H).factorization p)
    (hT : Nat.card T = p ^ (Nat.card H).factorization p) :
    ∃ g ∈ H, T = S.map (MulAut.conj g).toMonoidHom := by
  let S' : Sylow p H := Sylow.ofCard (S.subgroupOf H) (by rw [card_subgroupOf_of_le hSH, hS])
  let T' : Sylow p H := Sylow.ofCard (T.subgroupOf H) (by rw [card_subgroupOf_of_le hTH, hT])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S' T'
  have key : ∀ y : H, y ∈ (T' : Subgroup H) ↔ g⁻¹ * y * g ∈ (S' : Subgroup H) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have h1 := (key ⟨x, hTH hx⟩).1 (by
      show (⟨x, hTH hx⟩ : H) ∈ T.subgroupOf H
      exact mem_subgroupOf.2 hx)
    have h2 : ((g : G))⁻¹ * x * g ∈ S := by
      have h3 : g⁻¹ * ⟨x, hTH hx⟩ * g ∈ S.subgroupOf H := h1
      exact mem_subgroupOf.1 h3
    refine ⟨_, h2, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨s, hs, rfl⟩
    have hsH := hSH hs
    have h1 : g⁻¹ * (g * ⟨s, hsH⟩ * g⁻¹) * g ∈ (S' : Subgroup H) := by
      have : g⁻¹ * (g * ⟨s, hsH⟩ * g⁻¹) * g = ⟨s, hsH⟩ := by group
      rw [this]
      show (⟨s, hsH⟩ : H) ∈ S.subgroupOf H
      exact mem_subgroupOf.2 hs
    have h2 := (key _).2 h1
    have h3 : g * ⟨s, hsH⟩ * g⁻¹ ∈ T.subgroupOf H := h2
    have h4 := mem_subgroupOf.1 h3
    simpa [MulAut.conj_apply] using h4

theorem exists_conj_tau_zero {z : Equiv.Perm (Fin 45)} (hzP : z ∈ P) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hcard : Nat.card ↥(P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))) = 576) :
    ∃ g ∈ P, z = g * tauPerm 0 * g⁻¹ := by
  set C := P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45))) with hC
  have hzC : z ∈ C := ⟨hzP, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨S'⟩ : Nonempty (Sylow 2 C) := inferInstance
  set S := (S'.toSubgroup).map C.subtype with hSdef
  have hSC : S ≤ C := Subgroup.map_subtype_le _
  have hScard : Nat.card S = 2 ^ (Nat.card P).factorization 2 := by
    rw [hSdef, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
      hcard, card_P, factorization_two_576, factorization_two_25920]
  obtain ⟨g, hgP, hg⟩ := exists_conj_eq_of_card S0_le_P (hSC.trans inf_le_left) card_S0_eq_P
    hScard
  have hzS : z ∈ S := by
    have hnor : (zpowers (⟨z, hzC⟩ : C)).Normal := by
      constructor
      intro n hn c
      have hc : (c : Equiv.Perm (Fin 45)) * z = z * c :=
        mem_centralizer_singleton_iff.1 c.2.2
      have hcz : c * ⟨z, hzC⟩ * c⁻¹ = ⟨z, hzC⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hc, mul_inv_cancel_right]
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hcz]
      exact zpow_mem_zpowers _ k
    have hord : orderOf (⟨z, hzC⟩ : C) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hz2 hz1
    have hp : IsPGroup 2 (zpowers (⟨z, hzC⟩ : C)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have := hp.le_sylow_of_normal S' (mem_zpowers _)
    exact ⟨⟨z, hzC⟩, this, rfl⟩
  have hzcomm : ∀ s ∈ S, z * s = s * z := fun s hs =>
    (mem_centralizer_singleton_iff.1 (hSC hs).2).symm
  rw [hg] at hzS
  obtain ⟨y, hyS0, hyz⟩ := hzS
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyz
  have hycomm : ∀ s ∈ S0, y * s = s * y := by
    intro s hs
    have h1 := hzcomm (g * s * g⁻¹) (hg ▸ ⟨s, hs, rfl⟩)
    rw [← hyz] at h1
    have h2 : g * (y * s) * g⁻¹ = g * (s * y) * g⁻¹ := by
      calc g * (y * s) * g⁻¹ = g * y * g⁻¹ * (g * s * g⁻¹) := by group
        _ = g * s * g⁻¹ * (g * y * g⁻¹) := h1
        _ = g * (s * y) * g⁻¹ := by group
    simpa using h2
  rcases eq_of_mem_center_S0 hyS0 hycomm with h | h
  · exact absurd (by rw [← hyz, h]; group) hz1
  · exact ⟨g, hgP, by rw [← hyz, h]⟩

theorem P_inf_centralizer_conj {g : Equiv.Perm (Fin 45)} (hg : g ∈ P) (k : Equiv.Perm (Fin 45)) :
    P ⊓ centralizer ({g * k * g⁻¹} : Set (Equiv.Perm (Fin 45))) =
      (P ⊓ centralizer ({k} : Set (Equiv.Perm (Fin 45)))).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hxP, hx⟩
    refine ⟨g⁻¹ * x * g, ⟨mul_mem (mul_mem (inv_mem hg) hxP) hg, ?_⟩, by group⟩
    calc g⁻¹ * x * g * k = g⁻¹ * (x * (g * k * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * k * g⁻¹ * x) * g := by rw [hx]
      _ = k * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hyP, hy⟩, rfl⟩
    refine ⟨mul_mem (mul_mem hg hyP) (inv_mem hg), ?_⟩
    calc g * y * g⁻¹ * (g * k * g⁻¹) = g * (y * k) * g⁻¹ := by group
      _ = g * (k * y) * g⁻¹ := by rw [hy]
      _ = g * k * g⁻¹ * (g * y * g⁻¹) := by group

theorem card_le_eight_of_le_pCoreOf {z : Equiv.Perm (Fin 45)} (hzP : z ∈ P) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hcard : Nat.card ↥(P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))) = 576)
    {A : Subgroup (Equiv.Perm (Fin 45))} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAle : A ≤ CFSG.Open.pCoreOf 2 (P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45))))) :
    Nat.card A ≤ 8 := by
  obtain ⟨g, hgP, rfl⟩ := exists_conj_tau_zero hzP hz2 hz1 hcard
  rw [P_inf_centralizer_conj hgP, pCoreOf_map_of_injective' (MulAut.conj g).injective,
    pCoreOf_H0] at hAle
  set B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hBE : B ≤ E := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨e, he, rfl⟩ := hAle ha
    simpa [MulAut.conj_apply, mul_assoc] using he
  have hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hA a ha b hb]
  have := card_le_eight_of_isMulCommutative hBE hB
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
