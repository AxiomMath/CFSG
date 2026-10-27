module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51EndGame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification.AschbacherTightEmbedding

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem prod_no_conj (cfg : L3E8Cfg K z J zJ H Q E S) (hU : UniqueCosetZ K z)
    (hC : L3E8CentLe K z) {a : T} (ha : a ∈ L3E8ProdP K z) {g : T} (hg : g ∉ sigmaNorm K)
    (hb : g⁻¹ * a * g ∈ S) : False := by
  have hz := cfg.datum.unique
  obtain ⟨hEab, hE8⟩ := cfg.E8
  have hzE : z ∈ E := cfg.z_mem_E
  have hzHt : z ∈ firstFactor K := cfg.Q_le_ht (cfg.E_le_Q hzE)
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have h1Q : conjSub (1 : T) Q = Q := conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hzO : z ∉ oddCoreOf (sigmaGen K) := not_mem_oddCoreOf_of_sq _ hz.sq hz.ne_one
  have hp2 : ∀ u : T, u * u = 1 → IsPGroup 2 (Subgroup.zpowers u) := by
    intro u hu2
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hEab.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← pow_two]; exact hEab.2 x hx
  have hCa : Subgroup.centralizer ({a} : Set T) ≤ sigmaNorm K := hC a ha
  obtain ⟨h, hne, hc, hnot, ha_eq⟩ := ha
  have hcz : h⁻¹ * z * h ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc.symm
  have hhM : h ∈ sigmaNorm K := cfg.zconj_cent hcz
  have ha2 : a * a = 1 := by
    rw [ha_eq, ← pow_two, ← (cfg.prod_basic hne hc).2]
    exact pow_orderOf_eq_one _
  obtain ⟨b, hb_def⟩ : ∃ b, b = g⁻¹ * a * g := ⟨_, rfl⟩
  rw [← hb_def] at hb
  have hab : a = g * b * g⁻¹ := by rw [hb_def]; group
  have hb2 : b * b = 1 := by
    rw [hb_def]
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hbM : b ∈ sigmaNorm K := cfg.hS.1 hb
  have hgM : g⁻¹ ∉ sigmaNorm K := fun h' => hg (by simpa using (sigmaNorm K).inv_mem h')
  have hbN : b ∉ Subgroup.normalizer (firstFactor K : Set T) := by
    intro hbN
    have hbQ := cfg.normalizer_ht_le hbN
    refine cfg.clash hU hCa (hp2 a ha2) hgM ?_
    rw [Subgroup.mem_normalizer_iff] at hbQ ⊢
    intro w
    have := hbQ (g⁻¹ * w * g⁻¹⁻¹)
    simp only [SetLike.mem_coe, mem_rightConjugate_iff] at this ⊢
    rw [show g⁻¹ * (a * w * a⁻¹) * g⁻¹⁻¹ = b * (g⁻¹ * w * g⁻¹⁻¹) * b⁻¹ by rw [hab]; group]
    exact this
  have hA := fun e (he : e ∈ E) => cfg.wreath_diag hb hb2 hbN he
  have hcommb : ∀ e ∈ E, ∀ f ∈ E, (b⁻¹ * e * b) * f = f * (b⁻¹ * e * b) := by
    intro e he f hf
    have h3 := (hA e he).2.2 f hf
    have : e * ((b⁻¹ * e * b) * f) = e * (f * (b⁻¹ * e * b)) := by
      calc e * ((b⁻¹ * e * b) * f) = e * (b⁻¹ * e * b) * f := by group
        _ = f * (e * (b⁻¹ * e * b)) := h3
        _ = (f * e) * (b⁻¹ * e * b) := by group
        _ = (e * f) * (b⁻¹ * e * b) := by rw [hEcomm f hf e he]
        _ = e * (f * (b⁻¹ * e * b)) := by group
    exact mul_left_cancel this
  have hAsq : ∀ e ∈ E, e * (b⁻¹ * e * b) * (e * (b⁻¹ * e * b)) = 1 := by
    intro e he
    calc e * (b⁻¹ * e * b) * (e * (b⁻¹ * e * b)) = e * ((b⁻¹ * e * b) * e) * (b⁻¹ * e * b) := by
          group
      _ = e * (e * (b⁻¹ * e * b)) * (b⁻¹ * e * b) := by rw [hcommb e he e he]
      _ = (e * e) * (b⁻¹ * (e * e) * b) := by group
      _ = 1 := by rw [hEsq e he]; group
  have hAmul : ∀ e ∈ E, ∀ f ∈ E,
      e * f * (b⁻¹ * (e * f) * b) = e * (b⁻¹ * e * b) * (f * (b⁻¹ * f * b)) := by
    intro e he f hf
    calc e * f * (b⁻¹ * (e * f) * b) = e * (f * (b⁻¹ * e * b)) * (b⁻¹ * f * b) := by group
      _ = e * ((b⁻¹ * e * b) * f) * (b⁻¹ * f * b) := by rw [← hcommb e he f hf]
      _ = e * (b⁻¹ * e * b) * (f * (b⁻¹ * f * b)) := by group
  have hne_f : conjSub (1 : T) (firstFactor K) ≠ conjSub h⁻¹ (firstFactor K) := by
    intro h'
    apply hnot
    have hz'' : h⁻¹ * z * h ∈ conjSub h⁻¹ (firstFactor K) := by
      have := conj_mem_conjSub (n := h⁻¹) hzHt
      simpa using this
    rw [← h', h1Ht] at hz''
    exact hz''
  have hx₁ : z ∈ conjSub (1 : T) (firstFactor K) := by rw [h1Ht]; exact hzHt
  have hx₂ : h⁻¹ * z * h ∈ conjSub h⁻¹ (firstFactor K) := by
    have := conj_mem_conjSub (n := h⁻¹) hzHt
    simpa using this
  have key : ∀ e ∈ E,
      conjSub (g * (e * (b⁻¹ * e * b)) * g⁻¹) (firstFactor K) = firstFactor K ∨
        conjSub (g * (e * (b⁻¹ * e * b)) * g⁻¹) (firstFactor K) = conjSub h⁻¹ (firstFactor K) := by
    intro e he
    have h2 := (hA e he).2.1
    have hpc : g * (e * (b⁻¹ * e * b)) * g⁻¹ * (z * (h⁻¹ * z * h)) =
        z * (h⁻¹ * z * h) * (g * (e * (b⁻¹ * e * b)) * g⁻¹) := by
      rw [← ha_eq, hab]
      calc g * (e * (b⁻¹ * e * b)) * g⁻¹ * (g * b * g⁻¹) =
          g * (e * (b⁻¹ * e * b) * b) * g⁻¹ := by group
        _ = g * (b * (e * (b⁻¹ * e * b))) * g⁻¹ := by rw [h2]
        _ = g * b * g⁻¹ * (g * (e * (b⁻¹ * e * b)) * g⁻¹) := by group
    have hpM : g * (e * (b⁻¹ * e * b)) * g⁻¹ ∈ sigmaNorm K := by
      apply hCa
      rw [Subgroup.mem_centralizer_singleton_iff, ha_eq]
      exact hpc
    have := cfg.two_factor_support (Subgroup.one_mem _) ((sigmaNorm K).inv_mem hhM) hne_f hx₁ hx₂
      hzO hpM hpc
    rwa [h1Ht] at this
  have hconj_one : ∀ e ∈ E, conjSub (g * (e * (b⁻¹ * e * b)) * g⁻¹)
      (conjSub (g * (e * (b⁻¹ * e * b)) * g⁻¹) (firstFactor K)) = firstFactor K := by
    intro e he
    rw [← conjSub_mul,
      show g * (e * (b⁻¹ * e * b)) * g⁻¹ * (g * (e * (b⁻¹ * e * b)) * g⁻¹) =
        g * (e * (b⁻¹ * e * b) * (e * (b⁻¹ * e * b))) * g⁻¹ by group,
      hAsq e he, show g * 1 * g⁻¹ = (1 : T) by group, h1Ht]
  obtain ⟨e, he, he1, heN⟩ : ∃ e ∈ E, e ≠ 1 ∧
      conjSub (g * (e * (b⁻¹ * e * b)) * g⁻¹) (firstFactor K) = firstFactor K := by
    rcases key z hzE with h1 | h1
    · exact ⟨z, hzE, hz.ne_one, h1⟩
    obtain ⟨f, hf, hf1, hfz⟩ : ∃ f ∈ E, f ≠ 1 ∧ f ≠ z := by
      by_contra hcon
      push Not at hcon
      haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE8]; norm_num)
      have hsurj : Function.Surjective (![1, ⟨z, hzE⟩] : Fin 2 → E) := by
        intro f
        by_cases hf1 : (f : T) = 1
        · exact ⟨0, Subtype.ext (by simpa using hf1.symm)⟩
        · exact ⟨1, Subtype.ext (by simpa using (hcon f f.2 hf1).symm)⟩
      have := Nat.card_le_card_of_surjective _ hsurj
      rw [hE8] at this
      simp at this
    rcases key f hf with h2 | h2
    · exact ⟨f, hf, hf1, h2⟩
    refine ⟨z * f, E.mul_mem hzE hf, ?_, ?_⟩
    · intro h0
      apply hfz
      have : f = z⁻¹ := eq_inv_of_mul_eq_one_right h0
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz.sq
    · rw [hAmul z hzE f hf,
        show g * (z * (b⁻¹ * z * b) * (f * (b⁻¹ * f * b))) * g⁻¹ =
          g * (z * (b⁻¹ * z * b)) * g⁻¹ * (g * (f * (b⁻¹ * f * b)) * g⁻¹) by group,
        conjSub_mul, h2, ← h1]
      exact hconj_one z hzE
  have hneb : conjSub (1 : T) (firstFactor K) ≠ conjSub b⁻¹ (firstFactor K) := by
    intro h'
    apply hbN
    have h1 : conjSub b⁻¹ (firstFactor K) = firstFactor K := h'.symm.trans h1Ht
    have := mem_normalizer_iff_conjSub_eq.mpr h1
    simpa using (Subgroup.normalizer _).inv_mem this
  have heQ : e ∈ conjSub (1 : T) Q := by rw [h1Q]; exact cfg.E_le_Q he
  have hebQ : b⁻¹ * e * b ∈ conjSub b⁻¹ Q := by
    have := conj_mem_conjSub (n := b⁻¹) (cfg.E_le_Q he)
    simpa using this
  have heb2 : (b⁻¹ * e * b) * (b⁻¹ * e * b) = 1 := by
    calc (b⁻¹ * e * b) * (b⁻¹ * e * b) = b⁻¹ * (e * e) * b := by group
      _ = 1 := by rw [hEsq e he]; group
  have heb1 : b⁻¹ * e * b ≠ 1 := fun h' => he1 (by
    have := congrArg (fun w => b * w * b⁻¹) h'
    simpa [mul_assoc] using this)
  have hPM := cfg.prod_mem_P (Subgroup.one_mem _) ((sigmaNorm K).inv_mem hbM) hneb heQ hebQ
    (hEsq e he) he1 heb2 heb1 (hcommb e he e he).symm
  have hCp := cent_le_of_mem_prodPM hC hPM
  have hpN : e * (b⁻¹ * e * b) ∈ Subgroup.normalizer (rightConjugate Q g : Set T) := by
    apply cfg.normalizer_rightConjugate_ht_le g
    have hgN : g * (e * (b⁻¹ * e * b)) * g⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) :=
      mem_normalizer_iff_conjSub_eq.mpr heN
    rw [Subgroup.mem_normalizer_iff] at hgN ⊢
    intro w
    have := hgN (g * w * g⁻¹)
    simp only [SetLike.mem_coe, mem_rightConjugate_iff] at this ⊢
    rw [show g * (e * (b⁻¹ * e * b)) * g⁻¹ * (g * w * g⁻¹) * (g * (e * (b⁻¹ * e * b)) * g⁻¹)⁻¹ =
        g * (e * (b⁻¹ * e * b) * w * (e * (b⁻¹ * e * b))⁻¹) * g⁻¹ by group] at this
    exact this
  exact cfg.clash hU hCp (hp2 _ (hAsq e he)) hg hpN

theorem prod_unique (cfg : L3E8Cfg K z J zJ H Q E S) (hU : UniqueCosetZ K z)
    (hC : L3E8CentLe K z) {h : T} (hne : h⁻¹ * z * h ≠ z)
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    ∃! c : T ⧸ sigmaNorm K, (z * (h⁻¹ * z * h)) • c = c := by
  obtain ⟨haM, ha2⟩ := cfg.prod_basic hne hc
  by_cases hmem : h⁻¹ * z * h ∈ firstFactor K
  · obtain ⟨l, hl, hla⟩ := cfg.prod_mem hmem hne hc
    refine fixesUnique_of_only_base haM fun x hx => ?_
    have h1 : (l * x)⁻¹ * z * (l * x) ∈ sigmaNorm K := by
      have e : (l * x)⁻¹ * z * (l * x) = x⁻¹ * (l⁻¹ * z * l) * x := by group
      rw [e, hla]
      exact hx
    have h2 := hU _ h1
    simpa using (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl)) h2
  · have ha : z * (h⁻¹ * z * h) ∈ L3E8ProdP K z := ⟨h, hne, hc, hmem, rfl⟩
    refine fixesUnique_of_only_base haM fun x hx => ?_
    exact cfg.unique_of_S ha2 (fun g hg hb => cfg.prod_no_conj hU hC ha hg hb) hx

end L3E8Cfg

theorem l3e8_endgame {T : Type} [Group T] [Finite T]
    [CaseIAmbient T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T} {H Q E S : Subgroup T}
    (h39 : Lemma39FStar) (cfg : L3E8Cfg K z J zJ H Q E S) (hC : L3E8CentLe K z) : False := by
  have hU := cfg.unique_coset
  exact cfg.toFrameCfg.endgame_fstar h39 hU fun h hne hc => cfg.prod_unique hU hC hne hc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
