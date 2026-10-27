module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Fac
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43EndGame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification.AschbacherTightEmbedding

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem wreath_diag (cfg : L3E8Cfg K z J zJ H Q E S) {s : T} (hs : s ∈ S) (hs2 : s * s = 1)
    (hsN : s ∉ Subgroup.normalizer (firstFactor K : Set T)) {e : T} (he : e ∈ E) :
    e⁻¹ * s * e = s * (e * (s⁻¹ * e * s)) ∧
      e * (s⁻¹ * e * s) * s = s * (e * (s⁻¹ * e * s)) ∧
      ∀ f ∈ E, e * (s⁻¹ * e * s) * f = f * (e * (s⁻¹ * e * s)) := by
  obtain ⟨hEab, -⟩ := cfg.E8
  have hsM : s ∈ sigmaNorm K := cfg.hS.1 hs
  have hS2 : IsPGroup 2 S := cfg.hS.2.1
  have hEHt : E ≤ firstFactor K := cfg.E_le_Q.trans cfg.Q_le_ht
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have := hEab.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  have he2 : e * e = 1 := by rw [← pow_two]; exact hEab.2 e he
  have he1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hne : conjSub (1 : T) (firstFactor K) ≠ conjSub s⁻¹ (firstFactor K) := by
    intro h
    apply hsN
    have h1 : conjSub s⁻¹ (firstFactor K) = firstFactor K := h.symm.trans h1Ht
    have := mem_normalizer_iff_conjSub_eq.mpr h1
    simpa using (Subgroup.normalizer _).inv_mem this
  have key : ∀ f ∈ E, f * (s⁻¹ * e * s) = (s⁻¹ * e * s) * f := by
    intro f hf
    have hf1 : f ∈ conjSub (1 : T) (firstFactor K) := by rw [h1Ht]; exact hEHt hf
    have hes : s⁻¹ * e * s ∈ conjSub s⁻¹ (firstFactor K) := by
      have := conj_mem_conjSub (n := s⁻¹) (hEHt he)
      simpa using this
    have hc := cfg.factor_comm (Subgroup.one_mem _) ((sigmaNorm K).inv_mem hsM) hne hf1 hes
    have hfS := cfg.E_le_S hf
    have hesS : s⁻¹ * e * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) (cfg.E_le_S he)) hs
    have hcS : f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem hfS hesS) (S.inv_mem hfS)) (S.inv_mem hesS)
    have h1 : f * (s⁻¹ * e * s) * f⁻¹ * (s⁻¹ * e * s)⁻¹ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc
        (hS2.to_le (Subgroup.zpowers_le.mpr hcS))
    have h2 := mul_inv_eq_one.mp h1
    calc f * (s⁻¹ * e * s) = f * (s⁻¹ * e * s) * f⁻¹ * f := by group
      _ = (s⁻¹ * e * s) * f := by rw [h2]
  have hi : e⁻¹ * s * e = s * (e * (s⁻¹ * e * s)) := by
    calc e⁻¹ * s * e = s * (s⁻¹ * e * s * e) := by rw [he1]; group
      _ = s * (e * (s⁻¹ * e * s)) := by rw [← key e he]
  refine ⟨hi, ?_, ?_⟩
  · calc e * (s⁻¹ * e * s) * s = e * s⁻¹ * e * (s * s) := by group
      _ = e * s⁻¹ * e := by rw [hs2, mul_one]
      _ = e⁻¹ * s * e := by rw [hs1, he1]
      _ = s * (e * (s⁻¹ * e * s)) := hi
  · intro f hf
    calc e * (s⁻¹ * e * s) * f = e * ((s⁻¹ * e * s) * f) := by group
      _ = e * (f * (s⁻¹ * e * s)) := by rw [← key f hf]
      _ = (e * f) * (s⁻¹ * e * s) := by group
      _ = (f * e) * (s⁻¹ * e * s) := by rw [hEcomm e he f hf]
      _ = f * (e * (s⁻¹ * e * s)) := by group

theorem two_factor_support (cfg : L3E8Cfg K z J zJ H Q E S) {m₁ m₂ : T}
    (hm₁ : m₁ ∈ sigmaNorm K) (hm₂ : m₂ ∈ sigmaNorm K)
    (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K)) {x₁ x₂ : T}
    (hx₁ : x₁ ∈ conjSub m₁ (firstFactor K)) (hx₂ : x₂ ∈ conjSub m₂ (firstFactor K))
    (hx₁O : x₁ ∉ oddCoreOf (sigmaGen K)) {y : T} (hy : y ∈ sigmaNorm K)
    (hc : y * (x₁ * x₂) = x₁ * x₂ * y) :
    conjSub y (conjSub m₁ (firstFactor K)) = conjSub m₁ (firstFactor K) ∨
      conjSub y (conjSub m₁ (firstFactor K)) = conjSub m₂ (firstFactor K) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hF3 : conjSub y (conjSub m₁ (firstFactor K)) = conjSub (y * m₁) (firstFactor K) :=
    (conjSub_mul y m₁ _).symm
  have hF4 : conjSub y (conjSub m₂ (firstFactor K)) = conjSub (y * m₂) (firstFactor K) :=
    (conjSub_mul y m₂ _).symm
  have h3 : conjSub (y * m₂) (firstFactor K) ≠ conjSub (y * m₁) (firstFactor K) := by
    intro h
    apply hne
    have := congrArg (conjSub y⁻¹) h
    rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    exact this.symm
  let m : Fin 3 → T := ![m₁, m₂, y * m₂]
  have hm : ∀ i, m i ∈ sigmaNorm K := by
    intro i
    fin_cases i
    · exact hm₁
    · exact hm₂
    · exact (sigmaNorm K).mul_mem hy hm₂
  have hne' : ∀ i, conjSub (m i) (firstFactor K) ≠ conjSub (y * m₁) (firstFactor K) := by
    intro i
    fin_cases i
    · exact fun h => h1 (hF3.trans h.symm)
    · exact fun h => h2 (hF3.trans h.symm)
    · exact h3
  have hind := cfg.factor_indep m ((sigmaNorm K).mul_mem hy hm₁) hm hne'
  have hmem : y * x₁ * y⁻¹ ∈ conjSub (y * m₁) (firstFactor K) ⊓
      ⨆ i, conjSub (m i) (firstFactor K) := by
    refine ⟨?_, ?_⟩
    · rw [← hF3]
      exact conj_mem_conjSub hx₁
    · have e : y * x₁ * y⁻¹ = x₁ * x₂ * (y * x₂ * y⁻¹)⁻¹ := by
        calc y * x₁ * y⁻¹ = (y * (x₁ * x₂)) * y⁻¹ * (y * x₂ * y⁻¹)⁻¹ := by group
          _ = (x₁ * x₂ * y) * y⁻¹ * (y * x₂ * y⁻¹)⁻¹ := by rw [hc]
          _ = x₁ * x₂ * (y * x₂ * y⁻¹)⁻¹ := by group
      rw [e]
      have hA : x₁ ∈ ⨆ i, conjSub (m i) (firstFactor K) := Subgroup.mem_iSup_of_mem 0 hx₁
      have hB : x₂ ∈ ⨆ i, conjSub (m i) (firstFactor K) := Subgroup.mem_iSup_of_mem 1 hx₂
      have hC : y * x₂ * y⁻¹ ∈ ⨆ i, conjSub (m i) (firstFactor K) := by
        refine Subgroup.mem_iSup_of_mem 2 ?_
        show y * x₂ * y⁻¹ ∈ conjSub (y * m₂) (firstFactor K)
        rw [← hF4]
        exact conj_mem_conjSub hx₂
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hB) (Subgroup.inv_mem _ hC)
  have hO := hind hmem
  apply hx₁O
  have h5 : y⁻¹ * (y * x₁ * y⁻¹) * y⁻¹⁻¹ ∈ conjSub y⁻¹ (oddCoreOf (sigmaGen K)) :=
    conj_mem_conjSub hO
  rw [Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer ((sigmaNorm K).inv_mem hy),
    show y⁻¹ * (y * x₁ * y⁻¹) * y⁻¹⁻¹ = x₁ by group] at h5
  exact h5

theorem E_le_M_conj (cfg : L3E8Cfg K z J zJ H Q E S) {g : T} (hg : g ∉ sigmaNorm K)
    (ht : g⁻¹ * z * g ∈ S) : E ≤ rightConjugate (sigmaNorm K) g := by
  have hz := cfg.datum.unique
  have ht2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz.sq]; group
  have htN : g⁻¹ * z * g ∉ Subgroup.normalizer (firstFactor K : Set T) :=
    fun h => hg (cfg.lemmaA (cfg.normalizer_ht_le h))
  intro e he
  obtain ⟨h1, h2, -⟩ := cfg.wreath_diag ht ht2 htN he
  rw [mem_rightConjugate_iff]
  apply cfg.zconj_cent
  rw [Subgroup.mem_centralizer_singleton_iff]
  set t := g⁻¹ * z * g with ht_def
  have hc : e⁻¹ * t * e * t = t * (e⁻¹ * t * e) := by
    rw [h1]
    calc t * (e * (t⁻¹ * e * t)) * t = t * (e * (t⁻¹ * e * t) * t) := by group
      _ = t * (t * (e * (t⁻¹ * e * t))) := by rw [h2]
  calc (g * e * g⁻¹)⁻¹ * z * (g * e * g⁻¹) * z = g * (e⁻¹ * t * e * t) * g⁻¹ := by
        rw [ht_def]; group
    _ = g * (t * (e⁻¹ * t * e)) * g⁻¹ := by rw [hc]
    _ = z * ((g * e * g⁻¹)⁻¹ * z * (g * e * g⁻¹)) := by rw [ht_def]; group

theorem normalizer_E_Lg_ne_bot (cfg : L3E8Cfg K z J zJ H Q E S) {g : T} (hg : g ∉ sigmaNorm K)
    (ht : g⁻¹ * z * g ∈ S) :
    ∃ e ∈ E, e ≠ 1 ∧ e ∈ Subgroup.normalizer (rightConjugate (firstFactor K) g : Set T) := by
  have hz := cfg.datum.unique
  obtain ⟨hEab, hE8⟩ := cfg.E8
  have hzE : z ∈ E := cfg.z_mem_E
  have hzHt : z ∈ firstFactor K := cfg.Q_le_ht (cfg.E_le_Q hzE)
  have ht2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz.sq]; group
  have htN : g⁻¹ * z * g ∉ Subgroup.normalizer (firstFactor K : Set T) :=
    fun h => hg (cfg.lemmaA (cfg.normalizer_ht_le h))
  have hEM := cfg.E_le_M_conj hg ht
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hzO : z ∉ oddCoreOf (sigmaGen K) := not_mem_oddCoreOf_of_sq _ hz.sq hz.ne_one
  have hNiff : ∀ y : T, g * y * g⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) →
      y ∈ Subgroup.normalizer (rightConjugate (firstFactor K) g : Set T) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro w
    have := hy (g * w * g⁻¹)
    simp only [SetLike.mem_coe, mem_rightConjugate_iff] at this ⊢
    rw [show g * y * g⁻¹ * (g * w * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * w * y⁻¹) * g⁻¹ by group]
      at this
    exact this
  by_cases heN : z ∈ Subgroup.normalizer (rightConjugate (firstFactor K) g : Set T)
  · exact ⟨z, hzE, hz.ne_one, heN⟩
  have key : ∀ f ∈ E, g * f * g⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) ∨
      g * (z * f) * g⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) := by
    intro f hf
    have he'M : g * z * g⁻¹ ∈ sigmaNorm K := (mem_rightConjugate_iff _ g z).mp (hEM hzE)
    have hf'M : g * f * g⁻¹ ∈ sigmaNorm K := (mem_rightConjugate_iff _ g f).mp (hEM hf)
    have hne : conjSub (1 : T) (firstFactor K) ≠ conjSub (g * z * g⁻¹)⁻¹ (firstFactor K) := by
      intro h
      apply heN
      apply hNiff
      have h1 : conjSub (g * z * g⁻¹)⁻¹ (firstFactor K) = firstFactor K := h.symm.trans h1Ht
      have := mem_normalizer_iff_conjSub_eq.mpr h1
      simpa using (Subgroup.normalizer _).inv_mem this
    have hx₁ : z ∈ conjSub (1 : T) (firstFactor K) := by rw [h1Ht]; exact hzHt
    have hx₂ : (g * z * g⁻¹)⁻¹ * z * (g * z * g⁻¹) ∈ conjSub (g * z * g⁻¹)⁻¹ (firstFactor K) := by
      have := conj_mem_conjSub (n := (g * z * g⁻¹)⁻¹) hzHt
      simpa using this
    obtain ⟨h1, -, h3⟩ := cfg.wreath_diag ht ht2 htN hzE
    have hf3 := h3 f hf
    have ha : z * ((g * z * g⁻¹)⁻¹ * z * (g * z * g⁻¹)) =
        g * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g))) * g⁻¹ := by
      calc z * ((g * z * g⁻¹)⁻¹ * z * (g * z * g⁻¹))
          = g * ((g⁻¹ * z * g) * (z⁻¹ * (g⁻¹ * z * g) * z)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * ((g⁻¹ * z * g) * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g)))))
            * g⁻¹ := by rw [h1]
        _ = g * (((g⁻¹ * z * g) * (g⁻¹ * z * g)) * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g))))
            * g⁻¹ := by group
        _ = g * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g))) * g⁻¹ := by rw [ht2, one_mul]
    have hc : g * f * g⁻¹ * (z * ((g * z * g⁻¹)⁻¹ * z * (g * z * g⁻¹))) =
        z * ((g * z * g⁻¹)⁻¹ * z * (g * z * g⁻¹)) * (g * f * g⁻¹) := by
      rw [ha]
      calc g * f * g⁻¹ * (g * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g))) * g⁻¹)
          = g * (f * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g)))) * g⁻¹ := by group
        _ = g * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g)) * f) * g⁻¹ := by rw [hf3]
        _ = g * (z * ((g⁻¹ * z * g)⁻¹ * z * (g⁻¹ * z * g))) * g⁻¹ * (g * f * g⁻¹) := by group
    rcases cfg.two_factor_support (Subgroup.one_mem _) ((sigmaNorm K).inv_mem he'M) hne hx₁ hx₂
        hzO hf'M hc with h | h
    · left
      rw [h1Ht] at h
      exact mem_normalizer_iff_conjSub_eq.mpr h
    · right
      rw [h1Ht] at h
      have h2 : conjSub (g * z * g⁻¹ * (g * f * g⁻¹)) (firstFactor K) = firstFactor K := by
        have h0 := conjSub_inv_conjSub (g * z * g⁻¹)⁻¹ (firstFactor K)
        rw [inv_inv] at h0
        rw [conjSub_mul, h, h0]
      rw [show g * (z * f) * g⁻¹ = g * z * g⁻¹ * (g * f * g⁻¹) by group]
      exact mem_normalizer_iff_conjSub_eq.mpr h2
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
  rcases key f hf with h | h
  · exact ⟨f, hf, hf1, hNiff f h⟩
  · refine ⟨z * f, E.mul_mem hzE hf, fun h1 => hfz ?_, hNiff _ h⟩
    have h2 : f = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right hz.sq

theorem unique_coset (cfg : L3E8Cfg K z J zJ H Q E S) : UniqueCosetZ K z := by
  have hz := cfg.datum.unique
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  intro x hx
  refine cfg.unique_of_S hz2 (fun g hg ht => ?_) hx
  obtain ⟨e, he, he1, heN⟩ := cfg.normalizer_E_Lg_ne_bot hg ht
  obtain ⟨l, hl, hle⟩ := cfg.E_conj he he1
  exact cfg.lemmaA_conj (cfg.ht_le_sigmaNorm hl) hg (hle ▸ heN)

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
