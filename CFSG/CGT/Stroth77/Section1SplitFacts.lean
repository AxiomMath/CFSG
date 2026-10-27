module

public import Certificates.Certificate778711

public section

namespace CFSG.CGT.Stroth77

open Equiv Equiv.Perm

theorem card_Tsp : Nat.card Tsp = 256 := Certificates.certificate778711.1
theorem card_Asp : Nat.card Asp = 32 := Certificates.certificate778711.2.1
theorem card_Esp : Nat.card Esp = 16 := Certificates.certificate778711.2.2.1

theorem closure_le_of_subset {gens : List Msp} {H : Subgroup Msp} (h : ∀ g ∈ gens, g ∈ H) :
    Subgroup.closure {g | g ∈ gens} ≤ H :=
  (Subgroup.closure_le H).2 fun g hg => h g hg

theorem mem_of_mem_gens {gens : List Msp} {g : Msp} (h : g ∈ gens) :
    g ∈ Subgroup.closure {g | g ∈ gens} := Subgroup.subset_closure h

theorem Asp_le_Tsp : Asp ≤ Tsp := closure_le_of_subset fun g hg =>
  mem_of_mem_gens (by simp only [gensAsp, gensTsp, List.mem_cons, List.not_mem_nil] at hg ⊢; tauto)
theorem Esp_le_Tsp : Esp ≤ Tsp := closure_le_of_subset fun g hg =>
  mem_of_mem_gens (by simp only [gensEsp, gensTsp, List.mem_cons, List.not_mem_nil] at hg ⊢; tauto)
theorem Dsp_le_Tsp : Dsp ≤ Tsp := closure_le_of_subset fun g hg =>
  mem_of_mem_gens (by simp only [gensDsp, gensTsp, List.mem_cons, List.not_mem_nil] at hg ⊢; tauto)
theorem AEsp_le_Tsp : AEsp ≤ Tsp := closure_le_of_subset fun g hg =>
  mem_of_mem_gens (by simp only [gensAEsp, gensTsp, List.mem_cons, List.not_mem_nil] at hg ⊢; tauto)
theorem Asp_le_AEsp : Asp ≤ AEsp := closure_le_of_subset fun g hg =>
  mem_of_mem_gens (by simp only [gensAsp, gensAEsp, List.mem_cons, List.not_mem_nil] at hg ⊢; tauto)
theorem Esp_le_AEsp : Esp ≤ AEsp := closure_le_of_subset fun g hg =>
  mem_of_mem_gens (by simp only [gensEsp, gensAEsp, List.mem_cons, List.not_mem_nil] at hg ⊢; tauto)

theorem spX1_mem_Asp : spX1 ∈ Asp := mem_of_mem_gens (by simp [gensAsp])
theorem spY1_mem_Asp : spY1 ∈ Asp := mem_of_mem_gens (by simp [gensAsp])
theorem spX_mem_Asp : spX ∈ Asp := mem_of_mem_gens (by simp [gensAsp])
theorem spY_mem_Asp : spY ∈ Asp := mem_of_mem_gens (by simp [gensAsp])
theorem spW_mem_Asp : spW ∈ Asp := mem_of_mem_gens (by simp [gensAsp])
theorem spUV_mem_Esp : spUV ∈ Esp := mem_of_mem_gens (by simp [gensEsp])
theorem spT_mem_Esp : spT ∈ Esp := mem_of_mem_gens (by simp [gensEsp])
theorem spU_mem_Dsp : spU ∈ Dsp := mem_of_mem_gens (by simp [gensDsp])

theorem spBasis_mem_Asp (i : Fin 5) : spBasis i ∈ Asp := by
  fin_cases i
  · exact spX1_mem_Asp
  · exact spY1_mem_Asp
  · exact spX_mem_Asp
  · exact spY_mem_Asp
  · exact spW_mem_Asp

theorem ite_mem_Asp (p : Prop) [Decidable p] {m : Msp} (hm : m ∈ Asp) :
    (if p then m else 1) ∈ Asp := by
  split_ifs
  · exact hm
  · exact one_mem _

theorem spPhi_mem_Asp (r : Nat) : spPhi r ∈ Asp := by
  unfold spPhi
  exact mul_mem (mul_mem (mul_mem (mul_mem (ite_mem_Asp _ spX1_mem_Asp)
    (ite_mem_Asp _ spY1_mem_Asp)) (ite_mem_Asp _ spX_mem_Asp)) (ite_mem_Asp _ spY_mem_Asp))
    (ite_mem_Asp _ spW_mem_Asp)

theorem Tsp_isSylow : ∃ S : Sylow 2 Msp, (S : Subgroup Msp) = Tsp := by
  refine ⟨Sylow.ofCard Tsp ?_, rfl⟩
  rw [card_Tsp, card_Msp]
  rw [show (11520 : ℕ) = 2 ^ 8 * 45 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem Asp_comm {a b : Msp} (ha : a ∈ Asp) (hb : b ∈ Asp) : a * b = b * a :=
  Certificates.certificate778711.2.2.2.1 a ha b hb

theorem Asp_sq {a : Msp} (ha : a ∈ Asp) : a * a = 1 :=
  Certificates.certificate778711.2.2.2.2.1 a ha

theorem Asp_unique (B : Subgroup Msp) (hB : B ≤ Tsp) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hcard : Nat.card B = 32) : B = Asp :=
  Certificates.certificate778711.2.2.2.2.2.1 B hB hc hcard

theorem mem_Asp_of_commute {s : Msp} (hs : s ∈ Tsp) (h : ∀ a ∈ Asp, s * a = a * s) : s ∈ Asp :=
  Certificates.certificate778711.2.2.2.2.2.2.1 s hs h

theorem Esp_le_Qsp : Esp ≤ Qsp := closure_le_of_subset fun g hg => by
  rw [mem_Qsp]
  simp only [gensEsp, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> rfl

theorem Esp_eq_Qsp : Esp = Qsp :=
  Subgroup.eq_of_le_of_card_ge Esp_le_Qsp (by rw [card_Esp, card_Qsp])

theorem mem_Esp_iff {s : Msp} (hs : s ∈ AEsp) : s ∈ Esp ↔ s * s = 1 ∧
    (s ∈ Asp → ∀ z ∈ AEsp, s * z = z * s) ∧
    (s ∉ Asp → ∃ z ∈ AEsp, z ∉ Asp ∧ s⁻¹ * z ∉ Asp ∧ z * z = 1 ∧ s * z = z * s) :=
  Certificates.certificate778711.2.2.2.2.2.2.2.1 s hs

theorem act_spUV : spUV * spX1 * spUV⁻¹ = spPhi (GL5.r0 GL5.uvC) ∧
    spUV * spY1 * spUV⁻¹ = spPhi (GL5.r1 GL5.uvC) ∧ spUV * spX * spUV⁻¹ = spPhi (GL5.r2 GL5.uvC) ∧
    spUV * spY * spUV⁻¹ = spPhi (GL5.r3 GL5.uvC) ∧ spUV * spW * spUV⁻¹ = spPhi (GL5.r4 GL5.uvC) :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.1
theorem act_spT : spT * spX1 * spT⁻¹ = spPhi (GL5.r0 GL5.tC) ∧
    spT * spY1 * spT⁻¹ = spPhi (GL5.r1 GL5.tC) ∧ spT * spX * spT⁻¹ = spPhi (GL5.r2 GL5.tC) ∧
    spT * spY * spT⁻¹ = spPhi (GL5.r3 GL5.tC) ∧ spT * spW * spT⁻¹ = spPhi (GL5.r4 GL5.tC) :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.1
theorem act_spU : spU * spX1 * spU⁻¹ = spPhi (GL5.r0 GL5.uC) ∧
    spU * spY1 * spU⁻¹ = spPhi (GL5.r1 GL5.uC) ∧ spU * spX * spU⁻¹ = spPhi (GL5.r2 GL5.uC) ∧
    spU * spY * spU⁻¹ = spPhi (GL5.r3 GL5.uC) ∧ spU * spW * spU⁻¹ = spPhi (GL5.r4 GL5.uC) :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.2.1
theorem act_spRho : spRho * spX1 * spRho⁻¹ = spPhi (GL5.r0 GL5.rhoC) ∧
    spRho * spY1 * spRho⁻¹ = spPhi (GL5.r1 GL5.rhoC) ∧
    spRho * spX * spRho⁻¹ = spPhi (GL5.r2 GL5.rhoC) ∧
    spRho * spY * spRho⁻¹ = spPhi (GL5.r3 GL5.rhoC) ∧
    spRho * spW * spRho⁻¹ = spPhi (GL5.r4 GL5.rhoC) :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.2.2.1

theorem spRho_mem_normalizer_Asp : spRho ∈ Subgroup.normalizer (Asp : Set Msp) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hle : Asp ≤ Asp.comap (MulAut.conj spRho).toMonoidHom := by
    refine closure_le_of_subset fun a ha => ?_
    simp only [gensAsp, List.mem_cons, List.not_mem_nil, or_false] at ha
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨h0, h1, h2, h3, h4⟩ := act_spRho
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · rw [h0]; exact spPhi_mem_Asp _
    · rw [h1]; exact spPhi_mem_Asp _
    · rw [h2]; exact spPhi_mem_Asp _
    · rw [h3]; exact spPhi_mem_Asp _
    · rw [h4]; exact spPhi_mem_Asp _
  have := hle hn
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem exists_mem_Dsp {s : Msp} (hs : s ∈ Tsp) : ∃ d ∈ Dsp, s * d⁻¹ ∈ Asp :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.2.2.2.1 s hs

@[expose] def S1sp : Subgroup Msp := Tsp ⊓ (Perm.sign.comp θsp).ker

theorem card_S1sp : Nat.card S1sp = 128 :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem S1sp_le_Tsp : S1sp ≤ Tsp := inf_le_left

theorem exists_conj_mem_spW4 {z : Msp} (hz : z ∈ S1sp) (hz2 : z * z = 1) :
    ∃ m : Msp, ∃ r, r < 16 ∧ m * z * m⁻¹ = spPhi r :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z hz hz2

theorem exists_spPhi_eq {a : Msp} (ha : a ∈ Asp) : ∃ r, r < 32 ∧ spPhi r = a :=
  Certificates.certificate778711.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a ha

end CFSG.CGT.Stroth77
