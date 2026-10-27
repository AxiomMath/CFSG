module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAR
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM4

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

namespace TD

variable {H : AD S T₁} (T : H.TD)

theorem d_mul_d (he : T.e = false) : T.d * T.d = 1 := by
  rw [T.sq, he]; exact map_one _

theorem d_conj_p' (he : T.e = false) : T.d * T.p * T.d⁻¹ = H.ι MA.w₂ := by
  rw [T.d_conj_p, he]; simp [tE]

theorem d_conj_ι {a : MA} (ha : MA.inT1 a = true) : T.d * H.ι a * T.d⁻¹ = H.ι (dc T.e T.c₂ a) :=
  (T.conj a ha).symm

theorem d_comm_w₁ (he : T.e = false) : T.d * H.ι MA.w₁ = H.ι MA.w₁ * T.d := by
  have h := T.d_conj_ι (a := MA.w₁) (by decide +kernel)
  rw [he, dc, (dAct_gens _ _ _).2.1, cOne, ite_eq_right_iff.mpr (by decide), mul_one] at h
  calc T.d * H.ι MA.w₁ = (T.d * H.ι MA.w₁ * T.d⁻¹) * T.d := by group
    _ = H.ι MA.w₁ * T.d := by rw [h]

theorem d_conj_ι_w₂ (b : MA) (hb : MA.inT1 b = true) :
    T.d * H.ι (MA.w₂ * b) * T.d⁻¹ = T.p * H.ι (dc T.e T.c₂ b) := by
  rw [map_mul, show T.d * (H.ι MA.w₂ * H.ι b) * T.d⁻¹ =
    (T.d * H.ι MA.w₂ * T.d⁻¹) * (T.d * H.ι b * T.d⁻¹) by group, T.d_conj_ι hb, p]

theorem rho_fix (he : T.e = false) {ζ : MA} (hζ : ζ ∈ MA.ZList)
    (h : T.p * H.ι MA.w₂ * T.p⁻¹ = H.ι (MA.condWit (cOne T.e) * ζ)) :
    pAct T.e T.c₂ (dc T.e T.c₂ (MA.w₂ * (MA.condWit (cOne T.e) * ζ))) =
      MA.w₂ * (MA.condWit (cOne T.e) * ζ) := by
  set ρ := MA.w₂ * (MA.condWit (cOne T.e) * ζ) with hρ
  have hρW : MA.inW ρ = true := MA.condW_wit_W (cOne T.e) (cOne_mem T.e) ζ hζ
  have hρT : MA.inT1 ρ = true := by
    have := MA.W_le_M1 ρ hρW
    simp only [MA.inM1, Bool.and_eq_true, Bool.not_eq_true'] at this
    simp only [MA.inT1, this.1, Bool.not_false]
  have hpw : T.p * H.ι MA.w₂ * T.p⁻¹ = H.ι (MA.w₂ * ρ) := by
    rw [h, hρ, ← mul_assoc, MA.w₂_sq, one_mul]
  have e1 : T.d * (T.p * H.ι MA.w₂ * T.p⁻¹) * T.d⁻¹ =
      H.ι MA.w₂ * T.p * (H.ι MA.w₂)⁻¹ := by
    rw [show T.d * (T.p * H.ι MA.w₂ * T.p⁻¹) * T.d⁻¹ = (T.d * T.p * T.d⁻¹) *
      (T.d * H.ι MA.w₂ * T.d⁻¹) * (T.d * T.p * T.d⁻¹)⁻¹ by group, T.d_conj_p' he, ← p]
  have e2 : T.d * H.ι (MA.w₂ * ρ) * T.d⁻¹ = T.p * H.ι (dc T.e T.c₂ ρ) := T.d_conj_ι_w₂ ρ hρT
  rw [hpw, e2] at e1
  have e3 : H.ι MA.w₂ * T.p * (H.ι MA.w₂)⁻¹ = H.ι ρ * T.p := by
    have h4 : T.p * (H.ι MA.w₂)⁻¹ = H.ι (MA.w₂ * ρ) * T.p := by
      rw [← map_inv, show MA.w₂⁻¹ = MA.w₂ by decide +kernel, ← hpw]; group
    rw [mul_assoc, h4, ← mul_assoc, ← map_mul, ← mul_assoc, MA.w₂_sq, one_mul]
  rw [e3] at e1
  have e4 : H.ι ρ = T.p * H.ι (dc T.e T.c₂ ρ) * T.p⁻¹ := by
    rw [e1]; group
  apply H.ι_injective
  rw [← T.p_conj_ι (dc_T1 T.e T.c₂ T.hc₂ ρ), ← e4]

@[expose] def inB (b : MA) : Bool := decide (InSpan [MA.z, qh, MA.t, MA.w₁] b)

theorem card_B : Nat.card {b : MA // inB b = true} = 16 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem eq_of_mul_dpow {x x' : X} (hx : x ∈ T.R₂) (hx' : x' ∈ T.R₂) {j j' : Bool}
    (h : x * (if j then T.d else 1) = x' * (if j' then T.d else 1)) : j = j' ∧ x = x' := by
  cases j <;> cases j' <;> simp only [Bool.false_eq_true, ite_false, ite_true, mul_one] at h
  · exact ⟨rfl, h⟩
  · exfalso; apply T.d_not_mem_R₂
    have := mul_mem (inv_mem hx') hx
    rwa [h, inv_mul_cancel_left] at this
  · exfalso; apply T.d_not_mem_R₂
    have := mul_mem (inv_mem hx) hx'
    rwa [← h, inv_mul_cancel_left] at this
  · exact ⟨rfl, mul_right_cancel h⟩

theorem eq_of_mul_epow {ε : X} (hε : ε * T.p⁻¹ ∈ H.G.D₁.S₁) {b b' : MA} {i i' : Bool}
    (h : H.ι b * (if i then ε else 1) = H.ι b' * (if i' then ε else 1)) : i = i' ∧ b = b' := by
  have hεS : ε ∉ H.G.D₁.S₁ := fun h' => T.p_not_mem_S₁ (by
    have := mul_mem (inv_mem hε) h'
    rwa [show (ε * T.p⁻¹)⁻¹ * ε = T.p by group] at this)
  cases i <;> cases i' <;> simp only [Bool.false_eq_true, ite_false, ite_true, mul_one] at h
  · exact ⟨rfl, H.ι_injective h⟩
  · exfalso; apply hεS
    have := mul_mem (inv_mem (H.ι_mem_S₁ b')) (H.ι_mem_S₁ b)
    rwa [h, inv_mul_cancel_left] at this
  · exfalso; apply hεS
    have := mul_mem (inv_mem (H.ι_mem_S₁ b)) (H.ι_mem_S₁ b')
    rwa [← h, inv_mul_cancel_left] at this
  · exact ⟨rfl, H.ι_injective (mul_right_cancel h)⟩

theorem not_conjTo_d (he : T.e = false) : ¬ ConjTo t T.d := by
  obtain ⟨ζ, hζ, hpw⟩ := T.exists_ζ
  have hcons := T.rho_fix he hζ hpw
  have hc1 : cOne T.e = 1 := by rw [he]; rfl
  have hdc : ∀ a, dc T.e T.c₂ a = dc false T.c₂ a := fun a => by rw [he]
  have hpa : ∀ a, pAct T.e T.c₂ a = pAct false T.c₂ a := fun a => by rw [he]
  rw [hc1, hdc, hpa] at hcons
  rw [hc1] at hpw
  obtain ⟨r, hr, E1, E2⟩ := cert_e T.c₂ T.hc₂ ζ hζ hcons
  have hrT : MA.inT1 r = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide +kernel
  have hqT : MA.inT1 qh = true := qh_facts.2.2.2
  obtain ⟨ε, hε⟩ : ∃ ε : X, ε = H.ι (MA.w₂ * r) * T.p := ⟨_, rfl⟩
  have hεR : ε * T.p⁻¹ ∈ H.G.D₁.S₁ := by rw [hε, mul_inv_cancel_right]; exact H.ι_mem_S₁ _
  have hεR₂ : ε ∈ T.R₂ := by rw [hε]; exact mul_mem (T.ι_mem_R₂ _) T.p_mem_R₂
  have hεd : ε * T.d = T.d * ε := by
    have h1 : T.d * ε * T.d⁻¹ = ε := by
      calc T.d * ε * T.d⁻¹ = (T.d * H.ι (MA.w₂ * r) * T.d⁻¹) * (T.d * T.p * T.d⁻¹) := by
            rw [hε]; group
        _ = T.p * H.ι (dc T.e T.c₂ r) * H.ι MA.w₂ := by
            rw [T.d_conj_ι_w₂ r hrT, T.d_conj_p' he]
        _ = H.ι (pAct T.e T.c₂ (dc T.e T.c₂ r)) * (T.p * H.ι MA.w₂ * T.p⁻¹) * T.p := by
            rw [← T.p_conj_ι (dc_T1 T.e T.c₂ T.hc₂ r)]; group
        _ = H.ι (pAct false T.c₂ (dc false T.c₂ r) *
              (MA.w₂ * (MA.w₂ * (MA.condWit 1 * ζ)))) * T.p := by
            rw [hpw, hdc, hpa, ← mul_assoc MA.w₂, MA.w₂_sq, one_mul, ← map_mul]
        _ = ε := by rw [E1, hε]
    calc ε * T.d = (T.d * ε * T.d⁻¹) * T.d := by rw [h1]
      _ = T.d * ε := by group
  have hεq : ε * H.ι qh = H.ι qh * ε := by
    have h1 : T.p * H.ι qh = H.ι (pAct T.e T.c₂ qh) * T.p := by
      rw [← T.p_conj_ι hqT]; group
    rw [hε, mul_assoc, h1, ← mul_assoc, ← map_mul, hpa, E2, map_mul, mul_assoc]
  have hdq : T.d * H.ι qh = H.ι qh * T.d := by
    have h1 := T.d_conj_ι hqT
    rw [hdc, dc_qh T.c₂ T.hc₂] at h1
    calc T.d * H.ι qh = (T.d * H.ι qh * T.d⁻¹) * T.d := by group
      _ = H.ι qh * T.d := by rw [h1]
  have hqt : H.ι qh * t = t * H.ι qh := by
    have h1 := congrArg H.ι qh_facts.2.1
    rwa [map_mul, map_mul, H.ι_t] at h1
  have hqw : H.ι qh * H.ι MA.w₁ = H.ι MA.w₁ * H.ι qh := by
    rw [← map_mul, ← map_mul, qh_facts.2.2.1]
  set Q := closure ({H.ι qh, t, T.d, H.ι MA.w₁, ε} : Set X) with hQ
  have hQT₂ : Q ≤ T.T₂ := by
    refine (closure_le _).mpr fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h | h <;> rw [h]
    · exact T.R₂_le_T₂ (T.ι_mem_R₂ _)
    · have h1 := T.ι_mem_R₂ MA.t
      rw [H.ι_t] at h1
      exact T.R₂_le_T₂ h1
    · exact T.d_mem_T₂
    · exact T.R₂_le_T₂ (T.ι_mem_R₂ _)
    · exact T.R₂_le_T₂ hεR₂
  have hQd : Q ≤ centralizer ({T.d} : Set X) := by
    refine (closure_le _).mpr fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with h | h | h | h | h
    · rw [h]; exact hdq.symm
    · rw [h]; exact T.d_comm_t.symm
    · rw [h]
    · rw [h]; exact (T.d_comm_w₁ he).symm
    · rw [h]; exact hεd
  have hqc : ∀ x ∈ Q, H.ι qh * x = x * H.ι qh := by
    have hle : Q ≤ centralizer ({H.ι qh} : Set X) := by
      refine (closure_le _).mpr fun g hg => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hg with h | h | h | h | h
      · rw [h]
      · rw [h]; exact hqt.symm
      · rw [h]; exact hdq
      · rw [h]; exact hqw.symm
      · rw [h]; exact hεq
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hle hx)).symm
  have hqQ : H.ι qh ∈ Q := subset_closure (Set.mem_insert _ _)
  have hq2 : (H.ι qh) ^ 2 ≠ 1 := by
    rw [pow_two, ← map_mul, qh_facts.1, H.ι_z]; exact z_ne_one S
  have hBQ : ∀ b : MA, inB b = true → H.ι b ∈ Q := by
    intro b hb
    refine map_mem_of_inSpan H.ι (of_decide_eq_true hb) fun g hg => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · rw [show MA.z = qh * qh from qh_facts.1.symm, map_mul]; exact mul_mem hqQ hqQ
    · exact hqQ
    · rw [H.ι_t]; exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hεQ : ε ∈ Q := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  have hdQ : T.d ∈ Q := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert _ _)))
  set f : {b : MA // inB b = true} × Bool × Bool → Q := fun x =>
    ⟨H.ι x.1.1 * (if x.2.1 then ε else 1) * (if x.2.2 then T.d else 1),
      mul_mem (mul_mem (hBQ _ x.1.2) (by split_ifs <;> first | exact hεQ | exact one_mem _))
        (by split_ifs <;> first | exact hdQ | exact one_mem _)⟩ with hf
  have hfinj : Function.Injective f := by
    rintro ⟨⟨b, hb⟩, i, j⟩ ⟨⟨b', hb'⟩, i', j'⟩ h
    have h1 : H.ι b * (if i then ε else 1) * (if j then T.d else 1) =
        H.ι b' * (if i' then ε else 1) * (if j' then T.d else 1) := congrArg Subtype.val h
    have hx : ∀ (c : MA) (k : Bool), H.ι c * (if k then ε else 1) ∈ T.R₂ := fun c k => by
      cases k
      · simp only [Bool.false_eq_true, ite_false, mul_one]; exact T.ι_mem_R₂ c
      · simp only [ite_true]; exact mul_mem (T.ι_mem_R₂ c) hεR₂
    obtain ⟨rfl, h2⟩ := T.eq_of_mul_dpow (hx b i) (hx b' i') h1
    obtain ⟨rfl, rfl⟩ := T.eq_of_mul_epow hεR h2
    rfl
  have hcard : Nat.card A.T ≤ Nat.card Q := by
    have h1 := Nat.card_le_card_of_injective f hfinj
    rw [Nat.card_prod, Nat.card_prod, card_B, Nat.card_eq_fintype_card (α := Bool),
      Fintype.card_bool] at h1
    exact (card_T_le (C := C)).trans h1
  exact not_conjTo_of_center A S (T.isPGroup_T₂.to_le hQT₂) hQd hcard hqQ hqc hq2

theorem T1_of_not : ∀ b : MA, MA.inT1 b = false → MA.inT1 (MA.w₂ * b) = true := by
  decide +kernel

theorem not_conjTo_of_comm_w₁ (he : T.e = false) {x : X} (hx : x ∈ T.T₂) (hxR : x ∉ T.R₂)
    (hxw : x * H.ι MA.w₁ = H.ι MA.w₁ * x) : ¬ ConjTo t x := by
  have hdc : ∀ a, dc T.e T.c₂ a = dc false T.c₂ a := fun a => by rw [he]
  have key : ∀ b : MA, H.ι b * T.d * H.ι MA.w₁ = H.ι MA.w₁ * (H.ι b * T.d) →
      ¬ ConjTo t (H.ι b * T.d) := by
    intro b hbw ⟨g, hg⟩
    have hx2 : H.ι b * T.d * (H.ι b * T.d) = 1 := by
      rw [← hg, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, tt (A := A),
        mul_one, mul_inv_cancel]
    have hsq : H.ι b * T.d * (H.ι b * T.d) = H.ι b * (T.d * H.ι b * T.d⁻¹) := by
      rw [show H.ι b * T.d * (H.ι b * T.d) = H.ι b * (T.d * H.ι b * T.d⁻¹) * (T.d * T.d) by
        group, T.d_mul_d he, mul_one]
    by_cases hbT : MA.inT1 b = true
    · rw [hsq, T.d_conj_ι hbT, hdc, ← map_mul] at hx2
      have hb1 : b * dc false T.c₂ b = 1 := H.ι_injective (by rw [hx2, map_one])
      have hbw' : b * MA.w₁ = MA.w₁ * b := by
        apply H.ι_injective
        rw [map_mul, map_mul]
        have h1 : H.ι b * T.d * H.ι MA.w₁ = H.ι b * H.ι MA.w₁ * T.d := by
          rw [mul_assoc, T.d_comm_w₁ he, ← mul_assoc]
        rw [h1, ← mul_assoc] at hbw
        exact mul_right_cancel hbw
      obtain ⟨s, hsT, hs⟩ := cobound T.c₂ T.hc₂ b hbT hb1 hbw'
      apply T.not_conjTo_d he
      have hsd : H.ι b * T.d = (H.ι s)⁻¹ * T.d * H.ι s := by
        have h1 := T.d_conj_ι hsT
        rw [hdc] at h1
        rw [hs, map_mul, map_inv, ← h1]; group
      refine ⟨H.ι s * g, ?_⟩
      calc H.ι s * g * t * (H.ι s * g)⁻¹ = H.ι s * (g * t * g⁻¹) * (H.ι s)⁻¹ := by group
        _ = T.d := by rw [hg, hsd]; group
    · exfalso
      have hb' : MA.inT1 (MA.w₂ * b) = true := T1_of_not b (by simpa using hbT)
      have hbe : b = MA.w₂ * (MA.w₂ * b) := by rw [← mul_assoc, MA.w₂_sq, one_mul]
      rw [hsq, hbe, T.d_conj_ι_w₂ _ hb'] at hx2
      apply T.p_not_mem_S₁
      have h1 : T.p = (H.ι (MA.w₂ * (MA.w₂ * b)))⁻¹ * (H.ι (dc T.e T.c₂ (MA.w₂ * b)))⁻¹ := by
        calc T.p = (H.ι (MA.w₂ * (MA.w₂ * b)))⁻¹ * (H.ι (MA.w₂ * (MA.w₂ * b)) *
              (T.p * H.ι (dc T.e T.c₂ (MA.w₂ * b)))) * (H.ι (dc T.e T.c₂ (MA.w₂ * b)))⁻¹ := by
              group
          _ = _ := by rw [hx2]; group
      rw [h1]
      exact mul_mem (inv_mem (H.ι_mem_S₁ _)) (inv_mem (H.ι_mem_S₁ _))
  have hxd : x * T.d⁻¹ ∈ T.R₂ := (T.mem_T₂ hx).resolve_left hxR
  rcases T.mem_R₂ hxd with h | h
  · obtain ⟨b, hb⟩ := H.mem_range_of_mem_S₁ h
    have hxe : x = H.ι b * T.d := by rw [hb]; group
    rw [hxe] at hxw ⊢
    exact key b hxw
  · obtain ⟨b, hb⟩ := H.mem_range_of_mem_S₁ h
    have hpd : T.p * T.d = T.d * H.ι MA.w₂ := by rw [p]; group
    have hxe : x = H.ι b * T.d * H.ι MA.w₂ := by
      rw [mul_assoc, ← hpd, ← mul_assoc, hb]; group
    have hw₂w : H.ι MA.w₂ * H.ι MA.w₁ = H.ι MA.w₁ * H.ι MA.w₂ := by
      rw [← map_mul, ← map_mul, show MA.w₂ * MA.w₁ = MA.w₁ * MA.w₂ by decide +kernel]
    intro hconj
    have hy : H.ι (MA.w₂ * b) * T.d = H.ι MA.w₂ * x * (H.ι MA.w₂)⁻¹ := by
      rw [hxe, map_mul]; group
    have hw₂w' : (H.ι MA.w₂)⁻¹ * H.ι MA.w₁ = H.ι MA.w₁ * (H.ι MA.w₂)⁻¹ := by
      calc (H.ι MA.w₂)⁻¹ * H.ι MA.w₁ =
          (H.ι MA.w₂)⁻¹ * (H.ι MA.w₁ * H.ι MA.w₂) * (H.ι MA.w₂)⁻¹ := by group
        _ = (H.ι MA.w₂)⁻¹ * (H.ι MA.w₂ * H.ι MA.w₁) * (H.ι MA.w₂)⁻¹ := by rw [hw₂w]
        _ = H.ι MA.w₁ * (H.ι MA.w₂)⁻¹ := by group
    apply key (MA.w₂ * b)
    · rw [hy]
      calc H.ι MA.w₂ * x * (H.ι MA.w₂)⁻¹ * H.ι MA.w₁ =
          H.ι MA.w₂ * x * ((H.ι MA.w₂)⁻¹ * H.ι MA.w₁) := by group
        _ = H.ι MA.w₂ * (x * H.ι MA.w₁) * (H.ι MA.w₂)⁻¹ := by rw [hw₂w']; group
        _ = (H.ι MA.w₂ * H.ι MA.w₁) * x * (H.ι MA.w₂)⁻¹ := by rw [hxw]; group
        _ = H.ι MA.w₁ * (H.ι MA.w₂ * x * (H.ι MA.w₂)⁻¹) := by rw [hw₂w]; group
    · rw [hy]
      obtain ⟨g, hg⟩ := hconj
      exact ⟨H.ι MA.w₂ * g, by rw [← hg]; group⟩

theorem not_conjTo_U₁ (he : T.e = false) {x : X} (hx : x ∈ T.T₂)
    (hxw : x * H.ι MA.w₁ = H.ι MA.w₁ * x) : ¬ ConjTo t x := by
  by_cases hxR : x ∈ T.R₂
  · refine T.not_conjTo_M ?_
    rcases T.mem_R₂ hxR with h | h
    · obtain ⟨a, rfl⟩ := H.mem_range_of_mem_S₁ h
      have ha : MA.inM a = true := (comm_w₁_iff a).mp (H.ι_injective (by
        rw [map_mul, map_mul]; exact hxw))
      exact mem_sup_left ⟨a, ha, rfl⟩
    · obtain ⟨a, ha⟩ := H.mem_range_of_mem_S₁ h
      have hxe : x = H.ι a * T.p := by rw [ha]; group
      have hpw : T.p * H.ι MA.w₁ = H.ι MA.w₁ * T.p := by
        have h1 := T.actsW.2.2.2.2.2.1
        calc T.p * H.ι MA.w₁ = (T.p * H.ι MA.w₁ * T.p⁻¹) * T.p := by group
          _ = H.ι MA.w₁ * T.p := by rw [h1]
      have haw : H.ι a * H.ι MA.w₁ = H.ι MA.w₁ * H.ι a := by
        rw [hxe] at hxw
        have h1 : H.ι a * T.p * H.ι MA.w₁ = H.ι a * H.ι MA.w₁ * T.p := by
          rw [mul_assoc, hpw, ← mul_assoc]
        rw [h1, ← mul_assoc] at hxw
        exact mul_right_cancel hxw
      have ham : MA.inM a = true := (comm_w₁_iff a).mp (H.ι_injective (by
        rw [map_mul, map_mul]; exact haw))
      rw [hxe]
      exact mul_mem (mem_sup_left ⟨a, ham, rfl⟩) (mem_sup_right (mem_zpowers _))
  · exact T.not_conjTo_of_comm_w₁ he hx hxR hxw

end TD

end AD

end KD8ab

end CFSG.ComponentClassification.HSFLit
