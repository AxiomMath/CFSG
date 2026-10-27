module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA1C
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckZ2
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada

theorem normalizer_A₁sub : normalizer (A₁sub : Set SU52) = CzSub := by
  refine le_antisymm (fun n hn => ?_) fun g hg =>
    mem_normalizer_fintype fun a ha => conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub hg) ha
  have hz : zSU ∈ A₁sub := X₄sub_le_A₁sub' (ZX₄sub_le_X₄sub zSU_mem)
  have hc : ∀ a ∈ A₁sub, n * zSU * n⁻¹ * a = a * (n * zSU * n⁻¹) := by
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A₁sub := by
      have := (mem_normalizer_iff.1 (inv_mem hn) a).1 ha
      rwa [inv_inv] at this
    have hza : zSU * (n⁻¹ * a * n) = n⁻¹ * a * n * zSU :=
      (ZX₄sub_comm zSU_mem (A₁sub_le_Ssub ha')).symm
    calc n * zSU * n⁻¹ * a = n * (zSU * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * (n⁻¹ * a * n * zSU) * n⁻¹ := by rw [hza]
      _ = a * (n * zSU * n⁻¹) := by group
  have hZ := mem_ZX₄sub_of_comm_A₁ hc
  exact mem_centralizer_singleton_iff.2 (comm_zSU_of_mem (mul_mem (inv_mem zSU_mem) hZ))

theorem K₁sub_le_CzSub : K₁sub ≤ CzSub := by
  have hX₁S : X₁sub ≤ Ssub := le_sup_left.trans (le_sup_left.trans le_sup_left)
  refine sup_le (fun x hx => mem_centralizer_singleton_iff.2 ?_) (zpowers_le.2 ?_)
  · exact ZX₄sub_comm zSU_mem (hX₁S hx)
  · exact mem_centralizer_singleton_iff.2 (genSU_comm_zSU 0 (by decide))

@[expose] def a₁ActU (c : Fin 3 → F4) : Fin 3 → F4 := ![c 2, c 1, c 0]

@[expose] def a₁ActX (a b : F4) (c : Fin 3 → F4) : Fin 3 → F4 :=
  ![c 0, a * c 0 + c 1, b * c 0 + bar a * c 1 + c 2]

theorem cvec_conj_of_corner {g a : SU52} (hg : g * zSU = zSU * g) (h00 : mat g 0 0 = 1)
    (ha : a ∈ A₁sub) : cvec (mat (g * a * g⁻¹)) = (blk3 (mat g)).mulVec (cvec (mat a)) := by
  rw [cvec_conj hg ha, h00, one_smul]

theorem cvec_conj_uSU {a : SU52} (ha : a ∈ A₁sub) :
    cvec (mat (uSU * a * uSU⁻¹)) = a₁ActU (cvec (mat a)) := by
  rw [cvec_conj_of_corner (show uSU * zSU = zSU * uSU from genSU_comm_zSU 0 (by decide)) rfl ha,
    mat_uSU]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3, uMat, a₁ActU]

theorem cvec_conj_x₁SU (α β : F4) (h : α * bar α = β + bar β) {a : SU52} (ha : a ∈ A₁sub) :
    cvec (mat (x₁SU α β h * a * (x₁SU α β h)⁻¹)) = a₁ActX α β (cvec (mat a)) := by
  have hX₁S : X₁sub ≤ Ssub := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hg : x₁SU α β h * zSU = zSU * x₁SU α β h := ZX₄sub_comm zSU_mem (hX₁S (x₁SU_mem _ _ _))
  rw [cvec_conj_of_corner hg rfl ha, mat_x₁SU]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blk3, ι3, x₁Mat, a₁ActX]

theorem eq_bot_or_eq_top_of_closed {V : AddSubgroup (Fin 3 → F4)} (hU : ∀ c ∈ V, a₁ActU c ∈ V)
    (h01 : ∀ c ∈ V, a₁ActX 0 1 c ∈ V) (h1ω : ∀ c ∈ V, a₁ActX 1 F4.ω c ∈ V)
    (hωω : ∀ c ∈ V, a₁ActX F4.ω F4.ω c ∈ V) : V = ⊥ ∨ V = ⊤ := by
  by_cases hV : ∀ c ∈ V, c = 0
  · left
    rw [eq_bot_iff]
    intro c hc
    exact (AddSubgroup.mem_bot).2 (hV c hc)
  right
  simp only [not_forall, exists_prop] at hV
  obtain ⟨v, hv, hv0⟩ := hV
  have i01 : ∀ c : Fin 3 → F4, a₁ActX 0 1 c - c = ![0, 0, c 0] := by
    intro c
    funext i
    fin_cases i <;> simp [a₁ActX]
  have i1ω : ∀ c : Fin 3 → F4, a₁ActX 1 F4.ω c - c = ![0, c 0, F4.ω * c 0 + bar 1 * c 1] := by
    intro c
    funext i
    fin_cases i <;> simp [a₁ActX]
  have step1 : ∃ d : F4, d ≠ 0 ∧ ![0, 0, d] ∈ V := by
    by_cases h0 : v 0 = 0
    · by_cases h2 : v 2 = 0
      · have h1 : v 1 ≠ 0 := fun h1 => hv0 (by
          funext i
          fin_cases i
          · exact h0
          · exact h1
          · exact h2)
        refine ⟨v 1, h1, ?_⟩
        have := sub_mem (h1ω v hv) hv
        rw [i1ω, h0, mul_zero, zero_add, map_one, one_mul] at this
        exact this
      · refine ⟨v 2, h2, ?_⟩
        have := sub_mem (h01 _ (hU v hv)) (hU v hv)
        rw [i01] at this
        exact this
    · refine ⟨v 0, h0, ?_⟩
      have := sub_mem (h01 v hv) hv
      rwa [i01] at this
  obtain ⟨d, hd0, hd⟩ := step1
  have step2 : ∀ e : F4, ![0, 0, e] ∈ V → ![0, 0, bar F4.ω * e] ∈ V := by
    intro e he
    have hp := hU _ he
    have hq := sub_mem (h1ω _ hp) hp
    have hr := sub_mem (hωω _ hp) hp
    have hqr := add_mem hq hr
    have key : ∀ e : F4,
        a₁ActX 1 F4.ω ((a₁ActX 1 F4.ω (a₁ActU ![0, 0, e]) - a₁ActU ![0, 0, e]) +
            (a₁ActX F4.ω F4.ω (a₁ActU ![0, 0, e]) - a₁ActU ![0, 0, e])) -
          ((a₁ActX 1 F4.ω (a₁ActU ![0, 0, e]) - a₁ActU ![0, 0, e]) +
            (a₁ActX F4.ω F4.ω (a₁ActU ![0, 0, e]) - a₁ActU ![0, 0, e])) =
          ![0, 0, bar F4.ω * e] := by
      unfold a₁ActX a₁ActU
      simp only [bar_apply]
      decide
    rw [← key]
    exact sub_mem (h1ω _ hqr) hqr
  have step3 : ∀ e : F4, ![0, 0, e] ∈ V := by
    intro e
    have key : ∀ d e : F4, d ≠ 0 →
        e = 0 ∨ e = d ∨ e = bar F4.ω * d ∨ e = bar F4.ω * (bar F4.ω * d) := by
      simp only [bar_apply]
      decide
    rcases key d e hd0 with rfl | rfl | rfl | rfl
    · have : (![0, 0, 0] : Fin 3 → F4) = 0 := by decide
      rw [this]
      exact zero_mem V
    · exact hd
    · exact step2 _ hd
    · exact step2 _ (step2 _ hd)
  have step4 : ∀ e : F4, ![e, 0, 0] ∈ V := fun e => hU _ (step3 e)
  have step5 : ∀ e : F4, ![0, e, 0] ∈ V := by
    intro e
    have h := sub_mem (sub_mem (h1ω _ (step4 e)) (step4 e)) (step3 (F4.ω * e))
    have key : ∀ e : F4,
        a₁ActX 1 F4.ω ![e, 0, 0] - ![e, 0, 0] - ![0, 0, F4.ω * e] = ![0, e, 0] := by
      unfold a₁ActX
      simp only [bar_apply]
      decide
    rwa [key] at h
  rw [eq_top_iff]
  intro c _
  have hc : c = ![c 0, 0, 0] + ![0, c 1, 0] + ![0, 0, c 2] := by
    funext i
    fin_cases i <;> simp
  rw [hc]
  exact add_mem (add_mem (step4 _) (step5 _)) (step3 _)

theorem eq_bot_or_eq_top_of_cvec_invariant {V : AddSubgroup (Fin 3 → F4)}
    (hV : ∀ g ∈ K₁sub, ∀ a ∈ A₁sub, cvec (mat a) ∈ V → cvec (mat (g * a * g⁻¹)) ∈ V) :
    V = ⊥ ∨ V = ⊤ := by
  have hX : ∀ (α β : F4) (h : α * bar α = β + bar β), ∀ c ∈ V, a₁ActX α β c ∈ V := by
    intro α β h c hc
    have := hV _ (mem_sup_left (x₁SU_mem α β h)) _ (nfA₁_mem c) (by rwa [cvec_nfA₁])
    rwa [cvec_conj_x₁SU α β h (nfA₁_mem c), cvec_nfA₁] at this
  refine eq_bot_or_eq_top_of_closed (fun c hc => ?_) (hX 0 1 zero_one_rel)
    (hX 1 F4.ω one_omega_rel) (hX F4.ω F4.ω omega_omega_rel)
  have := hV _ (mem_sup_right (mem_zpowers uSU)) _ (nfA₁_mem c) (by rwa [cvec_nfA₁])
  rwa [cvec_conj_uSU (nfA₁_mem c), cvec_nfA₁] at this

theorem eq_ZX₄sub_or_eq_A₁sub_of_conj {R : Subgroup SU52} (hZR : ZX₄sub ≤ R) (hR : R ≤ A₁sub)
    (hK : ∀ g ∈ K₁sub, ∀ r ∈ R, g * r * g⁻¹ ∈ R) : R = ZX₄sub ∨ R = A₁sub := by
  have hneg : ∀ {r : SU52}, r ∈ A₁sub → cvec (mat r⁻¹) = -cvec (mat r) := fun {r} hr => by
    have := cvec_mul (inv_mem hr) hr
    rw [inv_mul_cancel, mat_one, cvec_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let V : AddSubgroup (Fin 3 → F4) :=
    { carrier := {c | ∃ r ∈ R, cvec (mat r) = c}
      zero_mem' := ⟨1, one_mem _, by rw [mat_one, cvec_one]⟩
      add_mem' := by
        rintro _ _ ⟨r, hr, rfl⟩ ⟨r', hr', rfl⟩
        exact ⟨r * r', mul_mem hr hr', cvec_mul (hR hr) (hR hr')⟩
      neg_mem' := by
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨r⁻¹, inv_mem hr, hneg (hR hr)⟩ }
  have hcl : ∀ {r a : SU52}, r ∈ A₁sub → a ∈ A₁sub → cvec (mat r) = cvec (mat a) →
      a ∈ R → r ∈ R := fun {r a} hr ha hra haR => by
    have h := (inv_mul_mem_ZX₄sub_iff ha hr).2 hra.symm
    rw [show r = a * (a⁻¹ * r) by group]
    exact mul_mem haR (hZR h)
  have hinv : ∀ g ∈ K₁sub, ∀ a ∈ A₁sub, cvec (mat a) ∈ V → cvec (mat (g * a * g⁻¹)) ∈ V := by
    rintro g hg a ha ⟨r, hr, hra⟩
    have hgz := comm_of_mem_CzSub (K₁sub_le_CzSub hg)
    refine ⟨g * r * g⁻¹, hK g hg r hr, ?_⟩
    have e1 := cvec_conj hgz (hR hr)
    have e2 := cvec_conj hgz ha
    rw [hra, e2] at e1
    have hl0 : mat g 0 0 ≠ 0 := by
      obtain ⟨⟨h0, -⟩, -⟩ := isBlk_of_comm_z hgz
      intro h00
      have hrow : ∀ j, mat g 0 j = 0 := fun j => by
        by_cases hj : j = 0
        · rw [hj, h00]
        · exact h0 j hj
      have hdet := (mem_SU52.1 g.2).2
      rw [Matrix.det_succ_row_zero] at hdet
      simp [hrow] at hdet
    exact (smul_right_injective (Fin 3 → F4) hl0 e1).symm
  rcases eq_bot_or_eq_top_of_cvec_invariant hinv with hV | hV
  · left
    refine le_antisymm (fun r hr => mem_ZX₄sub_of_cvec_eq_zero (hR hr) ?_) hZR
    have : cvec (mat r) ∈ V := ⟨r, hr, rfl⟩
    rw [hV] at this
    exact (AddSubgroup.mem_bot).1 this
  · right
    refine le_antisymm hR fun a ha => ?_
    have : cvec (mat a) ∈ V := by
      rw [hV]
      exact AddSubgroup.mem_top _
    obtain ⟨r, hr, hra⟩ := this
    exact hcl ha (hR hr) hra.symm hr

theorem eq_ZX₄sub_or_eq_A₁sub_of_normalizer {R : Subgroup SU52} (hZR : ZX₄sub ≤ R)
    (hR : R ≤ A₁sub) (hN : ∀ g ∈ normalizer (A₁sub : Set SU52), ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    R = ZX₄sub ∨ R = A₁sub :=
  eq_ZX₄sub_or_eq_A₁sub_of_conj hZR hR fun g hg =>
    hN g (normalizer_A₁sub ▸ K₁sub_le_CzSub hg)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
