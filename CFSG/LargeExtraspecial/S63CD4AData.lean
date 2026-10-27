module

public import CFSG.LargeExtraspecial.S63CD4Class
public import Certificates.Certificate21112

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2 (allLt_spec)

theorem d4ACheck_eq_true : d4ACheck = true := Certificates.certificate21112

theorem parts_of_d4ACheckOn {Q L : EnumData} {irr : ℕ → List ℕ} {comms : List (ℕ × ℕ)}
    (h : d4ACheckOn Q L irr comms = true) :
    gensOK qGens = true ∧ gensOK lGens = true ∧ Q.ok qGens 512 = true ∧ Q.invOK 512 = true ∧
    L.ok lGens 504 = true ∧ L.invOK 504 = true ∧
    (∀ k < qGens.size, mulR qGens[k]! z0R = mulR z0R qGens[k]!) ∧
    (∀ k < lGens.size, mulR lGens[k]! z0R = mulR z0R lGens[k]!) ∧
    memR Q.El Q.idx z0R = true ∧
    (∀ i < 504, (L.El[i]! == oneR || !memR Q.El Q.idx L.El[i]!) = true) ∧
    (∀ k < lGens.size, ∀ i < 512, memR Q.El Q.idx (conjR lGens[k]! Q.El[i]!) = true) ∧
    (∀ i < 504, (!(mulR L.El[i]! L.El[i]! == oneR) || L.El[i]! == oneR ||
      (List.range 504).any fun c =>
        !(mulR L.El[i]! (conjI L.El[c]! L.El[L.inv[c]!]! L.El[i]!) == oneR) &&
          powRows 24 (mulR L.El[i]! (conjI L.El[c]! L.El[L.inv[c]!]! L.El[i]!)) 63 == oneR)
        = true) ∧
    (∀ j < 512, (Q.El[j]! == oneR || Q.El[j]! == z0R ||
      ((irr j).all (fun c => decide (c < 504)) &&
        coverOK Q.El Q.idx (subProds (irrList L (irr j) Q.El[j]!)))) = true) ∧
    (∀ p ∈ comms, p.1 < 512 ∧ p.2 < 504) ∧
    coverOK Q.El Q.idx (subProds (commList Q L comms)) = true ∧
    (∀ i < 512, ∀ k < qGens.size, conjI Q.El[i]! Q.El[Q.inv[i]!]! qGens[k]! = qGens[k]! ∨
      conjI Q.El[i]! Q.El[Q.inv[i]!]! qGens[k]! = mulR qGens[k]! z0R) ∧
    (∀ i < 504, (L.El[i]! == oneR || (List.range qGens.size).any fun k =>
      !(conjI L.El[i]! L.El[L.inv[i]!]! qGens[k]! == qGens[k]!) &&
        !(conjI L.El[i]! L.El[L.inv[i]!]! qGens[k]! == mulR qGens[k]! z0R)) = true) := by
  simp only [d4ACheckOn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    ⟨h14, h14'⟩⟩, h15⟩, h16⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun k hk => ?_, fun k hk => ?_, h9, fun i hi => allLt_spec h10 hi,
    fun k hk i hi => allLt_spec (allLt_spec h11 hk) hi, fun i hi => allLt_spec h12 hi,
    fun j hj => ?_, fun p hp => ?_, h14', fun i hi k hk => ?_, fun i hi => allLt_spec h16 hi⟩
  · simpa using allLt_spec h7 hk
  · simpa using allLt_spec h8 hk
  · have := allLt_spec h13 hj
    simpa only [Bool.or_eq_true, beq_iff_eq] using this
  · have := List.all_eq_true.1 h14 p hp
    simpa using this
  · have := allLt_spec (allLt_spec h15 hi) hk
    simpa using this

@[expose] noncomputable def d4Q : Subgroup trialityGroup8 := closure (genSet qGH qGens.size)

@[expose] noncomputable def d4L : Subgroup trialityGroup8 := closure (genSet lGH lGens.size)


theorem exists_d4ACheckOn : ∃ Q L irr comms, d4ACheckOn Q L irr comms = true :=
  ⟨_, _, _, _, d4ACheck_eq_true⟩

theorem qGens_hyp : ∀ k < qGens.size, RepE d4E qGens[k]! (qGH k) ∧ qGH k * qGH k = 1 := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  exact mul_self_of_gensOK (fun k hk => repE_qGens hk) (parts_of_d4ACheckOn h).1

theorem lGens_hyp : ∀ k < lGens.size, RepE d4E lGens[k]! (lGH k) ∧ lGH k * lGH k = 1 := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  exact mul_self_of_gensOK (fun k hk => repE_lGens hk) (parts_of_d4ACheckOn h).2.1

theorem card_d4Q : Nat.card d4Q = 512 := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  have h3 := (parts_of_d4ACheckOn h).2.2.1
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3
  rw [d4Q, card_of_enumOK d4E_injective qGens_hyp h3.1, h3.2]

theorem card_d4L : Nat.card d4L = 504 := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  have h5 := (parts_of_d4ACheckOn h).2.2.2.2.1
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h5
  rw [d4L, card_of_enumOK d4E_injective lGens_hyp h5.1, h5.2]

theorem comm_of_check {G : Array ℕ} {g : trialityGroup8} (hG : RepE d4E G g)
    (h : mulR G z0R = mulR z0R G) : g * d4z = d4z * g := by
  have h1 := repE_mul hG repE_z0R
  rw [h] at h1
  exact eq_of_repE d4E_injective h1 (repE_mul repE_z0R hG)

theorem d4Q_le_centralizer : d4Q ≤ centralizer ({d4z} : Set trialityGroup8) := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  have h7 := (parts_of_d4ACheckOn h).2.2.2.2.2.2.1
  rw [d4Q, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact comm_of_check (qGens_hyp k hk).1 (h7 k hk)

theorem d4L_le_centralizer : d4L ≤ centralizer ({d4z} : Set trialityGroup8) := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  have h8 := (parts_of_d4ACheckOn h).2.2.2.2.2.2.2.1
  rw [d4L, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact comm_of_check (lGens_hyp k hk).1 (h8 k hk)

theorem d4z_mem_d4Q : d4z ∈ d4Q := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, -, -, -, -, -, h9, -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3
  obtain ⟨hj, hQj⟩ := memR_spec h9
  obtain ⟨a, ha, hra⟩ := exists_of_enumOK (fun k hk => (qGens_hyp k hk).1) h3.1 _ hj
  rw [hQj] at hra
  rw [eq_of_repE d4E_injective repE_z0R hra]
  exact ha

theorem d4L_normalizes : ∀ l ∈ d4L, ∀ q ∈ d4Q, l * q * l⁻¹ ∈ d4Q := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, -, -, -, -, -, -, -, h11, -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3
  have hgen : ∀ k < lGens.size, ∀ q ∈ d4Q, lGH k * q * (lGH k)⁻¹ ∈ d4Q := by
    intro k hk q hq
    obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK qGens_hyp h3.1 hq
    have hc := repE_conjR (lGens_hyp k hk).1 hri (lGens_hyp k hk).2
    obtain ⟨hj, hQj⟩ := memR_spec (h11 k hk i (h3.2 ▸ hi))
    obtain ⟨a, ha, hra⟩ := exists_of_enumOK (fun k hk => (qGens_hyp k hk).1) h3.1 _ hj
    rw [hQj] at hra
    rw [eq_of_repE d4E_injective hc hra]
    exact ha
  intro l hl
  induction hl using closure_induction_left with
  | one => intro q hq; simpa using hq
  | mul_left x hx y _ ih =>
    obtain ⟨k, hk, rfl⟩ := hx
    intro q hq
    rw [show lGH k * y * q * (lGH k * y)⁻¹ = lGH k * (y * q * y⁻¹) * (lGH k)⁻¹ by group]
    exact hgen k hk _ (ih q hq)
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨k, hk, rfl⟩ := hx
    rw [show (lGH k)⁻¹ = lGH k from (eq_inv_of_mul_eq_one_left (lGens_hyp k hk).2).symm]
    intro q hq
    rw [show lGH k * y * q * (lGH k * y)⁻¹ = lGH k * (y * q * y⁻¹) * (lGH k)⁻¹ by group]
    exact hgen k hk _ (ih q hq)

theorem eq_one_of_mem_d4Q_d4L {x : trialityGroup8} (hxQ : x ∈ d4Q) (hxL : x ∈ d4L) : x = 1 := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, -, h5, -, -, -, -, h10, -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3 h5
  obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK lGens_hyp h5.1 hxL
  obtain ⟨j, hj, hrj⟩ := exists_mem_of_enumOK qGens_hyp h3.1 hxQ
  have hvi := ((enumOK_parts h5.1).2.2 i hi).1
  have hvj := ((enumOK_parts h3.1).2.2 j hj)
  have hij : L.El[i]! = Q.El[j]! := arr_eq_of_repE hvi hvj.1 hri hrj
  have h10' := h10 i (h5.2 ▸ hi)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h10'
  rcases h10' with h1 | h1
  · rw [h1] at hri
    exact eq_of_repE d4E_injective hri repE_one
  · exfalso
    rw [hij] at h1
    have : memR Q.El Q.idx Q.El[j]! = true := by
      simp only [memR, hvj.2.1, hj, decide_true, beq_self_eq_true, Bool.and_self]
    rw [this] at h1
    exact absurd h1 (by decide)

theorem exists_of_mem_centralizer_d4z
    {c : trialityGroup8}
    (hc : c ∈ centralizer ({d4z} : Set trialityGroup8)) :
    ∃ q ∈ d4Q, ∃ l ∈ d4L, c = q * l := by
  classical
  have : Finite trialityGroup8 := Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
  let f : d4Q × d4L → trialityGroup8 := fun p => (p.1 : trialityGroup8) * p.2
  have hf : Function.Injective f := by
    rintro ⟨q₁, l₁⟩ ⟨q₂, l₂⟩ h
    have h' : (q₁ : trialityGroup8) * l₁ = q₂ * l₂ := h
    set a₁ := q₁.1
    set a₂ := q₂.1
    set b₁ := l₁.1
    set b₂ := l₂.1
    have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
      calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
        _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h']
        _ = b₂ * b₁⁻¹ := by group
    have h2 := eq_one_of_mem_d4Q_d4L (d4Q.mul_mem (d4Q.inv_mem q₂.2) q₁.2)
      (h1 ▸ d4L.mul_mem l₂.2 (d4L.inv_mem l₁.2))
    have hq : q₁ = q₂ := Subtype.ext (inv_mul_eq_one.1 h2).symm
    have hl : l₁ = l₂ := by
      subst hq
      exact Subtype.ext (mul_left_cancel h')
    rw [hq, hl]
  have hsub : Set.range f ⊆ (centralizer ({d4z} : Set trialityGroup8) : Set trialityGroup8) := by
    rintro _ ⟨⟨q, l⟩, rfl⟩
    exact Subgroup.mul_mem _ (d4Q_le_centralizer q.2) (d4L_le_centralizer l.2)
  have heq : Set.range f = (centralizer ({d4z} : Set trialityGroup8) : Set trialityGroup8) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hf,
      Nat.card_prod, card_d4Q, card_d4L, SetLike.coe_sort_coe]
    exact card_centralizer_d4z_le.trans (by norm_num)
  rw [← SetLike.mem_coe, ← heq] at hc
  obtain ⟨⟨q, l⟩, rfl⟩ := hc
  exact ⟨q, q.2, l, l.2, rfl⟩

end CFSG.LargeExtraspecial.S63
