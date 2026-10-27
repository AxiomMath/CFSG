module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Br
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed

variable {Y : Type} [Group Y] {τ : Y}

private theorem z2a5_oTwoRes_le (H : Subgroup Y) : oTwoRes H ≤ H :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

private theorem z2a5_le_normalizer_oTwoRes (H : Subgroup Y) :
    H ≤ normalizer (oTwoRes H : Set Y) := by
  have key : ∀ c ∈ H, ∀ y ∈ oTwoRes H, c * y * c⁻¹ ∈ oTwoRes H := by
    intro c hc y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hc hx.1) (H.inv_mem hc), ?_⟩
      have : orderOf (c * x * c⁻¹) = orderOf x := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      rw [this]; exact hx.2
    | one => simp
    | mul a b _ _ ha hb =>
      have : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    | inv a _ ha =>
      have : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  intro c hc
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key c hc y, fun hy => ?_⟩
  have := key c⁻¹ (H.inv_mem hc) _ hy
  simpa [mul_assoc] using this

theorem z2a5_mul_self (h : Z2A5Hyp Y τ) : τ * τ = 1 := by
  have h1 := pow_orderOf_eq_one τ
  rw [h.1, sq] at h1
  exact h1

theorem z2a5_ne_one (h : Z2A5Hyp Y τ) : τ ≠ 1 := by
  intro h1
  have h2 := h.1
  rw [h1, orderOf_one] at h2
  omega

theorem z2a5_mem_cent (h : Z2A5Hyp Y τ) :
    τ ∈ centralizer (oTwoRes (centralizer ({τ} : Set Y)) : Set Y) := by
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.1 (z2a5_oTwoRes_le _ hx)

theorem z2a5_cent_le_norm (h : Z2A5Hyp Y τ) :
    centralizer ({τ} : Set Y) ≤ normalizer (oTwoRes (centralizer ({τ} : Set Y)) : Set Y) :=
  z2a5_le_normalizer_oTwoRes _

private theorem z2a5_tau_not_mem_range (h : Z2A5Hyp Y τ)
    (e : ↥(centralizer ({τ} : Set Y)) ≃* Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))) :
    τ ∉ (embA e).range := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rintro ⟨a, ha⟩
  apply zz_fst_ne sec128_A5_noncomm (z2a5_ne_one h) e
  have h1 : e.symm (1, a) = zz τ := Subtype.ext ha
  rw [← h1, MulEquiv.apply_symm_apply]

private theorem z2a5_cases_range (h : Z2A5Hyp Y τ)
    (e : ↥(centralizer ({τ} : Set Y)) ≃* Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))
    {d : Y} (hd : d ∈ centralizer ({τ} : Set Y)) :
    d ∈ (embA e).range ∨ ∃ x ∈ (embA e).range, d = τ * x := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases mem_range_or_mul sec128_A5_noncomm (z2a5_ne_one h) e hd with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨d * τ, h1, ?_⟩
    have hc : d * τ = τ * d := mem_centralizer_singleton_iff.1 hd
    rw [hc, ← mul_assoc, z2a5_mul_self h, one_mul]

theorem z2a5_oTwoRes_eq (h : Z2A5Hyp Y τ)
    (e : ↥(centralizer ({τ} : Set Y)) ≃* Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))) :
    oTwoRes (centralizer ({τ} : Set Y)) = (CFSG.EvenSporadicStandard.SolomonRed.embA e).range := by
  refine sec128_oTwoRes_cent (z2a5_mul_self h)
    ⟨(MonoidHom.ofInjective (embA_injective e)).symm⟩ (z2a5_tau_not_mem_range h e) ?_
    (fun d hd => z2a5_cases_range h e hd)
  rintro _ ⟨a, rfl⟩
  exact (mem_centralizer_singleton_iff.1 (embA_mem_cent e a)).symm

theorem z2a5_X_equiv (h : Z2A5Hyp Y τ) :
    Nonempty (↥(oTwoRes (centralizer ({τ} : Set Y))) ≃* ↥(alternatingGroup (Fin 5))) := by
  obtain ⟨e⟩ := h.2.1
  rw [z2a5_oTwoRes_eq h e]
  exact ⟨(MonoidHom.ofInjective (embA_injective e)).symm⟩

theorem z2a5_tau_not_mem (h : Z2A5Hyp Y τ) : τ ∉ oTwoRes (centralizer ({τ} : Set Y)) := by
  obtain ⟨e⟩ := h.2.1
  rw [z2a5_oTwoRes_eq h e]
  exact z2a5_tau_not_mem_range h e

theorem z2a5_cent_cent (h : Z2A5Hyp Y τ) {d : Y} (hd : d ∈ centralizer ({τ} : Set Y))
    (hdX : ∀ x ∈ oTwoRes (centralizer ({τ} : Set Y)), d * x = x * d) : d = 1 ∨ d = τ := by
  obtain ⟨e⟩ := h.2.1
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rw [z2a5_oTwoRes_eq h e] at hdX
  have hz1 := zz_snd sec128_A5_noncomm e
  have hz2 := zz_fst_ne sec128_A5_noncomm (z2a5_ne_one h) e
  set dd : ↥(centralizer ({τ} : Set Y)) := ⟨d, hd⟩ with hdd
  have hd1 : (e dd).2 = 1 := by
    refine eq_one_of_central_of_simple sec128_A5_noncomm fun a => ?_
    have h1 : d * embA e a = embA e a * d := hdX _ ⟨a, rfl⟩
    have h2 : dd * e.symm (1, a) = e.symm (1, a) * dd := Subtype.ext h1
    have h3 := congrArg e h2
    simp only [map_mul, MulEquiv.apply_symm_apply] at h3
    exact (congrArg Prod.snd h3).symm
  by_cases hg : (e dd).1 = 1
  · left
    have h3 : e dd = 1 := Prod.ext hg hd1
    have h4 : dd = 1 := e.injective (by rw [h3, map_one])
    exact congrArg Subtype.val h4
  · right
    have h3 : e dd = e (zz τ) := Prod.ext (z2_eq_of_ne_one hg hz2) (by rw [hd1, hz1])
    exact congrArg Subtype.val (e.injective h3)

theorem z2a5_exists_inv (h : Z2A5Hyp Y τ) :
    ∃ x ∈ oTwoRes (centralizer ({τ} : Set Y)), orderOf x = 2 := by
  obtain ⟨φ⟩ := z2a5_X_equiv h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(alternatingGroup (Fin 5))) 2
    (by rw [h60]; norm_num)
  refine ⟨(φ.symm a : Y), (φ.symm a).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]

end CFSG.OddStandard.SmallF3.Omega
