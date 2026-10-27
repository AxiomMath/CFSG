module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {T1 T2 : Subgroup G}

theorem sec8t84_wr_decomp (W : Sec8T84Wr G t T1 T2) {x : G} (hx : x ∈ T1 ⊔ T2) :
    ∃ a ∈ T1, ∃ b ∈ T2, x = a * b := by
  have hcoe : x = ((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩).1
      * ((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩).2 := by
    rw [← sec124SupEquiv_symm_coe W.comm W.inf ((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩),
      MulEquiv.symm_apply_apply]
  exact ⟨((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩).1.1,
    ((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩).1.2,
    ((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩).2.1,
    ((sec124SupEquiv W.comm W.inf) ⟨x, hx⟩).2.2, hcoe⟩

theorem sec8t84_wr_unique (W : Sec8T84Wr G t T1 T2) {a a' b b' : G} (ha : a ∈ T1)
    (ha' : a' ∈ T1) (hb : b ∈ T2) (hb' : b' ∈ T2) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have hm : a'⁻¹ * a = b' * b⁻¹ := by
    have h1 := congrArg (fun z => a'⁻¹ * z * b⁻¹) h
    simpa [mul_assoc] using h1
  have hbot : a'⁻¹ * a ∈ (⊥ : Subgroup G) := by
    rw [← W.inf]
    exact ⟨T1.mul_mem (T1.inv_mem ha') ha,
      by rw [hm]; exact T2.mul_mem hb' (T2.inv_mem hb)⟩
  rw [Subgroup.mem_bot] at hbot
  constructor
  · exact (inv_mul_eq_one.mp hbot).symm
  · have hb1 : b' * b⁻¹ = 1 := by rw [← hm]; exact hbot
    exact (mul_inv_eq_one.mp hb1).symm

theorem sec8t84_wr_conj_mem (W : Sec8T84Wr G t T1 T2) {x : G} (hx : x ∈ T1 ⊔ T2) :
    t * x * t⁻¹ ∈ T1 ⊔ T2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84_wr_decomp W hx
  have h1 : t * a * t⁻¹ ∈ T2 := W.swap1 a ha
  have h2 : t * b * t⁻¹ ∈ T1 := W.swap2 b hb
  have hmul : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [hmul]
  exact (T1 ⊔ T2).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)

theorem sec8t84_wr_mem_cent (W : Sec8T84Wr G t T1 T2) {x : G} :
    x ∈ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G) ↔ ∃ a ∈ T1, x = a * (t * a * t⁻¹) := by
  constructor
  · intro hx
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨hxT, hxC⟩ := hx
    obtain ⟨a, ha, b, hb, rfl⟩ := sec8t84_wr_decomp W hxT
    have hconj : t * (a * b) * t⁻¹ = a * b := by rw [← hxC]; group
    have hprod : (t * a * t⁻¹) * (t * b * t⁻¹) = a * b := by rw [← hconj]; group
    have ha' : t * a * t⁻¹ ∈ T2 := W.swap1 a ha
    have hb' : t * b * t⁻¹ ∈ T1 := W.swap2 b hb
    have hprod' : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b := by
      rw [W.comm (t * b * t⁻¹) hb' (t * a * t⁻¹) ha']; exact hprod
    obtain ⟨_, hb_eq⟩ := sec8t84_wr_unique W hb' ha ha' hb hprod'
    exact ⟨a, ha, by rw [hb_eq]⟩
  · rintro ⟨a, ha, rfl⟩
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right W.t_sq
    have hinner : t * (t * a * t⁻¹) * t⁻¹ = a := by
      rw [htinv]
      calc t * (t * a * t) * t = (t * t) * (a * (t * t)) := by group
        _ = a := by simp [W.t_sq]
    have hconj : t * (a * (t * a * t⁻¹)) * t⁻¹ = a * (t * a * t⁻¹) := by
      calc t * (a * (t * a * t⁻¹)) * t⁻¹
          = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by group
        _ = (t * a * t⁻¹) * a := by rw [hinner]
        _ = a * (t * a * t⁻¹) := (W.comm a ha (t * a * t⁻¹) (W.swap1 a ha)).symm
    have h2 : t * (a * (t * a * t⁻¹)) = a * (t * a * t⁻¹) * t := by
      calc t * (a * (t * a * t⁻¹))
          = (t * (a * (t * a * t⁻¹)) * t⁻¹) * t := by group
        _ = (a * (t * a * t⁻¹)) * t := by rw [hconj]
    exact ⟨Subgroup.mul_mem_sup ha (W.swap1 a ha),
      Subgroup.mem_centralizer_singleton_iff.mpr h2.symm⟩

theorem sec8t84_wr_diag_inj (W : Sec8T84Wr G t T1 T2) {a b : G} (ha : a ∈ T1) (hb : b ∈ T1)
    (h : a * (t * a * t⁻¹) = b * (t * b * t⁻¹)) : a = b := by
  exact (sec8t84_wr_unique W ha hb (W.swap1 a ha) (W.swap1 b hb) h).1

theorem sec8t84_wr_card_cent (W : Sec8T84Wr G t T1 T2) :
    Nat.card ↥((T1 ⊔ T2) ⊓ centralizer ({t} : Set G)) = Nat.card T1 := by
  let f : T1 → ↥((T1 ⊔ T2) ⊓ centralizer ({t} : Set G)) :=
    fun a => ⟨a * (t * a * t⁻¹), (sec8t84_wr_mem_cent W).mpr ⟨a, a.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact sec8t84_wr_diag_inj W a.2 b.2 (Subtype.ext_iff.mp hab)
    · intro y
      obtain ⟨a, ha, hx⟩ := (sec8t84_wr_mem_cent W).mp y.2
      exact ⟨⟨a, ha⟩, Subtype.ext hx.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end CFSG.OddStandard.SmallF3.Omega
