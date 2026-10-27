module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommT
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

namespace SylowEnd

omit [Finite G] in
theorem le_normalizer_of_conj_mem {N D : Subgroup G} (h : ∀ n ∈ N, ∀ x ∈ D, n * x * n⁻¹ ∈ D) :
    N ≤ normalizer (D : Set G) := fun n hn =>
  mem_normalizer_iff.2 fun x => ⟨fun hx => h n hn x hx, fun hx => by
    have := h n⁻¹ (N.inv_mem hn) _ hx
    simpa [mul_assoc] using this⟩

structure DHyp (A Aa : Subgroup G) (t : G) (D : Subgroup G) : Prop where
  le_C : D ≤ Csub A Aa t
  comm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x
  Aa_le : Aa ≤ D
  sup_eq : D ⊔ zpowers t = Csub A Aa t
  disjoint : Disjoint D (zpowers t)
  card : Nat.card D = 2 ^ 12
  norm : ∀ n ∈ normalizer ((W5 A t : Subgroup G) : Set G), ∀ x ∈ D, n * x * n⁻¹ ∈ D
  BpC : ∀ r ∈ Bp A t, ∀ c ∈ Csub A Aa t, r * c * r⁻¹ * c⁻¹ ∈ Aa

end SylowEnd

open SylowEnd

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W

theorem ThCyc.normalizer_le_normalizer_Bp :
    normalizer ((W5 A t : Subgroup G) : Set G) ≤ normalizer (Bp A t : Set G) :=
  le_normalizer_of_conj_mem fun _ hn _ hx => H.Bp_normal W hn hx

theorem ThCyc.B_le_Bp : B ≤ Bp A t := fun x hx =>
  centralizer_W5_le_Bp A t ((H.mem_centralizer_W5_iff W).2 ⟨x, hx, 0, by simp⟩)

theorem ThCyc.Bp_le_of_le_normalizer {P : Subgroup G} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) : Bp A t ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsPGroup 2 ↥(P ⊔ Bp A t) :=
    hP.to_sup_of_normal_right' (H.isPGroup_Bp W) (hPN.trans (H.normalizer_le_normalizer_Bp W))
  have h := (hP.toSylow hPidx).is_maximal' hX le_sup_left
  rw [IsPGroup.toSylow_coe] at h
  exact h ▸ le_sup_right

theorem ThCyc.inf_Bp_eq : S ⊓ Bp A t = B := by
  refine le_antisymm (fun x hx => ?_) (le_inf (W.B_le_S) (H.B_le_Bp W))
  exact (W.mem_B_iff x (W.S_le hx.1)).2 fun a ha => (mem_centralizer_iff.1 hx.2.1 a ha).symm

variable {P : Subgroup G}

theorem ThCyc.exists_mul_of_mem_P (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) {p : G} (hp : p ∈ P) :
    ∃ n ∈ S, ∃ r ∈ Bp A t, p = n * r := by
  obtain ⟨-, g, -, -, -, -, hgt⟩ := H.exists_fusing_z W
  obtain ⟨n, hnL, -, r, hr, rfl⟩ := H.exists_mul_of_mem_normalizer W hgt (hPN hp)
  refine ⟨n, ?_, r, hr, rfl⟩
  have hnP : n ∈ P := by
    have := P.mul_mem hp (P.inv_mem (hBpP hr))
    simpa using this
  exact W.maximal (P ⊓ L) inf_le_right (hP.to_le inf_le_left) (le_inf hSP W.S_le) ⟨hnP, hnL⟩

theorem ThCyc.P_eq_sup (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) : P = S ⊔ Bp A t := by
  refine le_antisymm (fun p hp => ?_) (sup_le hSP hBpP)
  obtain ⟨n, hn, r, hr, rfl⟩ := H.exists_mul_of_mem_P W hP hSP hBpP hPN hp
  exact mul_mem_sup hn hr

theorem ThCyc.card_P_mul (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) :
    Nat.card P * 2 ^ 9 = 2 ^ 14 * Nat.card S := by
  have hSN : S ≤ normalizer (Bp A t : Set G) :=
    (H.S_le_normalizer W).trans (H.normalizer_le_normalizer_Bp W)
  have h := SylowEnd.card_sup_mul_card_inf hSN
  rw [← H.P_eq_sup W hP hSP hBpP hPN, H.inf_Bp_eq W, W.B_card, H.natCard_Bp_eq W] at h
  rw [h, mul_comm]

end

section D

variable {D : Subgroup G} (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
  (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)

include H W W2

theorem ThCyc.mem_Aa_of_mem_C_of_mem_L {x : G} (hx : x ∈ Csub A Aa t) (hxL : x ∈ L) : x ∈ Aa := by
  have hxB : x ∈ B := (W.mem_B_iff x hxL).2 fun a ha => (mem_centralizer_iff.1 hx.1.1 a ha).symm
  rcases W2.mem_Aa_or_mul_b W hxB with h | h
  · exact h
  · exfalso
    refine W2.b_not_mem_centralizer W (mem_centralizer_iff.2 fun y hy => ?_)
    have h1 : y * x = x * y := mem_centralizer_iff.1 hx.2 y hy
    have h2 : y * (x * b) = (x * b) * y := W2.Aa_comm y hy _ h
    have : y * b = b * y := by
      calc y * b = x⁻¹ * (x * y) * b := by group
        _ = x⁻¹ * (y * x) * b := by rw [h1]
        _ = x⁻¹ * (y * (x * b)) := by group
        _ = x⁻¹ * ((x * b) * y) := by rw [h2]
        _ = b * y := by group
    exact this

include hD

theorem ThCyc.D_le_Bp : D ≤ Bp A t := hD.le_C.trans inf_le_left

theorem ThCyc.S_le_normalizer_D : S ≤ normalizer (D : Set G) :=
  (H.S_le_normalizer W).trans (le_normalizer_of_conj_mem hD.norm)

theorem ThCyc.t_mem_normalizer : t ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
  Subgroup.le_normalizer (mem_sup_right (mem_zpowers t))

theorem ThCyc.t_not_mem_sup : t ∉ D ⊔ S := by
  intro h
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D S
    (H.S_le_normalizer_D W W2 hD)] at h
  obtain ⟨d, hd, s, hs, hds⟩ := h
  have hdC : d⁻¹ ∈ Csub A Aa t := (Csub A Aa t).inv_mem (hD.le_C hd)
  have htC : t ∈ Csub A Aa t := H.t_mem_inf_centralizer_Aa W W2
  have hsE : d⁻¹ * t = s := by rw [← hds]; group
  have hAa : d⁻¹ * t ∈ Aa :=
    H.mem_Aa_of_mem_C_of_mem_L W W2 ((Csub A Aa t).mul_mem hdC htC) (hsE ▸ W.S_le hs)
  have htD : t ∈ D := by
    have := D.mul_mem hd (hD.Aa_le hAa)
    simpa using this
  have h1 : t = 1 := disjoint_def.1 hD.disjoint htD (mem_zpowers t)
  have := H.order_two
  rw [h1, orderOf_one] at this
  omega

theorem ThCyc.t_mem_normalizer_sup : t ∈ normalizer ((D ⊔ S : Subgroup G) : Set G) := by
  have hct : ∀ q ∈ D ⊔ S, t * q * t⁻¹ ∈ D ⊔ S := by
    intro q hq
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D S
      (H.S_le_normalizer_D W W2 hD)] at hq
    obtain ⟨d, hd, s, hs, rfl⟩ := hq
    have hts : t * s = s * t := H.comm_of_mem_L (W.S_le hs)
    have hs' : t⁻¹ * s = s * t⁻¹ := (show Commute t s from hts).inv_left.eq
    have : t * (d * s) * t⁻¹ = (t * d * t⁻¹) * s := by
      calc t * (d * s) * t⁻¹ = t * d * (s * t⁻¹) := by group
        _ = t * d * (t⁻¹ * s) := by rw [← hs']
        _ = (t * d * t⁻¹) * s := by group
    rw [this]
    exact mul_mem_sup (hD.norm t (H.t_mem_normalizer W W2 hD) d hd) hs
  refine mem_normalizer_iff.2 fun q => ⟨hct q, fun hq => ?_⟩
  have := hct _ hq
  have htt : t * t = 1 := by rw [← sq]; exact H.sq_t
  have e : t * (t * q * t⁻¹) * t⁻¹ = q := by
    calc t * (t * q * t⁻¹) * t⁻¹ = (t * t) * q * (t * t)⁻¹ := by group
      _ = q := by rw [htt]; group
  rwa [e] at this

variable {P : Subgroup G}

theorem ThCyc.P_le_sup (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) :
    P ≤ (D ⊔ S) ⊔ zpowers t := by
  intro p hp
  obtain ⟨n, hn, r, hr, rfl⟩ := H.exists_mul_of_mem_P W hP hSP hBpP hPN hp
  have hS : S ≤ (D ⊔ S) ⊔ zpowers t := le_sup_right.trans le_sup_left
  have hD' : D ⊔ zpowers t ≤ (D ⊔ S) ⊔ zpowers t :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  refine mul_mem (hS hn) ?_
  obtain ⟨c, hc, hrc⟩ := H.exists_mem_inf_centralizer_Aa W W2 hr
  have hcm : c ∈ (D ⊔ S) ⊔ zpowers t := hD' (hD.sup_eq ▸ hc)
  rcases hrc with rfl | rfl
  · exact hcm
  · exact mul_mem hcm (hS (W.B_le_S W2.b_mem))

theorem ThCyc.P_le_normalizer_sup (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) :
    P ≤ normalizer ((D ⊔ S : Subgroup G) : Set G) := by
  have hz : zpowers t ≤ normalizer ((D ⊔ S : Subgroup G) : Set G) :=
    zpowers_le.2 (H.t_mem_normalizer_sup W W2 hD)
  exact (H.P_le_sup W W2 hD hP hSP hBpP hPN).trans
    (sup_le Subgroup.le_normalizer hz)

theorem ThCyc.exists_zpow_mul_mem_sup (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) {p : G} (hp : p ∈ P) :
    ∃ k : ℤ, (t ^ k)⁻¹ * p ∈ D ⊔ S := by
  have hz : zpowers t ≤ normalizer ((D ⊔ S : Subgroup G) : Set G) :=
    zpowers_le.2 (H.t_mem_normalizer_sup W W2 hD)
  have hp' := H.P_le_sup W W2 hD hP hSP hBpP hPN hp
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hz] at hp'
  obtain ⟨x, hx, q, hq, rfl⟩ := hp'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact ⟨k, by simpa using hq⟩

theorem ThCyc.exists_cyclic_sup (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) (htP : t ∈ P) :
    ∃ b0 ∈ P, ∀ p ∈ P, ∃ k : ℤ, (b0 ^ k)⁻¹ * p ∈ D ⊔ S :=
  ⟨t, htP, fun _ hp => H.exists_zpow_mul_mem_sup W W2 hD hP hSP hBpP hPN hp⟩

theorem ThCyc.exists_decomp_P (hP : IsPGroup 2 P) (hSP : S ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) {p : G} (hp : p ∈ P) :
    ∃ d ∈ D, ∃ s ∈ S, ∃ τ : G, (τ = 1 ∨ τ = t) ∧ p = d * s * τ := by
  obtain ⟨k, hk⟩ := H.exists_zpow_mul_mem_sup W W2 hD hP hSP hBpP hPN hp
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D S
    (H.S_le_normalizer_D W W2 hD)] at hk
  obtain ⟨d, hd, s, hs, hds⟩ := hk
  have hds' : d * s = (t ^ k)⁻¹ * p := hds
  have hp' : p = t ^ k * (d * s) := by rw [hds']; group
  rcases zpow_eq_one_or_self H.sq_t k with h | h
  · refine ⟨d, hd, s, hs, 1, Or.inl rfl, ?_⟩
    rw [hp', h]
    group
  · refine ⟨t * d * t⁻¹, hD.norm t (H.t_mem_normalizer W W2 hD) d hd, s, hs, t, Or.inr rfl, ?_⟩
    rw [hp', h]
    have hts : t * s = s * t := H.comm_of_mem_L (W.S_le hs)
    calc t * (d * s) = (t * d * t⁻¹) * (t * s) := by group
      _ = (t * d * t⁻¹) * (s * t) := by rw [hts]
      _ = t * d * t⁻¹ * s * t := by group

end D

end CFSG.EvenSporadicStandard.ThStd
