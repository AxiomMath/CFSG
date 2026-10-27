module

import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
public import CFSG.ClassicalInvolution.Asc77.AscT7K8

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7L

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

section Twins

omit [IsSimpleGroup G] in
theorem twin_le_trivialOnQuot (hΩ : HypOmegaMod p f Ω) {J J' : Subgroup G} {w : G}
    (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') (hz : IsUniqueInvolution J w)
    (hz' : IsUniqueInvolution J' w) : J ≤ trivialOnQuot J' := by
  have h4 := hΩ.omega4 J hJ J' hJ' hne
  have hmem : w ∈ J ⊓ J' := ⟨hz.mem, hz'.mem⟩
  have hz2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hdvd : 2 ∣ Nat.card ↥(J ⊓ J') := by
    have := Subgroup.orderOf_dvd_natCard (J ⊓ J') hmem
    rwa [hz2] at this
  have hpos : Nat.card ↥(J ⊓ J') ≠ 0 := Nat.card_pos.ne'
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(J ⊓ J')) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
  have heq : padicValNat 2 (Nat.card ↥(J ⊓ J')) = 1 := le_antisymm h4.1 h1
  exact le_trivialOnQuot_of_commutator_le ((h4.2 heq).trans inf_le_right)

omit [IsSimpleGroup G] in
theorem not_mem_tqMembers_of_mul (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {J : Subgroup G} (hJ : J ∈ Ω) {w a b c : G} (hw : IsUniqueInvolution J w) (haJ : a ∈ J)
    (ha4 : orderOf a = 4) (hb : b ∈ trivialOnQuot J) (hc : c = a * b) : J ∉ tqMembers Ω c := by
  intro hJt
  have hcJ : c ∈ trivialOnQuot J := hJt.2
  have ha : a ∈ trivialOnQuot J := by
    have : a = c * b⁻¹ := by rw [hc]; group
    rw [this]
    exact Subgroup.mul_mem _ hcJ (Subgroup.inv_mem _ hb)
  have hcomm : ∀ y ∈ J, ⁅a, y⁆ ∈ oddCoreOf J := fun y hy =>
    (mem_trivialOnQuot_iff.mp ha).2 y hy
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := T7A.isPGroup_zpowers_of_orderOf_four ha4
  rcases hΩ.center_two hp hq hJ hw a haJ ha2 hcomm with h | h
  · rw [h, orderOf_one] at ha4
    omega
  · rw [h] at ha4
    have : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw.sq) hw.ne_one
    omega

end Twins

section Alg

omit [Finite G] in
omit [IsSimpleGroup G] in
theorem alg_aux {u z e : G} (hu : u * u = 1) (cuz : u * z = z * u) (cue : u * e = e * u)
    (he : e * e = 1) :
    (z * e) * (u * e) = z * u ∧ (u * z * e) * (u * e) = z ∧ u * (u * z) = z ∧
      u * (z * e * (u * e)) = z := by
  have h1 : u * e * e = u := by rw [mul_assoc, he, mul_one]
  have h2 : (e * u) * e = u := by rw [← cue]; exact h1
  have i1 : (z * e) * (u * e) = z * u := by
    calc (z * e) * (u * e) = z * ((e * u) * e) := by simp only [mul_assoc]
      _ = z * u := by rw [h2]
  have i3 : u * (u * z) = z := by rw [← mul_assoc, hu, one_mul]
  refine ⟨i1, ?_, i3, ?_⟩
  · calc (u * z * e) * (u * e) = (u * z) * ((e * u) * e) := by simp only [mul_assoc]
      _ = (u * z) * u := by rw [h2]
      _ = u * (z * u) := by rw [mul_assoc]
      _ = u * (u * z) := by rw [cuz]
      _ = z := i3
  · rw [i1, ← cuz]
    exact i3

end Alg

section Frame

theorem exists_uFrame (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (R₂ R₂' : Subgroup G) (a₂ b₂ v' : G),
      conjSub g K ∈ tqMembers Ω u ∧ conjSub g K' ∈ tqMembers Ω u ∧
      IsSylow2In R₂ (exactCore u (conjSub g K)) ∧ IsSylow2In R₂' (exactCore u (conjSub g K')) ∧
      Commutes R₂ R₂' ∧ a₂ ∈ R₂ ∧ b₂ ∈ R₂' ∧ a₂ * a₂ = u * e ∧ b₂ * b₂ = u * e ∧
      (v' = a₂ * b₂ ∨ v' = a₂ * b₂ * (u * e)) ∧ (z = v' ∨ z = u * v') := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, haR, hbR', haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    T7K.exists_decomp hs hd
  have hu2' : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hz2 : z * z = 1 := hzK.sq
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := T7K.g_mem_normalizer hd
  have hge : g * e * g⁻¹ = e := by
    rw [T7K.comm_e hd hgN]
    group
  have hgze : g * (z * e) * g⁻¹ = u := by
    calc g * (z * e) * g⁻¹ = (g * z * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (u * e) * e := by rw [hd.hgt, hge]
      _ = u * (e * e) := by group
      _ = u := by rw [hd.he2, mul_one]
  have hRze : ∀ x ∈ R, x * (z * e) = (z * e) * x := by
    intro x hx
    have h1 : x * z = z * x := (hzK.commute_of_mem (hR.1 hx)).symm
    have h2 : x * e = e * x := T7K.comm_e hd (hRN hx)
    calc x * (z * e) = (x * z) * e := by rw [mul_assoc]
      _ = (z * x) * e := by rw [h1]
      _ = z * (x * e) := by rw [mul_assoc]
      _ = z * (e * x) := by rw [h2]
      _ = (z * e) * x := by rw [mul_assoc]
  have hR'ze : ∀ x ∈ R', x * (z * e) = (z * e) * x := by
    intro x hx
    have h1 : x * z = z * x := (hzK'.commute_of_mem (hR'.1 hx)).symm
    have h2 : x * e = e * x := T7K.comm_e hd (hR'N hx)
    calc x * (z * e) = (x * z) * e := by rw [mul_assoc]
      _ = (z * x) * e := by rw [h1]
      _ = z * (x * e) := by rw [mul_assoc]
      _ = z * (e * x) := by rw [h2]
      _ = (z * e) * x := by rw [mul_assoc]
  have hconjc : ∀ (R₀ : Subgroup G), (∀ x ∈ R₀, x * (z * e) = (z * e) * x) →
      conjSub g R₀ ≤ Subgroup.centralizer ({u} : Set G) := by
    intro R₀ hR₀ y hy
    rw [mem_conjSub_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hR₀ _ hy
    refine Eq.symm ?_
    calc u * y = (g * (z * e) * g⁻¹) * y := by rw [hgze]
      _ = g * ((z * e) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (z * e)) * g⁻¹ := by rw [← h1]
      _ = y * (g * (z * e) * g⁻¹) := by group
      _ = y * u := by rw [hgze]
  have hRc := hconjc R hRze
  have hR'c := hconjc R' hR'ze
  have hK₂ : conjSub g K ∈ tqMembers Ω u :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hu2').mpr
      ⟨hΩ.conjInvariant g K hKΩ, conjSub g R, hR.conj g, hRc⟩
  have hK₂' : conjSub g K' ∈ tqMembers Ω u :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hu2').mpr
      ⟨hΩ.conjInvariant g K' hK'Ω, conjSub g R', hR'.conj g, hR'c⟩
  have hS₂ : IsSylow2In (conjSub g R) (exactCore u (conjSub g K)) :=
    (isSylow2In_exactCore_iff hΩ hu2' (hΩ.conjInvariant g K hKΩ) hK₂.2).mpr ⟨hR.conj g, hRc⟩
  have hS₂' : IsSylow2In (conjSub g R') (exactCore u (conjSub g K')) :=
    (isSylow2In_exactCore_iff hΩ hu2' (hΩ.conjInvariant g K' hK'Ω) hK₂'.2).mpr
      ⟨hR'.conj g, hR'c⟩
  have hcomm : Commutes (conjSub g R) (conjSub g R') := by
    intro x hx y hy
    rw [mem_conjSub_iff] at hx hy
    have h1 := hRR' _ hx _ hy
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group
  have ha₂ : g * a * g⁻¹ ∈ conjSub g R := conj_mem_conjSub haR
  have hb₂ : g * b * g⁻¹ ∈ conjSub g R' := conj_mem_conjSub hbR'
  have ha₂sq : (g * a * g⁻¹) * (g * a * g⁻¹) = u * e := by
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [haa]
      _ = u * e := hd.hgt
  have hb₂sq : (g * b * g⁻¹) * (g * b * g⁻¹) = u * e := by
    calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hbb]
      _ = u * e := hd.hgt
  have hv1 : g * u * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by rw [hab]; group
  have hcuz : u * z = z * u := T7K.comm_uz hs hd
  have hcue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hv1B : g * u * g⁻¹ ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (T7K.mem_normalizer_B hs hd hgN) u).mp (T7K.u_mem_B z u e)
  have hinj : ∀ x y : G, g * x * g⁻¹ = g * y * g⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hzsup : z ∈ K ⊔ K' := Subgroup.mem_sup_left hzK.mem
  have heK : ∀ x : G, x ∈ K ⊔ K' → e = x → False := fun x hx hex =>
    T7K.e_not_mem_sup hs hd (hex ▸ hx)
  have hKe : u = z * e → False := fun h => by
    refine T7K.e_not_mem_sup hs hd ?_
    have : e = z * u := by rw [h, ← mul_assoc, hz2, one_mul]
    rw [this]
    exact (K ⊔ K').mul_mem hzsup hd.hu
  obtain ⟨i1, i2, i3, i4⟩ := alg_aux hd.hu2 hcuz hcue hd.he2
  rcases T7K.mem_cases_of_commuting_involutions hd.hu2 hz2 hd.he2 hcuz hcue
    (T7K.comm_e_of_mem_W hd hd.hzW) hv1B with h | h | h | h | h | h | h | h
  · exact absurd (hinj u 1 (by rw [h]; group)) hd.hu1
  · refine ⟨_, _, _, _, z, hK₂, hK₂', hS₂, hS₂', hcomm, ha₂, hb₂, ha₂sq, hb₂sq, Or.inl ?_,
      Or.inl rfl⟩
    rw [← hv1, h]
  · exact absurd (hKe (hinj u (z * e) (by rw [h, hgze]))) id
  · refine ⟨_, _, _, _, (g * a * g⁻¹) * (g * b * g⁻¹), hK₂, hK₂', hS₂, hS₂', hcomm, ha₂, hb₂,
      ha₂sq, hb₂sq, Or.inl rfl, Or.inr ?_⟩
    rw [← hv1, h]
    exact i3.symm
  · exact absurd (hinj u e (by rw [h, hge])) (fun h' => heK u hd.hu h'.symm)
  · refine ⟨_, _, _, _, ((g * a * g⁻¹) * (g * b * g⁻¹)) * (u * e), hK₂, hK₂', hS₂, hS₂', hcomm, ha₂,
      hb₂, ha₂sq, hb₂sq, Or.inr rfl, Or.inr ?_⟩
    rw [← hv1, h]
    exact i4.symm
  · exact absurd (hinj u z (by rw [h, hd.hgt])) hd.huz
  · refine ⟨_, _, _, _, ((g * a * g⁻¹) * (g * b * g⁻¹)) * (u * e), hK₂, hK₂', hS₂, hS₂', hcomm, ha₂,
      hb₂, ha₂sq, hb₂sq, Or.inr rfl, Or.inl ?_⟩
    rw [← hv1, h]
    exact i2.symm


omit [Finite G] [IsSimpleGroup G] in
theorem orderOf_four_of_sq {a w : G} (h : a * a = w) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    orderOf a = 4 := by
  have h2 : a ^ (2 ^ 1) ≠ 1 := by
    intro h'
    rw [pow_one, pow_two, h] at h'
    exact hw1 h'
  have h4 : a ^ (2 ^ (1 + 1)) = 1 := by
    calc a ^ (2 ^ (1 + 1)) = (a * a) * (a * a) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [h, hw2]
  have := orderOf_eq_prime_pow (p := 2) h2 h4
  simpa using this

omit [IsSimpleGroup G] in
theorem not_mem_tqMembers_u (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    K ∉ tqMembers Ω u ∧ K' ∉ tqMembers Ω u := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', a, b, r, hR, hR', hRR', hRN, hR'N, haR, hbR', haW, hbW, hab, haa, hbb, hrR, hr⟩ :=
    T7K.exists_decomp hs hd
  have ha4 : orderOf a = 4 := orderOf_four_of_sq haa hzK.ne_one hzK.sq
  have hb4 : orderOf b = 4 := orderOf_four_of_sq hbb hzK.ne_one hzK.sq
  have hbK' : b ∈ K' := hR'.1 hbR'
  have haK : a ∈ K := hR.1 haR
  have hbt : b ∈ trivialOnQuot K :=
    twin_le_trivialOnQuot hΩ hK'Ω hKΩ hs.hne hzK' hzK hbK'
  have hat : a ∈ trivialOnQuot K' :=
    twin_le_trivialOnQuot hΩ hKΩ hK'Ω hs.hne.symm hzK hzK' haK
  refine ⟨not_mem_tqMembers_of_mul hp hq hΩ hKΩ hzK haK ha4 hbt hab, ?_⟩
  exact not_mem_tqMembers_of_mul hp hq hΩ hK'Ω hzK' hbK' hb4 hat
    (by rw [hab]; exact hRR' a haR b hbR')

end Frame

end T7L

end CFSG.ClassicalInvolution.Asc77
