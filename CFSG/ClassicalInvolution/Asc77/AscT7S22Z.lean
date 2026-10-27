module

public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp51
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinZ
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected

namespace Hyp22Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hzK' (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K' z :=
  isUniqueInvolution_of_mem_twinSet h.hz h.hK'

theorem hzK₃ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : IsUniqueInvolution K₃ z :=
  isUniqueInvolution_of_mem_twinSet h.hz h.hK₃

theorem sq₁ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₁ = z :=
  T7A.sq_eq_of_orderOf_four h.hz h.hu₁.1 h.hu₁.2

theorem sq₂ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₂ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK' h.hu₂.1 h.hu₂.2

theorem sq₃ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : u₃ * u₃ = z :=
  T7A.sq_eq_of_orderOf_four h.hzK₃ h.hu₃.1 h.hu₃.2

theorem comm_z₁ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : z * u₁ = u₁ * z :=
  e189_commute_of_mem h.hz h.hu₁.1

theorem comm_z₂ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : z * u₂ = u₂ * z :=
  e189_commute_of_mem h.hzK' h.hu₂.1

theorem comm_z₃ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : z * u₃ = u₃ * z :=
  e189_commute_of_mem h.hzK₃ h.hu₃.1

theorem sq_12 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : (u₁ * u₂) * (u₁ * u₂) = 1 :=
  h.hB.2 _ T7B.mem_closure_fst

theorem sq_23 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : (u₂ * u₃) * (u₂ * u₃) = 1 :=
  h.hB.2 _ T7B.mem_closure_thd

theorem comm₁₂ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ = u₂ * u₁ :=
  T7B.comm_of_mul_self_eq_one h.sq₁ h.sq₂ h.hz.sq h.comm_z₁ h.sq_12

theorem comm₂₃ (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₃ = u₃ * u₂ :=
  T7B.comm_of_mul_self_eq_one h.sq₂ h.sq₃ h.hz.sq h.comm_z₂ h.sq_23

theorem eq_13 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ = z * ((u₁ * u₂) * (u₂ * u₃)) := by
  have h1 : (u₁ * u₂) * (u₂ * u₃) = u₁ * z * u₃ := by
    calc (u₁ * u₂) * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
      _ = u₁ * z * u₃ := by rw [h.sq₂]
  calc u₁ * u₃ = (z * z) * (u₁ * u₃) := by rw [h.hz.sq, one_mul]
    _ = z * (z * u₁) * u₃ := by group
    _ = z * (u₁ * z) * u₃ := by rw [h.comm_z₁]
    _ = z * ((u₁ * u₂) * (u₂ * u₃)) := by rw [h1]; group

theorem mem_B_13 (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    u₁ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [h.eq_13]
  exact Subgroup.mul_mem _ T7B.mem_closure_snd
    (Subgroup.mul_mem _ T7B.mem_closure_fst T7B.mem_closure_thd)

theorem isElemAbelian_B (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian 2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  have hsq : ∀ x ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), x * x = 1 := h.hB.2
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hab : ((a : G) * b) * ((a : G) * b) = 1 := hsq _ (Subgroup.mul_mem _ a.2 b.2)
    have h1 : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a a.2)
    have h2 : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b b.2)
    have h3 : (a : G) * b = ((a : G) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    rw [mul_inv_rev, h1, h2] at h3
    exact h3
  · rw [pow_two]
    exact hsq x hx

end Hyp22Setting

namespace T7S22

open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) {x y : G}
    (hx : x ∈ A) (hy : y ∈ B) : x * y = y * x := by
  have h1 := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem mul_ne_one_of_twins {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) {K₁ K₂ : Subgroup G}
    {z a b : G} (hK₁ : K₁ ∈ Ω) (hK₂ : K₂ ∈ Ω) (hne : K₁ ≠ K₂) (hz : IsUniqueInvolution K₁ z)
    (haK : a ∈ K₁) (hbK : b ∈ K₂) (hb4 : orderOf b = 4) : a * b ≠ 1 ∧ a * b ≠ z := by
  have key : b ∈ K₁ → False := by
    intro hb
    have hle : Subgroup.zpowers b ≤ K₁ ⊓ K₂ :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hb, hbK⟩)
    have hdvd : 4 ∣ Nat.card ↥(K₁ ⊓ K₂) := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hb4] at this
    have hpos : Nat.card ↥(K₁ ⊓ K₂) ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K₁ ⊓ K₂)) :=
      (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
    have h1 := (hΩ.omega4 K₁ hK₁ K₂ hK₂ hne).1
    omega
  refine ⟨fun h1 => key ?_, fun h1 => key ?_⟩
  · have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact K₁.inv_mem haK
  · have : b = a⁻¹ * z := by
      rw [← h1]
      group
    rw [this]
    exact K₁.mul_mem (K₁.inv_mem haK) hz.mem

omit [Finite G] in
theorem le_centralizer_of_classical {K : Subgroup G} {z : G} (hc : IsClassicalMember p f K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) :=
  isSubnormal_le hc.subnormal

theorem image_ne_of_pair {B K₁ K₂ : Subgroup G} {z a b : G}
    (hc₁ : IsClassicalMember p f K₁ z) (hc₂ : IsClassicalMember p f K₂ z)
    (hz : IsUniqueInvolution K₁ z) (hB : IsElemAbelian 2 B) (hzB : z ∈ B) (hz1 : z ≠ 1)
    (haK : a ∈ K₁) (hbK : b ∈ K₂) (hxB : a * b ∈ B) (hx1 : a * b ≠ 1) (hxz : a * b ≠ z)
    (hxC : a * b ∈ Subgroup.centralizer ({z} : Set G)) : modOdd z K₁ ≠ modOdd z K₂ := by
  intro heq
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_classical hc₁ haK
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_classical hc₂ hbK
  have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 hxB hx1 hxz hxC
  have huniq := TwinVertex.isUniqueInvolution_modOdd (c := z) hz hzC
  have hxmem : oddQuotMk z ⟨a * b, hxC⟩ ∈ modOdd z K₁ := by
    have h1 : oddQuotMk z ⟨a * b, hxC⟩ = oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨b, hbC⟩ := by
      rw [← map_mul]
      rfl
    rw [h1]
    refine (modOdd z K₁).mul_mem (oddQuotMk_mem_modOdd haK haC) ?_
    rw [heq]
    exact oddQuotMk_mem_modOdd hbK hbC
  have hxsq : oddQuotMk z ⟨a * b, hxC⟩ * oddQuotMk z ⟨a * b, hxC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a * b, hxC⟩ * ⟨a * b, hxC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB hxB)
    rw [this, map_one]
  rcases huniq.unique _ hxmem hxsq with h | h
  · apply hnot
    rw [h]
    exact (modOdd z (Subgroup.zpowers z)).one_mem
  · apply hnot
    rw [h]
    exact oddQuotMk_mem_modOdd (Subgroup.mem_zpowers z) hzC

theorem eq_or_eq_of_movedByAll {B K₁ K₂ : Subgroup G} {z a b : G} (hq : 5 ≤ p ^ f)
    (hc₁ : IsClassicalMember p f K₁ z) (hc₂ : IsClassicalMember p f K₂ z)
    (hB : IsElemAbelian 2 B) (hzB : z ∈ B) (hz1 : z ≠ 1) (haK : a ∈ K₁) (hbK : b ∈ K₂)
    (hxB : a * b ∈ B) (hx1 : a * b ≠ 1) (hxz : a * b ≠ z)
    (hxC : a * b ∈ Subgroup.centralizer ({z} : Set G)) {L : Subgroup (OddQuot z)}
    (hL : CFSG.IsComponent L) (hmov : MovedByAll B z L) :
    L = modOdd z K₁ ∨ L = modOdd z K₂ := by
  by_contra hne
  replace hne := not_or.mp hne
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_classical hc₁ haK
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_classical hc₂ hbK
  have hK₁c : CFSG.IsComponent (modOdd z K₁) :=
    (CFSG.isComponent_iff_open _).mpr (isComponentOf_modOdd hc₁ hq)
  have hK₂c : CFSG.IsComponent (modOdd z K₂) :=
    (CFSG.isComponent_iff_open _).mpr (isComponentOf_modOdd hc₂ hq)
  have hc₁' : ⁅L, modOdd z K₁⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL hK₁c).resolve_left hne.1
  have hc₂' : ⁅L, modOdd z K₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL hK₂c).resolve_left hne.2
  obtain ⟨y, hyL, hy⟩ := hmov (oddQuotMk z ⟨a * b, hxC⟩) (oddQuotMk_mem_modOdd hxB hxC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 hxB hx1 hxz hxC)
  apply hy
  have e1 : y * oddQuotMk z ⟨a, haC⟩ = oddQuotMk z ⟨a, haC⟩ * y :=
    commute_of_commutator_eq_bot hc₁' hyL (oddQuotMk_mem_modOdd haK haC)
  have e2 : y * oddQuotMk z ⟨b, hbC⟩ = oddQuotMk z ⟨b, hbC⟩ * y :=
    commute_of_commutator_eq_bot hc₂' hyL (oddQuotMk_mem_modOdd hbK hbC)
  have h1 : oddQuotMk z ⟨a * b, hxC⟩ = oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨b, hbC⟩ := by
    rw [← map_mul]
    rfl
  rw [h1]
  calc oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨b, hbC⟩ * y
      = oddQuotMk z ⟨a, haC⟩ * (oddQuotMk z ⟨b, hbC⟩ * y) := mul_assoc _ _ _
    _ = oddQuotMk z ⟨a, haC⟩ * (y * oddQuotMk z ⟨b, hbC⟩) := by rw [e2]
    _ = (oddQuotMk z ⟨a, haC⟩ * y) * oddQuotMk z ⟨b, hbC⟩ := (mul_assoc _ _ _).symm
    _ = (y * oddQuotMk z ⟨a, haC⟩) * oddQuotMk z ⟨b, hbC⟩ := by rw [e1]
    _ = y * (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨b, hbC⟩) := mul_assoc _ _ _

end T7S22

theorem hyp22Hyp51z (p f : ℕ) [Fact p.Prime] : Hyp22Hyp51z p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ := h.stand.hyp
  have hKΩ : K ∈ Ω := h.stand.mem
  have hK'Ω : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hz := h.hz
  have hzK' := h.hzK'
  have hzK₃ := h.hzK₃
  have hc₁ : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hKΩ hz
  have hc₂ : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hc₃ : IsClassicalMember p f K₃ z := isClassicalMember_of_twin hΩ hK₃Ω hzK₃
  have hBab := h.isElemAbelian_B
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := T7B.mem_closure_snd
  have hxB12 : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := T7B.mem_closure_fst
  have hxB23 : u₂ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := T7B.mem_closure_thd
  have hxB13 := h.mem_B_13
  have hC12 : u₁ * u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq
  have hC23 : u₂ * u₃ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)).eq
  have hC13 : u₁ * u₃ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₃.symm : Commute u₃ z)).eq
  obtain ⟨h12₁, h12z⟩ := T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω h.hne.symm hz h.hu₁.1 h.hu₂.1
    h.hu₂.2
  obtain ⟨h23₁, h23z⟩ := T7S22.mul_ne_one_of_twins hΩ hK'Ω hK₃Ω h.hK₃K'.symm hzK' h.hu₂.1
    h.hu₃.1 h.hu₃.2
  obtain ⟨h13₁, h13z⟩ := T7S22.mul_ne_one_of_twins hΩ hKΩ hK₃Ω h.hK₃K.symm hz h.hu₁.1
    h.hu₃.1 h.hu₃.2
  have hz1 : z ≠ 1 := hz.ne_one
  have n12 := T7S22.image_ne_of_pair hc₁ hc₂ hz hBab hzB hz1 h.hu₁.1 h.hu₂.1 hxB12 h12₁ h12z hC12
  have n23 := T7S22.image_ne_of_pair hc₂ hc₃ hzK' hBab hzB hz1 h.hu₂.1 h.hu₃.1 hxB23 h23₁ h23z
    hC23
  have n13 := T7S22.image_ne_of_pair hc₁ hc₃ hz hBab hzB hz1 h.hu₁.1 h.hu₃.1 hxB13 h13₁ h13z hC13
  generalize Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) = B at hBab hzB hxB12 hxB23 hxB13 ⊢
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll B z L → False := by
    intro L hL hmov
    have e12 := T7S22.eq_or_eq_of_movedByAll hq hc₁ hc₂ hBab hzB hz1 h.hu₁.1 h.hu₂.1 hxB12
      h12₁ h12z hC12 hL hmov
    have e23 := T7S22.eq_or_eq_of_movedByAll hq hc₂ hc₃ hBab hzB hz1 h.hu₂.1 h.hu₃.1 hxB23
      h23₁ h23z hC23 hL hmov
    have e13 := T7S22.eq_or_eq_of_movedByAll hq hc₁ hc₃ hBab hzB hz1 h.hu₁.1 h.hu₃.1 hxB13
      h13₁ h13z hC13 hL hmov
    rcases e12 with rfl | rfl
    · rcases e23 with h2 | h2
      · exact n12 h2
      · exact n13 h2
    · rcases e13 with h3 | h3
      · exact n12 h3.symm
      · exact n23 h3
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end CFSG.ClassicalInvolution.Asc77
