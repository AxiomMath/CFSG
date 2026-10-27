module

public import CFSG.ClassicalInvolution.Asc77.AscT7CRecog
public import CFSG.ClassicalInvolution.Asc77.AscT7ASetup
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23
public import CFSG.ClassicalInvolution.Asc77.AscT7CHyp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7C

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_of_isSylow2In (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K R : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K) (hz : IsUniqueInvolution K z) : z ∈ R := by
  obtain ⟨x, hx, o⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  rw [← T7A.sq_eq_of_orderOf_four hz (hR.1 hx) o]
  exact R.mul_mem hx hx

theorem exists_normal_zpowers_order_four (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K R : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hR : IsSylow2In R K) (hz : IsUniqueInvolution K z) :
    ∃ u ∈ R, orderOf u = 4 ∧ ∀ r ∈ R, r * u * r⁻¹ ∈ Subgroup.zpowers u := by
  have hzR : z ∈ R := mem_of_isSylow2In hp hΩ hK hR hz
  have huniq : IsUniqueInvolution R z :=
    ⟨hzR, hz.ne_one, hz.sq, fun y hy hy2 => hz.unique y (hR.1 hy) hy2⟩
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨A, hAR, hAcyc, hA4, hAinv⟩ := exists_invariant_cyclic_order_four hR.2.1 le_rfl
    (fun q hq => conjSub_eq_self_of_mem hq) huniq (by omega)
  obtain ⟨g, hg⟩ := hAcyc.exists_generator
  have hgord : orderOf g = 4 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hA4
  refine ⟨(g : G), hAR g.2, by rw [Subgroup.orderOf_coe]; exact hgord, fun r hr => ?_⟩
  have h1 : r * (g : G) * r⁻¹ ∈ conjSub r A := conj_mem_conjSub g.2
  rw [hAinv r hr] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, h1⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_conj_mem_sylow_ne [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
  by_contra hcon
  push Not at hcon
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hord : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hzord
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hzc s s.2)
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hord hcon
  have hoc : CFSG.oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exfalso
      exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hzord
        (by rw [h]; exact Subgroup.mem_top z)
  have hzcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec g
    rw [hoc, Subgroup.mem_bot] at hk
    subst hk
    rw [mul_one]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have := T7C.center_eq_bot_of_exists_not_commute hnab
  rw [this, Subgroup.mem_bot] at hzcen
  exact hz1 hzcen

end T7C

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_RS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G),
        (R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)) ∧
        (R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)) ∧
        ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'

variable {p f}

theorem c25_setup_of (h : C25_RS p f) : C25_setup p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  obtain ⟨S, R, R', hR, hR', hRS⟩ := h G Ω K K' z hs.setting W hW hzW hE4
  have hst : AscStand p f Ω K := hs.1.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.1.hK'.1
  have hz : IsUniqueInvolution K z := hs.1.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.1.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hR.1 hR.2.1
  have hR'syl : IsSylow2In R' K' := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hR'.1 hR'.2.1
  have hzR : z ∈ R := T7C.mem_of_isSylow2In hp hΩ hK hRsyl hz
  have hzR' : z ∈ R' := T7C.mem_of_isSylow2In hp hΩ hK' hR'syl hz'
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := by
    intro s hs'
    have h1 : conjSub s R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR.1 s
    have h2 : conjSub s R ≤ (S : Subgroup G) := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs' (hR.2.2 hr))
        ((S : Subgroup G).inv_mem hs')
    have hconj : s * z * s⁻¹ ∈ conjSub s R := conj_mem_conjSub hzR
    have hsq : (s * z * s⁻¹) * (s * z * s⁻¹) = 1 := by
      calc (s * z * s⁻¹) * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    have hne : s * z * s⁻¹ ≠ 1 := by
      intro he
      apply hz.ne_one
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [he]; group
    have hzz : s * z * s⁻¹ = z := by
      rcases hRS _ h1 h2 with e | e
      · rw [e] at hconj
        exact (hz.unique _ (hR.2.1 hconj) hsq).resolve_left hne
      · rw [e] at hconj
        exact (hz'.unique _ (hR'.2.1 hconj) hsq).resolve_left hne
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [hzz]
  have hnab : ∃ a b : G, a * b ≠ b * a := T7C.exists_not_commute_of_stand hst
  obtain ⟨g, hgS, hgne⟩ := T7C.exists_conj_mem_sylow_ne hnab S (hR.2.2 hzR) hzS hz.sq hz.ne_one
  obtain ⟨u₁, hu₁R, o₁, hu₁n⟩ := T7C.exists_normal_zpowers_order_four hp hΩ hK hRsyl hz
  obtain ⟨u₂, hu₂R, o₂, hu₂n⟩ := T7C.exists_normal_zpowers_order_four hp hΩ hK' hR'syl hz'
  exact ⟨S, R, R', g⁻¹ * z * g, u₁, u₂,
    Hyp25Data.hyp25 ⟨hW, hzW, hE4, hR, hR', hRS, hzS, ⟨hgS, hgne, g⁻¹, by simp⟩,
      ⟨hu₁R, o₁, hu₁n⟩, ⟨hu₂R, o₂, hu₂n⟩⟩ hs⟩

end CFSG.ClassicalInvolution.Asc77
