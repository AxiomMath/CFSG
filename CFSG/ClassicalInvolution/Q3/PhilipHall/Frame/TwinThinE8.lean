module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinTail

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open scoped Pointwise

namespace TwinThin

namespace E8

variable {G : Type} [Group G] [Finite G]

abbrev conjAct (S E : Subgroup G) (h : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E) :
    MulAction ↥S ↥E where
  smul s e := ⟨(s : G) * e * (s : G)⁻¹, h s s.2 e e.2⟩
  one_smul e := Subtype.ext (by
    show ((1 : ↥S) : G) * (e : G) * ((1 : ↥S) : G)⁻¹ = e
    simp)
  mul_smul a b e := Subtype.ext (by
    show ((a * b : ↥S) : G) * (e : G) * ((a * b : ↥S) : G)⁻¹ =
      (a : G) * ((b : G) * (e : G) * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc])

@[expose] noncomputable def twist {X E : Subgroup G} (hE : E8Struct X E) {s : G} (hsX : s ∈ X) :
    ↥E →* ↥E :=
  MonoidHom.mk' (fun e => ⟨(e : G) * (s * (e : G) * s⁻¹),
      E.mul_mem e.2 (hE.normal s hsX e e.2)⟩) (by
    intro a b
    apply Subtype.ext
    have h1 : (s * (a : G) * s⁻¹) * (b : G) = (b : G) * (s * (a : G) * s⁻¹) :=
      comm_of_sq hE.sq (hE.normal s hsX a a.2) b.2
    have key : (a : G) * (b : G) * (s * ((a : G) * (b : G)) * s⁻¹) =
        ((a : G) * (s * (a : G) * s⁻¹)) * ((b : G) * (s * (b : G) * s⁻¹)) := by
      calc (a : G) * (b : G) * (s * ((a : G) * (b : G)) * s⁻¹)
          = (a : G) * ((b : G) * (s * (a : G) * s⁻¹)) * (s * (b : G) * s⁻¹) := by group
        _ = (a : G) * ((s * (a : G) * s⁻¹) * (b : G)) * (s * (b : G) * s⁻¹) := by rw [← h1]
        _ = _ := by group
    simpa [Subgroup.coe_mul] using key)

theorem twist_apply {X E : Subgroup G} (hE : E8Struct X E) {s : G} (hsX : s ∈ X) (e : ↥E) :
    ((twist hE hsX e : ↥E) : G) = (e : G) * (s * (e : G) * s⁻¹) := rfl

theorem fixed_card_four {X E : Subgroup G} (hE : E8Struct X E) {s : G} (hsX : s ∈ X)
    (hsE : s ∉ E) (hs2 : s * s ∈ E) :
    Nat.card {e : ↥E // s * (e : G) * s⁻¹ = e} = 4 := by
  set ψ := twist hE hsX with hψ
  have hker : ∀ e : ↥E, e ∈ ψ.ker ↔ s * (e : G) * s⁻¹ = e := by
    intro e
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (e : G) * (s * (e : G) * s⁻¹) = 1 := congrArg Subtype.val h
      have h2 := hE.sq e e.2
      have : (s * (e : G) * s⁻¹) = (e : G) := by
        calc (s * (e : G) * s⁻¹) = (e : G)⁻¹ * ((e : G) * (s * (e : G) * s⁻¹)) := by group
          _ = (e : G)⁻¹ := by rw [h1, mul_one]
          _ = e := inv_eq_of_mul_eq_one_right h2
      exact this
    · intro h
      apply Subtype.ext
      show (e : G) * (s * (e : G) * s⁻¹) = 1
      rw [h]
      exact hE.sq e e.2
  have hrange : ψ.range ≤ ψ.ker := by
    rintro _ ⟨e, rfl⟩
    rw [hker]
    set f : G := s * (e : G) * s⁻¹ with hf
    have hfE : f ∈ E := hE.normal s hsX e e.2
    have hs2e : ∀ x ∈ E, s * s * x * (s * s)⁻¹ = x := fun x hx => by
      have := comm_of_sq hE.sq hs2 hx
      calc s * s * x * (s * s)⁻¹ = (s * s * x) * (s * s)⁻¹ := rfl
        _ = x * (s * s) * (s * s)⁻¹ := by rw [this]
        _ = x := by group
    have e1 : s * (((twist hE hsX e : ↥E)) : G) * s⁻¹ = f * (s * f * s⁻¹) := by
      rw [twist_apply, hf]
      group
    have e2 : s * f * s⁻¹ = e := by
      have := hs2e e e.2
      rw [hf]
      calc s * (s * (e : G) * s⁻¹) * s⁻¹ = s * s * e * (s * s)⁻¹ := by group
        _ = e := this
    rw [e1, e2]
    exact comm_of_sq hE.sq hfE e.2
  have hprod := Subgroup.card_ker_mul_card_range ψ
  rw [hE.card] at hprod
  have hle : Nat.card ψ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrange
  have hdvd : Nat.card ψ.ker ∣ 8 := by
    rw [← hE.card]
    exact Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card ψ.ker = 4 := by
    have hmem : Nat.card ψ.ker ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [h] at hprod hle; omega
    · rw [h] at hprod hle; omega
    · exact h
    · exfalso
      have htop : ψ.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hE.card])
      apply hsE
      refine hE.cent s hsX fun e he => ?_
      have : (⟨e, he⟩ : ↥E) ∈ ψ.ker := by rw [htop]; trivial
      have h1 := (hker _).mp this
      have h2 : s * e * s⁻¹ = e := h1
      calc s * e = s * e * s⁻¹ * s := by group
        _ = e * s := by rw [h2]
  rw [← h4]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun e => (hker e).symm)

theorem le_of_card_thirtyTwo {X E S : Subgroup G} (hE : E8Struct X E) (hSX : S ≤ X)
    (hS : Nat.card S = 32) (hsq : ∀ s ∈ S, s * s ∈ E) : E ≤ S := by
  classical
  have hnorm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E := fun s hs e he => hE.normal s (hSX hs) e he
  let _ : MulAction ↥S ↥E := conjAct S E hnorm
  have _ : Fintype ↥S := Fintype.ofFinite _
  have _ : Fintype ↥E := Fintype.ofFinite _
  have _ : ∀ s : ↥S, Fintype (MulAction.fixedBy ↥E s) := fun s => Fintype.ofFinite _
  have _ : Fintype (MulAction.orbitRel.Quotient ↥S ↥E) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥S ↥E
  have hSc : Fintype.card ↥S = 32 := by rw [← Nat.card_eq_fintype_card, hS]
  have hEc : Fintype.card ↥E = 8 := by rw [← Nat.card_eq_fintype_card, hE.card]
  have hfix : ∀ s : ↥S, Fintype.card (MulAction.fixedBy ↥E s) =
      if (s : G) ∈ E then 8 else 4 := by
    intro s
    by_cases hsE : (s : G) ∈ E
    · simp only [hsE, ↓reduceIte]
      rw [← hEc]
      apply Fintype.card_of_subtype (Finset.univ : Finset ↥E)
      intro e
      simp only [Finset.mem_univ, true_iff, MulAction.mem_fixedBy]
      apply Subtype.ext
      show (s : G) * (e : G) * (s : G)⁻¹ = e
      rw [comm_of_sq hE.sq hsE e.2]
      group
    · simp only [hsE, ↓reduceIte]
      rw [← Nat.card_eq_fintype_card]
      rw [← fixed_card_four hE (hSX s.2) hsE (hsq s s.2)]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
      rw [MulAction.mem_fixedBy]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
  have hsum : (∑ s : ↥S, Fintype.card (MulAction.fixedBy ↥E s)) =
      ((Finset.univ : Finset ↥S).filter fun s : ↥S => (s : G) ∈ E).card * 8 +
        ((Finset.univ : Finset ↥S).filter fun s : ↥S => ¬ (s : G) ∈ E).card * 4 := by
    simp only [hfix]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  set w := ((Finset.univ : Finset ↥S).filter fun s : ↥S => (s : G) ∈ E).card with hw
  have hw2 : ((Finset.univ : Finset ↥S).filter fun s : ↥S => ¬ (s : G) ∈ E).card = 32 - w := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ↥S))
      (fun s : ↥S => (s : G) ∈ E)
    rw [Finset.card_univ, hSc] at this
    rw [hw]
    omega
  have hwle : w ≤ 32 := by
    have := Finset.card_filter_le (Finset.univ : Finset ↥S) fun s : ↥S => (s : G) ∈ E
    rw [Finset.card_univ, hSc] at this
    exact this
  have hdiv : 32 ∣ 128 + 4 * w := by
    refine ⟨Fintype.card (Quotient (MulAction.orbitRel ↥S ↥E)), ?_⟩
    have := hB
    rw [hsum, hw2, hSc] at this
    omega
  let ι : {s : ↥S // (s : G) ∈ E} → ↥E := fun s => ⟨(s.1 : G), s.2⟩
  have hι : Function.Injective ι := by
    intro a b h
    have h' := congrArg (Subtype.val : ↥E → G) h
    exact Subtype.ext (Subtype.ext h')
  have hwcard : w = Nat.card {s : ↥S // (s : G) ∈ E} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hw8 : w ≤ 8 := by
    rw [hwcard]
    calc Nat.card {s : ↥S // (s : G) ∈ E} ≤ Nat.card ↥E := Nat.card_le_card_of_injective ι hι
      _ = 8 := hE.card
  have hwpos : 0 < w := by
    rw [hwcard]
    exact Nat.card_pos_iff.mpr ⟨⟨⟨1, S.one_mem⟩, E.one_mem⟩, inferInstance⟩
  have hw8' : w = 8 := by omega
  have hbij : Function.Bijective ι := by
    refine hι.bijective_of_nat_card_le ?_
    rw [hE.card, ← hwcard, hw8']
  intro e he
  obtain ⟨s, hs⟩ := hbij.2 ⟨e, he⟩
  have : (s.1 : G) = e := congrArg Subtype.val hs
  rw [← this]
  exact s.1.2

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

omit [Finite G] in
theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ a ∈ A, b * a * b⁻¹ = a := fun a ha => by
    rw [← h a ha b hb]; group
  constructor
  · intro hx
    rw [key x hx]
    exact hx
  · intro hx
    have h1 := h _ hx b hb
    have h2 : b * x = b * (b * x * b⁻¹) := by
      calc b * x = (b * x * b⁻¹) * b := by group
        _ = b * (b * x * b⁻¹) := h1
    rw [mul_left_cancel h2]
    exact hx

theorem pow_four_of_card_eight {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {N : Subgroup G}
    (hN : N ∈ Ω) (h8 : Nat.card N = 8) {x : G} (hxN : x ∈ N) : x * x * (x * x) = 1 := by
  have hdvd : orderOf x ∣ 8 := by
    rw [← h8]
    exact Subgroup.orderOf_dvd_natCard N hxN
  have hne8 : orderOf x ≠ 8 := by
    intro h
    obtain ⟨-, P, hPN, hPnc⟩ := hΩ.omega1 N hN
    have hzN : Subgroup.zpowers x = N := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxN) ?_
      rw [Nat.card_zpowers, h, h8]
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : (a : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 a.2
    have hb : (b : G) ∈ Subgroup.zpowers x := hzN ▸ hPN.1 b.2
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    show (a : G) * b = b * a
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have h4 : orderOf x ∣ 4 := by
    have hmem : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]
    · exact absurd h hne8
  have := orderOf_dvd_iff_pow_eq_one.mp h4
  calc x * x * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := this

end E8

section Setting

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem le_sup_of_e8 {E : Subgroup G} (hE : E8Struct (conjSub g (piGen π)) E) : E ≤ K ⊔ K' := by
  have hΩ := S.hs.hyp
  have hK' := S.hK'
  obtain ⟨hK'Ω, z', hz1, hz2⟩ := hK'
  have hzz : z = z' := S.hz.eq hz1
  rw [← hzz] at hz2
  have hKne : K ≠ K' := S.hne.symm
  have hcomm := twin_commute hΩ S.hK hK'Ω hKne S.hz hz2 (S.hs.two K S.hK)
  have hinf := twin_inf_eq hΩ S.hK hK'Ω hKne S.hz hz2 (S.hs.two K S.hK)
  have h8 := S.card8
  have hz2ord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact S.hz.sq) S.hz.ne_one
  have hcardinf : Nat.card ↥(K ⊓ K') = 2 := by rw [hinf, Nat.card_zpowers, hz2ord]
  have hnormK' : K' ≤ Subgroup.normalizer (K : Set G) := E8.le_normalizer_of_commute hcomm
  have hcardS : Nat.card ↥(K ⊔ K') = 32 := by
    have := E8.card_sup_mul_card_inf hnormK'
    rw [hcardinf, h8 K S.hK, h8 K' hK'Ω] at this
    omega
  have hSX : K ⊔ K' ≤ conjSub g (piGen π) :=
    sup_le S.hKX (TwinSecXg.twin_le S.hos S.hK S.hπ S.hH1 S.hg S.hK')
  have hzE : z ∈ E := by
    obtain ⟨Q, hQX, hQn, hQ2, hzQ⟩ := S.exists_normalTwo S.mem_fam_self S.hz
    exact hE.core Q hQX hQn hQ2 hzQ
  have hsqK : ∀ a ∈ K, a * a ∈ E := fun a ha => by
    have h4 := E8.pow_four_of_card_eight hΩ S.hK (h8 K S.hK) ha
    rcases S.hz.unique (a * a) (K.mul_mem ha ha) h4 with h | h
    · rw [h]; exact E.one_mem
    · rw [h]; exact hzE
  have hsqK' : ∀ b ∈ K', b * b ∈ E := fun b hb => by
    have h4 := E8.pow_four_of_card_eight hΩ hK'Ω (h8 K' hK'Ω) hb
    rcases hz2.unique (b * b) (K'.mul_mem hb hb) h4 with h | h
    · rw [h]; exact E.one_mem
    · rw [h]; exact hzE
  have hsq : ∀ s ∈ K ⊔ K', s * s ∈ E := by
    intro s hs
    have hs' : s ∈ (K : Set G) * (K' : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K K' hnormK']
      exact hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs'
    have hab := hcomm a ha b hb
    have e : a * b * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
    rw [e]
    exact E.mul_mem (hsqK a ha) (hsqK' b hb)
  exact E8.le_of_card_thirtyTwo hE hSX hcardS hsq

theorem cent_of_e8 {E : Subgroup G} (hE : E8Struct (conjSub g (piGen π)) E) :
    ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u : G, IsUniqueInvolution L u →
      ∀ x ∈ piGen π, x * u = u * x := by
  intro L hL u hu x hx
  obtain ⟨Q, hQX, hQn, hQ2, huQ⟩ := S.exists_normalTwo hL hu
  have huS : u ∈ K ⊔ K' := S.le_sup_of_e8 hE (hE.core Q hQX hQn hQ2 huQ)
  have hKc : K ≤ Subgroup.centralizer (piGen π : Set G) := S.hos.le_centralizer_piGen S.hπ
  have hK'c : K' ≤ Subgroup.centralizer (piGen π : Set G) :=
    S.hos.beta_le_centralizer (S.hos.twinSet_subset_beta S.hπ S.hH1 S.hK')
  have := Subgroup.mem_centralizer_iff.mp ((sup_le hKc hK'c) huS) x hx
  exact this

theorem false_of_e8 {E : Subgroup G} (hE : E8Struct (conjSub g (piGen π)) E) : False :=
  S.false_of_cent (S.cent_of_e8 hE)

end Setting

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
