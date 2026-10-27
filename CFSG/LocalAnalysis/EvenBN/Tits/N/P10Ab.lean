module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step08
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P05Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise commutatorElement

section Generic

theorem node10_sq_t_mul_f_mul_u {Γ : Type*} [Group Γ] {t f ε u : Γ} (ht : t * t = 1)
    (hf : f * f = 1) (htf : t * f = f * t) (hεf : ε * f = f * ε) (huf : u * f = f * u)
    (hut : u * t = t * ε * u) : (t * f * u) * (t * f * u) = ε * (u * u) := by
  have h1 : t * f * t = f := by rw [mul_assoc, ← htf, ← mul_assoc, ht, one_mul]
  calc t * f * u * (t * f * u) = t * f * (u * t) * f * u := by group
    _ = t * f * (t * ε * u) * f * u := by rw [hut]
    _ = (t * f * t) * ε * (u * f) * u := by group
    _ = f * ε * (f * u) * u := by rw [h1, huf]
    _ = (f * ε * f) * (u * u) := by group
    _ = (ε * f * f) * (u * u) := by rw [← hεf]
    _ = ε * (u * u) := by rw [mul_assoc ε, hf, mul_one]

theorem node10_isElemAbelian_of_sq {Γ : Type*} [Group Γ] {V : Subgroup Γ}
    (h : ∀ x ∈ V, x * x = 1) : CFSG.Open.IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := h a a.2
    have h2 := h b b.2
    have h3 := h (a * b) (mul_mem a.2 b.2)
    have h4 : (a : Γ) * b * (b * a) = 1 := by
      calc (a : Γ) * b * (b * a) = a * (b * b) * a := by group
        _ = 1 := by rw [h2, mul_one, h1]
    show (a : Γ) * b = b * a
    rw [eq_inv_of_mul_eq_one_right h4, inv_eq_of_mul_eq_one_right h3]
  · rw [pow_two]
    exact h x hx

end Generic

section P10Ab

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem node10_sq_B_mul_P (h49 : d.Thm49Statement) (hd : d.Hyp) {b u : G} (hb : b ∈ d.B)
    (huP : u ∈ d.s56P) :
    (b * u) * (b * u) = u * u ∨ (b * u) * (b * u) = d.s56Eps u * (u * u) := by
  have hFt : ∀ f ∈ d.F, d.t * f = f * d.t := fun f hf =>
    congrArg Subtype.val (hd.B_facts.2.2.1.1.is_comm.comm ⟨d.t, d.s56_t_mem_B⟩
      ⟨f, d.s56_F_le_B hf⟩)
  have huF : ∀ f ∈ d.F, u * f = f * u := fun f hf =>
    mul_inv_eq_iff_eq_mul.1 (d.s56_P_conj_F huP hf)
  rcases hd.s56_mem_B_iff.1 hb with hf | hf
  · left
    calc b * u * (b * u) = b * (u * b) * u := by group
      _ = b * (b * u) * u := by rw [huF b hf]
      _ = (b * b) * (u * u) := by group
      _ = u * u := by rw [hd.s56_F_sq hf, one_mul]
  · right
    obtain ⟨f, hfdef⟩ : ∃ f, f = d.t * b := ⟨_, rfl⟩
    rw [← hfdef] at hf
    have hb' : b = d.t * f := by rw [hfdef, ← mul_assoc, hd.t_mul_self, one_mul]
    have hut : u * d.t = d.t * d.s56Eps u * u := by
      have := hd.s56_conj_t u
      calc u * d.t = (u * d.t * u⁻¹) * u := by group
        _ = d.t * d.s56Eps u * u := by rw [this]
    rw [hb']
    exact node10_sq_t_mul_f_mul_u hd.t_mul_self (hd.s56_F_sq hf) (hFt f hf)
      (hd.s56_F_comm (hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N huP)) hf) (huF f hf) hut

theorem node10_Y_sq (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) {u : G} (huV : u ∈ d.s56V) (huP : u ∈ d.s56P)
    (huε : d.s56Eps u = d.pv 10) : u * u = 1 := by
  obtain ⟨hyNC, -, -, -, hy10, -, hyz⟩ := hd.s56_Y_facts
  have hyN : d.s56Y ∈ d.N := (mem_inf.1 hyNC).1
  generalize d.s56Y = y at hyN hy10 hyz
  have hF10 : d.pv 10 ∈ d.F := d.s56_pv10_mem_F
  have hu₁P : y * u * y⁻¹ ∈ d.s56P := hd.s56_N_conj_P h49 hyN huP
  have hεu₁ : d.s56Eps (y * u * y⁻¹) = d.pv 10 := by
    rw [hd.s56_eps_conj_N h49 hyN huP, huε]
    calc y * d.pv 10 * y⁻¹ = (d.pv 10 * y) * y⁻¹ := by rw [hy10]
      _ = d.pv 10 := by group
  have hbP : y * u * y⁻¹ * u⁻¹ ∈ d.s56P := mul_mem hu₁P (inv_mem huP)
  have hεb : d.s56Eps (y * u * y⁻¹ * u⁻¹) = 1 := by
    rw [hd.s56_eps_mul_P h49 hu₁P (inv_mem huP), hd.s56_eps_inv_P h49 huP, hεu₁, huε]
    exact hd.s56_F_sq hF10
  have hbB : y * u * y⁻¹ * u⁻¹ ∈ d.B := hd.s56_mem_B_of_eps_one h49 hbP hεb
  have hkey := node10_sq_B_mul_P h49 hd hbB huP
  have e1 : (y * u * y⁻¹ * u⁻¹) * u = y * u * y⁻¹ := by group
  have e2 : y * u * y⁻¹ * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
  rw [e1, e2] at hkey
  have hu2 : u * u ∈ zpowers d.z := hd.s56_V_sq_mem_of_sq_eq_one h49 hz hsq huV
  rcases hd.s56_mem_zpowers_z hu2 with h1 | h1
  · exact h1
  · exfalso
    rw [h1, hyz] at hkey
    rcases hkey with h | h
    · exact d.s56_pv11_ne_one (mul_eq_right.1 h)
    · apply d.s56_pv10_not_mem_U11
      have h' : d.pv 11 = d.pv 10 := by rw [← huε]; exact mul_right_cancel h
      rw [← h']
      exact d.s56_pv11_mem_U11

theorem node10_exists_sq_one_U11 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) (hel : CFSG.Open.IsElemAbelian 2 (Pe11 d))
    (hFV : (Pe11 d : Set G) = (d.F : Set G) * ((Pe11 d ⊓ d.s56V : Subgroup G) : Set G))
    {a : G} (ha : a ∈ d.s56U11) : ∃ w ∈ d.s56V, d.s56Eps w = a ∧ w * w = 1 := by
  obtain ⟨w, hw, hwε⟩ := hd.s56_eps_Pe11_surj_Y h49 hz a ha
  have hw' : w ∈ (Pe11 d : Set G) := by rw [Pe11_eq_s56Pe11]; exact hw
  rw [hFV] at hw'
  obtain ⟨f, hf, v, hv, rfl⟩ := Set.mem_mul.1 hw'
  obtain ⟨hvPe, hvV⟩ := mem_inf.1 hv
  have hvPe' : v ∈ d.s56Pe11 := by rw [← Pe11_eq_s56Pe11]; exact hvPe
  have hfP : f ∈ d.s56P := hd.s56_B_le_P (d.s56_F_le_B hf)
  have hvP : v ∈ d.s56P := hd.s56_Pe11_le_P h49 hvPe'
  refine ⟨v, hvV, ?_, ?_⟩
  · rw [hd.s56_eps_mul_P h49 hfP hvP, hd.s56_eps_eq_one_of_mem_B (d.s56_F_le_B hf), one_mul]
      at hwε
    exact hwε
  · have := hel.2 v hvPe
    rwa [pow_two] at this

theorem node10_pv10_mem_of_invariant (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G}
    (hSF : S ≤ d.F) (hinv : ∀ k ∈ d.s56K, ∀ x ∈ S, k * x * k⁻¹ ∈ S) (hcard : 8 ≤ Nat.card S) :
    d.pv 10 ∈ S := by
  by_cases hS10 : S ≤ d.s56U10
  · have hS : S = d.s56U10 :=
      Subgroup.eq_of_le_of_card_ge hS10 (by rw [d.s56_card_U10]; exact hcard)
    rw [hS]
    exact d.s56_pv10_mem_U10
  obtain ⟨s, hsS, hsU⟩ : ∃ s ∈ S, s ∉ d.s56U10 := by
    by_contra hcon
    exact hS10 fun s hs => by_contra fun h => hcon ⟨s, hs, h⟩
  have hsF : s ∈ d.F := hSF hsS
  obtain ⟨k, hkK, hk⟩ : ∃ k ∈ d.s56K, k * s * k⁻¹ * s⁻¹ ∉ d.s56U11 := by
    by_contra hcon
    exact hsU (Data.s56_comm_K_le_U10 hsF fun k hk => by_contra fun h => hcon ⟨k, hk, h⟩)
  have hkP0 := hd.s56_K_le_P0 h49 hkK
  have hu₀10 : k * s * k⁻¹ * s⁻¹ ∈ d.s56U10 := hd.s56_P0_comm_F_le_U10 h49 hkP0 hsF
  have hu₀S : k * s * k⁻¹ * s⁻¹ ∈ S := mul_mem (hinv k hkK s hsS) (inv_mem hsS)
  obtain ⟨u', hu'U, hu'⟩ : ∃ u' ∈ d.s56U11, k * s * k⁻¹ * s⁻¹ = d.pv 10 * u' := by
    rcases Data.s56_U10_cases hu₀10 with h | ⟨u', hu', h⟩
    · exact absurd h hk
    · exact ⟨u', hu', h⟩
  have hU11S : ∀ u ∈ d.s56U11, u ∈ S := by
    intro u hu
    obtain ⟨k', hk'K, hk'⟩ := hd.s56_exists_K_comm h49 hu
    have hk'P0 := hd.s56_K_le_P0 h49 hk'K
    have h1 : k' * (k * s * k⁻¹ * s⁻¹) * k'⁻¹ ∈ S := hinv k' hk'K _ hu₀S
    have hc' : k' * u' = u' * k' := hd.s56_P0_comm_U11 h49 hk'P0 hu'U
    have e2 : k' * u' * k'⁻¹ = u' := by rw [hc']; group
    have h2 : k' * (k * s * k⁻¹ * s⁻¹) * k'⁻¹ = u * (k * s * k⁻¹ * s⁻¹) := by
      rw [hu']
      calc k' * (d.pv 10 * u') * k'⁻¹ = (k' * d.pv 10 * k'⁻¹) * (k' * u' * k'⁻¹) := by group
        _ = (u * d.pv 10) * u' := by rw [hk', e2]
        _ = u * (d.pv 10 * u') := by group
    rw [h2] at h1
    have e : u = u * (k * s * k⁻¹ * s⁻¹) * (k * s * k⁻¹ * s⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem h1 (inv_mem hu₀S)
  have : d.pv 10 = (k * s * k⁻¹ * s⁻¹) * u'⁻¹ := by rw [hu']; group
  rw [this]
  exact mul_mem hu₀S (inv_mem (hU11S u' hu'U))

theorem node10_card_V_inf_P_ge (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) (hPQ : Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9) :
    2 ^ 7 ≤ Nat.card (d.s56V ⊓ d.s56P : Subgroup G) := by
  have hQ2 : Nat.card d.s56Q2 ≤ 2 ^ 12 := by
    have h := (hd.s56_structure_M h49).2.1
    rcases hd.range_ρ with hR | hR
    · rw [h, (card_CA h49 hd).1 hR]
      norm_num
    · rw [h, (card_CA h49 hd).2 hR]
      norm_num
  have hRV : (d.s56Q2 ⊓ d.s56P) ≤ normalizer (d.s56V : Set G) :=
    inf_le_left.trans ((Q2_le_M d).trans (hd.s56_M_le_normalizer_V h49))
  have hprod := S56.card_sup_mul_card_inf_of_le_normalizer hRV
  have hsup : Nat.card (d.s56Q2 ⊓ d.s56P ⊔ d.s56V : Subgroup G) ≤ Nat.card d.s56Q2 :=
    Subgroup.card_le_of_le (sup_le inf_le_left (Data.s56_V_le_Q2 d))
  have hinf : (d.s56Q2 ⊓ d.s56P) ⊓ d.s56V = d.s56V ⊓ d.s56P := by
    ext x
    simp only [mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨Data.s56_V_le_Q2 d h.1, h.2⟩, h.1⟩⟩
  rw [hinf, hPQ, hd.s56_card_V h49 hz] at hprod
  by_contra hlt
  have hlt' : Nat.card (d.s56V ⊓ d.s56P : Subgroup G) < 2 ^ 7 := not_le.1 hlt
  have h1 : Nat.card (d.s56Q2 ⊓ d.s56P ⊔ d.s56V : Subgroup G) *
      Nat.card (d.s56V ⊓ d.s56P : Subgroup G) ≤
      2 ^ 12 * Nat.card (d.s56V ⊓ d.s56P : Subgroup G) :=
    Nat.mul_le_mul_right _ (hsup.trans hQ2)
  omega

theorem node10_exists_u0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hPQ : Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9) :
    ∃ u ∈ d.s56V, u ∈ d.s56P ∧ d.s56Eps u = d.pv 10 := by
  have hcard := node10_card_V_inf_P_ge h49 hd hz hPQ
  let φ : ↥(d.s56V ⊓ d.s56P) →* G := MonoidHom.mk' (fun x => d.s56Eps x.1) fun x y =>
    hd.s56_eps_mul_P h49 (mem_inf.1 x.2).2 (mem_inf.1 y.2).2
  have hker : φ.ker ≤ (d.E ⊓ d.F).subgroupOf (d.s56V ⊓ d.s56P) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : d.s56Eps x.1 = 1 := hx
    have hxE : x.1 ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 (mem_inf.1 x.2).1).1 hx1
    have hxB : x.1 ∈ d.B := hd.s56_mem_B_of_eps_one h49 (mem_inf.1 x.2).2 hx1
    exact mem_subgroupOf.2 (mem_inf.2 ⟨hxE, hd.s56_E_inf_B hxE hxB⟩)
  have hEF : d.E ⊓ d.F ≤ d.s56V ⊓ d.s56P :=
    le_inf (inf_le_left.trans (hd.s56_E_le_V h49))
      (inf_le_right.trans (d.s56_F_le_B.trans hd.s56_B_le_P))
  have hkcard : Nat.card φ.ker ≤ 16 := by
    calc Nat.card φ.ker ≤ Nat.card ((d.E ⊓ d.F).subgroupOf (d.s56V ⊓ d.s56P)) :=
          Subgroup.card_le_of_le hker
      _ = Nat.card (d.E ⊓ d.F : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv
      _ = 16 := hd.s56_card_E_inf_F
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hrange : 8 ≤ Nat.card φ.range := by
    by_contra hlt
    have hlt' : Nat.card φ.range ≤ 7 := by omega
    have := Nat.mul_le_mul hkcard hlt'
    omega
  have hSF : φ.range ≤ d.F := by
    rintro _ ⟨x, rfl⟩
    exact hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N (mem_inf.1 x.2).2)
  have hinv : ∀ k ∈ d.s56K, ∀ s ∈ φ.range, k * s * k⁻¹ ∈ φ.range := by
    intro k hk s hs
    obtain ⟨x, rfl⟩ := hs
    have hkC := hd.s56_K_le_CNt hk
    have hkN : k ∈ d.N := (mem_inf.1 hkC).1
    have hkt : k * d.t = d.t * k := mem_centralizer_singleton_iff.1 (mem_inf.1 hkC).2
    have hkM : k ∈ d.M := hd.s56_CP0t_le_M (hd.s56_K_le_P0 h49 hk) (mem_inf.1 hkC).2
    refine ⟨⟨k * x * k⁻¹, mem_inf.2 ⟨hd.s56_V_conj_mem h49 hkM (mem_inf.1 x.2).1,
      hd.s56_N_conj_P h49 hkN (mem_inf.1 x.2).2⟩⟩, ?_⟩
    exact hd.s56_eps_conj hkt x.1
  obtain ⟨x, hx⟩ := node10_pv10_mem_of_invariant h49 hd hSF hinv hrange
  exact ⟨x.1, (mem_inf.1 x.2).1, (mem_inf.1 x.2).2, hx⟩

theorem node10_sq_of_eps_eq (h49 : d.Thm49Statement) (hd : d.Hyp) {x w : G} (hx : x ∈ d.s56V)
    (hw : w ∈ d.s56V) (hε : d.s56Eps x = d.s56Eps w) (hw2 : w * w = 1) : x * x = 1 := by
  have hxw : x * w⁻¹ ∈ d.s56V := mul_mem hx (inv_mem hw)
  have hE : x * w⁻¹ ∈ d.E := by
    refine (hd.s56_V_eps_eq_one_iff h49 hxw).1 ?_
    rw [hd.s56_eps_mul_Q2' hx.2 (inv_mem hw).2, hd.s56_eps_inv_Q2 hw.2, hε]
    exact hd.s56_E_sq (hd.s56_V_eps_mem_E hw)
  have hcomm : w * (x * w⁻¹) = (x * w⁻¹) * w := Data.s56_V_comm_E hw hE
  have hee := hd.s56_E_sq hE
  calc x * x = (x * w⁻¹ * w) * (x * w⁻¹ * w) := by group
    _ = (x * w⁻¹) * (w * (x * w⁻¹)) * w := by group
    _ = (x * w⁻¹) * ((x * w⁻¹) * w) * w := by rw [hcomm]
    _ = ((x * w⁻¹) * (x * w⁻¹)) * (w * w) := by group
    _ = 1 := by rw [hee, hw2, one_mul]

theorem node10_sq_of_conj (h49 : d.Thm49Statement) (hd : d.Hyp) {g x w : G}
    (hg : g ∈ d.M ⊓ centralizer ({d.t} : Set G)) (hx : x ∈ d.s56V) (hw : w ∈ d.s56V)
    (hε : d.s56Eps x = g * d.s56Eps w * g⁻¹) (hw2 : w * w = 1) : x * x = 1 := by
  have hgM : g ∈ d.M := (mem_inf.1 hg).1
  have hgt : g * d.t = d.t * g := mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2
  refine node10_sq_of_eps_eq h49 hd hx (hd.s56_V_conj_mem h49 hgM hw) ?_ ?_
  · rw [hd.s56_eps_conj hgt w, hε]
  · calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [hw2]; group

theorem node10_sq_all (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (h11 : ∃ w ∈ d.s56V, d.s56Eps w = d.pv 11 ∧ w * w = 1)
    (h10 : ∃ w ∈ d.s56V, d.s56Eps w = d.pv 10 ∧ w * w = 1) : ∀ x ∈ d.s56V, x * x = 1 := by
  intro x hx
  have hε : d.s56Eps x ∈ d.E := hd.s56_V_eps_mem_E hx
  by_cases he1 : d.s56Eps x = 1
  · exact node10_sq_of_eps_eq h49 hd hx (one_mem _) (by rw [he1, hd.s56_eps_one]) (mul_one 1)
  by_cases hez : d.s56Eps x = d.z
  · exact node10_sq_of_eps_eq h49 hd hx hz.mem_V (by rw [hez, hz.eps]) hsq
  rcases d.mem_zL_or_vL (X := Model.hatE) (fun y hy hy1 => Model.hatE_long_or_short hy hy1) hε he1
    with hzL | hvL
  · have hmem : d.s56Eps x ∈ (d.zL ∩ d.A) \ {d.z} := ⟨⟨hzL, mem_sup_left hε⟩, hez⟩
    rw [← hd.orbits_A.2.2.1] at hmem
    obtain ⟨g, hg, hge⟩ := hmem
    obtain ⟨w, hwV, hwε, hw2⟩ := h11
    exact node10_sq_of_conj h49 hd hg hx hwV (by rw [hwε, hge]) hw2
  · have hmem : d.s56Eps x ∈ d.vL ∩ d.A := ⟨hvL, mem_sup_left hε⟩
    rw [← hd.orbits_A.2.2.2.2.1] at hmem
    obtain ⟨g, hg, hge⟩ := hmem
    obtain ⟨w, hwV, hwε, hw2⟩ := h10
    exact node10_sq_of_conj h49 hd hg hx hwV (by rw [hwε, hge]) hw2

theorem node10_V_elemAb (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hsq : z₀ * z₀ = 1) (_h05 : Node05 d z₀) (h08 : Node08 d z₀) (_h09 : Node09 d z₀)
    (hPQ : Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9) :
    CFSG.Open.IsElemAbelian 2 d.s56V := by
  obtain ⟨-, -, -, -, hel, -, -, hFV⟩ := h08
  obtain ⟨u, huV, huP, huε⟩ := node10_exists_u0 h49 hd hz hPQ
  have hall := node10_sq_all h49 hd hz hsq
    (node10_exists_sq_one_U11 h49 hd hz hel hFV d.s56_pv11_mem_U11)
    ⟨u, huV, huε, node10_Y_sq h49 hd hz hsq huV huP huε⟩
  exact node10_isElemAbelian_of_sq hall

end P10Ab

end CFSG.LocalAnalysis.EvenBN.Tits.N
