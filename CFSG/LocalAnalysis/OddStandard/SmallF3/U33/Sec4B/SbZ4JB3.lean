module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JB2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

abbrev zjAct (Y : Subgroup H) [Y.Normal] : H →* MulAut ↥Y := MulAut.conjNormal

theorem zjAct_ker (Y : Subgroup H) [Y.Normal] : (zjAct Y).ker = centralizer (Y : Set H) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg y hy
    have h1 : g * y * g⁻¹ = y := by
      have := congrArg (fun f : MulAut ↥Y => (f ⟨y, hy⟩ : H)) hg
      simpa using this
    have h2 : g * y = y * g := by
      calc g * y = (g * y * g⁻¹) * g := by group
        _ = y * g := by rw [h1]
    exact h2.symm
  · intro hg
    ext y
    simp only [zjAct, MulAut.conjNormal_apply, MulAut.one_apply]
    have hy : (y : H) * g = g * y := hg y y.2
    rw [← hy]
    group

theorem card_range_mul_card_E (Y : Subgroup H) [Y.Normal] :
    Nat.card (zjAct Y).range * Nat.card (centralizer (Y : Set H)) = Nat.card H := by
  rw [← zjAct_ker Y, mul_comm]
  exact Subgroup.card_ker_mul_card_range _

variable {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) [Y.Normal]
include h

theorem eight_dvd_card_range : 8 ∣ Nat.card (zjAct Y).range := by
  have hcard := card_range_mul_card_E (H := H) Y
  rw [h.card_E] at hcard
  have hcard' : Nat.card (zjAct Y).range * 2 ^ 7 = Nat.card H := by
    simpa using hcard
  have hdiv : 2 ^ 10 ∣ Nat.card (zjAct Y).range * 2 ^ 7 := by
    simpa only [← hcard'] using h.two_pow_ten
  have h2 : (2:ℕ) ^ 3 * 2 ^ 7 ∣ Nat.card (zjAct Y).range * 2 ^ 7 := by
    simpa [show (2:ℕ) ^ 3 * 2 ^ 7 = 2 ^ 10 by norm_num] using hdiv
  have h3 : (2:ℕ) ^ 3 ∣ Nat.card (zjAct Y).range :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2
  simpa using h3

theorem range_cent_two_group (W : Subgroup (MulAut ↥Y)) (hWS : W ≤ (zjAct Y).range)
    (hWc : W ≤ centralizer ({zjAct Y ρ} : Set (MulAut ↥Y))) (hW : IsPGroup 2 W) :
    Nat.card W ≤ 2 := by
  classical
  let f : H →* MulAut ↥Y := zjAct Y
  let E : Subgroup H := centralizer (Y : Set H)
  let W' : Subgroup H := W.comap f
  let C : Subgroup H := W' ⊓ centralizer ({ρ} : Set H)
  let A : Subgroup H := Subgroup.zpowers ρ
  have hfker : f.ker = E := by
    rw [show f = zjAct Y from rfl]
    exact zjAct_ker Y
  have hE_le_W' : E ≤ W' := by
    rw [← hfker]
    exact MonoidHom.ker_le_comap (zjAct Y) W
  have hW'2 : IsPGroup 2 W' := by
    intro g
    have hgW : f (g : H) ∈ W := g.2
    obtain ⟨k, hk⟩ := hW ⟨f (g : H), hgW⟩
    have hk' : (f (g : H)) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hker : (g : H) ^ 2 ^ k ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, hk']
    rw [hfker] at hker
    obtain ⟨m, hm⟩ := h.E_isPGroup ⟨(g : H) ^ 2 ^ k, hker⟩
    refine ⟨k + m, ?_⟩
    apply Subtype.ext
    have hm' : ((g : H) ^ 2 ^ k) ^ 2 ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using hm'
  have hρconj : ∀ w ∈ W', f (ρ * w * ρ⁻¹) = f w := by
    intro w hw
    rw [Subgroup.mem_comap] at hw
    have hcomm : f w * f ρ = f ρ * f w :=
      Subgroup.mem_centralizer_singleton_iff.mp (hWc hw)
    rw [map_mul, map_mul, map_inv]
    calc f ρ * f w * (f ρ)⁻¹ = (f w * f ρ) * (f ρ)⁻¹ := by rw [hcomm]
      _ = f w := by group
  have hρconj_inv : ∀ w ∈ W', f (ρ⁻¹ * w * ρ) = f w := by
    intro w hw
    rw [Subgroup.mem_comap] at hw
    have hcomm : f w * f ρ = f ρ * f w :=
      Subgroup.mem_centralizer_singleton_iff.mp (hWc hw)
    rw [map_mul, map_mul, map_inv]
    calc (f ρ)⁻¹ * f w * f ρ = (f ρ)⁻¹ * (f w * f ρ) := by group
      _ = (f ρ)⁻¹ * (f ρ * f w) := by rw [hcomm]
      _ = f w := by group
  have hρW' : ∀ w ∈ W', ρ * w * ρ⁻¹ ∈ W' := by
    intro w hw
    rw [Subgroup.mem_comap]
    rw [hρconj w hw]
    rwa [Subgroup.mem_comap] at hw
  have hρW'inv : ∀ w ∈ W', ρ⁻¹ * w * ρ ∈ W' := by
    intro w hw
    rw [Subgroup.mem_comap]
    rw [hρconj_inv w hw]
    rwa [Subgroup.mem_comap] at hw
  have hρ_norm : ρ ∈ normalizer (W' : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hρW' x hx, fun hx => ?_⟩
    have h2 : ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x := by group
    have := hρW'inv (ρ * x * ρ⁻¹) hx
    rwa [h2] at this
  have hA3 : IsPGroup 3 A := by
    have hcard : Nat.card A ∣ 3 := by
      rw [show A = Subgroup.zpowers ρ from rfl, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one h.rho_pow_three
    obtain ⟨k, -, hk'⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card A ∣ 3 ^ 1 by simpa using hcard)
    exact IsPGroup.of_card (n := k) hk'
  let α : A →* MulAut W' :=
    (Subgroup.normalizerMonoidHom W').comp
      (Subgroup.inclusion (Subgroup.zpowers_le.mpr hρ_norm))
  have hαH : ∀ (a : A) (x : W'), ((α a x : W') : H) = (a : H) * (x : H) * (a : H)⁻¹ :=
    fun a x => rfl
  let N : Subgroup W' := E.subgroupOf W'
  have hcop : ¬ 3 ∣ Nat.card N := by
    have hNcard : Nat.card N = 128 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_W').toEquiv]
      exact h.card_E
    rw [hNcard]
    norm_num
  have hlift : ∀ w ∈ W', ∃ c ∈ C, f c = f w := by
    intro w hw
    let g : W' := ⟨w, hw⟩
    have hP_rho : (g : H)⁻¹ * ρ * (g : H) * ρ⁻¹ ∈ E := by
      rw [← hfker, MonoidHom.mem_ker]
      have h1 : (g : H)⁻¹ * ρ * (g : H) * ρ⁻¹ =
          (g : H)⁻¹ * (ρ * (g : H) * ρ⁻¹) := by group
      rw [h1, map_mul, map_inv, hρconj w hw]
      rw [show f (g : H) = f w from rfl]
      group
    have hP_rho_inv : (g : H)⁻¹ * ρ⁻¹ * (g : H) * ρ ∈ E := by
      rw [← hfker, MonoidHom.mem_ker]
      have h1 : (g : H)⁻¹ * ρ⁻¹ * (g : H) * ρ =
          (g : H)⁻¹ * (ρ⁻¹ * (g : H) * ρ) := by group
      rw [h1, map_mul, map_inv, hρconj_inv w hw]
      rw [show f (g : H) = f w from rfl]
      group
    have hP_all : ∀ a : A, (g : H)⁻¹ * (a : H) * (g : H) * (a : H)⁻¹ ∈ E := by
      intro a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      rw [← hn]
      refine zpow_induction_left (g := ρ)
        (P := fun b : H => (g : H)⁻¹ * b * (g : H) * b⁻¹ ∈ E) ?_ ?_ ?_ n
      · simp
      · intro b hb
        have h1 : (g : H)⁻¹ * (ρ * b) * (g : H) * (ρ * b)⁻¹ =
            ((g : H)⁻¹ * ρ * (g : H) * ρ⁻¹) *
              (ρ * ((g : H)⁻¹ * b * (g : H) * b⁻¹) * ρ⁻¹) := by group
        rw [h1]
        exact Subgroup.mul_mem _ hP_rho (h.E_normal (g := ρ) hb)
      · intro b hb
        have h1 : (g : H)⁻¹ * (ρ⁻¹ * b) * (g : H) * (ρ⁻¹ * b)⁻¹ =
            ((g : H)⁻¹ * ρ⁻¹ * (g : H) * ρ) *
              (ρ⁻¹ * ((g : H)⁻¹ * b * (g : H) * b⁻¹) * ρ) := by group
        rw [h1]
        exact Subgroup.mul_mem _ hP_rho_inv (by
          simpa using h.E_normal (g := ρ⁻¹) hb)
    have hcond : ∀ a : A, ∀ x : W', (g : W')⁻¹ * x ∈ N → (g : W')⁻¹ * α a x ∈ N := by
      intro a x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      change (g : H)⁻¹ * ((α a x : W') : H) ∈ E
      have hpa := hP_all a
      have hxn : (a : H) * ((g : H)⁻¹ * (x : H)) * (a : H)⁻¹ ∈ E :=
        h.E_normal (g := (a : H)) (e := (g : H)⁻¹ * (x : H)) hx
      have halg : (g : H)⁻¹ * ((α a x : W') : H) =
          ((g : H)⁻¹ * (a : H) * (g : H) * (a : H)⁻¹) *
            ((a : H) * ((g : H)⁻¹ * (x : H)) * (a : H)⁻¹) := by
        rw [hαH]
        group
      rw [halg]
      exact Subgroup.mul_mem _ hpa hxn
    obtain ⟨c, hc, hcfix⟩ :=
      (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA3 α N hcop g).2 hcond
    have hcE : (g : H)⁻¹ * (c : H) ∈ E := by
      have := hc
      rwa [Subgroup.mem_subgroupOf] at this
    have hfc : f (c : H) = f w := by
      have h1 : f ((g : H)⁻¹ * (c : H)) = 1 := by
        rw [← hfker] at hcE
        exact MonoidHom.mem_ker.mp hcE
      rw [map_mul, map_inv] at h1
      have h2 : f (c : H) = f w := by
        calc f (c : H) = (f w) * ((f w)⁻¹ * f (c : H)) := by group
          _ = f w := by rw [h1]; group
      exact h2
    have hcρ : (c : H) ∈ centralizer ({ρ} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfixρ : ρ * (c : H) * ρ⁻¹ = (c : H) := by
        have := hcfix ⟨ρ, Subgroup.mem_zpowers ρ⟩
        have hcoe := congrArg Subtype.val this
        simpa [hαH] using hcoe
      calc (c : H) * ρ = (ρ * (c : H) * ρ⁻¹) * ρ := by rw [hfixρ]
        _ = ρ * (c : H) := by group
    exact ⟨c, ⟨c.2, hcρ⟩, hfc⟩
  have hC2 : IsPGroup 2 C := hW'2.to_le inf_le_left
  obtain ⟨c₀, -, hc₀map⟩ := h.tt_sylow C inf_le_right hC2
  have hcard_closure : Nat.card (closure ({t, τ} : Set H)) ≤ 4 := by
    let ψ0 : Fin 4 → closure ({t, τ} : Set H) := fun i =>
      if i = 0 then ⟨1, one_mem _⟩
      else if i = 1 then ⟨t, subset_closure (by simp)⟩
      else if i = 2 then ⟨τ, subset_closure (by simp)⟩
      else ⟨t * τ, mul_mem (subset_closure (by simp)) (subset_closure (by simp))⟩
    have hsurj : Function.Surjective ψ0 := by
      intro y
      have hy := (mem_closure_pair_of_invol h.t_sq h.tau_sq h.t_tau).mp y.2
      rcases hy with h1 | h1 | h1 | h1
      · exact ⟨0, Subtype.ext (by simp [ψ0, h1])⟩
      · exact ⟨1, Subtype.ext (by simp [ψ0, h1])⟩
      · exact ⟨2, Subtype.ext (by simp [ψ0, h1])⟩
      · exact ⟨3, Subtype.ext (by simp [ψ0, h1])⟩
    have := Nat.card_le_card_of_surjective ψ0 hsurj
    simpa using this
  have hC_le : Nat.card C ≤ 4 := by
    let ψ : C → closure ({t, τ} : Set H) :=
      fun p => ⟨c₀ * (p : H) * c₀⁻¹, hc₀map p p.2⟩
    have hψinj : Function.Injective ψ := by
      intro p q hpq
      apply Subtype.ext
      have hpq' : c₀ * (p : H) * c₀⁻¹ = c₀ * (q : H) * c₀⁻¹ := congrArg Subtype.val hpq
      calc (p : H) = c₀⁻¹ * (c₀ * (p : H) * c₀⁻¹) * c₀ := by group
        _ = c₀⁻¹ * (c₀ * (q : H) * c₀⁻¹) * c₀ := by rw [hpq']
        _ = (q : H) := by group
    exact (Nat.card_le_card_of_injective ψ hψinj).trans hcard_closure
  let φ : C →* MulAut ↥Y := f.comp C.subtype
  have hrange : φ.range = W := by
    apply le_antisymm
    · rintro x ⟨c, rfl⟩
      exact c.2.1
    · intro x hx
      obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp (hWS hx)
      have hhW' : h ∈ W' := by
        rw [Subgroup.mem_comap]
        rwa [hh]
      obtain ⟨c, hcC, hfc⟩ := hlift h hhW'
      refine ⟨⟨c, hcC⟩, ?_⟩
      change f c = x
      rw [hfc, hh]
  have hEinf_le_C : E ⊓ centralizer ({ρ} : Set H) ≤ C :=
    le_inf (inf_le_left.trans hE_le_W') inf_le_right
  have hker_eq : φ.ker = (E ⊓ centralizer ({ρ} : Set H)).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hc
      have hcE : (c : H) ∈ E := by
        rw [← hfker]
        exact hc
      exact ⟨hcE, c.2.2⟩
    · rintro ⟨hcE, -⟩
      rw [← hfker] at hcE
      exact hcE
  have hcent : E ⊓ centralizer ({ρ} : Set H) = zpowers τ := by
    rw [inf_comm]
    exact h.centralizer_rho_inf_E
  have htau_ne : τ ≠ 1 := by
    intro h1
    apply h.tau_not_mem_Q
    rw [h1]
    exact one_mem Q
  have htau_ord : orderOf τ = 2 := by
    refine orderOf_eq_prime ?_ htau_ne
    simpa [pow_two] using h.tau_sq
  have hkerCard : Nat.card φ.ker = 2 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEinf_le_C).toEquiv,
      hcent, Nat.card_zpowers, htau_ord]
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hkerCard, hrange] at hcard
  omega

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
