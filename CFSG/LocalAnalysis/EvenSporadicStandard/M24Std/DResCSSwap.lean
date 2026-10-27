module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSK
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6Aut

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

theorem swap_or_card_prod6
    (α : MulAut (alternatingGroup (Fin 6) × alternatingGroup (Fin 6))) (hα : α * α = 1) :
    (∃ f₁ f₂ : MulAut (alternatingGroup (Fin 6)), (∀ a b, α (a, b) = (f₁ b, f₂ a)) ∧
      (∀ b, f₂ (f₁ b) = b) ∧ Nat.card {g // α g = g} = 360) ∨
    (∃ n₁ n₂ : ℕ, (n₁ = 360 ∨ n₁ = 8 ∨ n₁ = 24 ∨ n₁ = 10) ∧
      (n₂ = 360 ∨ n₂ = 8 ∨ n₂ = 24 ∨ n₂ = 10) ∧ Nat.card {g // α g = g} = n₁ * n₂) := by
  have hnt : ∃ s : alternatingGroup (Fin 6), s ≠ 1 := by
    have : Nontrivial (alternatingGroup (Fin 6)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [card_alt6]; norm_num)
    exact exists_ne 1
  rcases ProdAut.mulAut_prod_cases alt6_hsimple (fun _ => alt6_central) hnt α with
    ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · right
    obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_preserve α hp1 hp2
    have hff : ∀ a b, (f₁ (f₁ a), f₂ (f₂ b)) = (a, b) := by
      intro a b
      have := congrArg (fun β : MulAut (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) =>
        β (a, b)) hα
      simpa [MulAut.mul_apply, hf] using this
    have hf1 : f₁ * f₁ = 1 := MulEquiv.ext fun a => by
      simpa using (Prod.ext_iff.1 (hff a 1)).1
    have hf2 : f₂ * f₂ = 1 := MulEquiv.ext fun b => by
      simpa using (Prod.ext_iff.1 (hff 1 b)).2
    have c1 := card_fix_involution_alt6 (MulEquiv.refl (alternatingGroup (Fin 6))) f₁ hf1
    have c2 := card_fix_involution_alt6 (MulEquiv.refl (alternatingGroup (Fin 6))) f₂ hf2
    have hprod : Nat.card {g // α g = g} =
        Nat.card {a // f₁ a = a} * Nat.card {b // f₂ b = b} := by
      rw [← Nat.card_prod]
      refine Nat.card_congr
        { toFun := fun g => (⟨g.1.1, ?_⟩, ⟨g.1.2, ?_⟩)
          invFun := fun p => ⟨(p.1.1, p.2.1), ?_⟩
          left_inv := fun g => rfl
          right_inv := fun p => rfl }
      · have := congrArg Prod.fst g.2
        simpa [hf] using this
      · have := congrArg Prod.snd g.2
        simpa [hf] using this
      · rw [hf, p.1.2, p.2.2]
    exact ⟨_, _, by omega, by omega, hprod⟩
  · left
    obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_swap α hs1 hs2
    have hf21 : ∀ b, f₂ (f₁ b) = b := by
      intro b
      have := congrArg (fun β : MulAut (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) =>
        β (1, b)) hα
      simpa [MulAut.mul_apply, hf] using (Prod.ext_iff.1 this).2
    refine ⟨f₁, f₂, hf, hf21, ?_⟩
    rw [← card_alt6]
    refine Nat.card_congr
      { toFun := fun g => g.1.2
        invFun := fun b => ⟨(f₁ b, b), by rw [hf, hf21]⟩
        left_inv := fun g => ?_
        right_inv := fun b => rfl }
    obtain ⟨⟨a, b⟩, hg⟩ := g
    have h1 := congrArg Prod.fst hg
    simp only [hf] at h1
    apply Subtype.ext
    simp only
    rw [h1]

section Swap

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {K : Subgroup Y} {φ : K →* Equiv.Perm (Fin 6)}

structure IsSwap6 (t : Y)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
    (f₁ f₂ : MulAut (alternatingGroup (Fin 6))) : Prop where
  conj : ∀ g : egaLayer (Yb Y), e ⟨proj Y t * g * (proj Y t)⁻¹,
    (egaLayer_normal _).conj_mem _ g.2 _⟩ = (f₁ (e g).2, f₂ (e g).1)
  inv : ∀ b, f₂ (f₁ b) = b

namespace CYHyp

variable (hY : CYHyp t K φ)
include hY

theorem swap
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    ∃ f₁ f₂ : MulAut (alternatingGroup (Fin 6)), IsSwap6 t e f₁ f₂ ∧
      Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) : Subgroup (Yb Y)) = 360 ∧
      (∀ γ : Y, γ ∈ K0 φ ↔ γ ∈ centralizer ({t} : Set Y) ∧ proj Y γ ∈ egaLayer (Yb Y)) ∧
      (∀ γ ∈ centralizer ({t} : Set Y), γ ∈ fusionOddCore Y → γ ∈ Zk φ) ∧
      Zk φ ≤ fusionOddCore Y := by
  have hEn := egaLayer_normal (Yb Y)
  have ht2 : proj Y t ^ 2 = 1 := by
    rw [← map_pow, ← hY.order, pow_orderOf_eq_one, map_one]
  obtain ⟨α, hαα, hαe, hαcard⟩ := exists_mulAut_of_normal' e ht2
  set Fbar : Subgroup (Yb Y) := egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) with hFbar
  set Gam : Subgroup Y := centralizer ({t} : Set Y) with hGam
  have htK : t ∈ centralizer (K : Set Y) := mem_centralizer_iff.2 fun k hk => hY.comm k hk
  have hC' := centralizer_mk_fusionOddCore_eq hY.order hY.cent htK
  have hlift : ∀ x ∈ centralizer ({proj Y t} : Set (Yb Y)), ∃ γ ∈ Gam, proj Y γ = x := by
    intro x hx
    have hle : K.map (proj Y) ⊔ zpowers (proj Y t) ≤ Gam.map (proj Y) := by
      refine sup_le (Subgroup.map_mono (le_sup_left.trans hY.cent.symm.le)) ?_
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.map_mono (le_sup_right.trans hY.cent.symm.le)
    rw [hC'] at hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 (hle hx)
    exact ⟨γ, hγ, rfl⟩
  let Ftil : Subgroup Y := Gam ⊓ Fbar.comap (proj Y)
  let GO : Subgroup Y := Gam ⊓ fusionOddCore Y
  have hFG : Ftil ≤ Gam := inf_le_left
  have hcommt : ∀ γ ∈ Gam, Commute (proj Y γ) (proj Y t) := fun γ hγ => by
    show proj Y γ * proj Y t = proj Y t * proj Y γ
    rw [← map_mul, ← map_mul]
    exact congrArg _ (mem_centralizer_singleton_iff.1 hγ)
  have hFn : ∀ γ ∈ Gam, ∀ n ∈ Ftil, γ * n * γ⁻¹ ∈ Ftil := by
    intro γ hγ n hn
    refine ⟨Gam.mul_mem (Gam.mul_mem hγ hn.1) (Gam.inv_mem hγ), ?_⟩
    have hn2 : proj Y n ∈ Fbar := hn.2
    have hc2 : Commute (proj Y n) (proj Y t) := mem_centralizer_singleton_iff.1 hn2.2
    have hc1 := hcommt γ hγ
    show proj Y (γ * n * γ⁻¹) ∈ Fbar
    rw [map_mul, map_mul, map_inv]
    exact ⟨hEn.conj_mem _ hn2.1 _, mem_centralizer_singleton_iff.2
      (((hc1.mul_left hc2).mul_left hc1.inv_left).eq)⟩
  have hGOZ : GO ≤ Zk φ := by
    refine hY.odd_le_Zk inf_le_left (fun γ hγ n hn => ⟨Gam.mul_mem (Gam.mul_mem hγ hn.1)
      (Gam.inv_mem hγ), (inferInstance : (fusionOddCore Y).Normal).conj_mem n hn.2 γ⟩) ?_
    exact Odd.of_dvd_nat (odd_natCard_fusionOddCore Y) (Subgroup.card_dvd_of_le inf_le_right)
  have hGOcard : Nat.card GO = 1 ∨ Nat.card GO = 3 := by
    have h : Nat.card GO ∣ 3 := hY.card_Zk ▸ Subgroup.card_dvd_of_le hGOZ
    exact (Nat.dvd_prime Nat.prime_three).1 h
  have hFcard : Nat.card Ftil = Nat.card GO * Nat.card Fbar := by
    let ρ : Ftil →* Yb Y := (proj Y).comp Ftil.subtype
    have hrange : ρ.range = Fbar := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2.2
      · intro hx
        obtain ⟨γ, hγ, hγx⟩ := hlift x hx.2
        refine ⟨⟨γ, hγ, ?_⟩, hγx⟩
        show proj Y γ ∈ Fbar
        rw [hγx]
        exact hx
    have hker : Nat.card ρ.ker = Nat.card GO := by
      refine Nat.card_congr
        { toFun := fun g => ⟨g.1.1, g.1.2.1, (QuotientGroup.eq_one_iff _).1 g.2⟩
          invFun := fun g => ⟨⟨g.1, g.2.1, by
            have : proj Y g.1 = 1 := (QuotientGroup.eq_one_iff _).2 g.2.2
            show proj Y g.1 ∈ Fbar
            rw [this]; exact one_mem _⟩, by
            exact (QuotientGroup.eq_one_iff _).2 g.2.2⟩
          left_inv := fun g => rfl
          right_inv := fun g => rfl }
    have := Subgroup.card_ker_mul_card_range ρ
    rw [hrange, hker] at this
    exact this.symm
  have hFGcard : Nat.card Ftil ≤ 4320 :=
    hY.card_Gam ▸ Subgroup.card_le_of_le hFG
  have hdich := hY.dichotomy_Gam hFG hFn
  have hCzt : ∀ H : Subgroup Y, H ≤ Czt t φ → Nat.card H ≤ 6 := fun H hH =>
    hY.card_Czt ▸ Subgroup.card_le_of_le hH
  rcases swap_or_card_prod6 α hαα with ⟨f₁, f₂, hf, hinv, hcard⟩ | ⟨n₁, n₂, hn₁, hn₂, hcard⟩
  ·
    have hFb : Nat.card Fbar = 360 := hαcard ▸ hcard
    rcases hdich with hK0 | hle
    · have h1080 : 1080 ∣ Nat.card Ftil := hY.card_K0 ▸ Subgroup.card_dvd_of_le hK0
      have hGO3 : Nat.card GO = 3 := by
        rcases hGOcard with h | h
        · rw [hFcard, h, hFb] at h1080
          omega
        · exact h
      have hFK : Ftil = K0 φ := (Subgroup.eq_of_le_of_card_ge hK0
        (by rw [hY.card_K0, hFcard, hGO3, hFb])).symm
      refine ⟨f₁, f₂, ⟨fun g => ?_, hinv⟩, hFb, fun γ => ⟨fun hγ => ?_, fun hγ => ?_⟩,
        fun γ hγ hγO => hGOZ ⟨hγ, hγO⟩, ?_⟩
      · rw [← hαe g, hf]
      · have : γ ∈ Ftil := hFK ▸ hγ
        exact ⟨this.1, this.2.1⟩
      · have : γ ∈ Ftil := ⟨hγ.1, ⟨hγ.2, mem_centralizer_singleton_iff.2 (hcommt γ hγ.1).eq⟩⟩
        rw [← hFK]
        exact this
      · have hGOeq : GO = Zk φ :=
          Subgroup.eq_of_le_of_card_ge hGOZ (by rw [hY.card_Zk, hGO3])
        rw [← hGOeq]
        exact inf_le_right
    · have h6 := hCzt _ hle
      rw [hFcard, hFb] at h6
      rcases hGOcard with h | h <;> rw [h] at h6 <;> omega
  ·
    exfalso
    have hFb : Nat.card Fbar = n₁ * n₂ := hαcard ▸ hcard
    rcases hdich with hK0 | hle
    · have h1080 : 1080 ∣ Nat.card Ftil := hY.card_K0 ▸ Subgroup.card_dvd_of_le hK0
      obtain ⟨j, hj⟩ := h1080
      rw [hFcard, hFb] at hj hFGcard
      rcases hGOcard with h | h <;> rw [h] at hj hFGcard <;> rcases hn₁ with h1 | h1 | h1 | h1 <;>
        rcases hn₂ with h2 | h2 | h2 | h2 <;> subst h1 h2 <;> omega
    · have h6 := hCzt _ hle
      rw [hFcard, hFb] at h6
      rcases hGOcard with h | h <;> rw [h] at h6 <;> rcases hn₁ with h1 | h1 | h1 | h1 <;>
        rcases hn₂ with h2 | h2 | h2 | h2 <;> subst h1 h2 <;> omega

end CYHyp

end Swap

end CFSG.EvenSporadicStandard.M24Std.DRes
