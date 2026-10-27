module

public import CFSG.CGT.PushingUpLit.BHS5.FiveFive

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS

theorem exists_perm_swap_conj {m : ℕ} {i j i' j' : Fin m} (hij : i ≠ j) (hij' : i' ≠ j') :
    ∃ σ : Equiv.Perm (Fin m), σ * Equiv.swap i j * σ⁻¹ = Equiv.swap i' j' := by
  have hi : Equiv.swap i i' i = i' := Equiv.swap_apply_left i i'
  have hj₁ : Equiv.swap i i' j ≠ i' := by
    intro h
    exact hij ((Equiv.swap i i').injective (h.trans hi.symm)).symm
  refine ⟨Equiv.swap (Equiv.swap i i' j) j' * Equiv.swap i i', ?_⟩
  have h1 : (Equiv.swap (Equiv.swap i i' j) j' * Equiv.swap i i') i = i' := by
    rw [Equiv.Perm.mul_apply, hi]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj₁) hij'
  have h2 : (Equiv.swap (Equiv.swap i i' j) j' * Equiv.swap i i') j = j' := by
    rw [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _
  rw [← Equiv.swap_apply_apply, h1, h2]

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_conjSub_eq (g : MulAut V) (X : Subgroup (MulAut V)) :
    Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem exists_conj_of_sylow {E B B' : Subgroup (MulAut V)} (hB : IsSylowOf 2 B E)
    (hB' : IsSylowOf 2 B' E) : ∃ e ∈ E, conjSub e B = B' := by
  obtain ⟨k, hk, hkle⟩ := Glauberman.exists_conj_le_of_isSylowOf hB' hB.2.1 hB.1
  obtain ⟨k', -, hk'le⟩ := Glauberman.exists_conj_le_of_isSylowOf hB hB'.2.1 hB'.1
  have hc : Nat.card B' ≤ Nat.card B :=
    calc Nat.card B' = Nat.card (conjSub k' B') := (card_conjSub_eq k' B').symm
      _ ≤ Nat.card B := Subgroup.card_le_of_le hk'le
  exact ⟨k, hk, Subgroup.eq_of_le_of_card_ge hkle (hc.trans (card_conjSub_eq k B).symm.le)⟩

omit [Finite V] in
theorem exists_conj_of_symType {M : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {E B B' : Subgroup (MulAut V)} (h : SymType M D E) (hB : B ∈ dInter D E)
    (hB' : B' ∈ dInter D E) (hne : B ≠ ⊥) (hne' : B' ≠ ⊥) :
    ∃ e ∈ E, conjSub e B = B' := by
  obtain ⟨m, θ, β, hm, h3, hinv, hsurj, hker, hequiv, htop, hD, -⟩ := h
  obtain ⟨i, j, hij, hBt⟩ := hD B hB
  obtain ⟨i', j', hij', hBt'⟩ := hD B' hB'
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  obtain ⟨b', hb1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne'
  have hbE : (b : MulAut V) ∈ E := hB.2 b.2
  have hbE' : (b' : MulAut V) ∈ E := hB'.2 b'.2
  have hθb : θ ⟨b, hbE⟩ = Equiv.swap i j := by
    rcases hBt ⟨b, hbE⟩ b.2 with h1 | h1
    · exfalso
      have : (⟨(b : MulAut V), hbE⟩ : ↥E) = 1 := θ.injective (h1.trans (map_one θ).symm)
      exact hb1 (Subtype.ext (congrArg (fun z : ↥E => (z : MulAut V)) this))
    · exact h1
  have hθb' : θ ⟨b', hbE'⟩ = Equiv.swap i' j' := by
    rcases hBt' ⟨b', hbE'⟩ b'.2 with h1 | h1
    · exfalso
      have : (⟨(b' : MulAut V), hbE'⟩ : ↥E) = 1 := θ.injective (h1.trans (map_one θ).symm)
      exact hb1' (Subtype.ext (congrArg (fun z : ↥E => (z : MulAut V)) this))
    · exact h1
  obtain ⟨σ, hσ⟩ := exists_perm_swap_conj hij hij'
  obtain ⟨g, hg⟩ : ∃ g : ↥E, θ g = σ := ⟨θ.symm σ, θ.apply_symm_apply σ⟩
  have hconj : (g : MulAut V) * b * (g : MulAut V)⁻¹ = b' := by
    have h1 : θ (g * ⟨b, hbE⟩ * g⁻¹) = θ ⟨b', hbE'⟩ := by
      rw [map_mul, map_mul, map_inv, hθb, hθb', hg, hσ]
    exact congrArg (fun z : ↥E => (z : MulAut V)) (θ.injective h1)
  have hBeq : ∀ x ∈ B, x = 1 ∨ x = b := by
    intro x hx
    rcases hBt ⟨x, hB.2 hx⟩ hx with h1 | h1
    · left
      have : (⟨x, hB.2 hx⟩ : ↥E) = 1 := θ.injective (h1.trans (map_one θ).symm)
      exact congrArg (fun z : ↥E => (z : MulAut V)) this
    · right
      have : (⟨x, hB.2 hx⟩ : ↥E) = ⟨b, hbE⟩ := θ.injective (h1.trans hθb.symm)
      exact congrArg (fun z : ↥E => (z : MulAut V)) this
  have hBeq' : ∀ x ∈ B', x = 1 ∨ x = b' := by
    intro x hx
    rcases hBt' ⟨x, hB'.2 hx⟩ hx with h1 | h1
    · left
      have : (⟨x, hB'.2 hx⟩ : ↥E) = 1 := θ.injective (h1.trans (map_one θ).symm)
      exact congrArg (fun z : ↥E => (z : MulAut V)) this
    · right
      have : (⟨x, hB'.2 hx⟩ : ↥E) = ⟨b', hbE'⟩ := θ.injective (h1.trans hθb'.symm)
      exact congrArg (fun z : ↥E => (z : MulAut V)) this
  refine ⟨g, g.2, ?_⟩
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    rcases hBeq _ hx with h1 | h1
    · have hx1 : x = 1 := by
        calc x = (g : MulAut V) * ((g : MulAut V)⁻¹ * x * (g : MulAut V)) * (g : MulAut V)⁻¹ := by
              group
          _ = 1 := by rw [h1]; group
      rw [hx1]
      exact B'.one_mem
    · have hxb : x = b' := by
        calc x = (g : MulAut V) * ((g : MulAut V)⁻¹ * x * (g : MulAut V)) * (g : MulAut V)⁻¹ := by
              group
          _ = b' := by rw [h1, hconj]
      rw [hxb]
      exact b'.2
  · intro hx
    rcases hBeq' x hx with h1 | h1
    · rw [h1]
      simp
    · rw [h1, ← hconj]
      have : (g : MulAut V)⁻¹ * ((g : MulAut V) * b * (g : MulAut V)⁻¹) * (g : MulAut V) = b := by
        group
      rw [this]
      exact b.2

namespace FiveFive

variable {P T M : Subgroup (MulAut V)}
  {ℰ : Set (Subgroup (MulAut V))}

theorem exists_conj_offSet (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
    {B B' : Subgroup (MulAut V)} (hB : B ∈ Hyp51.offSet P) (hB' : B' ∈ Hyp51.offSet P) :
    ∃ g ∈ P, conjSub g B = B' := by
  have h43 := h.hyp43 hV
  obtain ⟨E, hE, hBE⟩ := hF.cover B hB
  obtain ⟨E', hE', hB'E'⟩ := hF.cover B' hB'
  obtain ⟨t, ht, htE⟩ := hF.trans E hE E' hE'
  have htP : t ∈ P := h.minpar.T_le ht
  have hB'' : conjSub t B ∈ Hyp51.offSet P := hB.conj htP
  have hB''E' : conjSub t B ≤ E' := htE ▸ conjSub_mono t hBE
  obtain ⟨e, he, heq⟩ : ∃ e ∈ E', conjSub e (conjSub t B) = B' := by
    rcases hF.type E' hE' with hSL | hSym
    · obtain ⟨n, -, -, -, hsyl⟩ := hSL
      exact exists_conj_of_sylow ((hsyl _).1 ⟨hB'', hB''E'⟩) ((hsyl _).1 ⟨hB', hB'E'⟩)
    · exact exists_conj_of_symType hSym ⟨hB'', hB''E'⟩ ⟨hB', hB'E'⟩ (h43.ne_bot _ hB'')
        (h43.ne_bot _ hB')
  refine ⟨e * t, P.mul_mem (hF.le_P h hV hE' he) htP, ?_⟩
  rw [conjSub_mul]
  exact heq

end FiveFive

end CFSG.CGT.PushingUpLit.BHS5
