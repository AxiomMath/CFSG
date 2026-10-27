module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltHH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltPerm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem conj_closure_mem {Y : Type} [Group Y] (b : MulAut Y) (R₀ : Subgroup Y) {r : Y}
    (hr : r ∈ R₀) {x : MulAut Y}
    (hx : x ∈ closure {c : MulAut Y | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹}) :
    MulAut.conj r * x * (MulAut.conj r)⁻¹ ∈
      closure {c : MulAut Y | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹} := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', hr', rfl⟩ := hx
    refine subset_closure ⟨r * r', R₀.mul_mem hr hr', ?_⟩
    simp only [map_mul]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have : MulAut.conj r * (x * y) * (MulAut.conj r)⁻¹ =
        (MulAut.conj r * x * (MulAut.conj r)⁻¹) * (MulAut.conj r * y * (MulAut.conj r)⁻¹) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : MulAut.conj r * x⁻¹ * (MulAut.conj r)⁻¹ = (MulAut.conj r * x * (MulAut.conj r)⁻¹)⁻¹ := by
      group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem n1fam_alt : N1Fam FAlt := by
  intro Y _ _ p b R₀ hF hcfg
  obtain ⟨n, hn7, hn11, ⟨e⟩⟩ := hF
  obtain ⟨hpp, hp2, hord, hsyl, hpg⟩ := hcfg
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  obtain ⟨e', hne⟩ : ∃ e' : ℕ, (n = 7 ∧ e' = 3) ∨ (n = 8 ∧ e' = 6) ∨ (n = 9 ∧ e' = 6) ∨
      (n = 10 ∧ e' = 7) ∨ (n = 11 ∧ e' = 7) := by
    have : n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 := by omega
    rcases this with h | h | h | h | h
    · exact ⟨3, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨6, Or.inr (Or.inl ⟨h, rfl⟩)⟩
    · exact ⟨6, Or.inr (Or.inr (Or.inl ⟨h, rfl⟩))⟩
    · exact ⟨7, Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩)))⟩
    · exact ⟨7, Or.inr (Or.inr (Or.inr (Or.inr ⟨h, rfl⟩)))⟩
  let Φ := autTransport hn5 hn6 e
  let ι : Y →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  let T : Subgroup (Perm (Fin n)) := R₀.map ι
  let S : Set (MulAut Y) := {c | ∃ r ∈ R₀, c = MulAut.conj r * b * (MulAut.conj r)⁻¹}
  let X : Subgroup (Perm (Fin n)) := (closure S).map Φ.toMonoidHom
  have hTA : T ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨r, _, rfl⟩
    exact (e r).2
  have hTc : Nat.card ↥T = 2 ^ e' := by
    have h1 : Nat.card ↥T = Nat.card ↥R₀ := Subgroup.card_map_of_injective hι
    have h2 := IsSylowOf.card_eq hsyl
    rw [Subgroup.card_top] at h2
    have h3 : Nat.card Y = Nat.card ↥(alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
    rw [h1, h2, h3, AltPerm.card_alt_exp hne]
  have hX : IsPGroup p ↥X := hpg.map Φ.toMonoidHom
  have hΦconj : ∀ r : Y, Φ (MulAut.conj r) = ι r := fun r => autTransport_conj hn5 hn6 e r
  have hfwd : ∀ r ∈ R₀, ∀ h ∈ X, ι r * h * (ι r)⁻¹ ∈ X := by
    intro r hr h hh
    obtain ⟨x, hx, rfl⟩ := hh
    refine ⟨MulAut.conj r * x * (MulAut.conj r)⁻¹, conj_closure_mem b R₀ hr hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hΦconj]
  have hN : T ≤ normalizer (X : Set (Perm (Fin n))) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd r hr h, fun hh => ?_⟩
    have h1 := hfwd r⁻¹ (R₀.inv_mem hr) _ hh
    have h2 : ι r⁻¹ * (ι r * h * (ι r)⁻¹) * (ι r⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    rwa [h2] at h1
  have hc : Φ b ∈ X := ⟨b, subset_closure ⟨1, R₀.one_mem, by simp⟩, rfl⟩
  have hc1 : Φ b ≠ 1 := by
    intro h
    have hb1 : b = 1 := Φ.injective (by rw [h, map_one])
    rw [hb1, orderOf_one] at hord
    exact hpp.one_lt.ne hord
  obtain ⟨hp3, hn, hthree⟩ := AltPerm.perm_core hp2 hne hTA hTc hX hN hc hc1
  refine Or.inl ⟨hp3, ?_, ?_⟩
  · rcases hn with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr ⟨e⟩
  · obtain ⟨E, hE2, hEab, hEb, x, hxE, hbx⟩ := hhobs_of_threeCycle hn5 hn6 hn e b hthree
    refine ⟨2, Nat.prime_two, ?_, E, hE2, fun _ => hEab, hEb, x, hxE, hbx⟩
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
