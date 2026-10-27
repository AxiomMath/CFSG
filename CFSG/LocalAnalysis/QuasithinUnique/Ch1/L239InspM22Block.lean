module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22BlockSyl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspBlockData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22BlockAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Lift

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction CFSG.Open CFSG.Quasithin

section Cert

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

structure BlockData.Valid {m t : ℕ} (d : BlockData M m t) : Prop where
  card_B₀ : d.B₀.card = m
  H_reach : Reach d.gens d.B₀ d.H d.hp d.hl
  H_closed : ClosedUnder d.gens d.H
  H_nodup : d.H.Nodup
  ks_fix : ∀ g ∈ d.ks, g • d.B₀ = d.B₀
  R₁_reach : Reach d.ks d.r₁ d.R₁ d.p₁ d.l₁
  R₂_reach : Reach d.ks d.r₂ d.R₂ d.p₂ d.l₂
  R₁_nodup : d.R₁.Nodup
  R₂_nodup : d.R₂.Nodup
  R₁_sub : ∀ B ∈ d.R₁, B ∈ d.H
  R₂_sub : ∀ B ∈ d.R₂, B ∈ d.H
  B₀_not₁ : d.B₀ ∉ d.R₁
  B₀_not₂ : d.B₀ ∉ d.R₂
  cover : ∀ B ∈ d.H, B ≠ d.B₀ → B ∈ d.R₁ ∨ B ∈ d.R₂
  lev₁ : ∀ B ∈ d.H, B ≠ d.B₀ → (B ∈ d.R₁ ↔ (B ∩ d.B₀).card = d.c₁)
  lev₂ : ∀ B ∈ d.H, B ≠ d.B₀ → (B ∈ d.R₂ ↔ (B ∩ d.B₀).card = d.c₂)
  harith : ∀ k ∈ List.range d.H.length, k ∣ d.H.length →
    k < 1 + d.R₁.length ∧ k < 1 + d.R₂.length
  T_reach : Reach d.ks d.t₀ d.T d.tp d.tl
  T_nodup : d.T.Nodup
  t₀_mem : ∀ i, d.t₀ i ∈ d.B₀
  Es_len : d.Es.length = 16
  Es_nodup : d.Es.Nodup
  Es_fix : ∀ e ∈ d.Es, ∀ x ∈ d.B₀, e • x = x
  Es_sq : ∀ e ∈ d.Es, e * e = 1
  Es_comm : ∀ e ∈ d.Es, ∀ f ∈ d.Es, e * f = f * e
  noncentral : ∃ k ∈ d.ks, ∃ e ∈ d.Es, k * e ≠ e * k
  T_len : d.T.length * 2 = m.factorial
  num_M : d.H.length * (16 * d.T.length) = 2 ^ d.e * d.u
  odd_u : ¬ 2 ∣ d.u
  num_K : 16 * d.T.length = 2 ^ d.e * d.u'
  odd_u' : ¬ 2 ∣ d.u'
  div₁ : ¬ 2 ^ d.e ∣ (2 ^ d.e * d.u') / d.R₁.length
  div₂ : ¬ 2 ^ d.e ∣ (2 ^ d.e * d.u') / d.R₂.length

theorem BlockData.exists_struct {m t : ℕ} (d : BlockData M m t) (hv : d.Valid)
    (hgens : Subgroup.closure {g | g ∈ d.gens} = ⊤)
    (hcard : Nat.card ↥M = d.H.length * (16 * d.T.length))
    (hAut : ∀ α : MulAut ↥M, ∃ B' ∈ d.H,
      (stabilizer ↥M d.B₀).map α.toMonoidHom = stabilizer ↥M B') :
    ∃ K₀ E₀ S₀ : Subgroup ↥M, Alt2Struct K₀ E₀ m ∧ (∀ Y : Subgroup ↥M, K₀ ≤ Y → Y = K₀ ∨ Y = ⊤) ∧
      IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧
      ∀ α : MulAut ↥M, S₀.map α.toMonoidHom = S₀ → K₀.map α.toMonoidHom = K₀ := by
  classical
  have hks : ∀ g ∈ d.ks, g ∈ stabilizer ↥M d.B₀ := fun g hg => mem_stabilizer_iff.2 (hv.ks_fix g hg)
  have horb : ∀ B, B ∈ orbit ↥M d.B₀ ↔ B ∈ d.H :=
    orbit_eq_of_reach_closed hgens hv.H_reach hv.H_closed
  have hO : BlockOrbits M d.B₀ d.H d.R₁ d.R₂ d.c₁ d.c₂ :=
    ⟨horb, hv.H_nodup, hv.R₁_nodup, hv.R₂_nodup, hv.R₁_sub, hv.R₂_sub, hv.B₀_not₁, hv.B₀_not₂,
      hv.cover, hv.lev₁, hv.lev₂⟩
  have hsame₁ := hv.R₁_reach.sameOrbit (stabilizer ↥M d.B₀) hks
  have hsame₂ := hv.R₂_reach.sameOrbit (stabilizer ↥M d.B₀) hks
  have hNpos : 0 < d.H.length :=
    List.length_pos_of_mem ((horb d.B₀).1 (mem_orbit_self d.B₀))
  have hqpos : 0 < d.T.length := by
    have h1 := Nat.factorial_pos m
    have h2 := hv.T_len
    omega
  have hKcard : Nat.card (stabilizer ↥M d.B₀) = 16 * d.T.length := by
    have h1 := Subgroup.card_mul_index (stabilizer ↥M d.B₀)
    rw [hO.card_stab, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hNpos (h1.trans (mul_comm _ _))
  obtain ⟨E₀, hE₀⟩ := alt2Struct_stab d.B₀ hv.card_B₀ hv.T_len hqpos d.Es hv.Es_len hv.Es_nodup
    hv.Es_fix hv.Es_sq hv.Es_comm
    (by
      obtain ⟨k, hk, e, he, hne⟩ := hv.noncentral
      exact ⟨k, hks k hk, e, he, hne⟩)
    d.t₀ hv.t₀_mem hKcard (le_card_orbit (stabilizer ↥M d.B₀) hks hv.T_reach hv.T_nodup)
  have hmax := stab_maximal hO hsame₁ hsame₂ hv.harith
  obtain ⟨S₀, hS₀p, hS₀i, hS₀inv⟩ := exists_sylow_inv hO hsame₁ hsame₂ (hcard.trans hv.num_M)
    hv.odd_u (hKcard.trans hv.num_K) hv.odd_u' hv.div₁ hv.div₂ hAut
  exact ⟨_, E₀, S₀, hE₀, hmax, hS₀p, hS₀i, hS₀inv⟩

theorem BlockData.parabolic {G : Type} [Group G] [Finite G] {L R : Subgroup G} {m t : ℕ}
    (d : BlockData M m t) (hv : d.Valid) (hgens : Subgroup.closure {g | g ∈ d.gens} = ⊤)
    (hcard : Nat.card ↥M = d.H.length * (16 * d.T.length))
    (hAut : ∀ α : MulAut ↥M, ∃ B' ∈ d.H,
      (stabilizer ↥M d.B₀).map α.toMonoidHom = stabilizer ↥M B')
    (hs : IsSimpleGroup (alternatingGroup (Fin m))) (hn : ¬ IsPGroup 2 (alternatingGroup (Fin m)))
    (hm : Nat.card (alternatingGroup (Fin m)) = 360 ∨ Nat.card (alternatingGroup (Fin m)) = 2520)
    (e : ↥L ≃* ↥M) (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf (R ⊓ L) L) :
    ∃ K : Subgroup G, K ≤ L ∧ R ≤ Subgroup.normalizer (K : Set G) ∧ CharTwo K ∧
      ¬ HasChi0Block K ∧ IsAltOverElemAbelian K 4 m ∧
      ∀ Y : Subgroup G, K ≤ Y → Y ≤ L → Y = K ∨ Y = L := by
  obtain ⟨K₀, E₀, S₀, hstruct, hmax, hS₀p, hS₀i, hinv⟩ := d.exists_struct hv hgens hcard hAut
  exact exists_lift_local hRN hS e hS₀p hS₀i hinv hmax hstruct hs hn hm

end Cert

end CFSG.QuasithinUnique.Vol2Native.L239
