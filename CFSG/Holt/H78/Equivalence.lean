module

public import CFSG.Holt.H78.TwoPoint
import CFSG.Holt.H78.Lemma27Final
import CFSG.Holt.H78.Lemma27SE

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section Parity

theorem odd_card_of_involutive {X : Type*} [Finite X] {f : X → X} (hf : Function.Involutive f)
    {x₀ : X} (hfix : ∀ x, f x = x ↔ x = x₀) : Odd (Nat.card X) := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : hf.toPerm f ^ 2 ^ 1 = 1 := by
    ext x
    simp [sq, hf x]
  have h := Equiv.Perm.card_compl_support_modEq hσ
  have hc : (hf.toPerm f).supportᶜ = {x₀} := by
    ext x
    simp [Equiv.Perm.mem_support, hfix]
  rw [hc, Finset.card_singleton] at h
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact h.symm

theorem exists_fixed_of_involutive {X : Type*} [Finite X] {f : X → X}
    (hf : Function.Involutive f) (hX : Odd (Nat.card X)) : ∃ x, f x = x := by
  classical
  have := Fintype.ofFinite X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : hf.toPerm f ^ 2 ^ 1 = 1 := by
    ext x
    simp [sq, hf x]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2)
    (by rw [← Nat.card_eq_fintype_card]; exact hX.not_two_dvd_nat) hσ
  exact ⟨x, hx⟩

theorem odd_card_of_forall_mul_self_eq_one {X : Type*} [Group X] [Finite X]
    (h : ∀ g : X, g * g = 1 → g = 1) : Odd (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  have h1 := h g (by rw [← sq, ← hg, pow_orderOf_eq_one])
  rw [h1, orderOf_one] at hg
  omega

end Parity

section Conj

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem map_conj_stabilizer_inf (h : G) (α β : Ω) :
    (stabilizer G α ⊓ stabilizer G β).map (MulAut.conj h).toMonoidHom =
      stabilizer G (h • α) ⊓ stabilizer G (h • β) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective,
    ← stabilizer_smul_eq_stabilizer_map_conj, ← stabilizer_smul_eq_stabilizer_map_conj]

theorem fusionIsSylowIn_map_conj [Finite G] {S : Subgroup G} {α β : Ω}
    (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β)) (h : G) :
    fusionIsSylowIn 2 (S.map (MulAut.conj h).toMonoidHom)
      (stabilizer G (h • α) ⊓ stabilizer G (h • β)) := by
  have := fusionIsSylowIn_map (MulAut.conj h).toMonoidHom hS
  rwa [map_conj_stabilizer_inf] at this

end Conj

section Count

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]

omit [Finite Ω] in
theorem IsStarGroup.inv_smul_mem_iff (hG : IsStarGroup G Ω) {α : Ω} {Z : Set Ω}
    (hZ : ∀ h ∈ stabilizer G α, ∀ β ∈ Z, h • β ∈ Z) (g : G) :
    g⁻¹ • α ∈ Z ↔ g • α ∈ Z := by
  obtain ⟨x, hx⟩ := hG.swap_mem_orbit (α, g • α)
  simp only [Prod.smul_mk, Prod.swap_prod_mk, Prod.mk.injEq] at hx
  have hk : g⁻¹ * x ∈ stabilizer G α := by
    rw [mem_stabilizer_iff, mul_smul, hx.1, inv_smul_smul]
  have e : (g⁻¹ * x) • g • α = g⁻¹ • α := by rw [mul_smul, hx.2]
  constructor
  · intro h
    have := hZ _ (inv_mem hk) _ (e ▸ h)
    rwa [inv_smul_smul] at this
  · intro h
    rw [← e]
    exact hZ _ hk _ h

private def CountRel (α : Ω) (Z : Finset Ω) (ζ : Ω) (u : G) : Prop :=
  u ∈ longInv G Ω ∧ ∃ g : G, g • α = ζ ∧ g⁻¹ • u • ζ ∈ Z

omit [Finite G] [Finite Ω] in
private theorem card_filter_countRel [Fintype G] [Fintype Ω] [DecidableEq Ω]
    [IsPretransitive G Ω] {α : Ω} {Z : Finset Ω} (hZ : ∀ h ∈ stabilizer G α, ∀ β ∈ Z, h • β ∈ Z)
    [∀ ζ, DecidablePred (CountRel (G := G) α Z ζ)] [DecidablePred (· ∈ longInv G Ω)]
    (ζ : Ω) :
    ((Finset.univ.filter (· ∈ longInv G Ω)).filter (CountRel α Z ζ)).card =
      ∑ β ∈ Z, Nat.card (longInvSwap G Ω α β) := by
  classical
  obtain ⟨h₀, rfl⟩ := exists_smul_eq G α ζ
  have hc : ((Finset.univ.filter (· ∈ longInv G Ω)).filter (CountRel α Z (h₀ • α))).card =
      ((Finset.univ.filter (· ∈ longInv G Ω)).filter (fun u : G => u • α ∈ Z)).card := by
    refine Finset.card_nbij' (fun u => h₀⁻¹ * u * h₀) (fun u => h₀ * u * h₀⁻¹) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      obtain ⟨hJ, g, hg, hgZ⟩ := hu.2
      refine ⟨by simpa using conj_mem_longInv hJ h₀⁻¹, ?_⟩
      have hk : h₀⁻¹ * g ∈ stabilizer G α := by rw [mem_stabilizer_iff, mul_smul, hg, inv_smul_smul]
      have e : (h₀⁻¹ * u * h₀) • α = (h₀⁻¹ * g) • g⁻¹ • u • h₀ • α := by
        simp only [mul_smul, smul_inv_smul]
      rw [e]
      exact hZ _ hk _ hgZ
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      refine ⟨conj_mem_longInv hu.1 h₀, conj_mem_longInv hu.1 h₀, h₀, rfl, ?_⟩
      simpa [mul_smul] using hu.2
    · intro u _
      simp only
      group
    · intro u _
      simp only
      group
  rw [hc, Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ.filter (· ∈ longInv G Ω)).filter (fun u : G => u • α ∈ Z))
    (f := fun u : G => u • α) (t := Z) (fun u hu => (Finset.mem_filter.mp hu).2)]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_longInvSwap]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hβ⟩, h2⟩

private theorem sum_card_longInvSwap_le_and (hG : IsStarGroup G Ω) {α : Ω} {Z : Finset Ω}
    (hZ : ∀ h ∈ stabilizer G α, ∀ β ∈ Z, h • β ∈ Z) (hΔ : ∀ β ∈ Z, holtDelta G Ω α β ⊆ Z) :
    ∑ β ∈ Z, Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) * Z.card ∧
      (∑ β ∈ Z, Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) * Z.card →
        ∀ β γ : Ω, γ ∈ holtDelta G Ω α β → γ ∈ Z → β ∈ Z) := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite Ω
  have := hG.isPretransitive
  have hZ' : ∀ h ∈ stabilizer G α, ∀ β ∈ (Z : Set Ω), h • β ∈ (Z : Set Ω) := hZ
  set T : Finset G := Finset.univ.filter (· ∈ longInv G Ω) with hT
  have hmaps : ∀ u ∈ T, ∀ h : G, u • h • α = h • α → ∀ ζ, CountRel α Z ζ u →
      h⁻¹ • ζ ∈ Z := by
    intro u _ h hh ζ ⟨hJ, g, hg, hgZ⟩
    have hΔ' : g⁻¹ • h • α ∈ holtDelta G Ω α (g⁻¹ • u • ζ) := by
      refine ⟨g⁻¹ * u * g, ⟨by simpa using conj_mem_longInv hJ g⁻¹, ?_⟩, ?_⟩
      · rw [mul_smul, mul_smul, hg]
      · rw [mul_smul, mul_smul, smul_inv_smul, hh]
    have h1 : (g⁻¹ * h) • α ∈ (Z : Set Ω) := by
      rw [mul_smul]
      exact hΔ _ hgZ hΔ'
    have h2 := (hG.inv_smul_mem_iff hZ' (g⁻¹ * h)).mpr h1
    rwa [mul_inv_rev, inv_inv, mul_smul, hg] at h2
  have hfix : ∀ u ∈ T, ∃ h : G, u • h • α = h • α := fun u hu => by
    obtain ⟨θ, hθ⟩ := exists_mem_longInvAt (Finset.mem_filter.mp hu).2
    obtain ⟨h, rfl⟩ := exists_smul_eq G α θ
    exact ⟨h, hθ.2⟩
  have hc : ∀ u ∈ T, (Finset.univ.filter fun ζ => CountRel α Z ζ u).card ≤ Z.card :=
    fun u hu => by
      obtain ⟨h, hh⟩ := hfix u hu
      exact Finset.card_le_card_of_injOn (fun ζ => h⁻¹ • ζ)
        (fun ζ hζ => hmaps u hu h hh ζ (Finset.mem_filter.mp hζ).2)
        (fun a _ b _ hab => smul_left_cancel _ hab)
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun ζ u => CountRel (G := G) α Z ζ u) (s := Finset.univ) (t := T)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at key
  rw [Finset.sum_congr rfl fun ζ _ => card_filter_countRel hZ ζ, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at key
  have hTc : T.card = Fintype.card Ω * Nat.card (longInvAt G Ω α) := by
    rw [← card_longInv_eq_mul α, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hle := Finset.sum_le_sum hc
  rw [Finset.sum_const, smul_eq_mul, hTc] at hle
  have hpos : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨α⟩
  refine ⟨Nat.le_of_mul_le_mul_left (by rw [key, ← mul_assoc]; exact hle) hpos, ?_⟩
  intro heq β γ hγ hγZ
  have hsum : ∑ u ∈ T, (Finset.univ.filter fun ζ => CountRel α Z ζ u).card =
      ∑ _u ∈ T, Z.card := by
    rw [← key, Finset.sum_const, smul_eq_mul, hTc, heq, mul_assoc]
  have hall := (Finset.sum_eq_sum_iff_of_le hc).mp hsum
  obtain ⟨s, hs, hsγ⟩ := hγ
  have hsT : s ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1⟩
  obtain ⟨h, rfl⟩ := exists_smul_eq G α γ
  have himg : (Finset.univ.filter fun ζ => CountRel α Z ζ s).image (fun ζ => h⁻¹ • ζ) = Z := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.mp hx
      exact hmaps s hsT h hsγ ζ (Finset.mem_filter.mp hζ).2
    · rw [Finset.card_image_of_injective _ (MulAction.injective h⁻¹), hall s hsT]
  have hα : h⁻¹ • α ∈ Z := (hG.inv_smul_mem_iff hZ' h).mpr hγZ
  rw [← himg] at hα
  obtain ⟨ζ, hζ, hζα⟩ := Finset.mem_image.mp hα
  rw [smul_left_cancel_iff] at hζα
  subst hζα
  obtain ⟨-, g, hg, hgZ⟩ := (Finset.mem_filter.mp hζ).2
  rw [hs.2] at hgZ
  have := hZ g hg _ hgZ
  rwa [smul_inv_smul] at this

theorem sum_card_longInvSwap_le_of_holtDelta_subset (hG : IsStarGroup G Ω) {α : Ω}
    {Z : Finset Ω} (hZ : ∀ h ∈ stabilizer G α, ∀ β ∈ Z, h • β ∈ Z)
    (hΔ : ∀ β ∈ Z, holtDelta G Ω α β ⊆ Z) :
    ∑ β ∈ Z, Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) * Z.card :=
  (sum_card_longInvSwap_le_and hG hZ hΔ).1

theorem mem_of_mem_holtDelta_of_sum_eq (hG : IsStarGroup G Ω) {α : Ω} {Z : Finset Ω}
    (hZ : ∀ h ∈ stabilizer G α, ∀ β ∈ Z, h • β ∈ Z) (hΔ : ∀ β ∈ Z, holtDelta G Ω α β ⊆ Z)
    (heq : ∑ β ∈ Z, Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) * Z.card)
    {β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β) (hγZ : γ ∈ Z) : β ∈ Z :=
  (sum_card_longInvSwap_le_and hG hZ hΔ).2 heq β γ hγ hγZ

end Count

section OddCase

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem odd_orderOf_mul_of_odd_card {α β : Ω} {w s : G} (hw : w ∈ longInvAt G Ω β)
    (hs : s ∈ longInvSwap G Ω α β) (hodd : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))) :
    Odd (orderOf (w * s)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨k, hk⟩ := hev
  have hw2 := mul_self_eq_one_of_mem_longInv hw.1
  have hs2 := mul_self_eq_one_of_mem_longInv hs.1
  set z := (w * s) ^ k with hz
  have hpos : 0 < orderOf (w * s) := orderOf_pos (w * s)
  have hz1 : z ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hzz : z * z = 1 := by rw [hz, ← pow_add, ← hk, pow_orderOf_eq_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hwz : w * z = z * w := by
    have h1 := conj_pow_mul_eq_inv hw2 hs2 k
    rw [← hz, hzinv] at h1
    calc w * z = w * z * w⁻¹ * w := by group
      _ = z * w := by rw [h1]
  have hsz : s * z = z * s := by
    have h1 := conj_pow_mul_eq_inv hs2 hw2 k
    have e : s * w = (w * s)⁻¹ := by
      rw [mul_inv_rev, inv_eq_self_of_mem_longInv hw.1, inv_eq_self_of_mem_longInv hs.1]
    rw [e, inv_pow, ← hz, inv_inv, hzinv] at h1
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [h1]
  have hzβ : z • β = β := by
    have h1 : w • z • β = z • β := by rw [← mul_smul, hwz, mul_smul, hw.2]
    exact (smul_eq_iff_of_mem_longInvAt hw (z • β)).mp h1
  have hsβ : s • β = α := by rw [← hs.2, ← mul_smul, hs2, one_smul]
  have hzα : z • α = α := by rw [← hsβ, ← mul_smul, ← hsz, mul_smul, hzβ]
  have := eq_one_of_mul_self_eq_one_of_odd_card hodd (g := ⟨z, hzα, hzβ⟩) (Subtype.ext hzz)
  exact hz1 (congrArg Subtype.val this)

omit [Finite G] in
private theorem conj_mul_mem_longInvAt' {α β : Ω} {t u s : G} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInvSwap G Ω α β) (hs : s ∈ longInvSwap G Ω α β) :
    (s * u) * t * (s * u)⁻¹ ∈ longInvAt G Ω α := by
  have h := conj_mem_longInvAt ht (s * u)
  rwa [mem_stabilizer_iff.mp (mul_mem_stabilizer_inf_of_mem_longInvSwap hs hu).1] at h

theorem eq_of_conj_mul_eq_of_odd_card {α β : Ω}
    (hodd : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))) {t u s s' : G}
    (ht : t ∈ longInvAt G Ω α) (hu : u ∈ longInvSwap G Ω α β) (hs : s ∈ longInvSwap G Ω α β)
    (hs' : s' ∈ longInvSwap G Ω α β)
    (h : (s * u) * t * (s * u)⁻¹ = (s' * u) * t * (s' * u)⁻¹) : s = s' := by
  have hc : Commute (u * t * u⁻¹) (s' * s) := by
    show u * t * u⁻¹ * (s' * s) = s' * s * (u * t * u⁻¹)
    have e1 : s' * s * (u * t * u⁻¹) = s' * ((s * u) * t * (s * u)⁻¹) * s := by group
    have e2 : s' * ((s' * u) * t * (s' * u)⁻¹) * s =
        (s' * s') * (u * t * u⁻¹) * (s'⁻¹ * s) := by group
    rw [e1, h, e2, mul_self_eq_one_of_mem_longInv hs'.1, one_mul,
      inv_eq_self_of_mem_longInv hs'.1]
  have hw : u * t * u⁻¹ ∈ longInvAt G Ω β := hu.2 ▸ conj_mem_longInvAt ht u
  have hsq := mul_mul_self_eq_one_of_odd_of_commute (mul_self_eq_one_of_mem_longInv hw.1)
    (mul_self_eq_one_of_mem_longInv hs'.1) (mul_self_eq_one_of_mem_longInv hs.1)
    (odd_orderOf_mul_of_odd_card hw hs' hodd) hc
  have hst := Subgroup.mem_inf.mp (mul_mem_stabilizer_inf_of_mem_longInvSwap hs' hs)
  have h1 := eq_one_of_mul_self_eq_one_of_odd_card hodd (g := ⟨s' * s, hst.1, hst.2⟩)
    (Subtype.ext hsq)
  have h2 : s' * s = 1 := congrArg Subtype.val h1
  rw [← inv_eq_self_of_mem_longInv hs'.1]
  exact eq_inv_of_mul_eq_one_right h2

theorem card_longInvSwap_le_of_odd_card (hG : IsStarGroup G Ω) {α β : Ω}
    (hodd : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))) :
    Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) := by
  rcases (longInvSwap G Ω α β).eq_empty_or_nonempty with h | ⟨u, hu⟩
  · simp [h]
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  exact Nat.card_le_card_of_injective (fun s : longInvSwap G Ω α β =>
    (⟨((s : G) * u) * t * ((s : G) * u)⁻¹, conj_mul_mem_longInvAt' ht hu s.2⟩ :
      longInvAt G Ω α)) fun s s' h => Subtype.ext
    (eq_of_conj_mul_eq_of_odd_card hodd ht hu s.2 s'.2 (congrArg Subtype.val h))

end OddCase

section Known

variable {Y : Type} [Group Y] [Finite Y] {Δ : Type} [MulAction Y Δ] [Finite Δ] [FaithfulSMul Y Δ]

theorem odd_card_stabilizer_inf_of_mem_holtDelta
    (hY : IsStarGroup Y Δ) (hBY : HoltTheorem1Below (Nat.card Y) (Nat.card Δ + 1))
    {a b c : Δ} (hab : a ≠ b) (hc : c ∈ holtDelta Y Δ a b)
    (hodd : Odd (Nat.card ↥(stabilizer Y a ⊓ stabilizer Y b))) :
    Odd (Nat.card ↥(stabilizer Y a ⊓ stabilizer Y c)) := by
  have hca : c ≠ a := fun h => left_notMem_holtDelta hab (h ▸ hc)
  obtain ⟨u, hu, huc⟩ := hc
  have hu2 := mul_self_eq_one_of_mem_longInv hu.1
  have hub : u • b = a := smul_eq_of_mem_longInvSwap hu
  have hJab : Odd (Nat.card (longInvSwap Y Δ a b)) := by
    have hmem : ∀ x : longInvSwap Y Δ a b, u * (x : Y) * u⁻¹ ∈ longInvSwap Y Δ a b :=
      fun x => by
        have := conj_mem_longInvSwap x.2 u
        rwa [hu.2, hub, longInvSwap_comm] at this
    refine odd_card_of_involutive (f := fun x => ⟨u * x * u⁻¹, hmem x⟩) (x₀ := ⟨u, hu⟩)
      (fun x => Subtype.ext ?_) (fun x => ⟨fun hx => Subtype.ext ?_, fun hx => ?_⟩)
    · show u * (u * x * u⁻¹) * u⁻¹ = x
      rw [inv_eq_self_of_mem_longInv hu.1]
      calc u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [hu2, one_mul, mul_one]
    · have hx' : u * (x : Y) * u⁻¹ = x := congrArg Subtype.val hx
      have hcomm : u * (x : Y) = x * u := by
        calc u * (x : Y) = (u * x * u⁻¹) * u := by group
          _ = x * u := by rw [hx']
      have hx2 := mul_self_eq_one_of_mem_longInv x.2.1
      have hxa : (x : Y) • a = b := x.2.2
      have hxb : (x : Y) • b = a := smul_eq_of_mem_longInvSwap x.2
      have h1 : (u * x) • a = a := by rw [mul_smul, hxa, hub]
      have h2 : (u * x) • b = b := by rw [mul_smul, hxb, hu.2]
      have h3 : u * x * (u * x) = 1 := by
        calc u * x * (u * x) = u * (x * u) * x := by group
          _ = u * (u * x) * x := by rw [hcomm]
          _ = (u * u) * (x * x) := by group
          _ = 1 := by rw [hu2, hx2, one_mul]
      have h4 := eq_one_of_mul_self_eq_one_of_odd_card hodd (g := ⟨u * x, h1, h2⟩)
        (Subtype.ext h3)
      have h5 : u * (x : Y) = 1 := congrArg Subtype.val h4
      show (x : Y) = u
      rw [← inv_eq_self_of_mem_longInv hu.1]
      exact eq_inv_of_mul_eq_one_right h5
    · subst hx
      apply Subtype.ext
      show u * u * u⁻¹ = u
      group
  have hJc : Odd (Nat.card (longInvAt Y Δ c)) := by
    rw [hY.card_longInvAt_eq c a, ← card_longInvSwap_eq hY hBY hab]
    exact hJab
  have hb : b ∈ holtDelta' Y Δ c a := ⟨u, ⟨hu.1, huc⟩, hu.2⟩
  have horb := holtDelta'_eq_orbit hY hBY hca hb
  refine odd_card_of_forall_mul_self_eq_one fun ⟨z, hz⟩ hzz => Subtype.ext ?_
  have hzz' : z * z = 1 := congrArg Subtype.val hzz
  have hza : z • a = a := (Subgroup.mem_inf.mp hz).1
  have hzc : z • c = c := (Subgroup.mem_inf.mp hz).2
  have hmem : ∀ x : longInvAt Y Δ c, z * (x : Y) * z⁻¹ ∈ longInvAt Y Δ c := fun x => by
    have := conj_mem_longInvAt x.2 z
    rwa [hzc] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz'
  obtain ⟨⟨x, hx⟩, hxz⟩ := exists_fixed_of_involutive
    (f := fun x : longInvAt Y Δ c => ⟨z * x * z⁻¹, hmem x⟩)
    (fun x => Subtype.ext (by
      show z * (z * x * z⁻¹) * z⁻¹ = x
      rw [hzinv]
      calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz', one_mul, mul_one])) hJc
  have hxz' : z * x * z⁻¹ = x := congrArg Subtype.val hxz
  have hcomm : z * x = x * z := by
    calc z * x = (z * x * z⁻¹) * z := by group
      _ = x * z := by rw [hxz']
  have hzx : z • x • a = x • a := by rw [← mul_smul, hcomm, mul_smul, hza]
  have hxa : x • a ∈ holtDelta' Y Δ c a := ⟨x, hx, rfl⟩
  rw [horb] at hxa
  obtain ⟨⟨k, hk⟩, hkb⟩ := hxa
  have hkb' : k • b = x • a := hkb
  have hkc : k • c = c := (Subgroup.mem_inf.mp hk).1
  have hka : k • a = a := (Subgroup.mem_inf.mp hk).2
  have hwa : (k⁻¹ * z * k) • a = a := by
    rw [mul_smul, mul_smul, hka, hza, inv_smul_eq_iff, hka]
  have hwb : (k⁻¹ * z * k) • b = b := by
    rw [mul_smul, mul_smul, hkb', hzx, ← hkb', inv_smul_smul]
  have hww : k⁻¹ * z * k * (k⁻¹ * z * k) = 1 := by
    calc k⁻¹ * z * k * (k⁻¹ * z * k) = k⁻¹ * (z * z) * k := by group
      _ = 1 := by rw [hzz']; group
  have hw := eq_one_of_mul_self_eq_one_of_odd_card hodd (g := ⟨k⁻¹ * z * k, hwa, hwb⟩)
    (Subtype.ext hww)
  have hw' : k⁻¹ * z * k = 1 := congrArg Subtype.val hw
  show z = 1
  calc z = k * (k⁻¹ * z * k) * k⁻¹ := by group
    _ = 1 := by rw [hw']; group

end Known

section EvenCase

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

omit [Finite G] [Finite Ω] in
theorem inducedHom_eq_one_of_odd_card {X : Subgroup G} {Δ : Set Ω} {hX : X ≤ stabilizer G Δ}
    {a c : Δ}
    (hodd : Odd (Nat.card ↥(stabilizer (inducedPerm X Δ hX) a ⊓
      stabilizer (inducedPerm X Δ hX) c)))
    {e : X} {k : ℕ} (he : e ^ 2 ^ k = 1) (hea : (e : G) • (a : Ω) = a)
    (hec : (e : G) • (c : Ω) = c) : inducedHom X Δ hX e = 1 := by
  have : Finite ↥(stabilizer (inducedPerm X Δ hX) a ⊓ stabilizer (inducedPerm X Δ hX) c) :=
    Nat.finite_of_card_ne_zero hodd.pos.ne'
  set y : inducedPerm X Δ hX := ⟨inducedHom X Δ hX e, e, rfl⟩
  have hy : y ∈ stabilizer (inducedPerm X Δ hX) a ⊓ stabilizer (inducedPerm X Δ hX) c :=
    ⟨Subtype.ext hea, Subtype.ext hec⟩
  have hpow : (⟨y, hy⟩ : ↥(stabilizer (inducedPerm X Δ hX) a ⊓
      stabilizer (inducedPerm X Δ hX) c)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [y, SubgroupClass.coe_pow, ← map_pow, he, map_one, OneMemClass.coe_one]
  have h1 := eq_one_of_pow_two_pow_eq_one_of_odd_card hodd hpow
  exact congrArg (fun z : ↥(stabilizer (inducedPerm X Δ hX) a ⊓
    stabilizer (inducedPerm X Δ hX) c) => ((z : inducedPerm X Δ hX) : Equiv.Perm Δ)) h1

theorem odd_card_stabilizer_inf_inducedPerm_normalizer {α β : Ω} {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β)) (hα : α ∈ fixSet Ω S)
    (hβ : β ∈ fixSet Ω S) :
    Odd (Nat.card ↥(stabilizer (inducedPerm (Subgroup.normalizer (S : Set G)) (fixSet Ω S)
        (normalizer_le_stabilizer_fixSet S)) (⟨α, hα⟩ : fixSet Ω S) ⊓
      stabilizer (inducedPerm (Subgroup.normalizer (S : Set G)) (fixSet Ω S)
        (normalizer_le_stabilizer_fixSet S)) (⟨β, hβ⟩ : fixSet Ω S))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine odd_card_of_forall_mul_self_eq_one fun ⟨y, hy⟩ hyy => Subtype.ext ?_
  have hyy' : y * y = 1 := congrArg Subtype.val hyy
  show y = 1
  by_contra hy1
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq, hyy']) hy1
  obtain ⟨R', hR'X, hR', hlift, hlift'⟩ :=
    exists_isPGroup_lift_inducedPerm (isPGroup_zpowers_of_orderOf_eq_two hord)
  have hyαβ := Subgroup.zpowers_le.mpr hy
  have hR'αβ : R' ≤ stabilizer G α ⊓ stabilizer G β := fun r hr => by
    obtain ⟨y', hy', hy'r⟩ := hlift r hr
    have h1 := (Subgroup.mem_inf.mp (hyαβ hy')).1
    have h2 := (Subgroup.mem_inf.mp (hyαβ hy')).2
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at h1 h2
    have e1 := hy'r ⟨α, hα⟩
    have e2 := hy'r ⟨β, hβ⟩
    rw [h1] at e1
    rw [h2] at e2
    exact Subgroup.mem_inf.mpr ⟨e1.symm, e2.symm⟩
  have hSR := hS.2.2 (S ⊔ R') (sup_le hS.1 hR'αβ) (hS.2.1.to_sup_of_normal_left' hR' hR'X)
    le_sup_left
  obtain ⟨r, hr, hry⟩ := hlift' y (Subgroup.mem_zpowers y)
  have hrS : r ∈ S := hSR ▸ Subgroup.mem_sup_right hr
  apply hy1
  refine Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_)
  rw [hry δ]
  exact δ.2 r hrS

omit [Finite Ω] in
theorem fusionIsSylowIn_of_odd_card_stabilizer_inf_inducedPerm_normalizer {α β γ : Ω}
    {S : Subgroup G} (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β))
    (hα : α ∈ fixSet Ω S) (hγ : γ ∈ fixSet Ω S)
    (hodd : Odd (Nat.card ↥(stabilizer (inducedPerm (Subgroup.normalizer (S : Set G))
        (fixSet Ω S) (normalizer_le_stabilizer_fixSet S)) (⟨α, hα⟩ : fixSet Ω S) ⊓
      stabilizer (inducedPerm (Subgroup.normalizer (S : Set G)) (fixSet Ω S)
        (normalizer_le_stabilizer_fixSet S)) (⟨γ, hγ⟩ : fixSet Ω S)))) :
    fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ : β ∈ fixSet Ω S := mem_fixSet_iff_le_stabilizer.mpr (hS.1.trans inf_le_right)
  refine ⟨le_inf (mem_fixSet_iff_le_stabilizer.mp hα) (mem_fixSet_iff_le_stabilizer.mp hγ),
    hS.2.1, fun Q hQ hQ2 hSQ => ?_⟩
  have hE : ∀ x ∈ Q, x ∈ Subgroup.normalizer (S : Set G) → x ∈ S := by
    intro x hxQ hxN
    have hEQ : S ⊔ Subgroup.zpowers x ≤ Q := sup_le hSQ (Subgroup.zpowers_le.mpr hxQ)
    have hEN : S ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN)
    have hE2 : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers x) := hQ2.to_le hEQ
    have hEβ : S ⊔ Subgroup.zpowers x ≤ stabilizer G β := by
      intro e he
      obtain ⟨k, hk⟩ := hE2 ⟨e, he⟩
      have hek : (⟨e, hEN he⟩ : Subgroup.normalizer (S : Set G)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      have heQ := hQ (hEQ he)
      have h1 := inducedHom_eq_one_of_odd_card hodd hek (Subgroup.mem_inf.mp heQ).1
        (Subgroup.mem_inf.mp heQ).2
      have h2 := congrArg (fun π : Equiv.Perm (fixSet Ω S) => ((π ⟨β, hβ⟩ : fixSet Ω S) : Ω)) h1
      simpa [coe_inducedHom_apply] using h2
    have hES : S ⊔ Subgroup.zpowers x = S :=
      hS.2.2 _ (le_inf ((hEQ.trans hQ).trans inf_le_left) hEβ) hE2 le_sup_left
    exact hES ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  by_contra hne
  have hlt : S.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm (fun q hq => ?_) hSQ)
    have hq' : (⟨q, hq⟩ : Q) ∈ S.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hq'
  have : Group.IsNilpotent Q := hQ2.isNilpotent
  obtain ⟨x, hxN, hxS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hSQ]
    exact hxN
  exact hxS (Subgroup.mem_subgroupOf.mpr (hE x x.2 (Subgroup.mem_subgroupOf.mp hxsub)))

theorem fusionIsSylowIn_inf_of_ne_bot (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta G Ω α β) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ))
    (hS1 : S ≠ ⊥) : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSab, u, hu, huγ, huS⟩ := lemma_3_2_i hG hB hαβ hγ hS
  have hα : α ∈ fixSet Ω S :=
    mem_fixSet_iff_le_stabilizer.mpr (hS.1.trans (inf_le_left.trans inf_le_left))
  have hβ : β ∈ fixSet Ω S :=
    mem_fixSet_iff_le_stabilizer.mpr (hS.1.trans (inf_le_left.trans inf_le_right))
  have hγS : γ ∈ fixSet Ω S := mem_fixSet_iff_le_stabilizer.mpr (hS.1.trans inf_le_right)
  have hγα : α ≠ γ := fun h => left_notMem_holtDelta hαβ (by rwa [← h] at hγ)
  have hγβ : β ≠ γ := fun h => right_notMem_holtDelta hαβ (by rwa [← h] at hγ)
  have h3 : 3 ≤ Nat.card (fixSet Ω S) := by
    have hsub : ({α, β, γ} : Set Ω) ⊆ fixSet Ω S := by
      rintro ω (rfl | rfl | rfl)
      exacts [hα, hβ, hγS]
    calc 3 = Nat.card ({α, β, γ} : Set Ω) := by
          rw [Nat.card_coe_set_eq, Set.ncard_eq_three.mpr ⟨α, β, γ, hαβ, hγα, hγβ, rfl⟩]
      _ ≤ Nat.card (fixSet Ω S) := Nat.card_mono (Set.toFinite _) hsub
  have hX : Subgroup.normalizer (S : Set G) ≤ stabilizer G (fixSet Ω S) :=
    normalizer_le_stabilizer_fixSet S
  have hY := isStarGroup_inducedPerm_fixSet hG hS.2.1 h3
    (Subgroup.centralizer_le_normalizer _) le_rfl
  have hBY := hB.induced_fixSet hS.2.1 hS1 (Subgroup.centralizer_le_normalizer _) le_rfl
    (Nat.card (fixSet Ω S) + 1)
  have huX : u ∈ Subgroup.normalizer (S : Set G) := Subgroup.centralizer_le_normalizer _ huS
  have hū : (⟨inducedHom _ (fixSet Ω S) hX ⟨u, huX⟩, ⟨u, huX⟩, rfl⟩ :
      inducedPerm _ (fixSet Ω S) hX) ∈
      longInvSwap (inducedPerm _ (fixSet Ω S) hX) (fixSet Ω S) ⟨α, hα⟩ ⟨β, hβ⟩ :=
    ⟨mem_longInv_inducedPerm_of_eq hY.odd_card hY.three_le_card hu.1 rfl, Subtype.ext hu.2⟩
  have hc : (⟨γ, hγS⟩ : fixSet Ω S) ∈
      holtDelta (inducedPerm _ (fixSet Ω S) hX) (fixSet Ω S) ⟨α, hα⟩ ⟨β, hβ⟩ :=
    ⟨_, hū, Subtype.ext huγ⟩
  have hab : (⟨α, hα⟩ : fixSet Ω S) ≠ ⟨β, hβ⟩ := fun h => hαβ (congrArg Subtype.val h)
  exact fusionIsSylowIn_of_odd_card_stabilizer_inf_inducedPerm_normalizer hSab hα hγS
    (odd_card_stabilizer_inf_of_mem_holtDelta hY hBY hab hc
      (odd_card_stabilizer_inf_inducedPerm_normalizer hSab hα hβ))

end EvenCase

section Sim

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

@[expose] def HoltSim (α β γ : Ω) : Prop :=
  ∃ g ∈ stabilizer G α, ∃ S : Subgroup G,
    fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β) ∧
      fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G (g • γ))

variable {G Ω} [Finite G]

theorem exists_map_conj_eq_of_fusionIsSylowIn {P Q K : Subgroup G}
    (hP : fusionIsSylowIn 2 P K) (hQ : fusionIsSylowIn 2 Q K) :
    ∃ k ∈ K, Q = P.map (MulAut.conj k).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkQ⟩ := exists_mem_conj_of_fusionIsSylowIn hP hQ
  refine ⟨k, hk, Subgroup.ext fun x => ?_⟩
  rw [hkQ, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem holtSim_refl (α β : Ω) : HoltSim G Ω α β β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, -, hS⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
    (bot_le : ⊥ ≤ stabilizer G α ⊓ stabilizer G β)
  exact ⟨1, one_mem _, S, hS, by rwa [one_smul]⟩

omit [Finite G] in
theorem holtSim_smul_right_iff {α β γ : Ω} {h : G} (hh : h ∈ stabilizer G α) :
    HoltSim G Ω α β (h • γ) ↔ HoltSim G Ω α β γ := by
  constructor
  · rintro ⟨g, hg, S, hS, hS'⟩
    exact ⟨g * h, mul_mem hg hh, S, hS, by rwa [mul_smul]⟩
  · rintro ⟨g, hg, S, hS, hS'⟩
    exact ⟨g * h⁻¹, mul_mem hg (inv_mem hh), S, hS, by rwa [mul_smul, inv_smul_smul]⟩

theorem holtSim_smul_left_iff {α β γ : Ω} {h : G} (hh : h ∈ stabilizer G α) :
    HoltSim G Ω α (h • β) γ ↔ HoltSim G Ω α β γ := by
  have key : ∀ {h : G}, h ∈ stabilizer G α → ∀ {β : Ω}, HoltSim G Ω α β γ →
      HoltSim G Ω α (h • β) γ := by
    rintro h hh β ⟨g, hg, S, hS, hS'⟩
    have hhα : h • α = α := hh
    refine ⟨h * g, mul_mem hh hg, S.map (MulAut.conj h).toMonoidHom, ?_, ?_⟩
    · simpa [hhα] using fusionIsSylowIn_map_conj hS h
    · simpa [hhα, mul_smul] using fusionIsSylowIn_map_conj hS' h
  refine ⟨fun h1 => ?_, key hh⟩
  have := key (inv_mem hh) h1
  rwa [inv_smul_smul] at this

theorem HoltSim.symm {α β γ : Ω} (h : HoltSim G Ω α β γ) : HoltSim G Ω α γ β := by
  obtain ⟨g, hg, S, hS, hS'⟩ := h
  exact (holtSim_smul_left_iff hg).mp ⟨1, one_mem _, S, hS', by rwa [one_smul]⟩

end Sim

section Lemma33

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

omit [Finite Ω] in
theorem eq_bot_iff_odd_card_of_fusionIsSylowIn {S K : Subgroup G}
    (hS : fusionIsSylowIn 2 S K) : S = ⊥ ↔ Odd (Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro rfl
    refine odd_card_of_forall_mul_self_eq_one fun g hg => ?_
    by_contra hg1
    have hord : orderOf (g : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq, hg]) hg1
    have h := hS.2.2 (Subgroup.zpowers (g : G)) (Subgroup.zpowers_le.mpr g.2)
      (isPGroup_zpowers_of_orderOf_eq_two hord) bot_le
    have : (g : G) ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers _
    exact hg1 (Subtype.ext (Subgroup.mem_bot.mp this))
  · intro hodd
    refine (Subgroup.eq_bot_iff_forall S).mpr fun s hs => ?_
    obtain ⟨k, hk⟩ := hS.2.1 ⟨s, hs⟩
    have h1 := eq_one_of_pow_two_pow_eq_one_of_odd_card hodd (g := ⟨s, hS.1 hs⟩) (a := k)
      (Subtype.ext (by simpa using congrArg Subtype.val hk))
    exact congrArg Subtype.val h1

omit [Finite G] [Finite Ω] in
theorem card_stabilizer_inf_smul {α β : Ω} {h : G} (hh : h ∈ stabilizer G α) :
    Nat.card ↥(stabilizer G α ⊓ stabilizer G (h • β)) =
      Nat.card ↥(stabilizer G α ⊓ stabilizer G β) := by
  have hhα : h • α = α := hh
  have e := map_conj_stabilizer_inf h α β
  rw [hhα] at e
  rw [← e, Subgroup.card_map_of_injective (MulAut.conj h).injective]

private theorem sum_eq_of_le_of_le (hG : IsStarGroup G Ω) {α : Ω} {A B : Finset Ω}
    (hA : ∀ β ∈ A, β ≠ α) (hAB : ∀ β ∈ A, β ∉ B) (hcov : ∀ β, β ≠ α → β ∈ A ∨ β ∈ B)
    (hBα : α ∉ B)
    (hAle : ∑ β ∈ A, Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) * A.card)
    (hBle : ∑ β ∈ B, Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) * B.card) :
    ∑ β ∈ A, Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) * A.card ∧
      ∑ β ∈ B, Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) * B.card := by
  classical
  have := Fintype.ofFinite Ω
  have hdisj : Disjoint A B := Finset.disjoint_left.mpr hAB
  have hunion : A ∪ B = Finset.univ.erase α := by
    ext β
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => h.elim (hA β) (fun hb h' => hBα (h' ▸ hb)), hcov β⟩
  have htot := sum_card_longInvSwap hG α
  rw [← hunion, Finset.sum_union hdisj] at htot
  have hcard : Fintype.card Ω - 1 = A.card + B.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ]
  rw [hcard, mul_add] at htot
  have key : ∀ a b x y : ℕ, a ≤ x → b ≤ y → a + b = x + y → a = x ∧ b = y := by
    intro a b x y h1 h2 h3
    omega
  exact key _ _ _ _ hAle hBle htot

private theorem parity_aux (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) (α : Ω) :
    (∀ β γ : Ω, γ ∈ holtDelta G Ω α β → γ ≠ α →
      ¬ Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G γ)) →
        ¬ Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))) ∧
    (∀ β : Ω, β ≠ α → Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β)) →
      Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite Ω
  set E : Finset Ω := Finset.univ.filter fun η =>
    η ≠ α ∧ ¬ Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G η)) with hE
  set O : Finset Ω := Finset.univ.filter fun η =>
    η ≠ α ∧ Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G η)) with hO
  have hmemE : ∀ η, η ∈ E ↔ η ≠ α ∧ ¬ Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G η)) :=
    fun η => by simp [hE]
  have hmemO : ∀ η, η ∈ O ↔ η ≠ α ∧ Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G η)) :=
    fun η => by simp [hO]
  have hEinv : ∀ h ∈ stabilizer G α, ∀ β ∈ E, h • β ∈ E := by
    intro h hh β hβ
    rw [hmemE] at hβ ⊢
    refine ⟨fun h' => hβ.1 ?_, by rw [card_stabilizer_inf_smul hh]; exact hβ.2⟩
    have hhα : h • α = α := hh
    rw [← hhα] at h'
    exact smul_left_cancel h h'
  have hEΔ : ∀ β ∈ E, holtDelta G Ω α β ⊆ E := by
    intro β hβ γ hγ
    rw [Finset.mem_coe, hmemE]
    rw [hmemE] at hβ
    have hαβ : α ≠ β := fun h => hβ.1 h.symm
    refine ⟨fun h => left_notMem_holtDelta hαβ (h ▸ hγ), fun hodd => ?_⟩
    obtain ⟨S, -, hS⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
      (bot_le : ⊥ ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)
    have hSab := fusionIsSylowIn_inf_of_mem_holtDelta hγ hS
    have hS1 : S ≠ ⊥ := fun h => hβ.2 ((eq_bot_iff_odd_card_of_fusionIsSylowIn hSab).mp h)
    exact hS1 ((eq_bot_iff_odd_card_of_fusionIsSylowIn
      (fusionIsSylowIn_inf_of_ne_bot hG hB hαβ hγ hS hS1)).mpr hodd)
  have hOle : ∑ β ∈ O, Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) * O.card := by
    have := Finset.sum_le_sum fun β hβ =>
      card_longInvSwap_le_of_odd_card (G := G) hG ((hmemO β).mp hβ).2
    rwa [Finset.sum_const, smul_eq_mul, mul_comm] at this
  obtain ⟨hEeq, hOeq⟩ := sum_eq_of_le_of_le hG (fun β hβ => ((hmemE β).mp hβ).1)
    (fun β hβ hβO => ((hmemE β).mp hβ).2 ((hmemO β).mp hβO).2)
    (fun β hβ => by
      by_cases h : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))
      · exact Or.inr ((hmemO β).mpr ⟨hβ, h⟩)
      · exact Or.inl ((hmemE β).mpr ⟨hβ, h⟩))
    (fun h => ((hmemO α).mp h).1 rfl)
    (sum_card_longInvSwap_le_of_holtDelta_subset hG hEinv hEΔ) hOle
  refine ⟨fun β γ hγ hγα hγe => ?_, fun β hβ hodd => ?_⟩
  · exact ((hmemE β).mp (mem_of_mem_holtDelta_of_sum_eq hG hEinv hEΔ hEeq hγ
      ((hmemE γ).mpr ⟨hγα, hγe⟩))).2
  · have hsum : ∑ β ∈ O, Nat.card (longInvSwap G Ω α β) =
        ∑ _β ∈ O, Nat.card (longInvAt G Ω α) := by
      rw [hOeq, Finset.sum_const, smul_eq_mul, mul_comm]
    exact (Finset.sum_eq_sum_iff_of_le fun β hβ =>
      card_longInvSwap_le_of_odd_card (G := G) hG ((hmemO β).mp hβ).2).mp hsum β
        ((hmemO β).mpr ⟨hβ, hodd⟩)

omit [Finite Ω] in
theorem fusionIsSylowIn_bot_of_odd_card {K : Subgroup G} (hK : Odd (Nat.card K)) :
    fusionIsSylowIn 2 ⊥ K := by
  refine ⟨bot_le, IsPGroup.of_bot, fun P hPK hP _ => (Subgroup.eq_bot_iff_forall P).mpr
    fun p hp => ?_⟩
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have h1 := eq_one_of_pow_two_pow_eq_one_of_odd_card hK (g := ⟨p, hPK hp⟩) (a := k)
    (Subtype.ext (by simpa using congrArg Subtype.val hk))
  exact congrArg Subtype.val h1

theorem odd_card_stabilizer_inf_of_mem_holtDelta_of_odd
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β γ : Ω}
    (hγ : γ ∈ holtDelta G Ω α β) (hodd : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))) :
    Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G γ)) := by
  by_cases hγα : γ = α
  · subst hγα
    by_cases hαβ : γ = β
    · subst hαβ
      exact hodd
    · exact absurd hγ (left_notMem_holtDelta hαβ)
  by_contra h
  exact (parity_aux hG hB α).1 β γ hγ hγα h hodd

theorem card_longInvSwap_eq_of_odd_card
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β : Ω}
    (hodd : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))) :
    Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) := by
  by_cases hβα : β = α
  · rw [hβα, longInvSwap_self]
  exact (parity_aux hG hB α).2 β hβα hodd

theorem lemma_3_3_ii_sylow (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta G Ω α β) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)) :
    fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β) ∧
      fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G γ) ∧
        fusionIsSylowIn 2 S (stabilizer G β ⊓ stabilizer G γ) := by
  have hSab := fusionIsSylowIn_inf_of_mem_holtDelta hγ hS
  have hγ' : γ ∈ holtDelta G Ω β α := by rwa [holtDelta_comm]
  have hS' : fusionIsSylowIn 2 S (stabilizer G β ⊓ stabilizer G α ⊓ stabilizer G γ) := by
    rwa [inf_comm (stabilizer G β)]
  refine ⟨hSab, ?_⟩
  by_cases hS1 : S = ⊥
  · have hodd := (eq_bot_iff_odd_card_of_fusionIsSylowIn hSab).mp hS1
    have hodd' : Odd (Nat.card ↥(stabilizer G β ⊓ stabilizer G α)) := by
      rwa [inf_comm]
    subst hS1
    exact ⟨fusionIsSylowIn_bot_of_odd_card
        (odd_card_stabilizer_inf_of_mem_holtDelta_of_odd hG hB hγ hodd),
      fusionIsSylowIn_bot_of_odd_card
        (odd_card_stabilizer_inf_of_mem_holtDelta_of_odd hG hB hγ' hodd')⟩
  · exact ⟨fusionIsSylowIn_inf_of_ne_bot hG hB hαβ hγ hS hS1,
      fusionIsSylowIn_inf_of_ne_bot hG hB hαβ.symm hγ' hS' hS1⟩

omit [Finite Ω] in
theorem smul_mem_of_holtSim_closed {α : Ω} {Λ : Set Ω} (hΛα : ∀ β ∈ Λ, β ≠ α)
    (hΛ : ∀ β ∈ Λ, ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ Λ) {h : G}
    (hh : h ∈ stabilizer G α) {β : Ω} (hβ : β ∈ Λ) : h • β ∈ Λ := by
  refine hΛ β hβ _ (fun h' => hΛα β hβ ?_) ((holtSim_smul_right_iff hh).mpr (holtSim_refl α β))
  have hhα : h • α = α := hh
  rw [← hhα] at h'
  exact smul_left_cancel h h'

theorem holtDelta_subset_of_holtSim_closed
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω}
    {Λ : Set Ω} (hΛα : ∀ β ∈ Λ, β ≠ α)
    (hΛ : ∀ β ∈ Λ, ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ Λ) {β : Ω} (hβ : β ∈ Λ) :
    holtDelta G Ω α β ⊆ Λ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro γ hγ
  have hαβ : α ≠ β := fun h => hΛα β hβ h.symm
  obtain ⟨S, -, hS⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
    (bot_le : ⊥ ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)
  obtain ⟨h1, h2, -⟩ := lemma_3_3_ii_sylow hG hB hαβ hγ hS
  exact hΛ β hβ γ (fun h => left_notMem_holtDelta hαβ (h ▸ hγ))
    ⟨1, one_mem _, S, h1, by rwa [one_smul]⟩

theorem lemma_3_3_i (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α : Ω} {Λ : Finset Ω}
    (hΛα : ∀ β ∈ Λ, β ≠ α) (hΛ : ∀ β ∈ Λ, ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ Λ) :
    ∑ β ∈ Λ, Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) * Λ.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite Ω
  set Λ' : Finset Ω := Finset.univ.filter fun η => η ≠ α ∧ η ∉ Λ with hΛ'
  have hmem' : ∀ η, η ∈ Λ' ↔ η ≠ α ∧ η ∉ Λ := fun η => by simp [hΛ']
  have hΛα' : ∀ β ∈ (Λ : Set Ω), β ≠ α := hΛα
  have hΛ'' : ∀ β ∈ (Λ : Set Ω), ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ (Λ : Set Ω) := hΛ
  have hinv : ∀ h ∈ stabilizer G α, ∀ β ∈ Λ, h • β ∈ Λ := fun h hh β hβ =>
    smul_mem_of_holtSim_closed hΛα' hΛ'' hh hβ
  have hΔ : ∀ β ∈ Λ, holtDelta G Ω α β ⊆ Λ := fun β hβ =>
    holtDelta_subset_of_holtSim_closed hG hB hΛα' hΛ'' hβ
  have hinv' : ∀ h ∈ stabilizer G α, ∀ β ∈ Λ', h • β ∈ Λ' := by
    intro h hh β hβ
    rw [hmem'] at hβ ⊢
    refine ⟨fun h' => hβ.1 ?_, fun h' => hβ.2 ?_⟩
    · have hhα : h • α = α := hh
      rw [← hhα] at h'
      exact smul_left_cancel h h'
    · have := hinv _ (inv_mem hh) _ h'
      rwa [inv_smul_smul] at this
  have hΔ' : ∀ β ∈ Λ', holtDelta G Ω α β ⊆ Λ' := by
    intro β hβ γ hγ
    rw [hmem'] at hβ
    rw [Finset.mem_coe, hmem']
    have hαβ : α ≠ β := fun h => hβ.1 h.symm
    refine ⟨fun h => left_notMem_holtDelta hαβ (h ▸ hγ), fun hγΛ => hβ.2 ?_⟩
    obtain ⟨S, -, hS⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
      (bot_le : ⊥ ≤ stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G γ)
    obtain ⟨h1, h2, -⟩ := lemma_3_3_ii_sylow hG hB hαβ hγ hS
    exact hΛ γ hγΛ β hβ.1 (HoltSim.symm ⟨1, one_mem _, S, h1, by rwa [one_smul]⟩)
  exact (sum_eq_of_le_of_le hG hΛα (fun β hβ hβ' => ((hmem' β).mp hβ').2 hβ)
    (fun β hβ => by
      by_cases h : β ∈ Λ
      exacts [Or.inl h, Or.inr ((hmem' β).mpr ⟨hβ, h⟩)])
    (fun h => ((hmem' α).mp h).1 rfl)
    (sum_card_longInvSwap_le_of_holtDelta_subset hG hinv hΔ)
    (sum_card_longInvSwap_le_of_holtDelta_subset hG hinv' hΔ')).1

theorem lemma_3_3_iii_exists (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta' G Ω α β) :
    ∃ S : Subgroup G, fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β) ∧
      S ≤ stabilizer G γ ∧ ∃ u ∈ longInvAt G Ω α, u • β = γ ∧
        u ∈ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαΔ : α ∈ holtDelta G Ω β γ := mem_holtDelta'_iff.mp hγ
  have hβγ : β ≠ γ := by
    obtain ⟨s, hs, hsβ⟩ := hγ
    intro h
    exact hαβ ((smul_eq_iff_of_mem_longInvAt hs β).mp (hsβ.trans h.symm)).symm
  obtain ⟨T, -, hT⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
    (bot_le : ⊥ ≤ stabilizer G β ⊓ stabilizer G γ ⊓ stabilizer G α)
  obtain ⟨-, u, hu, huα, huT⟩ := lemma_3_2_i hG hB hβγ hαΔ hT
  obtain ⟨-, h2, -⟩ := lemma_3_3_ii_sylow hG hB hβγ hαΔ hT
  exact ⟨T, by rwa [inf_comm], hT.1.trans (inf_le_left.trans inf_le_right), u, ⟨hu.1, huα⟩,
    hu.2, huT⟩

omit [Finite G] [Finite Ω] in
theorem conj_mem_centralizer_map_conj {T : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.centralizer (T : Set G)) (k : G) :
    k * u * k⁻¹ ∈ Subgroup.centralizer ((T.map (MulAut.conj k).toMonoidHom : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hxu : x * u = u * x := Subgroup.mem_centralizer_iff.mp hu x hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc k * x * k⁻¹ * (k * u * k⁻¹) = k * (x * u) * k⁻¹ := by group
    _ = k * (u * x) * k⁻¹ := by rw [hxu]
    _ = k * u * k⁻¹ * (k * x * k⁻¹) := by group

theorem lemma_3_3_iii_centralizer (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β : Ω} (hαβ : α ≠ β)
    {S : Subgroup G} (hS : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β)) :
    ∃ u ∈ longInvAt G Ω α, u ∈ Subgroup.centralizer (S : Set G) := by
  obtain ⟨γ, hγ⟩ := holtDelta'_nonempty hG α β
  obtain ⟨T, hT, -, u, hu, -, huT⟩ := lemma_3_3_iii_exists hG hB hαβ hγ
  obtain ⟨k, hk, hkS⟩ := exists_map_conj_eq_of_fusionIsSylowIn hT hS
  have hkα : k • α = α := (Subgroup.mem_inf.mp hk).1
  refine ⟨k * u * k⁻¹, by simpa [hkα] using conj_mem_longInvAt hu k, ?_⟩
  rw [hkS]
  exact conj_mem_centralizer_map_conj huT k

theorem lemma_3_3_iii_orbit (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {α β γ : Ω} (hαβ : α ≠ β)
    (hγ : γ ∈ holtDelta' G Ω α β) :
    holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine holtDelta'_eq_orbit_of_subset hγ ?_
  by_cases hodd : Odd (Nat.card ↥(stabilizer G α ⊓ stabilizer G β))
  · obtain ⟨u, hu⟩ := longInvSwap_nonempty hG α β
    obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
    have hcard := card_longInvSwap_eq_of_odd_card hG hB hodd
    have hinj : Function.Injective (fun s : longInvSwap G Ω α β =>
        (⟨((s : G) * u) * t * ((s : G) * u)⁻¹, conj_mul_mem_longInvAt' ht hu s.2⟩ :
          longInvAt G Ω α)) := fun s s' h =>
      Subtype.ext (eq_of_conj_mul_eq_of_odd_card hodd ht hu s.2 s'.2 (congrArg Subtype.val h))
    have hsurj := (hinj.bijective_of_nat_card_le hcard.ge).2
    have hmem : ∀ δ ∈ holtDelta' G Ω α β,
        δ ∈ orbit ↥(stabilizer G α ⊓ stabilizer G β) (t • β) := by
      rintro _ ⟨s'', hs'', rfl⟩
      obtain ⟨⟨s, hs⟩, hfs⟩ := hsurj ⟨s'', hs''⟩
      have hsu := mul_mem_stabilizer_inf_of_mem_longInvSwap hs hu
      refine ⟨⟨s * u, hsu⟩, ?_⟩
      have e : s'' = (s * u) * t * (s * u)⁻¹ := (congrArg Subtype.val hfs).symm
      have hβ : (s * u)⁻¹ • β = β := by
        rw [inv_smul_eq_iff, mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hsu).2]
      show (s * u) • t • β = s'' • β
      rw [e]
      calc (s * u) • t • β = (s * u) • t • (s * u)⁻¹ • β := by rw [hβ]
        _ = ((s * u) * t * (s * u)⁻¹) • β := by simp only [mul_smul]
    rw [orbit_eq_iff.mpr (hmem γ hγ)]
    exact hmem
  intro γ' hγ'
  obtain ⟨T, hT, hTγ, u, hu, huβ, huT⟩ := lemma_3_3_iii_exists hG hB hαβ hγ
  obtain ⟨T', hT', hTγ', u', hu', hu'β, hu'T'⟩ := lemma_3_3_iii_exists hG hB hαβ hγ'
  obtain ⟨k, hk, hkT⟩ := exists_map_conj_eq_of_fusionIsSylowIn hT' hT
  have hkα : k • α = α := (Subgroup.mem_inf.mp hk).1
  have hkβ : k • β = β := (Subgroup.mem_inf.mp hk).2
  have hT1 : T ≠ ⊥ := fun h => hodd ((eq_bot_iff_odd_card_of_fusionIsSylowIn hT).mp h)
  have hα : α ∈ fixSet Ω T := mem_fixSet_iff_le_stabilizer.mpr (hT.1.trans inf_le_left)
  have hβ : β ∈ fixSet Ω T := mem_fixSet_iff_le_stabilizer.mpr (hT.1.trans inf_le_right)
  have hγT : γ ∈ fixSet Ω T := mem_fixSet_iff_le_stabilizer.mpr hTγ
  have hkγ' : k • γ' ∈ fixSet Ω T := by
    rw [hkT]
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul, inv_smul_smul]
    rw [mem_stabilizer_iff.mp (hTγ' hx)]
  have hwJ : k * u' * k⁻¹ ∈ longInvAt G Ω α := by simpa [hkα] using conj_mem_longInvAt hu' k
  have hwβ : (k * u' * k⁻¹) • β = k • γ' := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hkβ.symm, hu'β]
  have hwT : k * u' * k⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    rw [hkT]
    exact conj_mem_centralizer_map_conj hu'T' k
  have hγα : γ ≠ α := fun h => notMem_holtDelta' (G := G) (Ne.symm hαβ) (h ▸ hγ)
  have hγβ : β ≠ γ := fun h => hαβ ((smul_eq_iff_of_mem_longInvAt hu β).mp
    (huβ.trans h.symm)).symm
  have h3 : 3 ≤ Nat.card (fixSet Ω T) := by
    have hsub : ({α, β, γ} : Set Ω) ⊆ fixSet Ω T := by
      rintro ω (rfl | rfl | rfl)
      exacts [hα, hβ, hγT]
    calc 3 = Nat.card ({α, β, γ} : Set Ω) := by
          rw [Nat.card_coe_set_eq, Set.ncard_eq_three.mpr ⟨α, β, γ, hαβ, Ne.symm hγα, hγβ, rfl⟩]
      _ ≤ Nat.card (fixSet Ω T) := Nat.card_mono (Set.toFinite _) hsub
  have hX : Subgroup.centralizer (T : Set G) ≤ stabilizer G (fixSet Ω T) :=
    centralizer_le_stabilizer_fixSet T
  have hY := isStarGroup_inducedPerm_fixSet hG hT.2.1 h3 le_rfl
    (Subgroup.centralizer_le_normalizer _)
  have hBY := hB.induced_fixSet hT.2.1 hT1 le_rfl (Subgroup.centralizer_le_normalizer _)
    (Nat.card (fixSet Ω T) + 1)
  have himg : ∀ {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G)), x ∈ longInvAt G Ω α →
      (⟨inducedHom _ (fixSet Ω T) hX ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩ : inducedPerm _ (fixSet Ω T) hX) ∈
        longInvAt (inducedPerm _ (fixSet Ω T) hX) (fixSet Ω T) ⟨α, hα⟩ := fun hx hxα =>
    ⟨mem_longInv_inducedPerm_of_eq hY.odd_card hY.three_le_card hxα.1 rfl, Subtype.ext hxα.2⟩
  have hc : (⟨γ, hγT⟩ : fixSet Ω T) ∈
      holtDelta' (inducedPerm _ (fixSet Ω T) hX) (fixSet Ω T) ⟨α, hα⟩ ⟨β, hβ⟩ :=
    ⟨_, himg huT hu, Subtype.ext huβ⟩
  have hc' : (⟨k • γ', hkγ'⟩ : fixSet Ω T) ∈
      holtDelta' (inducedPerm _ (fixSet Ω T) hX) (fixSet Ω T) ⟨α, hα⟩ ⟨β, hβ⟩ :=
    ⟨_, himg hwT hwJ, Subtype.ext hwβ⟩
  have hab : (⟨α, hα⟩ : fixSet Ω T) ≠ ⟨β, hβ⟩ := fun h => hαβ (congrArg Subtype.val h)
  rw [holtDelta'_eq_orbit hY hBY hab hc] at hc'
  obtain ⟨⟨y, hy⟩, hyc⟩ := hc'
  obtain ⟨x, -, hx⟩ := mem_inducedPerm.mp y.2
  have hxα : x • α = α := by
    have h1 := (Subgroup.mem_inf.mp hy).1
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at h1
    have := hx ⟨α, hα⟩
    rw [h1] at this
    exact this.symm
  have hxβ : x • β = β := by
    have h1 := (Subgroup.mem_inf.mp hy).2
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at h1
    have := hx ⟨β, hβ⟩
    rw [h1] at this
    exact this.symm
  have hxγ : x • γ = k • γ' := by
    have := hx ⟨γ, hγT⟩
    have h1 := congrArg Subtype.val hyc
    exact this.symm.trans h1
  refine ⟨⟨k⁻¹ * x, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩, ?_⟩
  · rw [mem_stabilizer_iff, mul_smul, hxα, inv_smul_eq_iff, hkα]
  · rw [mem_stabilizer_iff, mul_smul, hxβ, inv_smul_eq_iff, hkβ]
  · show (k⁻¹ * x) • γ = γ'
    rw [mul_smul, hxγ, inv_smul_smul]

end Lemma33

end CFSG.Holt.H78
