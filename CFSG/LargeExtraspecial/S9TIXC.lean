module

public import CFSG.LargeExtraspecial.S9TIXB
public import CFSG.LargeExtraspecial.S9TIInput

public section

namespace CFSG.LargeExtraspecial.S9.TIX

open CFSG.CGT.Timmesfeld75 Subgroup

universe u

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj_subgroupOf {X T : Subgroup G} (y z : X) :
    z ∈ (T.subgroupOf X).map (MulAut.conj y).toMonoidHom ↔
      (z : G) ∈ conjSubgroup (y : G) T := by
  rw [mem_map, mem_conjSubgroup]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_subgroupOf] at hw
    simpa [MulAut.conj_apply, mul_assoc] using hw
  · intro hz
    refine ⟨y⁻¹ * z * y, ?_, ?_⟩
    · rw [mem_subgroupOf]
      simpa using hz
    · simp [MulAut.conj_apply, mul_assoc]

namespace Setup

variable {A Ab L Lb M : Subgroup G} (S : Setup A Ab L Lb M)
include S

theorem exists_conj_eq : ∃ x ∈ A ⊔ Ab, Ab = conjSubgroup x A := by
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have haa : a * a = 1 := S.sqA a ha
  have hbb : b * b = 1 := S.sqAb b hb
  have haX : a ∈ A ⊔ Ab := mem_sup_left ha
  have hbX : b ∈ A ⊔ Ab := mem_sup_right hb
  have hclX : closure ({b, a} : Set G) ≤ A ⊔ Ab := by
    rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hbX, haX⟩
  have hcrit : ∀ d ∈ A ⊔ Ab, (d⁻¹ * a * d) * b = b * (d⁻¹ * a * d) →
      ∃ x ∈ A ⊔ Ab, Ab = conjSubgroup x A := by
    intro d hd hcomm
    refine ⟨d⁻¹, inv_mem hd, (S.conj_eq_of_commutator_mem hd ha haL hb hbL ?_).symm⟩
    rw [show (d⁻¹ * a * d) * b * (d⁻¹ * a * d)⁻¹ * b⁻¹ =
      ((d⁻¹ * a * d) * b) * (b * (d⁻¹ * a * d))⁻¹ by group, hcomm, mul_inv_cancel]
    exact one_mem _
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨m, hm⟩ | ⟨k, hk⟩
  · have hm0 : 0 < m := by
      have := orderOf_pos (a * b)
      omega
    have hord : orderOf (b * a) = 2 * m := by
      have h1 : b * a = (a * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
      rw [h1, orderOf_inv]
      omega
    obtain ⟨z, hzz, hz1, hbz, haz, hconjz⟩ := dihedral_central_of_even_order_mem hbb haa hm0 hord
    rcases hconjz with ⟨g, hg, hgz⟩ | ⟨g, hg, hgz⟩
    ·
      refine hcrit g⁻¹ (inv_mem (hclX hg)) ?_
      have h1 : a * (g⁻¹ * b * g) = (g⁻¹ * b * g) * a := by
        rw [← hgz]
        calc a * (a * z) = a * (z * a) := by rw [haz]
          _ = a * z * a := by group
      rw [inv_inv]
      calc g * a * g⁻¹ * b = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by rw [h1]
        _ = b * (g * a * g⁻¹) := by group
    ·
      exfalso
      have hcom : a * (g⁻¹ * a * g) * a⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ M := by
        rw [← hgz]
        have e : a * (a * z) * a⁻¹ * (a * z)⁻¹ = 1 := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa]
          calc a * (a * z) * a * (z⁻¹ * a) = a * (a * (z * a)) * z⁻¹ * a := by group
            _ = a * (a * (a * z)) * z⁻¹ * a := by rw [haz]
            _ = 1 := by
              rw [show a * (a * (a * z)) * z⁻¹ * a = (a * a) * (a * a) by group, haa, one_mul]
        rw [e]
        exact one_mem _
      have hgA := S.conj_mem_of_commutator_mem (hclX hg) ha haL ha haL hcom
      rw [← hgz] at hgA
      have hzA : z ∈ A := by
        have := mul_mem (inv_mem ha) hgA
        rwa [inv_mul_cancel_left] at this
      exact hbL (S.mem_Lb_of_commute hb hzA hz1 hbz)
  ·
    have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts haa hbb) (k + 1)
    have hpow : (a * b) ^ (2 * (k + 1)) = a * b := by
      rw [show 2 * (k + 1) = orderOf (a * b) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [hpow] at h1
    have hbconj : ((a * b) ^ (k + 1))⁻¹ * a * (a * b) ^ (k + 1) = b := by
      rw [h1]
      exact (invol_eq_inv_mul_mul hbb).symm
    have hd : (a * b) ^ (k + 1) ∈ A ⊔ Ab := pow_mem (mul_mem haX hbX) _
    refine hcrit _ hd ?_
    rw [hbconj]

end Setup

theorem Setup.exists_conj_ne_of_tiPairInput {G : Type u} [Group G] [Finite G]
    {A Ab L Lb M : Subgroup G} (S : Setup A Ab L Lb M) (hTI : TIPairInput.{u})
    (h4 : 4 * Nat.card L ≤ Nat.card A) {t : G} (htL : t ∈ L) (ht1 : t ≠ 1) :
    ∃ x ∈ A ⊔ Ab, x * t * x⁻¹ ∈ A ∧ x * t * x⁻¹ ≠ t := by
  set X := A ⊔ Ab with hXdef
  obtain ⟨y, hyX, hy⟩ := S.exists_conj_eq
  set A' : Subgroup X := A.subgroupOf X with hA'
  set y' : X := ⟨y, hyX⟩ with hy'
  have hB' : ∀ z : X, z ∈ A'.map (MulAut.conj y').toMonoidHom ↔ (z : G) ∈ Ab := by
    intro z
    rw [mem_map_conj_subgroupOf, ← hy]
  have hN' : ∀ z : X, z ∈ normalizer (A'.map (MulAut.conj y').toMonoidHom : Set X) ↔
      (z : G) ∈ normalizer (Ab : Set G) := by
    intro z
    rw [mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro h w
      by_cases hwX : w ∈ X
      · have := h ⟨w, hwX⟩
        rw [hB', hB'] at this
        simpa using this
      · constructor
        · intro hw
          exact absurd (mem_sup_right hw) hwX
        · intro hw
          exfalso
          apply hwX
          have h1 : (z : G) * w * (z : G)⁻¹ ∈ X := mem_sup_right hw
          have := mul_mem (mul_mem (inv_mem z.2) h1) z.2
          rwa [show (z : G)⁻¹ * ((z : G) * w * (z : G)⁻¹) * z = w by group] at this
    · intro h w
      rw [hB', hB']
      simpa using h w
  have hLX : L ≤ X := S.L_le.trans le_sup_left
  have hinf : A' ⊓ normalizer (A'.map (MulAut.conj y').toMonoidHom : Set X) = L.subgroupOf X := by
    ext z
    rw [mem_inf, hN', mem_subgroupOf, mem_subgroupOf, S.mem_L]
  have hsq : ∀ a ∈ A', a * a = 1 := fun a ha => Subtype.ext (S.sqA _ ha)
  have hti : ∀ x : X, A' ⊓ A'.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      A' ⊓ A'.map (MulAut.conj x).toMonoidHom = A' := by
    intro x
    by_cases hne : A ⊓ conjSubgroup (x : G) A = ⊥
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := mem_inf.mp hz
      rw [mem_map_conj_subgroupOf] at hz2
      have : (z : G) ∈ A ⊓ conjSubgroup (x : G) A := mem_inf.mpr ⟨hz1, hz2⟩
      rw [hne, mem_bot] at this
      exact (mem_bot).mpr (Subtype.ext this)
    · right
      have heq := S.tiA x x.2 hne
      refine le_antisymm inf_le_left (le_inf le_rfl fun z hz => ?_)
      rw [mem_map_conj_subgroupOf, heq]
      exact hz
  have hcardL : Nat.card (L.subgroupOf X) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hLX).toEquiv
  have hcardA : Nat.card A' = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : A ≤ X)).toEquiv
  have hne : A' ⊓ normalizer (A'.map (MulAut.conj y').toMonoidHom : Set X) ≠ ⊥ := by
    rw [hinf]
    intro hbot
    apply S.ne_bot
    rw [eq_bot_iff]
    intro l hl
    have : (⟨l, hLX hl⟩ : X) ∈ L.subgroupOf X := hl
    rw [hbot, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have h4' : 4 * Nat.card ↥(A' ⊓ normalizer (A'.map (MulAut.conj y').toMonoidHom : Set X)) ≤
      Nat.card A' := by
    rw [hinf, hcardL, hcardA]
    exact h4
  have ht' : (⟨t, hLX htL⟩ : X) ∈
      A' ⊓ normalizer (A'.map (MulAut.conj y').toMonoidHom : Set X) := by
    rw [hinf]
    exact htL
  have ht1' : (⟨t, hLX htL⟩ : X) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨x, -, hxA, hxt⟩ := hTI X A' y' hsq hti hne h4' _ ht' ht1'
  refine ⟨x, x.2, hxA, fun h => hxt (Subtype.ext ?_)⟩
  simpa using h

end CFSG.LargeExtraspecial.S9.TIX
