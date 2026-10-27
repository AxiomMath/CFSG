module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVY

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem isSylowOf_of_normalizer_D4 {p : ℕ} [Fact p.Prime] {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q)
    (hN : ∀ g ∈ K, g ∈ normalizer (Q : Set G) → (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ Q) :
    IsSylowOf p Q K := by
  obtain ⟨T, hT⟩ := (hQ.comap_subtype : IsPGroup p (Q.subgroupOf K)).exists_le_sylow
  set P : Subgroup G := (T : Subgroup K).map K.subtype with hP
  have hPK : P ≤ K := map_subtype_le _
  have hQP : Q ≤ P := fun x hx => ⟨⟨x, hQK hx⟩, hT hx, rfl⟩
  have hPp : IsPGroup p P := T.isPGroup'.map _
  suffices hPQ : P ≤ Q from ⟨T, le_antisymm hPQ hQP⟩
  by_contra hne
  have : Group.IsNilpotent P := hPp.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ Q.subgroupOf P := htop ▸ mem_top _
    exact this
  obtain ⟨s, hsN, hsQ⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine hsQ (hN s (hPK s.2) (mem_normalizer_fintype fun x hx => ?_) ?_)
  · exact (mem_normalizer_iff.1 hsN ⟨x, hQP hx⟩).1 hx
  · obtain ⟨k, hk⟩ := hPp s
    exact ⟨k, by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩

theorem card_inf_centralizer_eq_of_coprime_D4 {p : ℕ} [Fact p.Prime] {P N A : Subgroup G}
    (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G)) (hAP : A ≤ normalizer (P : Set G))
    (hAN : A ≤ normalizer (N : Set G)) (hN : IsPGroup p N) (hA : ¬ p ∣ Nat.card A)
    (htriv : ∀ a ∈ A, ∀ x ∈ P, x⁻¹ * (a * x * a⁻¹) ∈ N) :
    Nat.card (P ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card (N ⊓ centralizer (A : Set G) : Subgroup G) * N.relIndex P := by
  classical
  have hlift : ∀ x ∈ P, ∃ c ∈ P ⊓ centralizer (A : Set G), c⁻¹ * x ∈ N := by
    intro x hx
    let : MulDistribMulAction A P := Subgroup.conjMulDistribMulActionOfLeNormalizer A P hAP
    have hsmul : ∀ (a : A) (y : P), ((a • y : P) : G) = a * y * (a : G)⁻¹ := fun _ _ => rfl
    have : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hNP).2 hPN
    have hinv : CFSG.IsInvariant A P (N.subgroupOf P) := ⟨fun a y => by
      rw [mem_subgroupOf, mem_subgroupOf, hsmul]
      exact mem_normalizer_iff.1 (hAN a.2) y⟩
    have hNp : IsPGroup p (N.subgroupOf P) := hN.comap_subtype
    have hsolv : Group.IsSolvable (N.subgroupOf P) := by
      have := hNp.isNilpotent
      infer_instance
    have hcop : Nat.Coprime (Nat.card A) (Nat.card (N.subgroupOf P)) := by
      obtain ⟨k, hk⟩ := hNp.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hA).symm
    have hl := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting (N.subgroupOf P)
      hinv hsolv hcop
    let : MulDistribMulAction A (P ⧸ N.subgroupOf P) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := P) (N.subgroupOf P) hinv
    let : MulAction.QuotientAction A (N.subgroupOf P) :=
      CFSG.quotientAction_of_isInvariant (A := A) (N.subgroupOf P) hinv
    have hx' : ((⟨x, hx⟩ : P) : P ⧸ N.subgroupOf P) ∈
        CFSG.fixedPointSubgroup A (P ⧸ N.subgroupOf P) := by
      intro a
      rw [MulAction.Quotient.smul_coe (H := N.subgroupOf P) a ⟨x, hx⟩, QuotientGroup.eq,
        mem_subgroupOf]
      change ((a : G) * x * (a : G)⁻¹)⁻¹ * x ∈ N
      have e : ((a : G) * x * (a : G)⁻¹)⁻¹ * x = (x⁻¹ * ((a : G) * x * (a : G)⁻¹))⁻¹ := by group
      rw [e]
      exact inv_mem (htriv _ a.2 x hx)
    rw [hl] at hx'
    obtain ⟨c, hc, hcx⟩ := hx'
    refine ⟨c, ⟨c.2, mem_centralizer_iff.2 fun a ha => ?_⟩, ?_⟩
    · have h2 : a * c * a⁻¹ = c := congrArg Subtype.val (hc ⟨a, ha⟩)
      calc a * c = a * c * a⁻¹ * a := by group
        _ = c * a := by rw [h2]
    · have h3 : ((c : P) : P ⧸ N.subgroupOf P) = ((⟨x, hx⟩ : P) : P ⧸ N.subgroupOf P) := hcx
      have h4 : c⁻¹ * (⟨x, hx⟩ : P) ∈ N.subgroupOf P := QuotientGroup.eq.1 h3
      exact h4
  set F := P ⊓ centralizer (A : Set G) with hF
  have hset : (F : Set G) * (N : Set G) = (P : Set G) := by
    ext x
    constructor
    · rintro ⟨c, hc, n, hn, rfl⟩
      exact mul_mem hc.1 (hNP hn)
    · intro hx
      obtain ⟨c, hc, hcx⟩ := hlift x hx
      exact ⟨c, hc, c⁻¹ * x, hcx, by group⟩
  have h1 := ncard_mul_mul_card_inf F N
  rw [hset, ← Nat.card_coe_set_eq] at h1
  have hFN : F ⊓ N = N ⊓ centralizer (A : Set G) := by
    rw [hF, inf_comm P, inf_assoc, inf_eq_right.2 hNP, inf_comm]
  rw [hFN] at h1
  have h2 := Subgroup.relIndex_mul_card N P
  rw [inf_eq_left.2 hNP] at h2
  have h1' : N.relIndex P * Nat.card N * Nat.card (N ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card F * Nat.card N := by
    rw [h2]
    exact h1
  have hpos : 0 < Nat.card N := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card F * Nat.card N =
      N.relIndex P * Nat.card N * Nat.card (N ⊓ centralizer (A : Set G) : Subgroup G) := h1'.symm
    _ = _ := by ring

end Generic

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

@[expose] def sylowJ₀ : Subgroup X := d.S ⊓ centralizer (d.J₀ : Set X)

theorem x₂_mem_centralizer_J₀ (a : d.Γ₀) : d.x₂ a ∈ centralizer (d.J₀ : Set X) :=
  le_centralizer_iff.1 (d.J₀_le_J₂.trans inf_le_right) (d.x₂_mem_U₂ a)

theorem x₅_mem_centralizer_J₀ (a : d.Γ₀) : d.x₅ a ∈ centralizer (d.J₀ : Set X) :=
  le_centralizer_iff.1 (d.J₀_le_J₅.trans inf_le_right) (d.x₅_mem_U₅ a)

theorem x₆_mem_centralizer_J₀ (a : d.Γ₀) : d.x₆ a ∈ centralizer (d.J₀ : Set X) :=
  le_centralizer_iff.1 (d.J₀_le_J₆.trans inf_le_right) (d.x₆_mem_V a)

theorem Y_le_centralizer_J₀ : d.Y ≤ centralizer (d.J₀ : Set X) :=
  sup_le (fun _ ⟨a, ha⟩ => ha ▸ d.x₅_mem_centralizer_J₀ a)
    (fun _ ⟨a, ha⟩ => ha ▸ d.x₆_mem_centralizer_J₀ a)

theorem mem_sylowJ₀_iff {x : X} :
    x ∈ d.sylowJ₀ ↔ ∃ a b c, d.x₂ a * d.x₅ b * d.x₆ c = x := by
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨m, hm, hm1⟩ := d.exists_mem_ker_nmUnits_ne_one
    obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩ := d.mem_S.1 hx
    have e := (mem_centralizer_iff.1 hc) _ (d.torus_one_mem_J₀ hm)
    obtain ⟨h1, -, h3, h4, -, -⟩ := d.nf_coords_of_commute e
    simp only [Units.val_one, OneMemClass.coe_one, one_mul] at h1 h3 h4
    have hm1' : (m : d.Γ) ≠ 1 := fun h => hm1 (Units.ext h)
    refine ⟨a₂, a₅, a₆, ?_⟩
    change _ = d.nf (a₁, a₂, a₃, a₄, a₅, a₆)
    rw [eq_zero_of_mul_eq_self hm1' h1, eq_zero_of_mul_eq_self hm1' h3,
      eq_zero_of_mul_eq_self (d.σ_mul_σσ_ne_one hm1) h4, nf_apply, d.x₁_zero, d.x₃_zero,
      d.x₄_zero, one_mul, mul_one, mul_one]
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨mul_mem (mul_mem (d.U₂_le_S (d.x₂_mem_U₂ a)) (d.U₅_le_S (d.x₅_mem_U₅ b)))
        (d.V_le_S (d.x₆_mem_V c)),
      mul_mem (mul_mem (d.x₂_mem_centralizer_J₀ a) (d.x₅_mem_centralizer_J₀ b))
        (d.x₆_mem_centralizer_J₀ c)⟩

theorem x₂_mul_x₅_mul_x₆_mem_sylowJ₀ (a b c : d.Γ₀) :
    d.x₂ a * d.x₅ b * d.x₆ c ∈ d.sylowJ₀ :=
  d.mem_sylowJ₀_iff.2 ⟨a, b, c, rfl⟩

theorem card_sylowJ₀ : Nat.card d.sylowJ₀ = q ^ 3 := by
  have h := d.card_eq_of_nf (α := d.Γ₀ × d.Γ₀ × d.Γ₀) (T := d.sylowJ₀)
    (fun c => (0, c.1, 0, 0, c.2.1, c.2.2))
    (fun c c' hc => by
      simp only [Prod.mk.injEq, true_and] at hc
      exact Prod.ext hc.1 (Prod.ext hc.2.1 hc.2.2))
    (fun c => by
      rw [nf_apply, d.x₁_zero, d.x₃_zero, d.x₄_zero, one_mul, mul_one, mul_one]
      exact d.x₂_mul_x₅_mul_x₆_mem_sylowJ₀ _ _ _)
    (fun g hg => by
      obtain ⟨a, b, c, rfl⟩ := d.mem_sylowJ₀_iff.1 hg
      refine ⟨(a, b, c), ?_⟩
      rw [nf_apply, d.x₁_zero, d.x₃_zero, d.x₄_zero, one_mul, mul_one, mul_one])
  rw [h, Nat.card_prod, Nat.card_prod, d.card_Γ₀]
  ring

theorem isPGroup_sylowJ₀ : IsPGroup 2 d.sylowJ₀ := by
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  exact P.isPGroup'.to_le (hP ▸ inf_le_left)

theorem sylowJ₀_le_leviJ₀ : d.sylowJ₀ ≤ d.leviJ₀ := fun _ hx =>
  d.mem_leviJ₀_of_mem_S_of_mem_centralizer_J₀ hx.1 hx.2

theorem sylowJ₀_inf_centralizer : d.sylowJ₀ ⊓ centralizer (d.sylowJ₀ : Set X) = d.V := by
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨a, b, c, rfl⟩ := d.mem_sylowJ₀_iff.1 hx
    have h5 := mem_centralizer_iff.1 hxc (d.x₅ 1)
      (by simpa [d.x₂_zero, d.x₆_zero] using d.x₂_mul_x₅_mul_x₆_mem_sylowJ₀ 0 1 0)
    have h55 : Commute (d.x₅ 1) (d.x₅ b) := by
      rw [Commute, SemiconjBy, ← d.x₅_add, ← d.x₅_add, add_comm]
    have hc5 : Commute (d.x₅ 1) (d.x₅ b * d.x₆ c) := h55.mul_right (d.commute₅₆ 1 c)
    have h5' : d.x₅ 1 * d.x₂ a = d.x₂ a * d.x₅ 1 := by
      have e : d.x₅ 1 * d.x₂ a * (d.x₅ b * d.x₆ c) = d.x₂ a * d.x₅ 1 * (d.x₅ b * d.x₆ c) := by
        calc d.x₅ 1 * d.x₂ a * (d.x₅ b * d.x₆ c) = d.x₅ 1 * (d.x₂ a * d.x₅ b * d.x₆ c) := by
              simp only [mul_assoc]
          _ = d.x₂ a * d.x₅ b * d.x₆ c * d.x₅ 1 := h5
          _ = d.x₂ a * (d.x₅ b * d.x₆ c * d.x₅ 1) := by simp only [mul_assoc]
          _ = d.x₂ a * (d.x₅ 1 * (d.x₅ b * d.x₆ c)) := by rw [hc5.eq]
          _ = d.x₂ a * d.x₅ 1 * (d.x₅ b * d.x₆ c) := by simp only [mul_assoc]
      exact mul_right_cancel e
    have ha : a = 0 := by
      have e := d.comm₂₅ a 1
      rw [commutatorElement_eq_one_iff_commute.2 (Commute.symm h5'), mul_one] at e
      exact d.x₆_eq_one_iff.1 e.symm
    subst ha
    rw [d.x₂_zero, one_mul] at hxc ⊢
    have h2 := mem_centralizer_iff.1 hxc (d.x₂ 1)
      (by simpa [d.x₅_zero, d.x₆_zero] using d.x₂_mul_x₅_mul_x₆_mem_sylowJ₀ 1 0 0)
    have h2' : d.x₂ 1 * d.x₅ b = d.x₅ b * d.x₂ 1 := by
      have e : d.x₂ 1 * d.x₅ b * d.x₆ c = d.x₅ b * d.x₂ 1 * d.x₆ c := by
        calc d.x₂ 1 * d.x₅ b * d.x₆ c = d.x₂ 1 * (d.x₅ b * d.x₆ c) := mul_assoc _ _ _
          _ = d.x₅ b * d.x₆ c * d.x₂ 1 := h2
          _ = d.x₅ b * (d.x₆ c * d.x₂ 1) := mul_assoc _ _ _
          _ = d.x₅ b * (d.x₂ 1 * d.x₆ c) := by rw [(d.commute₂₆ 1 c).eq]
          _ = d.x₅ b * d.x₂ 1 * d.x₆ c := (mul_assoc _ _ _).symm
      exact mul_right_cancel e
    have hb : b = 0 := by
      have e := d.comm₂₅ 1 b
      rw [commutatorElement_eq_one_iff_commute.2 h2', one_mul] at e
      exact d.x₆_eq_one_iff.1 e.symm
    subst hb
    rw [d.x₅_zero, one_mul]
    exact d.x₆_mem_V c
  · intro x hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨by simpa [d.x₂_zero, d.x₅_zero] using d.x₂_mul_x₅_mul_x₆_mem_sylowJ₀ 0 0 c, ?_⟩
    have hV : d.x₆ c ∈ centralizer (d.S : Set X) := by
      have h := d.S_inf_centralizer_S.ge (d.x₆_mem_V c)
      exact h.2
    exact centralizer_le (fun _ hy => (inf_le_left : d.sylowJ₀ ≤ d.S) hy) hV

theorem u_not_mem_centralizer_J₀ : d.u ∉ centralizer (d.J₀ : Set X) := by
  intro hu
  obtain ⟨m, hm, hm1⟩ := d.exists_mem_ker_nmUnits_ne_one
  have ht : d.torus (1, m) ∈ d.J₀ := d.torus_one_mem_J₀ hm
  have e1 := d.u_conj_eq_inv_of_mem_J₆ (d.J₀_le_J₆ ht)
  have hc : d.torus (1, m) * d.u = d.u * d.torus (1, m) := mem_centralizer_iff.1 hu _ ht
  rw [← hc, mul_assoc, d.u_mul_self, mul_one] at e1
  have e2 : d.torus ((1, m) * (1, m)) = d.torus 1 := by
    rw [map_mul, map_one]
    nth_rewrite 2 [e1]
    exact mul_inv_cancel _
  have e3 := congrArg Prod.snd (d.torus_injective e2)
  have hm2 : m ^ 2 = 1 := by
    rw [sq]
    exact e3
  exact hm1 (d.units_eq_one_of_sq hm2)

theorem mem_sylowJ₀_of_mem_normalizer {g : X} (hg : g ∈ centralizer (d.J₀ : Set X))
    (hn : g ∈ normalizer (d.sylowJ₀ : Set X)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ d.sylowJ₀ := by
  have := d.finite
  have hV : g ∈ normalizer (d.V : Set X) := mem_normalizer_fintype fun x hx => by
    rw [← d.sylowJ₀_inf_centralizer] at hx ⊢
    exact conj_mem_inf_centralizer hn hx
  rcases d.normalizer_V_cases hV with hB | ⟨x, hx, h, hh, y, hy, rfl⟩
  · obtain ⟨s, hs, j, hj, rfl⟩ := d.mem_B_iff.1 hB
    have hj1 := d.eq_one_of_mul_pow_eq_one_S hs hj hk
    subst hj1
    rw [mul_one] at hg ⊢
    exact ⟨hs, hg⟩
  · exfalso
    have hy' : y ∈ d.Uminus d.u := by
      rw [d.Uminus_u]
      exact hy
    obtain ⟨-, hu, -⟩ := d.bruhat_parts_mem_centralizer d.J₀_le_J hx hh d.u_mem_weyl hy' hg
    exact d.u_not_mem_centralizer_J₀ hu

theorem isSylowOf_sylowJ₀ : IsSylowOf 2 d.sylowJ₀ (centralizer (d.J₀ : Set X)) := by
  have := d.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_normalizer_D4 inf_le_right d.isPGroup_sylowJ₀
    fun g hg hn ⟨k, hk⟩ => d.mem_sylowJ₀_of_mem_normalizer hg hn hk

theorem eq_one_of_mem_centralizer_leviJ₀ {g : X} (hg : g ∈ centralizer (d.J₀ : Set X))
    (hK : g ∈ centralizer (d.leviJ₀ : Set X)) {k : ℕ} (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have hcQ : g ∈ centralizer (d.sylowJ₀ : Set X) :=
    centralizer_le (fun _ hx => d.sylowJ₀_le_leviJ₀ hx) hK
  have hgQ := d.mem_sylowJ₀_of_mem_normalizer hg (centralizer_le_normalizer _ hcQ) hk
  have hgV : g ∈ d.V := by
    rw [← d.sylowJ₀_inf_centralizer]
    exact ⟨hgQ, hcQ⟩
  obtain ⟨c, rfl⟩ := hgV
  have hc : d.u * d.v * d.u * d.x₆ c = d.x₆ c * (d.u * d.v * d.u) :=
    mem_centralizer_iff.1 hK _ d.uvu_mem_leviJ₀
  have e : d.x₆ c = d.x₂ c := by
    have h1 := d.uvu_conj_x₂ c
    calc d.x₆ c = d.x₆ c * (d.u * d.v * d.u) * (d.u * d.v * d.u)⁻¹ := by group
      _ = d.u * d.v * d.u * d.x₆ c * (d.u * d.v * d.u)⁻¹ := by rw [hc]
      _ = d.u * d.v * d.u * (d.u * d.v * d.u * d.x₂ c * (d.u * d.v * d.u)⁻¹) *
          (d.u * d.v * d.u)⁻¹ := by rw [h1]
      _ = (d.u * d.v * d.u * (d.u * d.v * d.u)) * d.x₂ c *
          (d.u * d.v * d.u * (d.u * d.v * d.u))⁻¹ := by group
      _ = d.x₂ c := by
          rw [show d.u * d.v * d.u * (d.u * d.v * d.u) = 1 by
            rw [show d.u * d.v * d.u * (d.u * d.v * d.u) = d.u * d.v * (d.u * d.u) * d.v * d.u by
              group, d.u_mul_self, mul_one, mul_assoc d.u, d.v_mul_self, mul_one, d.u_mul_self]]
          group
  have hc0 : c = 0 := d.x₂_mem_Y_iff.1 (e ▸ d.V_le_Y (d.x₆_mem_V c))
  rw [hc0, d.x₆_zero]

theorem M_inf_centralizer_J₀ : d.M ⊓ centralizer (d.J₀ : Set X) = d.Y := by
  apply le_antisymm
  · rintro x ⟨hxM, hxc⟩
    obtain ⟨a, b, c, rfl⟩ := d.mem_sylowJ₀_iff.1 ⟨d.M_le_S hxM, hxc⟩
    have hY : d.x₅ b * d.x₆ c ∈ d.Y := mul_mem (d.x₅_mem_Y b) (d.V_le_Y (d.x₆_mem_V c))
    have hYM : d.Y ≤ d.M := d.Y_le_W.trans (d.W_le_F.trans d.F_le_M)
    have ha : d.x₂ a ∈ d.M := by
      have h1 := d.M.mul_mem hxM (d.M.inv_mem (hYM hY))
      have e : d.x₂ a * d.x₅ b * d.x₆ c * (d.x₅ b * d.x₆ c)⁻¹ = d.x₂ a := by group
      rwa [e] at h1
    rw [d.x₂_mem_M_iff.1 ha, d.x₂_zero, one_mul]
    exact hY
  · exact le_inf (d.Y_le_W.trans (d.W_le_F.trans d.F_le_M)) d.Y_le_centralizer_J₀

theorem inv_mul_conj_mem_M {s j : X} (hs : s ∈ d.S) (hj : j ∈ d.J₀) :
    s⁻¹ * (j * s * j⁻¹) ∈ d.M := by
  obtain ⟨a, m, hm, rfl⟩ := d.mem_S_iff_x₂.1 hs
  have hjx : j * d.x₂ a = d.x₂ a * j := mem_centralizer_iff.1 (d.x₂_mem_centralizer_J₀ a) j hj
  have hjm : j * m * j⁻¹ ∈ d.M :=
    (mem_normalizer_iff.1 (d.J_le_normalizer_M (d.J₀_le_J hj)) m).1 hm
  have e : (d.x₂ a * m)⁻¹ * (j * (d.x₂ a * m) * j⁻¹) = m⁻¹ * (j * m * j⁻¹) := by
    calc (d.x₂ a * m)⁻¹ * (j * (d.x₂ a * m) * j⁻¹) =
        m⁻¹ * (d.x₂ a)⁻¹ * (j * d.x₂ a) * m * j⁻¹ := by group
      _ = m⁻¹ * (d.x₂ a)⁻¹ * (d.x₂ a * j) * m * j⁻¹ := by rw [hjx]
      _ = m⁻¹ * (j * m * j⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem hm) hjm

theorem odd_card_J₀ : Odd (Nat.card d.J₀) := by
  rw [d.yamada_three_five_four.2]
  have he := d.even_q
  exact ((he.pow_of_ne_zero (by norm_num)).add he).add_one

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
