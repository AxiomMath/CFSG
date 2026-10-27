module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open MulAction
open scoped Pointwise

section Free

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] [Finite X]

theorem card_dvd_of_free (hfree : ∀ x : X, ∀ g : Γ, g • x = x → g = 1) :
    Nat.card Γ ∣ Nat.card X := by
  classical
  have : Fintype (orbitRel.Quotient Γ X) := Fintype.ofFinite _
  have hstab : ∀ x : X, stabilizer Γ x = ⊥ := fun x => by
    rw [eq_bot_iff]
    intro g hg
    exact (Subgroup.mem_bot).2 (hfree x g (mem_stabilizer_iff.1 hg))
  have horb : ∀ x : X, Nat.card (orbit Γ x) = Nat.card Γ := fun x => by
    have h := (stabilizer Γ x).card_mul_index
    rw [index_stabilizer, hstab x, Subgroup.card_bot, one_mul] at h
    rw [Nat.card_coe_set_eq]
    exact h
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits Γ X), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => by
    rw [horb]

end Free

section TI

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem index_modEq_of_ti (P N' M' : Subgroup G) (hPN : P ≤ N') (hNM : N' ≤ M')
    (hP : IsPGroup p P)
    (hpel : ∀ y ∈ N', (∃ m : ℕ, y ^ (p ^ m) = 1) → y ∈ P)
    (hTI : ∀ a : G, a ∉ M' → ∀ g ∈ P, a⁻¹ * g * a ∈ P → g = 1) :
    N'.index ≡ N'.relIndex M' [MOD Nat.card P] := by
  classical
  let Y : Set (G ⧸ N') := {x | ∃ m ∈ M', (m : G ⧸ N') = x}
  have hY : ∀ g : P, ∀ y ∈ Y, g • y ∈ Y := by
    rintro g _ ⟨m, hm, rfl⟩
    exact ⟨(g : G) * m, M'.mul_mem (hNM (hPN g.2)) hm, rfl⟩
  have hY' : ∀ g : P, ∀ y, g • y ∈ Y → y ∈ Y := by
    intro g y hy
    have := hY g⁻¹ _ hy
    rwa [inv_smul_smul] at this
  let Z := {x : G ⧸ N' // x ∉ Y}
  let _ : MulAction P Z :=
    { smul := fun g z => ⟨g • z.1, fun h => z.2 (hY' g _ h)⟩
      one_smul := fun z => Subtype.ext (one_smul _ _)
      mul_smul := fun g h z => Subtype.ext (mul_smul g h z.1) }
  have hfree : ∀ z : Z, ∀ g : P, g • z = z → g = 1 := by
    intro z g hg
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective z.1
    have haM : a ∉ M' := fun h => z.2 ⟨a, h, ha⟩
    have hg' : g • z.1 = z.1 := congrArg Subtype.val hg
    rw [← ha] at hg'
    have hq : ((((g : G) * a : G)) : G ⧸ N') = (a : G ⧸ N') := hg'
    rw [QuotientGroup.eq] at hq
    have hb : a⁻¹ * (g : G)⁻¹ * a ∈ N' := by
      have : ((g : G) * a)⁻¹ * a = a⁻¹ * (g : G)⁻¹ * a := by group
      rwa [this] at hq
    have hbp : a⁻¹ * (g : G)⁻¹ * a ∈ P := by
      refine hpel _ hb ?_
      obtain ⟨k, hk⟩ := hP ⟨(g : G)⁻¹, P.inv_mem g.2⟩
      refine ⟨k, ?_⟩
      have hk' : ((g : G)⁻¹) ^ (p ^ k) = 1 := congrArg Subtype.val hk
      have := conj_pow (a := a⁻¹) (b := (g : G)⁻¹) (i := p ^ k)
      simp only [inv_inv] at this
      rw [this, hk']
      group
    have := hTI a haM _ (P.inv_mem g.2) hbp
    exact Subtype.ext (inv_eq_one.1 this)
  have hdvd := card_dvd_of_free (Γ := P) (X := Z) hfree
  have hsplit : Nat.card (G ⧸ N') = Nat.card Y + Nat.card Z := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun x : G ⧸ N' => x ∈ Y)).symm
  have hY : Nat.card Y = N'.relIndex M' := by
    set b : G ⧸ N' := ((1 : G) : G ⧸ N') with hb
    have hor : Y = orbit M' b := by
      ext x
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, by simp [hb, Subgroup.smul_def]⟩
      · rintro ⟨m, rfl⟩
        exact ⟨m, m.2, by simp [hb, Subgroup.smul_def]⟩
    have hstab : stabilizer M' b = N'.subgroupOf M' := by
      ext m
      rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
      change (((m : G) * 1 : G) : G ⧸ N') = ((1 : G) : G ⧸ N') ↔ (m : G) ∈ N'
      rw [QuotientGroup.eq]
      simp
    rw [hor, Nat.card_coe_set_eq, ← index_stabilizer, hstab, Subgroup.relIndex]
  have hmod := Nat.ModEq.add_left (Nat.card Y) (Nat.modEq_zero_iff_dvd.2 hdvd)
  rw [add_zero] at hmod
  rw [Subgroup.index, hsplit, ← hY]
  exact hmod

theorem relIndex_modEq_of_ti (H P N' M' : Subgroup G) (hPN : P ≤ N') (hNM : N' ≤ M')
    (hMH : M' ≤ H) (hP : IsPGroup p P)
    (hpel : ∀ y ∈ N', (∃ m : ℕ, y ^ (p ^ m) = 1) → y ∈ P)
    (hTI : ∀ a ∈ H, a ∉ M' → ∀ g ∈ P, a⁻¹ * g * a ∈ P → g = 1) :
    N'.relIndex H ≡ N'.relIndex M' [MOD Nat.card P] := by
  have hPH : P ≤ H := hPN.trans (hNM.trans hMH)
  have h := index_modEq_of_ti (G := H) (p := p) (P.subgroupOf H) (N'.subgroupOf H)
    (M'.subgroupOf H) (Subgroup.comap_mono hPN) (Subgroup.comap_mono hNM)
    (hP.comap_subtype (K := H)) (fun y hy hy3 => by
      obtain ⟨m, hm⟩ := hy3
      exact hpel y hy ⟨m, by simpa using congrArg Subtype.val hm⟩)
    (fun a ha g hg hg' => by
      have := hTI a a.2 ha g hg hg'
      exact Subtype.ext this)
  rw [Subgroup.relIndex_subgroupOf hMH] at h
  have hc : Nat.card (P.subgroupOf H) = Nat.card P := Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  rwa [hc] at h

end TI

section SylowAux

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_of_sylow_in (M' : Subgroup G) {k : ℕ} (hM : p ^ k ∣ Nat.card M')
    (hM' : ¬ p ^ (k + 1) ∣ Nat.card M') (S S' : Subgroup G) (hS : S ≤ M') (hS' : S' ≤ M')
    (hc : Nat.card S = p ^ k) (hc' : Nat.card S' = p ^ k) :
    ∃ m ∈ M', ∀ x, x ∈ S' ↔ m⁻¹ * x * m ∈ S := by
  have hfac : (Nat.card M').factorization p = k := by
    have h1 : k ≤ (Nat.card M').factorization p :=
      ((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hM
    have h2 : ¬ (k + 1 ≤ (Nat.card M').factorization p) := fun h =>
      hM' (((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h)
    omega
  have e1 : Nat.card (S.subgroupOf M') = p ^ (Nat.card M').factorization p := by
    rw [hfac, ← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have e2 : Nat.card (S'.subgroupOf M') = p ^ (Nat.card M').factorization p := by
    rw [hfac, ← hc']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS').toEquiv
  let P1 : Sylow p M' := Sylow.ofCard (S.subgroupOf M') e1
  let P2 : Sylow p M' := Sylow.ofCard (S'.subgroupOf M') e2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M' P1 P2
  refine ⟨g, g.2, fun x => ?_⟩
  have h3 : ((g • P1 : Sylow p M') : Subgroup M') = (P2 : Subgroup M') := congrArg _ hg
  rw [Sylow.coe_subgroup_smul] at h3
  by_cases hx : x ∈ M'
  · have key : (⟨x, hx⟩ : M') ∈ S'.subgroupOf M' ↔
        (⟨x, hx⟩ : M') ∈ MulAut.conj g • (S.subgroupOf M') := by
      have := SetLike.ext_iff.1 h3 ⟨x, hx⟩
      exact this.symm
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf] at key
    simpa [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.mem_subgroupOf] using key
  · constructor
    · intro h
      exact absurd (hS' h) hx
    · intro h
      refine absurd ?_ hx
      have h1 := hS h
      have : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
      rw [this]
      exact M'.mul_mem (M'.mul_mem g.2 h1) (M'.inv_mem g.2)

end SylowAux

end CFSG.AGLEmbedding.KFactProofs.Sp48
