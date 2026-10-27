module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Fusion

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.EvenSporadicStandard.Fin76b.AutETable

section Setting

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

@[expose] noncomputable def jH : Multiplicative (ZMod 2) × G12 →* G :=
  (centralizer ({e} : Set G)).subtype.comp e₀.symm.toMonoidHom

theorem jH_injective : Function.Injective (jH e₀) :=
  Subtype.val_injective.comp e₀.symm.injective

theorem jH_comm_e (p : Multiplicative (ZMod 2) × G12) : jH e₀ p * e = e * jH e₀ p :=
  mem_centralizer_iff.1 (e₀.symm p).2 e (Set.mem_singleton e) |>.symm

theorem mem_range_jH {y : G} : y ∈ (jH e₀).range ↔ y ∈ centralizer ({e} : Set G) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact (e₀.symm p).2
  · intro hy
    exact ⟨e₀ ⟨y, hy⟩, by simp [jH]⟩

end Setting

section Certified

set_option linter.unusedSectionVars false

theorem sylowDataPinned : ∃ b : G12, IsPGroup 2 bfS' ∧
    (∃ m : ℕ, Odd m ∧ Nat.card G12 = Nat.card bfS' * m) ∧ Jelt * Jelt = 1 ∧ Jelt ≠ 1 ∧
    Jelt ∈ bfS' ∧ (∀ x ∈ bfS', x * Jelt = Jelt * x) ∧
    (∀ y ∈ bfS', (∀ x ∈ bfS', x * y = y * x) → y = 1 ∨ y = Jelt) ∧ (∃ g : G12, g * g = Jelt) ∧
    ∀ a : G12, a * a = 1 → a ≠ 1 →
      (∃ c : G12, a = c * Jelt * c⁻¹) ∨ (∃ c : G12, a = c * b * c⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c0, hc0, hJ0⟩ := exists_conj_Jelt_m12Rep1
  obtain ⟨hb, hbo⟩ := m12_reps_mem m12Rep2 (by simp)
  have hord2 : ∀ a : G12, a * a = 1 → a ≠ 1 → orderOf (a : Equiv.Perm (Fin 12)) = 2 := by
    intro a ha2 ha1
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  refine ⟨⟨m12Rep2, hb⟩, IsPGroup.of_card (n := 6) (by rw [card_bfS']; norm_num),
    ⟨1485, by decide, by rw [card_G12, card_bfS']⟩, Jelt_mul_self, Jelt_ne_one, Jelt_mem_bfS',
    fun x hx => bfS'_comm_Jelt hx, fun y hy hc => bfS'_center hy hc,
    ⟨Felt * Felt, Subtype.ext ?_⟩, ?_⟩
  · show bfF * bfF * (bfF * bfF) = bfF ^ 4
    simp [pow_succ, mul_assoc]
  · intro a ha2 ha1
    obtain ⟨r, hr, c, hc, hac⟩ := m12_involution_cover.1 (a : Equiv.Perm (Fin 12))
      (by simp) (hord2 a ha2 ha1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine Or.inl ⟨⟨c * c0⁻¹, mul_mem hc (inv_mem hc0)⟩, Subtype.ext ?_⟩
      have h1 : m12Rep1 = c0⁻¹ * (Jelt : Equiv.Perm (Fin 12)) * c0 := by
        rw [hJ0]; group
      rw [hac, h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · exact Or.inr ⟨⟨c, hc⟩, Subtype.ext hac⟩

end Certified

section Config

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

@[expose] noncomputable def ιH : G12 →* G := (jH e₀).comp (MonoidHom.inr _ _)

theorem ιH_injective : Function.Injective (ιH e₀) := by
  intro a b h
  have := jH_injective e₀ h
  simpa using this

@[expose] noncomputable def LG : Subgroup G := (ιH e₀).range

@[expose] noncomputable def T0G : Subgroup G := bfS'.map (ιH e₀)

@[expose, irreducible] noncomputable def cG : G := ιH e₀ Jelt

theorem cG_def : cG e₀ = ιH e₀ Jelt := by unfold cG; rfl

theorem ιH_comm_e (m : G12) : ιH e₀ m * e = e * ιH e₀ m := jH_comm_e e₀ _

theorem LG_le_centralizer : LG e₀ ≤ centralizer ({e} : Set G) := by
  rintro _ ⟨m, rfl⟩
  exact mem_centralizer_iff.2 fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact
    (ιH_comm_e e₀ m).symm

theorem e_mem_centralizer : e ∈ centralizer ({e} : Set G) := mem_centralizer_iff.2 (by simp)

theorem e₀_e (he2 : orderOf e = 2) :
    e₀ ⟨e, e_mem_centralizer⟩ = (Multiplicative.ofAdd 1, 1) := by
  have hbot : center G12 = ⊥ := center_eq_bot_of_isSporadic_m12 ⟨MulEquiv.refl _⟩
  have hmem : e ∈ centralizer ({e} : Set G) := e_mem_centralizer
  set p := e₀ ⟨e, hmem⟩ with hp
  have hcentral : ∀ q : Multiplicative (ZMod 2) × G12, p * q = q * p := by
    intro q
    have h1 : (⟨e, hmem⟩ : centralizer ({e} : Set G)) * e₀.symm q =
        e₀.symm q * ⟨e, hmem⟩ :=
      Subtype.ext (mem_centralizer_iff.1 (e₀.symm q).2 e (Set.mem_singleton e))
    have := congrArg e₀ h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  have hp2 : p.2 = 1 := by
    have : p.2 ∈ center G12 := by
      rw [mem_center_iff]
      intro m
      exact (congrArg Prod.snd (hcentral (1, m))).symm
    rwa [hbot, mem_bot] at this
  have hp1 : p.1 ≠ 1 := by
    intro h1
    have hp0 : p = 1 := Prod.ext h1 hp2
    have h2 : (⟨e, hmem⟩ : centralizer ({e} : Set G)) = 1 :=
      e₀.injective (by rw [← hp, hp0, map_one])
    have : e = 1 := congrArg Subtype.val h2
    rw [this, orderOf_one] at he2
    omega
  have hp1' : p.1 = Multiplicative.ofAdd 1 := by
    rcases zmod_two_cases p.1.toAdd with h0 | h1
    · exact absurd (Multiplicative.toAdd.injective (by simpa using h0)) hp1
    · exact Multiplicative.toAdd.injective (by simpa using h1)
  exact Prod.ext hp1' hp2

theorem e_eq_jH (he2 : orderOf e = 2) : e = jH e₀ (Multiplicative.ofAdd 1, 1) := by
  have h := e₀_e e₀ he2
  calc e = ((e₀.symm (e₀ ⟨e, e_mem_centralizer⟩) : centralizer ({e} : Set G)) : G) := by
        rw [MulEquiv.symm_apply_apply]
    _ = jH e₀ (Multiplicative.ofAdd 1, 1) := by rw [h]; rfl

theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) ≠ 1 := by
  decide

theorem cG_sq : cG e₀ * cG e₀ = 1 := by
  rw [cG_def, ← map_mul, Jelt_mul_self, map_one]

theorem cG_ne_one : cG e₀ ≠ 1 := by
  intro h
  exact Jelt_ne_one (ιH_injective e₀ (by rw [← cG_def, h, map_one]))

theorem orderOf_cG : orderOf (cG e₀) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact cG_sq e₀) (cG_ne_one e₀)

theorem cG_comm_e : cG e₀ * e = e * cG e₀ := by
  rw [cG_def]; exact ιH_comm_e e₀ _

theorem disjoint_LG (he2 : orderOf e = 2) : Disjoint (LG e₀) (zpowers e) := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxe
  obtain ⟨m, rfl⟩ := hxL
  have hee : e * e = 1 := by rw [← pow_two, ← he2, pow_orderOf_eq_one]
  rcases Fin76b.mem_zpowers_sq_eq_one hee hxe with h1 | h1
  · exact h1
  · exfalso
    have h3 : jH e₀ (1, m) = jH e₀ (Multiplicative.ofAdd 1, 1) := by
      rw [← e_eq_jH e₀ he2]; exact h1
    have := congrArg Prod.fst (jH_injective e₀ h3)
    exact ofAdd_one_ne_one this.symm

theorem cent_eq_LG (he2 : orderOf e = 2) :
    centralizer ({e} : Set G) = LG e₀ ⊔ zpowers e := by
  apply le_antisymm
  · intro y hy
    obtain ⟨⟨a, m⟩, rfl⟩ := (mem_range_jH e₀).2 hy
    have hfac : jH e₀ (a, m) = jH e₀ (1, m) * jH e₀ (a, 1) := by
      rw [← map_mul]; simp
    rw [hfac]
    refine mul_mem (mem_sup_left ⟨m, rfl⟩) (mem_sup_right ?_)
    rcases zmod_two_cases a.toAdd with h0 | h1
    · have : a = 1 := Multiplicative.toAdd.injective (by simpa using h0)
      have h11 : jH e₀ (1, 1) = 1 := map_one (jH e₀)
      rw [this, h11]; exact one_mem _
    · have : a = Multiplicative.ofAdd 1 := Multiplicative.toAdd.injective (by simpa using h1)
      rw [this, ← e_eq_jH e₀ he2]; exact mem_zpowers e
  · refine sup_le (LG_le_centralizer e₀) ?_
    rw [zpowers_le]
    exact e_mem_centralizer

theorem card_LG : Nat.card (LG e₀) = Nat.card G12 :=
  Nat.card_congr (MonoidHom.ofInjective (ιH_injective e₀)).toEquiv.symm

theorem innerConfig_pinned (he2 : orderOf e = 2) :
    Fin76b.InnerConfig G (LG e₀) e (cG e₀) (T0G e₀) := by
  obtain ⟨b, hT, ⟨m, hm, hcard⟩, hJ2, hJ1, hJT, hJc, hcen, ⟨g, hg⟩, hcls⟩ := sylowDataPinned
  have hι := ιH_injective e₀
  have hee : e * e = 1 := by rw [← pow_two, ← he2, pow_orderOf_eq_one]
  have hcardT : Nat.card (T0G e₀) = Nat.card bfS' := Subgroup.card_map_of_injective hι
  have hrange : ∀ a ∈ LG e₀, ∃ a' : G12, ιH e₀ a' = a := fun a ha => ha
  have hιL : ∀ a' : G12, ιH e₀ a' ∈ LG e₀ := fun a' => ⟨a', rfl⟩
  exact
  { z_sq := hee
    z_ne := fun h1 => by rw [h1, orderOf_one] at he2; omega
    z_cent := fun h hh => by
      obtain ⟨m', rfl⟩ := hh
      exact (ιH_comm_e e₀ m').symm ▸ rfl
    disjoint := disjoint_LG e₀ he2
    cent_eq := cent_eq_LG e₀ he2
    T₀_le := by rintro _ ⟨x, -, rfl⟩; exact hιL x
    T₀_pgroup := hT.map (ιH e₀)
    T₀_odd := ⟨m, hm, by rw [card_LG, hcard, hcardT]⟩
    t_sq := cG_sq e₀
    t_ne := cG_ne_one e₀
    t_mem := ⟨Jelt, hJT, (cG_def e₀).symm⟩
    t_central := by
      rintro _ ⟨x, hx, rfl⟩
      rw [cG_def, ← map_mul, ← map_mul, hJc x hx]
    center_le := by
      intro y hy hc
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
      have : ∀ x ∈ bfS', x * y' = y' * x := fun x hx => hι (by
        rw [map_mul, map_mul]; exact hc (ιH e₀ x) ⟨x, hx, rfl⟩)
      rcases hcen y' hy' this with h1 | h1
      · exact Or.inl (by rw [h1, map_one])
      · exact Or.inr (by rw [h1, cG_def])
    t_square := ⟨ιH e₀ g, hιL g, by rw [cG_def, ← map_mul, hg]⟩
    classes := by
      refine ⟨ιH e₀ b, hιL b, ?_⟩
      intro a ha ha2 ha1
      obtain ⟨a', rfl⟩ := hrange a ha
      have hx : a' * a' = 1 := hι (by rw [map_mul, ha2, map_one])
      have hne : a' ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
      rcases hcls a' hx hne with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨ιH e₀ c, hιL c, by rw [hc, cG_def]; simp [map_mul, map_inv]⟩
      · exact Or.inr ⟨ιH e₀ c, hιL c, by rw [hc]; simp [map_mul, map_inv]⟩ }

include e₀ in
theorem nonabelian_G : ∃ a b : G, a * b ≠ b * a := by
  by_contra hna
  have h : ∀ a b : G, a * b = b * a := fun a b => by
    by_contra h'
    exact hna ⟨a, b, h'⟩
  have hbot : center G12 = ⊥ := center_eq_bot_of_isSporadic_m12 ⟨MulEquiv.refl _⟩
  have hJ : Jelt ∈ center G12 := by
    rw [mem_center_iff]
    intro g
    exact ιH_injective e₀ (by rw [map_mul, map_mul]; exact h _ _)
  rw [hbot, mem_bot] at hJ
  exact Jelt_ne_one hJ

theorem exists_swap_pinned [Finite G] [IsSimpleGroup G] (he2 : orderOf e = 2) :
    ∃ x : G, x * e * x⁻¹ = e * cG e₀ ∧ x * cG e₀ * x⁻¹ = cG e₀ := by
  obtain ⟨P, x, -, -, -, -, -, hxe, hxc⟩ :=
    (innerConfig_pinned e₀ he2).exists_swap (nonabelian_G (e₀ := e₀))
  exact ⟨x, hxe, hxc⟩

end Config

section Theta

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

set_option linter.unusedSectionVars false

@[expose] noncomputable def ρH : centralizer ({e} : Set G) →* Equiv.Perm (Fin 14) :=
  kapP.comp (((MonoidHom.id (Multiplicative (ZMod 2))).prodMap
    (NativeSporadic.M12).subtype).comp e₀.toMonoidHom)

theorem ρH_apply (y : centralizer ({e} : Set G)) :
    ρH e₀ y = kapP ((e₀ y).1, ((e₀ y).2 : Equiv.Perm (Fin 12))) := rfl

theorem ρH_injective : Function.Injective (ρH e₀) := by
  intro a b h
  have h1 := kapP_injective h
  have hf := congrArg (fun z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 12) => z.1) h1
  have hs := congrArg (fun z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 12) => z.2) h1
  have : e₀ a = e₀ b := Prod.ext hf (Subtype.ext hs)
  exact e₀.injective this

@[expose] noncomputable def HcG : Subgroup G :=
  centralizer ({e} : Set G) ⊓ centralizer ({cG e₀} : Set G)

theorem cG_mem_centralizer : cG e₀ ∈ centralizer ({e} : Set G) :=
  mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff] at hy; rw [hy]; exact (cG_comm_e e₀).symm

theorem e₀_cG : e₀ ⟨cG e₀, cG_mem_centralizer e₀⟩ = (1, Jelt) := by
  have : (⟨cG e₀, cG_mem_centralizer e₀⟩ : centralizer ({e} : Set G)) = e₀.symm (1, Jelt) :=
    Subtype.ext (show cG e₀ = ((e₀.symm (1, Jelt) : centralizer ({e} : Set G)) : G) from cG_def e₀)
  rw [this, MulEquiv.apply_symm_apply]

theorem ρH_mem_yK {y : G} (hy : y ∈ HcG e₀) : ρH e₀ ⟨y, hy.1⟩ ∈ yK := by
  rw [mem_yK_iff]
  refine ⟨(e₀ ⟨y, hy.1⟩).1, ((e₀ ⟨y, hy.1⟩).2 : Equiv.Perm (Fin 12)), ?_,
    ρH_apply e₀ ⟨y, hy.1⟩⟩
  rw [Cgen_eq, mem_centralizerIn]
  refine ⟨(e₀ ⟨y, hy.1⟩).2.2, ?_⟩
  have hc : (⟨y, hy.1⟩ : centralizer ({e} : Set G)) * ⟨cG e₀, cG_mem_centralizer e₀⟩ =
      ⟨cG e₀, cG_mem_centralizer e₀⟩ * ⟨y, hy.1⟩ :=
    Subtype.ext (mem_centralizer_iff.1 hy.2 (cG e₀) (Set.mem_singleton _)).symm
  have h3 := congrArg e₀ hc
  rw [map_mul, map_mul] at h3
  rw [e₀_cG e₀] at h3
  have hJ : ((Jelt : G12) : Equiv.Perm (Fin 12)) = bfJ := rfl
  have h4 := congrArg Prod.snd h3
  rw [Prod.snd_mul, Prod.snd_mul] at h4
  have h5 := congrArg (fun m : G12 => (m : Equiv.Perm (Fin 12))) h4
  simp only [Subgroup.coe_mul, hJ] at h5
  exact h5

theorem exists_of_mem_yK {z : Equiv.Perm (Fin 14)} (hz : z ∈ yK) :
    ∃ (y : G) (hy : y ∈ HcG e₀), ρH e₀ ⟨y, hy.1⟩ = z := by
  obtain ⟨a, σ, hσ, rfl⟩ := (mem_yK_iff z).1 hz
  rw [Cgen_eq, mem_centralizerIn] at hσ
  obtain ⟨hσM, hσc⟩ := hσ
  have hmem : jH e₀ (a, ⟨σ, hσM⟩) ∈ centralizer ({e} : Set G) :=
    (mem_range_jH e₀).1 ⟨_, rfl⟩
  have hcomm : jH e₀ (a, ⟨σ, hσM⟩) * cG e₀ = cG e₀ * jH e₀ (a, ⟨σ, hσM⟩) := by
    rw [cG_def, ιH, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Prod.ext
    · simp
    · exact Subtype.ext hσc
  refine ⟨jH e₀ (a, ⟨σ, hσM⟩), ⟨hmem, mem_centralizer_iff.2 fun h hh => ?_⟩, ?_⟩
  · rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcomm.symm
  · have : (⟨jH e₀ (a, ⟨σ, hσM⟩), hmem⟩ : centralizer ({e} : Set G)) = e₀.symm (a, ⟨σ, hσM⟩) :=
      Subtype.ext rfl
    rw [this, ρH_apply, MulEquiv.apply_symm_apply]

@[expose] noncomputable def ΘH : ↥(HcG e₀) →* ↥yK :=
  ((ρH e₀).comp (Subgroup.inclusion
    (inf_le_left : HcG e₀ ≤ centralizer ({e} : Set G)))).codRestrict yK
    (fun y => ρH_mem_yK e₀ y.2)

theorem ΘH_bijective : Function.Bijective (ΘH e₀) := by
  constructor
  · intro a b h
    have h1 : ρH e₀ ⟨a.1, a.2.1⟩ = ρH e₀ ⟨b.1, b.2.1⟩ := congrArg Subtype.val h
    have h2 := ρH_injective e₀ h1
    have h3 : a.1 = b.1 := congrArg (fun z : centralizer ({e} : Set G) => (z : G)) h2
    exact Subtype.ext h3
  · intro z
    obtain ⟨y, hy, hρ⟩ := exists_of_mem_yK e₀ z.2
    exact ⟨⟨y, hy⟩, Subtype.ext hρ⟩

@[expose] noncomputable def ΘE : ↥(HcG e₀) ≃* ↥yK :=
  MulEquiv.ofBijective (ΘH e₀) (ΘH_bijective e₀)

end Theta

end CFSG.EvenSporadicStandard.M12Std.Yosh
