module

import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.V

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

@[expose] def NL : Subgroup G := normalizer (H.E : Set G) ⊓ H.L

@[expose] def B : Subgroup G := normalizer (H.V : Set G) ⊓ centralizer ({H.z} : Set G)

theorem V_inf_M : H.V ⊓ H.M = H.E := by
  refine le_antisymm (fun y ⟨hyV, hyM⟩ => ?_) (le_inf H.E_le_V H.E_le_M)
  rcases H.mem_V_iff'.1 hyV with h | ⟨e, he, rfl⟩
  · exact h
  · exfalso
    apply H.z_not_mem_M
    have := mul_mem (inv_mem (H.E_le_M he)) hyM
    simpa using this

theorem mem_NL_iff {x : G} : x ∈ H.NL ↔ x ∈ H.L ∧ x ∈ normalizer (H.E : Set G) := by
  unfold NL; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem NL_le_centralizer_z : H.NL ≤ centralizer ({H.z} : Set G) := fun x hx => by
  rw [mem_centralizer_singleton_iff]
  exact H.comm_z_L ((H.mem_NL_iff.1 hx).1)

theorem mem_B_def {x : G} :
    x ∈ H.B ↔ x ∈ normalizer (H.V : Set G) ∧ x ∈ centralizer ({H.z} : Set G) :=
  Subgroup.mem_inf

theorem z_mem_B : H.z ∈ H.B := by
  refine H.mem_B_def.2 ⟨le_normalizer H.z_mem_V, ?_⟩
  exact mem_centralizer_singleton_iff.2 rfl

theorem NL_le_B : H.NL ≤ H.B := by
  intro x hx
  obtain ⟨hxL, hxN⟩ := H.mem_NL_iff.1 hx
  refine H.mem_B_def.2 ⟨?_, H.NL_le_centralizer_z hx⟩
  rw [mem_normalizer_iff]
  intro v
  have hxz := H.comm_z_L hxL
  have hE := mem_normalizer_iff.1 hxN
  constructor
  · intro hv
    rcases H.mem_V_iff'.1 hv with h | ⟨e, he, rfl⟩
    · exact H.E_le_V ((hE v).1 h)
    · refine H.mem_V_iff'.2 (Or.inr ⟨x * e * x⁻¹, (hE e).1 he, ?_⟩)
      calc x * (e * H.z) * x⁻¹ = x * e * (H.z * x⁻¹) := by group
        _ = x * e * (x⁻¹ * H.z) := by
          have : H.z * x⁻¹ = x⁻¹ * H.z := by
            calc H.z * x⁻¹ = x⁻¹ * (x * H.z) * x⁻¹ := by group
              _ = x⁻¹ * (H.z * x) * x⁻¹ := by rw [hxz]
              _ = x⁻¹ * H.z := by group
          rw [this]
        _ = x * e * x⁻¹ * H.z := by group
  · intro hv
    have hxinv : x⁻¹ ∈ H.NL := inv_mem hx
    obtain ⟨hxL', hxN'⟩ := H.mem_NL_iff.1 hxinv
    have hE' := mem_normalizer_iff.1 hxN'
    have : v = x⁻¹ * (x * v * x⁻¹) * x := by group
    rw [this]
    rcases H.mem_V_iff'.1 hv with h | ⟨e, he, he'⟩
    · exact H.E_le_V (by
        have := (hE' (x * v * x⁻¹)).1 h
        simpa using this)
    · refine H.mem_V_iff'.2 (Or.inr ⟨x⁻¹ * e * x, ?_, ?_⟩)
      · have := (hE' e).1 he
        simpa using this
      · rw [he']
        calc x⁻¹ * (e * H.z) * x = x⁻¹ * e * (H.z * x) := by group
          _ = x⁻¹ * e * (x * H.z) := by rw [← hxz]
          _ = x⁻¹ * e * x * H.z := by group

theorem B_le_centralizer : H.B ≤ centralizer ({H.z} : Set G) := inf_le_right

theorem B_le_normalizer_E : H.B ≤ normalizer (H.E : Set G) := by
  have key : ∀ b ∈ H.B, ∀ e ∈ H.E, b * e * b⁻¹ ∈ H.E := by
    intro b hb e he
    obtain ⟨hbV, hbC⟩ := H.mem_B_def.1 hb
    have h1 : b * e * b⁻¹ ∈ H.V := (mem_normalizer_iff.1 hbV e).1 (H.E_le_V he)
    have h2 : b * e * b⁻¹ ∈ H.M := by
      rcases H.mem_centralizer_iff.1 hbC with hm | hm
      · exact mul_mem (mul_mem hm (H.E_le_M he)) (inv_mem hm)
      · have hze : H.z * e * H.z⁻¹ = e := by rw [← H.z_comm_E he]; group
        have : b * e * b⁻¹ = (b * H.z) * e * (b * H.z)⁻¹ := by
          calc b * e * b⁻¹ = b * (H.z * e * H.z⁻¹) * b⁻¹ := by rw [hze]
            _ = (b * H.z) * e * (b * H.z)⁻¹ := by group
        rw [this]
        exact mul_mem (mul_mem hm (H.E_le_M he)) (inv_mem hm)
    exact H.V_inf_M ▸ (⟨h1, h2⟩ : b * e * b⁻¹ ∈ H.V ⊓ H.M)
  intro b hb
  refine mem_normalizer_iff.2 fun e => ⟨key b hb e, fun he' => ?_⟩
  have := key b⁻¹ (inv_mem hb) _ he'
  simpa [mul_assoc] using this

theorem card_NL : Nat.card H.NL = 168 := H.card_normalizer_E

end Setting

@[expose] def VOf (E : Subgroup G) (z : G) : Subgroup G := E ⊔ zpowers z

@[expose] def BOf (E : Subgroup G) (z : G) : Subgroup G :=
  normalizer (VOf E z : Set G) ⊓ centralizer ({z} : Set G)

@[expose] noncomputable def actBOf (E : Subgroup G) (z : G)
    (h : BOf E z ≤ normalizer (E : Set G)) : BOf E z →* MulAut E :=
  E.normalizerMonoidHom.comp (Subgroup.inclusion h)

structure LocalSetting (G : Type) [Group G] [Finite G] where
  z : G
  E : Subgroup G
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  order_z : orderOf z = 2
  card_E : Nat.card E = 8
  sq_E : ∀ e ∈ E, e * e = 1
  z_not_mem_E : z ∉ E
  z_comm_E : ∀ {e : G}, e ∈ E → e * z = z * e
  sylow : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) →
    ∃ g ∈ centralizer ({z} : Set G), P ≤ (VOf E z).map (MulAut.conj g).toMonoidHom
  hB_le : BOf E z ≤ normalizer (E : Set G)
  card_range_actB : Nat.card (actBOf E z hB_le).range = 21

namespace LocalSetting

variable (L : LocalSetting (G := G))

abbrev V : Subgroup G := VOf L.E L.z

abbrev B : Subgroup G := BOf L.E L.z

noncomputable abbrev actB : L.B →* MulAut L.E := actBOf L.E L.z L.hB_le

theorem actB_apply (b : L.B) (e : L.E) :
    ((L.actB b e : L.E) : G) = (b : G) * e * (b : G)⁻¹ := rfl

theorem z_mul_self : L.z * L.z = 1 := by
  rw [← pow_two, ← L.order_z, pow_orderOf_eq_one]

theorem z_inv : L.z⁻¹ = L.z := inv_eq_of_mul_eq_one_right L.z_mul_self

theorem z_ne_one : L.z ≠ 1 := by
  intro h
  have := L.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem E_comm {a b : G} (ha : a ∈ L.E) (hb : b ∈ L.E) : a * b = b * a := by
  have h1 := L.sq_E _ (mul_mem ha hb)
  have h2 := L.sq_E a ha
  have h3 := L.sq_E b hb
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3] at this
  exact this

theorem E_inv {a : G} (ha : a ∈ L.E) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (L.sq_E a ha)

theorem E_le_V : L.E ≤ L.V := le_sup_left

theorem z_mem_V : L.z ∈ L.V := mem_sup_right (mem_zpowers _)

theorem mem_V_iff {x : G} : x ∈ L.V ↔ x ∈ L.E ∨ x * L.z ∈ L.E := by
  constructor
  · intro hx
    obtain ⟨e, he, c, hc, rfl⟩ := CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer (A := L.E)
      (B := zpowers L.z) (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun e he =>
        L.z_comm_E he)) hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      have : L.z ^ n = 1 := by
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← L.order_z]
      rw [this, mul_one]; exact he
    · right
      have : L.z ^ n = L.z := by
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← L.order_z]
      rw [this, mul_assoc, L.z_mul_self, mul_one]; exact he
  · rintro (h | h)
    · exact mem_sup_left h
    · have : x = (x * L.z) * L.z⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers _)))

theorem mem_V_iff' {x : G} : x ∈ L.V ↔ x ∈ L.E ∨ ∃ e ∈ L.E, x = e * L.z := by
  rw [L.mem_V_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨x * L.z, h, ?_⟩
      calc x = x * (L.z * L.z) := by rw [L.z_mul_self, mul_one]
        _ = x * L.z * L.z := by group
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · right
      have : e * L.z * L.z = e := by
        calc e * L.z * L.z = e * (L.z * L.z) := by group
          _ = e := by rw [L.z_mul_self, mul_one]
      rw [this]; exact he

theorem V_sq {x : G} (hx : x ∈ L.V) : x * x = 1 := by
  rcases L.mem_V_iff'.1 hx with h | ⟨e, he, rfl⟩
  · exact L.sq_E x h
  · have hc := L.z_comm_E he
    calc e * L.z * (e * L.z) = e * (L.z * e) * L.z := by group
      _ = e * (e * L.z) * L.z := by rw [← hc]
      _ = (e * e) * (L.z * L.z) := by group
      _ = 1 := by rw [L.sq_E e he, L.z_mul_self, mul_one]

theorem V_comm {a b : G} (ha : a ∈ L.V) (hb : b ∈ L.V) : a * b = b * a := by
  have h1 := L.V_sq (mul_mem ha hb)
  have h2 := L.V_sq ha
  have h3 := L.V_sq hb
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3] at this
  exact this

theorem V_le_centralizer : L.V ≤ centralizer ({L.z} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact (L.V_comm hx L.z_mem_V)

theorem card_V : Nat.card L.V = 16 := by
  have hE : zpowers L.z ≤ centralizer (L.E : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun e he => L.z_comm_E he)
  have hd : Disjoint L.E (zpowers L.z) := by
    rw [Subgroup.disjoint_def]
    intro a ha hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
    rcases J1Std.zpow_eq_one_or_self L.z_mul_self n with h | h
    · exact h
    · exact (L.z_not_mem_E (h ▸ ha)).elim
  have := Nat.card_congr (CFSG.EvenSporadicStandard.mulEquivProdSup hE hd).toEquiv
  rw [show L.V = L.E ⊔ zpowers L.z from rfl, ← this, Nat.card_prod, Nat.card_zpowers,
    L.order_z, L.card_E]

theorem pgroup_V : IsPGroup 2 L.V := IsPGroup.of_card (n := 4) (by rw [L.card_V]; norm_num)

theorem mem_B_def {x : G} :
    x ∈ L.B ↔ x ∈ normalizer (L.V : Set G) ∧ x ∈ centralizer ({L.z} : Set G) :=
  Subgroup.mem_inf

theorem B_le_centralizer : L.B ≤ centralizer ({L.z} : Set G) := inf_le_right

theorem B_le_normalizer_E : L.B ≤ normalizer (L.E : Set G) := L.hB_le

theorem card_range_B : Nat.card L.actB.range = 21 := L.card_range_actB

theorem V_le_B : L.V ≤ L.B := by
  intro v hv
  refine L.mem_B_def.2 ⟨le_normalizer hv, L.V_le_centralizer hv⟩

end LocalSetting

namespace LocalSetting

variable (L : LocalSetting (G := G))

theorem star {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ centralizer ({L.z} : Set G)) :
    Nat.card P ≤ 16 ∧ ∀ x ∈ P, x * x = 1 := by
  obtain ⟨g, -, hg⟩ := L.sylow P hP hPC
  refine ⟨?_, fun x hx => ?_⟩
  · calc Nat.card P ≤ Nat.card (L.V.map (MulAut.conj g).toMonoidHom) :=
        Subgroup.card_le_of_le hg
      _ = 16 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, L.card_V]
  · obtain ⟨v, hv, hvx⟩ := hg hx
    rw [← hvx]
    have := L.V_sq hv
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [this]; group

theorem star_conj {w : G} (hw : IsConj L.z w) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({w} : Set G)) : Nat.card P ≤ 16 ∧ ∀ x ∈ P, x * x = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hw
  set P' : Subgroup G := P.map (MulAut.conj c⁻¹).toMonoidHom with hP'
  have hP'p : IsPGroup 2 P' := hP.map _
  have hP'C : P' ≤ centralizer ({L.z} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hPC hx)
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    have hz : L.z = c⁻¹ * w * c := by rw [← hc]; group
    rw [hz]
    calc c⁻¹ * x * c * (c⁻¹ * w * c) = c⁻¹ * (x * w) * c := by group
      _ = c⁻¹ * (w * x) * c := by rw [this]
      _ = c⁻¹ * w * c * (c⁻¹ * x * c) := by group
  obtain ⟨h1, h2⟩ := L.star hP'p hP'C
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hP', Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at h1
    exact h1
  · have := h2 _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      inv_inv] at this
    have h3 : c⁻¹ * (x * x) * c = 1 := by
      calc c⁻¹ * (x * x) * c = c⁻¹ * x * c * (c⁻¹ * x * c) := by group
        _ = 1 := this
    have := congrArg (fun y => c * y * c⁻¹) h3
    simpa [mul_assoc] using this

theorem le_V_of_isPGroup_of_le_centralizer_V {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer (L.V : Set G)) : P ≤ L.V := by
  have hcomm : ∀ p ∈ P, ∀ v ∈ L.V, p * v = v * p := fun p hp v hv =>
    (Subgroup.mem_centralizer_iff.1 (hPC hp) v hv).symm
  have hPz : P ≤ centralizer ({L.z} : Set G) := fun p hp => by
    rw [mem_centralizer_singleton_iff]
    exact hcomm p hp L.z L.z_mem_V
  have hVP : L.V ≤ centralizer (P : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun p hp => hcomm p hp v hv
  have hsq := (L.star hP hPz).2
  have hsup : IsPGroup 2 (P ⊔ L.V : Subgroup G) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hVP hx
    refine ⟨1, Subtype.ext ?_⟩
    have h1 := hsq a ha
    have h2 := L.V_sq hb
    have h3 := hcomm a ha b hb
    show (a * b) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← h3]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [h1, h2, mul_one]
  have hsupC : (P ⊔ L.V : Subgroup G) ≤ centralizer ({L.z} : Set G) := sup_le hPz L.V_le_centralizer
  have hcard := (L.star hsup hsupC).1
  have := Subgroup.eq_of_le_of_card_ge (le_sup_right : L.V ≤ P ⊔ L.V)
    (by rw [L.card_V]; exact hcard)
  exact le_sup_left.trans this.symm.le

end LocalSetting

end CFSG.EvenSporadicStandard.ReeStd
