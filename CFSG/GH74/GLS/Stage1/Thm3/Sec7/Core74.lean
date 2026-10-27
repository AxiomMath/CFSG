module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.C74

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {G : Type*} [Group G]

@[expose] def K4 (z t : G) : Subgroup G := zpowers z ⊔ zpowers t

@[expose] def Dsub (E S₁ E₂ : Subgroup G) : Subgroup G := E ⊓ S₁ ⊓ E₂

theorem Dsub_le_S₁ (E S₁ E₂ : Subgroup G) : Dsub E S₁ E₂ ≤ S₁ := fun _ hx => hx.1.2

theorem Dsub_le_E (E S₁ E₂ : Subgroup G) : Dsub E S₁ E₂ ≤ E := fun _ hx => hx.1.1

theorem eq_of_mul_system {r₁ r₂ a d f p s : ℕ} (e1 : r₁ * a = d) (e2 : r₂ * p = s)
    (hs : s = f * d) (hp : p = f * a) (hfa : 0 < f * a) : r₁ = r₂ := by
  have key : r₁ * (f * a) = r₂ * (f * a) := by
    calc r₁ * (f * a) = f * (r₁ * a) := by ring
      _ = f * d := by rw [e1]
      _ = s := hs.symm
      _ = r₂ * p := e2.symm
      _ = r₂ * (f * a) := by rw [hp]
  exact Nat.eq_of_mul_eq_mul_right hfa key

structure Ctx74 (z t : G) (S P₁ P₂ S₁ E E₂ : Subgroup G) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  zP₁ : z ∈ P₁
  zP₂ : z ∈ P₂
  P₁S₁ : P₁ ≤ S₁
  P₂S₁ : P₂ ≤ S₁
  S₁S : S₁ ≤ S
  P₁P₂ : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a
  P₁₂ : P₁ ⊓ P₂ ≤ zpowers z
  S₁P₁ : ∀ s ∈ S₁, ∀ p ∈ P₁, s * p * s⁻¹ ∈ P₁
  zS : ∀ s ∈ S, s * z = z * s
  t_mem : t ∈ S
  t_sq : t * t = 1
  t_nS₁ : t ∉ S₁
  S₁idx : S₁.relIndex S = 2
  tP₁ : ∀ x ∈ P₁, t * x * t⁻¹ ∈ P₂
  tP₂ : ∀ x ∈ P₂, t * x * t⁻¹ ∈ P₁
  hE : ∀ x, x ∈ E ↔ x ∈ S ∧ x * t = t * x
  frat : ∀ s ∈ S, ∃ c ∈ P₁ ⊔ P₂, c⁻¹ * s ∈ E
  E₂E : E₂ ≤ E
  E₂idx : ∀ e ∈ E, ∀ e' ∈ E, e ∈ E₂ ∨ e' ∈ E₂ ∨ e⁻¹ * e' ∈ E₂
  zE₂ : z ∉ E₂
  tE₂ : t ∈ E₂

namespace Ctx74

variable {z t : G} {S P₁ P₂ S₁ E E₂ : Subgroup G} (c : Ctx74 z t S P₁ P₂ S₁ E E₂)

include c

theorem zS₁ : z ∈ S₁ := c.P₁S₁ c.zP₁

theorem zS' : z ∈ S := c.S₁S c.zS₁

theorem z_comm_t : z * t = t * z := (c.zS t c.t_mem).symm

theorem z_mem_E : z ∈ E := (c.hE z).2 ⟨c.zS', c.z_comm_t⟩

theorem t_mem_E : t ∈ E := (c.hE t).2 ⟨c.t_mem, rfl⟩

theorem E_le_S : E ≤ S := fun x hx => ((c.hE x).1 hx).1

theorem E_comm {x : G} (hx : x ∈ E) : x * t = t * x := ((c.hE x).1 hx).2

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.t_sq

theorem K4_le_E : K4 z t ≤ E := sup_le (zpowers_le.2 c.z_mem_E) (zpowers_le.2 c.t_mem_E)

theorem K4_central : ∀ a ∈ K4 z t, ∀ b ∈ E, a * b = b * a := by
  have hz : ∀ b ∈ E, z * b = b * z := fun b hb => (c.zS b (c.E_le_S hb)).symm
  have ht : ∀ b ∈ E, t * b = b * t := fun b hb => (c.E_comm hb).symm
  have hle : K4 z t ≤ centralizer (E : Set G) := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_iff.2 (fun b hb => (hz b hb).symm)
    · exact Subgroup.mem_centralizer_iff.2 (fun b hb => (ht b hb).symm)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm

theorem K4_elems : ∀ a ∈ K4 z t, a = 1 ∨ a = z ∨ a = t ∨ a = z * t := by
  intro a ha
  have hc : Commute z t := c.z_comm_t
  have hcomm : ∀ x ∈ zpowers z, ∀ y ∈ zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
    exact (hc.zpow_zpow i j).eq
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ :=
    A.mem_sup_of_commute hcomm (show a ∈ zpowers z ⊔ zpowers t from ha)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha₁
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha₂
  rcases B.zpow_of_sq_eq_one c.z_sq i with h1 | h1 <;>
    rcases B.zpow_of_sq_eq_one c.t_sq j with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2]

theorem K4_inf_D : K4 z t ⊓ Dsub E S₁ E₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxD⟩
  rw [Subgroup.mem_bot]
  have hxS₁ : x ∈ S₁ := hxD.1.2
  have hxE₂ : x ∈ E₂ := hxD.2
  rcases c.K4_elems x hxK with h | h | h | h
  · exact h
  · rw [h] at hxE₂; exact absurd hxE₂ c.zE₂
  · rw [h] at hxS₁; exact absurd hxS₁ c.t_nS₁
  · exfalso
    apply c.t_nS₁
    rw [h] at hxS₁
    have := S₁.mul_mem (S₁.inv_mem c.zS₁) hxS₁
    simpa using this

theorem E_le_KD : E ≤ K4 z t ⊔ Dsub E S₁ E₂ := by
  intro e he
  have hzE := c.z_mem_E
  have htE := c.t_mem_E
  have p1 : ∀ x ∈ E, ∀ y ∈ E, x ∈ S₁ ∨ y ∈ S₁ ∨ x⁻¹ * y ∈ S₁ := fun x hx y hy =>
    A.relIndex_two_pigeon c.S₁idx (c.E_le_S hx) (c.E_le_S hy)
  have p2 := c.E₂idx
  have hK4z : z ∈ K4 z t := mem_sup_left (mem_zpowers z)
  have hK4t : t ∈ K4 z t := mem_sup_right (mem_zpowers t)
  by_cases h1 : e ∈ S₁ <;> by_cases h2 : e ∈ E₂
  · have : e ∈ Dsub E S₁ E₂ := ⟨⟨he, h1⟩, h2⟩
    exact mem_sup_right this
  · have hz2 : z⁻¹ * e ∈ E₂ := by
      rcases p2 z hzE e he with h | h | h
      · exact absurd h c.zE₂
      · exact absurd h h2
      · exact h
    have hz1 : z⁻¹ * e ∈ S₁ := S₁.mul_mem (S₁.inv_mem c.zS₁) h1
    have hD : z⁻¹ * e ∈ Dsub E S₁ E₂ := ⟨⟨E.mul_mem (E.inv_mem hzE) he, hz1⟩, hz2⟩
    have e' : e = z * (z⁻¹ * e) := by group
    rw [e']
    exact mul_mem (mem_sup_left hK4z) (mem_sup_right hD)
  · have ht1 : t⁻¹ * e ∈ S₁ := by
      rcases p1 t htE e he with h | h | h
      · exact absurd h c.t_nS₁
      · exact absurd h h1
      · exact h
    have ht2 : t⁻¹ * e ∈ E₂ := E₂.mul_mem (E₂.inv_mem c.tE₂) h2
    have hD : t⁻¹ * e ∈ Dsub E S₁ E₂ := ⟨⟨E.mul_mem (E.inv_mem htE) he, ht1⟩, ht2⟩
    have e' : e = t * (t⁻¹ * e) := by group
    rw [e']
    exact mul_mem (mem_sup_left hK4t) (mem_sup_right hD)
  · have hztE : z * t ∈ E := E.mul_mem hzE htE
    have hzt1 : z * t ∉ S₁ := by
      intro h
      apply c.t_nS₁
      have := S₁.mul_mem (S₁.inv_mem c.zS₁) h
      simpa using this
    have hzt2 : z * t ∉ E₂ := by
      intro h
      apply c.zE₂
      have := E₂.mul_mem h (E₂.inv_mem c.tE₂)
      simpa using this
    have ht1 : (z * t)⁻¹ * e ∈ S₁ := by
      rcases p1 (z * t) hztE e he with h | h | h
      · exact absurd h hzt1
      · exact absurd h h1
      · exact h
    have ht2 : (z * t)⁻¹ * e ∈ E₂ := by
      rcases p2 (z * t) hztE e he with h | h | h
      · exact absurd h hzt2
      · exact absurd h h2
      · exact h
    have hD : (z * t)⁻¹ * e ∈ Dsub E S₁ E₂ := ⟨⟨E.mul_mem (E.inv_mem hztE) he, ht1⟩, ht2⟩
    have e' : e = (z * t) * ((z * t)⁻¹ * e) := by group
    rw [e']
    exact mul_mem (mem_sup_left ((K4 z t).mul_mem hK4z hK4t)) (mem_sup_right hD)

theorem prod_eq : K4 z t ⊔ Dsub E S₁ E₂ = E :=
  le_antisymm (sup_le c.K4_le_E (Dsub_le_E E S₁ E₂)) c.E_le_KD

theorem S₁_norm_P₁ : S₁ ≤ normalizer (P₁ : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp; exact c.S₁P₁ x hx p hp
  · intro hp
    have := c.S₁P₁ x⁻¹ (S₁.inv_mem hx) _ hp
    simpa [mul_assoc] using this

theorem P_le_S₁ : P₁ ⊔ P₂ ≤ S₁ := sup_le c.P₁S₁ c.P₂S₁

theorem E₁_le {e : G} (he : e ∈ E) (heS₁ : e ∈ S₁) : e ∈ P₁ ⊔ Dsub E S₁ E₂ := by
  have h1 : e ∈ K4 z t ⊔ Dsub E S₁ E₂ := by rw [c.prod_eq]; exact he
  obtain ⟨a, ha, d, hd, rfl⟩ :=
    A.mem_sup_of_commute (A := K4 z t) (B := Dsub E S₁ E₂)
      (fun a ha b hb => c.K4_central a ha b hb.1.1) h1
  have haS₁ : a ∈ S₁ := by
    have := S₁.mul_mem heS₁ (S₁.inv_mem hd.1.2)
    simpa using this
  rcases c.K4_elems a ha with h | h | h | h
  · rw [h, one_mul]; exact mem_sup_right hd
  · rw [h]; exact mul_mem (mem_sup_left c.zP₁) (mem_sup_right hd)
  · rw [h] at haS₁; exact absurd haS₁ c.t_nS₁
  · exfalso
    apply c.t_nS₁
    rw [h] at haS₁
    have := S₁.mul_mem (S₁.inv_mem c.zS₁) haS₁
    simpa using this

theorem P₂_le : P₂ ≤ P₁ ⊔ Dsub E S₁ E₂ := by
  intro p hp
  have hp' : t * p * t⁻¹ ∈ P₁ := c.tP₂ p hp
  have hcomm : p * (t * p * t⁻¹) = (t * p * t⁻¹) * p := (c.P₁P₂ _ hp' p hp).symm
  have hpS : p ∈ S := c.S₁S (c.P₂S₁ hp)
  have hp'S : t * p * t⁻¹ ∈ S := c.S₁S (c.P₁S₁ hp')
  have he : p * (t * p * t⁻¹) ∈ E := by
    rw [c.hE]
    refine ⟨S.mul_mem hpS hp'S, ?_⟩
    rw [c.t_inv] at hcomm ⊢
    calc p * (t * p * t) * t = (t * p * t) * p * t := by rw [hcomm]
      _ = t * (p * (t * p * t)) := by group
  have heS₁ : p * (t * p * t⁻¹) ∈ S₁ := S₁.mul_mem (c.P₂S₁ hp) (c.P₁S₁ hp')
  have h1 := c.E₁_le he heS₁
  have e' : p = (p * (t * p * t⁻¹)) * (t * p * t⁻¹)⁻¹ := by group
  rw [e']
  exact mul_mem h1 ((P₁ ⊔ Dsub E S₁ E₂).inv_mem (mem_sup_left hp'))

theorem S₁_le : S₁ ≤ P₁ ⊔ Dsub E S₁ E₂ := by
  intro s hs
  obtain ⟨cc, hcP, hcE⟩ := c.frat s (c.S₁S hs)
  have hcS₁ : cc ∈ S₁ := c.P_le_S₁ hcP
  have heS₁ : cc⁻¹ * s ∈ S₁ := S₁.mul_mem (S₁.inv_mem hcS₁) hs
  have h1 : cc⁻¹ * s ∈ P₁ ⊔ Dsub E S₁ E₂ := c.E₁_le hcE heS₁
  have h2 : cc ∈ P₁ ⊔ Dsub E S₁ E₂ := sup_le le_sup_left c.P₂_le hcP
  have e' : s = cc * (cc⁻¹ * s) := by group
  rw [e']
  exact mul_mem h2 h1

theorem S₁_eq : S₁ = P₁ ⊔ Dsub E S₁ E₂ :=
  le_antisymm c.S₁_le (sup_le c.P₁S₁ (Dsub_le_S₁ E S₁ E₂))

theorem P₁_inf_D : P₁ ⊓ Dsub E S₁ E₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxD⟩
  rw [Subgroup.mem_bot]
  have hxE : x ∈ E := hxD.1.1
  have hcomm : x * t = t * x := c.E_comm hxE
  have hx2 : x ∈ P₂ := by
    have := c.tP₁ x hxP
    have e : t * x * t⁻¹ = x := by rw [← hcomm]; group
    rwa [e] at this
  have hz : x ∈ zpowers z := c.P₁₂ ⟨hxP, hx2⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
  rcases B.zpow_of_sq_eq_one c.z_sq k with h | h
  · rw [← hk, h]
  · exfalso
    have hxz : x = z := hk.symm.trans h
    apply c.zE₂
    rw [← hxz]
    exact hxD.2

theorem D_norm_P₁ : Dsub E S₁ E₂ ≤ normalizer (P₁ : Set G) := (Dsub_le_S₁ E S₁ E₂).trans c.S₁_norm_P₁

theorem quot_equiv :
    ∃ _ : (P₁.subgroupOf S₁).Normal, Nonempty ((↥S₁ ⧸ P₁.subgroupOf S₁) ≃* ↥(Dsub E S₁ E₂)) := by
  have hnormal : (P₁.subgroupOf S₁).Normal := ⟨fun n hn s => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using c.S₁P₁ (s : G) s.2 (n : G) hn⟩
  refine ⟨hnormal, ?_⟩
  let φ : ↥(Dsub E S₁ E₂) →* ↥S₁ ⧸ P₁.subgroupOf S₁ :=
    (QuotientGroup.mk' (P₁.subgroupOf S₁)).comp (Subgroup.inclusion (Dsub_le_S₁ E S₁ E₂))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hx
    have : (x : G) ∈ P₁ ⊓ Dsub E S₁ E₂ := ⟨hx, x.2⟩
    rw [c.P₁_inf_D] at this
    exact Subtype.ext (by simpa using this)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    have hs : (s : G) ∈ Dsub E S₁ E₂ ⊔ P₁ := by rw [sup_comm, ← c.S₁_eq]; exact s.2
    obtain ⟨d, hd, p, hp, hdp⟩ := A.mem_sup_of_le_normalizer c.D_norm_P₁ hs
    refine ⟨⟨d, hd⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (d : G)⁻¹ * (s : G) = p := by rw [hdp]; group
    simpa [e] using hp
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem P_eq_sup : P₁ ⊔ P₂ = P₁ ⊔ (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) := by
  apply le_antisymm
  · intro y hy
    have hyS₁ : y ∈ S₁ := c.P_le_S₁ hy
    have hy' : y ∈ Dsub E S₁ E₂ ⊔ P₁ := by rw [sup_comm, ← c.S₁_eq]; exact hyS₁
    obtain ⟨d, hd, p, hp, rfl⟩ := A.mem_sup_of_le_normalizer c.D_norm_P₁ hy'
    have hdP : d ∈ P₁ ⊔ P₂ := by
      have := (P₁ ⊔ P₂).mul_mem hy ((P₁ ⊔ P₂).inv_mem (mem_sup_left hp))
      simpa using this
    exact mul_mem (mem_sup_right ⟨hd, hdP⟩) (mem_sup_left hp)
  · exact sup_le le_sup_left inf_le_right

theorem card_S₁ [Finite G] :
    Nat.card ↥S₁ = Nat.card ↥P₁ * Nat.card ↥(Dsub E S₁ E₂) := by
  have h1 := A.card_sup_mul_card_inf c.D_norm_P₁
  rw [← c.S₁_eq, c.P₁_inf_D, Subgroup.card_bot] at h1
  simpa using h1

theorem card_P [Finite G] :
    Nat.card ↥(P₁ ⊔ P₂) = Nat.card ↥P₁ * Nat.card ↥(Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) := by
  have hn : (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) ≤ normalizer (P₁ : Set G) := inf_le_left.trans c.D_norm_P₁
  have h1 := A.card_sup_mul_card_inf hn
  have hbot : P₁ ⊓ (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : x ∈ P₁ ⊓ Dsub E S₁ E₂ := ⟨hx1, hx2.1⟩
    rw [c.P₁_inf_D] at this
    exact this
  rw [← c.P_eq_sup, hbot, Subgroup.card_bot] at h1
  simpa using h1

theorem index_eq [Finite G] :
    (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)).relIndex (Dsub E S₁ E₂) = (P₁ ⊔ P₂).relIndex S₁ := by
  have e1 := Subgroup.relIndex_mul_card (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) (Dsub E S₁ E₂)
  have e2 := Subgroup.relIndex_mul_card (P₁ ⊔ P₂) S₁
  rw [inf_eq_left.2 c.P_le_S₁] at e2
  have hDP : Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂) ⊓ Dsub E S₁ E₂ = Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂) := by
    rw [inf_eq_left.2 (inf_le_left : Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂) ≤ Dsub E S₁ E₂)]
  rw [hDP] at e1
  have hf : 0 < Nat.card ↥P₁ := Nat.card_pos
  have ha : 0 < Nat.card ↥(Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) := Nat.card_pos
  exact eq_of_mul_system e1 e2 c.card_S₁ c.card_P (Nat.mul_pos hf ha)

theorem inter_iso :
    ∃ _ : ((zpowers z).subgroupOf P₂).Normal,
      Nonempty (↥(Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) ≃* (↥P₂ ⧸ (zpowers z).subgroupOf P₂)) := by
  have hP₁P : P₁ ≤ P₁ ⊔ P₂ := le_sup_left
  have hP₂P : P₂ ≤ P₁ ⊔ P₂ := le_sup_right
  have hPS₁ : P₁ ⊔ P₂ ≤ S₁ := c.P_le_S₁
  have hnormal : (P₁.subgroupOf (P₁ ⊔ P₂)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using c.S₁P₁ (g : G) (hPS₁ g.2) (n : G) hn⟩
  let ψ : ↥(Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) →* ↥(P₁ ⊔ P₂) ⧸ P₁.subgroupOf (P₁ ⊔ P₂) :=
    (QuotientGroup.mk' (P₁.subgroupOf (P₁ ⊔ P₂))).comp
      (Subgroup.inclusion (inf_le_right : Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂) ≤ P₁ ⊔ P₂))
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hx
    have : (x : G) ∈ P₁ ⊓ Dsub E S₁ E₂ := ⟨hx, x.2.1⟩
    rw [c.P₁_inf_D] at this
    exact Subtype.ext (by simpa using this)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    have hs : (s : G) ∈ (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) ⊔ P₁ := by
      rw [sup_comm, ← c.P_eq_sup]; exact s.2
    have hn : (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) ≤ normalizer (P₁ : Set G) := inf_le_left.trans c.D_norm_P₁
    obtain ⟨d, hd, p, hp, hdp⟩ := A.mem_sup_of_le_normalizer hn hs
    refine ⟨⟨d, hd⟩, ?_⟩
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (d : G)⁻¹ * (s : G) = p := by rw [hdp]; group
    simpa [e] using hp
  let χ : ↥P₂ →* ↥(P₁ ⊔ P₂) ⧸ P₁.subgroupOf (P₁ ⊔ P₂) :=
    (QuotientGroup.mk' (P₁.subgroupOf (P₁ ⊔ P₂))).comp (Subgroup.inclusion hP₂P)
  have hχsurj : Function.Surjective χ := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, b, hb, hab⟩ := A.mem_sup_of_commute c.P₁P₂ (s.2 : (s : G) ∈ P₁ ⊔ P₂)
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (b : G)⁻¹ * (s : G) = a := by
      rw [hab]
      have := c.P₁P₂ a ha b hb
      calc (b : G)⁻¹ * (a * b) = b⁻¹ * (b * a) := by rw [this]
        _ = a := by group
    simpa [e] using ha
  have hker : χ.ker = (zpowers z).subgroupOf P₂ := by
    ext x
    simp only [MonoidHom.mem_ker, χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact c.P₁₂ ⟨h, x.2⟩
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      show (x : G) ∈ P₁
      rw [← hk]
      exact P₁.zpow_mem c.zP₁ k
  have hnormZ : ((zpowers z).subgroupOf P₂).Normal := hker ▸ MonoidHom.normal_ker χ
  refine ⟨hnormZ, ?_⟩
  let e₁ : ↥(Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) ≃* ↥(P₁ ⊔ P₂) ⧸ P₁.subgroupOf (P₁ ⊔ P₂) :=
    MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let e₂ : ↥P₂ ⧸ χ.ker ≃* ↥(P₁ ⊔ P₂) ⧸ P₁.subgroupOf (P₁ ⊔ P₂) :=
    QuotientGroup.quotientKerEquivOfSurjective χ hχsurj
  let e₃ : ↥P₂ ⧸ (zpowers z).subgroupOf P₂ ≃* ↥P₂ ⧸ χ.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact ⟨e₁.trans (e₂.symm.trans e₃.symm)⟩

end Ctx74

theorem core74 [Finite G] {z t : G} {S P₁ P₂ S₁ E E₂ : Subgroup G}
    (c : Ctx74 z t S P₁ P₂ S₁ E E₂) :
    Dsub E S₁ E₂ ≤ S₁ ∧
    (K4 z t ⊔ Dsub E S₁ E₂ = E ∧ (∀ a ∈ K4 z t, ∀ b ∈ Dsub E S₁ E₂, a * b = b * a) ∧
      K4 z t ⊓ Dsub E S₁ E₂ = ⊥) ∧
    (∃ _ : (P₁.subgroupOf S₁).Normal, Nonempty ((↥S₁ ⧸ P₁.subgroupOf S₁) ≃* ↥(Dsub E S₁ E₂))) ∧
    (Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)).relIndex (Dsub E S₁ E₂) = (P₁ ⊔ P₂).relIndex S₁ ∧
    (∃ _ : ((zpowers z).subgroupOf P₂).Normal,
      Nonempty (↥(Dsub E S₁ E₂ ⊓ (P₁ ⊔ P₂)) ≃* (↥P₂ ⧸ (zpowers z).subgroupOf P₂))) :=
  ⟨Dsub_le_S₁ E S₁ E₂, ⟨c.prod_eq, fun a ha b hb => c.K4_central a ha b hb.1.1, c.K4_inf_D⟩, c.quot_equiv,
    c.index_eq, c.inter_iso⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.C74
