module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinESound

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

structure PinModel (X : Type*) [Group X] (T E : Subgroup X) (t : X) : Prop where
  pgroup : IsPGroup 2 T
  odd : ∃ m : ℕ, Odd m ∧ Nat.card X = Nat.card T * m
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_mem : t ∈ T
  t_central : ∀ x ∈ T, x * t = t * x
  center : ∀ y ∈ T, (∀ x ∈ T, x * y = y * x) → y = 1 ∨ y = t
  pin : ∀ E' : Subgroup X, E' ≤ T → t ∈ E' → (∃ e₁ ∈ E', ∃ e₂ ∈ E', e₁ * e₂ ≠ e₂ * e₁) →
    (∀ e₁ ∈ E', ∀ e₂ ∈ E', e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = 1 ∨ e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = t) →
    (∀ y ∈ E', (∀ f ∈ E', f * y = y * f) → y = 1 ∨ y = t) →
    (∀ s ∈ T, ∀ e ∈ E', s * e * s⁻¹ ∈ E') →
    (∀ s ∈ T, (∀ e ∈ E', s * e = e * s) → s = 1 ∨ s = t) → E' = E
  E_eq : E = closure {x | x ∈ T ∧ x * x = t}
  roots_ge : 20 ≤ Set.ncard {x | x ∈ T ∧ x * x = t}

theorem PinModel.of_table {X : Type*} [Group X] {T : Subgroup X} {t : X} {n : ℕ} {elt : ℕ → X}
    {mul : ℕ → ℕ → ℕ} {tI : ℕ} (hT : TablePin.TableSpec T t n elt mul tI)
    (hcheck : TablePin.pinCheck n mul tI = true) (hp : IsPGroup 2 T)
    (hodd : ∃ m : ℕ, Odd m ∧ Nat.card X = Nat.card T * m) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ x ∈ T, x * t = t * x)
    (hcen : ∀ y ∈ T, (∀ x ∈ T, x * y = y * x) → y = 1 ∨ y = t) :
    PinModel X T (closure (elt '' {a | a ∈ TableE.eList n mul tI})) t :=
  { pgroup := hp
    odd := hodd
    t_sq := ht2
    t_ne := ht1
    t_mem := hT.tI_elt ▸ hT.memT tI hT.tI_lt
    t_central := htc
    center := hcen
    pin := fun _ hET htE hnab hcomm hcen' hnorm hcent =>
      hT.pin_eq htc hcheck hET htE hnab hcomm hcen' hnorm hcent
    E_eq := (hT.eCheck_facts hcheck).1
    roots_ge := (hT.eCheck_facts hcheck).2 }

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem InnerConfig.exists_embedding (h : InnerConfig G L z t T₀) {X : Type*} [Group X] [Finite X]
    {T E : Subgroup X} {tx : X} (hM : PinModel X T E tx) (φ : X ≃* L) :
    ∃ ι : X →* G, Function.Injective ι ∧ (∀ x, ι x ∈ L) ∧ (∀ a ∈ L, ∃ x, ι x = a) ∧
      T.map ι = T₀ ∧ ι tx = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hcardX⟩ := hM.odd
  have hcardL : Nat.card L = Nat.card X := Nat.card_congr φ.toEquiv.symm
  let T₁ : Subgroup L := T.map φ.toMonoidHom
  have hT₁card : Nat.card T₁ = Nat.card T := Subgroup.card_map_of_injective φ.injective
  have hT₁p : IsPGroup 2 T₁ := hM.pgroup.map _
  have hidx₁ : ¬ 2 ∣ T₁.index := by
    have h1 := Subgroup.index_mul_card (H := T₁)
    rw [hT₁card, hcardL, hcardX] at h1
    have hpos : 0 < Nat.card T := Nat.card_pos
    have : T₁.index = m := Nat.eq_of_mul_eq_mul_right hpos (h1.trans (mul_comm _ _))
    rw [this]
    exact fun hd => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hd)
  let S₁ : Sylow 2 L := hT₁p.toSylow hidx₁
  have hT₀p : IsPGroup 2 (T₀.subgroupOf L) := h.T₀_pgroup.comap_subtype
  have hidx₀ : ¬ 2 ∣ (T₀.subgroupOf L).index := by
    obtain ⟨m', hm', hAm⟩ := h.T₀_odd
    have h1 := Subgroup.index_mul_card (H := T₀.subgroupOf L)
    rw [Nat.card_congr (subgroupOfEquivOfLe h.T₀_le).toEquiv, hAm] at h1
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    have : (T₀.subgroupOf L).index = m' :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans (mul_comm _ _))
    rw [this]
    exact fun hd => (Nat.not_even_iff_odd.2 hm') (even_iff_two_dvd.2 hd)
  let S₀ : Sylow 2 L := hT₀p.toSylow hidx₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L S₁ S₀
  have hgS : ∀ x : L, x ∈ (S₀ : Subgroup L) ↔ g⁻¹ * x * g ∈ (S₁ : Subgroup L) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hsx⟩
      have : g⁻¹ * x * g = s := by
        rw [← hsx, MulAut.smul_def, MulAut.conj_apply]; group
      rw [this]; exact hs
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩
  let ι : X →* G := (MulAut.conj (g : G)).toMonoidHom.comp (L.subtype.comp φ.toMonoidHom)
  have hιapp : ∀ x, ι x = (g : G) * ((φ x : L) : G) * (g : G)⁻¹ := fun x => by
    simp [ι, MulAut.conj_apply]
  have hι : Function.Injective ι :=
    (MulAut.conj (g : G)).injective.comp (L.subtype_injective.comp φ.injective)
  have hιL : ∀ x, ι x ∈ L := fun x => by
    rw [hιapp]
    exact mul_mem (mul_mem g.2 (φ x).2) (inv_mem g.2)
  have hrange : ∀ a ∈ L, ∃ x, ι x = a := by
    intro a ha
    refine ⟨φ.symm (g⁻¹ * ⟨a, ha⟩ * g), ?_⟩
    rw [hιapp]
    simp only [MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hTι : T.map ι = T₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : φ x ∈ (S₁ : Subgroup L) := ⟨x, hx, rfl⟩
      have hx2 : g * φ x * g⁻¹ ∈ (S₀ : Subgroup L) := by
        rw [hgS]
        have : g⁻¹ * (g * φ x * g⁻¹) * g = φ x := by group
        rwa [this]
      have hx3 : g * φ x * g⁻¹ ∈ T₀.subgroupOf L := hx2
      have hx4 : (((g * φ x * g⁻¹ : L)) : G) ∈ T₀ := hx3
      rw [hιapp]
      simpa using hx4
    · intro hy
      have hyL : y ∈ L := h.T₀_le hy
      obtain ⟨x, rfl⟩ := hrange y hyL
      refine ⟨x, ?_, rfl⟩
      have hx2 : (⟨ι x, hyL⟩ : L) ∈ (S₀ : Subgroup L) := hy
      rw [hgS] at hx2
      have hx3 : φ x ∈ (S₁ : Subgroup L) := by
        have : g⁻¹ * (⟨ι x, hyL⟩ : L) * g = φ x := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hιapp]
          group
        rwa [this] at hx2
      obtain ⟨x', hx', hx'e⟩ := hx3
      have : x' = x := φ.injective hx'e
      rwa [← this]
  have hιt : ι tx = t := by
    have hmem : ι tx ∈ T₀ := hTι ▸ ⟨tx, hM.t_mem, rfl⟩
    have hc : ∀ y ∈ T₀, y * ι tx = ι tx * y := by
      intro y hy
      rw [← hTι] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      rw [← map_mul, ← map_mul, hM.t_central s hs]
    rcases h.center_le _ hmem (fun x hx => hc x hx) with h1 | h1
    · exact absurd (hι (by rw [h1, map_one])) hM.t_ne
    · exact h1
  exact ⟨ι, hι, hιL, hrange, hTι, hιt⟩

omit [Finite G] in
theorem EConfig.eq_map_of_pinModel {E : Subgroup G} (h : InnerConfig G L z t T₀)
    (hE : EConfig L T₀ E t) {X : Type*} [Group X] {T Ex : Subgroup X} {tx : X}
    (hM : PinModel X T Ex tx) (ι : X →* G) (hι : Function.Injective ι)
    (hrange : ∀ a ∈ L, ∃ x, ι x = a) (hTι : T.map ι = T₀) (hιt : ι tx = t) :
    E = Ex.map ι := by
  have hET : E ≤ ι.range := fun e he => by
    obtain ⟨x, hx⟩ := hrange e (h.T₀_le (hE.le he))
    exact ⟨x, hx⟩
  have hTmem : ∀ x, ι x ∈ T₀ → x ∈ T := by
    intro x hx
    rw [← hTι] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    rwa [← hι hsx]
  let E' : Subgroup X := E.comap ι
  have hE'T : E' ≤ T := fun x hx => hTmem x (hE.le hx)
  have hmapE' : E'.map ι = E := Subgroup.map_comap_eq_self hET
  have hpin := hM.pin E' hE'T (by
      show ι tx ∈ E
      rw [hιt]; exact hE.t_mem)
    (by
      obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hE.nonab
      obtain ⟨x₁, rfl⟩ := hrange e₁ (h.T₀_le (hE.le he₁))
      obtain ⟨x₂, rfl⟩ := hrange e₂ (h.T₀_le (hE.le he₂))
      refine ⟨x₁, he₁, x₂, he₂, fun hc => hne ?_⟩
      rw [← map_mul, ← map_mul, hc])
    (by
      intro x₁ hx₁ x₂ hx₂
      have := hE.comm _ hx₁ _ hx₂
      rcases this with h1 | h1
      · left
        apply hι
        simpa [map_mul, map_inv] using h1
      · right
        apply hι
        rw [hιt]
        simpa [map_mul, map_inv] using h1)
    (by
      intro y hy hc
      have hcomm : ∀ f ∈ E, f * ι y = ι y * f := by
        intro f hf
        obtain ⟨x, rfl⟩ := hrange f (h.T₀_le (hE.le hf))
        rw [← map_mul, ← map_mul]
        exact congrArg ι (hc x hf)
      rcases hE.center _ hy hcomm with h1 | h1
      · left; exact hι (by rw [h1, map_one])
      · right; exact hι (by rw [h1, hιt]))
    (by
      intro s hs x hx
      have := hE.normal (ι s) (by rw [← hTι]; exact ⟨s, hs, rfl⟩) _ hx
      show ι (s * x * s⁻¹) ∈ E
      simpa [map_mul, map_inv] using this)
    (by
      intro s hs hc
      have hcomm : ∀ e ∈ E, ι s * e = e * ι s := by
        intro e he
        obtain ⟨x, rfl⟩ := hrange e (h.T₀_le (hE.le he))
        rw [← map_mul, ← map_mul]
        exact congrArg ι (hc x he)
      rcases hE.cent _ (by rw [← hTι]; exact ⟨s, hs, rfl⟩) hcomm with h1 | h1
      · left; exact hι (by rw [h1, map_one])
      · right; exact hι (by rw [h1, hιt]))
  rw [← hmapE', hpin]

end CFSG.EvenSporadicStandard.Fin76b
