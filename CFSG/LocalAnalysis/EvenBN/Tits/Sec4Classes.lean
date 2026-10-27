module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4FusionTwo
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Orbits

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] noncomputable def liftSub (d : Data G) (X : Subgroup (Equiv.Perm (Fin 1755))) :
    Subgroup G :=
  ((X.subgroupOf titsD).map d.θ.symm.toMonoidHom).map d.L.subtype

omit [Finite G] in
theorem mem_liftSub {X : Subgroup (Equiv.Perm (Fin 1755))} {g : G} :
    g ∈ d.liftSub X ↔ ∃ x ∈ X, x ∈ titsD ∧ d.lift x = g := by
  constructor
  · rintro ⟨l, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, mem_subgroupOf.1 hy, y.2, by rw [d.lift_eq y.2]; rfl⟩
  · rintro ⟨x, hx, hxD, rfl⟩
    exact ⟨d.θ.symm ⟨x, hxD⟩, ⟨⟨x, hxD⟩, mem_subgroupOf.2 hx, rfl⟩, (d.lift_eq hxD).symm⟩

omit [Finite G] in
theorem liftSub_le (X : Subgroup (Equiv.Perm (Fin 1755))) : d.liftSub X ≤ d.L :=
  map_subtype_le _

omit [Finite G] in
theorem lift_θ (l : d.L) : d.lift ((d.θ l : titsD) : Equiv.Perm (Fin 1755)) = l := by
  rw [d.lift_eq (d.θ l).2]
  simp

omit [Finite G] in
theorem lift_inv {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) : d.lift a⁻¹ = (d.lift a)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← d.lift_mul (inv_mem ha) ha, inv_mul_cancel, d.lift_one]

omit [Finite G] in
theorem lift_conj {δ x : Equiv.Perm (Fin 1755)} (hδ : δ ∈ titsD) (hx : x ∈ titsD) :
    d.lift (δ * x * δ⁻¹) = d.lift δ * d.lift x * (d.lift δ)⁻¹ := by
  rw [d.lift_mul (mul_mem hδ hx) (inv_mem hδ), d.lift_mul hδ hx, d.lift_inv hδ]

omit [Finite G] in
theorem card_liftSub {X : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD) :
    Nat.card (d.liftSub X) = Nat.card X := by
  rw [liftSub, card_map_of_injective d.L.subtype_injective,
    card_map_of_injective (f := d.θ.symm.toMonoidHom) d.θ.symm.injective,
    Nat.card_congr (subgroupOfEquivOfLe hXD).toEquiv]

omit [Finite G] in
theorem liftSub_injective {X Y : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD)
    (hYD : Y ≤ titsD) (h : d.liftSub X = d.liftSub Y) : X = Y := by
  have key : ∀ {X Y : Subgroup (Equiv.Perm (Fin 1755))}, X ≤ titsD → Y ≤ titsD →
      d.liftSub X = d.liftSub Y → X ≤ Y := by
    intro X Y hXD hYD h x hx
    have hm : d.lift x ∈ d.liftSub X := mem_liftSub.2 ⟨x, hx, hXD hx, rfl⟩
    rw [h] at hm
    obtain ⟨y, hy, hyD, hyx⟩ := mem_liftSub.1 hm
    rwa [← d.lift_inj hyD (hXD hx) hyx]
  exact le_antisymm (key hXD hYD h) (key hYD hXD h.symm)

omit [Finite G] in
theorem liftSub_elemAbelian {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1) :
    (∀ a ∈ d.liftSub X, ∀ b ∈ d.liftSub X, a * b = b * a) ∧ ∀ a ∈ d.liftSub X, a * a = 1 := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 ha
    obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hb
    exact d.lift_comm hxD hyD (hc x hx y hy)
  · obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 ha
    rw [← d.lift_mul hxD hxD, h2 x hx, d.lift_one]

theorem Hyp.map_conj_liftSub (hd : d.Hyp) {c : G}
    (hc : c ∈ centralizer ({d.t} : Set G)) {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hXD : X ≤ titsD) :
    (d.liftSub X).map (MulAut.conj c).toMonoidHom =
      d.liftSub (X.map (MulAut.conj (d.ρ ⟨c, hc⟩ : Equiv.Perm (Fin 1755))).toMonoidHom) := by
  set r : Equiv.Perm (Fin 1755) := ↑(d.ρ ⟨c, hc⟩) with hr
  have hrA : r ∈ titsA := (d.ρ ⟨c, hc⟩).2
  have hconj : ∀ x ∈ titsD, r * x * r⁻¹ ∈ titsD := fun x hx =>
    (Model.conj_mem_titsD_iff hrA (titsD_le_titsA hx)).2 hx
  have hlift : ∀ x ∈ titsD, c * d.lift x * c⁻¹ = d.lift (r * x * r⁻¹) := fun x hx =>
    hd.conj_lift_eq hc hx (hconj x hx) (by rw [hr]; group)
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 hy
    refine mem_liftSub.2 ⟨r * x * r⁻¹, ⟨x, hx, rfl⟩, hconj x hxD, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (hlift x hxD).symm
  · intro hg
    obtain ⟨_, ⟨x, hx, rfl⟩, hxD', rfl⟩ := mem_liftSub.1 hg
    have hxD : x ∈ titsD := hXD hx
    refine ⟨d.lift x, mem_liftSub.2 ⟨x, hx, hxD, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hlift x hxD

omit [Finite G] in
theorem mem_sup_zpowers_iff {P : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hc : ∀ p ∈ P, p * t = t * p) {x : G} : x ∈ P ⊔ zpowers t ↔ x ∈ P ∨ t * x ∈ P := by
  have hct : ∀ y : G, (y ∈ P ∨ t * y ∈ P) → y * t = t * y := by
    rintro y (hy | hy)
    · exact hc y hy
    · have e : y = t * (t * y) := by rw [← mul_assoc, ht2, one_mul]
      rw [e, mul_assoc, hc _ hy]
  constructor
  · intro hx
    let K : Subgroup G :=
      { carrier := {y | y ∈ P ∨ t * y ∈ P}
        mul_mem' := by
          rintro a b ha hb
          have hat := hct a ha
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (mul_mem ha hb)
          · refine Or.inr ?_
            rw [← mul_assoc, ← hat, mul_assoc]
            exact mul_mem ha hb
          · refine Or.inr ?_
            rw [← mul_assoc]
            exact mul_mem ha hb
          · refine Or.inl ?_
            have e : a * b = t * a * (t * b) := by
              calc a * b = (t * t) * a * b := by rw [ht2, one_mul]
                _ = t * (t * a) * b := by group
                _ = t * (a * t) * b := by rw [hat]
                _ = t * a * (t * b) := by group
            rw [e]
            exact mul_mem ha hb
        one_mem' := Or.inl (one_mem _)
        inv_mem' := by
          rintro a ha
          have hat := hct a ha
          rcases ha with ha | ha
          · exact Or.inl (inv_mem ha)
          · refine Or.inr ?_
            have e : t * a⁻¹ = (t * a)⁻¹ := by
              rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2]
              calc t * a⁻¹ = a⁻¹ * (a * t) * a⁻¹ := by group
                _ = a⁻¹ * (t * a) * a⁻¹ := by rw [hat]
                _ = a⁻¹ * t := by group
            rw [e]
            exact inv_mem ha }
    have hle : P ⊔ zpowers t ≤ K :=
      sup_le (fun p hp => Or.inl hp) (zpowers_le.2 (Or.inr (by rw [ht2]; exact one_mem _)))
    exact hle hx
  · rintro (h | h)
    · exact mem_sup_left h
    · have e : x = t * (t * x) := by rw [← mul_assoc, ht2, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h)

omit [Finite G] in
theorem sup_zpowers_elemAbelian {P : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hc : ∀ p ∈ P, p * t = t * p) (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hP2 : ∀ a ∈ P, a * a = 1) :
    (∀ a ∈ P ⊔ zpowers t, ∀ b ∈ P ⊔ zpowers t, a * b = b * a) ∧
      ∀ a ∈ P ⊔ zpowers t, a * a = 1 := by
  have hct : ∀ y : G, (y ∈ P ∨ t * y ∈ P) → y * t = t * y := by
    rintro y (hy | hy)
    · exact hc y hy
    · have e : y = t * (t * y) := by rw [← mul_assoc, ht2, one_mul]
      rw [e, mul_assoc, hc _ hy]
  have htt : ∀ a b : G, a * t = t * a → t * a * (t * b) = a * b := fun a b hab => by
    calc t * a * (t * b) = t * (a * t) * b := by group
      _ = t * (t * a) * b := by rw [hab]
      _ = a * b := by rw [← mul_assoc, ht2, one_mul]
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [mem_sup_zpowers_iff ht2 hc] at ha hb
    have hat := hct a ha
    have hbt := hct b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hPc a ha b hb
    · have h := hPc a ha _ hb
      rw [← mul_assoc, hat, mul_assoc, mul_assoc] at h
      exact mul_left_cancel h
    · have h := hPc _ ha b hb
      rw [mul_assoc, ← mul_assoc b, hbt, mul_assoc] at h
      exact mul_left_cancel h
    · have h := hPc _ ha _ hb
      rwa [htt a b hat, htt b a hbt] at h
  · rw [mem_sup_zpowers_iff ht2 hc] at ha
    have hat := hct a ha
    rcases ha with ha | ha
    · exact hP2 a ha
    · rw [← htt a a hat]
      exact hP2 _ ha

theorem Hyp.t_mul_self (hd : d.Hyp) : d.t * d.t = 1 := by
  rw [← sq, ← hd.t_two, pow_orderOf_eq_one]

theorem Hyp.L_comm_t (hd : d.Hyp) {l : G} (hl : l ∈ d.L) : l * d.t = d.t * l :=
  mem_centralizer_iff.1 hd.t_mem l hl

theorem Hyp.tSup_facts (hd : d.Hyp) {P : Subgroup G} (hPL : P ≤ d.L) :
    (∀ x, x ∈ P ⊔ zpowers d.t ↔ x ∈ P ∨ d.t * x ∈ P) ∧
      (∀ x, x ∈ P ⊔ zpowers d.t → x ∈ d.L → x ∈ P) ∧
      P ⊔ zpowers d.t ≤ centralizer ({d.t} : Set G) ∧
      Nat.card (P ⊔ zpowers d.t : Subgroup G) = 2 * Nat.card P := by
  have ht2 := hd.t_mul_self
  have hc : ∀ p ∈ P, p * d.t = d.t * p := fun p hp => hd.L_comm_t (hPL hp)
  have hmem := fun x => mem_sup_zpowers_iff (x := x) ht2 hc
  refine ⟨hmem, fun x hx hxL => ?_, ?_, ?_⟩
  · rcases (hmem x).1 hx with h | h
    · exact h
    · exfalso
      apply hd.t_not_mem
      have e : d.t = d.t * x * x⁻¹ := by group
      rw [e]
      exact mul_mem (hPL h) (inv_mem hxL)
  · exact sup_le (hPL.trans hd.L_le) (zpowers_le.2 d.t_mem_centralizer)
  · have hset : ((P ⊔ zpowers d.t : Subgroup G) : Set G) =
        (P : Set G) ∪ (fun x => d.t * x) '' (P : Set G) := by
      ext x
      constructor
      · intro hx
        rcases (hmem x).1 hx with h | h
        · exact Or.inl h
        · refine Or.inr ⟨d.t * x, h, ?_⟩
          show d.t * (d.t * x) = x
          rw [← mul_assoc, ht2, one_mul]
      · rintro (hx | ⟨y, hy, rfl⟩)
        · exact (hmem x).2 (Or.inl hx)
        · refine (hmem _).2 (Or.inr ?_)
          show d.t * (d.t * y) ∈ P
          rw [← mul_assoc, ht2, one_mul]
          exact hy
    have hdisj : Disjoint (P : Set G) ((fun x => d.t * x) '' (P : Set G)) := by
      rw [Set.disjoint_left]
      rintro x hx ⟨y, hy, rfl⟩
      apply hd.t_not_mem
      have e : d.t = d.t * y * y⁻¹ := by group
      rw [e]
      exact mul_mem (hPL hx) (inv_mem (hPL hy))
    calc Nat.card (P ⊔ zpowers d.t : Subgroup G)
        = ((P ⊔ zpowers d.t : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
      _ = (P : Set G).ncard + ((fun x => d.t * x) '' (P : Set G)).ncard := by
          rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      _ = 2 * Nat.card P := by
          rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), ← Nat.card_coe_set_eq]
          change Nat.card P + Nat.card P = 2 * Nat.card P
          ring

@[expose] noncomputable def E
    (d : Data G) : Subgroup G :=
  d.liftSub Model.hatE

@[expose] noncomputable def F (d : Data G) : Subgroup G := d.liftSub Model.parrottF

@[expose] noncomputable def A
    (d : Data G) : Subgroup G :=
  d.E ⊔ zpowers d.t

@[expose] noncomputable def B (d : Data G) : Subgroup G := d.F ⊔ zpowers d.t

@[expose] noncomputable def M
    (d : Data G) : Subgroup G :=
  normalizer (d.A : Set G)

@[expose] noncomputable def N (d : Data G) : Subgroup G := normalizer (d.B : Set G)

@[expose] noncomputable def pv (d : Data G) (i : ℕ) : G := d.lift (Model.parrottV i)

@[expose] def zL (d : Data G) : Set G :=
  {y | ∃ l ∈ d.L, l * d.z * l⁻¹ = y}

@[expose] def vL (d : Data G) : Set G :=
  {y | ∃ l ∈ d.L, l * d.v * l⁻¹ = y}

omit [Finite G] in
theorem zL_eq (d : Data G) :
    d.zL = d.lift '' {x | x ∈ titsD ∧ Model.IsLong x} := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    set δ := ((d.θ ⟨l, hl⟩ : titsD) : Equiv.Perm (Fin 1755)) with hδ
    have hδD : δ ∈ titsD := (d.θ ⟨l, hl⟩).2
    refine ⟨δ * titsZ * δ⁻¹, ⟨mul_mem (mul_mem hδD titsZ_mem_titsD) (inv_mem hδD),
      δ, hδD, rfl⟩, ?_⟩
    rw [d.lift_conj hδD titsZ_mem_titsD, hδ, d.lift_θ, d.lift_titsZ]
  · rintro ⟨x, ⟨-, δ, hδD, rfl⟩, rfl⟩
    exact ⟨d.lift δ, d.lift_mem δ, by rw [d.lift_conj hδD titsZ_mem_titsD, d.lift_titsZ]⟩

omit [Finite G] in
theorem vL_eq (d : Data G) :
    d.vL = d.lift '' {x | x ∈ titsD ∧ Model.IsShort x} := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    set δ := ((d.θ ⟨l, hl⟩ : titsD) : Equiv.Perm (Fin 1755)) with hδ
    have hδD : δ ∈ titsD := (d.θ ⟨l, hl⟩).2
    refine ⟨δ * titsTInv * δ⁻¹, ⟨mul_mem (mul_mem hδD titsTInv_mem_titsD) (inv_mem hδD),
      δ, hδD, rfl⟩, ?_⟩
    rw [d.lift_conj hδD titsTInv_mem_titsD, hδ, d.lift_θ, d.lift_titsTInv]
  · rintro ⟨x, ⟨-, δ, hδD, rfl⟩, rfl⟩
    exact ⟨d.lift δ, d.lift_mem δ, by rw [d.lift_conj hδD titsTInv_mem_titsD, d.lift_titsTInv]⟩

omit [Finite G] in
theorem ncard_lift_image {Y : Set (Equiv.Perm (Fin 1755))} (hY : Y ⊆ titsD) :
    (d.lift '' Y).ncard = Y.ncard :=
  Set.InjOn.ncard_image fun _ hx _ hy h => d.lift_inj (hY hx) (hY hy) h

theorem Hyp.zL_vL_inter (hd : d.Hyp)
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD) :
    d.zL ∩ (d.liftSub X ⊔ zpowers d.t : Subgroup G) =
        d.lift '' {x | x ∈ X ∧ Model.IsLong x} ∧
      d.vL ∩ (d.liftSub X ⊔ zpowers d.t : Subgroup G) =
        d.lift '' {x | x ∈ X ∧ Model.IsShort x} := by
  have key : ∀ (C : Set (Equiv.Perm (Fin 1755))),
      (d.lift '' {x | x ∈ titsD ∧ x ∈ C}) ∩ (d.liftSub X ⊔ zpowers d.t : Subgroup G) =
        d.lift '' {x | x ∈ X ∧ x ∈ C} := by
    intro C
    ext y
    constructor
    · rintro ⟨⟨x, ⟨hxD, hxC⟩, rfl⟩, hy⟩
      have hyS := (hd.tSup_facts (d.liftSub_le X)).2.1 _ hy (d.lift_mem x)
      obtain ⟨x', hx', hx'D, he⟩ := mem_liftSub.1 hyS
      rw [← d.lift_inj hx'D hxD he]
      exact ⟨x', ⟨hx', by rw [d.lift_inj hx'D hxD he]; exact hxC⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxC⟩, rfl⟩
      exact ⟨⟨x, ⟨hXD hx, hxC⟩, rfl⟩, mem_sup_left (mem_liftSub.2 ⟨x, hx, hXD hx, rfl⟩)⟩
  refine ⟨?_, ?_⟩
  · rw [zL_eq]
    have := key {x | Model.IsLong x}
    simpa using this
  · rw [vL_eq]
    have := key {x | Model.IsShort x}
    simpa using this

theorem Hyp.liftSub_tSup_facts (hd : d.Hyp) {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hXD : X ≤ titsD) (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1)
    (h32 : Nat.card X = 32) :
    Nat.card (d.liftSub X) = 32 ∧ d.liftSub X ⊔ zpowers d.t ≤ centralizer ({d.t} : Set G) ∧
      CFSG.Open.IsElemAbelian 2 (d.liftSub X ⊔ zpowers d.t) ∧
      Nat.card (d.liftSub X ⊔ zpowers d.t : Subgroup G) = 2 ^ 6 ∧
      (∀ x, x ∈ d.liftSub X ⊔ zpowers d.t → x ∈ d.L → x ∈ d.liftSub X) := by
  obtain ⟨-, hL, hC, hcard⟩ := hd.tSup_facts (d.liftSub_le X)
  obtain ⟨hPc, hP2⟩ := d.liftSub_elemAbelian hc h2
  obtain ⟨hSc, hS2⟩ := sup_zpowers_elemAbelian hd.t_mul_self
    (fun p hp => hd.L_comm_t (d.liftSub_le X hp)) hPc hP2
  have h32' : Nat.card (d.liftSub X) = 32 := by rw [d.card_liftSub hXD, h32]
  refine ⟨h32', hC, ⟨⟨⟨fun a b => Subtype.ext (hSc a a.2 b b.2)⟩⟩, fun x hx => ?_⟩, ?_, hL⟩
  · rw [sq]
    exact hS2 x hx
  · rw [hcard, h32']
    norm_num

theorem Hyp.A_facts
    (hd : d.Hyp) :
    Nat.card d.E = 32 ∧ d.A ≤ centralizer ({d.t} : Set G) ∧ CFSG.Open.IsElemAbelian 2 d.A ∧
      Nat.card d.A = 2 ^ 6 ∧ (∀ x, x ∈ d.A → x ∈ d.L → x ∈ d.E) := by
  obtain ⟨hEJ, hE2, hEc, hE32⟩ := Model.card_hatE
  exact hd.liftSub_tSup_facts (hEJ.trans titsJ_le_titsD) hEc hE2 hE32

theorem Hyp.B_facts
    (hd : d.Hyp) :
    Nat.card d.F = 32 ∧ d.B ≤ centralizer ({d.t} : Set G) ∧ CFSG.Open.IsElemAbelian 2 d.B ∧
      Nat.card d.B = 2 ^ 6 ∧ (∀ x, x ∈ d.B → x ∈ d.L → x ∈ d.F) :=
  hd.liftSub_tSup_facts Model.parrottF_le_titsD Model.parrottF_elemAbelian.1
    Model.parrottF_elemAbelian.2 Model.card_parrottF

omit [Finite G] in
theorem liftSub_image {P : Subgroup G} (hPL : P ≤ d.L) :
    d.liftSub (((P.subgroupOf d.L).map d.θ.toMonoidHom).map titsD.subtype) = P := by
  ext g
  rw [mem_liftSub]
  constructor
  · rintro ⟨_, ⟨_, ⟨l, hl, rfl⟩, rfl⟩, -, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [d.lift_θ]
    exact mem_subgroupOf.1 hl
  · intro hg
    refine ⟨((d.θ ⟨g, hPL hg⟩ : titsD) : Equiv.Perm (Fin 1755)),
      ⟨d.θ ⟨g, hPL hg⟩, ⟨⟨g, hPL hg⟩, mem_subgroupOf.2 hg, rfl⟩, rfl⟩, (d.θ _).2, ?_⟩
    exact d.lift_θ ⟨g, hPL hg⟩

theorem Hyp.exists_map_conj_eq_A_or_B
    (hd : d.Hyp) {X : Subgroup G} (hX : X ≤ centralizer ({d.t} : Set G))
    (hXa : CFSG.Open.IsElemAbelian 2 X) (h64 : Nat.card X = 2 ^ 6) :
    ∃ c ∈ centralizer ({d.t} : Set G),
      X.map (MulAut.conj c).toMonoidHom = d.A ∨ X.map (MulAut.conj c).toMonoidHom = d.B := by
  obtain ⟨hcomm, hsq⟩ := hXa
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hX2 : ∀ a ∈ X, a * a = 1 := fun a ha => by rw [← sq]; exact hsq a ha
  have ht2 := hd.t_mul_self
  have htc : ∀ p ∈ X, p * d.t = d.t * p := fun p hp => mem_centralizer_singleton_iff.1 (hX hp)
  have htX : d.t ∈ X := by
    obtain ⟨hYc, hY2⟩ := sup_zpowers_elemAbelian ht2 htc hXc hX2
    have hYC : X ⊔ zpowers d.t ≤ centralizer ({d.t} : Set G) :=
      sup_le hX (zpowers_le.2 d.t_mem_centralizer)
    have hY := hd.card_le_of_isElemAbelian hYC
      ⟨⟨⟨fun a b => Subtype.ext (hYc a a.2 b b.2)⟩⟩, fun x hx => by rw [sq]; exact hY2 x hx⟩
    have heq : X = X ⊔ zpowers d.t := eq_of_le_of_card_ge le_sup_left (by rw [h64]; exact hY)
    rw [heq]
    exact mem_sup_right (mem_zpowers _)
  set P := X ⊓ d.L with hP
  have hPL : P ≤ d.L := inf_le_right
  obtain ⟨hmem, -, -, hcard⟩ := hd.tSup_facts hPL
  have hXP : X = P ⊔ zpowers d.t := by
    apply le_antisymm
    · intro x hx
      rw [hmem]
      rcases hd.involution_mem (hX hx) (by rw [sq]; exact hX2 x hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨mul_mem htX hx, h⟩
    · exact sup_le inf_le_left (zpowers_le.2 htX)
  have hP32 : Nat.card P = 32 := by
    have := hcard
    rw [← hXP, h64] at this
    omega
  set Q := ((P.subgroupOf d.L).map d.θ.toMonoidHom).map titsD.subtype with hQ
  have hQD : Q ≤ titsD := map_subtype_le _
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hab : a * b = b * a :=
      Subtype.ext (hXc _ (mem_subgroupOf.1 ha).1 _ (mem_subgroupOf.1 hb).1)
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  have hQ2 : ∀ a ∈ Q, a * a = 1 := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have haa : a * a = 1 := Subtype.ext (hX2 _ (mem_subgroupOf.1 ha).1)
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← Subgroup.coe_mul, ← map_mul, haa, map_one, OneMemClass.coe_one]
  have hQ32 : Nat.card Q = 32 := by
    rw [hQ, card_map_of_injective titsD.subtype_injective,
      card_map_of_injective (f := d.θ.toMonoidHom) d.θ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv, hP32]
  obtain ⟨δ, hδD, hδ⟩ := Model.exists_eq_conj_of_elemAbelian (hQD.trans titsD_le_titsA)
    hQc hQ2 hQ32
  have hδL : d.lift δ ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem δ)
  have hρδ : (d.ρ ⟨d.lift δ, hδL⟩ : Equiv.Perm (Fin 1755)) = δ := hd.ρ_lift hδD
  refine ⟨(d.lift δ)⁻¹, inv_mem hδL, ?_⟩
  have hPeq : ∀ Y : Subgroup (Equiv.Perm (Fin 1755)), Y ≤ titsD →
      Q = Y.map (MulAut.conj δ).toMonoidHom →
      X.map (MulAut.conj (d.lift δ)⁻¹).toMonoidHom = d.liftSub Y ⊔ zpowers d.t := by
    intro Y hYD hQY
    have h1 : P = (d.liftSub Y).map (MulAut.conj (d.lift δ)).toMonoidHom := by
      rw [hd.map_conj_liftSub hδL hYD, hρδ, ← hQY, hQ, liftSub_image hPL]
    rw [hXP, Subgroup.map_sup, h1, Model.map_conj_map_conj, inv_mul_cancel, Model.map_conj_one,
      MonoidHom.map_zpowers]
    congr 2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hc : d.lift δ * d.t = d.t * d.lift δ := hd.L_comm_t (d.lift_mem δ)
    calc (d.lift δ)⁻¹ * d.t * d.lift δ = (d.lift δ)⁻¹ * (d.lift δ * d.t) := by rw [mul_assoc, hc]
      _ = d.t := by group
  rcases hδ with h | h
  · exact Or.inl (hPeq _ (Model.hatE_le_titsJ.trans titsJ_le_titsD) h)
  · exact Or.inr (hPeq _ Model.parrottF_le_titsD h)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
