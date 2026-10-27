module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56HomCount
public import CFSG.LocalAnalysis.EvenBN.Tits.S56PermFive

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup

variable {Γ : Type*} [Group Γ]

@[expose] def psi (E : Subgroup Γ) (t : Γ) (ht2 : t * t = 1)
    (hconj : ∀ m : Γ, t * (m * t * m⁻¹) ∈ E) :
    ↥(centralizer (E : Set Γ)) →* ↥E where
  toFun m := ⟨t * ((m : Γ) * t * (m : Γ)⁻¹), hconj m⟩
  map_one' := by
    apply Subtype.ext
    simp [ht2]
  map_mul' m n := by
    obtain ⟨a, ha_eq⟩ : ∃ a, a = t * ((n : Γ) * t * (n : Γ)⁻¹) := ⟨_, rfl⟩
    have haE : a ∈ E := ha_eq ▸ hconj n
    have hna : (n : Γ) * t * (n : Γ)⁻¹ = t * a := by
      rw [ha_eq, ← mul_assoc, ht2, one_mul]
    have hma : (m : Γ) * a * (m : Γ)⁻¹ = a := by
      have h := mem_centralizer_iff.1 m.2 _ haE
      calc (m : Γ) * a * (m : Γ)⁻¹ = ((m : Γ) * a) * (m : Γ)⁻¹ := rfl
        _ = (a * (m : Γ)) * (m : Γ)⁻¹ := by rw [← h]
        _ = a := by group
    apply Subtype.ext
    show t * (((m : Γ) * (n : Γ)) * t * ((m : Γ) * (n : Γ))⁻¹) =
      (t * ((m : Γ) * t * (m : Γ)⁻¹)) * (t * ((n : Γ) * t * (n : Γ)⁻¹))
    rw [← ha_eq]
    have key : t * (((m : Γ) * (n : Γ)) * t * ((m : Γ) * (n : Γ))⁻¹) =
        t * ((m : Γ) * ((n : Γ) * t * (n : Γ)⁻¹) * (m : Γ)⁻¹) := by group
    rw [key, hna]
    calc t * ((m : Γ) * (t * a) * (m : Γ)⁻¹)
        = t * ((m : Γ) * t * (m : Γ)⁻¹) * ((m : Γ) * a * (m : Γ)⁻¹) := by group
      _ = t * ((m : Γ) * t * (m : Γ)⁻¹) * a := by rw [hma]

@[expose] def CA (E : Subgroup Γ) (t : Γ) : Subgroup Γ :=
  centralizer (E : Set Γ) ⊓ centralizer ({t} : Set Γ)

theorem mem_ker_psi {E : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (hconj : ∀ m : Γ, t * (m * t * m⁻¹) ∈ E) (m : ↥(centralizer (E : Set Γ))) :
    m ∈ (psi E t ht2 hconj).ker ↔ (m : Γ) ∈ centralizer ({t} : Set Γ) := by
  rw [MonoidHom.mem_ker, mem_centralizer_singleton_iff]
  have h1 : psi E t ht2 hconj m = 1 ↔ t * ((m : Γ) * t * (m : Γ)⁻¹) = 1 := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [h1]
  constructor
  · intro h
    have h2 : (m : Γ) * t * (m : Γ)⁻¹ = t := by
      have : (m : Γ) * t * (m : Γ)⁻¹ = t⁻¹ := by
        rw [eq_comm, inv_eq_iff_mul_eq_one]
        exact h
      rw [this, inv_eq_of_mul_eq_one_right ht2]
    calc (m : Γ) * t = (m : Γ) * t * (m : Γ)⁻¹ * (m : Γ) := by group
      _ = t * (m : Γ) := by rw [h2]
  · intro h
    have h2 : (m : Γ) * t * (m : Γ)⁻¹ = t := by
      calc (m : Γ) * t * (m : Γ)⁻¹ = (t * (m : Γ)) * (m : Γ)⁻¹ := by rw [h]
        _ = t := by group
    rw [h2, ht2]

theorem card_ker_psi [Finite Γ] {E : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (hconj : ∀ m : Γ, t * (m * t * m⁻¹) ∈ E) :
    Nat.card (psi E t ht2 hconj).ker = Nat.card (CA E t) := by
  have hle : CA E t ≤ centralizer (E : Set Γ) := inf_le_left
  have hker : (psi E t ht2 hconj).ker = (CA E t).subgroupOf (centralizer (E : Set Γ)) := by
    ext m
    rw [mem_ker_psi ht2 hconj, mem_subgroupOf]
    constructor
    · intro h
      exact ⟨m.2, h⟩
    · intro h
      exact h.2
  rw [hker]
  exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv

theorem card_centralizer_le [Finite Γ] {E : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (hconj : ∀ m : Γ, t * (m * t * m⁻¹) ∈ E) :
    Nat.card (centralizer (E : Set Γ)) ≤ Nat.card (CA E t) * Nat.card E := by
  have h := Subgroup.card_ker_mul_card_range (psi E t ht2 hconj)
  rw [card_ker_psi ht2 hconj] at h
  rw [← h]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

theorem exists_conj_of_card_eq [Finite Γ] {E : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (hconj : ∀ m : Γ, t * (m * t * m⁻¹) ∈ E)
    (hcard : Nat.card (centralizer (E : Set Γ)) = Nat.card (CA E t) * Nat.card E) :
    ∀ e ∈ E, ∃ m ∈ centralizer (E : Set Γ), m * t * m⁻¹ = t * e := by
  have h := Subgroup.card_ker_mul_card_range (psi E t ht2 hconj)
  rw [card_ker_psi ht2 hconj, hcard] at h
  have hpos : 0 < Nat.card (CA E t) := Nat.card_pos
  have hrange : Nat.card (psi E t ht2 hconj).range = Nat.card E :=
    Nat.eq_of_mul_eq_mul_left hpos h
  have htop : (psi E t ht2 hconj).range = ⊤ := Subgroup.eq_top_of_card_eq _ hrange
  intro e he
  have hmem : (⟨e, he⟩ : ↥E) ∈ (psi E t ht2 hconj).range := htop ▸ mem_top _
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, m.2, ?_⟩
  have h2 : t * ((m : Γ) * t * (m : Γ)⁻¹) = e := congrArg Subtype.val hm
  calc (m : Γ) * t * (m : Γ)⁻¹ = t * (t * ((m : Γ) * t * (m : Γ)⁻¹)) := by
        rw [← mul_assoc, ht2, one_mul]
    _ = t * e := by rw [h2]

theorem conj_eq_of_mem_zpowers {z : Γ} (hzc : ∀ g : Γ, g * z = z * g) {c : Γ}
    (hc : c ∈ zpowers z) (g : Γ) : g * c * g⁻¹ = c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have h : Commute g z := hzc g
  rw [(h.zpow_right k).eq]
  group

@[expose] def K1 (E : Subgroup Γ) [E.Normal] (z : Γ) (hzc : ∀ g : Γ, g * z = z * g) : Subgroup Γ where
  carrier := {m | ∀ e ∈ E, m * e * m⁻¹ * e⁻¹ ∈ zpowers z}
  one_mem' := fun e _ => by simp
  mul_mem' := by
    intro m n hm hn e he
    have h1 := hn e he
    have h2 := hm e he
    have key : m * n * e * (m * n)⁻¹ * e⁻¹ =
        (m * (n * e * n⁻¹ * e⁻¹) * m⁻¹) * (m * e * m⁻¹ * e⁻¹) := by group
    rw [key, conj_eq_of_mem_zpowers hzc h1 m]
    exact mul_mem h1 h2
  inv_mem' := by
    intro m hm e he
    have he' : m⁻¹ * e * m ∈ E := by
      have := (inferInstance : E.Normal).conj_mem e he m⁻¹
      simpa using this
    have h := hm _ he'
    have key : m⁻¹ * e * m⁻¹⁻¹ * e⁻¹ = (m * (m⁻¹ * e * m) * m⁻¹ * (m⁻¹ * e * m)⁻¹)⁻¹ := by
      group
    rw [key]
    exact inv_mem h

theorem mem_K1 {E : Subgroup Γ} [E.Normal] {z : Γ} {hzc : ∀ g : Γ, g * z = z * g} {m : Γ} :
    m ∈ K1 E z hzc ↔ ∀ e ∈ E, m * e * m⁻¹ * e⁻¹ ∈ zpowers z := Iff.rfl

theorem centralizer_le_K1 {E : Subgroup Γ} [E.Normal] {z : Γ} (hzc : ∀ g : Γ, g * z = z * g) :
    centralizer (E : Set Γ) ≤ K1 E z hzc := by
  intro m hm e he
  have h := mem_centralizer_iff.1 hm e he
  have : m * e * m⁻¹ * e⁻¹ = 1 := by
    calc m * e * m⁻¹ * e⁻¹ = (e * m) * m⁻¹ * e⁻¹ := by rw [h]
      _ = 1 := by group
  rw [this]
  exact one_mem _

instance K1_normal (E : Subgroup Γ) [E.Normal] (z : Γ) (hzc : ∀ g : Γ, g * z = z * g) :
    (K1 E z hzc).Normal where
  conj_mem m hm g e he := by
    have he' : g⁻¹ * e * g ∈ E := by
      have := (inferInstance : E.Normal).conj_mem e he g⁻¹
      simpa using this
    have h := hm _ he'
    have key : g * m * g⁻¹ * e * (g * m * g⁻¹)⁻¹ * e⁻¹ =
        g * (m * (g⁻¹ * e * g) * m⁻¹ * (g⁻¹ * e * g)⁻¹) * g⁻¹ := by group
    rw [key, conj_eq_of_mem_zpowers hzc h g]
    exact h

theorem card_K1_le [Finite Γ] (E : Subgroup Γ) [E.Normal] (z : Γ)
    (hzc : ∀ g : Γ, g * z = z * g) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1) (hzE : z ∈ E) (hz1 : z ≠ 1) :
    Nat.card (K1 E z hzc) ≤ Nat.card (centralizer (E : Set Γ)) * (Nat.card E / 2) := by
  let φ : ↥(K1 E z hzc) →* MulAut ↥E := (MulAut.conjNormal : Γ →* MulAut ↥E).comp (K1 E z hzc).subtype
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hker : φ.ker = (centralizer (E : Set Γ)).subgroupOf (K1 E z hzc) := by
    ext m
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro h e he
      have := congrArg (fun α : MulAut ↥E => (α ⟨e, he⟩ : Γ)) h
      simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, coe_subtype,
        MulAut.one_apply] at this
      calc e * (m : Γ) = ((m : Γ) * e * (m : Γ)⁻¹) * (m : Γ) := by rw [this]
        _ = (m : Γ) * e := by group
    · intro h
      ext e
      simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, coe_subtype, MulAut.one_apply]
      have := h e e.2
      calc (m : Γ) * e * (m : Γ)⁻¹ = (e * (m : Γ)) * (m : Γ)⁻¹ := by rw [this]
        _ = e := by group
  have hkc : Nat.card φ.ker = Nat.card (centralizer (E : Set Γ)) := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_K1 hzc)).toEquiv
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  have hrange : Nat.card φ.range ≤ Nat.card ↥E / 2 := by
    apply card_le_of_trivial_on_quotient (E := ↥E)
      (fun e => Subtype.ext (hE2 e e.2)) ⟨z, hzE⟩ (fun h => hz1 (congrArg Subtype.val h)) φ.range
    rintro _ ⟨m, rfl⟩ e
    have h := m.2 e e.2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    apply Subtype.ext
    simp only [φ, MonoidHom.comp_apply, MulAut.conjNormal_apply, coe_subtype]
    simpa using hk
  rw [← hcard, hkc]
  exact Nat.mul_le_mul_left _ hrange

@[expose] def KOrb (K : Subgroup Γ) (e : Γ) : Set Γ := {y | ∃ k ∈ K, k * e * k⁻¹ = y}

theorem mem_KOrb_self {K : Subgroup Γ} (e : Γ) : e ∈ KOrb K e := ⟨1, one_mem _, by simp⟩

theorem KOrb_eq_of_mem {K : Subgroup Γ} {e y : Γ} (hy : y ∈ KOrb K e) : KOrb K y = KOrb K e := by
  obtain ⟨k₀, hk₀, rfl⟩ := hy
  ext w
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * k₀, mul_mem hk hk₀, by group⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * k₀⁻¹, mul_mem hk (inv_mem hk₀), by group⟩

theorem card_eq_ncard_KOrb_mul [Finite Γ] (K : Subgroup Γ) (x : Γ) :
    Nat.card K = (KOrb K x).ncard * Nat.card (K ⊓ centralizer ({x} : Set Γ) : Subgroup Γ) := by
  let _ : MulAction K Γ := MulAction.compHom Γ ((MulAut.conj : Γ →* MulAut Γ).comp K.subtype)
  have hsmul : ∀ (k : K) (y : Γ), k • y = (k : Γ) * y * (k : Γ)⁻¹ := fun k y => by
    change (MulAut.conj (k : Γ)) • y = _
    rw [MulAut.smul_def, MulAut.conj_apply]
  have horb : (MulAction.orbit K x : Set Γ) = KOrb K x := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, (hsmul k x).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, hsmul _ _⟩
  have e : MulAction.stabilizer K x ≃ (K ⊓ centralizer ({x} : Set Γ) : Subgroup Γ) :=
    { toFun := fun k => ⟨k.1.1, mem_inf.2 ⟨k.1.2, mem_centralizer_singleton_iff.2 (by
        have h : (k.1 : Γ) * x * (k.1 : Γ)⁻¹ = x := (hsmul k.1 x).symm.trans k.2
        calc (k.1 : Γ) * x = (k.1 : Γ) * x * (k.1 : Γ)⁻¹ * k.1 := by group
          _ = x * k.1 := by rw [h])⟩⟩
      invFun := fun k => ⟨⟨k.1, (mem_inf.1 k.2).1⟩, by
        change (⟨k.1, (mem_inf.1 k.2).1⟩ : K) • x = x
        rw [hsmul]
        have h := mem_centralizer_singleton_iff.1 (mem_inf.1 k.2).2
        change (k : Γ) * x * (k : Γ)⁻¹ = x
        rw [h, mul_inv_cancel_right]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : Nat.card (MulAction.orbit K x) * Nat.card (MulAction.stabilizer K x) = Nat.card K := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
    exact (MulAction.stabilizer K x).card_mul_index
  rw [← h1, Nat.card_congr e, ← horb, Nat.card_coe_set_eq]

theorem orbit_inv_of_not_three [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) {K : Subgroup Γ}
    {X Y : Set Γ} {e : Γ} (hXe : X = KOrb K e) (hY : ∃ e', Y = KOrb K e')
    (hdisj : Disjoint X Y) (h3XY : 3 ∣ X.ncard + Y.ncard)
    (hsub : ∀ y ∈ KOrb (⊤ : Subgroup Γ) e, y ∈ X ∨ y ∈ Y) :
    ∀ m : Γ, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
  obtain ⟨e', hYe'⟩ := hY
  have hXO : X ⊆ KOrb (⊤ : Subgroup Γ) e := by
    rw [hXe]
    rintro _ ⟨k, -, rfl⟩
    exact ⟨k, mem_top _, rfl⟩
  have hnoY : ∀ y ∈ KOrb (⊤ : Subgroup Γ) e, y ∉ Y := by
    intro y hy hyY
    have hYO : Y ⊆ KOrb (⊤ : Subgroup Γ) e := by
      have hYy : KOrb K y = Y := by
        rw [hYe'] at hyY ⊢
        exact KOrb_eq_of_mem hyY
      intro w hw
      rw [← hYy] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      obtain ⟨m, -, rfl⟩ := hy
      exact ⟨k * m, mem_top _, by group⟩
    have hO : KOrb (⊤ : Subgroup Γ) e = X ∪ Y := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hsub y hy
      · exact Set.union_subset hXO hYO
    have hcard : (KOrb (⊤ : Subgroup Γ) e).ncard = X.ncard + Y.ncard := by
      rw [hO]
      exact Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have hdvd : (KOrb (⊤ : Subgroup Γ) e).ncard ∣ Nat.card Γ := by
      have := card_eq_ncard_KOrb_mul (⊤ : Subgroup Γ) e
      rw [Subgroup.card_top] at this
      exact Dvd.intro _ this.symm
    rw [hcard] at hdvd
    exact h3 (h3XY.trans hdvd)
  intro m x hx
  rw [hXe] at hx ⊢
  obtain ⟨k, hk, rfl⟩ := hx
  have hmem : m * (k * e * k⁻¹) * m⁻¹ ∈ KOrb (⊤ : Subgroup Γ) e := ⟨m * k, mem_top _, by group⟩
  rcases hsub _ hmem with h | h
  · rw [hXe] at h
    exact h
  · exact absurd h (hnoY _ hmem)

structure SqueezeData (Γ : Type*) [Group Γ] where
  E : Subgroup Γ
  z : Γ
  t : Γ
  Lg : Set Γ
  Sg : Set Γ
  normal : E.Normal
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  sq : ∀ a ∈ E, a * a = 1
  card_E : Nat.card E = 32
  z_mem : z ∈ E
  z_ne : z ≠ 1
  z_central : ∀ g : Γ, g * z = z * g
  t_sq : t * t = 1
  t_conj : ∀ m : Γ, t * (m * t * m⁻¹) ∈ E
  Lg_sub : Lg ⊆ E
  Sg_sub : Sg ⊆ E
  cover : ∀ e ∈ E, e = 1 ∨ e = z ∨ e ∈ Lg ∨ e ∈ Sg
  disj : Disjoint Lg Sg
  one_nmem_Lg : (1 : Γ) ∉ Lg
  z_nmem_Lg : z ∉ Lg
  one_nmem_Sg : (1 : Γ) ∉ Sg
  z_nmem_Sg : z ∉ Sg
  Lg_orbit : ∃ e, Lg = KOrb (centralizer ({t} : Set Γ)) e
  Sg_orbit : ∃ e, Sg = KOrb (centralizer ({t} : Set Γ)) e
  Lg_card : Lg.ncard = 10
  Sg_card : Sg.ncard = 20
  Lg_z : ∀ e ∈ Lg, e * z ∈ Lg

namespace SqueezeData

variable (S : SqueezeData Γ)

theorem conj_mem_E {m e : Γ} (he : e ∈ S.E) : m * e * m⁻¹ ∈ S.E :=
  S.normal.conj_mem e he m

theorem orbit_cover {e : Γ} (he : e ∈ S.E) (h1 : e ≠ 1) (hz : e ≠ S.z) :
    ∀ y ∈ KOrb (⊤ : Subgroup Γ) e, y ∈ S.Lg ∨ y ∈ S.Sg := by
  rintro _ ⟨m, -, rfl⟩
  have hyE : m * e * m⁻¹ ∈ S.E := S.conj_mem_E he
  have hy1 : m * e * m⁻¹ ≠ 1 := by
    intro h
    apply h1
    have : e = m⁻¹ * (m * e * m⁻¹) * m := by group
    rw [this, h]
    group
  have hyz : m * e * m⁻¹ ≠ S.z := by
    intro h
    apply hz
    have h2 : e = m⁻¹ * S.z * m := by
      rw [← h]
      group
    rw [h2, S.z_central m⁻¹]
    group
  rcases S.cover _ hyE with h | h | h | h
  · exact absurd h hy1
  · exact absurd h hyz
  · exact Or.inl h
  · exact Or.inr h

theorem Lg_inv [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) : ∀ m : Γ, ∀ e ∈ S.Lg, m * e * m⁻¹ ∈ S.Lg := by
  obtain ⟨e₀, he₀⟩ := S.Lg_orbit
  have he₀L : e₀ ∈ S.Lg := he₀ ▸ mem_KOrb_self e₀
  refine orbit_inv_of_not_three h3 he₀ S.Sg_orbit S.disj ?_ ?_
  · rw [S.Lg_card, S.Sg_card]
    norm_num
  · exact S.orbit_cover (S.Lg_sub he₀L) (fun h => S.one_nmem_Lg (h ▸ he₀L))
      (fun h => S.z_nmem_Lg (h ▸ he₀L))

theorem closure_Lg_inv [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) (m : Γ) {x : Γ}
    (hx : x ∈ Subgroup.closure S.Lg) : m * x * m⁻¹ ∈ Subgroup.closure S.Lg := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (S.Lg_inv h3 m y hy)
  | one => simp
  | mul y w _ _ hy hw =>
    have : m * (y * w) * m⁻¹ = (m * y * m⁻¹) * (m * w * m⁻¹) := by group
    rw [this]
    exact mul_mem hy hw
  | inv y _ hy =>
    have : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hy

theorem closure_Lg_eq [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) :
    Subgroup.closure S.Lg = S.E := by
  have hle : Subgroup.closure S.Lg ≤ S.E := (Subgroup.closure_le _).2 S.Lg_sub
  obtain ⟨e₀, he₀⟩ := S.Lg_orbit
  have he₀L : e₀ ∈ S.Lg := he₀ ▸ mem_KOrb_self e₀
  have hzH : S.z ∈ Subgroup.closure S.Lg := by
    have h1 : e₀ ∈ Subgroup.closure S.Lg := Subgroup.subset_closure he₀L
    have h2 : e₀ * S.z ∈ Subgroup.closure S.Lg := Subgroup.subset_closure (S.Lg_z e₀ he₀L)
    have h3' := mul_mem h1 h2
    have hsq := S.sq e₀ (S.Lg_sub he₀L)
    have : e₀ * (e₀ * S.z) = S.z := by rw [← mul_assoc, hsq, one_mul]
    rwa [this] at h3'
  by_cases hSg : ∃ y ∈ S.Sg, y ∈ Subgroup.closure S.Lg
  · obtain ⟨y, hyS, hyH⟩ := hSg
    obtain ⟨e₁, he₁⟩ := S.Sg_orbit
    have hSgy : KOrb (centralizer ({S.t} : Set Γ)) y = S.Sg := by
      rw [he₁] at hyS ⊢
      exact KOrb_eq_of_mem hyS
    apply le_antisymm hle
    intro e he
    rcases S.cover e he with h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hzH
    · exact Subgroup.subset_closure h
    · rw [← hSgy] at h
      obtain ⟨k, -, rfl⟩ := h
      exact S.closure_Lg_inv h3 k hyH
  · push Not at hSg
    exfalso
    have hset : ((Subgroup.closure S.Lg : Subgroup Γ) : Set Γ) = ({1, S.z} : Set Γ) ∪ S.Lg := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases S.cover x (hle hx) with h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact absurd hx (hSg x h)
      · rintro x (hx | hx)
        · rcases hx with rfl | rfl
          · exact one_mem _
          · exact hzH
        · exact Subgroup.subset_closure hx
    have hdisj : Disjoint ({1, S.z} : Set Γ) S.Lg := by
      rw [Set.disjoint_left]
      rintro x (rfl | rfl)
      · exact S.one_nmem_Lg
      · exact S.z_nmem_Lg
    have hcard : Nat.card (Subgroup.closure S.Lg) = 12 := by
      have h1 : Nat.card (Subgroup.closure S.Lg) =
          ((Subgroup.closure S.Lg : Subgroup Γ) : Set Γ).ncard := Nat.card_coe_set_eq _
      rw [h1, hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), S.Lg_card,
        Set.ncard_pair (Ne.symm S.z_ne)]
    have hdvd : Nat.card (Subgroup.closure S.Lg) ∣ Nat.card S.E :=
      Subgroup.card_dvd_of_le hle
    rw [hcard, S.card_E] at hdvd
    norm_num at hdvd

instance instNormalE : S.E.Normal := S.normal

instance instCommE : IsMulCommutative ↥S.E := ⟨⟨fun a b => Subtype.ext (S.comm a a.2 b b.2)⟩⟩

@[expose] def Z : Subgroup ↥S.E := zpowers ⟨S.z, S.z_mem⟩

theorem conjE_z (m : Γ) :
    (MulAut.conjNormal m : MulAut ↥S.E) ⟨S.z, S.z_mem⟩ = ⟨S.z, S.z_mem⟩ := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  calc m * S.z * m⁻¹ = (S.z * m) * m⁻¹ := by rw [S.z_central m]
    _ = S.z := by group

theorem map_Z (m : Γ) :
    S.Z.map ((MulAut.conjNormal m : MulAut ↥S.E) : ↥S.E →* ↥S.E) = S.Z := by
  unfold Z
  rw [MonoidHom.map_zpowers]
  congr 1
  exact S.conjE_z m

@[expose] def act (m : Γ) : (↥S.E ⧸ S.Z) ≃* (↥S.E ⧸ S.Z) :=
  QuotientGroup.congr S.Z S.Z (MulAut.conjNormal m) (S.map_Z m)

theorem act_mk (m : Γ) (e : ↥S.E) :
    S.act m (QuotientGroup.mk e) = QuotientGroup.mk (MulAut.conjNormal m e) := rfl

@[expose] def actHom : Γ →* MulAut (↥S.E ⧸ S.Z) where
  toFun := S.act
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp [act_mk]
  map_mul' m n := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp [act_mk]

theorem actHom_mk (m : Γ) (e : ↥S.E) :
    S.actHom m (QuotientGroup.mk e) = QuotientGroup.mk (MulAut.conjNormal m e) := rfl

@[expose] def Sig : Set (↥S.E ⧸ S.Z) :=
  {x | ∃ e : ↥S.E, (e : Γ) ∈ S.Lg ∧ (QuotientGroup.mk e : ↥S.E ⧸ S.Z) = x}

theorem actHom_mem_Sig [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) (m : Γ) {x : ↥S.E ⧸ S.Z}
    (hx : x ∈ S.Sig) : S.actHom m x ∈ S.Sig := by
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨MulAut.conjNormal m e, ?_, S.actHom_mk m e⟩
  rw [MulAut.conjNormal_apply]
  exact S.Lg_inv h3 m _ he

theorem sig_iff [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) (m : Γ) (x : ↥S.E ⧸ S.Z) :
    (MulAut.toPerm _ (S.actHom m)) x ∈ S.Sig ↔ x ∈ S.Sig := by
  constructor
  · intro hx
    have h := S.actHom_mem_Sig h3 m⁻¹ hx
    have e : S.actHom m⁻¹ ((MulAut.toPerm _ (S.actHom m)) x) = x := by
      change (S.actHom m⁻¹) ((S.actHom m) x) = x
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [e] at h
  · intro hx
    exact S.actHom_mem_Sig h3 m hx

@[expose] noncomputable def sigHom [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) : Γ →* Equiv.Perm ↥S.Sig where
  toFun m := (MulAut.toPerm _ (S.actHom m)).subtypePerm (S.sig_iff h3 m)
  map_one' := by
    ext x
    simp
  map_mul' m n := by
    ext x
    show (MulAut.toPerm _ (S.actHom (m * n))) x.1 =
      (MulAut.toPerm _ (S.actHom m)) ((MulAut.toPerm _ (S.actHom n)) x.1)
    rw [map_mul, map_mul]
    rfl

theorem mem_Z_iff (x : ↥S.E) : x ∈ S.Z ↔ (x : Γ) ∈ zpowers S.z := by
  unfold Z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem eq_one_or_z_of_mem_zpowers {x : Γ} (hx : x ∈ zpowers S.z) : x = 1 ∨ x = S.z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hsq : S.z * S.z = 1 := S.sq _ S.z_mem
  have h2 : S.z ^ (2 : ℤ) = 1 := by rw [zpow_two, hsq]
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem mk_eq_mk_iff (a b : ↥S.E) :
    (QuotientGroup.mk a : ↥S.E ⧸ S.Z) = QuotientGroup.mk b ↔
      (a : Γ)⁻¹ * (b : Γ) ∈ zpowers S.z := by
  rw [QuotientGroup.eq, S.mem_Z_iff]
  rfl

theorem mem_ker_sigHom [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) (m : Γ) :
    m ∈ (S.sigHom h3).ker ↔
      ∀ e : ↥S.E, (e : Γ) ∈ S.Lg → S.actHom m (QuotientGroup.mk e) = QuotientGroup.mk e := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h e he
    have := congrArg (fun f : Equiv.Perm ↥S.Sig =>
      ((f ⟨QuotientGroup.mk e, e, he, rfl⟩ : ↥S.Sig) : ↥S.E ⧸ S.Z)) h
    exact this
  · intro h
    ext x
    obtain ⟨_, e, he, rfl⟩ := x
    exact h e he

theorem ker_sigHom_eq_K1 [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) :
    (S.sigHom h3).ker = K1 S.E S.z S.z_central := by
  ext m
  rw [S.mem_ker_sigHom h3, mem_K1]
  constructor
  · intro h
    have hLg : ∀ a ∈ S.Lg, m * a * m⁻¹ * a⁻¹ ∈ zpowers S.z := by
      intro a ha
      have h1 := h ⟨a, S.Lg_sub ha⟩ ha
      rw [S.actHom_mk, S.mk_eq_mk_iff] at h1
      have h2 : (m * a * m⁻¹)⁻¹ * a ∈ zpowers S.z := h1
      have h2' : a⁻¹ * (m * a * m⁻¹) ∈ zpowers S.z := by
        have := inv_mem h2
        simpa using this
      have e3 : m * a * m⁻¹ * a⁻¹ = a * (a⁻¹ * (m * a * m⁻¹)) * a⁻¹ := by group
      rw [e3, conj_eq_of_mem_zpowers S.z_central h2' a]
      exact h2'
    intro e he
    rw [← S.closure_Lg_eq h3] at he
    induction he using Subgroup.closure_induction with
    | mem y hy => exact hLg y hy
    | one => simp
    | mul y w _ _ hy hw =>
      have key : m * (y * w) * m⁻¹ * (y * w)⁻¹ =
          (m * y * m⁻¹ * y⁻¹) * (y * (m * w * m⁻¹ * w⁻¹) * y⁻¹) := by group
      rw [key, conj_eq_of_mem_zpowers S.z_central hw y]
      exact mul_mem hy hw
    | inv y _ hy =>
      have key : m * y⁻¹ * m⁻¹ * y⁻¹⁻¹ = y⁻¹ * (m * y * m⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
      rw [key, conj_eq_of_mem_zpowers S.z_central (inv_mem hy) y⁻¹]
      exact inv_mem hy
  · intro h e he
    rw [S.actHom_mk, S.mk_eq_mk_iff]
    obtain ⟨a, haE⟩ := e
    have h1 := h a (S.Lg_sub he)
    have e3 : (m * a * m⁻¹)⁻¹ * a = (a⁻¹ * (m * a * m⁻¹ * a⁻¹) * a⁻¹⁻¹)⁻¹ := by group
    show (m * a * m⁻¹)⁻¹ * a ∈ zpowers S.z
    rw [e3, conj_eq_of_mem_zpowers S.z_central h1 a⁻¹]
    exact inv_mem h1

theorem ncard_Sig [Finite Γ] : S.Sig.ncard = 5 := by
  classical
  have hLfin : S.Lg.Finite := Set.toFinite _
  let φ : Γ → ↥S.E ⧸ S.Z := fun γ => if h : γ ∈ S.E then QuotientGroup.mk ⟨γ, h⟩ else 1
  have hφ : ∀ γ (h : γ ∈ S.E), φ γ = QuotientGroup.mk ⟨γ, h⟩ := fun γ h => dif_pos h
  have hSig : S.Sig = φ '' S.Lg := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, hφ e e.2⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨⟨γ, S.Lg_sub hγ⟩, hγ, (hφ γ _).symm⟩
  have hfib : ∀ b ∈ hLfin.toFinset.image φ,
      (hLfin.toFinset.filter (fun γ => φ γ = b)).card = 2 := by
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hb
    have heL : e ∈ S.Lg := hLfin.mem_toFinset.1 he
    have heE := S.Lg_sub heL
    have hsq : S.z * S.z = 1 := S.sq _ S.z_mem
    have hset : hLfin.toFinset.filter (fun γ => φ γ = φ e) = {e, e * S.z} := by
      ext γ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hγ, hφγ⟩
        have hγE := S.Lg_sub hγ
        rw [hφ γ hγE, hφ e heE, S.mk_eq_mk_iff] at hφγ
        rcases S.eq_one_or_z_of_mem_zpowers hφγ with h | h
        · left
          have h' : γ⁻¹ * e = 1 := h
          exact inv_mul_eq_one.1 h'
        · right
          have h' : γ⁻¹ * e = S.z := h
          calc γ = e * (γ⁻¹ * e)⁻¹ := by group
            _ = e * S.z := by rw [h', inv_eq_of_mul_eq_one_right hsq]
      · rintro (h | h)
        · rw [h]
          exact ⟨heL, rfl⟩
        · rw [h]
          refine ⟨S.Lg_z e heL, ?_⟩
          have hmem : e * S.z ∈ S.E := mul_mem heE S.z_mem
          rw [hφ _ hmem, hφ e heE, S.mk_eq_mk_iff]
          show (e * S.z)⁻¹ * e ∈ zpowers S.z
          have : (e * S.z)⁻¹ * e = S.z := by
            rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, inv_eq_of_mul_eq_one_right hsq]
          rw [this]
          exact mem_zpowers _
    rw [hset]
    apply Finset.card_pair
    intro h
    exact S.z_ne (by simpa using h)
  have hsum := Finset.card_eq_sum_card_image φ hLfin.toFinset
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
  have h10 : hLfin.toFinset.card = 10 := by
    rw [← Set.ncard_eq_toFinset_card S.Lg hLfin, S.Lg_card]
  have himg : (hLfin.toFinset.image φ).card = 5 := by omega
  have hcoe : S.Sig = ↑(hLfin.toFinset.image φ) := by
    rw [hSig, Finset.coe_image, Set.Finite.coe_toFinset]
  rw [hcoe, Set.ncard_coe_finset, himg]

theorem index_K1 [Finite Γ] (h3 : ¬ 3 ∣ Nat.card Γ) :
    (K1 S.E S.z S.z_central).index ≤ 20 ∧
      ((K1 S.E S.z S.z_central).index = 20 → CFSG.pCore 2 Γ ≤ K1 S.E S.z S.z_central) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e5 : ↥S.Sig ≃ Fin 5 :=
    Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq]; exact S.ncard_Sig)
  let ι : Γ →* Equiv.Perm (Fin 5) :=
    (e5.permCongrHom : Equiv.Perm ↥S.Sig ≃* Equiv.Perm (Fin 5)).toMonoidHom.comp (S.sigHom h3)
  have hker : ι.ker = K1 S.E S.z S.z_central := by
    rw [← S.ker_sigHom_eq_K1 h3]
    ext m
    simp only [MonoidHom.mem_ker, ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact MulEquiv.map_eq_one_iff _
  have hcard := Subgroup.card_ker_mul_card_range ι
  have hidx := Subgroup.card_mul_index (K1 S.E S.z S.z_central)
  rw [hker] at hcard
  have hrange : Nat.card ι.range = (K1 S.E S.z S.z_central).index := by
    have hpos : 0 < Nat.card (K1 S.E S.z S.z_central) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (hcard.trans hidx.symm)
  have h3P : ¬ 3 ∣ Nat.card ι.range := fun h => h3 (h.trans (Dvd.intro_left _ hcard))
  obtain ⟨hle, hcore⟩ := card_le_twenty_of_embeds_perm_five (P := ↥ι.range) ι.range.subtype
    Subtype.val_injective h3P
  refine ⟨hrange ▸ hle, fun hidx20 => ?_⟩
  have hP20 : Nat.card ι.range = 20 := hrange.trans hidx20
  have hbot := hcore hP20
  intro r hr
  have hmap : (CFSG.pCore 2 Γ).map ι.rangeRestrict ≤ CFSG.pCore 2 ↥ι.range := by
    apply le_sSup
    refine ⟨?_, ?_⟩
    · exact Subgroup.Normal.map CFSG.pCore_normal ι.rangeRestrict ι.rangeRestrict_surjective
    · exact (CFSG.pCore_isPGroup).map _
  have h1 : ι.rangeRestrict r ∈ CFSG.pCore 2 ↥ι.range := hmap (mem_map_of_mem _ hr)
  rw [hbot, Subgroup.mem_bot] at h1
  rw [← hker, MonoidHom.mem_ker]
  exact congrArg Subtype.val h1

end SqueezeData

theorem squeeze [Finite Γ] (S : SqueezeData Γ) (h3 : ¬ 3 ∣ Nat.card Γ)
    (hcard : 10240 * Nat.card (CA S.E S.t) ≤ Nat.card Γ) :
    Nat.card Γ = 10240 * Nat.card (CA S.E S.t) ∧
    Nat.card (centralizer (S.E : Set Γ)) = 32 * Nat.card (CA S.E S.t) ∧
    (∀ e ∈ S.E, ∃ m ∈ centralizer (S.E : Set Γ), m * S.t * m⁻¹ = S.t * e) ∧
    Nat.card (K1 S.E S.z S.z_central) = 512 * Nat.card (CA S.E S.t) ∧
    (K1 S.E S.z S.z_central).index = 20 ∧
    (IsPGroup 2 (CA S.E S.t) → CFSG.pCore 2 Γ = K1 S.E S.z S.z_central) := by
  haveI := S.instNormalE
  obtain ⟨hidx_le, hcore⟩ := S.index_K1 h3
  have hK1 := card_K1_le S.E S.z S.z_central S.comm S.sq S.z_mem S.z_ne
  have hC := card_centralizer_le S.t_sq S.t_conj
  rw [S.card_E] at hK1 hC
  have hN := Subgroup.card_mul_index (K1 S.E S.z S.z_central)
  have hbpos : 0 < Nat.card (K1 S.E S.z S.z_central) := Nat.card_pos
  have hdpos : 0 < Nat.card (CA S.E S.t) := Nat.card_pos
  have hcpos : 0 < Nat.card (centralizer (S.E : Set Γ)) := Nat.card_pos
  set N := Nat.card Γ
  set a := (K1 S.E S.z S.z_central).index
  set b := Nat.card (K1 S.E S.z S.z_central)
  set c := Nat.card (centralizer (S.E : Set Γ))
  set d := Nat.card (CA S.E S.t)
  have h16 : (32 : ℕ) / 2 = 16 := by norm_num
  rw [h16] at hK1
  have hab : b * a ≤ b * 20 := Nat.mul_le_mul_left b hidx_le
  have ha20 : a = 20 := by
    have h1 : b * a = b * 20 := by
      apply le_antisymm hab
      omega
    exact Nat.eq_of_mul_eq_mul_left hbpos h1
  have hb : b = 16 * c := by omega
  have hc : c = 32 * d := by omega
  have hN' : N = 10240 * d := by omega
  have hCE : c = d * 32 := by omega
  refine ⟨hN', hc, exists_conj_of_card_eq S.t_sq S.t_conj (by rw [S.card_E]; exact hCE),
    by omega, ha20, fun hCA => ?_⟩
  have hCAcard := (IsPGroup.iff_card (p := 2)).1 hCA
  obtain ⟨k, hk⟩ := hCAcard
  have hK1p : IsPGroup 2 (K1 S.E S.z S.z_central) := by
    apply IsPGroup.of_card (n := 9 + k)
    have hbd : b = 512 * d := by omega
    have hk' : d = 2 ^ k := hk
    change b = 2 ^ (9 + k)
    rw [hbd, hk', pow_add]
    norm_num
  apply le_antisymm
  · exact hcore ha20
  · exact le_sSup ⟨inferInstance, hK1p⟩

end CFSG.LocalAnalysis.EvenBN.Tits.S56
