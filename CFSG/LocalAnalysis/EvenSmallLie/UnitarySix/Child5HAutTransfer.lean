module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Transport

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut.ThetaSpec

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaSec3

variable {G : Type} [Group G] {L : Subgroup G} {t : G}
  {e : L ≃* T46} {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem conj_mem_L (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) {l : G} (hl : l ∈ L) :
    (x : G) * l * (x : G)⁻¹ ∈ L :=
  (mem_normalizer_iff.mp (hΘ.normalizer x) l).mp hl

theorem conj_mem (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) (y : T46) :
    Θ x * (y : Equiv.Perm (Fin 693)) * (Θ x)⁻¹ ∈ T46 := by
  have h := hΘ.conj x (e.symm y) ⟨(x : G) * (e.symm y : G) * (x : G)⁻¹,
    hΘ.conj_mem_L x (e.symm y).2⟩ rfl
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  exact (e _).2

theorem conj_iotaG (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) (y : T46) :
    (x : G) * iotaG e y * (x : G)⁻¹ = iotaG e ⟨Θ x * y * (Θ x)⁻¹, hΘ.conj_mem x y⟩ := by
  have h := hΘ.conj x (e.symm y) ⟨(x : G) * (e.symm y : G) * (x : G)⁻¹,
    hΘ.conj_mem_L x (e.symm y).2⟩ rfl
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (⟨Θ x * y * (Θ x)⁻¹, hΘ.conj_mem x y⟩ : T46) =
      e ⟨(x : G) * (e.symm y : G) * (x : G)⁻¹, hΘ.conj_mem_L x (e.symm y).2⟩ :=
    Subtype.ext h
  rw [h2]
  simp [iotaG]

theorem conj_iotaG_eq_iff (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) (y y' : T46) :
    (x : G) * iotaG e y * (x : G)⁻¹ = iotaG e y' ↔
      Θ x * (y : Equiv.Perm (Fin 693)) * (Θ x)⁻¹ = y' := by
  rw [hΘ.conj_iotaG x y]
  constructor
  · intro h
    have := iotaG_injective h
    exact congrArg Subtype.val this
  · intro h
    congr 1
    exact Subtype.ext h

theorem comm_iotaG_iff (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) (y : T46) :
    (x : G) * iotaG e y = iotaG e y * x ↔ Θ x * (y : Equiv.Perm (Fin 693)) = y * Θ x := by
  have key : ∀ {M : Type} [Group M] (a b : M), a * b = b * a ↔ a * b * a⁻¹ = b := by
    intro M _ a b
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h
      calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [h]
  have h1 := key (x : G) (iotaG e y)
  have h2 := key (Θ x) (y : Equiv.Perm (Fin 693))
  rw [h1, h2, hΘ.conj_iotaG_eq_iff]

theorem conj_mem_T46 (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G))
    {g : Equiv.Perm (Fin 693)} : g ∈ T46 ↔ Θ x * g * (Θ x)⁻¹ ∈ T46 :=
  mem_normalizer_iff.mp (hΘ.mem_autT x) g

theorem mem_normalizer_toG_iff (hΘ : ThetaSpec t e Θ) {X : Subgroup (Equiv.Perm (Fin 693))}
    (hX : X ≤ T46) (x : centralizer ({t} : Set G)) :
    (x : G) ∈ Subgroup.normalizer (toG e X : Set G) ↔
      Θ x ∈ Subgroup.normalizer (X : Set (Equiv.Perm (Fin 693))) := by
  constructor
  · intro hx
    rw [mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ T46
    · have h1 := mem_normalizer_iff.mp hx (iotaG e ⟨g, hg⟩)
      rw [hΘ.conj_iotaG x, iotaG_mem_toG, iotaG_mem_toG] at h1
      exact h1
    · have h1 : Θ x * g * (Θ x)⁻¹ ∉ T46 := fun h => hg ((hΘ.conj_mem_T46 x).mpr h)
      exact ⟨fun h => absurd (hX h) hg, fun h => absurd (hX h) h1⟩
  · intro hx
    rw [mem_normalizer_iff]
    intro w
    by_cases hw : w ∈ L
    · obtain ⟨y, rfl⟩ := exists_iotaG (e := e) hw
      rw [hΘ.conj_iotaG x, iotaG_mem_toG, iotaG_mem_toG]
      exact mem_normalizer_iff.mp hx y
    · have h1 : (x : G) * w * (x : G)⁻¹ ∉ L := fun h => hw (by
        have := hΘ.conj_mem_L x⁻¹ h
        simpa [mul_assoc] using this)
      exact ⟨fun h => absurd (toG_le_L X h) hw, fun h => absurd (toG_le_L X h) h1⟩

theorem mem_centralizer_toG_iff (hΘ : ThetaSpec t e Θ) {X : Subgroup (Equiv.Perm (Fin 693))}
    (hX : X ≤ T46) (x : centralizer ({t} : Set G)) :
    (x : G) ∈ centralizer (toG e X : Set G) ↔
      Θ x ∈ centralizer (X : Set (Equiv.Perm (Fin 693))) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx g hg
    have h1 := hx (iotaG e ⟨g, hX hg⟩) (iotaG_mem_toG.mpr hg)
    exact ((hΘ.comm_iotaG_iff x ⟨g, hX hg⟩).mp h1.symm).symm
  · intro hx w hw
    obtain ⟨y, hy, rfl⟩ := mem_toG.mp hw
    exact ((hΘ.comm_iotaG_iff x y).mpr (hx y hy).symm).symm

theorem t_mem_centralizer (hΘ : ThetaSpec t e Θ) : t ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have ht : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have h1 : Θ ⟨t, ht⟩ = 1 := (hΘ.eq_one_iff ⟨t, ht⟩).mpr (mem_zpowers t)
  have h2 := hΘ.conj ⟨t, ht⟩ ⟨l, hl⟩ ⟨t * l * t⁻¹, hΘ.conj_mem_L ⟨t, ht⟩ hl⟩ rfl
  rw [h1, one_mul, inv_one, mul_one] at h2
  have h3 : l = t * l * t⁻¹ := congrArg Subtype.val (e.injective (Subtype.ext h2))
  calc l * t = t * l * t⁻¹ * t := by rw [← h3]
    _ = t * l := by group

theorem L_le_centralizer (hΘ : ThetaSpec t e Θ) : L ≤ centralizer ({t} : Set G) :=
  fun l hl => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hΘ.t_mem_centralizer l hl)

theorem apply_iotaG (hΘ : ThetaSpec t e Θ) (y : T46) :
    Θ ⟨iotaG e y, hΘ.L_le_centralizer (iotaG_mem y)⟩ = y := by
  rw [hΘ.apply_of_mem _ (iotaG_mem y)]
  simp [iotaG]

theorem toG_sup_le (hΘ : ThetaSpec t e Θ) (X : Subgroup (Equiv.Perm (Fin 693))) :
    toG e X ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
  sup_le ((toG_le_L X).trans hΘ.L_le_centralizer)
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))

theorem mem_toG_sup_iff (hΘ : ThetaSpec t e Θ) {X : Subgroup (Equiv.Perm (Fin 693))}
    (hX : X ≤ T46) (x : centralizer ({t} : Set G)) :
    (x : G) ∈ toG e X ⊔ zpowers t ↔ Θ x ∈ X := by
  constructor
  · intro hx
    have hle : toG e X ⊔ zpowers t ≤ (X.comap Θ).map (centralizer ({t} : Set G)).subtype := by
      refine sup_le ?_ ?_
      · intro l hl
        obtain ⟨y, hy, rfl⟩ := mem_toG.mp hl
        refine ⟨⟨iotaG e y, hΘ.L_le_centralizer (iotaG_mem y)⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_comap, hΘ.apply_iotaG]
        exact hy
      · rw [zpowers_le]
        have ht : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
        refine ⟨⟨t, ht⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_comap, (hΘ.eq_one_iff ⟨t, ht⟩).mpr (mem_zpowers t)]
        exact one_mem _
    obtain ⟨x', hx', hxx'⟩ := hle hx
    have : x' = x := Subtype.ext hxx'
    rw [← this]
    exact hx'
  · intro hx
    set l : centralizer ({t} : Set G) :=
      ⟨iotaG e ⟨Θ x, hX hx⟩, hΘ.L_le_centralizer (iotaG_mem _)⟩ with hl_def
    have h1 : Θ l = Θ x := hΘ.apply_iotaG ⟨Θ x, hX hx⟩
    have h2 : Θ (l⁻¹ * x) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := (hΘ.eq_one_iff _).mp h2
    have h4 : (x : G) = (l : G) * ((l⁻¹ * x : centralizer ({t} : Set G)) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h4]
    exact mul_mem (mem_sup_left (iotaG_mem_toG.mpr hx)) (mem_sup_right h3)

theorem mem_L_sup_iff (hΘ : ThetaSpec t e Θ) (x : centralizer ({t} : Set G)) :
    (x : G) ∈ L ⊔ zpowers t ↔ Θ x ∈ T46 := by
  have h := hΘ.mem_toG_sup_iff (X := T46) le_rfl x
  rwa [toG_T46] at h

theorem toG_sup_inf_L (hΘ : ThetaSpec t e Θ) {X : Subgroup (Equiv.Perm (Fin 693))}
    (hX : X ≤ T46) : (toG e X ⊔ zpowers t) ⊓ L = toG e X := by
  ext w
  constructor
  · rintro ⟨hw, hwL⟩
    obtain ⟨y, rfl⟩ := exists_iotaG (e := e) hwL
    have h := (hΘ.mem_toG_sup_iff hX ⟨iotaG e y, hΘ.L_le_centralizer (iotaG_mem y)⟩).mp hw
    rw [hΘ.apply_iotaG] at h
    exact iotaG_mem_toG.mpr h
  · intro hw
    exact ⟨mem_sup_left hw, toG_le_L X hw⟩

theorem mem_normalizer_toG_sup_iff (hΘ : ThetaSpec t e Θ) {X : Subgroup (Equiv.Perm (Fin 693))}
    (hX : X ≤ T46) (x : centralizer ({t} : Set G)) :
    (x : G) ∈ Subgroup.normalizer ((toG e X ⊔ zpowers t : Subgroup G) : Set G) ↔
      Θ x ∈ Subgroup.normalizer (X : Set (Equiv.Perm (Fin 693))) := by
  constructor
  · intro hx
    rw [mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ T46
    · set l : centralizer ({t} : Set G) :=
        ⟨iotaG e ⟨g, hg⟩, hΘ.L_le_centralizer (iotaG_mem _)⟩ with hl_def
      have hl : Θ l = g := hΘ.apply_iotaG ⟨g, hg⟩
      have h1 := mem_normalizer_iff.mp hx (l : G)
      rw [hΘ.mem_toG_sup_iff hX l, hl] at h1
      have h2 := hΘ.mem_toG_sup_iff hX (x * l * x⁻¹)
      rw [map_mul, map_mul, map_inv, hl] at h2
      exact h1.trans h2
    · have h1 : Θ x * g * (Θ x)⁻¹ ∉ T46 := fun h => hg ((hΘ.conj_mem_T46 x).mpr h)
      exact ⟨fun h => absurd (hX h) hg, fun h => absurd (hX h) h1⟩
  · intro hx
    rw [mem_normalizer_iff]
    intro w
    by_cases hw : w ∈ centralizer ({t} : Set G)
    · have h1 : w ∈ toG e X ⊔ zpowers t ↔ Θ ⟨w, hw⟩ ∈ X := hΘ.mem_toG_sup_iff hX ⟨w, hw⟩
      have h2 : (x : G) * w * (x : G)⁻¹ ∈ toG e X ⊔ zpowers t ↔
          Θ x * Θ ⟨w, hw⟩ * (Θ x)⁻¹ ∈ X := by
        have h := hΘ.mem_toG_sup_iff hX (x * ⟨w, hw⟩ * x⁻¹)
        rw [map_mul, map_mul, map_inv] at h
        exact h
      rw [h1, h2]
      exact mem_normalizer_iff.mp hx _
    · have h1 : (x : G) * w * (x : G)⁻¹ ∉ centralizer ({t} : Set G) := fun h => hw (by
        have := mul_mem (mul_mem (inv_mem x.2) h) x.2
        simpa [mul_assoc] using this)
      exact ⟨fun h => absurd (hΘ.toG_sup_le X h) hw, fun h => absurd (hΘ.toG_sup_le X h) h1⟩

theorem le_toG_sup_iff (hΘ : ThetaSpec t e Θ) {X : Subgroup (Equiv.Perm (Fin 693))}
    (hX : X ≤ T46) {P : Subgroup G} (hP : P ≤ centralizer ({t} : Set G)) :
    P ≤ toG e X ⊔ zpowers t ↔ (P.subgroupOf (centralizer ({t} : Set G))).map Θ ≤ X := by
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    exact (hΘ.mem_toG_sup_iff hX x).mp (h (mem_subgroupOf.mp hx))
  · intro h p hp
    exact (hΘ.mem_toG_sup_iff hX ⟨p, hP hp⟩).mpr (h ⟨⟨p, hP hp⟩, mem_subgroupOf.mpr hp, rfl⟩)

theorem card_le_two_mul (hΘ : ThetaSpec t e Θ) (ht : orderOf t = 2) {P : Subgroup G}
    (hP : P ≤ centralizer ({t} : Set G)) :
    Nat.card P ≤ 2 * Nat.card ((P.subgroupOf (centralizer ({t} : Set G))).map Θ) := by
  set P' := P.subgroupOf (centralizer ({t} : Set G))
  have hcard : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv
  set f := Θ.domRestrict P'
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    MonoidHom.domRestrict_range] at h1
  have hfin : Finite (zpowers t) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, ht]; norm_num)
  have hk : Nat.card f.ker ≤ 2 := by
    have h2 : Nat.card f.ker ≤ Nat.card (zpowers t) := by
      refine Nat.card_le_card_of_injective
        (fun k => ⟨(((k : P') : centralizer ({t} : Set G)) : G),
          (hΘ.eq_one_iff _).mp (MonoidHom.mem_ker.mp k.2)⟩) ?_
      intro a b hab
      have h : (((a : P') : centralizer ({t} : Set G)) : G) =
          (((b : P') : centralizer ({t} : Set G)) : G) :=
        congrArg (fun z : zpowers t => (z : G)) hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
    rwa [Nat.card_zpowers, ht] at h2
  rw [← hcard, h1]
  calc Nat.card (P'.map Θ) * Nat.card f.ker ≤ Nat.card (P'.map Θ) * 2 :=
        Nat.mul_le_mul_left _ hk
    _ = 2 * Nat.card (P'.map Θ) := mul_comm _ _

theorem isPGroup_map {p : ℕ} {P : Subgroup G} (hp : IsPGroup p P) :
    IsPGroup p ((P.subgroupOf (centralizer ({t} : Set G))).map Θ) := by
  refine IsPGroup.map ?_ Θ
  intro g
  obtain ⟨k, hk⟩ := hp ⟨((g : centralizer ({t} : Set G)) : G), g.2⟩
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩

theorem map_le_normalizer {P N : Subgroup G} (hN : N ≤ Subgroup.normalizer (P : Set G)) :
    (N.subgroupOf (centralizer ({t} : Set G))).map Θ ≤
      Subgroup.normalizer (((P.subgroupOf (centralizer ({t} : Set G))).map Θ :
        Subgroup (Equiv.Perm (Fin 693))) : Set (Equiv.Perm (Fin 693))) := by
  refine le_trans (map_mono ?_) (le_normalizer_map Θ)
  intro n hn
  rw [mem_normalizer_iff]
  intro h
  rw [mem_subgroupOf, mem_subgroupOf]
  have := mem_normalizer_iff.mp (hN (mem_subgroupOf.mp hn)) h
  simpa using this

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut.ThetaSpec
