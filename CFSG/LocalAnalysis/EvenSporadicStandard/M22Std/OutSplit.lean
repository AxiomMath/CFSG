module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutBuild

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

theorem ncard_preimage_ker {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) {A : Set Y}
    (hA : A ⊆ (φ.range : Set Y)) : (φ ⁻¹' A).ncard = A.ncard * Nat.card φ.ker := by
  classical
  choose g hg using fun a : A => (hA a.2)
  let e : A × φ.ker ≃ (φ ⁻¹' A) :=
    { toFun := fun p => ⟨g p.1 * p.2, by
        show φ (g p.1 * p.2) ∈ A
        rw [map_mul, hg p.1, (MonoidHom.mem_ker.1 p.2.2), mul_one]
        exact p.1.2⟩
      invFun := fun y => (⟨φ y, y.2⟩, ⟨(g ⟨φ y, y.2⟩)⁻¹ * y, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel]⟩)
      left_inv := fun p => by
        obtain ⟨a, k⟩ := p
        have h1 : φ (g a * k) = a := by
          rw [map_mul, hg a, (MonoidHom.mem_ker.1 k.2), mul_one]
        apply Prod.ext
        · apply Subtype.ext
          show φ (g a * k) = a
          exact h1
        · apply Subtype.ext
          show (g ⟨φ (g a * k), _⟩)⁻¹ * (g a * k) = k
          have : (⟨φ (g a * k), by rw [h1]; exact a.2⟩ : A) = a := Subtype.ext h1
          rw [this]
          group
      right_inv := fun y => by
        apply Subtype.ext
        show g ⟨φ y, y.2⟩ * ((g ⟨φ y, y.2⟩)⁻¹ * y) = y
        group }
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_congr e, Nat.card_prod]

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

omit D in
theorem zpowers_le_H : zpowers z ≤ centralizer ({z} : Set G) :=
  zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)

include D in
theorem theta_inner_iff (y : centralizer ({z} : Set G)) :
    thetaH D.cfg.cent_le y ∈ innerImage (L ⧸ center L) ⊤ ↔ (y : G) ∈ L ⊔ zpowers z := by
  constructor
  · rintro ⟨q, -, hq⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : thetaH D.cfg.cent_le (⟨(l : G), D.l_mem_H l.2⟩⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, D.theta_conj]
      exact inv_mul_eq_one.2 hq
    have h2 := (D.ker _).1 h1
    have h3 : ((l : G))⁻¹ * y ∈ zpowers z := h2
    have h4 : (y : G) = l * ((l : G)⁻¹ * y) := by group
    rw [h4]
    exact Subgroup.mul_mem _ (mem_sup_left l.2) (mem_sup_right h3)
  · intro hy
    obtain ⟨l, hl, b, hb, hlb⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 D.cfg.z_cent) hy
    have hbH : b ∈ centralizer ({z} : Set G) := zpowers_le_H hb
    have hlH : l ∈ centralizer ({z} : Set G) := D.l_mem_H hl
    have hy' : y = ⟨l, hlH⟩ * ⟨b, hbH⟩ := Subtype.ext hlb
    have hθb : thetaH D.cfg.cent_le ⟨b, hbH⟩ = 1 := (D.ker _).2 hb
    rw [hy', map_mul, hθb, mul_one]
    exact ⟨(⟨l, hl⟩ : L), trivial, (D.theta_conj ⟨l, hl⟩).symm⟩

include D in
theorem sq_mem_L_iff [Finite G] {y y' : G} (hy : y ∈ centralizer ({z} : Set G))
    (hy' : y' ∈ centralizer ({z} : Set G)) (hyo : y ∉ L ⊔ zpowers z)
    (hyo' : y' ∉ L ⊔ zpowers z) : y' * y' ∈ L ↔ y * y ∈ L := by
  have hidx : ((L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 :=
    D.cfg.index_two
  have hc : y⁻¹ * y' ∈ L ⊔ zpowers z := by
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : centralizer ({z} : Set G))) (b := ⟨y', hy'⟩)).2 (by
        constructor
        · intro h
          exact absurd (by simpa using Subgroup.inv_mem _ (mem_subgroupOf.1 h)) hyo
        · intro h
          exact absurd (mem_subgroupOf.1 h) hyo')
    exact mem_subgroupOf.1 h1
  obtain ⟨l, hl, b, hb, hlb⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 D.cfg.z_cent) hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hy'eq : y' = y * (l * z ^ k) := by rw [← hlb]; group
  have hyb : y * z ^ k = z ^ k * y :=
    (Commute.zpow_right (show Commute y z from mem_centralizer_singleton_iff.1 hy) k).eq
  have hlb' : l * z ^ k = z ^ k * l :=
    ((Commute.zpow_right (D.cfg.z_comm_of_mem_A hl : Commute l z) k)).eq
  have hbb : z ^ k * z ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact D.cfg.z_sq
    rw [this, one_zpow]
  have key : y' * y' = (y * l * y⁻¹) * (y * y) * l := by
    rw [hy'eq]
    calc y * (l * z ^ k) * (y * (l * z ^ k)) = y * l * (z ^ k * y) * (l * z ^ k) := by group
      _ = y * l * (y * z ^ k) * (l * z ^ k) := by rw [hyb]
      _ = y * l * y * (z ^ k * l) * z ^ k := by group
      _ = y * l * y * (l * z ^ k) * z ^ k := by rw [hlb']
      _ = y * l * y * l * (z ^ k * z ^ k) := by group
      _ = y * l * y * l := by rw [hbb, mul_one]
      _ = (y * l * y⁻¹) * (y * y) * l := by group
  have hu : y * l * y⁻¹ ∈ L := D.conj_mem_L hy hl
  rw [key]
  constructor
  · intro h
    have := L.mul_mem (L.inv_mem hu) (L.mul_mem h (L.inv_mem hl))
    simpa [mul_assoc] using this
  · intro h
    exact L.mul_mem (L.mul_mem hu h) hl


include D in
theorem sq_mem_L_of_mem_sup {y : G} (hy : y ∈ L ⊔ zpowers z) : y * y ∈ L := by
  obtain ⟨l, hl, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 D.cfg.z_cent) hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : l * z ^ k = z ^ k * l :=
    ((Commute.zpow_right (D.cfg.z_comm_of_mem_A hl : Commute l z) k)).eq
  have hbb : z ^ k * z ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact D.cfg.z_sq
    rw [this, one_zpow]
  have : l * z ^ k * (l * z ^ k) = l * l := by
    calc l * z ^ k * (l * z ^ k) = l * (z ^ k * l) * z ^ k := by group
      _ = l * (l * z ^ k) * z ^ k := by rw [h1]
      _ = l * l * (z ^ k * z ^ k) := by group
      _ = l * l := by rw [hbb, mul_one]
  rw [this]
  exact L.mul_mem hl hl


section Main

variable [Finite G]

include D in
theorem exists_outer_involution (hcZ : center (L ⧸ center L) = ⊥) {x : G}
    (hx : x ∈ normalizer ((T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) : Set G))
    (hxz : x * z * x⁻¹ = z * t) (hxt : x * t * x⁻¹ = t) :
    ∃ y ∈ centralizer ({z} : Set G), y ∉ L ⊔ zpowers z ∧ y * y = 1 := by
  classical
  by_contra hno
  push Not at hno
  have hz2 : z * z = 1 := D.cfg.z_sq
  have hconjinj := HypOne.conj_injective_of_center_eq_bot hcZ
  obtain ⟨s, hsS, hsout, hs2⟩ := D.W.outer_inv
  obtain ⟨y₀, hy₀, rfl⟩ := hsS
  have hy₀o : (y₀ : G) ∉ L ⊔ zpowers z := fun h => hsout ((D.theta_inner_iff y₀).2 h)
  have hy₀sq : (y₀ : G) * y₀ = z := by
    have h1 : thetaH D.cfg.cent_le (y₀ * y₀) = 1 := by rw [map_mul]; exact hs2
    have h2 : ((y₀ * y₀ : centralizer ({z} : Set G)) : G) ∈ zpowers z := (D.ker _).1 h1
    rcases mem_zpowers_sq_eq_one hz2 h2 with h3 | h3
    · exact absurd h3 (hno y₀ y₀.2 hy₀o)
    · exact h3
  have htw : ∀ y ∈ centralizer ({z} : Set G), y ∉ L ⊔ zpowers z → y * y ∉ L := by
    intro y hy hyo hL
    have := (D.sq_mem_L_iff y₀.2 hy hy₀o hyo).1 hL
    rw [hy₀sq] at this
    exact D.cfg.z_not_mem_A this
  have htL : t ∈ L := D.t_mem_L
  have ht_sq : t * t = 1 := D.cfg.t_sq
  obtain ⟨t', htb, htt⟩ := D.tlift
  let θ := thetaH D.cfg.cent_le
  let φ : T₁ →* MulAut (L ⧸ center L) := θ.comp T₁.subtype
  have hker2 : Nat.card φ.ker = 2 := by
    have hker : φ.ker = (zpowers (zH z)).subgroupOf T₁ := by
      ext g
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact D.ker_zH g
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 D.zH_mem_T₁)).toEquiv,
      Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]; exact Subtype.ext D.cfg.z_sq
    · intro h
      exact D.cfg.z_ne (congrArg Subtype.val h)
  have hrange : (φ.range : Set (MulAut (L ⧸ center L))) = (T₁.map θ : Set _) := by
    ext β
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let A₁ : Set (MulAut (L ⧸ center L)) :=
    {s | s ∈ T₁.map θ ∧ s ∉ innerImage (L ⧸ center L) ⊤ ∧ s * s = 1}
  let A₂ : Set (MulAut (L ⧸ center L)) :=
    {s | s ∈ T₁.map θ ∧ s ∉ innerImage (L ⧸ center L) ⊤ ∧ s * s = MulAut.conj tb}
  let Rz : Set T₁ := {y | ((y : centralizer ({z} : Set G)) : G) * y = z}
  let Rzt : Set T₁ := {y | ((y : centralizer ({z} : Set G)) : G) * y = z * t}
  have hθz : ∀ y : centralizer ({z} : Set G), (y : G) * y = z → θ y * θ y = 1 := by
    intro y hy
    rw [← map_mul]
    apply (D.ker _).2
    have : ((y * y : centralizer ({z} : Set G)) : G) = z := hy
    rw [this]
    exact mem_zpowers z

  have hA₁ : A₁ ⊆ (φ.range : Set (MulAut (L ⧸ center L))) := fun s hs => by
    rw [hrange]; exact hs.1
  have hA₂ : A₂ ⊆ (φ.range : Set (MulAut (L ⧸ center L))) := fun s hs => by
    rw [hrange]; exact hs.1
  have hRz : Rz = φ ⁻¹' A₁ := by
    ext y
    constructor
    · intro hy
      refine ⟨⟨y, y.2, rfl⟩, ?_, hθz y.1 hy⟩
      intro hin
      have := D.sq_mem_L_of_mem_sup ((D.theta_inner_iff y.1).1 hin)
      rw [show ((y : centralizer ({z} : Set G)) : G) * y = z from hy] at this
      exact D.cfg.z_not_mem_A this
    · rintro ⟨-, hout, hsq⟩
      have hyo : ((y.1 : centralizer ({z} : Set G)) : G) ∉ L ⊔ zpowers z :=
        fun h => hout ((D.theta_inner_iff y.1).2 h)
      have h1 : θ (y.1 * y.1) = 1 := by rw [map_mul]; exact hsq
      have h2 : ((y.1 * y.1 : centralizer ({z} : Set G)) : G) ∈ zpowers z := (D.ker _).1 h1
      rcases mem_zpowers_sq_eq_one hz2 h2 with h3 | h3
      · exact absurd h3 (hno y.1 y.1.2 hyo)
      · exact h3
  have hRzt : Rzt = φ ⁻¹' A₂ := by
    ext y
    constructor
    · intro hy
      have hy' : ((y : centralizer ({z} : Set G)) : G) * y = z * t := hy
      refine ⟨⟨y, y.2, rfl⟩, ?_, ?_⟩
      · intro hin
        have := D.sq_mem_L_of_mem_sup ((D.theta_inner_iff y.1).1 hin)
        rw [hy'] at this
        exact D.cfg.z_not_mem_A (by simpa using L.mul_mem this (L.inv_mem htL))
      · have h1 : y.1 * y.1 = zH z * ⟨t, D.l_mem_H htL⟩ := Subtype.ext hy'
        have h2 : θ ⟨t, D.l_mem_H htL⟩ = MulAut.conj tb := by
          subst htt
          subst htb
          exact D.theta_conj t'
        have h3 : θ (zH z) = 1 := (D.ker _).2 (mem_zpowers z)
        show θ y.1 * θ y.1 = MulAut.conj tb
        rw [← map_mul, h1, map_mul, h3, h2, one_mul]
    · rintro ⟨-, hout, hsq⟩
      have hyH := y.1.2
      have hyo : ((y.1 : centralizer ({z} : Set G)) : G) ∉ L ⊔ zpowers z :=
        fun h => hout ((D.theta_inner_iff y.1).2 h)
      obtain ⟨l, hl, b, hb, hlb⟩ := exists_mul_of_mem_sup_of_le_centralizer
        (zpowers_le.2 D.cfg.z_cent) (D.cfg.sq_mem_sup hyH)
      have hlH : l ∈ centralizer ({z} : Set G) := D.l_mem_H hl
      have hbH : b ∈ centralizer ({z} : Set G) := zpowers_le_H hb
      have h1 : y.1 * y.1 = ⟨l, hlH⟩ * ⟨b, hbH⟩ := Subtype.ext hlb
      have h2 : θ (y.1 * y.1) = MulAut.conj tb := by rw [map_mul]; exact hsq
      have h3 : θ ⟨b, hbH⟩ = 1 := (D.ker _).2 hb
      rw [h1, map_mul, h3, mul_one] at h2
      have h4 : θ ⟨l, hlH⟩ = MulAut.conj ((⟨l, hl⟩ : L) : L ⧸ center L) := D.theta_conj ⟨l, hl⟩
      rw [h4] at h2
      have h5 := hconjinj h2
      have h6 : (⟨l, hl⟩ : L) = t' := by
        apply D.mk_injective
        rw [h5, htb]
      have h7 : l = t := by
        have := congrArg Subtype.val h6
        rw [← htt]; exact this
      rcases mem_zpowers_sq_eq_one hz2 hb with hb1 | hbz
      · exfalso
        apply htw y.1 y.1.2 hyo
        rw [hlb, hb1, mul_one, h7]
        exact htL
      · show ((y.1 : centralizer ({z} : Set G)) : G) * y.1 = z * t
        rw [hlb, hbz, h7]
        exact (D.cfg.t_comm_z)
  have hcard1 : Rz.ncard = A₁.ncard * 2 := by
    rw [hRz, ncard_preimage_ker φ hA₁, hker2]
  have hcard2 : Rzt.ncard = A₂.ncard * 2 := by
    rw [hRzt, ncard_preimage_ker φ hA₂, hker2]
  let f : T₁ → G := fun y => ((y : centralizer ({z} : Set G)) : G)
  have hfinj : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext h)
  have hxT : ∀ g, g ∈ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) ↔
      x * g * x⁻¹ ∈ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) :=
    fun g => Subgroup.mem_normalizer_iff.1 hx g
  have hz_conj' : x⁻¹ * (z * t) * x = z := by
    rw [← hxz]
    group
  have himg : (MulAut.conj x) '' (f '' Rz) = f '' Rzt := by
    ext g
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hgT : f y ∈ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) :=
        ⟨y.1, y.2, rfl⟩
      have hxg : x * f y * x⁻¹ ∈ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) :=
        (hxT _).1 hgT
      obtain ⟨y', hy', hy'eq⟩ := hxg
      refine ⟨⟨y', hy'⟩, ?_, hy'eq⟩
      show ((y' : centralizer ({z} : Set G)) : G) * y' = z * t
      have hy2 : f y * f y = z := hy
      have hy'eq' : ((y' : centralizer ({z} : Set G)) : G) = x * f y * x⁻¹ := hy'eq
      rw [hy'eq']
      calc x * f y * x⁻¹ * (x * f y * x⁻¹) = x * (f y * f y) * x⁻¹ := by group
        _ = x * z * x⁻¹ := by rw [hy2]
        _ = z * t := hxz
    · rintro ⟨y', hy', rfl⟩
      have hg'T : f y' ∈ (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) :=
        ⟨y'.1, y'.2, rfl⟩
      have hgT : x⁻¹ * f y' * x ∈
          (T₁.map (centralizer ({z} : Set G)).subtype : Subgroup G) := by
        refine (hxT _).2 ?_
        rw [show x * (x⁻¹ * f y' * x) * x⁻¹ = f y' by group]
        exact hg'T
      obtain ⟨y, hy, hyeq⟩ := hgT
      refine ⟨f ⟨y, hy⟩, ⟨⟨y, hy⟩, ?_, rfl⟩, ?_⟩
      · show ((y : centralizer ({z} : Set G)) : G) * y = z
        have hyeq' : ((y : centralizer ({z} : Set G)) : G) = x⁻¹ * f y' * x := hyeq
        have hy2 : f y' * f y' = z * t := hy'
        rw [hyeq']
        calc x⁻¹ * f y' * x * (x⁻¹ * f y' * x) = x⁻¹ * (f y' * f y') * x := by group
          _ = x⁻¹ * (z * t) * x := by rw [hy2]
          _ = z := hz_conj'
      · show x * ((y : centralizer ({z} : Set G)) : G) * x⁻¹ = f y'
        have hyeq' : ((y : centralizer ({z} : Set G)) : G) = x⁻¹ * f y' * x := hyeq
        rw [hyeq']
        group
  have hcard : Rz.ncard = Rzt.ncard := by
    have h1 := Set.ncard_image_of_injective Rz hfinj
    have h2 := Set.ncard_image_of_injective (f '' Rz) (MulAut.conj x).injective
    have h3 := Set.ncard_image_of_injective Rzt hfinj
    rw [← h1, ← h2, himg, h3]
  have hcount : A₁.ncard = A₂.ncard := by
    rw [hcard1, hcard2] at hcard
    omega
  exact D.W.count_ne hcount


include D in
omit [Finite G] in
theorem exists_complement {y : G} (hy : y ∈ centralizer ({z} : Set G)) (hyo : y ∉ L ⊔ zpowers z)
    (hy2 : y * y = 1) :
    ∃ A : Subgroup G, L ≤ A ∧ A ≤ centralizer ({z} : Set G) ∧ y ∈ A ∧ z ∉ A ∧
      A ⊔ zpowers z = centralizer ({z} : Set G) ∧ (L.subgroupOf A).index = 2 := by
  classical
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hconj : ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun l hl => D.conj_mem_L hy hl
  let A : Subgroup G :=
    { carrier := {g | g ∈ L ∨ ∃ l ∈ L, g = l * y}
      one_mem' := Or.inl L.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨l₁, hl₁, rfl⟩) (hb | ⟨l₂, hl₂, rfl⟩)
        · exact Or.inl (L.mul_mem ha hb)
        · exact Or.inr ⟨a * l₂, L.mul_mem ha hl₂, by group⟩
        · refine Or.inr ⟨l₁ * (y * b * y⁻¹), L.mul_mem hl₁ (hconj b hb), ?_⟩
          group
        · refine Or.inl ?_
          have : l₁ * y * (l₂ * y) = l₁ * (y * l₂ * y⁻¹) * (y * y) := by group
          rw [this, hy2, mul_one]
          exact L.mul_mem hl₁ (hconj l₂ hl₂)
      inv_mem' := by
        rintro a (ha | ⟨l, hl, rfl⟩)
        · exact Or.inl (L.inv_mem ha)
        · refine Or.inr ⟨y * l⁻¹ * y⁻¹, hconj _ (L.inv_mem hl), ?_⟩
          calc (l * y)⁻¹ = y⁻¹ * l⁻¹ := mul_inv_rev l y
            _ = y * l⁻¹ := by rw [hyi]
            _ = y * l⁻¹ * y⁻¹ * y := by group }
  have hLA : L ≤ A := fun l hl => Or.inl hl
  have hyA : y ∈ A := Or.inr ⟨1, L.one_mem, by group⟩
  have hLH : L ≤ centralizer ({z} : Set G) := fun l hl => D.l_mem_H hl
  have hAH : A ≤ centralizer ({z} : Set G) := by
    rintro a (ha | ⟨l, hl, rfl⟩)
    · exact hLH ha
    · exact Subgroup.mul_mem _ (hLH hl) hy
  have hzA : z ∉ A := by
    rintro (hz | ⟨l, hl, hlz⟩)
    · exact D.cfg.z_not_mem_A hz
    · apply hyo
      have : y = l⁻¹ * z := by rw [hlz]; group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_left (L.inv_mem hl)) (mem_sup_right (mem_zpowers z))
  refine ⟨A, hLA, hAH, hyA, hzA, ?_, ?_⟩
  · apply le_antisymm (sup_le hAH zpowers_le_H)
    intro h hh
    have hidx : ((L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 :=
      D.cfg.index_two
    by_cases hM : h ∈ L ⊔ zpowers z
    · exact sup_le_sup hLA le_rfl hM
    · have h1 := (Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : centralizer ({z} : Set G)))
        (b := ⟨h, hh⟩)).2 (by
          constructor
          · intro h'
            exact absurd (by simpa using Subgroup.inv_mem _ (mem_subgroupOf.1 h')) hyo
          · intro h'
            exact absurd (mem_subgroupOf.1 h') hM)
      have h2 : y⁻¹ * h ∈ L ⊔ zpowers z := mem_subgroupOf.1 h1
      have h3 : h = y * (y⁻¹ * h) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (mem_sup_left hyA) (sup_le_sup hLA le_rfl h2)
  · have hyL : y ∉ L := fun h => hyo (mem_sup_left h)
    refine Subgroup.index_eq_two_iff.2 ⟨⟨y, hyA⟩, fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | ⟨l, hl, rfl⟩
    · refine Or.inr ⟨hb, fun h => hyL ?_⟩
      have := L.mul_mem (L.inv_mem hb) h
      simpa using this
    · refine Or.inl ⟨?_, fun h => hyL ?_⟩
      · have : l * y * y = l := by rw [mul_assoc, hy2, mul_one]
        rw [this]
        exact hl
      · have := L.mul_mem (L.inv_mem hl) h
        simpa using this

end Main

end OutData

end CFSG.EvenSporadicStandard.M22Std
