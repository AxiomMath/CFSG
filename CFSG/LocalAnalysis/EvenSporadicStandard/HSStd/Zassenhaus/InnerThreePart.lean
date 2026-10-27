module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFullness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SylowCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section General

theorem card_comap_of_surj {P Q : Type*} [Group P] [Group Q] [Finite P] (f : P →* Q)
    (hf : Function.Surjective f) (H : Subgroup Q) :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  have : Finite Q := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (H.comap f)
  have h2 := Subgroup.card_mul_index H
  have h3 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at h3
  rw [Subgroup.index_comap_of_surjective _ hf] at h1
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1, ← h3, ← h2, mul_assoc]

theorem card_centralizer_singleton_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    Nat.card (centralizer ({φ a} : Set B)) = Nat.card (centralizer ({a} : Set A)) :=
  Nat.card_congr
    { toFun := fun k => ⟨φ.symm k, by
        rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.1 k.2
        apply φ.injective
        simpa using this⟩
      invFun := fun k => ⟨φ k, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          mem_centralizer_singleton_iff.1 k.2]⟩
      left_inv := fun k => by ext; simp
      right_inv := fun k => by ext; simp }

theorem congr_conj {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (a : A) :
    MulAut.congr φ (MulAut.conj a) = MulAut.conj (φ a) := by
  ext y
  simp [MulAut.congr_apply]

theorem swapChar_mapEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) (w : Wr2 A) :
    swapChar (mapEquiv φ w) = swapChar w := by
  rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ <;>
    simp [mapEquiv_base, mapEquiv_tau]

theorem exists_base_of_mem_centralizer {A : Type*} [Group A] {a : A} (ha : a ≠ 1) {w : Wr2 A}
    (hw : w ∈ centralizer ({base a 1} : Set (Wr2 A))) : ∃ c d : A, w = base c d := by
  rcases eq_base_or_eq_base_mul_tau w with ⟨c, d, rfl⟩ | ⟨c, d, rfl⟩
  · exact ⟨c, d, rfl⟩
  · exfalso
    obtain ⟨-, h2⟩ := (base_mul_tau_mem_centralizer_base_iff c d a 1).1 hw
    apply ha
    simpa using h2

end General

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

namespace InnerD8Config

variable (c : InnerD8Config L t)

abbrev X3 : Subgroup G := c.L₁ ⊓ centralizer ({c.x} : Set G)

abbrev X3t : Subgroup G := conjSub t c.X3

abbrev y : G := c.x * (t * c.x * t⁻¹)

theorem x_ne_one : c.x ≠ 1 := by
  intro h
  have := c.x_ord
  rw [h, orderOf_one] at this
  omega

theorem x_mem_P : c.x ∈ c.P := c.pair.K_le c.x_mem

theorem x_mem_X3 : c.x ∈ c.X3 := ⟨c.x_mem, mem_centralizer_singleton_iff.2 rfl⟩

theorem orderOf_eL₁_x : orderOf (c.eL₁ ⟨c.x, c.x_mem⟩) = 3 := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact c.x_ord

theorem conj_injective_L₁ {m n : ↥c.L₁} (h : MulAut.conj m = MulAut.conj n) : m = n := by
  have hz : n⁻¹ * m ∈ center ↥c.L₁ := by
    rw [mem_center_iff]
    intro g
    have h1 : m * g * m⁻¹ = n * g * n⁻¹ := by
      have := congrArg (fun f : MulAut ↥c.L₁ => f g) h
      simpa [MulAut.conj_apply] using this
    calc g * (n⁻¹ * m) = n⁻¹ * (n * g * n⁻¹) * m := by group
      _ = n⁻¹ * (m * g * m⁻¹) * m := by rw [h1]
      _ = n⁻¹ * m * g := by group
  rw [center_L₁_eq_bot c, mem_bot] at hz
  exact (inv_mul_eq_one.1 hz).symm

theorem X3_facts
    (hT3 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
      Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 6)))) = 9 ∧
      (∀ a ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))),
        ∀ b ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))), a * b = b * a) ∧
      ∀ a ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))), a ^ 3 = 1) :
    Nat.card c.X3 = 9 ∧ (∀ a ∈ c.X3, ∀ b ∈ c.X3, a * b = b * a) ∧ ∀ a ∈ c.X3, a ^ 3 = 1 := by
  obtain ⟨h9, hcomm, hcube⟩ := hT3 _ c.orderOf_eL₁_x
  have key : ∀ a (ha : a ∈ c.X3),
      c.eL₁ ⟨a, ha.1⟩ ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set (alternatingGroup (Fin 6))) := by
    intro a ha
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 ha.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [← card_centralizer_subtype c.L₁ c.x_mem, ← card_centralizer_singleton_equiv c.eL₁, h9]
  · intro a ha b hb
    have := hcomm _ (key a ha) _ (key b hb)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (c.eL₁.injective this)
  · intro a ha
    have := hcube _ (key a ha)
    rw [← map_pow] at this
    have h1 : (⟨a, ha.1⟩ : ↥c.L₁) ^ 3 = 1 := c.eL₁.injective (this.trans (map_one c.eL₁).symm)
    exact congrArg Subtype.val h1

theorem orderOf_eq_three_of_mem_X3 (hcube : ∀ a ∈ c.X3, a ^ 3 = 1) {a : G} (ha : a ∈ c.X3)
    (ha1 : a ≠ 1) : orderOf a = 3 :=
  orderOf_eq_prime (hcube a ha) ha1

theorem exists_conj_of_mem_X3t {b : G} (hb : b ∈ c.X3t) : ∃ b' ∈ c.X3, t * b' * t⁻¹ = b := by
  obtain ⟨b', hb', rfl⟩ := hb
  exact ⟨b', hb', rfl⟩

theorem comm_L₁_conj {a b : G} (ha : a ∈ c.L₁) (hb : b ∈ conjSub t c.L₁) : Commute a b := by
  obtain ⟨b', hb', rfl⟩ := hb
  exact c.pair.comm a ha b' hb'

theorem eq_one_of_mem_L₁_of_mem_conj {a : G} (ha : a ∈ c.L₁) (hb : a ∈ conjSub t c.L₁) :
    a = 1 := by
  have hz : (⟨a, ha⟩ : ↥c.L₁) ∈ center ↥c.L₁ := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (c.comm_L₁_conj k.2 hb).eq
  rw [center_L₁_eq_bot c, mem_bot] at hz
  exact congrArg Subtype.val hz

theorem X3_inf_X3t : c.X3 ⊓ c.X3t = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [mem_bot]
  exact c.eq_one_of_mem_L₁_of_mem_conj ha.1.1 (Subgroup.map_mono inf_le_left ha.2)

theorem commute_X3_X3t (m : ↥c.X3) (n : ↥c.X3t) : Commute (c.X3.subtype m) (c.X3t.subtype n) :=
  c.comm_L₁_conj m.2.1 (Subgroup.map_mono inf_le_left n.2)

def V3 : Subgroup G :=
  (MonoidHom.noncommCoprod c.X3.subtype c.X3t.subtype c.commute_X3_X3t).range

theorem mem_V3 {v : G} : v ∈ c.V3 ↔ ∃ a ∈ c.X3, ∃ b ∈ c.X3t, v = a * b := by
  constructor
  · rintro ⟨⟨m, n⟩, rfl⟩
    exact ⟨m, m.2, n, n.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem X3_le_V3 : c.X3 ≤ c.V3 := fun a ha =>
  c.mem_V3.2 ⟨a, ha, 1, one_mem _, (mul_one a).symm⟩

theorem X3t_le_V3 : c.X3t ≤ c.V3 := fun b hb =>
  c.mem_V3.2 ⟨1, one_mem _, b, hb, (one_mul b).symm⟩

theorem card_X3t (h9 : Nat.card c.X3 = 9) : Nat.card c.X3t = 9 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, h9]

theorem card_V3 (h9 : Nat.card c.X3 = 9) : Nat.card c.V3 = 81 := by
  let φ := MonoidHom.noncommCoprod c.X3.subtype c.X3t.subtype c.commute_X3_X3t
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ h
    have h1 : (m : G) * n = 1 := h
    have hm : (m : G) ∈ c.X3t := by
      have : (m : G) = (n : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_mem n.2
    have hm1 : (m : G) = 1 := by
      have : (m : G) ∈ c.X3 ⊓ c.X3t := ⟨m.2, hm⟩
      rw [c.X3_inf_X3t, mem_bot] at this
      exact this
    have hn1 : (n : G) = 1 := by
      rw [hm1, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hm1) (Subtype.ext hn1)
  have := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [Nat.card_prod, h9, c.card_X3t h9] at this
  exact this.symm.trans (by norm_num)

theorem V3_comm (hcomm : ∀ a ∈ c.X3, ∀ b ∈ c.X3, a * b = b * a) :
    ∀ v ∈ c.V3, ∀ w ∈ c.V3, Commute v w := by
  intro v hv w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := c.mem_V3.1 hv
  obtain ⟨a', ha', b', hb', rfl⟩ := c.mem_V3.1 hw
  have haa : Commute a a' := hcomm a ha a' ha'
  have hbb : Commute b b' := by
    obtain ⟨d, hd, rfl⟩ := c.exists_conj_of_mem_X3t hb
    obtain ⟨d', hd', rfl⟩ := c.exists_conj_of_mem_X3t hb'
    have e : t * d * t⁻¹ * (t * d' * t⁻¹) = t * (d * d') * t⁻¹ := by group
    have e' : t * d' * t⁻¹ * (t * d * t⁻¹) = t * (d' * d) * t⁻¹ := by group
    show _ = _
    rw [e, e', hcomm d hd d' hd']
  have hab' : Commute a b' := c.commute_X3_X3t ⟨a, ha⟩ ⟨b', hb'⟩
  have hba' : Commute b a' := (c.commute_X3_X3t ⟨a', ha'⟩ ⟨b, hb⟩).symm
  exact ((haa.mul_right hab').mul_left (hba'.mul_right hbb))

theorem exists_pair_rho_eq (hsurj : c.rho.range = ⊤) (α β : MulAut ↥c.L₁) :
    ∃ p : ↥c.P, c.pair.rho p = base α β := by
  obtain ⟨p, hp⟩ : base (MulAut.congr c.eL₁ α) (MulAut.congr c.eL₁ β) ∈ c.rho.range := by
    rw [hsurj]
    exact mem_top _
  refine ⟨p, ?_⟩
  apply (mapEquiv (MulAut.congr c.eL₁)).injective
  rw [mapEquiv_base, ← hp]
  exact (c.rho_apply p).symm

theorem exists_transport
    (hT1 : ∀ x x' : alternatingGroup (Fin 6), orderOf x = 3 → orderOf x' = 3 →
      ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x')
    (hsurj : c.rho.range = ⊤) {a b : G} (ha : a ∈ c.L₁) (ha3 : orderOf a = 3)
    (hb : b ∈ c.L₁) (hb3 : orderOf b = 3) :
    ∃ p : G, p * c.x * p⁻¹ = a ∧ (t * p * t) * c.x * (t * p * t)⁻¹ = b := by
  have hord : ∀ {a : G} (ha : a ∈ c.L₁), orderOf a = 3 → orderOf (c.eL₁ ⟨a, ha⟩) = 3 := by
    intro a ha h
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h
  have hex : ∀ {a : G} (ha : a ∈ c.L₁), orderOf a = 3 →
      ∃ α : MulAut ↥c.L₁, α ⟨c.x, c.x_mem⟩ = ⟨a, ha⟩ := by
    intro a ha h
    obtain ⟨α, hα⟩ := hT1 _ _ c.orderOf_eL₁_x (hord ha h)
    refine ⟨c.eL₁.trans (α.trans c.eL₁.symm), ?_⟩
    show c.eL₁.symm (α (c.eL₁ ⟨c.x, c.x_mem⟩)) = _
    rw [hα]
    simp
  obtain ⟨α, hα⟩ := hex ha ha3
  obtain ⟨β, hβ⟩ := hex hb hb3
  obtain ⟨p, hp⟩ := c.exists_pair_rho_eq hsurj α β
  have hn : (p : G) ∈ normalizer (c.L₁ : Set G) := by
    rw [mem_normalizer_iff_map_eq, ← c.pair.rho_mem_baseSubgroup_iff p, hp,
      mem_baseSubgroup_iff, swapChar_base]
  have hr := c.pair.rho_of_normalizes p hn
  rw [hp, base_injective] at hr
  refine ⟨p, ?_, ?_⟩
  · have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.1
    simp only [hα, conjAutOf_apply] at this
    exact this.symm
  · have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.2
    simp only [hβ, conjAutOf_apply] at this
    exact this.symm

theorem exists_conj_pair
    (hT1 : ∀ x x' : alternatingGroup (Fin 6), orderOf x = 3 → orderOf x' = 3 →
      ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x')
    (hsurj : c.rho.range = ⊤) (hcube : ∀ a ∈ c.X3, a ^ 3 = 1) {a b : G} (ha : a ∈ c.X3)
    (ha1 : a ≠ 1) (hb : b ∈ c.X3t) (hb1 : b ≠ 1) :
    ∃ p : G, p * c.x * p⁻¹ = a ∧ p * (t * c.x * t⁻¹) * p⁻¹ = b := by
  obtain ⟨b', hb', rfl⟩ := c.exists_conj_of_mem_X3t hb
  have hb'1 : b' ≠ 1 := by
    rintro rfl
    apply hb1
    simp
  obtain ⟨p, h1, h2⟩ := c.exists_transport hT1 hsurj ha.1
    (c.orderOf_eq_three_of_mem_X3 hcube ha ha1) hb'.1
    (c.orderOf_eq_three_of_mem_X3 hcube hb' hb'1)
  refine ⟨p, h1, ?_⟩
  have htg : t * (t * p * t) = p * t := by
    calc t * (t * p * t) = (t * t) * p * t := by group
      _ = p * t := by rw [c.pair.t_sq, one_mul]
  calc p * (t * c.x * t⁻¹) * p⁻¹ = (p * t) * c.x * (p * t)⁻¹ := by group
    _ = (t * (t * p * t)) * c.x * (t * (t * p * t))⁻¹ := by rw [htg]
    _ = t * ((t * p * t) * c.x * (t * p * t)⁻¹) * t⁻¹ := by group
    _ = t * b' * t⁻¹ := by rw [h2]

theorem isConj_y_mul
    (hT1 : ∀ x x' : alternatingGroup (Fin 6), orderOf x = 3 → orderOf x' = 3 →
      ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x')
    (hsurj : c.rho.range = ⊤) (hcube : ∀ a ∈ c.X3, a ^ 3 = 1) {a b : G} (ha : a ∈ c.X3)
    (ha1 : a ≠ 1) (hb : b ∈ c.X3t) (hb1 : b ≠ 1) : IsConj c.y (a * b) := by
  obtain ⟨p, h1, h2⟩ := c.exists_conj_pair hT1 hsurj hcube ha ha1 hb hb1
  rw [isConj_iff]
  refine ⟨p, ?_⟩
  rw [← h1, ← h2]
  group

theorem isConj_x_of_mem
    (hT1 : ∀ x x' : alternatingGroup (Fin 6), orderOf x = 3 → orderOf x' = 3 →
      ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x')
    (hsurj : c.rho.range = ⊤) (hcube : ∀ a ∈ c.X3, a ^ 3 = 1) {d : G}
    (hd : d ∈ c.X3 ∨ d ∈ c.X3t) (hd1 : d ≠ 1) : IsConj c.x d := by
  have hxt : t * c.x * t⁻¹ ∈ c.X3t := ⟨c.x, c.x_mem_X3, rfl⟩
  have hxt1 : t * c.x * t⁻¹ ≠ 1 := by
    intro h
    apply c.x_ne_one
    simpa using h
  rcases hd with hd | hd
  · obtain ⟨p, h1, -⟩ := c.exists_conj_pair hT1 hsurj hcube hd hd1 hxt hxt1
    exact isConj_iff.2 ⟨p, h1⟩
  · obtain ⟨p, -, h2⟩ := c.exists_conj_pair hT1 hsurj hcube c.x_mem_X3 c.x_ne_one hd hd1
    have h3 : IsConj c.x (t * c.x * t⁻¹) := isConj_iff.2 ⟨t, rfl⟩
    exact h3.trans (isConj_iff.2 ⟨p, h2⟩)

theorem card_centralizer_one {A : Type*} [Group A] :
    Nat.card (centralizer ({1} : Set A)) = Nat.card A := by
  have : centralizer ({1} : Set A) = ⊤ :=
    eq_top_iff.2 fun g _ => mem_centralizer_singleton_iff.2 (by simp)
  rw [this, Subgroup.card_top]

theorem card_P_inf_centralizer_x (hsurj : c.rho.range = ⊤)
    (hT2 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
      Nat.card (centralizer ({MulAut.conj x} : Set (MulAut (alternatingGroup (Fin 6))))) = 18) :
    Nat.card ↥(c.P ⊓ centralizer ({c.x} : Set G)) = 103680 := by
  let x' : ↥c.P := ⟨c.x, c.x_mem_P⟩
  let xh : ↥c.L₁ := ⟨c.x, c.x_mem⟩
  have hρx' : c.rho x' = base (MulAut.congr c.eL₁ (MulAut.conj xh)) 1 := by
    rw [rho_apply, c.pair.rho_of_mem c.x c.x_mem, mapEquiv_base, map_one]
  have hρx : c.rho x' = base (MulAut.conj (c.eL₁ xh)) 1 := by rw [hρx', congr_conj]
  have ha1 : MulAut.conj (c.eL₁ xh) ≠ 1 := by
    intro h
    have h2 : MulAut.conj xh = 1 := by
      apply (MulAut.congr c.eL₁).injective
      rw [congr_conj, h, map_one]
    have h3 : xh = 1 := c.conj_injective_L₁ (by rw [h2, map_one])
    exact c.x_ne_one (congrArg Subtype.val h3)
  have hcomap : (c.P ⊓ centralizer ({c.x} : Set G)).subgroupOf c.P =
      (centralizer ({c.rho x'} : Set _)).comap c.rho := by
    ext p
    simp only [mem_subgroupOf, mem_comap, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h
    · intro h
      refine ⟨mem_centralizer_singleton_iff.1 p.2, ?_⟩
      have hw : c.rho p ∈ centralizer ({base (MulAut.conj (c.eL₁ xh)) 1} :
          Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) := by
        rw [mem_centralizer_singleton_iff, ← hρx]
        exact h
      obtain ⟨c', d', hcd⟩ := exists_base_of_mem_centralizer ha1 hw
      have hbase : c.pair.rho p ∈ (baseSubgroup : Subgroup (Wr2 (MulAut ↥c.L₁))) := by
        rw [mem_baseSubgroup_iff, ← swapChar_mapEquiv (MulAut.congr c.eL₁), ← rho_apply, hcd,
          swapChar_base]
      have hn : (p : G) ∈ normalizer (c.L₁ : Set G) := by
        rw [mem_normalizer_iff_map_eq]
        exact (c.pair.rho_mem_baseSubgroup_iff p).1 hbase
      have hk : (p : G) * c.x * (p : G)⁻¹ ∈ c.L₁ := (mem_normalizer_iff.1 hn c.x).1 c.x_mem
      have hkP : (p : G) * c.x * (p : G)⁻¹ ∈ c.P := c.pair.K_le hk
      have hρk : c.rho ⟨(p : G) * c.x * (p : G)⁻¹, hkP⟩ = c.rho x' := by
        have : (⟨(p : G) * c.x * (p : G)⁻¹, hkP⟩ : ↥c.P) = p * x' * p⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv, h, mul_inv_cancel_right]
      have hρk2 : c.rho ⟨(p : G) * c.x * (p : G)⁻¹, hkP⟩ = base (MulAut.congr c.eL₁
          (MulAut.conj (⟨(p : G) * c.x * (p : G)⁻¹, hk⟩ : ↥c.L₁))) 1 := by
        rw [rho_apply, c.pair.rho_of_mem _ hk, mapEquiv_base, map_one]
      rw [hρk2, hρx'] at hρk
      have h5 := c.conj_injective_L₁ ((MulAut.congr c.eL₁).injective (base_injective.1 hρk).1)
      have hkx : (p : G) * c.x * (p : G)⁻¹ = c.x := congrArg Subtype.val h5
      exact mul_inv_eq_iff_eq_mul.1 hkx
  have hsurj' : Function.Surjective c.rho := MonoidHom.range_eq_top.1 hsurj
  rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : c.P ⊓ centralizer ({c.x} : Set G) ≤ c.P)).toEquiv,
    hcomap, card_comap_of_surj c.rho hsurj', c.card_ker_rho, hρx,
    card_centralizer_base_of_not_isConj (a := MulAut.conj (c.eL₁ xh)) (b := 1)
      (fun h => ha1 (isConj_one_left.1 h)),
    c.orderOf_eL₁_x |> hT2 _, card_centralizer_one, CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]

theorem not_isConj_x_y (hsurj : c.rho.range = ⊤)
    (hT2 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
      Nat.card (centralizer ({MulAut.conj x} : Set (MulAut (alternatingGroup (Fin 6))))) = 18) :
    ¬ IsConj c.x c.y := by
  intro h
  have h1 := card_centralizer_eq_of_isConj h
  rw [c.card_centralizer_y] at h1
  have h2 := Subgroup.card_dvd_of_le
    (inf_le_right : c.P ⊓ centralizer ({c.x} : Set G) ≤ centralizer ({c.x} : Set G))
  rw [c.card_P_inf_centralizer_x hsurj hT2, h1] at h2
  omega

end InnerD8Config

theorem InnerD8Config.factorization_three (c : InnerD8Config L t)
    (hL : IsSporadic ↥L .HS) (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n)
    (hT1 : ∀ x x' : alternatingGroup (Fin 6), orderOf x = 3 → orderOf x' = 3 →
      ∃ α : MulAut (alternatingGroup (Fin 6)), α x = x')
    (hT2 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
      Nat.card (centralizer ({MulAut.conj x} : Set (MulAut (alternatingGroup (Fin 6))))) = 18)
    (hT3 : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 →
      Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 6)))) = 9 ∧
      (∀ a ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))),
        ∀ b ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))), a * b = b * a) ∧
      ∀ a ∈ centralizer ({x} : Set (alternatingGroup (Fin 6))), a ^ 3 = 1) :
    (Nat.card G).factorization 3 = 4 := by
  have hsurj := c.rho_surjective hL htL ht2 hin hf
  obtain ⟨h9, hcomm, hcube⟩ := c.X3_facts hT3
  have h9t := c.card_X3t h9
  have hne : c.x ≠ 1 := c.x_ne_one
  refine factorization_eq_of_two_factors (X := c.X3) (Y := c.X3t) (V := c.V3) (by norm_num)
    (IsPGroup.of_card (n := 2) (by rw [h9]; norm_num))
    (IsPGroup.of_card (n := 2) (by rw [h9t]; norm_num)) ?_ ?_ c.X3_inf_X3t c.X3_le_V3
    c.X3t_le_V3 (fun v hv => c.mem_V3.1 hv) (c.V3_comm hcomm) ?_ ?_
    (IsPGroup.of_card (n := 4) (by rw [c.card_V3 h9]; norm_num)) (k := 4)
    (by rw [c.card_V3 h9]; norm_num)
  · intro h
    rw [h, Subgroup.card_bot] at h9
    omega
  · intro h
    rw [h, Subgroup.card_bot] at h9t
    omega
  · intro a ha ha1 b hb hb1 Q hQ hVQ hQC
    have hconj := c.isConj_y_mul hT1 hsurj hcube ha ha1 hb hb1
    have hcard : Nat.card (centralizer ({a * b} : Set G)) = 259200 := by
      rw [card_centralizer_eq_of_isConj hconj.symm, c.card_centralizer_y]
    have hQdvd : Nat.card Q ∣ 259200 := hcard ▸ Subgroup.card_dvd_of_le hQC
    have hVdvd : 81 ∣ Nat.card Q := c.card_V3 h9 ▸ Subgroup.card_dvd_of_le hVQ
    obtain ⟨m, hm⟩ := hQ.exists_card_eq
    rw [hm] at hQdvd hVdvd
    have h3 : 3 ^ m = 81 := by
      by_cases hm4 : m ≤ 4
      · interval_cases m <;> simp_all
      · exfalso
        have : 3 ^ 5 ∣ 3 ^ m := pow_dvd_pow 3 (by omega)
        have := this.trans hQdvd
        norm_num at this
    refine (Subgroup.eq_of_le_of_card_ge hVQ ?_).symm
    rw [hm, h3, c.card_V3 h9]
  · intro g d hd hd1 a ha ha1 b hb hb1 hg
    have h1 : IsConj c.x d := c.isConj_x_of_mem hT1 hsurj hcube hd hd1
    have h2 : IsConj d (a * b) := isConj_iff.2 ⟨g, hg⟩
    have h3 : IsConj (a * b) c.y := (c.isConj_y_mul hT1 hsurj hcube ha ha1 hb hb1).symm
    exact c.not_isConj_x_y hsurj hT2 (h1.trans (h2.trans h3))

theorem InnerD8Config.factorization_three_eq_four (c : InnerD8Config L t) (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) : (Nat.card G).factorization 3 = 4 :=
  c.factorization_three hL htL ht2 hin hf (fun _ _ hx hx' => exists_mulAut_apply_eq_of_orderOf_eq_three hx hx')
    (fun _ hx => card_centralizer_conj_of_orderOf_eq_three hx)
    (fun _ hx => ⟨card_centralizer_of_orderOf_eq_three hx, centralizer_commute_of_orderOf_eq_three hx,
      pow_three_of_mem_centralizer hx⟩)

end Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
