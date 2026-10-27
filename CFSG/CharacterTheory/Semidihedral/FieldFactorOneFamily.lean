module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily
public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

variable {G : Type*} [Group G]

@[expose] def conjSub (k : G) (Q : Subgroup G) : Subgroup G := Q.map (MulAut.conj k).toMonoidHom

theorem mem_conjSub {k x : G} {Q : Subgroup G} : x ∈ conjSub k Q ↔ k⁻¹ * x * k ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨k⁻¹ * x * k, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_conjSub {k x : G} {Q : Subgroup G} (hx : x ∈ Q) : k * x * k⁻¹ ∈ conjSub k Q :=
  mem_conjSub.mpr (by simpa [mul_assoc] using hx)

theorem conjSub_mul (k k' : G) (Q : Subgroup G) :
    conjSub (k * k') Q = conjSub k (conjSub k' Q) := by
  ext x
  simp only [mem_conjSub, mul_inv_rev, mul_assoc]

theorem conjSub_one (Q : Subgroup G) : conjSub 1 Q = Q := by
  ext x
  simp [mem_conjSub]

theorem isPGroup_conjSub {p : ℕ} {Q : Subgroup G} (hQ : IsPGroup p Q) (k : G) :
    IsPGroup p (conjSub k Q) := hQ.map _

theorem conjSub_ne_bot {Q : Subgroup G} (hQ : Q ≠ ⊥) (k : G) : conjSub k Q ≠ ⊥ := by
  intro h
  apply hQ
  rw [eq_bot_iff]
  intro x hx
  have hx' : k * x * k⁻¹ ∈ conjSub k Q := conj_mem_conjSub hx
  rw [h, Subgroup.mem_bot] at hx'
  have : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  rw [Subgroup.mem_bot, this, hx']
  group

@[expose] def Special (t : G) (Q : Subgroup G) : Prop := t ∈ Q ∧ ∀ x ∈ Q, x * t = t * x

theorem conj_mem_C_of_special {t k : G} {Q : Subgroup G} (hk : Special t (conjSub k Q))
    {g : G} (hg : g ∈ Subgroup.centralizer (Q : Set G)) : k * g * k⁻¹ ∈ C t := by
  have htQ : k⁻¹ * t * k ∈ Q := mem_conjSub.mp hk.1
  have hcomm := Subgroup.mem_centralizer_iff.mp hg _ htQ
  rw [C, Subgroup.mem_centralizer_singleton_iff]
  calc k * g * k⁻¹ * t = k * (g * (k⁻¹ * t * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * t * k) * g) * k⁻¹ := by rw [hcomm]
    _ = t * (k * g * k⁻¹) := by group

open Classical in
@[expose] noncomputable def thetaG (t : G) (θ : C t →* ℂˣ) (g : G) : ℂˣ :=
  if hg : g ∈ C t then θ ⟨g, hg⟩ else 1

theorem thetaG_of_mem {t : G} (θ : C t →* ℂˣ) {g : G} (hg : g ∈ C t) :
    thetaG t θ g = θ ⟨g, hg⟩ := by
  classical
  simp [thetaG, hg]

theorem thetaG_coe {t : G} (θ : C t →* ℂˣ) (c : C t) : thetaG t θ c = θ c := by
  rw [thetaG_of_mem θ c.2]

theorem thetaG_mul {t : G} (θ : C t →* ℂˣ) {x y : G} (hx : x ∈ C t) (hy : y ∈ C t) :
    thetaG t θ (x * y) = thetaG t θ x * thetaG t θ y := by
  rw [thetaG_of_mem θ (Subgroup.mul_mem _ hx hy), thetaG_of_mem θ hx, thetaG_of_mem θ hy,
    ← map_mul]
  rfl

theorem thetaG_conj {t : G} (θ : C t →* ℂˣ) {c x : G} (hc : c ∈ C t) (hx : x ∈ C t) :
    thetaG t θ (c * x * c⁻¹) = thetaG t θ x := by
  have hci : c⁻¹ ∈ C t := Subgroup.inv_mem _ hc
  rw [thetaG_mul θ (Subgroup.mul_mem _ hc hx) hci, thetaG_mul θ hc hx, mul_comm (thetaG t θ c),
    mul_assoc, ← thetaG_mul θ hc hci, mul_inv_cancel, thetaG_of_mem θ (Subgroup.one_mem _)]
  have : (⟨1, Subgroup.one_mem _⟩ : C t) = 1 := rfl
  rw [this, map_one, mul_one]

section Setting

variable {n : ℕ} {S : Sylow 2 G} (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

theorem t_eq_image_z (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) : t = (fS (z n) : G) := by
  rw [ht, z, map_pow, Subgroup.coe_pow, half]

theorem t_mem_sylow (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) : t ∈ (S : Subgroup G) := by
  rw [t_eq_image_z fS ht]
  exact (fS (z n)).2

theorem orderOf_t (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) : orderOf t = 2 := by
  rw [t_eq_image_z fS ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_z n (by omega)]

theorem sylow_le_C (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    (S : Subgroup G) ≤ C t := by
  intro x hx
  rw [C, Subgroup.mem_centralizer_singleton_iff, t_eq_image_z fS ht]
  have hzc := Subgroup.mem_center_iff.mp (z_mem_center n hn) (fS.symm ⟨x, hx⟩)
  have h := congrArg (fun y : SemidihedralGroup n => ((fS y : S) : G)) hzc
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h
  exact h

theorem exists_conj_le_sylow [Finite G] (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQt : Q ≤ C t) :
    ∃ c ∈ C t, ∀ x ∈ Q, c * x * c⁻¹ ∈ (S : Subgroup G) := by
  have hQ' : IsPGroup 2 (Q.subgroupOf (C t)) :=
    hQ.of_injective ((Subgroup.subgroupOfEquivOfLe hQt).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQt).injective
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (C t) P (S.subtype (sylow_le_C fS hn ht))
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxP : (⟨x, hQt hx⟩ : C t) ∈ (P : Subgroup (C t)) := hP (Subgroup.mem_subgroupOf.mpr hx)
  have hmem : c * ⟨x, hQt hx⟩ * c⁻¹ ∈ ((c • P : Sylow 2 (C t)) : Subgroup (C t)) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hxP, rfl⟩
  rw [hc] at hmem
  simpa using Subgroup.mem_subgroupOf.mp hmem

theorem exists_conj_s0 [Finite G] (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    {u : G} (hu : u ∈ C t) (hu2 : orderOf u = 2) (hut : u ≠ t) :
    ∃ c ∈ C t, c * u * c⁻¹ = (fS (s n) : G) := by
  have hpu : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  obtain ⟨c₁, hc₁, hc₁S⟩ := exists_conj_le_sylow fS hn ht hpu
    ((Subgroup.zpowers_le (H := C t)).mpr hu)
  have huS : c₁ * u * c₁⁻¹ ∈ (S : Subgroup G) := hc₁S u (Subgroup.mem_zpowers u)
  set v : SemidihedralGroup n := fS.symm ⟨c₁ * u * c₁⁻¹, huS⟩ with hv
  have hfv : ((fS v : S) : G) = c₁ * u * c₁⁻¹ := by rw [hv, MulEquiv.apply_symm_apply]
  have hv2 : orderOf v = 2 := by
    have h1 : orderOf ((fS v : S) : G) = orderOf v := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    rw [← h1, hfv]
    have : orderOf (c₁ * u * c₁⁻¹) = orderOf u := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [this, hu2]
  have hvz : v ≠ z n := by
    intro hvz
    apply hut
    have h1 : c₁ * u * c₁⁻¹ = t := by rw [← hfv, hvz, ← t_eq_image_z fS ht]
    have h2 : c₁ * t * c₁⁻¹ = t := by
      have := (Subgroup.mem_centralizer_singleton_iff.mp hc₁)
      calc c₁ * t * c₁⁻¹ = t * c₁ * c₁⁻¹ := by rw [this]
        _ = t := by group
    have : c₁ * u * c₁⁻¹ = c₁ * t * c₁⁻¹ := h1.trans h2.symm
    exact mul_left_cancel (mul_right_cancel this)
  have hconj : IsConj (s n) v := by
    rcases (involution_iff n (by omega) v).mp hv2 with h | ⟨j, hj⟩
    · exact absurd h hvz
    · rw [hj]
      have h := even_outside_conjugate n hn (j.val : ℤ)
      change IsConj (s n) (r n ^ ((2 : ℕ) * j.val : ℤ) * s n) at h
      rw [← Int.natCast_mul, zpow_natCast] at h
      exact h
  obtain ⟨d', hd'⟩ := isConj_iff.mp hconj
  have hdS : ((fS d' : S) : G) ∈ C t := sylow_le_C fS hn ht (fS d').2
  refine ⟨((fS d' : S) : G)⁻¹ * c₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hdS) hc₁, ?_⟩
  have h := congrArg (fun y : SemidihedralGroup n => ((fS y : S) : G)) hd'
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [hfv] at h
  calc ((fS d' : S) : G)⁻¹ * c₁ * u * (((fS d' : S) : G)⁻¹ * c₁)⁻¹ =
      ((fS d' : S) : G)⁻¹ * (c₁ * u * c₁⁻¹) * ((fS d' : S) : G) := by group
    _ = ((fS d' : S) : G)⁻¹ * (((fS d' : S) : G) * ((fS (s n) : S) : G) *
        ((fS d' : S) : G)⁻¹) * ((fS d' : S) : G) := by rw [h]
    _ = ((fS (s n) : S) : G) := by group

theorem s0_mem_C (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) :
    (fS (s n) : G) ∈ C t := sylow_le_C fS hn ht (fS (s n)).2

theorem orderOf_s0 (hn : 4 ≤ n) : orderOf (fS (s n) : G) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_s n (by omega)]

theorem s0_ne_t (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) : (fS (s n) : G) ≠ t := by
  rw [t_eq_image_z fS ht]
  intro h
  have h' : s n = z n := fS.injective (Subtype.ext h)
  rw [s_eq_element n (by omega), z_eq_element n (by omega), element_eq_iff] at h'
  exact absurd h'.2 (by decide)

theorem mem_centralizer_T {x : G} (hxt : x * t = t * x)
    (hxs : x * (fS (s n) : G) = (fS (s n) : G) * x) :
    x ∈ Subgroup.centralizer
      ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro y (rfl | rfl)
  · exact hxt.symm
  · exact hxs.symm

theorem centralizer_T_le_C :
    Subgroup.centralizer ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) ≤ C t := by
  intro x hx
  rw [C, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hx t (Subgroup.subset_closure (by simp))).symm

theorem mem_normalizer_T [Finite G] {η : G}
    (h₁ : η * t * η⁻¹ ∈ (Subgroup.closure {t, (fS (s n) : G)} : Subgroup G))
    (h₂ : η * (fS (s n) : G) * η⁻¹ ∈ (Subgroup.closure {t, (fS (s n) : G)} : Subgroup G)) :
    η ∈ Subgroup.normalizer
      ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hle : Subgroup.closure {t, (fS (s n) : G)} ≤
      (Subgroup.closure {t, (fS (s n) : G)}).comap (MulAut.conj η).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact h₁
    · exact h₂
  exact hle hx

theorem exists_normalizer_s0_to_t [Finite G] (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) :
    ∃ η ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      η * (fS (s n) : G) * η⁻¹ = t := by
  set s₀ : G := (fS (s n) : G) with hs₀
  have hconj : IsConj s₀ t := by
    rw [t_eq_image_z fS ht]
    exact InvolutionFusion.ambient_involution_isConj_z n hn S fS hindex s₀ (orderOf_s0 fS hn)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hts : s₀ * t = t * s₀ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (s0_mem_C fS hn ht))
  set w : G := g * t * g⁻¹ with hw
  have hwC : w ∈ C t := by
    rw [C, Subgroup.mem_centralizer_singleton_iff]
    have h : t * w = w * t := by
      calc t * w = g * s₀ * g⁻¹ * (g * t * g⁻¹) := by rw [hg]
        _ = g * (s₀ * t) * g⁻¹ := by group
        _ = g * (t * s₀) * g⁻¹ := by rw [hts]
        _ = g * t * g⁻¹ * (g * s₀ * g⁻¹) := by group
        _ = w * t := by rw [hg]
    exact h.symm
  have hw2 : orderOf w = 2 := by
    rw [hw, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_t fS hn ht]
  have hwt : w ≠ t := by
    intro h
    apply s0_ne_t fS hn ht
    have : g * t * g⁻¹ = g * s₀ * g⁻¹ := h.trans hg.symm
    exact (mul_left_cancel (mul_right_cancel this)).symm
  obtain ⟨b, hb, hbw⟩ := exists_conj_s0 fS hn ht hwC hw2 hwt
  have hbt : b * t * b⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hb
    calc b * t * b⁻¹ = t * b * b⁻¹ := by rw [this]
      _ = t := by group
  refine ⟨b * g, mem_normalizer_T fS ?_ ?_, ?_⟩
  · have : b * g * t * (b * g)⁻¹ = s₀ := by
      calc b * g * t * (b * g)⁻¹ = b * w * b⁻¹ := by rw [hw]; group
        _ = s₀ := hbw
    rw [this]
    exact Subgroup.subset_closure (by simp [hs₀])
  · have : b * g * s₀ * (b * g)⁻¹ = t := by
      calc b * g * s₀ * (b * g)⁻¹ = b * (g * s₀ * g⁻¹) * b⁻¹ := by group
        _ = t := by rw [hg, hbt]
    rw [this]
    exact Subgroup.subset_closure (by simp)
  · calc b * g * s₀ * (b * g)⁻¹ = b * (g * s₀ * g⁻¹) * b⁻¹ := by group
      _ = t := by rw [hg, hbt]

theorem conj_mem_centralizer_T {η : G} (hη : η ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G)) :
    η * c * η⁻¹ ∈ Subgroup.centralizer
      ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : η⁻¹ * y * η ∈ (Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hη) y).mp hy
    simpa using this
  have := Subgroup.mem_centralizer_iff.mp hc _ hy'
  calc y * (η * c * η⁻¹) = η * ((η⁻¹ * y * η) * c) * η⁻¹ := by group
    _ = η * (c * (η⁻¹ * y * η)) * η⁻¹ := by rw [this]
    _ = η * c * η⁻¹ * y := by group

theorem thetaG_normalizer_invariant (θ : C t →* ℂˣ)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    {η : G} (hη : η ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G))
    {c : G} (hc : c ∈ Subgroup.centralizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G)) :
    thetaG t θ (η * c * η⁻¹) = thetaG t θ c := by
  have hcT := centralizer_T_le_C fS hc
  have hcη := conj_mem_centralizer_T fS hη hc
  rw [thetaG_of_mem θ (centralizer_T_le_C fS hcη), thetaG_of_mem θ hcT]
  exact hθT η hη ⟨c, hcT⟩ ⟨η * c * η⁻¹, centralizer_T_le_C fS hcη⟩ hc rfl

theorem thetaG_conj_special [Finite G] (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (θ : C t →* ℂˣ)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    {Q₀ : Subgroup G} (h₀ : Special t Q₀) {h : G} (hh : Special t (conjSub h Q₀)) {c : G}
    (hc : c ∈ Subgroup.centralizer (Q₀ : Set G)) :
    thetaG t θ (h * c * h⁻¹) = thetaG t θ c := by
  set s₀ : G := (fS (s n) : G) with hs₀
  have hcC : c ∈ C t := by
    rw [C, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc t h₀.1).symm
  set u : G := h⁻¹ * t * h with hu
  have huQ : u ∈ Q₀ := mem_conjSub.mp hh.1
  by_cases hut : u = t
  · have hhC : h ∈ C t := by
      rw [C, Subgroup.mem_centralizer_singleton_iff]
      calc h * t = h * u := by rw [hut]
        _ = t * h := by rw [hu]; group
    exact thetaG_conj θ hhC hcC
  have huC : u ∈ C t := by
    rw [C, Subgroup.mem_centralizer_singleton_iff]
    exact h₀.2 u huQ
  have hu2 : orderOf u = 2 := by
    have : u = (MulAut.conj h⁻¹) t := by simp [hu]
    rw [this, MulEquiv.orderOf_eq, orderOf_t fS hn ht]
  obtain ⟨a, ha, hau⟩ := exists_conj_s0 fS hn ht huC hu2 hut
  set w : G := h * t * h⁻¹ with hw
  have hwQ : w ∈ conjSub h Q₀ := conj_mem_conjSub h₀.1
  have hwC : w ∈ C t := by
    rw [C, Subgroup.mem_centralizer_singleton_iff]
    exact hh.2 w hwQ
  have hw2 : orderOf w = 2 := by
    rw [hw, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_t fS hn ht]
  have hwt : w ≠ t := by
    intro hwt
    apply hut
    rw [hu]
    calc h⁻¹ * t * h = h⁻¹ * (h * t * h⁻¹) * h := by rw [← hw, hwt]
      _ = t := by group
  obtain ⟨b, hb, hbw⟩ := exists_conj_s0 fS hn ht hwC hw2 hwt
  have hat : a * t * a⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp ha
    calc a * t * a⁻¹ = t * a * a⁻¹ := by rw [this]
      _ = t := by group
  have hbt : b * t * b⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hb
    calc b * t * b⁻¹ = t * b * b⁻¹ := by rw [this]
      _ = t := by group
  have hhu : h * u * h⁻¹ = t := by rw [hu]; group
  set η : G := b * h * a⁻¹ with hη
  have hηt : η * t * η⁻¹ = s₀ := by
    have hat' : a⁻¹ * t * a = t := by
      calc a⁻¹ * t * a = a⁻¹ * (a * t * a⁻¹) * a := by rw [hat]
        _ = t := by group
    calc η * t * η⁻¹ = b * h * (a⁻¹ * t * a) * h⁻¹ * b⁻¹ := by rw [hη]; group
      _ = b * w * b⁻¹ := by rw [hat', hw]; group
      _ = s₀ := hbw
  have hηs : η * s₀ * η⁻¹ = t := by
    have has : a⁻¹ * s₀ * a = u := by
      calc a⁻¹ * s₀ * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [hau]
        _ = u := by group
    calc η * s₀ * η⁻¹ = b * h * (a⁻¹ * s₀ * a) * h⁻¹ * b⁻¹ := by rw [hη]; group
      _ = b * (h * u * h⁻¹) * b⁻¹ := by rw [has]; group
      _ = t := by rw [hhu, hbt]
  have hηN : η ∈ Subgroup.normalizer
      ((Subgroup.closure {t, s₀} : Subgroup G) : Set G) := by
    refine mem_normalizer_T fS ?_ ?_
    · rw [hηt]; exact Subgroup.subset_closure (by simp [hs₀])
    · rw [hηs]; exact Subgroup.subset_closure (by simp)
  set c' : G := a * c * a⁻¹ with hc'
  have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp hc u huQ).symm
  have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.mp hc t h₀.1).symm
  have hc'T : c' ∈ Subgroup.centralizer
      ((Subgroup.closure {t, s₀} : Subgroup G) : Set G) := by
    refine mem_centralizer_T fS ?_ ?_
    · calc c' * t = a * c * a⁻¹ * (a * t * a⁻¹) := by rw [hat]
        _ = a * (c * t) * a⁻¹ := by group
        _ = a * (t * c) * a⁻¹ := by rw [hct]
        _ = a * t * a⁻¹ * (a * c * a⁻¹) := by group
        _ = t * c' := by rw [hat]
    · calc c' * s₀ = a * c * a⁻¹ * (a * u * a⁻¹) := by rw [hau]
        _ = a * (c * u) * a⁻¹ := by group
        _ = a * (u * c) * a⁻¹ := by rw [hcu]
        _ = a * u * a⁻¹ * (a * c * a⁻¹) := by group
        _ = s₀ * c' := by rw [hau]
  have hkey := thetaG_normalizer_invariant fS θ hθT hηN hc'T
  have hX : η * c' * η⁻¹ ∈ C t := by
    have hc'C := centralizer_T_le_C fS hc'T
    have : η * c' * η⁻¹ = b * (h * c * h⁻¹) * b⁻¹ := by
      rw [hη, hc']; group
    rw [this]
    have hhc : h * c * h⁻¹ ∈ C t := by
      rw [C, Subgroup.mem_centralizer_singleton_iff]
      calc h * c * h⁻¹ * t = h * (c * u) * h⁻¹ := by rw [hu]; group
        _ = h * (u * c) * h⁻¹ := by rw [hcu]
        _ = t * (h * c * h⁻¹) := by rw [hu]; group
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hhc) (Subgroup.inv_mem _ hb)
  have hhc : h * c * h⁻¹ = b⁻¹ * (η * c' * η⁻¹) * b := by
    rw [hη, hc']; group
  rw [hhc, show b⁻¹ * (η * c' * η⁻¹) * b = b⁻¹ * (η * c' * η⁻¹) * b⁻¹⁻¹ by group,
    thetaG_conj θ (Subgroup.inv_mem _ hb) hX, hkey, hc', thetaG_conj θ ha hcC]

end Setting

theorem exists_central_prime_order [Finite G] {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥) :
    ∃ u ∈ Q, orderOf u = p ∧ ∀ x ∈ Q, x * u = u * x := by
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  have hZ : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hZp : IsPGroup p (Subgroup.center Q) := hQ.to_subgroup _
  have hdvd : p ∣ Nat.card (Subgroup.center Q) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card).ne'
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) p hdvd
  refine ⟨((x : Q) : G), (x : Q).2, ?_, fun y hy => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
    exact congrArg Subtype.val this

section Family

variable [Finite G] {n : ℕ} {S : Sylow 2 G} (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

theorem exists_special_conj (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQ1 : Q ≠ ⊥) : ∃ k : G, Special t (conjSub k Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, huQ, hu2, hucent⟩ := exists_central_prime_order hQ hQ1
  have hconj : IsConj u t := by
    rw [t_eq_image_z fS ht]
    exact InvolutionFusion.ambient_involution_isConj_z n hn S fS hindex u hu2
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  refine ⟨k, ?_, fun y hy => ?_⟩
  · rw [← hk]; exact conj_mem_conjSub huQ
  · have hyQ := mem_conjSub.mp hy
    have h := hucent _ hyQ
    rw [← hk]
    calc y * (k * u * k⁻¹) = k * ((k⁻¹ * y * k) * u) * k⁻¹ := by group
      _ = k * (u * (k⁻¹ * y * k)) * k⁻¹ := by rw [h]
      _ = k * u * k⁻¹ * y := by group

end Family

@[expose] noncomputable def conjHom (t k : G) (Q : Subgroup G) (hk : Special t (conjSub k Q)) :
    Subgroup.centralizer (Q : Set G) →* C t where
  toFun g := ⟨k * g * k⁻¹, conj_mem_C_of_special hk g.2⟩
  map_one' := by ext; simp
  map_mul' g g' := by ext; simp [mul_assoc]

open Classical in
@[expose] noncomputable def family (t : G) (θ : C t →* ℂˣ) (Q : Subgroup G) :
    Subgroup.centralizer (Q : Set G) →* ℂˣ :=
  if h : ∃ k, Special t (conjSub k Q) then θ.comp (conjHom t h.choose Q h.choose_spec) else 1

section FamilyFacts

variable [Finite G] {n : ℕ} {S : Sylow 2 G} (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

theorem family_apply (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (θ : C t →* ℂˣ)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    {Q : Subgroup G} {k : G} (hk : Special t (conjSub k Q))
    (g : Subgroup.centralizer (Q : Set G)) :
    family t θ Q g = thetaG t θ (k * g * k⁻¹) := by
  classical
  have hex : ∃ k, Special t (conjSub k Q) := ⟨k, hk⟩
  have hdef : family t θ Q g = θ (conjHom t hex.choose Q hex.choose_spec g) := by
    rw [family, dite_eq_left hex, MonoidHom.comp_apply]
  rw [hdef, ← thetaG_coe]
  change thetaG t θ (hex.choose * g * hex.choose⁻¹) = _
  have hspec := hex.choose_spec
  have hgc : k * (g : G) * k⁻¹ ∈ Subgroup.centralizer ((conjSub k Q : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ := mem_conjSub.mp hy
    have := Subgroup.mem_centralizer_iff.mp g.2 _ hyQ
    calc y * (k * g * k⁻¹) = k * ((k⁻¹ * y * k) * g) * k⁻¹ := by group
      _ = k * (g * (k⁻¹ * y * k)) * k⁻¹ := by rw [this]
      _ = k * g * k⁻¹ * y := by group
  have hh : Special t (conjSub (hex.choose * k⁻¹) (conjSub k Q)) := by
    rw [← conjSub_mul, inv_mul_cancel_right]
    exact hspec
  have h := thetaG_conj_special fS hn ht θ hθT hk hh hgc
  rw [← h]
  congr 1
  group

theorem thetaG_eq_one_of_isPGroup (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) {x : G}
    (hx : x ∈ C t) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : thetaG t θ x = 1 := by
  obtain ⟨c, hc, hcS⟩ := exists_conj_le_sylow fS hn ht hx2 ((Subgroup.zpowers_le).mpr hx)
  have h1 := hcS x (Subgroup.mem_zpowers x)
  rw [← thetaG_conj θ hc hx,
    thetaG_of_mem θ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx) (Subgroup.inv_mem _ hc))]
  exact hθS _ h1

theorem family_apply_special (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (θ : C t →* ℂˣ)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    {Q : Subgroup G} (hQ : Special t Q) (g : Subgroup.centralizer (Q : Set G)) :
    family t θ Q g = thetaG t θ g := by
  have hQ' : Special t (conjSub 1 Q) := by rw [conjSub_one]; exact hQ
  rw [family_apply fS hn ht θ hθT hQ' g]
  simp

theorem family_compatible (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) (θ : C t →* ℂˣ)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c) :
    CFSG.Wreathed.CompatibleCentralizerFamily 2 (S : Subgroup G)
      (fun g => ((thetaG t θ (g : G) : ℂˣ) : ℂ)) (family t θ) := by
  have hSC := sylow_le_C fS hn ht
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro Q hQ hQ1 z hzQ
    obtain ⟨k, hk⟩ := exists_special_conj fS hn ht hindex hQ hQ1
    rw [family_apply fS hn ht θ hθT hk z]
    exact thetaG_eq_one_of_isPGroup fS hn ht θ hθS (conj_mem_C_of_special hk z.2)
      ((isPGroup_conjSub hQ k).to_le ((Subgroup.zpowers_le).mpr (conj_mem_conjSub hzQ)))
  ·
    intro Q hQ hQ1 h g g' hg'
    obtain ⟨k, hk⟩ := exists_special_conj fS hn ht hindex hQ hQ1
    have hk' : Special t (conjSub (k * h) (Q.map (MulAut.conj h⁻¹).toMonoidHom)) := by
      change Special t (conjSub (k * h) (conjSub h⁻¹ Q))
      rw [← conjSub_mul, mul_inv_cancel_right]
      exact hk
    rw [family_apply fS hn ht θ hθT hk' g', family_apply fS hn ht θ hθT hk g, hg']
    congr 1
    group
  ·
    intro Q Q₁ hQ hQ1 hQ₁ hle g g' hg'
    have hQ₁1 : Q₁ ≠ ⊥ := fun h => hQ1 (eq_bot_iff.mpr (h ▸ hle))
    obtain ⟨k₁, hk₁⟩ := exists_special_conj fS hn ht hindex hQ₁ hQ₁1
    rw [family_apply fS hn ht θ hθT hk₁ g]
    have hmono : conjSub k₁ Q ≤ conjSub k₁ Q₁ := Subgroup.map_mono hle
    by_cases htQ : t ∈ conjSub k₁ Q
    · have hsp : Special t (conjSub k₁ Q) := ⟨htQ, fun x hx => hk₁.2 x (hmono hx)⟩
      rw [family_apply fS hn ht θ hθT hsp g', hg']
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨u, huQ, hu2, hucent⟩ :=
        exists_central_prime_order (isPGroup_conjSub hQ k₁) (conjSub_ne_bot hQ1 k₁)
      have hut : u ≠ t := fun h => htQ (h ▸ huQ)
      have hutc : u * t = t * u := hk₁.2 u (hmono huQ)
      have huC : u ∈ C t := by
        rw [C, Subgroup.mem_centralizer_singleton_iff]
        exact hutc
      obtain ⟨a, ha, hau⟩ := exists_conj_s0 fS hn ht huC hu2 hut
      obtain ⟨η₁, hη₁, hη₁s⟩ := exists_normalizer_s0_to_t fS hn ht hindex
      set η' : G := a⁻¹ * η₁ * a with hη'
      have hat : a * t * a⁻¹ = t := by
        have := Subgroup.mem_centralizer_singleton_iff.mp ha
        calc a * t * a⁻¹ = t * a * a⁻¹ := by rw [this]
          _ = t := by group
      have hη'u : η' * u * η'⁻¹ = t := by
        calc η' * u * η'⁻¹ = a⁻¹ * (η₁ * (a * u * a⁻¹) * η₁⁻¹) * a := by rw [hη']; group
          _ = a⁻¹ * t * a := by rw [hau, hη₁s]
          _ = a⁻¹ * (a * t * a⁻¹) * a := by rw [hat]
          _ = t := by group
      have hm : Special t (conjSub (η' * k₁) Q) := by
        rw [conjSub_mul]
        refine ⟨?_, fun y hy => ?_⟩
        · rw [← hη'u]
          exact conj_mem_conjSub huQ
        · have hyQ := mem_conjSub.mp hy
          have hxu := hucent _ hyQ
          rw [← hη'u]
          calc y * (η' * u * η'⁻¹) = η' * ((η'⁻¹ * y * η') * u) * η'⁻¹ := by group
            _ = η' * (u * (η'⁻¹ * y * η')) * η'⁻¹ := by rw [hxu]
            _ = η' * u * η'⁻¹ * y := by group
      rw [family_apply fS hn ht θ hθT hm g', hg']
      set g₁ : G := k₁ * g * k₁⁻¹ with hg₁
      have hg₁C : g₁ ∈ C t := conj_mem_C_of_special hk₁ g.2
      have hg₁t : g₁ * t = t * g₁ := Subgroup.mem_centralizer_singleton_iff.mp hg₁C
      have hg₁u : g₁ * u = u * g₁ := by
        have huQ₁ : k₁⁻¹ * u * k₁ ∈ Q₁ := mem_conjSub.mp (hmono huQ)
        have := Subgroup.mem_centralizer_iff.mp g.2 _ huQ₁
        calc g₁ * u = k₁ * (g * (k₁⁻¹ * u * k₁)) * k₁⁻¹ := by rw [hg₁]; group
          _ = k₁ * ((k₁⁻¹ * u * k₁) * g) * k₁⁻¹ := by rw [this]
          _ = u * g₁ := by rw [hg₁]; group
      set c' : G := a * g₁ * a⁻¹ with hc'
      have hc'T : c' ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) := by
        refine mem_centralizer_T fS ?_ ?_
        · calc c' * t = a * g₁ * a⁻¹ * (a * t * a⁻¹) := by rw [hat]
            _ = a * (g₁ * t) * a⁻¹ := by group
            _ = a * (t * g₁) * a⁻¹ := by rw [hg₁t]
            _ = a * t * a⁻¹ * (a * g₁ * a⁻¹) := by group
            _ = t * c' := by rw [hat]
        · calc c' * (fS (s n) : G) = a * g₁ * a⁻¹ * (a * u * a⁻¹) := by rw [hau]
            _ = a * (g₁ * u) * a⁻¹ := by group
            _ = a * (u * g₁) * a⁻¹ := by rw [hg₁u]
            _ = a * u * a⁻¹ * (a * g₁ * a⁻¹) := by group
            _ = (fS (s n) : G) * c' := by rw [hau]
      have hX := centralizer_T_le_C fS (conj_mem_centralizer_T fS hη₁ hc'T)
      have heq : η' * k₁ * (g : G) * (η' * k₁)⁻¹ = a⁻¹ * (η₁ * c' * η₁⁻¹) * a⁻¹⁻¹ := by
        rw [hη', hc', hg₁]; group
      rw [heq, thetaG_conj θ (Subgroup.inv_mem _ ha) hX,
        thetaG_normalizer_invariant fS θ hθT hη₁ hc'T, hc', thetaG_conj θ ha hg₁C]
  ·
    intro g
    have hS : Special t (S : Subgroup G) := ⟨t_mem_sylow fS ht, fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hSC hx)⟩
    rw [family_apply_special fS hn ht θ hθT hS g]

end FamilyFacts

end CFSG.Semidihedral.FieldFactorOne
