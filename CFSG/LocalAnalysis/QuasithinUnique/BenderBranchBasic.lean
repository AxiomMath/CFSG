module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

namespace BenderBranch

section Conj

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjugate_conjugate (H : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate H a) b = CFSG.conjugate H (a * b) := by
  ext x
  simp only [mem_conjugate_iff, mul_inv_rev, mul_assoc]

theorem conjugate_one (H : Subgroup G) : CFSG.conjugate H 1 = H := by
  ext x
  simp [mem_conjugate_iff]

theorem conjugate_inf (H K : Subgroup G) (g : G) :
    CFSG.conjugate (H ⊓ K) g = CFSG.conjugate H g ⊓ CFSG.conjugate K g := by
  ext x
  simp [mem_conjugate_iff]

theorem conjugate_mono {H K : Subgroup G} (h : H ≤ K) (g : G) :
    CFSG.conjugate H g ≤ CFSG.conjugate K g := fun x hx => by
  rw [mem_conjugate_iff] at hx ⊢
  exact h hx

theorem conjugate_inj {H K : Subgroup G} {g : G} :
    CFSG.conjugate H g = CFSG.conjugate K g ↔ H = K := by
  constructor
  · intro h
    ext x
    have := congrArg (fun S => x ∈ CFSG.conjugate S g⁻¹) h
    simpa [conjugate_conjugate, conjugate_one] using this
  · rintro rfl
    rfl

theorem card_conjugate (H : Subgroup G) (g : G) :
    Nat.card ↥(CFSG.conjugate H g) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_eq_iff_mem_normalizer {H : Subgroup G} {g : G} :
    CFSG.conjugate H g = H ↔ g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := SetLike.ext_iff.mp h x
    rw [mem_conjugate_iff] at this
    exact this.symm
  · intro h
    ext x
    rw [mem_conjugate_iff]
    exact (h x).symm

theorem conjugate_centralizer (S : Subgroup G) (g : G) :
    CFSG.conjugate (Subgroup.centralizer (S : Set G)) g =
      Subgroup.centralizer ((CFSG.conjugate S g : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    rw [SetLike.mem_coe, mem_conjugate_iff] at ht
    have h1 := h _ ht
    have h2 : g * (t * x) * g⁻¹ = g * (x * t) * g⁻¹ := by
      calc g * (t * x) * g⁻¹ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * t * g⁻¹) := h1
        _ = g * (x * t) * g⁻¹ := by group
    simpa using h2
  · intro h s hs
    have h1 := h (g⁻¹ * s * g) (by
      rw [SetLike.mem_coe, mem_conjugate_iff]
      simpa [mul_assoc] using hs)
    calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * s := by group

theorem conjugate_centralizer_singleton (u g : G) :
    CFSG.conjugate (Subgroup.centralizer ({u} : Set G)) g =
      Subgroup.centralizer ({g⁻¹ * u * g} : Set G) := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g⁻¹ * u * g) = g⁻¹ * ((g * x * g⁻¹) * u) * g := by group
      _ = g⁻¹ * (u * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * u * g) * x := by group
  · intro h
    calc (g * x * g⁻¹) * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [h]
      _ = u * (g * x * g⁻¹) := by group

end Conj

section Component

variable {G : Type*} [Group G]

theorem isComponentIn_of_isComponent {H : Subgroup G} {L : Subgroup H} (hL : CFSG.IsComponent L) :
    IsComponentIn (L.map H.subtype) H :=
  ⟨Subgroup.map_subtype_le L, by
    have : (L.map H.subtype).subgroupOf H = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    rwa [this]⟩

theorem exists_isComponent_of_isComponentIn {H L : Subgroup G} (hL : IsComponentIn L H) :
    ∃ L' : Subgroup H, CFSG.IsComponent L' ∧ L'.map H.subtype = L :=
  ⟨L.subgroupOf H, hL.2, by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL.1]⟩

theorem isQuasisimple_of_isComponentIn {L H : Subgroup G} (h : IsComponentIn L H) :
    CFSG.IsQuasisimple L :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

theorem isComponentIn_of_le {L K H : Subgroup G} (h : IsComponentIn L H) (hLK : L ≤ K)
    (hKH : K ≤ H) : IsComponentIn L K := by
  refine ⟨hLK, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm
      (isQuasisimple_of_isComponentIn h)
  · have := h.2.2.comap (Subgroup.inclusion hKH)
    convert this using 1
    ext x
    simp [Subgroup.mem_subgroupOf]

theorem eq_or_commute_of_isComponentIn [Finite G] {K L H : Subgroup G} (hK : IsComponentIn K H)
    (hL : IsComponentIn L H) : K = L ∨ ⁅K, L⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute hK.2 hL.2 with h | h
  · left
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at this
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_eq_left.mpr hL.1] at this

theorem isComponentIn_map {L H : Subgroup G} (φ : G ≃* G) (h : IsComponentIn L H) :
    IsComponentIn (L.map φ.toMonoidHom) (H.map φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  have key : (L.map φ.toMonoidHom).subgroupOf (H.map φ.toMonoidHom) =
      (L.subgroupOf H).map (φ.subgroupMap H).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, hly⟩
      obtain ⟨k, hk, hky⟩ := y.2
      have hlk : l = k := φ.injective (hly.trans hky.symm)
      subst hlk
      exact ⟨⟨l, hk⟩, hl, Subtype.ext (by simpa using hly)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
  rw [key]
  exact CFSG.LocalCores.isComponent_map_mulEquiv (φ.subgroupMap H) h.2

theorem eq_one_of_commute_of_simple {L : Subgroup G} (hs : IsSimpleGroup L)
    (hna : ∃ a b : L, a * b ≠ b * a) {x : G} (hx : x ∈ L) (hc : ∀ y ∈ L, y * x = x * y) :
    x = 1 := by
  rcases (Subgroup.center L).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · have : (⟨x, hx⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2)
    rw [h] at this
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : b ∈ Subgroup.center L := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp this a)

end Component

section Sup

variable {G : Type*} [Group G]

theorem mul_mul_inv_eq_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {h k : G} (hh : h ∈ H) (hk : k ∈ K) : h * k * h⁻¹ = k := by
  rw [mul_inv_eq_iff_eq_mul]
  exact hc h hh k hk

theorem mem_sup_iff_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
    {x : G} : x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hle : H ≤ Subgroup.normalizer (K : Set G) := fun h hh => by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rwa [mul_mul_inv_eq_of_commute hc hh hk]
    · intro hk
      have h1 := hc h⁻¹ (H.inv_mem hh) _ hk
      have h2 : h⁻¹ * (h * k * h⁻¹) * h = h * k * h⁻¹ := by
        rw [h1, inv_mul_cancel_right]
      have h3 : k = h⁻¹ * (h * k * h⁻¹) * h := by group
      rw [h3, h2]
      exact hk
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K hle
  rw [← SetLike.mem_coe, this, Set.mem_mul]
  simp

theorem card_sup_of_commute_of_inf_eq_bot [Finite G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : H × K →* G := H.subtype.noncommCoprod K.subtype (fun h k => hc h h.2 k k.2)
  have hf : ∀ p : H × K, f p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hinj : Function.Injective f := by
    intro p q hpq
    rw [hf, hf] at hpq
    have h1 : ((q.1 : G))⁻¹ * (p.1 : G) = (q.2 : G) * ((p.2 : G))⁻¹ := by
      calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * (q.1 * q.2) * (p.2 : G)⁻¹ := by rw [hpq]
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have h2 : ((q.1 : G))⁻¹ * (p.1 : G) ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem q.1.2) p.1.2, h1 ▸ K.mul_mem q.2.2 (K.inv_mem p.2.2)⟩
    rw [hd, Subgroup.mem_bot] at h2
    have h3 : (q.2 : G) * (p.2 : G)⁻¹ = 1 := h1 ▸ h2
    exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp h2).symm)
      (Subtype.ext (mul_inv_eq_one.mp h3).symm)
  have hrange : f.range = H ⊔ K := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hf]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · refine sup_le ?_ ?_
      · intro h hh
        exact ⟨(⟨h, hh⟩, 1), by simp [hf]⟩
      · intro k hk
        exact ⟨(1, ⟨k, hk⟩), by simp [hf]⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofInjective f hinj)).symm

end Sup

section Orbit

variable {G : Type*} [Group G]

theorem card_sub_one_dvd_card_of_transitive [Finite G] {N S : Subgroup G}
    (hN : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S)
    (htrans : ∀ a ∈ S, ∀ b ∈ S, a ≠ 1 → b ≠ 1 → ∃ n ∈ N, n⁻¹ * a * n = b)
    (hS : S ≠ ⊥) : Nat.card S - 1 ∣ Nat.card N := by
  classical
  let X := {s : G // s ∈ S ∧ s ≠ 1}
  let _ : SMul N X := ⟨fun n s => ⟨(n : G) * s * (n : G)⁻¹, hN n n.2 s s.2.1, fun h => s.2.2 (by
    have := congrArg (fun y => (n : G)⁻¹ * y * (n : G)) h
    simpa [mul_assoc] using this)⟩⟩
  have hsmul : ∀ (n : N) (s : X), ((n • s : X) : G) = (n : G) * s * (n : G)⁻¹ := fun n s => rfl
  let _ : MulAction N X :=
    { one_smul := fun s => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun a b s => Subtype.ext (by rw [hsmul, hsmul, hsmul]; simp [mul_assoc]) }
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
  let a₀ : X := ⟨(a : G), a.2, fun h => ha (Subtype.ext h)⟩
  have horb : MulAction.orbit N a₀ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    obtain ⟨n, hn, hnb⟩ := htrans a₀ a₀.2.1 b b.2.1 a₀.2.2 b.2.2
    refine ⟨⟨n⁻¹, N.inv_mem hn⟩, Subtype.ext ?_⟩
    rw [hsmul]
    simpa using hnb
  have hX : Nat.card X = Nat.card S - 1 := by
    have : Nat.card X = ((S : Set G) \ {1}).ncard := by
      rw [← Nat.card_coe_set_eq]
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun s => by simp)
    rw [this, Set.ncard_sdiff_singleton_of_mem S.one_mem, ← Nat.card_coe_set_eq]
    rfl
  have := MulAction.index_stabilizer N a₀
  rw [horb, Set.ncard_univ, hX] at this
  rw [← this]
  exact Subgroup.index_dvd_card (MulAction.stabilizer N a₀)

end Orbit

section Obstruction

variable {G : Type*} [Group G]

theorem commute_of_commutator_eq_bot {H K : Subgroup G} (h : ⁅H, K⁆ = ⊥) {x y : G}
    (hx : x ∈ H) (hy : y ∈ K) : x * y = y * x := by
  have := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy
  exact this.symm

theorem mem_normalizer_of_forall_commute {A : Subgroup G} {y : G}
    (hy : ∀ k ∈ A, y * k = k * y) : y ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : y * h * y⁻¹ = h := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hy h hh
    rwa [this]
  · intro hk
    have h1 := hy _ hk
    have h2 : y * h * y⁻¹ = h := by
      have h3 : y * (y * h * y⁻¹) = y * h := by
        calc y * (y * h * y⁻¹) = (y * h * y⁻¹) * y := h1
          _ = y * h := by group
      exact mul_left_cancel h3
    rwa [h2] at hk

theorem three_commuting_factors_obstruction {G : Type} [Group G] [Finite G]
    (he : CFSG.Assembly.evenRank G ≤ 2) {L₁ L₂ L₃ A₁ : Subgroup G}
    (hZ₁ : ∀ x ∈ L₁, (∀ y ∈ L₁, y * x = x * y) → x = 1)
    (hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, y * x = x * y) → x = 1)
    (h₁₂ : ⁅L₁, L₂⁆ = ⊥) (h₁₃ : ⁅L₁, L₃⁆ = ⊥) (h₂₃ : ⁅L₂, L₃⁆ = ⊥)
    (hA₁ : A₁ ≤ L₁) (hA₁0 : A₁ ≠ ⊥) (hA₁2 : IsPGroup 2 A₁)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd₁ : p ∣ Nat.card ↥(L₁ ⊓ Subgroup.normalizer (A₁ : Set G)))
    (hd₂ : p ∣ Nat.card L₂) (hd₃ : p ∣ Nat.card L₃) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' p hd₁
  obtain ⟨x₂, hx₂⟩ := exists_prime_orderOf_dvd_card' p hd₂
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' p hd₃
  set a₁ : G := (x₁ : G) with ha₁
  set a₂ : G := (x₂ : G) with ha₂
  set a₃ : G := (x₃ : G) with ha₃
  have ho₁ : orderOf a₁ = p := (Subgroup.orderOf_coe x₁).trans hx₁
  have ho₂ : orderOf a₂ = p := (Subgroup.orderOf_coe x₂).trans hx₂
  have ho₃ : orderOf a₃ = p := (Subgroup.orderOf_coe x₃).trans hx₃
  have hP₁ : Subgroup.zpowers a₁ ≤ L₁ ⊓ Subgroup.normalizer (A₁ : Set G) :=
    Subgroup.zpowers_le.mpr x₁.2
  have hP₂ : Subgroup.zpowers a₂ ≤ L₂ := Subgroup.zpowers_le.mpr x₂.2
  have hP₃ : Subgroup.zpowers a₃ ≤ L₃ := Subgroup.zpowers_le.mpr x₃.2
  have c₁₂ : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₂, x * y = y * x :=
    fun x hx y hy => commute_of_commutator_eq_bot h₁₂ (hP₁ hx).1 (hP₂ hy)
  have c₁₃ : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₃, x * y = y * x :=
    fun x hx y hy => commute_of_commutator_eq_bot h₁₃ (hP₁ hx).1 (hP₃ hy)
  have c₂₃ : ∀ x ∈ Subgroup.zpowers a₂, ∀ y ∈ Subgroup.zpowers a₃, x * y = y * x :=
    fun x hx y hy => commute_of_commutator_eq_bot h₂₃ (hP₂ hx) (hP₃ hy)
  let φ₁₂ : Subgroup.zpowers a₁ × Subgroup.zpowers a₂ →* G :=
    (Subgroup.zpowers a₁).subtype.noncommCoprod (Subgroup.zpowers a₂).subtype
      (fun x y => c₁₂ x x.2 y y.2)
  have hφ₁₂ : ∀ p : Subgroup.zpowers a₁ × Subgroup.zpowers a₂, φ₁₂ p = (p.1 : G) * (p.2 : G) :=
    fun p => rfl
  let φ : (Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃ →* G :=
    φ₁₂.noncommCoprod (Subgroup.zpowers a₃).subtype (fun x z => by
      show φ₁₂ x * (z : G) = (z : G) * φ₁₂ x
      rw [hφ₁₂]
      calc (x.1 : G) * x.2 * z = x.1 * (x.2 * z) := by rw [mul_assoc]
        _ = x.1 * (z * x.2) := by rw [c₂₃ _ x.2.2 _ z.2]
        _ = (x.1 * z) * x.2 := by rw [mul_assoc]
        _ = (z * x.1) * x.2 := by rw [c₁₃ _ x.1.2 _ z.2]
        _ = z * (x.1 * x.2) := by rw [mul_assoc])
  have hφ : ∀ q : (Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃,
      φ q = (q.1.1 : G) * (q.1.2 : G) * (q.2 : G) := fun q => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, c⟩ hq
    rw [hφ] at hq
    simp only at hq
    have hcb : ∀ y ∈ L₁, y * ((b : G) * c) = ((b : G) * c) * y := by
      intro y hy
      have hb : y * b = b * y := commute_of_commutator_eq_bot h₁₂ hy (hP₂ b.2)
      have hc : y * c = c * y := commute_of_commutator_eq_bot h₁₃ hy (hP₃ c.2)
      calc y * (b * c) = (y * b) * c := by rw [mul_assoc]
        _ = (b * y) * c := by rw [hb]
        _ = b * (y * c) := by rw [mul_assoc]
        _ = b * (c * y) := by rw [hc]
        _ = (b * c) * y := by rw [mul_assoc]
    have ha : (a : G) = 1 := by
      apply hZ₁ _ (hP₁ a.2).1
      intro y hy
      have hbc := hcb y hy
      have h1 : (a : G) = ((b : G) * c)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rwa [mul_assoc] at hq
      rw [h1]
      exact ((show Commute y ((b : G) * c) from hbc).inv_right).eq
    have hbc1 : (b : G) * c = 1 := by
      rw [ha, one_mul] at hq
      exact hq
    have hb : (b : G) = 1 := by
      apply hZ₂ _ (hP₂ b.2)
      intro y hy
      have hc : y * c = c * y := commute_of_commutator_eq_bot h₂₃ hy (hP₃ c.2)
      have h1 : (b : G) = (c : G)⁻¹ := eq_inv_of_mul_eq_one_left hbc1
      rw [h1]
      exact ((show Commute y (c : G) from hc).inv_right).eq
    have hc1 : (c : G) = 1 := by
      rw [hb, one_mul] at hbc1
      exact hbc1
    exact Prod.ext (Prod.ext (Subtype.ext ha) (Subtype.ext hb)) (Subtype.ext hc1)
  have hcard : Nat.card φ.range = p ^ 3 := by
    have h1 : Nat.card ((Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃) =
        Nat.card φ.range := Nat.card_congr (Equiv.ofInjective φ hinj)
    rw [← h1, Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers,
      ho₁, ho₂, ho₃]
    ring
  have hE : CFSG.Assembly.IsElemAbelian p φ.range := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨q, rfl⟩
    rw [← map_pow]
    have hc1 : Nat.card (Subgroup.zpowers a₁) = p := by rw [Nat.card_zpowers, ho₁]
    have hc2 : Nat.card (Subgroup.zpowers a₂) = p := by rw [Nat.card_zpowers, ho₂]
    have hc3 : Nat.card (Subgroup.zpowers a₃) = p := by rw [Nat.card_zpowers, ho₃]
    have : q ^ p = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · have := (pow_card_eq_one' : q.1.1 ^ Nat.card (Subgroup.zpowers a₁) = 1)
        rwa [hc1] at this
      · have := (pow_card_eq_one' : q.1.2 ^ Nat.card (Subgroup.zpowers a₂) = 1)
        rwa [hc2] at this
      · have := (pow_card_eq_one' : q.2 ^ Nat.card (Subgroup.zpowers a₃) = 1)
        rwa [hc3] at this
    rw [this, map_one]
  have hle : φ.range ≤ Subgroup.normalizer (A₁ : Set G) := by
    rintro _ ⟨q, rfl⟩
    rw [hφ]
    have h1 : (q.1.1 : G) ∈ Subgroup.normalizer (A₁ : Set G) := (hP₁ q.1.1.2).2
    have h2 : (q.1.2 : G) ∈ Subgroup.normalizer (A₁ : Set G) :=
      mem_normalizer_of_forall_commute fun k hk =>
        (commute_of_commutator_eq_bot h₁₂ (hA₁ hk) (hP₂ q.1.2.2)).symm
    have h3 : (q.2 : G) ∈ Subgroup.normalizer (A₁ : Set G) :=
      mem_normalizer_of_forall_commute fun k hk =>
        (commute_of_commutator_eq_bot h₁₃ (hA₁ hk) (hP₃ q.2.2)).symm
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3
  have hrank : 3 ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (A₁ : Set G)) := by
    unfold CFSG.Assembly.pRank
    apply le_csSup
    · refine ⟨Nat.card G, ?_⟩
      rintro k ⟨E, _, _, hk⟩
      calc k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
        _ = Nat.card E := hk.symm
        _ ≤ Nat.card G := Subgroup.card_le_card_group E
    · exact ⟨φ.range, hle, hE, hcard⟩
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (A₁ : Set G)) :=
    ⟨A₁, hA₁0, hA₁2, rfl⟩
  have h3 : CFSG.Assembly.pRank p (Subgroup.normalizer (A₁ : Set G)) ≤
      CFSG.Assembly.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _ hloc
  omega

end Obstruction

end BenderBranch

theorem three_commuting_local_factors_obstruction {G : Type} [Group G] [Finite G]
    (he : CFSG.Assembly.evenRank G ≤ 2) {L₁ L₂ L₃ A₁ A₂ A₃ : Subgroup G}
    (hs₁ : IsSimpleGroup L₁) (hna₁ : ∃ a b : L₁, a * b ≠ b * a)
    (hs₂ : IsSimpleGroup L₂) (hna₂ : ∃ a b : L₂, a * b ≠ b * a)
    (_hs₃ : IsSimpleGroup L₃) (_hna₃ : ∃ a b : L₃, a * b ≠ b * a)
    (h₁₂ : ⁅L₁, L₂⁆ = ⊥) (h₁₃ : ⁅L₁, L₃⁆ = ⊥) (h₂₃ : ⁅L₂, L₃⁆ = ⊥)
    (hA₁ : A₁ ≤ L₁) (_hA₂ : A₂ ≤ L₂) (_hA₃ : A₃ ≤ L₃)
    (hA₁0 : A₁ ≠ ⊥) (_hA₂0 : A₂ ≠ ⊥) (_hA₃0 : A₃ ≠ ⊥)
    (hA₁2 : IsPGroup 2 A₁) (_hA₂2 : IsPGroup 2 A₂) (_hA₃2 : IsPGroup 2 A₃)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd₁ : p ∣ Nat.card ↥(L₁ ⊓ Subgroup.normalizer (A₁ : Set G)))
    (hd₂ : p ∣ Nat.card ↥(L₂ ⊓ Subgroup.normalizer (A₂ : Set G)))
    (hd₃ : p ∣ Nat.card ↥(L₃ ⊓ Subgroup.normalizer (A₃ : Set G))) : False :=
  BenderBranch.three_commuting_factors_obstruction he
    (fun _ hx hc => BenderBranch.eq_one_of_commute_of_simple hs₁ hna₁ hx hc)
    (fun _ hx hc => BenderBranch.eq_one_of_commute_of_simple hs₂ hna₂ hx hc)
    h₁₂ h₁₃ h₂₃ hA₁ hA₁0 hA₁2 hp hp2 hd₁
    (hd₂.trans (Subgroup.card_dvd_of_le inf_le_left))
    (hd₃.trans (Subgroup.card_dvd_of_le inf_le_left))

end CFSG.QuasithinUnique
