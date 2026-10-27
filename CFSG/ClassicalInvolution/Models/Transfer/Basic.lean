module

public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open scoped commutatorElement MatrixGroups

variable {G X : Type*} [Group G] [Group X]

@[expose] def KerConjFree (θ : G →* X) (i : G) : Prop :=
  ∀ g z : G, z ∈ θ.ker → g * i * g⁻¹ = z * i → z = 1

@[expose] def KerInvolutionFree (θ : G →* X) : Prop :=
  ∀ z ∈ θ.ker, z * z = 1 → z = 1

variable (θ : G →* X)

theorem commutator_mem_ker {a b : G} (h : Commute (θ a) (θ b)) : ⁅a, b⁆ ∈ θ.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact h

theorem sq_eq_one_of_mul_sq_eq_one {i z : G} (hi : i * i = 1) (hz : z ∈ Subgroup.center G)
    (h : (z * i) * (z * i) = 1) : z * z = 1 := by
  have hzi : i * z = z * i := (Subgroup.mem_center_iff.mp hz i)
  calc z * z = z * z * (i * i) := by rw [hi, mul_one]
    _ = z * (z * i) * i := by simp only [mul_assoc]
    _ = z * (i * z) * i := by rw [hzi]
    _ = (z * i) * (z * i) := by simp only [mul_assoc]
    _ = 1 := h

theorem sq_eq_one_of_conj_eq {g i z : G} (hi : i * i = 1) (hz : z ∈ Subgroup.center G)
    (h : g * i * g⁻¹ = z * i) : z * z = 1 := by
  refine sq_eq_one_of_mul_sq_eq_one hi hz ?_
  rw [← h]
  calc (g * i * g⁻¹) * (g * i * g⁻¹) = g * (i * i) * g⁻¹ := by group
    _ = 1 := by rw [hi]; group

theorem kerConjFree_of_kerInvolutionFree (hker : θ.ker ≤ Subgroup.center G) {i : G}
    (hi : i * i = 1) (h : KerInvolutionFree θ) : KerConjFree θ i :=
  fun _ z hz hg => h z hz (sq_eq_one_of_conj_eq hi (hker hz) hg)

theorem commute_of_commute_map {a b : G} (hb : KerConjFree θ b) (h : Commute (θ a) (θ b)) :
    Commute a b := by
  have hz := commutator_mem_ker θ h
  have h1 : a * b * a⁻¹ = ⁅a, b⁆ * b := by
    rw [commutatorElement_def]
    group
  have := hb a _ hz h1
  exact commutatorElement_eq_one_iff_commute.mp this

section Inj

variable {θ} {L : Subgroup G}

theorem injective_domRestrict (h : ∀ z ∈ L, z ∈ θ.ker → z = 1) :
    Function.Injective (θ.domRestrict L) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  exact Subtype.ext (h x x.2 hx)

noncomputable def mulEquivMap (h : ∀ z ∈ L, z ∈ θ.ker → z = 1) : L ≃* L.map θ :=
  (MonoidHom.ofInjective (injective_domRestrict h)).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range L θ))

theorem mulEquivMap_apply (h : ∀ z ∈ L, z ∈ θ.ker → z = 1) (x : L) :
    ((mulEquivMap h x : L.map θ) : X) = θ x := by
  simp [mulEquivMap, MonoidHom.ofInjective_apply]

theorem orderOf_map_eq_two (h : ∀ z ∈ L, z ∈ θ.ker → z = 1) {i : G} (hi : i ∈ L)
    (h2 : orderOf i = 2) : orderOf (θ i) = 2 := by
  have hi2 : i * i = 1 := by rw [← pow_two]; exact h2 ▸ pow_orderOf_eq_one i
  have hi1 : i ≠ 1 := fun h1 => by simp [h1] at h2
  refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hi2, map_one]) fun h1 => hi1 ?_
  exact h i hi (MonoidHom.mem_ker.mpr h1)

theorem eq_map_of_orderOf_eq_two (hL : ∀ z ∈ L, z ∈ θ.ker → z = 1) {i : G}
    (huniq : ∀ t ∈ L, orderOf t = 2 → t = i) {t : X} (ht : t ∈ L.map θ) (h2 : orderOf t = 2) :
    t = θ i := by
  obtain ⟨y, hy, rfl⟩ := ht
  have hsq : θ y * θ y = 1 := by rw [← pow_two]; exact h2 ▸ pow_orderOf_eq_one (θ y)
  have hy2 : y * y = 1 :=
    hL (y * y) (L.mul_mem hy hy) (MonoidHom.mem_ker.mpr (by rw [map_mul, hsq]))
  have hy1 : y ≠ 1 := fun h1 => by simp [h1] at h2
  exact congrArg θ (huniq y hy (orderOf_eq_prime (by rw [pow_two, hy2]) hy1))

end Inj

theorem centralizer_map_eq (hsurj : Function.Surjective θ) {d : G} (hd : KerConjFree θ d) :
    Subgroup.centralizer ({θ d} : Set X) = (Subgroup.centralizer ({d} : Set G)).map θ := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := hsurj x
    refine ⟨g, ?_, rfl⟩
    have hc : Commute (θ g) (θ d) := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hz := commutator_mem_ker θ hc
    have h1 : g * d * g⁻¹ = ⁅g, d⁆ * d := by
      rw [commutatorElement_def]
      group
    have h2 := hd g _ hz h1
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_commute.mp h2
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]

theorem map_mem_normalizer {J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    θ g ∈ Subgroup.normalizer ((J.map θ : Subgroup X) : Set X) := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hg
  rw [Subgroup.mem_normalizer_iff] at hg hg' ⊢
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (hg y).mp hy, by simp⟩
  · rintro ⟨w, hw, hwx⟩
    have hx : x = θ (g⁻¹ * w * g) := by
      rw [map_mul, map_mul, map_inv, hwx]
      group
    refine ⟨g⁻¹ * w * g, ?_, hx.symm⟩
    simpa using (hg' w).mp hw

theorem isClassicalSL2_map {F : Type*} [Field F] (hsurj : Function.Surjective θ)
    {J : Subgroup G} {d : G} (h : IsClassicalSL2 F J d)
    (hJ : ∀ z ∈ J, z ∈ θ.ker → z = 1) (hd : KerConjFree θ d) :
    IsClassicalSL2 F (J.map θ) (θ d) where
  nonempty_mulEquiv := by
    obtain ⟨e⟩ := h.nonempty_mulEquiv
    exact ⟨(mulEquivMap hJ).symm.trans e⟩
  mem := ⟨d, h.mem, rfl⟩
  orderOf_eq_two := orderOf_map_eq_two hJ h.mem h.orderOf_eq_two
  le_centralizer := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hy)]
  centralizer_le_normalizer := by
    rw [centralizer_map_eq θ hsurj hd]
    rintro _ ⟨g, hg, rfl⟩
    exact map_mem_normalizer θ (h.centralizer_le_normalizer hg)

theorem eq_one_of_mem_ker_of_equiv_sl2 {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hker : θ.ker ≤ Subgroup.center G) {J : Subgroup G} {d : G}
    (e : J ≃* SL(2, F)) (hdJ : d ∈ J) (hord : orderOf d = 2) (hd : θ d ≠ 1) :
    ∀ z ∈ J, z ∈ θ.ker → z = 1 := by
  intro z hz hzk
  have hzc : (⟨z, hz⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hzk) g)
  rw [mem_center_iff_of_equiv_sl2 e] at hzc
  rcases (mem_center_sl2_iff _).mp hzc with h1 | h1
  · have : (⟨z, hz⟩ : J) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · exfalso
    apply hd
    have h2 : (⟨d, hdJ⟩ : J) = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rw [Subgroup.orderOf_mk, hord])
    have h3 : (⟨z, hz⟩ : J) = ⟨d, hdJ⟩ := by
      rw [h2]
      exact e.injective (by rw [h1, MulEquiv.apply_symm_apply])
    have hzd : z = d := congrArg Subtype.val h3
    rw [← hzd]
    exact MonoidHom.mem_ker.mp hzk

theorem eq_one_of_mem_ker_of_isClassicalSL2 {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (hker : θ.ker ≤ Subgroup.center G) {J : Subgroup G} {d : G}
    (h : IsClassicalSL2 F J d) (hd : θ d ≠ 1) : ∀ z ∈ J, z ∈ θ.ker → z = 1 := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact eq_one_of_mem_ker_of_equiv_sl2 θ hodd hker e h.mem h.orderOf_eq_two hd

section Perfect

variable {θ}

theorem commutatorElement_mul_center_left {z : G} (hz : z ∈ Subgroup.center G) (a b : G) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hz'' : ∀ x, z⁻¹ * x = x * z⁻¹ := fun x =>
    (Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hz) x).symm
  have h1 : (a * b * a⁻¹) * z⁻¹ = z⁻¹ * (a * b * a⁻¹) := (hz'' _).symm
  calc ⁅z * a, b⁆ = z * ((a * b * a⁻¹) * z⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = z * (z⁻¹ * (a * b * a⁻¹)) * b⁻¹ := by rw [h1]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def, mul_assoc, mul_inv_cancel_left]

theorem commutatorElement_mul_center_right {z : G} (hz : z ∈ Subgroup.center G) (a b : G) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  calc ⁅a, z * b⁆ = ⁅z * b, a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = ⁅b, a⁆⁻¹ := by rw [commutatorElement_mul_center_left hz]
    _ = ⁅a, b⁆ := commutatorElement_inv _ _

theorem commutatorElement_eq_of_map_eq (hker : θ.ker ≤ Subgroup.center G) {x y m m' : G}
    (hx : θ x = θ m) (hy : θ y = θ m') : ⁅x, y⁆ = ⁅m, m'⁆ := by
  have hxz : x * m⁻¹ ∈ Subgroup.center G :=
    hker (MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hx, mul_inv_cancel]))
  have hyz : y * m'⁻¹ ∈ Subgroup.center G :=
    hker (MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hy, mul_inv_cancel]))
  calc ⁅x, y⁆ = ⁅(x * m⁻¹) * m, (y * m'⁻¹) * m'⁆ := by congr 1 <;> group
    _ = ⁅m, (y * m'⁻¹) * m'⁆ := commutatorElement_mul_center_left hxz _ _
    _ = ⁅m, m'⁆ := commutatorElement_mul_center_right hyz _ _

theorem commutatorElement_mem_subgroup (M : Subgroup G) {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    ⁅a, b⁆ ∈ M := by
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

theorem le_of_map_le_map (hker : θ.ker ≤ Subgroup.center G) {L M : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (h : L.map θ ≤ M.map θ) : L ≤ M := by
  rw [← hperf]
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨m, hm, hxm⟩ := h ⟨x, hx, rfl⟩
  obtain ⟨m', hm', hym⟩ := h ⟨y, hy, rfl⟩
  rw [commutatorElement_eq_of_map_eq hker hxm.symm hym.symm]
  exact commutatorElement_mem_subgroup M hm hm'

theorem eq_of_map_eq_map (hker : θ.ker ≤ Subgroup.center G) {L M : Subgroup G}
    (hL : ⁅L, L⁆ = L) (hM : ⁅M, M⁆ = M) (h : L.map θ = M.map θ) : L = M :=
  le_antisymm (le_of_map_le_map hker hL h.le) (le_of_map_le_map hker hM h.ge)

theorem mem_centralizer_of_map (hker : θ.ker ≤ Subgroup.center G) {L : Subgroup G}
    (hperf : ⁅L, L⁆ = L) {g : G}
    (hg : θ g ∈ Subgroup.centralizer ((L.map θ : Subgroup X) : Set X)) :
    g ∈ Subgroup.centralizer (L : Set G) := by
  have hc : ∀ x ∈ L, ∃ c ∈ Subgroup.center G, g * x * g⁻¹ = c * x := by
    intro x hx
    have h1 : Commute (θ g) (θ x) :=
      (Subgroup.mem_centralizer_iff.mp hg (θ x) ⟨x, hx, rfl⟩).symm
    refine ⟨⁅g, x⁆, hker (commutator_mem_ker θ h1), ?_⟩
    rw [commutatorElement_def]
    group
  have hL : L ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [← hperf]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨ca, hca, hga⟩ := hc a ha
    obtain ⟨cb, hcb, hgb⟩ := hc b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
      have := map_commutatorElement (MulAut.conj g).toMonoidHom a b
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this, hga, hgb, commutatorElement_mul_center_left hca,
        commutatorElement_mul_center_right hcb]
    calc ⁅a, b⁆ * g = (g * ⁅a, b⁆ * g⁻¹) * g := by rw [h1]
      _ = g * ⁅a, b⁆ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hL hx)

theorem mem_normalizer_of_map (hker : θ.ker ≤ Subgroup.center G) {L : Subgroup G}
    (hperf : ⁅L, L⁆ = L) {g : G}
    (hg : θ g ∈ Subgroup.normalizer ((L.map θ : Subgroup X) : Set X)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have key : ∀ g : G, θ g ∈ Subgroup.normalizer ((L.map θ : Subgroup X) : Set X) →
      ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
    intro g hg
    have hconj : ∀ x ∈ L, ∃ y ∈ L, θ (g * x * g⁻¹) = θ y := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_normalizer_iff.mp hg (θ x)).mp ⟨x, hx, rfl⟩
      exact ⟨y, hy, by rw [map_mul, map_mul, map_inv]; exact hyx.symm⟩
    have hle : L ≤ L.comap (MulAut.conj g).toMonoidHom := by
      conv_lhs => rw [← hperf]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      obtain ⟨ya, hya, hya'⟩ := hconj a ha
      obtain ⟨yb, hyb, hyb'⟩ := hconj b hb
      rw [Subgroup.mem_comap]
      have h1 := map_commutatorElement (MulAut.conj g).toMonoidHom a b
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 ⊢
      rw [h1, commutatorElement_eq_of_map_eq hker hya' hyb']
      exact commutatorElement_mem_subgroup L hya hyb
    exact fun x hx => hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have hg' : θ g⁻¹ ∈ Subgroup.normalizer ((L.map θ : Subgroup X) : Set X) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  simpa [mul_assoc] using key g⁻¹ hg' _ hx

end Perfect

section Kernel

variable {θ} {H : Type*} [Group H]

theorem ker_comp_le_center (ρ : H →* G) (hρ : Function.Injective ρ)
    (hker : θ.ker ≤ Subgroup.center G) : (θ.comp ρ).ker ≤ Subgroup.center H := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro h
  apply hρ
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mp hz)) (ρ h)

end Kernel

section Dichotomy

variable {θ} {H : Type*} [Group H]

theorem mem_centralizer_map_iff (hker : θ.ker ≤ Subgroup.center G) {L₁ L₂ : Subgroup G}
    (hperf : ⁅L₁, L₁⁆ = L₁) {i₂ : G} (hi₂ : i₂ ∈ L₂)
    (h : i₂ ∈ Subgroup.centralizer (L₁ : Set G) ↔ ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) :
    θ i₂ ∈ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ↔
      ∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x := by
  constructor
  · intro hmem
    have hcomm := h.mp (mem_centralizer_of_map hker hperf hmem)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · intro hcomm
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx (θ i₂) ⟨i₂, hi₂, rfl⟩

theorem dichotomy_map (hker : θ.ker ≤ Subgroup.center G) {L₁ L₂ : Subgroup G}
    (hperf : ⁅L₁, L₁⁆ = L₁) {i₂ : G} (B₁ B₂ : Subgroup H)
    (h : (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) ∨
      (i₂ ∉ Subgroup.centralizer (L₁ : Set G) ∧
        ∃ ρ : H →* G, Function.Injective ρ ∧ ρ.range = L₁ ⊔ L₂ ∧ B₁.map ρ = L₁ ∧
          B₂.map ρ = L₂)) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        ∃ ρ : H →* X, ρ.ker ≤ Subgroup.center H ∧ ρ.range = L₁.map θ ⊔ L₂.map θ ∧
          B₁.map ρ = L₁.map θ ∧ B₂.map ρ = L₂.map θ) := by
  rcases h with hcomm | ⟨hnot, ρ, hinj, hrange, h₁, h₂⟩
  · left
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · right
    refine ⟨fun hmem => hnot (mem_centralizer_of_map hker hperf hmem), θ.comp ρ,
      ker_comp_le_center ρ hinj hker, ?_, ?_, ?_⟩
    · rw [MonoidHom.range_comp, hrange, Subgroup.map_sup]
    · rw [← Subgroup.map_map, h₁]
    · rw [← Subgroup.map_map, h₂]

end Dichotomy

theorem isSubnormal_subgroupOf_congr {A B L : Subgroup X} (h : A = B)
    (hA : (L.subgroupOf A).IsSubnormal) : (L.subgroupOf B).IsSubnormal := by
  subst h
  exact hA

section SubgroupOf

variable {G' : Type*} [Group G'] {Ω L L₁ L₂ : Subgroup G'}

theorem mem_centralizer_subgroupOf_iff (hL : L ≤ Ω) {g : Ω} :
    g ∈ Subgroup.centralizer ((L.subgroupOf Ω : Subgroup Ω) : Set Ω) ↔
      (g : G') ∈ Subgroup.centralizer (L : Set G') := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hL hx⟩ hx)
  · intro h x hx
    exact Subtype.ext (h x hx)

theorem mem_normalizer_subgroupOf_iff (hL : L ≤ Ω) {g : Ω} :
    g ∈ Subgroup.normalizer ((L.subgroupOf Ω : Subgroup Ω) : Set Ω) ↔
      (g : G') ∈ Subgroup.normalizer (L : Set G') := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ Ω
    · simpa [Subgroup.mem_subgroupOf] using h ⟨x, hx⟩
    · have hgx : (g : G') * x * (g : G')⁻¹ ∉ Ω := fun hmem => hx (by
        have := Ω.mul_mem (Ω.mul_mem (Ω.inv_mem g.2) hmem) g.2
        simpa [mul_assoc] using this)
      exact ⟨fun hxL => absurd (hL hxL) hx, fun hgL => absurd (hL hgL) hgx⟩
  · intro h x
    simpa [Subgroup.mem_subgroupOf] using h (x : G')

theorem forall_comm_subgroupOf_iff (hL₁ : L₁ ≤ Ω) (hL₂ : L₂ ≤ Ω) :
    (∀ x ∈ L₁.subgroupOf Ω, ∀ y ∈ L₂.subgroupOf Ω, x * y = y * x) ↔
      ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  constructor
  · intro h x hx y hy
    exact congrArg Subtype.val (h ⟨x, hL₁ hx⟩ hx ⟨y, hL₂ hy⟩ hy)
  · intro h x hx y hy
    exact Subtype.ext (h x hx y hy)

variable {H : Type*} [Group H]

theorem exists_hom_subgroupOf (hL₁ : L₁ ≤ Ω) (hL₂ : L₂ ≤ Ω) (B₁ B₂ : Subgroup H)
    (θ₀ : H →* G') (hinj : Function.Injective θ₀) (hrange : θ₀.range = L₁ ⊔ L₂)
    (h₁ : B₁.map θ₀ = L₁) (h₂ : B₂.map θ₀ = L₂) :
    ∃ ρ : H →* Ω, Function.Injective ρ ∧ ρ.range = L₁.subgroupOf Ω ⊔ L₂.subgroupOf Ω ∧
      B₁.map ρ = L₁.subgroupOf Ω ∧ B₂.map ρ = L₂.subgroupOf Ω := by
  have hmem : ∀ g, θ₀ g ∈ Ω := fun g =>
    sup_le hL₁ hL₂ (hrange ▸ (⟨g, rfl⟩ : θ₀ g ∈ θ₀.range))
  let ρ : H →* Ω := θ₀.codRestrict Ω hmem
  have hsub : ∀ (S : Subgroup H) (T : Subgroup G'), S.map θ₀ = T → T ≤ Ω →
      S.map ρ = T.subgroupOf Ω := fun S T hST hTΩ => by
    refine Subgroup.map_injective (f := Ω.subtype) Subtype.val_injective ?_
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hTΩ, ← hST]
    rfl
  refine ⟨ρ, fun x y hxy => hinj (congrArg Subtype.val hxy), ?_, hsub _ _ h₁ hL₁, hsub _ _ h₂ hL₂⟩
  rw [MonoidHom.range_eq_map, hsub ⊤ (L₁ ⊔ L₂) (by rw [← MonoidHom.range_eq_map]; exact hrange)
    (sup_le hL₁ hL₂)]
  exact Subgroup.subgroupOf_sup hL₁ hL₂

end SubgroupOf

end CFSG.ClassicalInvolution.Models.Transfer
