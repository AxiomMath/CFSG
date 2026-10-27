module

public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.GH74.GLS.Stage4.T2Defs
public import CFSG.GH74.GLS.Stage4.T2SL2C

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Basic

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite G] in
theorem t2C_zz (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rw [hSet.central.1, sq] at h
  exact h

omit [Finite G] in
theorem t2C_z_ne (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) : z ≠ 1 := by
  intro h
  have := hSet.central.1
  rw [h, orderOf_one] at this
  omega

omit [Finite G] in
theorem t2C_comp_of (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂)
    (hgen₁ : K₁ ≤ Subgroup.closure {x | x ∈ K₁ ∧ Odd (orderOf x)})
    (hgen₂ : K₂ ≤ Subgroup.closure {x | x ∈ K₂ ∧ Odd (orderOf x)}) : T2Comp z K₁ K₂ := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hzz := t2C_zz hSet
  have hz1 := t2C_z_ne hSet
  obtain ⟨e₁⟩ := hSet.iso₁
  obtain ⟨e₂⟩ := hSet.iso₂
  have h4₁ : 4 ≤ Nat.card F₁ := by rw [hSet.card₁]; exact le_trans (by norm_num) hSet.five
  have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card (by rw [hSet.card₁]; exact hSet.odd₁)
  have hzc₁ : ∀ k ∈ K₁, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_left hk))
  have hzc₂ : ∀ k ∈ K₂, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_right hk))
  obtain ⟨hze₁, hZ₁⟩ := t2C_Z_of_sl2 e₁ hz1 hSet.z_mem₁ hzc₁
  obtain ⟨hze₂, hZ₂⟩ := t2C_Z_of_sl2 e₂ hz1 hSet.z_mem₂ hzc₂
  refine ⟨hzz, hz1, hSet.z_mem₁, hSet.z_mem₂, hzc₁, hzc₂, hSet.comm, hSet.inter_eq.le, hZ₁, hZ₂,
    t2C_Q_of_sl2 h4₁ e₁ hSet.z_mem₁ hze₁, t2C_nab_of_sl2 h2₁ hzz e₁ hSet.z_mem₁ hze₁, hgen₁, hgen₂, ?_⟩
  rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv, t2C_card_sl2, t2C_card_sl2,
    hSet.card₁, hSet.card₂]
  exact Nat.mul_le_mul hSet.le (Nat.sub_le_sub_right (Nat.pow_le_pow_left hSet.le 2) 1)

omit [Finite G] in
theorem t2C_K_normal (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {X₁ X₁' X₂ X₂' : Subgroup G}
    (hK₁ : K₁ = X₁ ⊔ X₁') (hK₂ : K₂ = X₂ ⊔ X₂')
    (he₁ : ∀ x ∈ X₁, x ^ q₁.minFac = 1) (he₁' : ∀ x ∈ X₁', x ^ q₁.minFac = 1)
    (he₂ : ∀ x ∈ X₂, x ^ q₂.minFac = 1) (he₂' : ∀ x ∈ X₂', x ^ q₂.minFac = 1) :
    ∀ c ∈ centralizer ({z} : Set G), ∀ x ∈ K₁ ⊔ K₂, c * x * c⁻¹ ∈ K₁ ⊔ K₂ := by
  intro c hc
  have hres := hSet.le_residual
  have hidx := hSet.index_two
  have key : ∀ (X : Subgroup G) (q : ℕ), Odd q → X ≤ K₁ ⊔ K₂ → (∀ x ∈ X, x ^ q.minFac = 1) →
      X ≤ (K₁ ⊔ K₂).comap (MulAut.conj c).toMonoidHom := by
    intro X q hq hX hexp x hx
    have hxC₁ : c * x * c⁻¹ ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
      t2C_oPrimeResidualOf_conj 2 hc (hres (hX hx))
    have hodd : Odd (orderOf (c * x * c⁻¹)) := by
      have h1 : (c * x * c⁻¹) ^ q.minFac = 1 := by rw [conj_pow, hexp x hx]; group
      exact Odd.of_dvd_nat (Odd.of_dvd_nat hq (Nat.minFac_dvd q)) (orderOf_dvd_of_pow_eq_one h1)
    have := t2C_odd_mem_of_index_two hidx hxC₁ hodd
    simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
  have hX₁ : X₁ ≤ K₁ ⊔ K₂ := (hK₁ ▸ le_sup_left : X₁ ≤ K₁).trans le_sup_left
  have hX₁' : X₁' ≤ K₁ ⊔ K₂ := (hK₁ ▸ le_sup_right : X₁' ≤ K₁).trans le_sup_left
  have hX₂ : X₂ ≤ K₁ ⊔ K₂ := (hK₂ ▸ le_sup_left : X₂ ≤ K₂).trans le_sup_right
  have hX₂' : X₂' ≤ K₁ ⊔ K₂ := (hK₂ ▸ le_sup_right : X₂' ≤ K₂).trans le_sup_right
  have hle : K₁ ⊔ K₂ ≤ (K₁ ⊔ K₂).comap (MulAut.conj c).toMonoidHom := by
    calc K₁ ⊔ K₂ = (X₁ ⊔ X₁') ⊔ (X₂ ⊔ X₂') := by rw [← hK₁, ← hK₂]
      _ ≤ _ := sup_le (sup_le (key X₁ q₁ hSet.odd₁ hX₁ he₁) (key X₁' q₁ hSet.odd₁ hX₁' he₁'))
          (sup_le (key X₂ q₂ hSet.odd₂ hX₂ he₂) (key X₂' q₂ hSet.odd₂ hX₂' he₂'))
  intro x hx
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using hle hx

end Basic

section Odd

variable {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G}

theorem t2C_odd_normalizes (hC : T2Comp z K₁ K₂) {m : G} (hmz : m * z = z * m)
    (hK : ∀ x ∈ K₁ ⊔ K₂, m * x * m⁻¹ ∈ K₁ ⊔ K₂) (hK' : ∀ x ∈ K₁ ⊔ K₂, m⁻¹ * x * m ∈ K₁ ⊔ K₂)
    (hodd : Odd (orderOf m)) :
    (∀ x ∈ K₁, m * x * m⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, m * x * m⁻¹ ∈ K₂) := by
  have hmz' : m⁻¹ * z = z * m⁻¹ := by
    have : m⁻¹ * (m * z) * m⁻¹ = m⁻¹ * (z * m) * m⁻¹ := by rw [hmz]
    have h2 : z * m⁻¹ = m⁻¹ * z := by simpa [mul_assoc] using this
    exact h2.symm
  have hZK₁ : Subgroup.zpowers z ≤ K₁ := Subgroup.zpowers_le.2 hC.z₁
  have hZK₂ : Subgroup.zpowers z ≤ K₂ := Subgroup.zpowers_le.2 hC.z₂
  have hmem : ∀ x ∈ K₁, m * x * m⁻¹ ∈ K₁.map (MulAut.conj m).toMonoidHom := fun x hx =>
    ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rcases t2C_conj_K₁ hC hmz hK hK' with hL | hL
  · have hK₁m : ∀ x ∈ K₁, m * x * m⁻¹ ∈ K₁ := by
      intro x hx
      have := hmem x hx
      rwa [hL] at this
    refine ⟨hK₁m, fun y hy => ?_⟩
    have hKy := hK y (Subgroup.mem_sup_right hy)
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hC.comm _).1 hKy
    have hcomm : ∀ k ∈ K₁, (m * y * m⁻¹) * k = k * (m * y * m⁻¹) := by
      intro k hk
      have hkL : k ∈ K₁.map (MulAut.conj m).toMonoidHom := by rw [hL]; exact hk
      obtain ⟨k₀, hk₀, rfl⟩ := hkL
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : y * k₀ = k₀ * y := (hC.comm k₀ hk₀ y hy).symm
      calc m * y * m⁻¹ * (m * k₀ * m⁻¹) = m * (y * k₀) * m⁻¹ := by group
        _ = m * (k₀ * y) * m⁻¹ := by rw [this]
        _ = m * k₀ * m⁻¹ * (m * y * m⁻¹) := by group
    have ha1 : a ∈ Subgroup.zpowers z := by
      refine hC.Z₁ a ha (fun k hk => ?_)
      have h1 := hcomm k hk
      rw [hab] at h1
      have h2 : b * k = k * b := (hC.comm k hk b hb).symm
      calc a * k = a * (k * b) * b⁻¹ := by group
        _ = a * (b * k) * b⁻¹ := by rw [h2]
        _ = (a * b) * k * b⁻¹ := by group
        _ = k * (a * b) * b⁻¹ := by rw [h1]
        _ = k * a := by group
    rw [hab]
    exact K₂.mul_mem (hZK₂ ha1) hb
  · exfalso
    have hi : ∀ y ∈ K₂, m * y * m⁻¹ ∈ K₁ := by
      intro y hy
      have hKy := hK y (Subgroup.mem_sup_right hy)
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hC.comm _).1 hKy
      have hcomm : ∀ k ∈ K₂, (m * y * m⁻¹) * k = k * (m * y * m⁻¹) := by
        intro k hk
        have hkL : k ∈ K₁.map (MulAut.conj m).toMonoidHom := by rw [hL]; exact hk
        obtain ⟨k₀, hk₀, rfl⟩ := hkL
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have : y * k₀ = k₀ * y := (hC.comm k₀ hk₀ y hy).symm
        calc m * y * m⁻¹ * (m * k₀ * m⁻¹) = m * (y * k₀) * m⁻¹ := by group
          _ = m * (k₀ * y) * m⁻¹ := by rw [this]
          _ = m * k₀ * m⁻¹ * (m * y * m⁻¹) := by group
      have hb1 : b ∈ Subgroup.zpowers z := by
        refine hC.Z₂ b hb (fun k hk => ?_)
        have h1 := hcomm k hk
        rw [hab] at h1
        have h2 : a * k = k * a := hC.comm a ha k hk
        calc b * k = a⁻¹ * (a * b * k) := by group
          _ = a⁻¹ * (k * (a * b)) := by rw [h1]
          _ = a⁻¹ * (k * a) * b := by group
          _ = a⁻¹ * (a * k) * b := by rw [h2]
          _ = k * b := by group
      rw [hab]
      exact K₁.mul_mem ha (hZK₁ hb1)
    have hstep : ∀ x ∈ K₁, (m * m) * x * (m * m)⁻¹ ∈ K₁ := by
      intro x hx
      have h1 : m * x * m⁻¹ ∈ K₂ := by
        have := hmem x hx
        rwa [hL] at this
      have := hi _ h1
      have e : (m * m) * x * (m * m)⁻¹ = m * (m * x * m⁻¹) * m⁻¹ := by group
      rwa [e]
    have hiter : ∀ j : ℕ, ∀ x ∈ K₁, (m * m) ^ j * x * ((m * m) ^ j)⁻¹ ∈ K₁ := by
      intro j
      induction j with
      | zero => intro x hx; simpa using hx
      | succ j ih =>
        intro x hx
        have e : (m * m) ^ (j + 1) * x * ((m * m) ^ (j + 1))⁻¹ =
            (m * m) * ((m * m) ^ j * x * ((m * m) ^ j)⁻¹) * (m * m)⁻¹ := by
          rw [pow_succ']; generalize (m * m) ^ j = w; group
        rw [e]
        exact hstep _ (ih x hx)
    obtain ⟨k, hk⟩ := hodd
    have hmpow : (m * m) ^ (k + 1) = m := by
      have h1 : m ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one m
      calc (m * m) ^ (k + 1) = m ^ (2 * k + 1) * m := by
            rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
        _ = m := by rw [h1, one_mul]
    have hm1 : ∀ x ∈ K₁, m * x * m⁻¹ ∈ K₁ := by
      intro x hx
      have := hiter (k + 1) x hx
      rwa [hmpow] at this
    apply hC.nab₁
    intro x hx
    have h1 := hm1 x hx
    have h2 : m * x * m⁻¹ ∈ K₂ := by
      have := hmem x hx
      rwa [hL] at this
    have hg : m * x * m⁻¹ ∈ Subgroup.zpowers z := hC.inter ⟨h1, h2⟩
    have h5 := t2C_conj_zpowers hmz' hg
    rw [inv_inv] at h5
    have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
    rw [e] at h5
    rw [h5]
    exact hg

end Odd

section Center

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Finite G] in
theorem t2C_center_K (hC : T2Comp z K₁ K₂) :
    ∀ x ∈ K₁ ⊔ K₂, (∀ k ∈ K₁ ⊔ K₂, x * k = k * x) → x ∈ Subgroup.zpowers z := by
  intro x hx hcent
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hC.comm x).1 hx
  have ha1 : a ∈ Subgroup.zpowers z := by
    refine hC.Z₁ a ha (fun k hk => ?_)
    have h := hcent k (Subgroup.mem_sup_left hk)
    have h2 : b * k = k * b := (hC.comm k hk b hb).symm
    have : a * k * b = k * a * b := by
      calc a * k * b = a * (k * b) := by group
        _ = a * (b * k) := by rw [h2]
        _ = a * b * k := by group
        _ = k * (a * b) := h
        _ = k * a * b := by group
    exact mul_right_cancel this
  have hb1 : b ∈ Subgroup.zpowers z := by
    refine hC.Z₂ b hb (fun k hk => ?_)
    have h := hcent k (Subgroup.mem_sup_right hk)
    have h2 : a * k = k * a := hC.comm a ha k hk
    have : a * (b * k) = a * (k * b) := by
      calc a * (b * k) = a * b * k := by group
        _ = k * (a * b) := h
        _ = (k * a) * b := by group
        _ = (a * k) * b := by rw [h2]
        _ = a * (k * b) := by group
    exact mul_left_cancel this
  exact Subgroup.mul_mem _ ha1 hb1

omit [Finite G] in
theorem t2C_outer_coset {K C₁ : Subgroup G} (hidx : K.relIndex C₁ = 2) {x y : G} (hx : x ∈ C₁)
    (hy : y ∈ C₁) (hxK : x ∉ K) (hyK : y ∉ K) : x * y⁻¹ ∈ K := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := K.subgroupOf C₁) hidx
    (a := ⟨x, hx⟩) (b := ⟨y, hy⟩⁻¹)
  have h1 : (⟨x, hx⟩ : ↥C₁) ∉ K.subgroupOf C₁ := fun h' => hxK (Subgroup.mem_subgroupOf.1 h')
  have h2 : (⟨y, hy⟩ : ↥C₁)⁻¹ ∉ K.subgroupOf C₁ := by
    intro h'
    apply hyK
    have := Subgroup.mem_subgroupOf.1 h'
    simpa using K.inv_mem this
  have h3 : (⟨x, hx⟩ : ↥C₁) * (⟨y, hy⟩ : ↥C₁)⁻¹ ∈ K.subgroupOf C₁ := h.2 (iff_of_false h1 h2)
  simpa using Subgroup.mem_subgroupOf.1 h3

omit [Finite G] in
theorem t2C_not_cent_K₁ (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC : T2Comp z K₁ K₂) {x : G} (hx : x ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)))
    (hxK : x ∉ K₁ ⊔ K₂) (hcent : ∀ y ∈ K₁, x * y = y * x) : False := by
  have hgen := hRem.gen
  have hidx := hSet.index_two
  have htC₁ : t ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← hgen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htK : t ∉ K₁ ⊔ K₂ := by
    intro htK
    have hle : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ K₁ ⊔ K₂ := by
      rw [← hgen]; exact sup_le le_rfl (Subgroup.zpowers_le.2 htK)
    have h1 : (K₁ ⊔ K₂).relIndex (oPrimeResidualOf 2 (centralizer ({z} : Set G))) = 1 :=
      Subgroup.relIndex_eq_one.2 hle
    rw [h1] at hidx
    exact absurd hidx (by norm_num)
  have hxt : x * t⁻¹ ∈ K₁ ⊔ K₂ := t2C_outer_coset hidx hx htC₁ hxK htK
  obtain ⟨e, g, hns, hact⟩ := hRem.diag₁
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hC.comm _).1 hxt
  have hxe : ∀ y₀ ∈ K₁, t * y₀ * t⁻¹ = a⁻¹ * y₀ * a := by
    intro y₀ hy₀
    have h1 := hcent y₀ hy₀
    have hx' : x = (a * b) * t := by rw [← hab]; group
    rw [hx'] at h1
    have h2 : t * y₀ * t⁻¹ = (a * b)⁻¹ * y₀ * (a * b) := by
      calc t * y₀ * t⁻¹ = (a * b)⁻¹ * ((a * b) * t * y₀) * t⁻¹ := by group
        _ = (a * b)⁻¹ * (y₀ * ((a * b) * t)) * t⁻¹ := by rw [h1]
        _ = (a * b)⁻¹ * y₀ * (a * b) := by group
    rw [h2]
    have hbc : b⁻¹ * (a⁻¹ * y₀ * a) * b = a⁻¹ * y₀ * a := by
      have hw : a⁻¹ * y₀ * a ∈ K₁ := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem ha) hy₀) ha
      have := hC.comm _ hw b hb
      calc b⁻¹ * (a⁻¹ * y₀ * a) * b = b⁻¹ * (b * (a⁻¹ * y₀ * a)) := by rw [← this]; group
        _ = a⁻¹ * y₀ * a := by group
    calc (a * b)⁻¹ * y₀ * (a * b) = b⁻¹ * (a⁻¹ * y₀ * a) * b := by group
      _ = a⁻¹ * y₀ * a := hbc
  apply hns
  have hainv : (e ⟨a⁻¹, K₁.inv_mem ha⟩)⁻¹ = e ⟨a, ha⟩ := by
    rw [← map_inv]
    exact congrArg e (Subtype.ext (by simp))
  refine t2C_isSquare_of_slConj_eq_inner g (e ⟨a⁻¹, K₁.inv_mem ha⟩) ?_
  intro s
  obtain ⟨y₀, rfl⟩ := e.surjective s
  obtain ⟨y, hy1, hy2⟩ := hact y₀
  have hy : y = ⟨a⁻¹, K₁.inv_mem ha⟩ * y₀ * ⟨a, ha⟩ := by
    apply Subtype.ext
    rw [hy1]
    exact hxe y₀ y₀.2
  apply Subtype.ext
  rw [coe_slConj, ← hy2, hy, hainv, map_mul, map_mul]

omit [Finite G] in
theorem t2C_centK_C₁ (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC : T2Comp z K₁ K₂) :
    ∀ x ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)), (∀ k ∈ K₁ ⊔ K₂, x * k = k * x) →
      x ∈ Subgroup.zpowers z := by
  intro x hx hcent
  by_cases hxK : x ∈ K₁ ⊔ K₂
  · exact t2C_center_K hC x hxK hcent
  · exact (t2C_not_cent_K₁ hSet hRem hC hx hxK
      (fun y hy => hcent y (Subgroup.mem_sup_left hy))).elim

omit [Finite G] in
theorem t2C_C₁_normalizes (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    [Finite G] :
    (∀ c ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)), ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧
    (∀ c ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)), ∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂) := by
  have hgen := hRem.gen
  have ht₁ : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₁ := by
    intro x hx
    obtain ⟨e, g, -, hact⟩ := hRem.diag₁
    obtain ⟨y, hy1, -⟩ := hact ⟨x, hx⟩
    rw [← hy1]; exact y.2
  have ht₂ : ∀ x ∈ K₂, t * x * t⁻¹ ∈ K₂ := by
    intro x hx
    obtain ⟨e, g, -, hact⟩ := hRem.diag₂
    obtain ⟨y, hy1, -⟩ := hact ⟨x, hx⟩
    rw [← hy1]; exact y.2
  have h₁ : K₁ ⊔ K₂ ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (K₁ : Set G) := by
    refine sup_le (sup_le (fun k hk => Subgroup.mem_normalizer_fintype (fun x hx => ?_)) ?_) ?_
    · exact K₁.mul_mem (K₁.mul_mem hk hx) (K₁.inv_mem hk)
    · intro k hk
      refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
      have : k * x * k⁻¹ = x := by
        rw [← hcomm x hx k hk]; group
      rw [this]; exact hx
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_normalizer_fintype ht₁
  have h₂ : K₁ ⊔ K₂ ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (K₂ : Set G) := by
    refine sup_le (sup_le ?_ (fun k hk => Subgroup.mem_normalizer_fintype (fun x hx => ?_))) ?_
    · intro k hk
      refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
      have : k * x * k⁻¹ = x := by
        rw [hcomm k hk x hx]; group
      rw [this]; exact hx
    · exact K₂.mul_mem (K₂.mul_mem hk hx) (K₂.inv_mem hk)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_normalizer_fintype ht₂
  rw [hgen] at h₁ h₂
  exact ⟨fun c hc x hx => (Subgroup.mem_normalizer_iff.1 (h₁ hc) x).1 hx,
    fun c hc x hx => (Subgroup.mem_normalizer_iff.1 (h₂ hc) x).1 hx⟩

end Center



end CFSG.GH74.GLS.Stage4.Rest
