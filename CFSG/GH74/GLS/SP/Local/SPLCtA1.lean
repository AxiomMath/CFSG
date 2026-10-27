module

public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtA1

theorem antidiag_cyclic {G : Type} [Group G] (E₁ E₂ Y : Subgroup G) (t : G) (e : ℕ)
    (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) (hinf : E₁ ⊓ E₂ = ⊥)
    (hc₁ : IsCyclic ↥E₁) (hc₂ : IsCyclic ↥E₂) (hcard₁ : Nat.card ↥E₁ = e)
    (ht₁ : ∀ a ∈ E₁, t * a * t⁻¹ ∈ E₂) (ht₂ : ∀ a ∈ E₂, t * a * t⁻¹ ∈ E₁)
    (hY : Y ≤ E₁ ⊔ E₂) (hinv : ∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) :
    IsCyclic ↥Y ∧ Nat.card ↥Y ∣ e := by
  have hE₂comm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨g, hg⟩ := hc₂.exists_zpow_surjective
    obtain ⟨i, hi⟩ := hg ⟨x, hx⟩
    obtain ⟨j, hj⟩ := hg ⟨y, hy⟩
    have h : (⟨x, hx⟩ : ↥E₂) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      rw [← hi, ← hj]; exact (Commute.zpow_zpow_self g i j).eq
    exact congrArg Subtype.val h
  let φ : ↥E₁ →* G :=
    MonoidHom.mk' (fun a => (a : G) * (t * (a : G) * t⁻¹)⁻¹) (by
      intro a b
      have hb : t * (b : G) * t⁻¹ ∈ E₂ := ht₁ b b.2
      have ha : t * (a : G) * t⁻¹ ∈ E₂ := ht₁ a a.2
      have h1 : (b : G) * (t * (a : G) * t⁻¹)⁻¹ = (t * (a : G) * t⁻¹)⁻¹ * (b : G) :=
        hcomm b b.2 _ (E₂.inv_mem ha)
      have h2 : (t * (b : G) * t⁻¹)⁻¹ * (t * (a : G) * t⁻¹)⁻¹ =
          (t * (a : G) * t⁻¹)⁻¹ * (t * (b : G) * t⁻¹)⁻¹ :=
        hE₂comm _ (E₂.inv_mem hb) _ (E₂.inv_mem ha)
      calc ((a * b : ↥E₁) : G) * (t * ((a * b : ↥E₁) : G) * t⁻¹)⁻¹
          = (a : G) * (b : G) * ((t * (b : G) * t⁻¹)⁻¹ * (t * (a : G) * t⁻¹)⁻¹) := by
            simp only [Subgroup.coe_mul]; group
        _ = (a : G) * (b : G) * ((t * (a : G) * t⁻¹)⁻¹ * (t * (b : G) * t⁻¹)⁻¹) := by rw [h2]
        _ = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)⁻¹) * (t * (b : G) * t⁻¹)⁻¹ := by group
        _ = (a : G) * ((t * (a : G) * t⁻¹)⁻¹ * (b : G)) * (t * (b : G) * t⁻¹)⁻¹ := by rw [h1]
        _ = ((a : G) * (t * (a : G) * t⁻¹)⁻¹) * ((b : G) * (t * (b : G) * t⁻¹)⁻¹) := by group)
  have hYφ : Y ≤ φ.range := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm (hY hy)
    have h1 := hinv _ hy
    have hta : t * a * t⁻¹ ∈ E₂ := ht₁ a ha
    have htb : t * b * t⁻¹ ∈ E₁ := ht₂ b hb
    have h2 : (t * a * t⁻¹) * (t * b * t⁻¹) = a⁻¹ * b⁻¹ := by
      calc (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
        _ = (a * b)⁻¹ := h1
        _ = (b * a)⁻¹ := by rw [hcomm a ha b hb]
        _ = a⁻¹ * b⁻¹ := mul_inv_rev b a
    have hc' : (t * a * t⁻¹) * (t * b * t⁻¹) = (t * b * t⁻¹) * (t * a * t⁻¹) :=
      (hcomm (t * b * t⁻¹) htb (t * a * t⁻¹) hta).symm
    have h3 : a * (t * b * t⁻¹) = b⁻¹ * (t * a * t⁻¹)⁻¹ := by
      calc a * (t * b * t⁻¹) = a * ((t * b * t⁻¹) * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
        _ = a * ((t * a * t⁻¹) * (t * b * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [← hc']
        _ = a * (a⁻¹ * b⁻¹) * (t * a * t⁻¹)⁻¹ := by rw [h2]
        _ = b⁻¹ * (t * a * t⁻¹)⁻¹ := by group
    have hL : a * (t * b * t⁻¹) ∈ E₁ := E₁.mul_mem ha htb
    have hR : b⁻¹ * (t * a * t⁻¹)⁻¹ ∈ E₂ := E₂.mul_mem (E₂.inv_mem hb) (E₂.inv_mem hta)
    have hbot : a * (t * b * t⁻¹) ∈ E₁ ⊓ E₂ := ⟨hL, h3 ▸ hR⟩
    rw [hinf, Subgroup.mem_bot] at hbot
    have h4 : b⁻¹ * (t * a * t⁻¹)⁻¹ = 1 := h3 ▸ hbot
    have hb_eq : b = (t * a * t⁻¹)⁻¹ := by
      have : b⁻¹ = t * a * t⁻¹ := by
        calc b⁻¹ = (b⁻¹ * (t * a * t⁻¹)⁻¹) * (t * a * t⁻¹) := by group
          _ = t * a * t⁻¹ := by rw [h4, one_mul]
      calc b = (b⁻¹)⁻¹ := (inv_inv b).symm
        _ = (t * a * t⁻¹)⁻¹ := by rw [this]
    exact ⟨⟨a, ha⟩, by simp only [φ, MonoidHom.mk'_apply]; rw [hb_eq]⟩
  have hφcyc : IsCyclic ↥φ.range := isCyclic_of_surjective φ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective φ)
  have hφcard : Nat.card ↥φ.range ∣ e := by
    rw [← hcard₁]; exact Subgroup.card_range_dvd φ
  refine ⟨?_, (Subgroup.card_dvd_of_le hYφ).trans hφcard⟩
  have : IsCyclic ↥(Y.subgroupOf φ.range) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hYφ).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hYφ).surjective

theorem A0_cyclic {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0)
    {u : G} (hu : SPLCtU D u) (hK3 : SPLCenUAt D u)
    (hd : ∃ g : G, g⁻¹ * u * g = u ∧ g⁻¹ * D.z * g = D.t * u ∧ g⁻¹ * D.t * g = D.z * u) :
    IsCyclic ↥(D.Act ⊓ centralizer ({u} : Set G)) ∧
      Nat.card ↥(D.Act ⊓ centralizer ({u} : Set G)) ∣ D.e := by
  obtain ⟨g, hgu, hgz, hgt⟩ := hd
  have htt := t_mul_t' D hs
  have hz2 := z_mul_z' D hs
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu.ord, pow_two] at this
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huz : D.z * u = u * D.z := z_central_in_K D hs (mem_zpowers D.z) u (Ict_le_K D hs hu.mem_I)
  have hut : u * D.t = D.t * u := mem_centralizer_singleton_iff.mp (Ict_le_Ct D hs hu.mem_I)
  have hzt : D.z * D.t = D.t * D.z := z_comm_t' D hs
  have hgu' : g * u * g⁻¹ = u := by
    calc g * u * g⁻¹ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [hgu]
      _ = u := by group
  have hgz' : g * D.z * g⁻¹ = D.t * u := by
    have h1 : D.t = (g * D.z * g⁻¹) * u := by
      calc D.t = g * (g⁻¹ * D.t * g) * g⁻¹ := by group
        _ = g * (D.z * u) * g⁻¹ := by rw [hgt]
        _ = (g * D.z * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * D.z * g⁻¹) * u := by rw [hgu']
    calc g * D.z * g⁻¹ = (g * D.z * g⁻¹) * (u * u) := by rw [hu2, mul_one]
      _ = ((g * D.z * g⁻¹) * u) * u := by group
      _ = D.t * u := by rw [← h1]
  have hgt' : g * D.t * g⁻¹ = D.z * u := by
    have h1 : D.z = (g * D.t * g⁻¹) * u := by
      calc D.z = g * (g⁻¹ * D.z * g) * g⁻¹ := by group
        _ = g * (D.t * u) * g⁻¹ := by rw [hgz]
        _ = (g * D.t * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * D.t * g⁻¹) * u := by rw [hgu']
    calc g * D.t * g⁻¹ = (g * D.t * g⁻¹) * (u * u) := by rw [hu2, mul_one]
      _ = ((g * D.t * g⁻¹) * u) * u := by group
      _ = D.z * u := by rw [← h1]
  set A₀ : Subgroup G := D.Act ⊓ centralizer ({u} : Set G) with hA₀
  set Y : Subgroup G := A₀.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hYmem : ∀ y, y ∈ Y ↔ ∃ a ∈ A₀, y = g⁻¹ * a * g := by
    intro y
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by simp⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by simp⟩
  have hA₀u : ∀ a ∈ A₀, a * u = u * a := fun a ha => mem_centralizer_singleton_iff.mp ha.2
  have hA₀t : ∀ a ∈ A₀, a * D.t = D.t * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (Act_le_Ct D ha.1)
  have hYle : Y ≤ D.C ⊓ centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (hYmem y).mp hy
    have hyu : (g⁻¹ * a * g) * u = u * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * u = g⁻¹ * a * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * (a * u) * g := by rw [hgu']; group
        _ = g⁻¹ * (u * a) * g := by rw [hA₀u a ha]
        _ = g⁻¹ * u * g * (g⁻¹ * a * g) := by group
        _ = u * (g⁻¹ * a * g) := by rw [hgu]
    have hyzu : (g⁻¹ * a * g) * (D.z * u) = (D.z * u) * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * (D.z * u) = (g⁻¹ * a * g) * (g⁻¹ * D.t * g) := by rw [hgt]
        _ = g⁻¹ * (a * D.t) * g := by group
        _ = g⁻¹ * (D.t * a) * g := by rw [hA₀t a ha]
        _ = (g⁻¹ * D.t * g) * (g⁻¹ * a * g) := by group
        _ = (D.z * u) * (g⁻¹ * a * g) := by rw [hgt]
    refine ⟨?_, mem_centralizer_singleton_iff.mpr hyu⟩
    show g⁻¹ * a * g ∈ centralizer ({D.z} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hzuu : D.z * u * u = D.z := by rw [mul_assoc, hu2, mul_one]
    calc (g⁻¹ * a * g) * D.z = (g⁻¹ * a * g) * ((D.z * u) * u) := by rw [hzuu]
      _ = ((g⁻¹ * a * g) * (D.z * u)) * u := by group
      _ = ((D.z * u) * (g⁻¹ * a * g)) * u := by rw [hyzu]
      _ = (D.z * u) * ((g⁻¹ * a * g) * u) := by group
      _ = (D.z * u) * (u * (g⁻¹ * a * g)) := by rw [hyu]
      _ = ((D.z * u) * u) * (g⁻¹ * a * g) := by group
      _ = D.z * (g⁻¹ * a * g) := by rw [hzuu]
  have hYnorm : ∀ c ∈ D.C ⊓ centralizer ({u} : Set G), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    obtain ⟨a, ha, rfl⟩ := (hYmem y).mp hy
    have hcz : c * D.z = D.z * c := mem_centralizer_singleton_iff.mp hc.1
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.mp hc.2
    obtain ⟨c', hc'⟩ : ∃ c' : G, c' = g * c * g⁻¹ := ⟨_, rfl⟩
    have hc't : c' * D.t = D.t * c' := by
      have h1 : c * (D.z * u) = (D.z * u) * c := by
        calc c * (D.z * u) = (c * D.z) * u := by group
          _ = (D.z * c) * u := by rw [hcz]
          _ = D.z * (c * u) := by group
          _ = D.z * (u * c) := by rw [hcu]
          _ = (D.z * u) * c := by group
      have h2 : g * (D.z * u) * g⁻¹ = D.t := by
        calc g * (D.z * u) * g⁻¹ = g * (g⁻¹ * D.t * g) * g⁻¹ := by rw [hgt]
          _ = D.t := by group
      calc c' * D.t = (g * c * g⁻¹) * (g * (D.z * u) * g⁻¹) := by rw [hc', h2]
        _ = g * (c * (D.z * u)) * g⁻¹ := by group
        _ = g * ((D.z * u) * c) * g⁻¹ := by rw [h1]
        _ = (g * (D.z * u) * g⁻¹) * (g * c * g⁻¹) := by group
        _ = D.t * c' := by rw [h2, hc']
    have hc'u : c' * u = u * c' := by
      calc c' * u = (g * c * g⁻¹) * (g * u * g⁻¹) := by rw [hc', hgu']
        _ = g * (c * u) * g⁻¹ := by group
        _ = g * (u * c) * g⁻¹ := by rw [hcu]
        _ = (g * u * g⁻¹) * (g * c * g⁻¹) := by group
        _ = u * c' := by rw [hgu', hc']
    have hmem : c' * a * c'⁻¹ ∈ A₀ := by
      refine ⟨Act_normal D c' (mem_centralizer_singleton_iff.mpr hc't) a ha.1,
        mem_centralizer_singleton_iff.mpr ?_⟩
      have hau := hA₀u a ha
      calc c' * a * c'⁻¹ * u = c' * a * (c'⁻¹ * u) := by group
        _ = c' * a * (u * c'⁻¹) := by
            have : c'⁻¹ * u = u * c'⁻¹ := (show Commute c' u from hc'u).inv_left.eq
            rw [this]
        _ = c' * (a * u) * c'⁻¹ := by group
        _ = c' * (u * a) * c'⁻¹ := by rw [hau]
        _ = (c' * u) * a * c'⁻¹ := by group
        _ = (u * c') * a * c'⁻¹ := by rw [hc'u]
        _ = u * (c' * a * c'⁻¹) := by group
    exact (hYmem _).mpr ⟨c' * a * c'⁻¹, hmem, by rw [hc']; group⟩
  have hcardY : Nat.card ↥Y = Nat.card ↥A₀ :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hYodd : Odd (Nat.card ↥Y) := by
    rw [hcardY]
    exact Odd.of_dvd_nat (Act_odd D) (Subgroup.card_dvd_of_le inf_le_left)
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨a₁, ha₁, rfl⟩ := (hYmem y₁).mp hy₁
    obtain ⟨a₂, ha₂, rfl⟩ := (hYmem y₂).mp hy₂
    calc g⁻¹ * a₁ * g * (g⁻¹ * a₂ * g) = g⁻¹ * (a₁ * a₂) * g := by group
      _ = g⁻¹ * (a₂ * a₁) * g := by rw [Act_comm D hs a₁ ha₁.1 a₂ ha₂.1]
      _ = g⁻¹ * a₂ * g * (g⁻¹ * a₁ * g) := by group
  have hYE : Y ≤ D.Eu u := hK3.fit Y hYle hYnorm hYodd hYcomm
  have hYt : ∀ y ∈ Y, D.t * y * D.t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (hYmem y).mp hy
    have hyu : u * (g⁻¹ * a * g) * u⁻¹ = g⁻¹ * a * g := by
      have := (hYle hy).2
      have h := mem_centralizer_singleton_iff.mp this
      calc u * (g⁻¹ * a * g) * u⁻¹ = ((g⁻¹ * a * g) * u) * u⁻¹ := by rw [← h]
        _ = g⁻¹ * a * g := by group
    have e1 : (D.t * u) * (g⁻¹ * a * g) * (D.t * u)⁻¹ = (g⁻¹ * a * g)⁻¹ := by
      calc (D.t * u) * (g⁻¹ * a * g) * (D.t * u)⁻¹
          = (g⁻¹ * D.z * g) * (g⁻¹ * a * g) * (g⁻¹ * D.z * g)⁻¹ := by rw [hgz]
        _ = g⁻¹ * (D.z * a * D.z⁻¹) * g := by group
        _ = g⁻¹ * a⁻¹ * g := by rw [Act_inv D hs a ha.1]
        _ = (g⁻¹ * a * g)⁻¹ := by group
    have e2 : (D.t * u) * (g⁻¹ * a * g) * (D.t * u)⁻¹ = D.t * (g⁻¹ * a * g) * D.t⁻¹ := by
      calc (D.t * u) * (g⁻¹ * a * g) * (D.t * u)⁻¹
          = D.t * (u * (g⁻¹ * a * g) * u⁻¹) * D.t⁻¹ := by group
        _ = D.t * (g⁻¹ * a * g) * D.t⁻¹ := by rw [hyu]
    rw [← e2, e1]
  obtain ⟨E₁, E₂, hsup, hinf, hcomm, hc₁, hc₂, hcard₁, -, ht₁, ht₂⟩ := hK3.prod
  have hYle' : Y ≤ E₁ ⊔ E₂ := hsup ▸ hYE
  obtain ⟨hYcyc, hYdvd⟩ := antidiag_cyclic E₁ E₂ Y D.t D.e hcomm hinf hc₁ hc₂ hcard₁ ht₁ ht₂ hYle' hYt
  let eA : ↥A₀ ≃* ↥Y :=
    Subgroup.equivMapOfInjective A₀ (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  refine ⟨isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective, ?_⟩
  rw [Nat.card_congr eA.toEquiv]
  exact hYdvd

end CtA1

end CFSG.GH74.GLS.SP.Local
