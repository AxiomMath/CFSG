module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMY
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup Pointwise

theorem ruG1_conj_mem {G : Type*} [Group G] {U : Subgroup G} {σ : G} {S : Set G}
    (hU : closure S = U) (hS : ∀ s ∈ S, σ * s * σ⁻¹ ∈ U) : ∀ u ∈ U, σ * u * σ⁻¹ ∈ U := by
  have hle : closure S ≤ U.comap (MulAut.conj σ).toMonoidHom := by
    rw [closure_le]
    intro s hs
    exact hS s hs
  rw [hU] at hle
  intro u hu
  exact hle hu

theorem ruG1_closure_three {G : Type*} [Group G] (v ξ g : G) :
    closure ({v, ξ, g} : Set G) = closure ({v, ξ} : Set G) ⊔ zpowers g := by
  apply le_antisymm
  · rw [closure_le]
    rintro y (rfl | rfl | rfl)
    · exact mem_sup_left (subset_closure (Set.mem_insert _ _))
    · exact mem_sup_left (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (closure_mono fun x hx => ?_) ?_
    · rcases hx with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [zpowers_le]
      exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem card_sup_zpowers_two {G : Type*} [Group G] [Finite G] {U : Subgroup G} {g : G}
    (hg2 : g * g = 1) (hgU : g ∉ U) (hn : ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    Nat.card ↥(U ⊔ zpowers g) = 2 * Nat.card ↥U := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hsurj' : ∀ x ∈ U ⊔ zpowers g, ∃ a ∈ U, x = a ∨ x = a * g := by
    intro x hx
    have hnorm : g ∈ normalizer (U : Set G) := by
      rw [mem_normalizer_iff]
      intro a
      refine ⟨fun ha => hn a ha, fun ha => ?_⟩
      have h1 := hn _ ha
      have h2 : g * (g * a * g⁻¹) * g⁻¹ = a := by
        calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g⁻¹ * g⁻¹) := by group
          _ = a := by rw [hg2, hgi, hg2]; group
      rwa [h2] at h1
    have hle : zpowers g ≤ normalizer (U : Set G) := zpowers_le.2 hnorm
    have h := Subgroup.coe_mul_of_right_le_normalizer_left U (zpowers g) hle
    have hx' : x ∈ ((U : Set G) * (zpowers g : Set G)) := by
      rw [← h]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    rcases mem_zpowers_sq_eq_one hg2 hb with rfl | rfl
    · exact ⟨a, ha, Or.inl (mul_one a)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  obtain ⟨f, hf1, hf2⟩ : ∃ f : (↥U ⊕ ↥U) → ↥(U ⊔ zpowers g),
      (∀ a : ↥U, ((f (Sum.inl a) : ↥(U ⊔ zpowers g)) : G) = (a : G)) ∧
      (∀ a : ↥U, ((f (Sum.inr a) : ↥(U ⊔ zpowers g)) : G) = (a : G) * g) :=
    ⟨Sum.elim (fun a => ⟨(a : G), mem_sup_left a.2⟩)
      (fun a => ⟨(a : G) * g, mul_mem (mem_sup_left a.2) (mem_sup_right (mem_zpowers g))⟩),
      fun a => rfl, fun a => rfl⟩
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) h
    · have h1 : (a : G) = (b : G) := by
        have h' := congrArg Subtype.val h
        rwa [hf1, hf1] at h'
      exact congrArg Sum.inl (Subtype.ext h1)
    · exfalso
      have h1 : (a : G) = (b : G) * g := by
        have h' := congrArg Subtype.val h
        rwa [hf1, hf2] at h'
      apply hgU
      have h2 : g = (b : G)⁻¹ * (a : G) := by rw [h1, inv_mul_cancel_left]
      rw [h2]
      exact mul_mem (inv_mem b.2) a.2
    · exfalso
      have h1 : (a : G) * g = (b : G) := by
        have h' := congrArg Subtype.val h
        rwa [hf2, hf1] at h'
      apply hgU
      have h2 : g = (a : G)⁻¹ * (b : G) := by rw [← h1, inv_mul_cancel_left]
      rw [h2]
      exact mul_mem (inv_mem a.2) b.2
    · have h1 : (a : G) * g = (b : G) * g := by
        have h' := congrArg Subtype.val h
        rwa [hf2, hf2] at h'
      exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h1))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, h⟩ := hsurj' x hx
    rcases h with h | h
    · exact ⟨Sum.inl ⟨a, ha⟩, Subtype.ext ((hf1 ⟨a, ha⟩).trans h.symm)⟩
    · exact ⟨Sum.inr ⟨a, ha⟩, Subtype.ext ((hf2 ⟨a, ha⟩).trans h.symm)⟩
  have hcardeq : Nat.card (↥U ⊕ ↥U) = Nat.card ↥(U ⊔ zpowers g) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_sum] at hcardeq
  omega

theorem card_closure_mul_z {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t σ v ξ : G}
    (hz2 : z * z = 1) (hzL : ∀ ℓ ∈ L, z * ℓ = ℓ * z) (hσz : σ * z = z * σ) (hσ2 : σ * σ = 1)
    (hσnot : σ ∉ L ⊔ zpowers z) (hvL : v ∈ L) (hξL : ξ ∈ L) (hv4 : v ^ 4 = t)
    (hσv : σ * v * σ⁻¹ = v * t) (hσξ : σ * ξ * σ⁻¹ = ξ * t)
    (hcard : Nat.card ↥(closure ({v, ξ, σ} : Set G)) = 32) :
    Nat.card ↥(closure ({v, ξ, σ * z} : Set G)) = 32 := by
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G, closure ({v, ξ} : Set G) = U := ⟨_, rfl⟩
  have hUL : U ≤ L := by
    rw [← hU, closure_le]
    rintro y (rfl | rfl)
    · exact hvL
    · exact hξL
  have htU : t ∈ U := by
    rw [← hU, ← hv4]
    exact pow_mem (subset_closure (Set.mem_insert _ _)) 4
  have hvU : v ∈ U := by
    rw [← hU]; exact subset_closure (Set.mem_insert _ _)
  have hξU : ξ ∈ U := by
    rw [← hU]; exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hzv : ∀ ℓ ∈ L, z * ℓ * z⁻¹ = ℓ := fun ℓ hℓ => by
    rw [hzL ℓ hℓ, mul_inv_cancel_right]
  have hσzconj : ∀ ℓ ∈ L, σ * z * ℓ * (σ * z)⁻¹ = σ * ℓ * σ⁻¹ := fun ℓ hℓ => by
    calc σ * z * ℓ * (σ * z)⁻¹ = σ * (z * ℓ * z⁻¹) * σ⁻¹ := by group
      _ = σ * ℓ * σ⁻¹ := by rw [hzv ℓ hℓ]
  have hS_σ : ∀ s ∈ ({v, ξ} : Set G), σ * s * σ⁻¹ ∈ U := by
    intro s hs
    rcases hs with h | h
    · rw [h, hσv]; exact mul_mem hvU htU
    · rw [Set.mem_singleton_iff.1 h, hσξ]; exact mul_mem hξU htU
  have hS_σz : ∀ s ∈ ({v, ξ} : Set G), σ * z * s * (σ * z)⁻¹ ∈ U := by
    intro s hs
    rcases hs with h | h
    · rw [h, hσzconj v hvL, hσv]; exact mul_mem hvU htU
    · rw [Set.mem_singleton_iff.1 h, hσzconj ξ hξL, hσξ]; exact mul_mem hξU htU
  have hnσ : ∀ u ∈ U, σ * u * σ⁻¹ ∈ U := ruG1_conj_mem hU hS_σ
  have hnσz : ∀ u ∈ U, σ * z * u * (σ * z)⁻¹ ∈ U := ruG1_conj_mem hU hS_σz
  have hσU : σ ∉ U := fun h => hσnot (mem_sup_left (hUL h))
  have hσzU : σ * z ∉ U := by
    intro h
    apply hσnot
    have h1 : σ * z ∈ L ⊔ zpowers z := mem_sup_left (hUL h)
    have h2 : z⁻¹ ∈ L ⊔ zpowers z := inv_mem (mem_sup_right (mem_zpowers z))
    have h3 := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at h3
  have hgz2 : σ * z * (σ * z) = 1 := by
    calc σ * z * (σ * z) = σ * (z * σ) * z := by group
      _ = σ * (σ * z) * z := by rw [← hσz]
      _ = (σ * σ) * (z * z) := by group
      _ = 1 := by rw [hσ2, hz2, one_mul]
  have h1 := card_sup_zpowers_two hσ2 hσU hnσ
  have h2 := card_sup_zpowers_two hgz2 hσzU hnσz
  rw [ruG1_closure_three v ξ σ, hU, h1] at hcard
  rw [ruG1_closure_three v ξ (σ * z), hU, h2]
  omega

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem exists_cent_128' {s σ' v ξ : G} (hS : S16Gen S s z t) (hvL : v ∈ L) (hξL : ξ ∈ L)
    (hvt : v * t = t * v) (hξt : ξ * t = t * ξ) (hv4 : v ^ 4 = t) (hvβ : v * β * v⁻¹ = β⁻¹)
    (hξβ : ξ * β * ξ⁻¹ = β⁻¹) (hσβ : σ' * β * σ'⁻¹ = β⁻¹) (hσz : σ' * z = z * σ')
    (hcard : Nat.card ↥(closure ({v, ξ, σ'} : Set G)) = 32) (hσs : σ' * s * σ'⁻¹ = s) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer ((zpowers β : Subgroup G) : Set G) ∧
      s ∈ P ∧ P ≤ centralizer ({s} : Set G) ∧ Nat.card ↥P = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := c.hyp.outerE.cfg
  have ht2 : t * t = 1 := hcfg.t_sq
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : Subgroup G, Y0 = closure ({v, ξ, σ'} : Set G) := ⟨_, rfl⟩
  have hY0card : Nat.card ↥Y0 = 32 := by rw [hY0]; exact hcard
  have hvY : v ∈ Y0 := by rw [hY0]; exact subset_closure (Set.mem_insert _ _)
  have hEB : ∀ w ∈ L ⊓ centralizer ({t} : Set G), w * s = s * w := fun w hw =>
    (mem_centralizer_iff.1 (c.EB_le_centS hw) s hS.hs).symm
  have hvs : v * s = s * v :=
    hEB v ⟨hvL, mem_centralizer_singleton_iff.2 hvt⟩
  have hξs : ξ * s = s * ξ :=
    hEB ξ ⟨hξL, mem_centralizer_singleton_iff.2 hξt⟩
  have hσs' : σ' * s = s * σ' := by
    calc σ' * s = (σ' * s * σ'⁻¹) * σ' := by group
      _ = s * σ' := by rw [hσs]
  have hYcent : Y0 ≤ centralizer ({s} : Set G) := by
    rw [hY0, closure_le]
    rintro g (rfl | rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 hvs
    · exact mem_centralizer_singleton_iff.2 hξs
    · exact mem_centralizer_singleton_iff.2 hσs'
  have hY0z : ∀ y ∈ Y0, y * z = z * y := by
    have : Y0 ≤ centralizer ({z} : Set G) := by
      rw [hY0, closure_le]
      rintro g (rfl | rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A hvL)
      · exact mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A hξL)
      · exact mem_centralizer_singleton_iff.2 hσz
    exact fun y hy => mem_centralizer_singleton_iff.1 (this hy)
  have htS : t ∈ zpowers s := ⟨4, by simpa using hS.hs4⟩
  have htY : t ∈ Y0 := by
    rw [← hv4]; exact pow_mem hvY 4
  have hint : ∀ w ∈ zpowers s, w ∈ Y0 → w = 1 ∨ w = t := by
    intro w hw hwY
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    have hcomm := hY0z _ hwY
    have h1 : z * s ^ k * z⁻¹ = s ^ (-k) := by
      rw [← conj_zpow, hS.hzs, inv_zpow', zpow_neg]
    have h2 : s ^ k = s ^ (-k) := by
      rw [← h1]
      calc s ^ k = z * s ^ k * z⁻¹ := by rw [← hcomm]; group
        _ = z * s ^ k * z⁻¹ := rfl
    have h3 : s ^ (2 * k) = 1 := by
      calc s ^ (2 * k) = s ^ k * s ^ k := by rw [two_mul, zpow_add]
        _ = s ^ k * s ^ (-k) := by rw [← h2]
        _ = 1 := by rw [← zpow_add]; simp
    have h4 : ((orderOf s : ℕ) : ℤ) ∣ 2 * k := (orderOf_dvd_iff_zpow_eq_one).2 h3
    rw [hS.hord] at h4
    obtain ⟨m, rfl⟩ : (4 : ℤ) ∣ k := by omega
    have h5 : s ^ (4 * m) = t ^ m := by
      rw [zpow_mul, ← hS.hs4]
      norm_cast
    rw [h5]
    rcases Int.even_or_odd' m with ⟨r, rfl | rfl⟩
    · left
      have : t ^ (2 * r) = (t ^ 2) ^ r := by rw [zpow_mul]; norm_cast
      rw [this, pow_two, ht2, one_zpow]
    · right
      have : t ^ (2 * r + 1) = (t ^ 2) ^ r * t := by rw [zpow_add, zpow_mul]; simp
      rw [this, pow_two, ht2, one_zpow, one_mul]
  have hSE : zpowers s ≤ centralizer ((Y0 : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hYcent hy)
  have hcard' := card_sup_commuting_two hSE hint ht2 hcfg.t_ne htS htY
  rw [Nat.card_zpowers, hS.hord, hY0card] at hcard'
  refine ⟨zpowers s ⊔ Y0, IsPGroup.of_card (n := 7) (by omega), ?_, mem_sup_left (mem_zpowers s),
    ?_, by omega⟩
  · refine sup_le ?_ ?_
    · rw [zpowers_le]
      refine mem_normalizer_zpowers_of_conj (Or.inl ?_)
      have := c.BS β c.hyp.outerB.beta_mem s hS.hs
      calc s * β * s⁻¹ = (β * s) * s⁻¹ := by rw [this]
        _ = β := by group
    · rw [hY0, closure_le]
      rintro g (rfl | rfl | rfl)
      · exact mem_normalizer_zpowers_of_conj (Or.inr hvβ)
      · exact mem_normalizer_zpowers_of_conj (Or.inr hξβ)
      · exact mem_normalizer_zpowers_of_conj (Or.inr hσβ)
  · refine sup_le ?_ hYcent
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
