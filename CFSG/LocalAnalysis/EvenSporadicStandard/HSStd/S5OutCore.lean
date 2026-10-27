module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5A8

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv

variable {G : Type*} [Group G] {L : Subgroup G} {t : G}

theorem mem_centralizer_of_commute_mul
    (hL : t ∈ centralizer (L : Set G))
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hZ : ∀ l ∈ L, (∀ x ∈ L, x * l = l * x) → l = 1)
    (hNC : ∀ h ∈ normalizer (L : Set G), ∃ c ∈ centralizer ({t} : Set G),
      h * c⁻¹ ∈ centralizer (L : Set G))
    {z : G} (hzL : z ∈ L) {h : G} (hh : h ∈ normalizer (L : Set G))
    (hcomm : h * (t * z) = (t * z) * h) : h ∈ centralizer ({t} : Set G) := by
  obtain ⟨c, hcC, hz'⟩ := hNC h hh
  set z' : G := h * c⁻¹ with hz'def
  have hct : c * t = t * c := mem_centralizer_singleton_iff.1 hcC
  have hcN : c ∈ normalizer (L : Set G) := hC hcC
  have hczL : c * z * c⁻¹ ∈ L := (mem_normalizer_iff.1 hcN z).1 hzL
  have hz'L : ∀ x ∈ L, x * z' = z' * x := fun x hx => mem_centralizer_iff.1 hz' x hx
  have hz'inv : ∀ x ∈ L, x * z'⁻¹ = z'⁻¹ * x := fun x hx => by
    have := hz'L x hx
    calc x * z'⁻¹ = z'⁻¹ * (z' * x) * z'⁻¹ := by group
      _ = z'⁻¹ * (x * z') * z'⁻¹ := by rw [this]
      _ = z'⁻¹ * x := by group
  have hhz : h = z' * c := by rw [hz'def]; group
  have e1 : h * t * h⁻¹ = z' * t * z'⁻¹ := by
    rw [hhz]
    calc z' * c * t * (z' * c)⁻¹ = z' * (c * t * c⁻¹) * z'⁻¹ := by group
      _ = z' * t * z'⁻¹ := by rw [hct]; group
  have e2 : h * z * h⁻¹ = c * z * c⁻¹ := by
    rw [hhz]
    calc z' * c * z * (z' * c)⁻¹ = z' * (c * z * c⁻¹) * z'⁻¹ := by group
      _ = (c * z * c⁻¹) * z' * z'⁻¹ := by rw [← hz'L _ hczL]
      _ = c * z * c⁻¹ := by group
  have e3 : (z' * t * z'⁻¹) * (c * z * c⁻¹) = t * z := by
    have : h * (t * z) * h⁻¹ = t * z := by
      rw [hcomm]; group
    calc (z' * t * z'⁻¹) * (c * z * c⁻¹) = (h * t * h⁻¹) * (h * z * h⁻¹) := by rw [e1, e2]
      _ = h * (t * z) * h⁻¹ := by group
      _ = t * z := this
  set l : G := z * (c * z * c⁻¹)⁻¹ with hl
  have hlL : l ∈ L := L.mul_mem hzL (L.inv_mem hczL)
  have e4 : z' * t * z'⁻¹ = t * l := by
    rw [hl]
    calc z' * t * z'⁻¹ = (z' * t * z'⁻¹) * (c * z * c⁻¹) * (c * z * c⁻¹)⁻¹ := by group
      _ = t * z * (c * z * c⁻¹)⁻¹ := by rw [e3]
      _ = t * (z * (c * z * c⁻¹)⁻¹) := by group
  have hlc : ∀ x ∈ L, x * l = l * x := by
    intro x hx
    have ht' : x * t = t * x := mem_centralizer_iff.1 hL x hx
    have h5 : x * (z' * t * z'⁻¹) = (z' * t * z'⁻¹) * x := by
      calc x * (z' * t * z'⁻¹) = (x * z') * t * z'⁻¹ := by group
        _ = (z' * x) * t * z'⁻¹ := by rw [hz'L x hx]
        _ = z' * (x * t) * z'⁻¹ := by group
        _ = z' * (t * x) * z'⁻¹ := by rw [ht']
        _ = z' * t * (x * z'⁻¹) := by group
        _ = z' * t * (z'⁻¹ * x) := by rw [hz'inv x hx]
        _ = (z' * t * z'⁻¹) * x := by group
    rw [e4] at h5
    calc x * l = t⁻¹ * (x * t) * l := by rw [ht']; group
      _ = t⁻¹ * (x * (t * l)) := by group
      _ = t⁻¹ * ((t * l) * x) := by rw [h5]
      _ = l * x := by group
  have hl1 : l = 1 := hZ l hlL hlc
  rw [hl1, mul_one] at e4
  have hz't : z' * t = t * z' := by
    calc z' * t = (z' * t * z'⁻¹) * z' := by group
      _ = t * z' := by rw [e4]
  have hz'C : z' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hz't
  rw [hhz]
  exact (centralizer ({t} : Set G)).mul_mem hz'C hcC

section Core

variable {v z s : G} (ψ : Perm (Fin 8) →* G)

theorem conj_mem_of_commute
    (hgen : (alternatingGroup (Fin 8)).map ψ ⊔
      ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom = L)
    (hv : s * v * s⁻¹ = v * z)
    (hΛ : ∀ g : G, v * g = g * v → ∀ l ∈ (alternatingGroup (Fin 8)).map ψ,
      g * l * g⁻¹ ∈ (alternatingGroup (Fin 8)).map ψ)
    {g : G} (hgv : v * g = g * v) (hgz : z * g = g * z) : ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  set Λ := (alternatingGroup (Fin 8)).map ψ with hΛdef
  set K : Subgroup G := L.comap (MulAut.conj g).toMonoidHom with hK
  have hΛL : Λ ≤ L := hgen ▸ le_sup_left
  have hΛ₂L : Λ.map (MulAut.conj s).toMonoidHom ≤ L := hgen ▸ le_sup_right
  have h1 : Λ ≤ K := fun l hl => hΛL (hΛ g hgv l hl)
  have h2 : Λ.map (MulAut.conj s).toMonoidHom ≤ K := by
    rintro _ ⟨l, hl, rfl⟩
    have hg₂ : v * (s⁻¹ * g * s) = (s⁻¹ * g * s) * v := by
      have h3 : (v * z) * g = g * (v * z) := by
        calc v * z * g = v * (z * g) := by group
          _ = v * (g * z) := by rw [hgz]
          _ = (v * g) * z := by group
          _ = (g * v) * z := by rw [hgv]
          _ = g * (v * z) := by group
      have h4 : (s * v * s⁻¹) * g = g * (s * v * s⁻¹) := by rw [hv]; exact h3
      calc v * (s⁻¹ * g * s) = s⁻¹ * ((s * v * s⁻¹) * g) * s := by group
        _ = s⁻¹ * (g * (s * v * s⁻¹)) * s := by rw [h4]
        _ = (s⁻¹ * g * s) * v := by group
    have h5 := hΛ _ hg₂ l hl
    have h6 : (MulAut.conj g).toMonoidHom ((MulAut.conj s).toMonoidHom l) =
        (MulAut.conj s).toMonoidHom ((s⁻¹ * g * s) * l * (s⁻¹ * g * s)⁻¹) := by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    show (MulAut.conj g).toMonoidHom ((MulAut.conj s).toMonoidHom l) ∈ L
    rw [h6]
    exact hΛ₂L ⟨_, h5, rfl⟩
  have h3 : Λ ⊔ Λ.map (MulAut.conj s).toMonoidHom ≤ K := sup_le h1 h2
  intro l hl
  have : l ∈ K := h3 (hgen ▸ hl)
  simpa [hK, MulAut.conj_apply] using this

theorem mem_normalizer_of_normal
    (hψ : Function.Injective ψ) (hrange : ψ.range = centralizer ({v} : Set G) ⊓ L)
    {σ₀ : Perm (Fin 8)} (hσ₀ : σ₀ ∈ alternatingGroup (Fin 8)) (hz : ψ σ₀ = z)
    {κ : Perm (Fin 8)} (hκ : κ ∉ alternatingGroup (Fin 8)) (hκz : ψ κ * z = z * ψ κ)
    (hgen : (alternatingGroup (Fin 8)).map ψ ⊔
      ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom = L)
    (hv : s * v * s⁻¹ = v * z)
    (hN : (((alternatingGroup (Fin 8)).map ψ).subgroupOf (centralizer ({v} : Set G))).Normal)
    {g : G} (hg : g ∈ centralizer ({v} : Set G)) : g ∈ normalizer (L : Set G) := by
  classical
  set A := alternatingGroup (Fin 8) with hA
  set Λ := A.map ψ with hΛdef
  set H := centralizer ({v} : Set G) with hH
  have hψmem : ∀ σ, ψ σ ∈ H ⊓ L := fun σ => hrange ▸ ⟨σ, rfl⟩
  have hψH : ∀ σ, ψ σ ∈ H := fun σ => (hψmem σ).1
  have hψL : ∀ σ, ψ σ ∈ L := fun σ => (hψmem σ).2
  have hΛH : ∀ l ∈ Λ, l ∈ H := by
    rintro _ ⟨a, -, rfl⟩
    exact hψH a
  have hΛ : ∀ g : G, v * g = g * v → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ := by
    intro g hgv l hl
    have hgH : g ∈ H := mem_centralizer_singleton_iff.2 hgv.symm
    have := hN.conj_mem ⟨l, hΛH l hl⟩ (mem_subgroupOf.2 hl) ⟨g, hgH⟩
    exact mem_subgroupOf.1 this
  let ψ' : Perm (Fin 8) →* H := ψ.codRestrict H hψH
  have hψ' : Function.Injective ψ' := fun a b h => hψ (congrArg Subtype.val h)
  have hmapeq : A.map ψ' = Λ.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mem_subgroupOf.2 ⟨a, ha, rfl⟩
    · intro hx
      obtain ⟨a, ha, hax⟩ := mem_subgroupOf.1 hx
      exact ⟨a, ha, Subtype.ext hax⟩
  have hN' : (A.map ψ').Normal := hmapeq ▸ hN
  obtain ⟨σ, hσ⟩ := exists_conj_perm_eight ψ' hψ' hN' ⟨g, hg⟩
  have hσ' : ∀ l ∈ Λ, g * l * g⁻¹ = ψ σ * l * (ψ σ)⁻¹ := by
    intro l hl
    have := hσ ⟨l, hΛH l hl⟩ (hmapeq ▸ mem_subgroupOf.2 hl)
    exact congrArg Subtype.val this
  obtain ⟨a, ha, k, hkz, hak⟩ : ∃ a ∈ A, ∃ k : Perm (Fin 8), ψ k * z = z * ψ k ∧ σ = a * k := by
    by_cases hσA : σ ∈ A
    · exact ⟨σ, hσA, 1, by simp, by simp⟩
    · exact ⟨σ * κ⁻¹, mul_inv_mem_alternatingGroup hσA hκ, κ, hκz, by simp⟩
  set h0 : G := (ψ σ)⁻¹ * g with hh0
  have hzΛ : z ∈ Λ := ⟨σ₀, hσ₀, hz⟩
  have hh0c : ∀ l ∈ Λ, h0 * l = l * h0 := by
    intro l hl
    have := hσ' l hl
    rw [hh0]
    calc (ψ σ)⁻¹ * g * l = (ψ σ)⁻¹ * (g * l * g⁻¹) * g := by group
      _ = (ψ σ)⁻¹ * (ψ σ * l * (ψ σ)⁻¹) * g := by rw [this]
      _ = l * ((ψ σ)⁻¹ * g) := by group
  have hcvσ : Commute v (ψ σ) :=
    (show Commute (ψ σ) v from mem_centralizer_singleton_iff.1 (hψH σ)).symm
  have hcvg : Commute v g := (show Commute g v from mem_centralizer_singleton_iff.1 hg).symm
  have hcvk : Commute v (ψ k) :=
    (show Commute (ψ k) v from mem_centralizer_singleton_iff.1 (hψH k)).symm
  have hcvh0 : Commute v h0 := hcvσ.inv_right.mul_right hcvg
  have hczk : Commute z (ψ k) := hkz.symm
  have hczh0 : Commute z h0 := (hh0c z hzΛ).symm
  set g₁ : G := ψ k * h0 with hg₁
  have hgv : v * g₁ = g₁ * v := (hcvk.mul_right hcvh0).eq
  have hgz : z * g₁ = g₁ * z := (hczk.mul_right hczh0).eq
  have hmaps : ∀ g : G, v * g = g * v → z * g = g * z → ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
    fun g hgv hgz => conj_mem_of_commute ψ hgen hv hΛ hgv hgz
  have hg₁N : g₁ ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hmaps g₁ hgv hgz h, fun hh => ?_⟩
    have hv' : v * g₁⁻¹ = g₁⁻¹ * v := (Commute.inv_right (show Commute v g₁ from hgv)).eq
    have hz' : z * g₁⁻¹ = g₁⁻¹ * z := (Commute.inv_right (show Commute z g₁ from hgz)).eq
    have := hmaps g₁⁻¹ hv' hz' _ hh
    simpa [mul_assoc] using this
  have hgeq : g = ψ a * g₁ := by
    have : ψ σ = ψ a * ψ k := by rw [hak, map_mul]
    have e1 : g = ψ σ * h0 := by rw [hh0]; group
    calc g = ψ σ * h0 := e1
      _ = ψ a * ψ k * h0 := by rw [this]
      _ = ψ a * g₁ := by rw [hg₁, mul_assoc]
  rw [hgeq]
  exact (normalizer (L : Set G)).mul_mem (le_normalizer (hψL a)) hg₁N


end Core

theorem not_normal_of_data
    (hL : t ∈ centralizer (L : Set G)) (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hZ : ∀ l ∈ L, (∀ x ∈ L, x * l = l * x) → l = 1)
    (hNC : ∀ h ∈ normalizer (L : Set G), ∃ c ∈ centralizer ({t} : Set G),
      h * c⁻¹ ∈ centralizer (L : Set G))
    {S : Subgroup G} {n v s z : G} (hzL : z ∈ L) (hn : n ∈ normalizer (S : Set G))
    (hnt : n * t * n⁻¹ = z * t) (hvS : v ∈ S) (hv2 : v * v = 1) (hvN : v ∉ L ⊔ zpowers t)
    (hv : s * v * s⁻¹ = v * z) (ψ : Perm (Fin 8) →* G) (hψ : Function.Injective ψ)
    (hrange : ψ.range = centralizer ({v} : Set G) ⊓ L)
    {σ₀ : Perm (Fin 8)} (hσ₀ : σ₀ ∈ alternatingGroup (Fin 8)) (hz : ψ σ₀ = z)
    {κ : Perm (Fin 8)} (hκ : κ ∉ alternatingGroup (Fin 8)) (hκz : ψ κ * z = z * ψ κ)
    (hgen : (alternatingGroup (Fin 8)).map ψ ⊔
      ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom = L)
    (hno5 : ∀ u ∈ centralizer ({t} : Set G), u * v = v * u → u * z = z * u → u ^ 5 = 1 → u = 1)
    (hfive : ∀ x ∈ S, x * x = 1 → x ≠ 1 → x ≠ t →
      ∃ u ∈ centralizer ({t} : Set G), u ^ 5 = 1 ∧ u ≠ 1 ∧ u * x = x * u) :
    ¬ (((alternatingGroup (Fin 8)).map ψ).subgroupOf (centralizer ({v} : Set G))).Normal := by
  intro hN
  set x : G := n⁻¹ * v * n with hx
  have hxS : x ∈ S := by
    refine (mem_normalizer_iff.1 hn x).2 ?_
    have : n * x * n⁻¹ = v := by rw [hx]; group
    rw [this]
    exact hvS
  have hx2 : x * x = 1 := by
    calc x * x = n⁻¹ * (v * v) * n := by rw [hx]; group
      _ = 1 := by rw [hv2]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply hvN
    have : v = 1 := by
      calc v = n * x * n⁻¹ := by rw [hx]; group
        _ = 1 := by rw [h]; group
    rw [this]
    exact one_mem _
  have hxt : x ≠ t := by
    intro h
    apply hvN
    have : v = z * t := by
      calc v = n * x * n⁻¹ := by rw [hx]; group
        _ = z * t := by rw [h, hnt]
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_left hzL) (mem_sup_right (mem_zpowers t))
  obtain ⟨u, huC, hu5, hu1, hux⟩ := hfive x hxS hx2 hx1 hxt
  set u' : G := n * u * n⁻¹ with hu'
  have hu'v : u' * v = v * u' := by
    have hvx : v = n * x * n⁻¹ := by rw [hx]; group
    calc u' * v = n * (u * x) * n⁻¹ := by rw [hu', hvx]; group
      _ = n * (x * u) * n⁻¹ := by rw [hux]
      _ = v * u' := by rw [hu', hvx]; group
  have hut : u * t = t * u := mem_centralizer_singleton_iff.1 huC
  have hzt : z * t = t * z := mem_centralizer_iff.1 hL z hzL
  have hu'tz : u' * (t * z) = (t * z) * u' := by
    rw [← hzt, ← hnt]
    calc u' * (n * t * n⁻¹) = n * (u * t) * n⁻¹ := by rw [hu']; group
      _ = n * (t * u) * n⁻¹ := by rw [hut]
      _ = n * t * n⁻¹ * u' := by rw [hu']; group
  have hu'H : u' ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 hu'v
  have hu'N : u' ∈ normalizer (L : Set G) :=
    mem_normalizer_of_normal ψ hψ hrange hσ₀ hz hκ hκz hgen hv hN hu'H
  have hu'C : u' ∈ centralizer ({t} : Set G) :=
    mem_centralizer_of_commute_mul hL hC hZ hNC hzL hu'N hu'tz
  have hu't : u' * t = t * u' := mem_centralizer_singleton_iff.1 hu'C
  have hu'z : u' * z = z * u' := by
    have h1 : Commute u' t := hu't
    have h2 : Commute u' (t * z) := hu'tz
    have h3 : Commute u' (t⁻¹ * (t * z)) := h1.inv_right.mul_right h2
    simpa using h3.eq
  have hu'5 : u' ^ 5 = 1 := by
    rw [hu', conj_pow, hu5]
    group
  have := hno5 u' hu'C hu'v hu'z hu'5
  apply hu1
  calc u = n⁻¹ * u' * n := by rw [hu']; group
    _ = 1 := by rw [this]; group

theorem not_normal_mul_of_data
    (hL : t ∈ centralizer (L : Set G)) (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hZ : ∀ l ∈ L, (∀ x ∈ L, x * l = l * x) → l = 1)
    (hNC : ∀ h ∈ normalizer (L : Set G), ∃ c ∈ centralizer ({t} : Set G),
      h * c⁻¹ ∈ centralizer (L : Set G))
    {S : Subgroup G} {n v s z : G} (hzL : z ∈ L) (hn : n ∈ normalizer (S : Set G))
    (hnt : n * t * n⁻¹ = z * t) (hSC : S ≤ centralizer ({t} : Set G)) (htS : t ∈ S)
    (ht2 : t * t = 1) (hvS : v ∈ S) (hv2 : v * v = 1) (hvN : v ∉ L ⊔ zpowers t) (hsS : s ∈ S)
    (hv : s * v * s⁻¹ = v * z) (ψ : Perm (Fin 8) →* G) (hψ : Function.Injective ψ)
    (hrange : ψ.range = centralizer ({v} : Set G) ⊓ L)
    {σ₀ : Perm (Fin 8)} (hσ₀ : σ₀ ∈ alternatingGroup (Fin 8)) (hz : ψ σ₀ = z)
    {κ : Perm (Fin 8)} (hκ : κ ∉ alternatingGroup (Fin 8)) (hκz : ψ κ * z = z * ψ κ)
    (hgen : (alternatingGroup (Fin 8)).map ψ ⊔
      ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj s).toMonoidHom = L)
    (hno5 : ∀ u ∈ centralizer ({t} : Set G), u * v = v * u → u * z = z * u → u ^ 5 = 1 → u = 1)
    (hfive : ∀ x ∈ S, x * x = 1 → x ≠ 1 → x ≠ t →
      ∃ u ∈ centralizer ({t} : Set G), u ^ 5 = 1 ∧ u ≠ 1 ∧ u * x = x * u) :
    ¬ (((alternatingGroup (Fin 8)).map ψ).subgroupOf (centralizer ({t * v} : Set G))).Normal := by
  have hvt : t * v = v * t := (mem_centralizer_singleton_iff.1 (hSC hvS)).symm
  have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (hSC hsS)
  have hcl : ∀ g : G, g ∈ centralizer (L : Set G) → ∀ l ∈ L, l * g = g * l :=
    fun g hg l hl => mem_centralizer_iff.1 hg l hl
  have hcomm_tv : ∀ u : G, u * t = t * u → (u * (t * v) = (t * v) * u ↔ u * v = v * u) := by
    intro u hu
    constructor
    · intro h
      have h1 : t * (u * v) = t * (v * u) := by
        calc t * (u * v) = u * (t * v) := by rw [← mul_assoc, ← hu, mul_assoc]
          _ = (t * v) * u := h
          _ = t * (v * u) := by rw [mul_assoc]
      exact mul_left_cancel h1
    · intro h
      calc u * (t * v) = (u * t) * v := by rw [mul_assoc]
        _ = t * (u * v) := by rw [hu, mul_assoc]
        _ = t * (v * u) := by rw [h]
        _ = (t * v) * u := by rw [mul_assoc]
  refine not_normal_of_data (v := t * v) hL hC hZ hNC hzL hn hnt (S := S) ?_ ?_ ?_ ?_ ψ hψ ?_
    hσ₀ hz hκ hκz hgen ?_ hfive
  · exact S.mul_mem htS hvS
  · calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [← hvt]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [ht2, hv2, one_mul]
  · intro h
    apply hvN
    have : v = t * (t * v) := by rw [← mul_assoc, ht2, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right (mem_zpowers t)) h
  · calc s * (t * v) * s⁻¹ = (s * t * s⁻¹) * (s * v * s⁻¹) := by group
      _ = t * (v * z) := by rw [hst, mul_inv_cancel_right, hv]
      _ = (t * v) * z := by rw [mul_assoc]
  · rw [hrange]
    ext l
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hcomm_tv l (hcl t hL l h2)).2 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hcomm_tv l (hcl t hL l h2)).1 h1, h2⟩
  · intro u hu huv huz hu5
    exact hno5 u hu ((hcomm_tv u (mem_centralizer_singleton_iff.1 hu)).1 huv) huz hu5

end CFSG.EvenSporadicStandard.HSStd

