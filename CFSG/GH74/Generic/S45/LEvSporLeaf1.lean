module

public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.GH74.Generic.S45.LEvSporCorr

public section

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45


structure J2Facts {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Prop where
  card : Nat.card ↥H = 604800
  data : ∃ (tA tB : G) (M E : Subgroup G), tA ∈ H ∧ tB ∈ H ∧ orderOf tA = 2 ∧ orderOf tB = 2 ∧
    (∀ y ∈ H, orderOf y = 2 → (∃ g ∈ H, y = g * tA * g⁻¹) ∨ ∃ g ∈ H, y = g * tB * g⁻¹) ∧
    Nat.card ↥(H ⊓ centralizer ({tA} : Set G)) = 1920 ∧
    Nat.card ↥(H ⊓ centralizer ({tB} : Set G)) = 240 ∧
    (∀ z ∈ H, z ∈ centralizer ({tA} : Set G) → orderOf z = 5 →
      ∀ c ∈ H, c ∈ centralizer ({tA} : Set G) → c * z = z * c →
        ∃ j : ℕ, c = z ^ j ∨ c = tA * z ^ j) ∧
    M ≤ H ∧ Nat.card ↥M = 60 ∧
    (∀ x ∈ H, x ∈ centralizer ({tB} : Set G) → ∀ y ∈ H, y ∈ centralizer ({tB} : Set G) →
      ⁅x, y⁆ ∈ M) ∧
    Nat.card ↥(H ⊓ normalizer (M : Set G)) = 720 ∧ E ≤ H ⊓ normalizer (M : Set G) ∧
    IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 16

section

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem conj_setup {H K : Subgroup G} {t g x : G} (hg : g ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) (hx : x = g * t * g⁻¹) (hKx : ∀ k ∈ K, k * x = x * k) :
    ∃ K₁ : Subgroup G, (∀ y, y ∈ K₁ ↔ g * y * g⁻¹ ∈ K) ∧
      Nonempty (↥K₁ ≃* alternatingGroup (Fin 5)) ∧ K₁ ≤ H ∧ K₁ ≤ centralizer ({t} : Set G) := by
  set K₁ : Subgroup G := K.map (MulAut.conj g⁻¹).toMonoidHom with hK₁
  have hmem : ∀ y, y ∈ K₁ ↔ g * y * g⁻¹ ∈ K := fun y => by
    rw [hK₁, mem_map_conj_iff, inv_inv]
  have e₁ : ↥K₁ ≃* alternatingGroup (Fin 5) :=
    (Subgroup.equivMapOfInjective K (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans e
  have hK₁H : K₁ ≤ H := by
    intro y hy
    have : g * y * g⁻¹ ∈ K := (hmem y).1 hy
    have h2 : g⁻¹ * (g * y * g⁻¹) * g ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hg) (hKH this)) hg
    simpa [mul_assoc] using h2
  have hK₁t : K₁ ≤ centralizer ({t} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have hk := (hmem y).1 hy
    have h1 := hKx _ hk
    rw [hx] at h1
    have h2 : g * (y * t) * g⁻¹ = g * (t * y) * g⁻¹ := by
      calc g * (y * t) * g⁻¹ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := h1
        _ = g * (t * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  exact ⟨K₁, hmem, ⟨e₁⟩, hK₁H, hK₁t⟩

omit [Finite G] in
theorem eq_one_or_eq_of_conj {H K : Subgroup G} {t g x w : G} (hg : g ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) (ht2 : t * t = 1)
    (hcent5 : ∀ z ∈ H, z ∈ centralizer ({t} : Set G) → orderOf z = 5 →
      ∀ c ∈ H, c ∈ centralizer ({t} : Set G) → c * z = z * c → ∃ j : ℕ, c = z ^ j ∨ c = t * z ^ j)
    (hx : x = g * t * g⁻¹) (hKx : ∀ k ∈ K, k * x = x * k) (hwH : w ∈ H)
    (hwK : ∀ k ∈ K, k * w = w * k) (hwx : w * x = x * w) : w = 1 ∨ w = x := by
  obtain ⟨K₁, hmem, ⟨e₁⟩, hK₁H, hK₁t⟩ := conj_setup hg hKH e hx hKx
  have hw₁H : g⁻¹ * w * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hwH) hg
  have hw₁t : g⁻¹ * w * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    rw [hx] at hwx
    calc g⁻¹ * w * g * t = g⁻¹ * (w * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w) * g := by rw [hwx]
      _ = t * (g⁻¹ * w * g) := by group
  have hw₁K : ∀ k ∈ K₁, k * (g⁻¹ * w * g) = (g⁻¹ * w * g) * k := by
    intro k hk
    have h1 := hwK _ ((hmem k).1 hk)
    calc k * (g⁻¹ * w * g) = g⁻¹ * ((g * k * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * k * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * w * g) * k := by group
  rcases eq_one_or_eq_of_cent5 ht2 hcent5 hK₁H hK₁t e₁ hw₁H hw₁t hw₁K with h | h
  · left
    have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [this, h]; group
  · right
    have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [this, h, hx]

theorem mem_iff_of_conj_derived {H K M : Subgroup G} {t g x : G} (hg : g ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) (hx : x = g * t * g⁻¹) (hKx : ∀ k ∈ K, k * x = x * k)
    (hMcomm : ∀ a ∈ H, a ∈ centralizer ({t} : Set G) → ∀ b ∈ H, b ∈ centralizer ({t} : Set G) →
      ⁅a, b⁆ ∈ M) (hM : Nat.card ↥M = 60) : ∀ y, y ∈ K ↔ g⁻¹ * y * g ∈ M := by
  obtain ⟨K₁, hmem, ⟨e₁⟩, hK₁H, hK₁t⟩ := conj_setup hg hKH e hx hKx
  have hK₁M : K₁ = M :=
    eq_of_perfect_le_derived (D := H ⊓ centralizer ({t} : Set G)) (le_inf hK₁H hK₁t)
      (a5_perfect e₁) (fun a ha b hb => hMcomm a ha.1 ha.2 b hb.1 hb.2)
      (by rw [hM, a5_card e₁])
  intro y
  have := hmem (g⁻¹ * y * g)
  rw [hK₁M] at this
  have h2 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [h2] at this
  exact this.symm

omit [Finite G] in
theorem inf_centralizer_conj {H : Subgroup G} {t g : G} (hg : g ∈ H) :
    H ⊓ centralizer ({g * t * g⁻¹} : Set G) =
      (H ⊓ centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext z
  rw [mem_map_conj_iff, Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  have hH : z ∈ H ↔ g⁻¹ * z * g ∈ H :=
    ⟨fun h => H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg, fun h => by
      have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
      simpa [mul_assoc] using this⟩
  rw [hH]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    have h' : g⁻¹ * (z * (g * t * g⁻¹)) * g = g⁻¹ * ((g * t * g⁻¹) * z) * g := by rw [h]
    calc g⁻¹ * z * g * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * z) * g := h'
      _ = t * (g⁻¹ * z * g) := by group
  · intro h
    calc z * (g * t * g⁻¹) = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * z := by group

theorem factorization_604800 : (604800 : ℕ).factorization 2 = 7 := by
  rw [show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem leaf1_of_facts {H : Subgroup G} (hF : J2Facts H) {K : Subgroup G} (hKH : K ≤ H)
    (e5 : Nonempty (↥K ≃* alternatingGroup (Fin 5)))
    (hrk : ∃ E : Subgroup G, E ≤ centralizer (K : Set G) ⊓ H ∧ IsElementaryAbelian 2 ↥E ∧
      4 ≤ Nat.card ↥E) :
    (∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (normalizer (K : Set G) ⊓ H) →
        IsElementaryAbelian 2 ↥S ∧ Nat.card ↥S = 2 ^ 4) ∧
    (∀ y ∈ centralizer (K : Set G) ⊓ H, orderOf y = 2 →
        ¬ ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ y ∈ S ∧
          ∀ s ∈ S, s * y = y * s) := by
  obtain ⟨e⟩ := e5
  obtain ⟨hcard, tA, tB, M, E, htA, htB, htA2, htB2, hcover, hcA, hcB, hcent5, hMH, hMc, hMcomm,
    hNc, hEN, hEa, hEc⟩ := hF
  obtain ⟨E₀, hE₀Y, hE₀a, hE₀4⟩ := hrk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul : ∀ t : G, orderOf t = 2 → t * t = 1 := fun t ht => by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have hKc : ∀ y ∈ centralizer (K : Set G) ⊓ H, ∀ k ∈ K, k * y = y * k := fun y hy k hk =>
    Subgroup.mem_centralizer_iff.1 hy.1 k hk
  refine ⟨fun S hS => ?_, fun y hyY hy2 ⟨S, hSyl, hyS, hSc⟩ => ?_⟩
  ·
    obtain ⟨x, hxE, x', hx'E, hx2, hx'2, hxx'⟩ := exists_two_involutions hE₀a hE₀4
    have hxY := hE₀Y hxE
    have hx'Y := hE₀Y hx'E
    have hcomm : x' * x = x * x' := by
      have := hE₀a.toIsMulCommutative.is_comm.comm (⟨x', hx'E⟩ : ↥E₀) ⟨x, hxE⟩
      exact congrArg Subtype.val this
    have hx'1 : x' ≠ 1 := fun h => by rw [h, orderOf_one] at hx'2; omega
    obtain ⟨g, hg, hxg⟩ : ∃ g ∈ H, x = g * tB * g⁻¹ := by
      rcases hcover x hxY.2 hx2 with ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
      · exfalso
        have := eq_one_or_eq_of_conj hg hKH e (hmul tA htA2) hcent5 hgx (hKc x hxY) hx'Y.2
          (hKc x' hx'Y) hcomm
        rcases this with h | h
        · exact hx'1 h
        · exact hxx' h
      · exact ⟨g, hg, hgx⟩
    have hKM := mem_iff_of_conj_derived hg hKH e hxg (hKc x hxY) hMcomm hMc
    have hKeq : K = M.map (MulAut.conj g).toMonoidHom := by
      ext y
      rw [mem_map_conj_iff]
      exact hKM y
    have hHeq : H = H.map (MulAut.conj g).toMonoidHom := by
      ext y
      rw [mem_map_conj_iff]
      exact ⟨fun h => H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg, fun h => by
        have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
        simpa [mul_assoc] using this⟩
    have hN₀ : normalizer (K : Set G) ⊓ H =
        (H ⊓ normalizer (M : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, ← hHeq, hKeq,
        inf_comm, Subgroup.map_equiv_normalizer_eq M (MulAut.conj g)]
    have hN₀card : Nat.card ↥(normalizer (K : Set G) ⊓ H) = 2 ^ 4 * 45 := by
      rw [hN₀, Subgroup.card_map_of_injective (MulAut.conj g).injective, hNc]
      norm_num
    have hE' : E.map (MulAut.conj g).toMonoidHom ≤ normalizer (K : Set G) ⊓ H := by
      rw [hN₀]
      exact Subgroup.map_mono hEN
    have hEa' : IsElementaryAbelian 2 ↥(E.map (MulAut.conj g).toMonoidHom) := by
      have := hEa
      exact IsElementaryAbelian.map _
    exact sylow_elemAb hE' hEa' (a := 4) (m := 45)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]; norm_num) hN₀card
      (by decide) hS
  ·
    have hSH : S ≤ H := hSyl.le
    have hS128 : Nat.card ↥S = 2 ^ 7 := by
      rw [hSyl.card_eq, hcard, factorization_604800]
    have hSC : S ≤ H ⊓ centralizer ({y} : Set G) := fun s hs =>
      ⟨hSH hs, mem_centralizer_singleton_iff.2 (hSc s hs)⟩
    have hdvd : 2 ^ 7 ∣ Nat.card ↥(H ⊓ centralizer ({y} : Set G)) := by
      rw [← hS128]
      exact Subgroup.card_dvd_of_le hSC
    obtain ⟨g, hg, hyg⟩ : ∃ g ∈ H, y = g * tA * g⁻¹ := by
      rcases hcover y hyY.2 hy2 with ⟨g, hg, hgy⟩ | ⟨g, hg, hgy⟩
      · exact ⟨g, hg, hgy⟩
      · exfalso
        rw [hgy, inf_centralizer_conj hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
          hcB] at hdvd
        norm_num at hdvd
    obtain ⟨E₀', hE₀Y', hE₀a', hE₀4'⟩ : ∃ E : Subgroup G, E ≤ centralizer (K : Set G) ⊓ H ∧
        IsElementaryAbelian 2 ↥E ∧ 4 ≤ Nat.card ↥E := ⟨E₀, hE₀Y, hE₀a, hE₀4⟩
    have hle := card_le_two_of_centralizer_le (Y := centralizer (K : Set G) ⊓ H) hyY hy2
      (fun w hw hwy => eq_one_or_eq_of_conj hg hKH e (hmul tA htA2) hcent5 hyg (hKc y hyY) hw.2
        (hKc w hw) hwy) hE₀Y' (IsElementaryAbelian.isPGroup 2 ↥E₀')
    omega

end

theorem J2Facts.of_equiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {H : Subgroup G} {H' : Subgroup G'} (e : ↥H ≃* ↥H') (F : J2Facts H') : J2Facts H := by
  obtain ⟨hcard, tA', tB', M', E', htA', htB', htA2', htB2', hcover', hcA', hcB', hcent5', hMH',
    hMc', hMcomm', hNc', hEN', hEa', hEc'⟩ := F
  obtain ⟨M, hM⟩ := Corr.exists_of_le e hMH'
  obtain ⟨E, hE⟩ := Corr.exists_of_le e (hEN'.trans inf_le_left)
  have hN : Corr e (H ⊓ normalizer (M : Set G)) (H' ⊓ normalizer (M' : Set G')) := by
    rw [inf_comm, inf_comm H']
    exact hM.normalizer
  set a : ↥H := e.symm ⟨tA', htA'⟩ with ha
  set b : ↥H := e.symm ⟨tB', htB'⟩ with hb
  have hea : ((e a : ↥H') : G') = tA' := by rw [ha, MulEquiv.apply_symm_apply]
  have heb : ((e b : ↥H') : G') = tB' := by rw [hb, MulEquiv.apply_symm_apply]
  have hcA : Corr e (centralizer ({(a : G)} : Set G) ⊓ H) (centralizer ({tA'} : Set G') ⊓ H') :=
    (SCorr.singleton a.2 hea).centralizer
  have hcB : Corr e (centralizer ({(b : G)} : Set G) ⊓ H) (centralizer ({tB'} : Set G') ⊓ H') :=
    (SCorr.singleton b.2 heb).centralizer
  have hpull : ∀ u v : ↥H, ((e u : ↥H') : G') = ((e v : ↥H') : G') → u = v := fun u v h =>
    e.injective (Subtype.ext h)
  have hconj : ∀ (g t y : ↥H), ((e y : ↥H') : G') = ((e g : ↥H') : G') * ((e t : ↥H') : G') *
      ((e g : ↥H') : G')⁻¹ → (y : G) = (g : G) * (t : G) * (g : G)⁻¹ := by
    intro g t y h
    have : y = g * t * g⁻¹ := hpull _ _ (by simpa using h)
    rw [this]
    rfl
  refine ⟨(Corr.top (ψ := e)).card_eq.trans hcard, (a : G), (b : G), M, E, a.2, b.2, ?_, ?_, ?_,
    ?_, ?_, ?_, hM.le, hM.card_eq.trans hMc', ?_, ?_, ?_, ?_, ?_⟩
  · rw [← orderOf_corr e a, hea]
    exact htA2'
  · rw [← orderOf_corr e b, heb]
    exact htB2'
  · intro y hy hy2
    have hy2' : orderOf ((e ⟨y, hy⟩ : ↥H') : G') = 2 := by
      rw [orderOf_corr]
      exact hy2
    rcases hcover' _ (e ⟨y, hy⟩).2 hy2' with ⟨g', hg', hyg'⟩ | ⟨g', hg', hyg'⟩
    · left
      refine ⟨((e.symm ⟨g', hg'⟩ : ↥H) : G), (e.symm ⟨g', hg'⟩).2, hconj _ _ ⟨y, hy⟩ ?_⟩
      rw [MulEquiv.apply_symm_apply, hea]
      exact hyg'
    · right
      refine ⟨((e.symm ⟨g', hg'⟩ : ↥H) : G), (e.symm ⟨g', hg'⟩).2, hconj _ _ ⟨y, hy⟩ ?_⟩
      rw [MulEquiv.apply_symm_apply, heb]
      exact hyg'
  · rw [inf_comm]
    exact hcA.card_eq.trans (by rw [inf_comm]; exact hcA')
  · rw [inf_comm]
    exact hcB.card_eq.trans (by rw [inf_comm]; exact hcB')
  · intro z hz hzc hz5 c hc hcc hcz
    have hzc' := (SCorr.singleton a.2 hea).mem_centralizer_of (n := ⟨z, hz⟩) hzc
    have hcc' := (SCorr.singleton a.2 hea).mem_centralizer_of (n := ⟨c, hc⟩) hcc
    have hz5' : orderOf ((e ⟨z, hz⟩ : ↥H') : G') = 5 := by
      rw [orderOf_corr]
      exact hz5
    have hcz' : ((e ⟨c, hc⟩ : ↥H') : G') * ((e ⟨z, hz⟩ : ↥H') : G') =
        ((e ⟨z, hz⟩ : ↥H') : G') * ((e ⟨c, hc⟩ : ↥H') : G') := by
      have : (⟨c, hc⟩ : ↥H) * ⟨z, hz⟩ = ⟨z, hz⟩ * ⟨c, hc⟩ := Subtype.ext hcz
      have := congrArg (fun w : ↥H => ((e w : ↥H') : G')) this
      simpa only [map_mul, Subgroup.coe_mul] using this
    obtain ⟨j, hj | hj⟩ := hcent5' _ (e ⟨z, hz⟩).2 hzc' hz5' _ (e ⟨c, hc⟩).2 hcc' hcz'
    · refine ⟨j, Or.inl ?_⟩
      have := hpull ⟨c, hc⟩ (⟨z, hz⟩ ^ j) (by simpa only [map_pow, Subgroup.coe_pow] using hj)
      exact congrArg Subtype.val this
    · refine ⟨j, Or.inr ?_⟩
      have := hpull ⟨c, hc⟩ (a * ⟨z, hz⟩ ^ j)
        (by simpa only [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, hea] using hj)
      exact congrArg Subtype.val this
  · intro x hx hxc y hy hyc
    have hxc' := (SCorr.singleton b.2 heb).mem_centralizer_of (n := ⟨x, hx⟩) hxc
    have hyc' := (SCorr.singleton b.2 heb).mem_centralizer_of (n := ⟨y, hy⟩) hyc
    have h1 := hMcomm' _ (e ⟨x, hx⟩).2 hxc' _ (e ⟨y, hy⟩).2 hyc'
    have h2 : ((e ⁅(⟨x, hx⟩ : ↥H), (⟨y, hy⟩ : ↥H)⁆ : ↥H') : G') ∈ M' := by
      rw [map_commutatorElement]
      exact h1
    exact (hM.mem_iff _).2 h2
  · exact hN.card_eq.trans hNc'
  · intro x hx
    have hxH : x ∈ H := hE.le hx
    have := hEN' ((hE.mem_iff ⟨x, hxH⟩).1 hx)
    exact (hN.mem_iff ⟨x, hxH⟩).2 this
  · exact hE.isElementaryAbelian_iff.2 hEa'
  · exact hE.card_eq.trans hEc'


end CFSG.GH74.Generic.S45
