module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L51Main
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsShortGroup)
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Case4

variable {K T P S W : Subgroup G} {x : G} (c : Case4 K T P S W x)

include c

theorem exists_inv (hne : ⁅T, K⁆ ≠ ⊥) :
    ∃ g ∈ K, g ∉ K ⊓ Subgroup.centralizer (W : Set G) ∧
      g * g ∈ K ⊓ Subgroup.centralizer (W : Set G) := by
  classical
  set C := K ⊓ Subgroup.centralizer (W : Set G) with hC
  have hex : ∃ g ∈ K, (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ∉ C := by
    by_contra hcon
    push Not at hcon
    have hCK : C = K := eq_of_forall_isTwoElement_mem c.blk.perfect inf_le_left
      (fun g hg n hn => by
        refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hg (Subgroup.mem_inf.1 hn).1)
          (K.inv_mem hg), ?_⟩
        exact conj_mem_centralizer_of_mem_normalizer (c.K_norm_W hg) (Subgroup.mem_inf.1 hn).2)
      (fun g hg h2 => hcon g hg h2)
    apply hne
    have hKcent : K ≤ Subgroup.centralizer (W : Set G) := fun k hk =>
      (Subgroup.mem_inf.1 (hCK.symm ▸ hk)).2
    have hWK : ⁅W, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKcent
    exact le_bot_iff.1 ((Subgroup.commutator_mono c.T_le_W le_rfl).trans hWK.le)
  obtain ⟨g, hgK, ⟨a, ha⟩, hgC⟩ := hex
  have hm : ∃ m : ℕ, g ^ 2 ^ m ∈ C := ⟨a, by rw [ha]; exact C.one_mem⟩
  have hmC : g ^ 2 ^ (Nat.find hm) ∈ C := Nat.find_spec hm
  have hm0 : Nat.find hm ≠ 0 := by
    intro h0
    apply hgC
    have := hmC
    rw [h0] at this
    simpa using this
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hm = m' + 1 := ⟨Nat.find hm - 1, by omega⟩
  refine ⟨g ^ 2 ^ m', K.pow_mem hgK _, ?_, ?_⟩
  · intro h
    exact Nat.find_min hm (show m' < Nat.find hm by omega) h
  · have e : g ^ 2 ^ m' * g ^ 2 ^ m' = g ^ 2 ^ (Nat.find hm) := by
      rw [← pow_add, hm', pow_succ]
      congr 1
      ring
    rw [e]
    exact hmC

theorem dl_dl_eq_one (hne : ⁅T, K⁆ ≠ ⊥) {g w : G}
    (hg2 : ∀ w ∈ W, w * (g * g) = (g * g) * w) (hw : w ∈ W) (hgK : g ∈ K) :
    dl g (dl g w) = 1 := by
  have hww : g⁻¹ * (g⁻¹ * w * g) * g = w := by
    have := hg2 w hw
    calc g⁻¹ * (g⁻¹ * w * g) * g = (g * g)⁻¹ * (w * (g * g)) := by group
      _ = (g * g)⁻¹ * ((g * g) * w) := by rw [this]
      _ = w := by group
  have hw' : g⁻¹ * w * g ∈ W := by
    have h1 : g⁻¹ * w * g⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (c.K_norm_W (K.inv_mem hgK)) w).1 hw
    rwa [inv_inv] at h1
  have hmem : (g⁻¹ * w * g)⁻¹ * w ∈ W := W.mul_mem (W.inv_mem hw') hw
  have hsq := c.W_sq hne _ hmem
  unfold dl
  have e : g⁻¹ * (w⁻¹ * (g⁻¹ * w * g)) * g = (g⁻¹ * w * g)⁻¹ * w := by
    calc g⁻¹ * (w⁻¹ * (g⁻¹ * w * g)) * g
        = (g⁻¹ * w⁻¹ * g) * (g⁻¹ * (g⁻¹ * w * g) * g) := by group
      _ = (g⁻¹ * w * g)⁻¹ * w := by rw [hww]; group
  rw [e]
  calc (w⁻¹ * (g⁻¹ * w * g))⁻¹ * ((g⁻¹ * w * g)⁻¹ * w)
      = ((g⁻¹ * w * g)⁻¹ * w) * ((g⁻¹ * w * g)⁻¹ * w) := by group
    _ = 1 := hsq

theorem dl_mul_D (hne : ⁅T, K⁆ ≠ ⊥) {g h w : G} (hg : g ∈ K)
    (hh : h ∈ K ⊓ Subgroup.centralizer (blockU K : Set G)) (hw : w ∈ W) :
    dl (g * h) w = dl h w * dl g w := by
  have ha : dl g w ∈ blockU K := c.dl_mem_blockU hne hg hw
  have hah : dl g w * h = h * dl g w := Subgroup.mem_centralizer_iff.1 hh.2 _ ha
  have e1 : g⁻¹ * w * g = w * dl g w := by
    unfold dl
    group
  unfold dl at hah ⊢
  calc w⁻¹ * ((g * h)⁻¹ * w * (g * h)) = w⁻¹ * (h⁻¹ * (g⁻¹ * w * g) * h) := by group
    _ = w⁻¹ * (h⁻¹ * (w * (w⁻¹ * (g⁻¹ * w * g))) * h) := by
        congr 3
    _ = w⁻¹ * (h⁻¹ * w * ((w⁻¹ * (g⁻¹ * w * g)) * h)) := by group
    _ = w⁻¹ * (h⁻¹ * w * (h * (w⁻¹ * (g⁻¹ * w * g)))) := by rw [hah]
    _ = (w⁻¹ * (h⁻¹ * w * h)) * (w⁻¹ * (g⁻¹ * w * g)) := by group

theorem dl_conj (hne : ⁅T, K⁆ ≠ ⊥) {k g w : G} (hk : k ∈ K)
    (hg : g ∈ K ⊓ Subgroup.centralizer (blockU K : Set G)) (hw : w ∈ W) :
    dl (k * g * k⁻¹) w = k * dl g w * k⁻¹ := by
  have h1 : dl (k * g * k⁻¹) w = k * dl g (k⁻¹ * w * k) * k⁻¹ := by
    unfold dl
    group
  have hu : dl k w ∈ blockU K := c.dl_mem_blockU hne hk hw
  have hcomm : dl k w * g = g * dl k w := Subgroup.mem_centralizer_iff.1 hg.2 _ hu
  have h2 : k⁻¹ * w * k = w * dl k w := by
    unfold dl
    group
  have h3 : dl g (k⁻¹ * w * k) = dl g w := by
    rw [h2, c.dl_mul_W (Subgroup.mem_inf.1 hg).1 hw (c.dl_mem_W hk hw),
      dl_eq_one_iff.2 hcomm, mul_one]
  rw [h1, h3]

theorem false_of_ne (hne : ⁅T, K⁆ ≠ ⊥) : False := by
  classical
  have hperf := c.blk.perfect
  set U := blockU K with hUdef
  set D : Subgroup G := K ⊓ Subgroup.centralizer (U : Set G) with hD
  set C : Subgroup G := K ⊓ Subgroup.centralizer (W : Set G) with hC
  obtain ⟨g₀, hg₀K, hg₀C, hg₀2⟩ := c.exists_inv hne
  have hTg₀ : T ⊓ rightConjugate T g₀ = ⊥ := c.inf_eq_bot_of_sq_mem hne hg₀K hg₀C hg₀2
  have hfU : ∀ t : ↥T, dl g₀ t ∈ U := fun t => c.dl_mem_blockU hne hg₀K (c.T_le_W t.2)
  have hbij : Function.Bijective (fun t : ↥T => (⟨dl g₀ t, hfU t⟩ : ↥U)) := by
    have hinj : Function.Injective (fun t : ↥T => (⟨dl g₀ t, hfU t⟩ : ↥U)) := fun t₁ t₂ h =>
      Subtype.ext (c.dl_injOn hg₀K hTg₀ t₁ t₁.2 t₂ t₂.2 (congrArg Subtype.val h))
    exact hinj.bijective_of_nat_card_le (by rw [c.card_T_eq hne])
  have hsurj : ∀ u ∈ U, ∃ t ∈ T, dl g₀ t = u := fun u hu => by
    obtain ⟨t, ht⟩ := hbij.2 ⟨u, hu⟩
    exact ⟨t, t.2, congrArg Subtype.val ht⟩
  have hg₀W2 : ∀ w ∈ W, w * (g₀ * g₀) = (g₀ * g₀) * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 hg₀2.2 w hw
  have hg₀D : g₀ ∈ D := by
    refine Subgroup.mem_inf.2 ⟨hg₀K, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hsurj u hu
    exact dl_eq_one_iff.1 (c.dl_dl_eq_one hne hg₀W2 (c.T_le_W ht) hg₀K)
  have hDconj : ∀ k ∈ K, ∀ g ∈ D, k * g * k⁻¹ ∈ D := fun k hk g hg =>
    Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk (Subgroup.mem_inf.1 hg).1) (K.inv_mem hk),
      conj_mem_centralizer_of_mem_normalizer (le_normalizer_blockU K hk) (Subgroup.mem_inf.1 hg).2⟩
  have hK2 : ∀ k ∈ K, (∃ a : ℕ, k ^ 2 ^ a = 1) → k ∈ D := by
    intro k hk hk2
    by_contra hkD
    obtain ⟨a, ha⟩ := hk2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZ2 : IsPGroup 2 (Subgroup.zpowers k) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha)
      exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
    have hUp : IsPGroup 2 U := c.blk.isPGroup_blockU
    have hU0 : U ≠ ⊥ := blockU_ne_bot_of_short c.blk.short
    have hnormU : Subgroup.zpowers k ≤ Subgroup.normalizer (U : Set G) :=
      Subgroup.zpowers_le.2 (le_normalizer_blockU K hk)
    have hfix := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      hZ2 hUp hU0 hnormU
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hfix
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.1 hu
    have hku : k * u = u * k := Subgroup.mem_centralizer_iff.1 huC k (Subgroup.mem_zpowers k)
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    obtain ⟨t, ht, hut⟩ := hsurj u huU
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hu1' (hut.symm.trans (dl_one_right g₀))
    have htW : t ∈ W := c.T_le_W ht
    have hkgk : k * g₀ * k⁻¹ ∈ D := hDconj k hk g₀ hg₀D
    have hkuk : k * u * k⁻¹ = u := by rw [hku]; group
    have hsq : ∀ u' ∈ U, u' * u' = 1 := c.blk.blockU_sq_eq_one
    set y := g₀ * (k * g₀ * k⁻¹) with hy
    have hyK : y ∈ K := K.mul_mem hg₀K (Subgroup.mem_inf.1 hkgk).1
    have hyD : y ∈ D := D.mul_mem hg₀D hkgk
    have hdly : ∀ w ∈ W, dl y w = dl (k * g₀ * k⁻¹) w * dl g₀ w := fun w hw =>
      c.dl_mul_D hne hg₀K hkgk hw
    have hdlk : ∀ w ∈ W, dl (k * g₀ * k⁻¹) w = k * dl g₀ w * k⁻¹ := fun w hw =>
      c.dl_conj hne hk hg₀D hw
    by_cases hyC : y ∈ C
    ·
      apply hkD
      refine Subgroup.mem_inf.2 ⟨hk, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u' hu'
      obtain ⟨w, hw, rfl⟩ := hsurj u' hu'
      have h1 : dl y w = 1 := dl_eq_one_iff.2 (Subgroup.mem_centralizer_iff.1 hyC.2 w
        (c.T_le_W hw))
      rw [hdly w (c.T_le_W hw), hdlk w (c.T_le_W hw)] at h1
      have h2 : k * dl g₀ w * k⁻¹ = (dl g₀ w)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : (dl g₀ w)⁻¹ = dl g₀ w :=
        inv_eq_of_mul_eq_one_right (hsq _ (hfU ⟨w, hw⟩))
      rw [h3] at h2
      calc dl g₀ w * k = (k * dl g₀ w * k⁻¹) * k := by rw [h2]
        _ = k * dl g₀ w := by group
    ·
      have hyy : y * y ∈ C := by
        refine Subgroup.mem_inf.2 ⟨K.mul_mem hyK hyK, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        apply dl_eq_one_iff.1
        rw [c.dl_mul_D hne hyK hyD hw]
        exact hsq _ (c.dl_mem_blockU hne hyK hw)
      have hTy := c.inf_eq_bot_of_sq_mem hne hyK hyC hyy
      have h1 : dl y t = 1 := by
        rw [hdly t htW, hdlk t htW, hut, hkuk]
        exact hsq u huU
      exact ht1 (c.dl_injOn hyK hTy t ht 1 T.one_mem (h1.trans (dl_one_right y).symm))
  have hDK : D = K := eq_of_forall_isTwoElement_mem hperf inf_le_left hDconj hK2
  have hKcent : K ≤ Subgroup.centralizer (U : Set G) := fun k hk => by
    have : k ∈ D := by rw [hDK]; exact hk
    exact (Subgroup.mem_inf.1 this).2
  have hUK : ⁅U, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKcent
  exact blockU_ne_bot_of_short c.blk.short (c.blk.blockU_stable.symm.trans hUK)

end Case4

end CFSG.CGT.PushingUpLit.LIT.Foote
