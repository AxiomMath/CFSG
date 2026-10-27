module

public import CFSG.LargeExtraspecial.AS35IFaith
public import CFSG.LargeExtraspecial.AS35IBender
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LargeExtraspecial.AS35DFourEight
public import CFSG.LargeExtraspecial.AS35IExtra
public import CFSG.LargeExtraspecial.AS35IS3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace Asc22

variable {G : Type} [Group G] {N U P : Subgroup G} {z : G}

namespace Hyp

variable (h : Hyp N U P z)
include h

omit h in
theorem index_Mb [Finite G] : (barOf N z (cenM N z)).index = Nat.card (conjIn z N) := by
  rw [card_conjIn, index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.2 (piK_surjective (N := N) (z := z)), index_top, mul_one]
  congr 1
  apply sup_eq_left.2
  intro n hn
  exact mem_subgroupOf.2 (kerV_le_M (mem_kerK.1 hn))

theorem exists_two_pow_of_mul [Finite G] {w : ℕ}
    (hw : w * Nat.card (Asc77.centerIn z N) = Nat.card (genV N z)) : ∃ d, w = 2 ^ d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (genV N z) := fun v => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
    exact h.mul_self_V v.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hV2
  have hdvd : w ∣ 2 ^ a := ⟨Nat.card (Asc77.centerIn z N), by rw [hw, ha]⟩
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨d, hd⟩

theorem exists_ne_z [Finite G] : ∃ t ∈ conjIn z N, t ≠ z := by
  obtain ⟨g, hgN, hgz⟩ : ∃ g ∈ N, g ∉ centralizer ({z} : Set G) := by
    by_contra hcon
    push Not at hcon
    exact h.notcen hcon
  exact ⟨g * z * g⁻¹, conj_mem_conjIn hgN, fun h1 =>
    hgz (mem_inf.1 ((conj_eq_iff hgN).1 h1)).2⟩

theorem exists_conj_of_card [Finite G]
    (hcard : Nat.card (barOf N z (U ⊔ P)) + 1 = Nat.card (conjIn z N)) {t₁ : G}
    (ht₁ : t₁ ∈ conjIn z N) (ht₁z : t₁ ≠ z) :
    ∀ t ∈ conjIn z N, t ≠ z → ∃ a ∈ U ⊔ P, a * t₁ * a⁻¹ = t := by
  classical
  let _ : Fintype (conjIn z N) := Fintype.ofFinite _
  let _ : Fintype (barOf N z (U ⊔ P)) := Fintype.ofFinite _
  let φ : Gbar N z →* Equiv.Perm (conjIn z N) := QuotientGroup.kerLift (conjAct z N)
  let t₀ : conjIn z N := ⟨t₁, ht₁⟩
  let z₀ : conjIn z N := ⟨z, self_mem_conjIn z N⟩
  let F : barOf N z (U ⊔ P) → conjIn z N := fun x => φ x t₀
  have hlift : ∀ x : barOf N z (U ⊔ P), ∃ n : N, (n : G) ∈ U ⊔ P ∧ piK N z n = x := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨n, mem_subgroupOf.1 hn, rfl⟩
  have hφ : ∀ (n : N) (t : conjIn z N),
      ((φ (piK N z n) t : conjIn z N) : G) = n * t * (n : G)⁻¹ := by
    intro n t
    change ((QuotientGroup.kerLift (conjAct z N) (n : Gbar N z) t : conjIn z N) : G) = _
    rw [QuotientGroup.kerLift_mk, conjAct_apply]
  have hinj : Function.Injective F := by
    intro x y hxy
    have hw : φ ((y : Gbar N z)⁻¹ * x) t₀ = t₀ := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply]
      change (φ y)⁻¹ (F x) = t₀
      rw [hxy]
      exact Equiv.Perm.inv_eq_iff_eq.2 rfl
    obtain ⟨n, hnQ, hn⟩ := hlift (y⁻¹ * x)
    have hn' : piK N z n = (y : Gbar N z)⁻¹ * x := by rw [hn]; rfl
    rw [← hn'] at hw
    have h1 : (n : G) * t₁ * (n : G)⁻¹ = t₁ := by
      have := congrArg Subtype.val hw
      rwa [hφ] at this
    have hnK : (n : G) ∈ kerV N z := by
      by_contra hnK
      exact h.conj_ne_of_ne hnQ hnK ht₁ ht₁z h1
    have h2 : (y : Gbar N z)⁻¹ * x = 1 := by rw [← hn', piK_eq_one]; exact hnK
    exact (Subtype.ext (inv_mul_eq_one.1 h2)).symm
  have hmiss : ∀ x, F x ≠ z₀ := by
    intro x hx
    obtain ⟨n, hnQ, hn⟩ := hlift x⁻¹
    have hz : φ (piK N z n) z₀ = z₀ := by
      apply Subtype.ext
      rw [hφ]
      change (n : G) * z * (n : G)⁻¹ = z
      rw [h.comm_sup hnQ]
      group
    have hn' : piK N z n = (x : Gbar N z)⁻¹ := by rw [hn]; rfl
    rw [hn'] at hz
    apply ht₁z
    have h3 : t₀ = z₀ := by
      calc t₀ = (φ x)⁻¹ (φ x t₀) := (Equiv.Perm.inv_eq_iff_eq.2 rfl).symm
        _ = (φ x)⁻¹ z₀ := by rw [show φ x t₀ = z₀ from hx]
        _ = z₀ := by rw [← map_inv]; exact hz
    exact congrArg Subtype.val h3
  set img := (Finset.univ : Finset (barOf N z (U ⊔ P))).image F with himg
  have hcard_img : img.card = Fintype.card (barOf N z (U ⊔ P)) :=
    Finset.card_image_of_injective _ hinj
  have hsub : img ⊆ (Finset.univ : Finset (conjIn z N)).erase z₀ := by
    intro t ht
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_erase.2 ⟨hmiss x, Finset.mem_univ _⟩
  have hcard_erase : ((Finset.univ : Finset (conjIn z N)).erase z₀).card =
      Fintype.card (conjIn z N) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have heq : img = (Finset.univ : Finset (conjIn z N)).erase z₀ := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard_erase, hcard_img, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← hcard]
    omega
  intro t ht htz
  have hmem : (⟨t, ht⟩ : conjIn z N) ∈ img := by
    rw [heq]
    exact Finset.mem_erase.2 ⟨fun h' => htz (congrArg Subtype.val h'), Finset.mem_univ _⟩
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hmem
  obtain ⟨n, hnQ, hn⟩ := hlift x
  refine ⟨n, hnQ, ?_⟩
  have h4 := congrArg Subtype.val hx
  change ((φ x t₀ : conjIn z N) : G) = t at h4
  rw [← hn, hφ] at h4
  exact h4

theorem isAFiveAt_of_card [Finite G] (hΩ : Nat.card (conjIn z N) = 5)
    (hV : Nat.card (genV N z) = 16 * Nat.card (Asc77.centerIn z N))
    (hR : Nat.card (conjAct z N).range = 60) : IsAFiveAt z N := by
  classical
  let _ : Fintype (conjIn z N) := Fintype.ofFinite _
  have hR' : (conjAct z N).range = alternatingGroup (conjIn z N) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have h1 := (conjAct z N).range.card_mul_index
    rw [hR, Nat.card_perm, hΩ] at h1
    have h5 : Nat.factorial 5 = 120 := rfl
    rw [h5] at h1
    omega
  refine ⟨inferInstance, inferInstance, ?_, fun a ha b hb => h.comm_conjIn ha hb, hV, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, hΩ]
  · intro n
    have hn : conjAct z N n ∈ (conjAct z N).range := ⟨n, rfl⟩
    rw [hR'] at hn
    exact Equiv.Perm.mem_alternatingGroup.1 hn
  · intro σ hσ
    have hσ' : σ ∈ alternatingGroup (conjIn z N) := Equiv.Perm.mem_alternatingGroup.2 hσ
    rw [← hR'] at hσ'
    exact hσ'

theorem isAFiveAt_of_two_lt
    [Finite G]
    (h2 : 2 < Nat.card (barOf N z (U ⊔ P))) : IsAFiveAt z N := by
  classical
  have habs := h.absTI
  have hM := h.Mb_ne_top
  have hQ1 := h.Qb_ne_bot
  have hcl := h.normalClosure_Qb
  have hSE := habs.stronglyEmbedded hQ1 hM hcl
  have hB := habs.fusionIsBenderGroup h2 hM hcl (fun H hQH hH => h.le_Mb hQH hH)
    (fun Y hY hYM => eq_bot_of_normal_le hY hYM)
  have : IsSimpleGroup (Gbar N z) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨T, hQT, hTM⟩ := h.exists_sylow
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB T
  obtain ⟨-, hidx, hQZ⟩ := habs.borel_facts hQ1 hM hSE hQT hTM hD
  have hΩ : Nat.card (conjIn z N) = Nat.card (T : Subgroup (Gbar N z)) + 1 := by
    rw [← index_Mb, hidx]
  obtain ⟨W, _, _, ρ, hρ, hW⟩ := h.exists_faithful
  obtain ⟨d, hd⟩ := h.exists_two_pow_of_mul hW
  have hCpos : 0 < Nat.card (Asc77.centerIn z N) := Nat.card_pos
  obtain ⟨g, hgN, hgz⟩ : ∃ g ∈ N, g ∉ centralizer ({z} : Set G) := by
    by_contra hcon
    push Not at hcon
    exact h.notcen hcon
  have hgM : g ∉ cenM N z := fun hg => hgz (mem_inf.1 hg).2
  have hgen := h.card_genV_mul_le hgN hgM
  have hA := h.card_commutator_sup_le
  have hW4 : Nat.card W ≤ 4 * Nat.card (barOf N z (U ⊔ P)) ^ 2 := by
    have h3 : Nat.card W * Nat.card (Asc77.centerIn z N) * Nat.card (Asc77.centerIn z N) ≤
        (4 * Nat.card (barOf N z (U ⊔ P)) ^ 2) * Nat.card (Asc77.centerIn z N) *
          Nat.card (Asc77.centerIn z N) := by
      calc Nat.card W * Nat.card (Asc77.centerIn z N) * Nat.card (Asc77.centerIn z N)
          = Nat.card (genV N z) * Nat.card (Asc77.centerIn z N) := by rw [hW]
        _ ≤ Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) *
            Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) := hgen
        _ ≤ (2 * Nat.card (barOf N z (U ⊔ P)) * Nat.card (Asc77.centerIn z N)) *
            (2 * Nat.card (barOf N z (U ⊔ P)) * Nat.card (Asc77.centerIn z N)) :=
            Nat.mul_le_mul hA hA
        _ = (4 * Nat.card (barOf N z (U ⊔ P)) ^ 2) * Nat.card (Asc77.centerIn z N) *
            Nat.card (Asc77.centerIn z N) := by ring
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_right h3 hCpos) hCpos
  have hQcard : Nat.card (barOf N z (U ⊔ P)) = Nat.card
      (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        (T : Subgroup (Gbar N z))) := by rw [← hQZ]
  have hpow : ∀ m : ℕ, Nat.card W ≤ 2 ^ m → d ≤ m := fun m hm => by
    rw [hd] at hm
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hm
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨hTc, -, hZc⟩ := hD.orders_psl2 hf e
    have hQf : Nat.card (barOf N z (U ⊔ P)) = 2 ^ f := hQcard.trans hZc
    have hΩf : Nat.card (conjIn z N) = 2 ^ f + 1 := by rw [hΩ, hTc]
    obtain ⟨t₁, ht₁, ht₁z⟩ := h.exists_ne_z
    have htr := h.exists_conj_of_card (by rw [hQf, hΩf]) ht₁ ht₁z
    have hV2 := h.card_genV_le_of_transitive ht₁ htr
    have hWf : Nat.card W ≤ 2 ^ (f + 2) := by
      have h3 : Nat.card W * Nat.card (Asc77.centerIn z N) ≤
          2 ^ (f + 2) * Nat.card (Asc77.centerIn z N) := by
        calc Nat.card W * Nat.card (Asc77.centerIn z N) = Nat.card (genV N z) := hW
          _ ≤ 2 * Nat.card ↥(⁅genV N z, U ⊔ P⁆ ⊔ Asc77.centerIn z N) := hV2
          _ ≤ 2 * (2 * Nat.card (barOf N z (U ⊔ P)) * Nat.card (Asc77.centerIn z N)) :=
            Nat.mul_le_mul_left _ hA
          _ = 2 ^ (f + 2) * Nat.card (Asc77.centerIn z N) := by rw [hQf]; ring
      exact Nat.le_of_mul_le_mul_right h3 hCpos
    have hdf := hpow _ hWf
    have hXcard : Nat.card (Gbar N z) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.psl2_even_card (by omega)
    by_cases hf3 : f = 3
    · subst hf3
      have := CFSG.CGT.Timmesfeld75.lemma27_psl2_eight e.toMonoidHom e.surjective ρ hρ hd
      omega
    · have h27 := CFSG.CGT.Timmesfeld75.lemma27_psl2 hf hf3 (by rw [hXcard]) ρ hρ hd
      have hf2 : f = 2 := by omega
      subst hf2
      have hd4 : d = 4 := by omega
      refine h.isAFiveAt_of_card (by rw [hΩf]; norm_num) ?_ ?_
      · rw [← hW, hd, hd4]
        ring
      · rw [card_range_conjAct, hXcard]
        norm_num
  · obtain ⟨hZc, -, -⟩ := hD.orders_psu3 hf e
    have hQf : Nat.card (barOf N z (U ⊔ P)) = 2 ^ f := hQcard.trans hZc
    have h27 := CFSG.CGT.Timmesfeld75.lemma27_psu3 hf
      (by rw [Nat.card_congr e.toEquiv]) ρ hρ hd
    have hdf := hpow (2 * f + 2) (by
      calc Nat.card W ≤ 4 * Nat.card (barOf N z (U ⊔ P)) ^ 2 := hW4
        _ = 2 ^ (2 * f + 2) := by rw [hQf]; ring)
    omega
  · obtain ⟨hZc, -, -⟩ := hD.orders_sz ha e
    have hQf : Nat.card (barOf N z (U ⊔ P)) = 2 ^ (2 * a + 1) := hQcard.trans hZc
    have h27 := CFSG.CGT.Timmesfeld75.lemma27_sz ha
      (by rw [Nat.card_congr e.toEquiv]) ρ hρ hd
    have hdf := hpow (2 * (2 * a + 1) + 2) (by
      calc Nat.card W ≤ 4 * Nat.card (barOf N z (U ⊔ P)) ^ 2 := hW4
        _ = 2 ^ (2 * (2 * a + 1) + 2) := by rw [hQf]; ring)
    omega

end Hyp

end Asc22

namespace S14

theorem aschbacherTwoTwoStmt_of :
    AschbacherTwoTwoStmt := by
  intro G _ _ N U P z hUN hPN hUc hU2 hUP hext hzP hZP hQn hsyl hzO hnc hmax hgen
  have h : Asc22.Hyp N U P z :=
    ⟨hUN, hPN, hUc, hU2, hUP, hext, hzP, hZP, hQn, hsyl, hzO, hnc, hmax, hgen⟩
  by_cases h2 : Nat.card (Asc22.barOf N z (U ⊔ P)) = 2
  · exact Or.inl (h.isSThreeAt_of_card_two h2)
  · right
    apply h.isAFiveAt_of_two_lt
    have h1 : Nat.card (Asc22.barOf N z (U ⊔ P)) ≠ 1 := fun h1 =>
      h.Qb_ne_bot (eq_bot_of_card_eq _ h1)
    have hpos : 0 < Nat.card (Asc22.barOf N z (U ⊔ P)) := Nat.card_pos
    omega

end S14

end CFSG.LargeExtraspecial
