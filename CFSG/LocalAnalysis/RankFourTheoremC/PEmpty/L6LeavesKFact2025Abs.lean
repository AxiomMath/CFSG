module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Perm
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open Subgroup CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open scoped commutatorElement

universe u v

section Lift

variable {Q A : Type*} [Group Q] [Group A]

theorem exists_lift [Finite Q] (F : Q →* A) (hker : IsPGroup 2 F.ker) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {z : A} (hz : z ∈ F.range) (hzp : z ^ p = 1) :
    ∃ q : Q, F q = z ∧ q ^ p = 1 := by
  obtain ⟨q₀, hq₀⟩ := hz
  obtain ⟨a, ha⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime (Nat.card F.ker) p := by
    rw [ha]
    exact ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left a
  obtain ⟨d, -, hd⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨q₀ ^ (Nat.card F.ker * d), ?_, ?_⟩
  · rw [map_pow, hq₀]
    calc z ^ (Nat.card F.ker * d)
        = z ^ (p * (Nat.card F.ker * d / p) + Nat.card F.ker * d % p) := by
          rw [Nat.div_add_mod]
      _ = z := by rw [hd, pow_add, pow_mul, hzp, one_pow, one_mul, pow_one]
  · have hk : q₀ ^ p ∈ F.ker := by rw [MonoidHom.mem_ker, map_pow, hq₀, hzp]
    have hk' : (q₀ ^ p) ^ Nat.card F.ker = 1 := by
      have := pow_card_eq_one' (G := F.ker) (x := ⟨q₀ ^ p, hk⟩)
      exact congrArg Subtype.val this
    calc (q₀ ^ (Nat.card F.ker * d)) ^ p = ((q₀ ^ p) ^ Nat.card F.ker) ^ d := by
          simp only [← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [hk', one_pow]

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {g : G} {p : ℕ} (h : g ^ p = 1) :
    IsPGroup p (zpowers g) := by
  intro x
  obtain ⟨n, hn⟩ := x.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, h, one_zpow]

theorem mem_normalizer_commutator' {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

end Lift


section Main

variable {Q A : Type} [Group Q] [Finite Q] [Group A]
  {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem exists_alt_section [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    (hdim : Module.finrank k V ≤ 4) (ρ : Q →* (Module.End k V)ˣ) (hρ : Function.Injective ρ)
    (F : Q →* A) (hker2 : IsPGroup 2 F.ker)
    (hkerc : ∀ y ∈ F.ker, ∀ g : (Module.End k V)ˣ, ρ y * g = g * ρ y)
    (hW : ∀ (x₀ u₀ : Q) (x' : (Module.End k V)ˣ) (hx : ρ x₀ * ρ x₀ = -1) (hx' : x' * x' = -1),
      x' = ρ u₀ * ρ x₀ * (ρ u₀)⁻¹ → half h2 * gam h2 (ρ x₀) hx * gam h2 x' hx' ∈ ρ.range)
    {S : Subgroup A} (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hSF : S ≤ F.range) {z : A}
    (hz : z ∈ F.range) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hzp : z ^ p = 1)
    (hzS : z ∈ normalizer (S : Set A)) (hcomm : ⁅S, zpowers z⁆ = S) :
    ∃ (H : Subgroup A) (hzH : z ∈ H), H ≤ normalizer (S : Set A) ∧ H ≤ F.range ∧
      ∃ φ : H →* alternatingGroup (Fin 5), Function.Surjective φ ∧ φ ⟨z, hzH⟩ ≠ 1 := by
  obtain ⟨zt, hFzt, hztp⟩ := exists_lift F hker2 hp (by omega) hz hzp
  have hSt2 : IsPGroup 2 (S.comap F) := hS2.comap_of_ker_isPGroup F hker2
  have hFSt : (S.comap F).map F = S := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hSF
  have hztSt : zt ∈ normalizer ((S.comap F : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    simp only [Subgroup.mem_comap, map_mul, map_inv, hFzt]
    exact Subgroup.mem_normalizer_iff.mp hzS (F q)
  have hzpow : zpowers zt ≤ normalizer ((S.comap F : Subgroup Q) : Set Q) :=
    Subgroup.zpowers_le.mpr hztSt
  have hRSt : ⁅S.comap F, zpowers zt⁆ ≤ S.comap F :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hzpow
  have hR2 : IsPGroup 2 (⁅S.comap F, zpowers zt⁆ : Subgroup Q) := hSt2.to_le hRSt
  have hcop : ¬ p ∣ Nat.card (S.comap F) := by
    obtain ⟨n, hn⟩ := hSt2.exists_card_eq
    rw [hn]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
    omega
  have hRR : ⁅⁅S.comap F, zpowers zt⁆, zpowers zt⁆ = ⁅S.comap F, zpowers zt⁆ :=
    CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent hp (zpowers zt)
      (S.comap F) (isPGroup_zpowers_of_pow_eq_one hztp) hcop hzpow
  have hFR : (⁅S.comap F, zpowers zt⁆ : Subgroup Q).map F = S := by
    rw [Subgroup.map_commutator, hFSt, MonoidHom.map_zpowers, hFzt, hcomm]
  have hR1 : (⁅S.comap F, zpowers zt⁆ : Subgroup Q) ≠ ⊥ := by
    intro h
    apply hS1
    rw [← hFR, h, Subgroup.map_bot]
  have hztR : zt ∈ normalizer ((⁅S.comap F, zpowers zt⁆ : Subgroup Q) : Set Q) :=
    mem_normalizer_commutator' hztSt (Subgroup.le_normalizer (Subgroup.mem_zpowers zt))
  generalize hRdef : (⁅S.comap F, zpowers zt⁆ : Subgroup Q) = R at hR2 hRR hFR hR1 hztR
  haveI : Finite (R.map ρ) := Finite.of_surjective _ (ρ.subgroupMap_surjective R)
  have hRρ2 : IsPGroup 2 (R.map ρ) := hR2.map ρ
  have hRρ1 : R.map ρ ≠ ⊥ := by
    intro h
    apply hR1
    have := (Subgroup.map_eq_bot_iff _).mp h
    rw [ρ.ker_eq_bot_iff.mpr hρ] at this
    exact le_bot_iff.mp this
  have hu : ρ zt ∈ normalizer ((R.map ρ : Subgroup _) : Set _) :=
    Subgroup.le_normalizer_map ρ ⟨zt, hztR, rfl⟩
  have hup : (ρ zt) ^ p = 1 := by rw [← map_pow, hztp, map_one]
  have hcR : ⁅R.map ρ, zpowers (ρ zt)⁆ = R.map ρ := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hRR]
  obtain ⟨hp5', -, hmin⟩ := core_lemma h2 hdim hp hp5 hRρ2 hRρ1 hu hup hcR
  subst hp5'
  obtain ⟨t, ht⟩ := hmin.exists_pent hup
  obtain ⟨x, x', hx, hx', hxR, hxu, w, hw, hu', ψ, hψs, hψn, hψc, hψu⟩ := alt_section h2 hmin ht
  obtain ⟨x₀, hx₀R, rfl⟩ := hxR
  have hwr : w ∈ ρ.range := hw ▸ hW x₀ zt x' hx hx' hxu
  have hCr : Subgroup.closure ({ρ zt, w} : Set (Module.End k V)ˣ) ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨zt, rfl⟩
    · exact hwr
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup Q, Y = (Subgroup.closure
      ({ρ zt, w} : Set (Module.End k V)ˣ)).comap ρ := ⟨_, rfl⟩
  have hYmem : ∀ y : Q, y ∈ Y ↔ ρ y ∈ Subgroup.closure ({ρ zt, w} : Set (Module.End k V)ˣ) := by
    intro y
    rw [hY]
    exact Iff.rfl
  have hztY : zt ∈ Y := (hYmem zt).mpr hu'
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : Y →* alternatingGroup (Fin 5),
      ∀ (y : Q) (hy : y ∈ Y), ψ' ⟨y, hy⟩ = ψ ⟨ρ y, (hYmem y).mp hy⟩ :=
    ⟨ψ.comp (ρ.subgroupComap _ |>.comp (Subgroup.inclusion (by rw [hY]))), fun _ _ => rfl⟩
  have hψ's : Function.Surjective ψ' := by
    intro a
    obtain ⟨c, hc⟩ := hψs a
    obtain ⟨q, hq⟩ := hCr c.2
    have hqY : q ∈ Y := (hYmem q).mpr (by rw [hq]; exact c.2)
    refine ⟨⟨q, hqY⟩, ?_⟩
    rw [hψ']
    have : (⟨ρ q, (hYmem q).mp hqY⟩ :
        Subgroup.closure ({ρ zt, w} : Set (Module.End k V)ˣ)) = c := Subtype.ext hq
    rw [this]
    exact hc
  have hker' : (F.subgroupMap Y).ker ≤ ψ'.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have hFy : F y.1 = 1 := congrArg Subtype.val hy
    obtain ⟨y, hyY⟩ := y
    rw [hψ']
    exact hψc (ρ y) ((hYmem y).mp hyY) (hkerc y hFy)
  have hsurj := F.subgroupMap_surjective Y
  obtain ⟨φ, hφ⟩ : ∃ φ : (Y.map F) →* alternatingGroup (Fin 5),
      ∀ y : Y, φ (F.subgroupMap Y y) = ψ' y :=
    ⟨(F.subgroupMap Y).liftOfRightInverse (Function.surjInv hsurj)
        (Function.rightInverse_surjInv hsurj) ⟨ψ', hker'⟩,
      fun y => (F.subgroupMap Y).liftOfRightInverse_comp_apply (Function.surjInv hsurj)
        (Function.rightInverse_surjInv hsurj) ⟨ψ', hker'⟩ y⟩
  refine ⟨Y.map F, ⟨zt, hztY, hFzt⟩, ?_, ?_, φ, ?_, ?_⟩
  ·
    have key : ∀ y ∈ Y, ∀ s ∈ S, F y * s * (F y)⁻¹ ∈ S := by
      intro y hy s hs
      rw [← hFR] at hs
      obtain ⟨r, hr, rfl⟩ := hs
      have hn := Subgroup.mem_normalizer_iff.mp (hψn (ρ y) ((hYmem y).mp hy)) (ρ r)
      obtain ⟨r', hr', hr'e⟩ := hn.mp ⟨r, hr, rfl⟩
      have hrr : r' = y * r * y⁻¹ := hρ (by rw [hr'e]; simp)
      rw [← hFR]
      exact ⟨r', hr', by rw [hrr]; simp⟩
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => key y hy s hs, fun hs => ?_⟩
    have := key y⁻¹ (Y.inv_mem hy) _ hs
    have e : F y⁻¹ * (F y * s * (F y)⁻¹) * (F y⁻¹)⁻¹ = s := by
      simp only [map_inv]
      group
    rwa [e] at this
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  · intro a
    obtain ⟨y, hy⟩ := hψ's a
    exact ⟨F.subgroupMap Y y, by rw [hφ]; exact hy⟩
  · have e : (⟨z, ⟨zt, hztY, hFzt⟩⟩ : Y.map F) = F.subgroupMap Y ⟨zt, hztY⟩ :=
      Subtype.ext hFzt.symm
    rw [e, hφ, hψ']
    exact hψu

end Main


section Assemble

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem alt_five_not_comm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  by_contra hcon
  have hc : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  letI : CommGroup (alternatingGroup (Fin 5)) :=
    { (inferInstance : Group (alternatingGroup (Fin 5))) with mul_comm := hc }
  have hprime := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 5))
  rw [card_alt_five] at hprime
  exact absurd hprime (by norm_num)

theorem kxSection_of_alt {A : Type} [Group A] {X H : Subgroup A} {z : A} (hHX : H ≤ X)
    (hzH : z ∈ H) (φ : H →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hz1 : φ ⟨z, hzH⟩ ≠ 1) : KxSection z X 3 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hsec := S622IsSimpleSection.of_surjective φ hφ alt_five_not_comm
  refine ⟨H, φ.ker.map H.subtype, hHX, hsec, hzH, ?_, ?_⟩
  · rintro ⟨k, hk, hkz⟩
    apply hz1
    have : k = ⟨z, hzH⟩ := Subtype.ext hkz
    rw [← this]
    exact MonoidHom.mem_ker.mp hk
  · have hsub : (φ.ker.map H.subtype).subgroupOf H = φ.ker :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective φ.ker
    show 3 ∣ ((φ.ker.map H.subtype).subgroupOf H).index
    rw [hsub, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, card_alt_five]
    norm_num

end Assemble

section Abstract

variable {Q A : Type} [Group Q] [Finite Q] [Group A]
  {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem kxSection_of_model [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    (hdim : Module.finrank k V ≤ 4) (ρ : Q →* (Module.End k V)ˣ) (hρ : Function.Injective ρ)
    (F : Q →* A) (hker2 : IsPGroup 2 F.ker)
    (hkerc : ∀ y ∈ F.ker, ∀ g : (Module.End k V)ˣ, ρ y * g = g * ρ y)
    (hW : ∀ (x₀ u₀ : Q) (x' : (Module.End k V)ˣ) (hx : ρ x₀ * ρ x₀ = -1) (hx' : x' * x' = -1),
      x' = ρ u₀ * ρ x₀ * (ρ u₀)⁻¹ → half h2 * gam h2 (ρ x₀) hx * gam h2 x' hx' ∈ ρ.range)
    {L S : Subgroup A} (hL : F.range = L) {z : A} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hzp : orderOf z = p) (hzL : z ∈ L) (hSL : S ≤ L) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set A)) (hcomm : ⁅S, zpowers z⁆ = S) :
    KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  have hzp' : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
  obtain ⟨H, hzH, hHn, hHF, φ, hφ, hφz⟩ := exists_alt_section h2 hdim ρ hρ F hker2 hkerc hW hS2 hS1
    (hL ▸ hSL) (hL ▸ hzL) hp hp5 hzp' hzS hcomm
  exact kxSection_of_alt (le_inf hHn (hL ▸ hHF)) hzH φ hφ hφz

end Abstract

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
