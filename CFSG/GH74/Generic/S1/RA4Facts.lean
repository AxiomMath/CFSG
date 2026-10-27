module

public import CFSG.GH74.Generic.S1.Props
public import CFSG.GH74.Generic.S1.RInvClasses
public import CFSG.GH74.Generic.S1.RCard
public import CFSG.GH74.Generic.S1.RSP

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

theorem factorization_range_eq {S H : Type} [Group S] [Finite S] [Group H] (ψ : S →* H)
    (hker : Odd (Nat.card ψ.ker)) :
    (Nat.card ψ.range).factorization 2 = (Nat.card S).factorization 2 := by
  have : Finite ↥ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  have h := Subgroup.card_ker_mul_card_range ψ
  have h1 : (Nat.card ψ.ker).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h2
    exact (Nat.not_even_iff_odd.2 hker) (even_iff_two_dvd.2 h2)
  rw [← h, Nat.factorization_mul (Nat.card_pos).ne' (Nat.card_pos).ne', Finsupp.add_apply, h1,
    zero_add]

theorem odd_card_ker {S H : Type} [Group S] [Finite S] [Group H] (ψ : S →* H)
    (hker : ψ.ker ≤ Subgroup.center S) (hodd : Odd (Nat.card (Subgroup.center S))) :
    Odd (Nat.card ψ.ker) :=
  Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker)

theorem exists_involution_preimage {S H : Type} [Group S] [Finite S] [Group H] (ψ : S →* H)
    (hker : ψ.ker ≤ Subgroup.center S) (hodd : Odd (Nat.card (Subgroup.center S))) {z : H}
    (hz : z ∈ ψ.range) (hz2 : z * z = 1) : ∃ s : S, s * s = 1 ∧ ψ s = z := by
  obtain ⟨s, rfl⟩ := hz
  set m := Nat.card (Subgroup.center S) with hm
  have hs2 : s * s ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact hz2
  have hsc : s * s ∈ Subgroup.center S := hker hs2
  have hpow : (s * s) ^ m = 1 := by
    have := pow_card_eq_one' (G := ↥(Subgroup.center S)) (x := ⟨s * s, hsc⟩)
    exact congrArg Subtype.val this
  refine ⟨s ^ m, ?_, ?_⟩
  · exact ((Commute.refl s).mul_pow m).symm.trans hpow
  · rw [map_pow]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]


structure S1A4Facts {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x))
    (J : Fin 4 → Subgroup G) (y : G) : Prop where
  jc : ∀ i : Fin 3, J i.succ ≤ centralizer ({x} : Set G)
  hk : (⨆ i : Fin 3, (J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) = K
  perf : ⁅(⨆ i, J i : Subgroup G), (⨆ i, J i : Subgroup G)⁆ = (⨆ i, J i : Subgroup G)
  cnt : (Nat.card K).factorization 2 + 1 ≤ (Nat.card ↥(⨆ i, J i : Subgroup G)).factorization 2
  noncomm : ¬ ∀ v ∈ J 2, v * y = y * v
  classes : ∃ a b : G, ∀ z ∈ (⨆ i, J i : Subgroup G), orderOf z = 2 →
    (∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = a) ∨
      ∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = b

theorem s1A4Facts_lin {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (J : Fin 4 → Subgroup G) (p f : ℕ) (F : Type) [Field F] [Finite F]
    (hp : p.Prime) (hF : Nat.card F = p ^ f) (hq : 3 ≤ p ^ f) (hW : WeakCTA4 F J)
    (hlink : S1LinkedLin x K F J) {y : G} (hyJ : y ∈ J 1) (hy2 : orderOf y = 2)
    (hyc : ∀ a ∈ J 1, a * y = y * a) : S1A4Facts x K J y := by
  classical
  obtain ⟨W12, hP⟩ := hW.2 1 2 rfl
  obtain ⟨h2F, hnoncomm⟩ := sp_noncomm_lin (by omega) hP hyJ hy2 hyc
  obtain ⟨U, W', hWCT, hlink'⟩ := hlink
  have hJC : ∀ i : Fin 3, J i.succ ≤ centralizer ({x} : Set G) := fun i => (hlink' i).1
  have hHK : (⨆ i : Fin 3, (J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) = K := by
    rw [Subgroup.map_iSup]
    have h1 : ∀ i : Fin 3, ((J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) =
        (U i).map K.subtype := fun i => (hlink' i).2
    simp only [h1]
    rw [← Subgroup.map_iSup, hWCT.gen, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨ψ, hψr, hψk, hqs, -⟩ := exists_surjection_A4 p f hp hF hq J hW.1 hW.2
  have hperf : ⁅(⨆ i, J i : Subgroup G), (⨆ i, J i : Subgroup G)⁆ = (⨆ i, J i : Subgroup G) :=
    Subgroup.isPerfect_iff.1 hqs.1
  have hoddF : Odd (Nat.card F) := by
    have h2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2F
    have := Fintype.ofFinite F
    have := FiniteField.odd_card_of_char_ne_two h2
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.2 this
  have hKdvd : Nat.card K ∣ Nat.card SL(4, F) := by
    obtain ⟨ψK, hψKr, -⟩ := exists_surjection_iSup p f hp hF hq (n := 3) (le_refl 3) U
      hWCT.comm (fun i j hj => ⟨W' i j, hWCT.pair i j hj⟩)
    have hsurj : Function.Surjective ψK := by
      rw [← MonoidHom.range_eq_top, hψKr, hWCT.gen]
    exact Subgroup.card_dvd_of_surjective hsurj
  have hν : (Nat.card K).factorization 2 ≤ (Nat.card SL(4, F)).factorization 2 :=
    (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (Nat.card_pos).ne').2 hKdvd 2
  have hkerodd := odd_card_ker ψ hψk odd_card_center_lin5
  have hG₁ν : (Nat.card ↥(⨆ i, J i : Subgroup G)).factorization 2 =
      (Nat.card SL(5, F)).factorization 2 := by
    rw [← hψr]
    exact factorization_range_eq ψ hkerodd
  have hcnt : (Nat.card K).factorization 2 + 1 ≤
      (Nat.card ↥(⨆ i, J i : Subgroup G)).factorization 2 := by
    rw [hG₁ν]
    exact (Nat.add_le_add_right hν 1).trans (card2_lin hoddF)
  obtain ⟨d₂, d₄, hd⟩ := invClasses_lin h2F
  have hab : ∃ a b : G, ∀ z ∈ (⨆ i, J i : Subgroup G), orderOf z = 2 →
      (∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = a) ∨
        ∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = b := by
    refine ⟨ψ d₂, ψ d₄, fun z hz hz2 => ?_⟩
    have hzz : z * z = 1 := by rw [← sq, ← hz2]; exact pow_orderOf_eq_one z
    have hzr : z ∈ ψ.range := hψr ▸ hz
    obtain ⟨s, hs2, hsz⟩ := exists_involution_preimage ψ hψk odd_card_center_lin5 hzr hzz
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, map_one] at hsz
      rw [← hsz, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    rcases hd s hs2 hs1 with ⟨g, hg⟩ | ⟨g, hg⟩
    · left
      refine ⟨ψ g⁻¹, hψr ▸ ⟨g⁻¹, rfl⟩, ?_⟩
      have h1 : (ψ g⁻¹)⁻¹ * z * ψ g⁻¹ = ψ (g * s * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, hsz, inv_inv]
      rw [h1, hg]
    · right
      refine ⟨ψ g⁻¹, hψr ▸ ⟨g⁻¹, rfl⟩, ?_⟩
      have h1 : (ψ g⁻¹)⁻¹ * z * ψ g⁻¹ = ψ (g * s * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, hsz, inv_inv]
      rw [h1, hg]
  exact ⟨hJC, hHK, hperf, hcnt, hnoncomm, hab⟩


theorem s1A4Facts_uni {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (J : Fin 4 → Subgroup G) (p f : ℕ) (F : Type) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hW : WeakPhanA4 F p f J) (hlink : S1LinkedUni x K F p f J) {y : G} (hyJ : y ∈ J 1)
    (hy2 : orderOf y = 2) (hyc : ∀ a ∈ J 1, a * y = y * a) : S1A4Facts x K J y := by
  classical
  obtain ⟨W12, hP⟩ := hW.2 1 2 rfl
  obtain ⟨hp2, hnoncomm⟩ := sp_noncomm_uni hF hq hP hyJ hy2 hyc
  obtain ⟨U, W', hWCT, hlink'⟩ := hlink
  have hJC : ∀ i : Fin 3, J i.succ ≤ centralizer ({x} : Set G) := fun i => (hlink' i).1
  have hHK : (⨆ i : Fin 3, (J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) = K := by
    rw [Subgroup.map_iSup]
    have h1 : ∀ i : Fin 3, ((J i.succ).subgroupOf (centralizer ({x} : Set G))).map (proj x) =
        (U i).map K.subtype := fun i => (hlink' i).2
    simp only [h1]
    rw [← Subgroup.map_iSup, hWCT.gen, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨ψ, hψr, hψk, hqs, -⟩ := exists_surjection_A4_statedSU F p f hF hq J hW.1 hW.2
  have hperf : ⁅(⨆ i, J i : Subgroup G), (⨆ i, J i : Subgroup G)⁆ = (⨆ i, J i : Subgroup G) :=
    Subgroup.isPerfect_iff.1 hqs.1
  have hqodd : Odd (p ^ f) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hKdvd : Nat.card K ∣ Nat.card ↥(StatedSU 4 (p ^ f) F) := by
    obtain ⟨ψK, hψKr, -⟩ := exists_surjection_iSup_statedSU F p f hF hq (n := 3) (le_refl 3) U
      hWCT.comm (fun i j hj => ⟨W' i j, hWCT.pair i j hj⟩)
    have hsurj : Function.Surjective ψK := by
      rw [← MonoidHom.range_eq_top, hψKr, hWCT.gen]
    exact Subgroup.card_dvd_of_surjective hsurj
  have hν : (Nat.card K).factorization 2 ≤ (Nat.card ↥(StatedSU 4 (p ^ f) F)).factorization 2 :=
    (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (Nat.card_pos).ne').2 hKdvd 2
  have hkerodd := odd_card_ker ψ hψk (odd_card_center_uni5 hF)
  have hG₁ν : (Nat.card ↥(⨆ i, J i : Subgroup G)).factorization 2 =
      (Nat.card ↥(StatedSU 5 (p ^ f) F)).factorization 2 := by
    rw [← hψr]
    exact factorization_range_eq ψ hkerodd
  have hcnt : (Nat.card K).factorization 2 + 1 ≤
      (Nat.card ↥(⨆ i, J i : Subgroup G)).factorization 2 := by
    rw [hG₁ν]
    exact (Nat.add_le_add_right hν 1).trans (card2_uni hF hqodd)
  obtain ⟨d₂, d₄, hd⟩ := invClasses_uni hF hqodd
  have hab : ∃ a b : G, ∀ z ∈ (⨆ i, J i : Subgroup G), orderOf z = 2 →
      (∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = a) ∨
        ∃ g ∈ (⨆ i, J i : Subgroup G), g⁻¹ * z * g = b := by
    refine ⟨ψ d₂, ψ d₄, fun z hz hz2 => ?_⟩
    have hzz : z * z = 1 := by rw [← sq, ← hz2]; exact pow_orderOf_eq_one z
    have hzr : z ∈ ψ.range := hψr ▸ hz
    obtain ⟨s, hs2, hsz⟩ := exists_involution_preimage ψ hψk (odd_card_center_uni5 hF) hzr hzz
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, map_one] at hsz
      rw [← hsz, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    rcases hd s hs2 hs1 with ⟨g, hg⟩ | ⟨g, hg⟩
    · left
      refine ⟨ψ g⁻¹, hψr ▸ ⟨g⁻¹, rfl⟩, ?_⟩
      have h1 : (ψ g⁻¹)⁻¹ * z * ψ g⁻¹ = ψ (g * s * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, hsz, inv_inv]
      rw [h1, hg]
    · right
      refine ⟨ψ g⁻¹, hψr ▸ ⟨g⁻¹, rfl⟩, ?_⟩
      have h1 : (ψ g⁻¹)⁻¹ * z * ψ g⁻¹ = ψ (g * s * g⁻¹) := by
        rw [map_mul, map_mul, map_inv, hsz, inv_inv]
      rw [h1, hg]
  exact ⟨hJC, hHK, hperf, hcnt, hnoncomm, hab⟩

end CFSG.GH74.Generic.S1
