module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3TwoElem
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Dual
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open scoped commutatorElement
open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

variable {F : Type} [Field F] [Finite F]

theorem exists_card_eq_two_pow (hF : 2 ∣ Nat.card F) : ∃ f : ℕ, Nat.card F = 2 ^ f := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨p, f, hp, hf, hcard⟩ := (isPrimePow_nat_iff _).1 (FiniteField.isPrimePow_card F)
  have hFc : Nat.card F = p ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hcard.symm
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow (hFc ▸ hF))).symm
  exact ⟨f, hp2 ▸ hFc⟩

theorem false_of_embed_P1_of_isLThreeTwo (hF : 2 ∣ Nat.card F) {Y : Subgroup (SL3 F)}
    (ι : ↥Y →* ↥(P1 : Subgroup (SL3 F))) (hι : Function.Injective ι)
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : False := by
  obtain ⟨R, hR, a, ha, b, hb, hab⟩ := exists_two_subgroup_comm_not_mem_pCore hY
  let φ : ↥Y →* GL (Fin 2) F := rho1.comp ι
  have hcomm := gl2_two_group_comm hF (hR.map φ) (φ a) ⟨a, ha, rfl⟩ (φ b) ⟨b, hb, rfl⟩
  have h1 : φ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  apply hab
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow hF
  have hQp : IsPGroup 2 (Q1 : Subgroup (SL3 F)) :=
    IsPGroup.of_card (n := 2 * f) (by rw [card_Q1, hf, pow_mul'])
  have hmem : ∀ x : φ.ker, (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈
      (Q1 : Subgroup (SL3 F)) := fun x => mem_ker_rho1.mp x.2
  let ψ : φ.ker →* (Q1 : Subgroup (SL3 F)) :=
    ((P1 : Subgroup (SL3 F)).subtype.comp (ι.comp φ.ker.subtype)).codRestrict _ hmem
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (hι (Subtype.ext this))
  have hkerp : IsPGroup 2 φ.ker := hQp.of_injective ψ hψ
  have hle : φ.ker ≤ CFSG.pCore 2 ↥Y := by
    unfold CFSG.pCore
    exact le_sSup ⟨inferInstance, hkerp⟩
  exact hle h1

theorem false_of_le_P1_of_isLThreeTwo (hF : 2 ∣ Nat.card F) {Y : Subgroup (SL3 F)}
    (hYP : Y ≤ P1) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : False :=
  false_of_embed_P1_of_isLThreeTwo hF (Subgroup.inclusion hYP) (Subgroup.inclusion_injective hYP)
    hY

theorem false_of_le_P2_of_isLThreeTwo (hF : 2 ∣ Nat.card F) {Y : Subgroup (SL3 F)}
    (hYP : Y ≤ P2) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : False := by
  refine false_of_embed_P1_of_isLThreeTwo hF
    ((dualAut.toMonoidHom.comp Y.subtype).codRestrict (P1 : Subgroup (SL3 F))
      (fun y => dualAut_mem_P1 (hYP y.2))) ?_ hY
  intro x y hxy
  have := congrArg Subtype.val hxy
  exact Subtype.ext (dualAut.injective this)

theorem false_of_transitive_of_isLThreeTwo (hF : 2 ∣ Nat.card F) {W Y : Subgroup (SL3 F)}
    (hYW : Y ≤ W) (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v)
    (hb : W ⊓ P1 ⊓ Q1 = ⊥) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : False := by
  obtain ⟨R, hR, a, ha, b, hb', hab⟩ := exists_two_subgroup_comm_not_mem_pCore hY
  let T : Subgroup ↥W := (P1 : Subgroup (SL3 F)).subgroupOf W
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 : T.index = Nat.card F ^ 2 + Nat.card F + 1 := by
      change (P1 : Subgroup (SL3 F)).relIndex W = _
      rw [relIndex_P1_of_transitive htr, index_P1]
    rw [h1]
    intro hd
    have hev : 2 ∣ Nat.card F ^ 2 + Nat.card F :=
      dvd_add (dvd_pow hF two_ne_zero) hF
    exact absurd ((Nat.dvd_add_right hev).mp hd) (by norm_num)
  let ι : ↥T →* ↥(P1 : Subgroup (SL3 F)) :=
    ((W.subtype).comp T.subtype).codRestrict _ (fun x => x.2)
  let ρ : ↥T →* GL (Fin 2) F := rho1.comp ι
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hQ : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ (Q1 : Subgroup (SL3 F)) :=
      mem_ker_rho1.mp hx
    have hxW : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ W := (x : ↥W).2
    have hxP : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ (P1 : Subgroup (SL3 F)) :=
      (ι x).2
    have : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ (⊥ : Subgroup (SL3 F)) :=
      hb ▸ ⟨⟨hxW, hxP⟩, hQ⟩
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp this))
  have hcomm := two_subgroup_comm_of_odd_index hTidx ρ hρ (fun Q hQ => gl2_two_group_comm hF hQ)
    (R := R.map (Subgroup.inclusion hYW)) (hR.map _)
    (Subgroup.inclusion hYW a) ⟨a, ha, rfl⟩ (Subgroup.inclusion hYW b) ⟨b, hb', rfl⟩
  have hab' : a * b = b * a :=
    Subgroup.inclusion_injective hYW (by rw [map_mul, map_mul]; exact hcomm)
  exact hab ((commutatorElement_eq_one_iff_mul_comm.mpr hab') ▸ (CFSG.pCore 2 ↥Y).one_mem)

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
