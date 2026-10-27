module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.CharacterTheory.PSL2Table.Basic
import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactL2UnipotentCentralizer : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ n → ∀ (U : Sylow p (PSL2GF p n))
    (α : MulAut (PSL2GF p n)), (∀ u ∈ (U : Subgroup (PSL2GF p n)), α u = u) →
      ∃ u ∈ (U : Subgroup (PSL2GF p n)), α = MulAut.conj u

@[expose] def KFactL2AutPCard : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ n → ∀ A : Subgroup (MulAut (PSL2GF p n)),
    IsPGroup p A → Nat.card A ∣ p ^ n * n

theorem nonempty_mulEquiv_sylow_psl2GF {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (T : Sylow p (PSL2GF p n)) : Nonempty (Multiplicative (GaloisField p n) ≃* T) :=
  BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
    (GaloisField.card p n (by omega)) T

theorem psl2GF_sylow (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (T : Sylow p (PSL2GF p n)) :
    IsElemAbelian p (T : Subgroup (PSL2GF p n)) ∧
      Nat.card (T : Subgroup (PSL2GF p n)) = p ^ n := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sylow_psl2GF hn T
  refine ⟨⟨e.surjective.isMulCommutative inferInstance, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have h : (⟨x, hx⟩ : (T : Subgroup (PSL2GF p n))) ^ p = 1 := by
      rw [← ha, ← map_pow, hap, map_one]
    simpa using congrArg Subtype.val h
  · rw [← Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p n (by omega)]

section Borel

open CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open scoped MatrixGroups

theorem normalizer_unipotent_eq_borel {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    Subgroup.normalizer (unipotent F : Set PSL(2, F)) = borel F := by
  have h2 := Ring.two_ne_zero hF
  apply le_antisymm
  · intro g hg
    have hx := mk_unip_mem_unipotent (1 : F)
    have hx1 : mk (unip (1 : F)) ≠ 1 := fun h => one_ne_zero ((mk_unip_eq_one_iff h2 1).mp h)
    exact (unipotent_TI hF _ hx hx1 g).mp ((Subgroup.mem_normalizer_iff.mp hg _).mp hx)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · rw [hx1, mul_one, mul_inv_cancel]
        exact (unipotent F).one_mem
      · exact (unipotent_TI hF x hx hx1 g).mpr hg
    · intro hx
      by_cases hx1 : g * x * g⁻¹ = 1
      · have e : x = 1 := by
          have e' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
          rw [e', hx1, mul_one, inv_mul_cancel]
        rw [e]
        exact (unipotent F).one_mem
      · have h := (unipotent_TI hF _ hx hx1 g⁻¹).mpr ((borel F).inv_mem hg)
        have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rwa [e] at h

theorem exists_sylow_eq_unipotent_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    ∃ U : Sylow p (PSL2GF p n), (U : Subgroup (PSL2GF p n)) = unipotent (GaloisField p n) := by
  let : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  have hcard : Nat.card (unipotent (GaloisField p n)) = p ^ n := by
    rw [card_unipotent (Ring.two_ne_zero hF), ← Nat.card_eq_fintype_card,
      GaloisField.card p n (by omega)]
  obtain ⟨U, hU⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  refine ⟨U, (Subgroup.eq_of_le_of_card_ge hU ?_).symm⟩
  rw [hcard, (psl2GF_sylow p n hn U).2]

theorem psl2GF_borelCoatom (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (T : Sylow p (PSL2GF p n)) :
    IsCoatom (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))) := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨U, hU⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (PSL2GF p n) U T
  have hgU : ((g • U : Sylow p (PSL2GF p n)) : Subgroup (PSL2GF p n)) =
      (unipotent (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, hU]
    rfl
  rw [hgU, normalizer_map_conj, normalizer_unipotent_eq_borel hF, isCoatom_map_conj_iff,
    ← stabilizer_lineZero]
  exact isCoatom_stabilizer _

end Borel

theorem isSimpleGroup_psl2GF {p n : ℕ} [Fact p.Prime] (h4 : 4 ≤ p ^ n) :
    IsSimpleGroup (PSL2GF p n) := by
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h4
    omega
  exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rwa [GaloisField.card p n hn])

theorem isSimpleGroup_psl2GF_of_two_le {p n : ℕ} [Fact p.Prime] (hn : 2 ≤ n) :
    IsSimpleGroup (PSL2GF p n) :=
  isSimpleGroup_psl2GF (calc 4 = 2 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le 2
    _ ≤ p ^ n := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn)

theorem prime_dvd_card_psl2GF {p n ℓ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hℓ : ℓ.Prime) (hℓdvd : ℓ ∣ p ^ (2 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 2 * n → ¬ ℓ ∣ p ^ k - 1) :
    ℓ ∣ Nat.card (PSL2GF p n) := by
  have hp : p.Prime := Fact.out
  rw [CFSG.SectionRank.OddCover.card_psl_two hp hp2 (GaloisField.card p n (by omega))]
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    refine hprim 1 one_pos (by omega) ?_
    rw [pow_one]
    exact (Nat.Prime.even_sub_one hp hp2).two_dvd
  have hsq : (p ^ n) ^ 2 - 1 = p ^ (2 * n) - 1 := by rw [← pow_mul, mul_comm]
  have hev : 2 ∣ (p ^ n) ^ 2 - 1 := by
    have hodd : Odd ((p ^ n) ^ 2) := (hp.odd_of_ne_two hp2).pow.pow
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  refine Dvd.dvd.mul_left ?_ _
  obtain ⟨c, hc⟩ := hev
  rw [hc, Nat.mul_div_cancel_left c two_pos]
  rw [← hsq, hc] at hℓdvd
  exact (Nat.Prime.dvd_mul hℓ).mp hℓdvd |>.resolve_left
    (fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h))

end CFSG.AGLEmbedding
