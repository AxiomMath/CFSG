module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.AGL81I.Section3.PSL2BorelMaximal
public import CFSG.Adapters.LieModelSimple
public import CFSG.RankThree.ThinCatalog.OuterThreeFree
public import CFSG.Quasithin.Background.F918V3T3A
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowLin

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

theorem threeNineOut_psl_two {G : Type} [Group G] [Finite G] {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : f = 2 ∨ f = 3) (hG : StatedClassicalModel G .PSL 2 p f) :
    Subgroup.center G = ⊥ ∧ ¬ p ∣ Nat.card (Outer G) ∧
      (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (Outer G) → q = 3) ∧ 3 ∣ Nat.card G := by
  have hfpos : 0 < f := by
    have := hG.1.2.1
    omega
  let : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup G :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hG
  have hnc : ¬ ∀ a b : G, a * b = b * a := by
    rintro hall
    let F := GaloisField p f
    have hFcard : Nat.card F = p ^ f := GaloisField.card p f hfpos.ne'
    have h4 : 4 ≤ Nat.card F := by
      rw [hFcard]
      calc 4 ≤ 5 := by norm_num
        _ ≤ p := hp5
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hfpos
    obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated 2 p f hfpos hFcard hG
    obtain ⟨a, b, hab⟩ := CFSG.Walter.psl2_exists_mul_ne_mul F h4
    exact hab (by
      have h := hall (e.symm a) (e.symm b)
      simpa using congrArg e h)
  have hdiv : Nat.card (Outer G) ∣ f * Nat.gcd 2 (p ^ f - 1) :=
    CFSG.RankThree.ThinCatalog.outer_card_dvd_of_psl_two hG
  have hgcd : Nat.gcd 2 (p ^ f - 1) ∣ 2 := Nat.gcd_dvd_left 2 _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CFSG.BenderSuzuki.center_eq_bot_of_isSimpleGroup_of_not_commutative hsimple hnc
  · intro hpO
    have hpdvd : p ∣ f * 2 :=
      hpO.trans (hdiv.trans (Nat.mul_dvd_mul_left f hgcd))
    rcases hf with rfl | rfl
    · have hp4 : p ∣ 4 := by simpa using hpdvd
      have hp4' : p ∣ 2 ^ 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hp4
        exact hp4
      have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hp4'
      have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd
      omega
    · have hp6 : p ∣ 6 := by simpa using hpdvd
      have hp6' : p ∣ 2 * 3 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num] at hp6
        exact hp6
      have hp23 : p = 2 ∨ p = 3 := by
        rcases hp.dvd_mul.mp hp6' with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
      omega
  · intro q hq hq2 hqO
    have hqdvd : q ∣ f * 2 :=
      hqO.trans (hdiv.trans (Nat.mul_dvd_mul_left f hgcd))
    rcases hf with rfl | rfl
    · have hq4 : q ∣ 4 := by simpa using hqdvd
      have hq4' : q ∣ 2 ^ 2 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hq4
        exact hq4
      have hq2dvd : q ∣ 2 := hq.dvd_of_dvd_pow hq4'
      have hq_eq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2dvd
      omega
    · have hq6 : q ∣ 6 := by simpa using hqdvd
      have hq6' : q ∣ 2 * 3 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num] at hq6
        exact hq6
      rcases hq.dvd_mul.mp hq6' with h2 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2) hq2
      · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
  · exact CFSG.Quasithin.F918V3T3.three_dvd_card_of_PSL hG

theorem not_isBorelDLocal_psl_two {G : Type} [Group G] [Finite G] {p d f : ℕ} {Y : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : d.Prime) (hdp : d ≠ p) (hdG : d ∣ Nat.card G)
    (hG : StatedClassicalModel G .PSL 2 p f) : ¬ IsBorelDLocal p d Y := by
  intro hY
  have hfpos : 0 < f := by
    have := hG.1.2.1
    omega
  let : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p f
  have hFcard : Nat.card F = p ^ f := GaloisField.card p f hfpos.ne'
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hchar : ((2 : ℕ) : F) = 0 := by simpa using h
    have hp2dvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp hchar
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated 2 p f hfpos hFcard hG
  let Y' : Subgroup (PSL(2, F)) := Y.map e.toMonoidHom
  have hY' : IsBorelDLocal p d Y' := hY.map_equiv e
  have hcardG : Nat.card G = Nat.card (PSL(2, F)) := Nat.card_congr e.toEquiv
  have hdG' : d ∣ Nat.card (PSL(2, F)) := by
    rwa [← hcardG]
  obtain ⟨Q, hQ⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_sylow_unipotent
    (F := F) hFcard
  obtain ⟨g, hY'', hNQ⟩ := hY'.exists_conj hp Q
  set Y'' : Subgroup (PSL(2, F)) := Y'.map (MulAut.conj g).toMonoidHom with hY''def
  have hY''loc : IsBorelDLocal p d Y'' := hY''
  have hNB : Subgroup.normalizer ((Q : Subgroup (PSL(2, F))) : Set (PSL(2, F))) =
      CFSG.PSL2Table.borel F := by
    rw [hQ]
    exact CFSG.GH74.GLS.IVK.L2Borel.normalizer_unipotent_eq h2
  have hborel_le : CFSG.PSL2Table.borel F ≤ Y'' := hNB ▸ hNQ
  rcases borel_overgroup_eq_borel_or_top hborel_le with hmax | htop
  · have hidx : Y''.index = Nat.card F + 1 := by
      rw [hmax]
      letI : Fintype F := Fintype.ofFinite F
      have hcard : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
      rw [hcard, ← CFSG.GH74.GLS.IVK.L2Borel.normalizer_unipotent_eq h2]
      exact (CFSG.AGLEmbedding.KFactProofs.OneLieSylow.card_psl2_unipotent h2).2
    have hmod : Y''.index ≡ 1 [MOD d] := hY''loc.index_modEq_one_of_dvd hd hdG'
    have hdvdq : d ∣ Nat.card F := by
      have h := hmod.symm.dvd'
      rw [hidx] at h
      simpa using h
    have hdvdq' : d ∣ p ^ f := by
      rwa [hFcard] at hdvdq
    have hdp' : d = p :=
      (Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow hdvdq')
    exact hdp hdp'
  · exact absurd htop hY''loc.lt_top.ne

end CFSG.LocalAnalysis.AGL81I.Section3
