module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42T2
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.AutPerm
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open scoped commutatorElement

private def fixCount (t : Tab) : ℕ :=
  (Finset.univ.filter (fun j : Fin 45 => t.getD (j : ℕ) 0 = (j : ℕ))).card

private def invFixB (elems : List Tab) : Bool :=
  elems.all fun t => (t == tid) || !(tmul t t == tid) || (fixCount t % 3 != 0)

private lemma invFixB_check : invFixB S0elems = true := by
  decide +kernel

private lemma fixCount_eq {x : Equiv.Perm (Fin 45)} {t : Tab} (hr : Rep x t) :
    fixCount t = Nat.card {j : Fin 45 // x j = j} := by
  rw [fixCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [Fin.ext_iff, ← hr.2 j j.2]

private lemma not_three_dvd_fixed_of_S0 {x : Equiv.Perm (Fin 45)} (hxS : x ∈ S0)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ¬ 3 ∣ Nat.card {j : Fin 45 // x j = j} := by
  obtain ⟨t, ht, hr⟩ := exists_mem_tab S0_enumOK hxS
  have htab : tmul t t = tid := by
    have h1 : Rep (x * x) (tmul t t) := rep_mul hr hr
    rw [hx2] at h1
    exact rep_eq_tab h1 rep_one
  have hne : t ≠ tid := by
    intro h
    rw [h] at hr
    exact hx1 (rep_unique hr rep_one)
  have hchk : fixCount t % 3 ≠ 0 := by
    have h := List.all_eq_true.1 invFixB_check t ht
    have hne' : (t == tid) = false := beq_eq_false_iff_ne.2 hne
    have htab' : (tmul t t == tid) = true := by rw [htab]; rfl
    simp only [invFixB, hne', htab', Bool.not_true, Bool.false_or, bne_iff_ne] at h
    exact h
  rw [← fixCount_eq hr]
  intro h
  exact hchk (Nat.mod_eq_zero_of_dvd h)

private lemma card_fixed_conj (x g : Equiv.Perm (Fin 45)) :
    Nat.card {j : Fin 45 // (g⁻¹ * x * g) j = j} = Nat.card {j : Fin 45 // x j = j} := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  show Fintype.card ↑(Function.fixedPoints ⇑(g⁻¹ * x * g)) =
    Fintype.card ↑(Function.fixedPoints ⇑x)
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints,
    show g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹ by rw [inv_inv],
    Equiv.Perm.cycleType_conj]

private lemma exists_conj_mem_S0 {x : Equiv.Perm (Fin 45)} (hxP : x ∈ P) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : ∃ g ∈ P, g⁻¹ * x * g ∈ S0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let xP : ↥P := ⟨x, hxP⟩
  have hxP2 : xP ^ 2 = 1 := Subtype.ext hx2
  have hxP1 : xP ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hord : orderOf xP = 2 := orderOf_eq_prime hxP2 hxP1
  have hp : IsPGroup 2 (Subgroup.zpowers xP) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨S', hS'⟩ := hp.exists_le_sylow
  let S : Subgroup (Equiv.Perm (Fin 45)) := S'.toSubgroup.map P.subtype
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  have hScard : Nat.card S = 2 ^ (Nat.card P).factorization 2 := by
    rw [show S = S'.toSubgroup.map P.subtype from rfl,
      Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity,
      card_P, factorization_two_25920]
  obtain ⟨g, hgP, hSg⟩ := exists_conj_eq_of_card S0_le_P hSP card_S0_eq_P hScard
  refine ⟨g, hgP, ?_⟩
  have hxS : x ∈ S := ⟨xP, hS' (Subgroup.mem_zpowers xP), rfl⟩
  rw [hSg] at hxS
  obtain ⟨s, hs, hsx⟩ := hxS
  have hgs : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hgs]; exact hs

private lemma not_three_dvd_fixed_of_involution {x : Equiv.Perm (Fin 45)} (hxP : x ∈ P)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : ¬ 3 ∣ Nat.card {j : Fin 45 // x j = j} := by
  obtain ⟨g, _, hgS⟩ := exists_conj_mem_S0 hxP hx2 hx1
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have h2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hxx]; group
  have hne : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have h := not_three_dvd_fixed_of_S0 hgS h2 hne
  rwa [card_fixed_conj x g] at h

theorem u42InvFact_holds : U42InvFact := by
  intro Y _instY hcat F z hFcard hz2 hz1 hzc
  obtain ⟨e⟩ := bridge_u4two hcat
  let φ : Y →* Equiv.Perm (Fin 45) := psi.comp e.toMonoidHom
  have hφinj : Function.Injective φ := psi_injective'.comp e.injective
  have hφrange : φ.range = P := by
    rw [← MonoidHom.map_range psi e.toMonoidHom,
      MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective, Subgroup.map_top]
    exact range_psi_eq
  let F1 : Subgroup (Equiv.Perm (Fin 45)) := F.map φ
  have hF1card : Nat.card F1 = 9 := by
    rw [Subgroup.card_map_of_injective hφinj, hFcard]
  have hF1P : F1 ≤ P := by
    rw [← hφrange]; exact Subgroup.map_le_range φ F
  have hF1c : ∀ f ∈ F1, φ z * f = f * φ z := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, hzc f hf]
  have hz2' : φ z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hz1' : φ z ≠ 1 := fun h => hz1 (hφinj (h.trans (map_one φ).symm))
  have hzP : φ z ∈ P := by rw [← hφrange]; exact ⟨z, rfl⟩
  let Fix := {j : Fin 45 // φ z j = j}
  have hFixn : ¬ 3 ∣ Nat.card Fix := not_three_dvd_fixed_of_involution hzP hz2' hz1'
  have hFix : ∀ f ∈ F1, ∀ j : Fix, φ z (f j.1) = f j.1 := by
    intro f hf j
    have hc := hF1c f hf
    calc φ z (f j.1) = (φ z * f) j.1 := rfl
      _ = (f * φ z) j.1 := by rw [hc]
      _ = f (φ z j.1) := rfl
      _ = f j.1 := by rw [j.2]
  letI : MulAction ↥F1 Fix :=
    { smul := fun f j => ⟨f.1 j.1, hFix f.1 f.2 j⟩
      one_smul := fun j => Subtype.ext rfl
      mul_smul := fun f g j => Subtype.ext (Equiv.Perm.mul_apply f.1 g.1 j.1) }
  have hF13 : IsPGroup 3 ↥F1 :=
    IsPGroup.of_card (n := 2) (by rw [hF1card]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hF13 Fix hFixn
  rw [MulAction.mem_fixedPoints] at hj
  have hfixj : ∀ f ∈ F1, f j.1 = j.1 := by
    intro f hf
    exact congrArg Subtype.val (hj ⟨f, hf⟩)
  have hF1cent : F1 ≤ Subgroup.centralizer ({tauPerm j.1} : Set (Equiv.Perm (Fin 45))) := by
    intro f hf
    exact (mem_centralizer_tauPerm_iff (hF1P hf) j.1).2 (hfixj f hf)
  have hFc : ∀ f ∈ F1, tauPerm j.1 * f = f * tauPerm j.1 := by
    intro f hf
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hF1cent hf)).symm
  obtain ⟨g, hgP, hg0⟩ := exists_mem_P_apply_zero j.1
  let S : Subgroup (Equiv.Perm (Fin 45)) := S0.map (MulAut.conj g).toMonoidHom
  have hSP : S ≤ P := by
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    exact mul_mem (mul_mem hgP (S0_le_P hs0)) (inv_mem hgP)
  have hScard : Nat.card S = 64 := by
    rw [show S = S0.map (MulAut.conj g).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, card_S0]
  have hS2 : IsPGroup 2 ↥S := IsPGroup.of_card (n := 6) (by rw [hScard]; norm_num)
  have hconj0 : g * tauPerm 0 * g⁻¹ = tauPerm j.1 := by
    rw [conj_tauPerm hgP (0 : Fin 45), hg0]
  have htau0S0 : tauPerm (0 : Fin 45) ∈ S0 := by
    have h := wperm_mem_gen (ws := S0gens) (w := [0]) (by simp [S0gens])
    simpa [wperm] using h
  have htaujS : tauPerm j.1 ∈ S :=
    ⟨tauPerm 0, htau0S0, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hconj0⟩
  have hSc : ∀ s ∈ S, tauPerm j.1 * s = s * tauPerm j.1 := by
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    have hc : s0 * tauPerm 0 = tauPerm 0 * s0 :=
      Subgroup.mem_centralizer_singleton_iff.1 (S0_le_H0 hs0).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hconj0]
    calc (g * tauPerm 0 * g⁻¹) * (g * s0 * g⁻¹) = g * (tauPerm 0 * s0) * g⁻¹ := by group
      _ = g * (s0 * tauPerm 0) * g⁻¹ := by rw [hc]
      _ = (g * s0 * g⁻¹) * (g * tauPerm 0 * g⁻¹) := by group
  have htauj1 : tauPerm j.1 ≠ 1 := tauPerm_ne_one j.1
  obtain ⟨T1, hT1P, _, hT1card, hT1n, x, hxT1, y, hyF1, hxy⟩ :=
    YS09U42T2.finite_P_part (tauPerm_mem j.1) (by rw [pow_two]; exact tauPerm_mul_self j.1)
      htauj1 hSP hS2 hScard htaujS hSc hF1P hFc hF1card
  let T : Subgroup Y := T1.comap φ
  have hT1range : T1 ≤ φ.range := by rw [hφrange]; exact hT1P
  have hmapT : T.map φ = T1 := Subgroup.map_comap_eq_self hT1range
  have hTcard : Nat.card T = 32 := by
    have h1 := Subgroup.card_map_of_injective (f := φ) hφinj (K := T)
    rw [hmapT, hT1card] at h1
    exact h1.symm
  have hFT : F ≤ Subgroup.normalizer (T : Set Y) := by
    rw [Subgroup.le_normalizer_iff]
    intro f hf t ht
    have hmem : φ (f * t * f⁻¹) ∈ T1 := by
      have h := hT1n (φ f) (Subgroup.mem_map_of_mem φ hf) (φ t) ht
      simpa [map_mul, map_inv] using h
    exact hmem
  have hcomm : (⁅T, F⁆ : Subgroup Y) ≠ ⊥ := by
    intro hbot
    obtain ⟨xb, hxbx⟩ := MonoidHom.mem_range.1 (hT1range hxT1)
    have hxbT : xb ∈ T := by
      show φ xb ∈ T1
      rw [hxbx]; exact hxT1
    obtain ⟨yb, hybF, hyby⟩ := Subgroup.mem_map.1 hyF1
    have hne : xb * yb ≠ yb * xb := by
      intro h
      apply hxy
      rw [← hxbx, ← hyby, ← map_mul, ← map_mul, h]
    have hmem : ⁅xb, yb⁆ ∈ (⁅T, F⁆ : Subgroup Y) :=
      Subgroup.commutator_mem_commutator hxbT hybF
    rw [hbot] at hmem
    have h1 : ⁅xb, yb⁆ = 1 := by simpa using hmem
    exact hne (commutatorElement_eq_one_iff_mul_comm.1 h1)
  exact ⟨T, IsPGroup.of_card (n := 5) (by rw [hTcard]; norm_num),
    by rw [hTcard]; norm_num, hFT, hcomm⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
