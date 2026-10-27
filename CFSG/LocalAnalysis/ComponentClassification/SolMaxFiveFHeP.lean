module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenC
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.OuterFixedCore
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterCentQS

public section

namespace CFSG.ComponentClassification.SolMax.FiveFHe

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem pPrimeCore_two_eq_bot_of_oddCore {Y : Type*} [Group Y] (h : CFSG.oddCore Y = ⊥) :
    pPrimeCore 2 Y = ⊥ := by
  have e : CFSG.oddCore Y = pPrimeCore 2 Y := by
    unfold CFSG.oddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]
  rw [← e, h]

theorem false_of_normal_heInnerGrp0
    {K₀ : Subgroup heInnerGrp0} (hK₀n : K₀.Normal)
    (h5 : 5 ∣ Nat.card K₀) (hle : Nat.card K₀ ≤ 20160) : False := by
  obtain ⟨hC, -⟩ := oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one
    heDelta0_injective heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8)
    (by rw [card_heX0]; norm_num) oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])
  have hcard0 : Nat.card heInnerGrp0 = 161280 := by
    rw [hC]
    exact card_heP_cent0
  obtain ⟨ψ, hψ⟩ : ∃ ψ : heInnerGrp0 →* Equiv.Perm (Fin 240),
      ψ = restrictHom heDelta0_injective heInnerGrp0 heInnerGrp0_stab := ⟨_, rfl⟩
  have hψr : ψ.range = heX0.originalSubgroup := by
    rw [hψ]
    exact heInnerRes0_range
  have hker : Nat.card ψ.ker = 2 := by
    have h := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hψr, card_heX0, hcard0] at h
    omega
  have hN : K₀.map ψ = (ψ.comp K₀.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hK₀N : Nat.card K₀ = Nat.card (ψ.comp K₀.subtype).ker * Nat.card (K₀.map ψ) := by
    rw [hN, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker' : Nat.card (ψ.comp K₀.subtype).ker ∣ 2 := by
    rw [← hker, ← Subgroup.card_map_of_injective K₀.subtype_injective]
    refine card_dvd_of_le fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact hy
  have hpos : 0 < Nat.card (ψ.comp K₀.subtype).ker := Nat.card_pos
  have h5N : 5 ∣ Nat.card (K₀.map ψ) := by
    have h1 : 5 ∣ Nat.card (ψ.comp K₀.subtype).ker * Nat.card (K₀.map ψ) := by
      rw [← hK₀N]
      exact h5
    exact (Nat.Coprime.coprime_dvd_right hker' (by norm_num)).dvd_of_dvd_mul_left h1
  have hltN : Nat.card (K₀.map ψ) < 40320 := by
    have h1 : Nat.card (K₀.map ψ) ≤ Nat.card K₀ := by
      rw [hK₀N]
      exact Nat.le_mul_of_pos_left _ hpos
    omega
  refine HeGen.false_of_normal_heX0 (N := K₀.map ψ) ?_ ?_ h5N hltN
  · rw [← hψr]
    exact map_le_range ψ K₀
  · intro g hg n hn
    rw [← hψr] at hg
    obtain ⟨h, rfl⟩ := hg
    obtain ⟨k, hk, rfl⟩ := mem_map.1 hn
    rw [← map_mul, ← map_inv, ← map_mul]
    exact mem_map_of_mem ψ (hK₀n.conj_mem k hk h)

variable {A : Type*} [Group A]

theorem not_hasOddA_cent0
    [IsSimpleGroup A] (hA : Nat.card A = 60) :
    ¬ HasOddA (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) A := by
  intro h
  have hO : pPrimeCore 2 (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) =
      ⊥ := pPrimeCore_two_eq_bot_of_oddCore (heInner0_oddCore card_heP_cent0)
  obtain ⟨S, hS, ⟨e⟩⟩ := exists_mulEquiv_of_hasOddA hO h
  have : IsSimpleGroup S := e.isSimpleGroup
  have hS60 : Nat.card S = 60 := by rw [Nat.card_congr e.toEquiv, hA]
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_of_card_sixty hA
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hc0 : Nat.card (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) =
      161280 := card_heP_cent0
  have hn := normal_of_isSubnormal_simple hS hnab (by rw [hS60, hc0]; norm_num)
  obtain ⟨hC, -⟩ := oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one
    heDelta0_injective heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8)
    (by rw [card_heX0]; norm_num) oddWitness_heX0 (by rw [card_heP_cent0, card_heX0])
  let f : (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) ≃* heInnerGrp0 :=
    MulEquiv.subgroupCongr hC.symm
  have hcard : Nat.card (S.map f.toMonoidHom) = 60 := by
    rw [card_map_of_injective f.injective, hS60]
  exact false_of_normal_heInnerGrp0 (hn.map _ f.surjective) (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num)

theorem not_hasOddA_cent1
    (hA : Nat.card A = 60) :
    ¬ HasOddA (heP ⊓ centralizer {heT1P} : Subgroup (Equiv.Perm (Fin 8330))) A := by
  have hc1 : Nat.card (heP ⊓ centralizer {heT1P} : Subgroup (Equiv.Perm (Fin 8330))) = 21504 :=
    card_heP_cent1
  exact not_hasOddA_of_not_dvd hA (by rw [hc1]; norm_num)

theorem not_hasOddA_outer
    [IsSimpleGroup A]
    (hA : Nat.card A = 60) : ¬ HasOddA heOuterC A := by
  obtain ⟨hDC, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  refine not_hasOddA_of_quasisimple (inclusion heOuterD_le_C) (inclusion_injective _) hq
    (fun S hS x hx => ?_) (exists_mul_ne_of_card_sixty hA) fun k hk hodd => ?_
  · have hxD : (x : Equiv.Perm (Fin 8330)) ∈ heOuterD := by
      rw [hDC]
      have h1 : S.map heOuterC.subtype ≤ ⁅heOuterC, heOuterC⁆ := by
        rw [← hS, map_commutator]
        exact commutator_mono (map_subtype_le _) (map_subtype_le _)
      exact h1 (mem_map_of_mem _ hx)
    exact ⟨⟨x, hxD⟩, Subtype.ext rfl⟩
  · rw [card_heOuterD, hA] at hk
    obtain ⟨m, rfl⟩ := hodd
    omega

theorem not_hasOddA_heP
    [IsSimpleGroup A] (hA : Nat.card A = 60) :
    ¬ HasOddA heP A := by
  have : IsSimpleGroup heP := heP_simple
  have hnab : ∃ a b : heP, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : center heP = ⊤ := eq_top_iff.2 fun g _ => mem_center_iff.2 fun g' => h g' g
    rw [heP_center_eq_bot] at htop
    have h2 := congrArg (fun H : Subgroup heP => Nat.card H) htop
    simp only [card_bot, card_top, card_heP] at h2
    norm_num at h2
  refine not_hasOddA_of_quasisimple (MonoidHom.id heP) Function.injective_id
    (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1 (fun S _ x _ => ⟨x, rfl⟩)
    (exists_mul_ne_of_card_sixty hA) fun k hk hodd => ?_
  rw [card_heP, hA] at hk
  obtain ⟨m, rfl⟩ := hodd
  omega

theorem not_hasOddA_fixedSubgroup_heConjR
    [IsSimpleGroup A] (hA : Nat.card A = 60) (x : heAutGroup)
    (hx2 : orderOf (x : Equiv.Perm (Fin 8330)) = 2) : ¬ HasOddA (fixedSubgroup (heConjR x)) A := by
  intro h
  let e₁ : fixedSubgroup (heConjR x) ≃*
      (heP ⊓ centralizer {(x : Equiv.Perm (Fin 8330))} : Subgroup (Equiv.Perm (Fin 8330))) :=
    ((fixedSubgroup (heConjR x)).equivMapOfInjective heP.subtype heP.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_fixedSubgroup_heConjR x))
  have h1 := h.of_mulEquiv e₁
  by_cases hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP
  · rcases involution_conj_cases hxP hx2 with ⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩
    · rw [hxc] at h1
      exact not_hasOddA_cent0 hA (h1.of_mulEquiv (infCentralizerConjEquiv hc _))
    · rw [hxc] at h1
      exact not_hasOddA_cent1 hA (h1.of_mulEquiv (infCentralizerConjEquiv hc _))
  · obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
    rw [hxg] at h1
    have h2 := h1.of_mulEquiv (infCentralizerConjEquiv hg heAutU)
    rw [← heOuterC_eq] at h2
    exact not_hasOddA_outer hA h2

theorem map_fixedSubgroup_congr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (s : MulAut G) :
    (fixedSubgroup s).map φ.toMonoidHom = fixedSubgroup (MulAut.congr φ s) := by
  ext y
  rw [mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change φ (s (φ.symm (φ x))) = φ x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg φ (show s x = x from hx)
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    change s (φ.symm y) = φ.symm y
    apply φ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy

theorem not_hasOddA_fixedSubgroup_held
    {G : Type*} [Group G] [IsSimpleGroup A]
    (hA : Nat.card A = 60) (Θ : G ≃* heP) (s : MulAut G) (hs : s * s = 1) :
    ¬ HasOddA (fixedSubgroup s) A := by
  intro h
  have hbij := ctbh_full_automorphism_permutation_model.1
  have h0 := h.of_mulEquiv (((fixedSubgroup s).equivMapOfInjective Θ.toMonoidHom
    Θ.injective).trans (MulEquiv.subgroupCongr (map_fixedSubgroup_congr Θ s)))
  obtain ⟨x, hx⟩ := hbij.2 (MulAut.congr Θ s)
  have hxx : x * x = 1 := hbij.1 (by rw [map_mul, hx, map_one, ← map_mul, hs, map_one])
  rw [← hx] at h0
  by_cases hx1 : x = 1
  · rw [hx1, map_one] at h0
    have htop : fixedSubgroup (1 : MulAut heP) = ⊤ := eq_top_iff.2 fun g _ => rfl
    exact not_hasOddA_heP hA ((h0.of_mulEquiv (MulEquiv.subgroupCongr htop)).of_mulEquiv
      Subgroup.topEquiv)
  · have hx2 : orderOf (x : Equiv.Perm (Fin 8330)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq]; exact hxx) hx1
    exact not_hasOddA_fixedSubgroup_heConjR hA x hx2 h0

end CFSG.ComponentClassification.SolMax.FiveFHe
