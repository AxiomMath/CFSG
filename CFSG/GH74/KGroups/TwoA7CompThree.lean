module

public import CFSG.GH74.KGroups.TwoA7Odd
public import CFSG.GH74.KGroups.TwoA7Small
public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting
public import CFSG.GH74.GLS.IVK.A7.Core
public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.GH74.KGroups.TwoA7Fixed

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG CFSG.ClassicalInvolution.Hat2A7 CFSG.ClassicalInvolution.QuaternionStructure
  CFSG.Assembly.LowTwoRank Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
open scoped MatrixGroups

section Three

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

omit [Finite E] in
theorem oddCore_eq_bot_of_cover (h : IsDoubleCoverA7 π z) : CFSG.oddCore E = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro M ⟨hM, hodd⟩
  have hord : ∀ m ∈ M, Odd (orderOf m) := fun m hm =>
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard M hm)
  have hzM : z ∉ M := fun hz => by
    have h1 := hord z hz
    rw [orderOf_z h] at h1
    exact absurd h1 (by decide)
  have hsimple : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by norm_num)
  have : (M.map π).Normal := hM.map π h.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map π) with h0 | h0
  · rw [eq_bot_iff]
    intro m hm
    have h1 : π m ∈ M.map π := Subgroup.mem_map_of_mem π hm
    rw [h0, Subgroup.mem_bot] at h1
    rcases (h.ker_iff m).1 h1 with h2 | h2
    · rw [h2]
      exact Subgroup.one_mem _
    · exact absurd (h2 ▸ hm) hzM
  · exfalso
    have hdvd : 2 ∣ Nat.card A7 := by rw [card_A7]; norm_num
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := A7) 2 hdvd
    have hy' : y ∈ M.map π := by rw [h0]; exact Subgroup.mem_top y
    obtain ⟨m, hm, rfl⟩ := hy'
    have h1 : orderOf (π m) ∣ orderOf m := orderOf_map_dvd π m
    rw [hy] at h1
    exact absurd ((hord m hm).of_dvd_nat h1) (by decide)

theorem quaternionSetting_four
    (h : IsDoubleCoverA7 π z) : QuaternionSetting E z 4 where
  three_le := by norm_num
  orderOf_eq_two := orderOf_z h
  mem_center := z_mem_center h
  eq_of_orderOf_eq_two := by
    intro t ht
    have ht2 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, pow_two] at this
    rcases h.eq_one_or_eq_z_of_sq_eq_one ht2 with h1 | h1
    · rw [h1, orderOf_one] at ht
      omega
    · exact h1
  sylow_equiv := fun P => sylow_quaternion h P
  oddCore_eq_bot := oddCore_eq_bot_of_cover h

theorem nonempty_equiv_sl23_comap
    (h : IsDoubleCoverA7 π z) (X : Subgroup E) (hzX : z ∈ X)
    (ρ : ↥X →* Perm (Fin 4)) (hker : ∀ x : ↥X, ρ x = 1 ↔ (x : E) = 1 ∨ (x : E) = z)
    (hrange : alternatingGroup (Fin 4) ≤ ρ.range) :
    Nonempty (↥((alternatingGroup (Fin 4)).comap ρ) ≃* SL(2, ZMod 3)) := by
  have hF : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := quaternionSetting_four h
  have : (Subgroup.zpowers z).Normal := hQ.normal_zpowers
  set L : Subgroup ↥X := (alternatingGroup (Fin 4)).comap ρ with hL
  set LE : Subgroup E := L.map X.subtype with hLE
  set N : Subgroup (E ⧸ Subgroup.zpowers z) :=
    LE.map (QuotientGroup.mk' (Subgroup.zpowers z)) with hN
  have hz1 : ρ ⟨z, hzX⟩ = 1 := (hker ⟨z, hzX⟩).2 (Or.inr rfl)
  have hzL : z ∈ LE := by
    refine ⟨⟨z, hzX⟩, ?_, rfl⟩
    show ρ ⟨z, hzX⟩ ∈ alternatingGroup (Fin 4)
    rw [hz1]
    exact Subgroup.one_mem _
  have hcomap : N.comap (QuotientGroup.mk' (Subgroup.zpowers z)) = LE := by
    apply Subgroup.comap_map_eq_self
    rw [QuotientGroup.ker_mk']
    exact Subgroup.zpowers_le.2 hzL
  let ψ : ↥L →* ↥N :=
    ((QuotientGroup.mk' (Subgroup.zpowers z)).comp (X.subtype.comp L.subtype)).codRestrict N
      (fun x => ⟨(x : E), ⟨(x : ↥X), x.2, rfl⟩, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨e, he, hey⟩ := Subgroup.mem_map.1 y.2
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 he
    exact ⟨⟨l, hl⟩, Subtype.ext hey⟩
  let θ : ↥L →* ↥(alternatingGroup (Fin 4)) := (ρ.comp L.subtype).codRestrict _ (fun x => x.2)
  have hθ : Function.Surjective θ := by
    intro a
    obtain ⟨x, hx⟩ := hrange a.2
    have hxL : x ∈ L := by
      show ρ x ∈ alternatingGroup (Fin 4)
      rw [hx]
      exact a.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  have hkers : ψ.ker = θ.ker := by
    ext x
    have h1 : ψ x = 1 ↔ ((x : ↥X) : E) ∈ Subgroup.zpowers z := by
      rw [← QuotientGroup.eq_one_iff ((x : ↥X) : E)]
      exact Subtype.ext_iff
    have h2 : θ x = 1 ↔ ((x : ↥X) : E) = 1 ∨ ((x : ↥X) : E) = z := by
      rw [← hker]
      exact Subtype.ext_iff
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, h1, h2,
      mem_zpowers_iff_of_orderOf_eq_two (orderOf_z h)]
  obtain ⟨eN⟩ := nonempty_mulEquiv_of_ker_eq ψ θ hψ hθ hkers
  let eN' : ↥N ≃* CFSG.GorensteinWalter.PSL2 (ZMod 3) :=
    eN.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup.symm
  have hchar : ringChar (ZMod 3) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  obtain ⟨eSL⟩ := hQ.exists_mulEquiv_specialLinearGroup hchar N eN'
  exact ⟨((L.equivMapOfInjective X.subtype X.subtype_injective).trans
    (MulEquiv.subgroupCongr hcomap.symm)).trans eSL⟩

end Three

section Fixed

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem hasSolvableTwoComponentSL23_fixed
    (h : IsDoubleCoverA7 π z) (φ : MulAut E)
    (hσ : (h.autPerm φ).cycleType = {2, 2, 2}) :
    HasSolvableTwoComponentSL23 ↥(fixedSubgroup E φ) := by
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.A7.centralizer_A7_two_two_two_equiv hσ
  let e' : ↥(centA (h.autPerm φ)) ≃* Perm (Fin 4) := e
  set ρ := rhoX h φ e' with hρ
  let zX : ↥(fixedSubgroup E φ) := ⟨z, z_mem_fixed h φ⟩
  have hzX : orderOf zX = 2 := by rw [Subgroup.orderOf_mk, orderOf_z h]
  have hker : ∀ x : ↥(fixedSubgroup E φ), ρ x = 1 → x = 1 ∨ x = zX := by
    intro x hx
    rcases (rhoX_eq_one_iff h φ e' x).1 hx with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  have hrange : alternatingGroup (Fin 4) ≤ ρ.range := alternatingGroup_le_range_rhoX h φ e'
  have hX : pPrimeCore 2 ↥(fixedSubgroup E φ) = ⊥ :=
    pPrimeCore_eq_bot_of_rho ρ hzX hker V4 (V4_le_alternating.trans hrange) hBodd_V4 hC_V4
  have : ((alternatingGroup (Fin 4)).comap ρ).Normal := inferInstance
  obtain ⟨eSL⟩ := nonempty_equiv_sl23_comap h (fixedSubgroup E φ) (z_mem_fixed h φ) ρ
    (rhoX_eq_one_iff h φ e') hrange
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 ↥(fixedSubgroup E φ))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hX]
  have hF : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨((alternatingGroup (Fin 4)).comap ρ).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(fixedSubgroup E φ))), ?_, ZMod 3, inferInstance,
    inferInstance, Nat.card_zmod 3, ?_⟩
  · exact (Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)).isSubnormal
  · exact ⟨((Subgroup.equivMapOfInjective _ _ hinj).symm.trans eSL).trans
      (specialLinearGroupEquivStatedSL 2 (ZMod 3))⟩

end Fixed

end CFSG.GH74.KGroups.TwoA7
