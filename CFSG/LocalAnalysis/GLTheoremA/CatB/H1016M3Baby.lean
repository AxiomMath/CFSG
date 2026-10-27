module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3BabyLocal
public import CFSG.Monster.Existence.BabyOrder
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltUtil

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open CFSG.Blueprint CFSG.Monster.B.Pinned Subgroup
  CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.BabySyl

section Local


private theorem exists_sylow_le_comap (h13 : (Nat.card NativeSporadic.B).factorization 3 = 13) :
    ∃ T : Sylow 3 NativeSporadic.B,
      (T : Subgroup NativeSporadic.B) ≤ (sylS.comap rhoThree).map LThree.subtype := by
  haveI := finite_B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : sylS ≤ rhoThree.range := by rw [range_rhoThree]; exact sylS_le_KThree
  have h9 : 3 ^ 9 ∣ Nat.card rhoThree.ker := by
    have := card_dvd_of_le QThree_le_ker
    rwa [Nat.card_congr (subgroupOfEquivOfLe QThree_le_LThree).toEquiv, card_QThree] at this
  have hdvd : 3 ^ 13 ∣ Nat.card ((sylS.comap rhoThree).map LThree.subtype) := by
    rw [card_map_of_injective LThree.subtype_injective,
      KD264Util.card_comap_eq_mul rhoThree sylS hle, card_sylS,
      show 3 ^ 13 = 81 * 3 ^ 9 by norm_num]
    exact Nat.mul_dvd_mul_left 81 h9
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨Sylow.ofCard (K.map (Subgroup.subtype _)) ?_, ?_⟩
  · rw [card_map_of_injective (Subgroup.subtype_injective _), hK, h13]
  · rw [Sylow.coe_ofCard]
    exact map_subtype_le K

private theorem card_le_of_isElemAbelian
    (h13 : (Nat.card NativeSporadic.B).factorization 3 = 13) {E : Subgroup NativeSporadic.B}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 6 := by
  haveI := finite_B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 e e.2)⟩
  obtain ⟨T, hT⟩ := exists_sylow_le_comap h13
  obtain ⟨S', hES'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq NativeSporadic.B S' T
  set φ := (MulAut.conj g).toMonoidHom with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MulEquiv.coe_toMonoidHom]
    exact (MulAut.conj g).injective
  have hgS : ((g • S' : Sylow 3 NativeSporadic.B) : Subgroup NativeSporadic.B) =
      (S' : Subgroup NativeSporadic.B).map φ := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hle : E.map φ ≤ (sylS.comap rhoThree).map LThree.subtype := by
    rw [← hg, hgS] at hT
    exact (map_mono hES').trans hT
  have hEL : E.map φ ≤ LThree := hle.trans (map_subtype_le _)
  have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    (isMulCommutative_iff_of_setLike (M := NativeSporadic.B) (s := E)).1 hE.1
  have hF3 : IsPGroup 3 ((E.map φ).subgroupOf LThree) := by
    rw [← Subgroup.comap_subtype]
    exact (hEp.map φ).comap_subtype
  have h := card_le_of_le_comap_sylS h13 (F := (E.map φ).subgroupOf LThree)
    (fun f hf => (mem_map_iff_mem LThree.subtype_injective).1 (hle (mem_subgroupOf.1 hf)))
    (fun a ha b hb => by
      obtain ⟨a', ha', e₁⟩ := mem_subgroupOf.1 ha
      obtain ⟨b', hb', e₂⟩ := mem_subgroupOf.1 hb
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← e₁, ← e₂, ← map_mul, ← map_mul,
        hab a' ha' b' hb'])
    hF3
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv, card_map_of_injective hinj] at h

end Local


theorem card_le_of_isElemAbelian_three_B (E : Subgroup CFSG.Blueprint.NativeSporadic.B)
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 6 := by
  have h2 : CFSG.Open.monsterBabyOrder =
      3 ^ 13 * (2 ^ 41 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47) := by
    unfold CFSG.Open.monsterBabyOrder
    ring
  have h13 : (Nat.card NativeSporadic.B).factorization 3 = 13 := by
    rw [CFSG.Monster.Existence.card_nativeB, h2, Nat.factorization_mul (by positivity)
      (by positivity), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  exact card_le_of_isElemAbelian h13 hE

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

end
