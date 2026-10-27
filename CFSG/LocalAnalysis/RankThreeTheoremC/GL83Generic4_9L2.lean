module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9L2b
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.GorensteinWalter CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

theorem kFactL2UnipotentCoprime : KFactL2UnipotentCoprime := by
  intro p _ hp5 G _ _ L hL u huL hup V hVL hVp hN
  obtain ⟨e⟩ := hL
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hpg : IsPGroup p (Subgroup.zpowers (⟨u, huL⟩ : L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hup, pow_one]
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  have hU : IsSylowOf p ((Q : Subgroup L).map L.subtype) L := ⟨Q, rfl⟩
  have huU : u ∈ (Q : Subgroup L).map L.subtype :=
    ⟨⟨u, huL⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl hK e hU
  obtain ⟨a, ha⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 ((he' ⟨u, huL⟩).1 huU)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : e' ⟨u, huL⟩ = 1 := by rw [ha]; simp
    have h2 : u = 1 := congrArg Subtype.val (e'.injective (h1.trans (map_one e').symm))
    rw [h2, orderOf_one] at hup
    exact (Fact.out : p.Prime).one_lt.ne hup
  set V' : Subgroup (PSL2 (GaloisField p 2)) := (V.subgroupOf L).map e'.toMonoidHom with hV'
  have hV'mem : ∀ w : L, e' w ∈ V' ↔ (w : G) ∈ V := fun w => by
    rw [hV', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  have hcop' : ¬ p ∣ Nat.card V' := by
    have h1 : Nat.card V' = Nat.card (V.subgroupOf L) :=
      Subgroup.card_map_of_injective e'.injective
    have h2 : Nat.card (V.subgroupOf L) = Nat.card V :=
      Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv
    rw [h1, h2]
    exact hVp
  have hN' : psl2Root a ∈ normalizer (V' : Set (PSL2 (GaloisField p 2))) := by
    have hu' := Subgroup.mem_normalizer_iff.mp hN
    have hroot : psl2Root a = e' ⟨u, huL⟩ := ha.symm
    rw [hroot, Subgroup.mem_normalizer_iff]
    intro w
    obtain ⟨w₀, rfl⟩ := e'.surjective w
    rw [← map_inv, ← map_mul, ← map_mul, hV'mem, hV'mem]
    simpa using hu' (w₀ : G)
  have hbot := gen49l2_root_coprime hp5 ha0 hcop' hN'
  rw [eq_bot_iff]
  intro w hw
  have hwL : w ∈ L := hVL hw
  have hw' : e' ⟨w, hwL⟩ ∈ V' := (hV'mem _).2 hw
  rw [hbot, Subgroup.mem_bot] at hw'
  have h1 := e'.injective (hw'.trans (map_one e').symm)
  exact congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankThreeTheoremC
