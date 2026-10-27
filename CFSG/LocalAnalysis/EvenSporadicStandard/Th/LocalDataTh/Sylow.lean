module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.DataLemmas
public import Certificates.Certificate24200

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped Matrix

section Facts

theorem ptFacts : PtFacts := of_decide_eq_true Certificates.certificate24200

theorem Pt_card : Pt.card = 64 := ptFacts.1

theorem Pc_wf : ∀ a ∈ Pc, ∀ x ∈ a, x < 256 := fun a ha => (ptFacts.2.1 a ha).2

theorem one_mem_Pt : (1 : Mat8) ∈ Pt :=
  mem_Pt_iff.2 ⟨idCols 8, ptFacts.2.2.1, matOfCols_idCols⟩

theorem mul_mem_Pt {T T' : Mat8} (hT : T ∈ Pt) (hT' : T' ∈ Pt) : T * T' ∈ Pt := by
  obtain ⟨a, ha, rfl⟩ := mem_Pt_iff.1 hT
  obtain ⟨b, hb, rfl⟩ := mem_Pt_iff.1 hT'
  exact mem_Pt_iff.2 ⟨mulCols 8 a b, ptFacts.2.2.2.1 a ha b hb, matOfCols_mulCols 8 a b⟩

theorem exists_inv_Pt {T : Mat8} (hT : T ∈ Pt) : ∃ T' ∈ Pt, T * T' = 1 := by
  obtain ⟨a, ha, rfl⟩ := mem_Pt_iff.1 hT
  obtain ⟨b, hb, hab⟩ := ptFacts.2.2.2.2.1 a ha
  refine ⟨matOfCols 8 b, mem_Pt_iff.2 ⟨b, hb, rfl⟩, ?_⟩
  rw [← matOfCols_mulCols, hab, matOfCols_idCols]

end Facts

@[expose] noncomputable def S : Subgroup J where
  carrier := {m | m ∈ M ∧ rho m ∈ Pt}
  one_mem' := ⟨M.one_mem, by rw [rho_one]; exact one_mem_Pt⟩
  mul_mem' := fun {a b} ha hb => ⟨M.mul_mem ha.1 hb.1, by
    rw [rho_mul ha.1 hb.1]; exact mul_mem_Pt ha.2 hb.2⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨T', hT', hT⟩ := exists_inv_Pt ha.2
    have h1 : rho a * rho a⁻¹ = 1 := by
      rw [← rho_mul ha.1 (M.inv_mem ha.1), mul_inv_cancel, rho_one]
    have h2 : rho a⁻¹ * rho a = 1 := by
      rw [← rho_mul (M.inv_mem ha.1) ha.1, inv_mul_cancel, rho_one]
    refine ⟨M.inv_mem ha.1, ?_⟩
    have : rho a⁻¹ = T' := by
      calc rho a⁻¹ = rho a⁻¹ * (rho a * T') := by rw [hT, mul_one]
        _ = (rho a⁻¹ * rho a) * T' := by rw [mul_assoc]
        _ = T' := by rw [h2, one_mul]
    rw [this]
    exact hT'

theorem S_le_M : S ≤ M := fun _ h => h.1

theorem Q_le_S : Q ≤ S := fun q hq =>
  ⟨Q_le_M hq, by rw [(rho_eq_one_iff (Q_le_M hq)).2 hq]; exact one_mem_Pt⟩

theorem z_mem_S : z ∈ S := Q_le_S z_mem_Q

theorem nf_mem_S (s : ZMod 2) (v : Vec) : nf s v ∈ S := Q_le_S (nf_mem_Q s v)

theorem mem_Pt_iff_exists_S {T : Mat8} : T ∈ Pt ↔ ∃ s ∈ S, rho s = T := by
  constructor
  · intro hT
    obtain ⟨str, hstr, rfl⟩ := exists_word_of_mem_Pt hT
    refine ⟨wordProd (wordOfString str), ⟨wordProd_mem_M _, ?_⟩, ?_⟩
    · rw [rho_wordProd]
      exact wordMat_mem_Pt hstr
    · exact rho_wordProd _
  · rintro ⟨s, hs, rfl⟩
    exact hs.2

theorem center_le_S : ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x ∈ Subgroup.zpowers z := by
  intro x hx hc
  rw [← centralizer_Q_inf_M]
  refine ⟨Subgroup.mem_centralizer_iff.2 fun q hq => ?_, hx.1⟩
  exact (hc q (Q_le_S hq)).symm

@[expose] noncomputable def rhoHom : ↥M →* Mat8 where
  toFun m := rho m.1
  map_one' := rho_one
  map_mul' a b := rho_mul a.2 b.2

@[expose] noncomputable def rhoU : ↥M →* Mat8ˣ := rhoHom.toHomUnits

@[expose] noncomputable def rhoS : ↥S →* Mat8ˣ := rhoU.comp (Subgroup.inclusion S_le_M)

theorem coe_rhoS (s : ↥S) : (rhoS s : Mat8) = rho s.1 := rfl

theorem ker_rhoS : rhoS.ker = Q.subgroupOf S := by
  ext ⟨s, hs⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show rhoS ⟨s, hs⟩ = 1 ↔ s ∈ Q
  rw [Units.ext_iff, coe_rhoS, Units.val_one]
  exact rho_eq_one_iff hs.1

theorem card_ker_rhoS : Nat.card rhoS.ker = 512 := by
  rw [ker_rhoS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q_le_S).toEquiv]
  exact card_Q

theorem card_range_rhoS : Nat.card rhoS.range = 64 := by
  have h : Nat.card rhoS.range = Nat.card (↑Pt : Set Mat8) := by
    refine Nat.card_eq_of_bijective (fun u => ⟨(u.1 : Mat8), ?_⟩) ⟨?_, ?_⟩
    · obtain ⟨⟨s, hs⟩, hsu⟩ := u.2
      rw [← hsu, coe_rhoS]
      exact hs.2
    · intro u u' huu
      exact Subtype.ext (Units.ext (congrArg Subtype.val huu))
    · rintro ⟨T, hT⟩
      obtain ⟨s, hs, hsT⟩ := mem_Pt_iff_exists_S.1 hT
      refine ⟨⟨rhoS ⟨s, hs⟩, ⟨s, hs⟩, rfl⟩, ?_⟩
      exact Subtype.ext (by simpa [coe_rhoS] using hsT)
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, Pt_card]

theorem card_S : Nat.card S = 2 ^ 15 := by
  have h := rhoS.ker.card_mul_index
  rw [Subgroup.index_ker, card_ker_rhoS, card_range_rhoS] at h
  rw [← h]
  norm_num

theorem pgroup_S : IsPGroup 2 S := IsPGroup.of_card card_S

theorem not_dvd_index_S (hJ : Nat.card J = 90745943887872000) : ¬ 2 ∣ S.index := by
  have h := S.card_mul_index
  rw [card_S, hJ] at h
  have h' : S.index = 2769346432125 := by omega
  rw [h']
  omega

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
