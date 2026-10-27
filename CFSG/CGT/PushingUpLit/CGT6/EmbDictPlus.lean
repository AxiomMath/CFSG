module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbShort

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section Plus

variable {G : Type} [Group G] [Finite G] {V A : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
  (D : DictHyp V A)

include D hV in
theorem isCharacteristicP_phi (hA : InClassX ↥A) :
    IsCharacteristicP 2 ↥(yuHolOf hV (autOn A V)) := by
  intro g hg
  rw [pCore_phi hV A D.hK]
  obtain ⟨a, ha⟩ := rhoA_surjective V A (projPhi hV A g)
  refine Subgroup.mem_comap.mpr ⟨a, ?_, ha⟩
  apply centralizer_shortU_le_pCore hA
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm := Subgroup.mem_centralizer_iff.mp hg _
    (incPhi_mem_pCore hV D.toDict0 (uComm hV D ⟨u, hu⟩))
  obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV g (uComm hV D ⟨u, hu⟩)
  have h2 : incPhi hV A u' = incPhi hV A (uComm hV D ⟨u, hu⟩) := by
    rw [← hu'2, ← hcomm]
    group
  have h3 : u' = uComm hV D ⟨u, hu⟩ :=
    @yuInc_injective ↥V (commGroupOfElemAbelian hV) (autOn A V) _ _ h2
  have h4 : (a : G) * ((u : ↥A) : G) * (a : G)⁻¹ = ((u : ↥A) : G) := by
    have h5 := right_apply_coe hV g a ha (uComm hV D ⟨u, hu⟩).1
    have h6 : (((g : HolOf hV).right : MulAut ↥V) ((uComm hV D ⟨u, hu⟩).1 : ↥V) : ↥V) =
        ((uComm hV D ⟨u, hu⟩).1 : ↥V) := by
      rw [← hu'1, h3]
    exact h5.symm.trans (congrArg Subtype.val h6)
  apply Subtype.ext
  show ((u : ↥A) : G) * (a : G) = (a : G) * ((u : ↥A) : G)
  calc ((u : ↥A) : G) * (a : G) = ((a : G) * ((u : ↥A) : G) * (a : G)⁻¹) * a := by rw [h4]
    _ = (a : G) * ((u : ↥A) : G) := by group

include D hV in
theorem oResidualTwo_phi (hres : oResidualTwo ↥A = ⊤) :
    oResidualTwo ↥(yuHolOf hV (autOn A V)) = ⊤ := by
  rw [oResidualTwo_eq_top_iff]
  intro N hN hpow
  have hσ : ∀ a : ↥A, sigPhi hV A a ∈ N := by
    have hNA : N.comap (sigPhi hV A) = ⊤ := by
      refine (oResidualTwo_eq_top_iff).1 hres _ (hN.comap _) (fun a => ?_)
      obtain ⟨k, hk⟩ := hpow (sigPhi hV A a)
      exact ⟨k, by simpa [Subgroup.mem_comap, map_pow] using hk⟩
    intro a
    have : a ∈ N.comap (sigPhi hV A) := by rw [hNA]; trivial
    exact this
  have hU' : ∀ w : ↥(commOn hV A), incPhi hV A w ∈ N := by
    intro w
    refine incPhi_mem_of_comm hV D.toDict0 N (fun m hm a => ?_) w
    rw [incPhi_mkV_comm hV hm a, commutatorElement_def]
    exact N.mul_mem (hN.conj_mem _ (hσ a) _) (N.inv_mem (hσ a))
  rw [eq_top_iff]
  intro x _
  have hx := @yu_eq_inc_mul_sec ↥V (commGroupOfElemAbelian hV) (autOn A V) x
  obtain ⟨a, ha⟩ := rhoA_surjective V A ⟨(x : HolOf hV).right, x.2.2⟩
  have hsec : @yuSec ↥V (commGroupOfElemAbelian hV) (autOn A V) ⟨(x : HolOf hV).right, x.2.2⟩ =
      sigPhi hV A a := by
    rw [← ha]
    rfl
  rw [hx, hsec]
  exact N.mul_mem (hU' _) (hσ a)

include D hV in
theorem shortU_phi_le_center :
    shortU ↥(yuHolOf hV (autOn A V)) ≤
      (Subgroup.center (pCore 2 ↥(yuHolOf hV (autOn A V)))).map
        (pCore 2 ↥(yuHolOf hV (autOn A V))).subtype := by
  rw [shortU_le_center_iff]
  intro u hu
  have hu' := hu
  rw [shortU_phi_eq_ker hV D, ker_projPhi hV A] at hu'
  obtain ⟨w, rfl⟩ := hu'
  refine ⟨incPhi_mem_pCore hV D.toDict0 w, fun r hr => ?_⟩
  rw [pCore_phi hV A D.hK] at hr
  obtain ⟨q, hq, hqr⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hr)
  obtain ⟨u', hu'1, hu'2⟩ := conj_incPhi_exists hV r w
  have hqO : ((q : ↥A) : G) ∈ oTwoIn A := ⟨q, hq, rfl⟩
  have hZ := D.hZ _ (mem_U_of_mem_commOn hV D w.2) _ hqO
  have h3 : u' = w := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [hu'1, right_apply_coe hV r q hqr w.1]
    calc (q : G) * ((w : ↥V) : G) * (q : G)⁻¹ = ((w : ↥V) : G) * (q : G) * (q : G)⁻¹ := by
          rw [← hZ]
      _ = ((w : ↥V) : G) := by group
  rw [h3] at hu'2
  rw [mul_inv_eq_iff_eq_mul] at hu'2
  exact hu'2.symm

end Plus

theorem embDictPlus_holds : EmbDictPlus := by
  intro G _ _ V A _ hV hA _ hU
  have hK : KTwo V A := kTwo_of_le_oTwoIn (inf_centralizer_le_oTwoIn hA hU)
  have hZ : ∀ u ∈ ⁅oTwoIn A, A⁆, ∀ q ∈ oTwoIn A, u * q = q * u := fun u hu q hq =>
    blockU_comm_of_short hA.1 u hu q hq
  have D : DictHyp V A :=
    ⟨⟨hK, SubTwo.noTwoQuotient_of_oResidualTwo hA.1.residual_eq⟩, hU, hZ⟩
  let S := shortIsoPhi hV D
  refine ⟨⟨?_, oResidualTwo_phi hV D hA.1.residual_eq, S.quotient_type hA.1.quotient_type,
    shortU_phi_le_center hV D, S.nonzero hA.1.nonzero, S.irreducible hA.1.irreducible⟩, ?_⟩
  · exact (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp
      (isCharacteristicP_phi hV D hA)
  · rcases hA.2 with ⟨n, hn, hnat⟩ | ⟨n, hn, hnat⟩
    · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
      exact Or.inl ⟨n, hn, isNaturalAltModule_iff.mpr ⟨_, S.symm.altModule hφ⟩⟩
    · exact Or.inr ⟨n, hn, S.symm.slModule hnat⟩

end CFSG.CGT.PushingUpLit.CGT6
