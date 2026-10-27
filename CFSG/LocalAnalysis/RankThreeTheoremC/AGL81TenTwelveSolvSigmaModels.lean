module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups
public import Certificates.Certificate5169
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCAlt9
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCU42
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCSp62
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCDispatch

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open Subgroup
open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6 CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

open CFSG.GH74.Uniqueness.SU.SU13.TA.L9 Equiv in
theorem solvSigmaSylowFacts_alt9 : SolvSigmaSylowFacts (alternatingGroup (Fin 9)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : ea * eb * ec ∈ Ebar := mul_mem (mul_mem ea_mem_Ebar eb_mem_Ebar) ec_mem_Ebar
  have hzσ : ew * (ea * eb * ec) = ea * eb * ec * ew := by
    have h := ew_mem_Pst
    rw [Pst, Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have hpow : ∀ i j k : Fin 3, toP i j k ^ 3 = 1 := by
    intro i j k
    have hab : Commute pa pb := congrArg Subtype.val commute_ea_eb.eq
    have hac : Commute pa pc := congrArg Subtype.val commute_ea_ec.eq
    have hbc : Commute pb pc := congrArg Subtype.val commute_eb_ec.eq
    have hp : ∀ (q : Perm (Fin 9)) (n : ℕ), q ^ 3 = 1 → (q ^ n) ^ 3 = 1 := fun q n hq => by
      rw [← pow_mul, mul_comm, pow_mul, hq, one_pow]
    rw [toP, ((hac.pow_pow _ _).mul_left (hbc.pow_pow _ _)).mul_pow, (hab.pow_pow _ _).mul_pow,
      hp _ _ pa_pow_three, hp _ _ pb_pow_three, hp _ _ pc_pow_three, one_mul, one_mul]
  refine solvSigmaSylowFacts_of_data (S₀ := Pst) (A₀ := Ebar) (σ := ew) (z := ea * eb * ec)
    (f := et) (IsPGroup.of_card (n := 4) (by rw [card_Pst]; norm_num))
    TenNineOneThree.not_three_dvd_index_Pst card_Pst Ebar_le_Pst ⟨?_, ?_⟩ card_Ebar ew_mem_Pst
    ?_ hz ?_ hzσ ?_ ?_ ?_
  · exact ⟨⟨fun x y => Subtype.ext (Ebar_comm x x.2 y y.2).eq⟩⟩
  · intro x hx
    obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hpow i j k
  ·
    intro h
    have h1 : (ew : Perm (Fin 9)) * pa = pa * ew := (mem_Ebar_iff.mp h).1
    exact absurd h1 (by decide)
  · intro h
    have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
    revert this
    decide
  · intro b hb hc
    exact Ebar_inf_centralizer_ew_le ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩
  ·
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hy
    exact mem_Ebar_iff_toE.mpr ⟨j, i, -k, Subtype.ext (pt_mul_toP i j k)⟩
  ·
    intro hm
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
    have hc : Commute ((ea * eb * ec) ^ k) ew := (Commute.zpow_left hzσ.symm k)
    rw [hk] at hc
    have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) hc.eq
    revert this
    decide

private theorem genB_cIo : genB cIo = true := by decide

private theorem sg_not_mem_B0 : elt cSg ∉ B0 := by
  intro h
  have hc : elt cSg * elt cW0 = elt cW0 * elt cSg :=
    congrArg Subtype.val (B0_elemAbelian.1.is_comm.comm ⟨_, h⟩ ⟨_, elt_mem_Hgen (by simp [gensB])⟩)
  rw [(rep_elt (genB_isoB TenNineOneThree.genB_cSg)).comm_iff
    (rep_elt (genB_isoB (c := cW0) (by decide)))] at hc
  exact absurd hc (by decide)

private theorem z0_mem_B0 : z0 ∈ B0 := by
  have r0 := rep_elt (genB_isoB (c := cW0) (by decide))
  have r1 := rep_elt (genB_isoB (c := cW1) (by decide))
  have r2 := rep_elt (genB_isoB (c := cW2) (by decide))
  have h : Rep (elt cW0 * (elt cW1 * elt cW2)) cZ := by
    rw [TenNineOneThree.cZ_eq]
    exact r0.mul (r1.mul r2)
  rw [rep_z0.eq h]
  exact mul_mem (elt_mem_Hgen (by simp [gensB]))
    (mul_mem (elt_mem_Hgen (by simp [gensB])) (elt_mem_Hgen (by simp [gensB])))

private theorem mem_zpowers_z0_of_comm :
    ∀ b ∈ B0, elt cSg * b = b * elt cSg → b ∈ zpowers z0 := by
  intro b hb hc
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_B hb
  have hcomm : commB t cSg = true :=
    beq_iff_eq.2 ((hrep.comm_iff (rep_elt (genB_isoB TenNineOneThree.genB_cSg))).1 hc.symm)
  have hZt : inZ t = true := by
    have h := forall_of_allCheck Certificates.certificate5169 t ht
    simpa [hcomm] using h
  exact mem_zpowers_z0 hrep hZt

private theorem not_mem_zpowers_z0 {y : H6} {t : List ℕ}
    (hy : Rep y t) (ht : inZ t = false) : y ∉ zpowers z0 := by
  intro hm
  rcases zpowers_z0_cases hm with h | h | h
  · have h' := (hy.eq_iff Rep.one).1 h
    simp [inZ, h'] at ht
  · have h' := (hy.eq_iff rep_z0).1 h
    simp [inZ, h'] at ht
  · have h' := (hy.eq_iff rep_z0_sq).1 h
    simp [inZ, h'] at ht

theorem solvSigmaSylowFacts_H6 :
    SolvSigmaSylowFacts CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 := by
  have hσT : elt cSg ∈ T0 := elt_mem_Hgen (by simp [gensT])
  have hσE : elt cSg ∈ E0 := elt_mem_Hgen (by simp [gensE])
  refine solvSigmaSylowFacts_of_data (S₀ := T0) (A₀ := B0) (σ := elt cSg) (z := z0)
    (f := elt cIo) isPGroup_T0 not_dvd_index_T0 (by rw [card_T0]; norm_num) B0_le_T0
    B0_elemAbelian (by rw [card_B0]; norm_num) hσT sg_not_mem_B0 z0_mem_B0 z0_ne_one
    (z0_comm_E0 _ hσE).symm mem_zpowers_z0_of_comm (elt_mem_normalizer_B0 (by simp [gensN])) ?_
  exact not_mem_zpowers_z0 (rep_conj_elt genB_cIo rep_z0) (by decide)

private theorem elt_cA_mem_normalizer_B0 :
    elt cA ∈ normalizer (B0 : Set H6) := by
  have rA := TenNineOneThree.genB_cA'
  have r0 := rep_elt (genB_isoB (c := cW0) (by decide))
  have r1 := rep_elt (genB_isoB (c := cW1) (by decide))
  have r2 := rep_elt (genB_isoB (c := cW2) (by decide))
  have hW : ∀ c ∈ gensB, elt c ∈ B0 := fun c hc => elt_mem_Hgen hc
  have hcl : B0 ≤ B0.comap (MulAut.conj (elt cA)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [gensB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · have h1 : conjC cA cW0 = mulC cW2 cW2 := by decide
      have h := rep_conj_elt rA r0
      rw [h1] at h
      rw [h.eq (r2.mul r2)]
      exact mul_mem (hW _ (by simp [gensB])) (hW _ (by simp [gensB]))
    · have h1 : conjC cA cW1 = cW1 := by decide
      have h := rep_conj_elt rA r1
      rw [h1] at h
      rw [h.eq r1]
      exact hW _ (by simp [gensB])
    · have h1 : conjC cA cW2 = mulC cW0 cW0 := by decide
      have h := rep_conj_elt rA r2
      rw [h1] at h
      rw [h.eq (r0.mul r0)]
      exact mul_mem (hW _ (by simp [gensB])) (hW _ (by simp [gensB]))
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have := hcl hy
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem solvSigmaSylowFacts_V0 :
    SolvSigmaSylowFacts ↥CFSG.AGLEmbedding.KFactProofs.Sp62Local.V0 := by
  have hσT : elt cSg ∈ T0 := elt_mem_Hgen (by simp [gensT])
  have hσE : elt cSg ∈ E0 := elt_mem_Hgen (by simp [gensE])
  have hidx : ¬ 3 ∣ (T0.subgroupOf V0).index := by
    have h := (T0.subgroupOf V0).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_V0).toEquiv, card_T0, card_V0] at h
    have : (T0.subgroupOf V0).index = 320 := by omega
    rw [this]
    norm_num
  refine solvSigmaSylowFacts_of_data_of_le (H := V0) (S₀ := T0) (A₀ := B0) (σ := elt cSg)
    (z := z0) (f := elt cA) T0_le_V0 (by rw [card_T0]; norm_num) hidx B0_le_T0 B0_elemAbelian
    (by rw [card_B0]; norm_num) hσT sg_not_mem_B0 z0_mem_B0 z0_ne_one (z0_comm_E0 _ hσE).symm
    mem_zpowers_z0_of_comm (elt_mem_Hgen cA_mem_gensV) elt_cA_mem_normalizer_B0 ?_
  refine not_mem_zpowers_z0 (rep_conj_elt TenNineOneThree.genB_cA' rep_z0) ?_
  rw [TenNineOneThree.conjC_cA_cZ]
  exact TenNineOneThree.not_inZ_cAz

theorem solvSigmaSylowFacts_of_target
    {K : Type} [Group K] [Finite K]
    (h : IsLieOver K (.twistedA 3) 2 1 ∨ IsLieOver K (.B 3) 2 1 ∨
      Nonempty (K ≃* alternatingGroup (Fin 9))) : SolvSigmaSylowFacts K := by
  rcases h with ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩ | he
  · obtain ⟨e'⟩ := nonempty_V0_of_isSpFourIndex d ⟨q, Or.inr ⟨rfl, hqp, hqe, hd⟩⟩ e
    exact SolvSigmaSylowFacts.of_mulEquiv e' solvSigmaSylowFacts_V0
  · obtain ⟨e'⟩ := nonempty_H6_of_B3 d hd e
    exact SolvSigmaSylowFacts.of_mulEquiv e' solvSigmaSylowFacts_H6
  · obtain ⟨e⟩ := he
    exact SolvSigmaSylowFacts.of_mulEquiv e solvSigmaSylowFacts_alt9

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
