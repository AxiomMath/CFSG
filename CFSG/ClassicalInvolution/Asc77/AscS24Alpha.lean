module

public import CFSG.ClassicalInvolution.Asc77.AscS24Toral
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian)

set_option linter.unusedSectionVars false


section Gamma

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem oddCore_le_gamma2_of {z : G} {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hBC : B ≤ Subgroup.centralizer ({z} : Set G)) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 B (Subgroup.centralizer ({z} : Set G)) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B (oddCoreOf (Subgroup.centralizer ({z} : Set G))) hB (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)).trans
    (T7K.le_gamma2 hE.1 hE2)

theorem le_gamma2_of_trivial (hΩ : HypOmegaMod p f Ω) {z e : G} {B : Subgroup G}
    (hzB : z ∈ B) (heB : e ∈ B) (he2 : e * e = 1) (he1 : e ≠ 1) (hze : z ≠ e)
    (hcomm : z * e = e * z) (hO : oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 B (Subgroup.centralizer ({z} : Set G))) {L : Subgroup G} (hLΩ : L ∈ Ω)
    (hzL : IsUniqueInvolution L z) (hetq : e ∈ trivialOnQuot L) :
    L ≤ gamma2 B (Subgroup.centralizer ({z} : Set G)) := by
  have hcl : IsClassicalMember p f L z := isClassicalMember_of_twin hΩ hLΩ hzL
  have he2' : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one he2 he1
  have hA : IsElemAbelian2 (Subgroup.closure ({z, e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hzL.sq he2 hzL.ne_one he1 hze hcomm
  have hAB : Subgroup.closure ({z, e} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzB
    · exact heB
  intro ℓ hℓ
  obtain ⟨i, hi, n, hn, rfl⟩ := exactCore_cover hcl he2' hetq ℓ hℓ
  refine Subgroup.mul_mem _ ?_ ?_
  · have hiL : i ∈ L := exactCore_le_left e L hi
    have hiC : i ∈ Subgroup.centralizer ({e} : Set G) := exactCore_le_centralizer e L hi
    have hzi : z * i = i * z := hzL.commute_of_mem hiL
    have hiz : i ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzi.symm
    have hie : e * i = i * e := (Subgroup.mem_centralizer_singleton_iff.mp hiC).symm
    exact T7K.le_gamma2 hAB hA ⟨hiz, T7B.mem_centralizer_closure_pair hzi hie⟩
  · exact hO (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
      (T7A.isSubnormal_centralizer hΩ hLΩ hzL) hn)

end Gamma


namespace Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem e0_not_central [IsSimpleGroup G] : ¬ ({C.e0} : Set G) ⊆ Subgroup.center G := by
  intro hsub
  have hst := C.hs.stand
  obtain ⟨z₀, hz₀⟩ := hst.hyp.classical K hst.mem
  obtain ⟨x, -, y, -, hxy⟩ := ih8_exists_noncomm hz₀
  have hcen : C.e0 ∈ Subgroup.center G := hsub (Set.mem_singleton _)
  exact C.e0_ne_one (T7B.eq_one_of_central ⟨x, y, hxy⟩
    (fun g' => Subgroup.mem_center_iff.mp hcen g'))

theorem hyp51At_e0 [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    Hyp51At C.B C.e0 := by
  have hst := C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  obtain ⟨t, ht, hLt⟩ : ∃ t : CFSG.Assembly.LowTwoRank.StatedLieTag, (t = .PSL ∨ t = .PSU) ∧
      LayerLieType p f Ω C.e0 t 3 := by
    by_cases hπ : piSign p f = true
    · simp only [hπ, ↓reduceIte] at hL
      exact ⟨_, Or.inl rfl, hL⟩
    · simp only [hπ] at hL
      exact ⟨_, Or.inr rfl, hL⟩
  obtain ⟨D, hD1, i, hDt, hDr⟩ := exists_local_of_layerLieType hLt
  refine FrameVertex.hyp51At_of_system_lin hp hq hΩ.conjInvariant hΩ.classical (hst.below f hq)
    (C.e0_isPGroup hZ) C.e0_not_central (C.B_isElemAbelian hZ) (C.B_natCard hZ) C.e0_mem_B
    C.e0_ne_one C.z_mem_B C.hs.hz.ne_one C.e0_ne_z.symm (C.K_mem_tq_e0 hZ) C.K_classical
    ⟨D, fun j _ => ?_⟩
  obtain rfl : i = j := eq_of_card_one hD1 i j
  have htag : D.tag i = .PSL ∨ D.tag i = .PSU := hDt ▸ ht
  exact ⟨htag, C.toral hZ D hD1 i htag hDr⟩

theorem hyp51_B [IsSimpleGroup G] (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) : Hyp51 C.B := by
  refine hyp51_of_orbitReps (C.B_isElemAbelian hZ) (C.B_natCard hZ) (R := {z, C.e0}) ?_
    (C.orbit_cover hZ)
  rintro x (rfl | rfl)
  · exact C.hyp51At_z hZ
  · exact C.hyp51At_e0 hZ hL

theorem centralizer_z_le_gamma2 (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    Subgroup.centralizer ({z} : Set G) ≤ gamma2 C.B (Subgroup.centralizer ({z} : Set G)) := by
  have hst := C.hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hB := C.B_isElemAbelian hZ
  have hBC : C.B ≤ Subgroup.centralizer ({z} : Set G) := fun _ hb =>
    Lemma52Proof.le_centralizer_of_mem hB C.z_mem_B hb
  have hO := oddCore_le_gamma2_of hB (C.B_natCard hZ) hBC
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'
  have hK := le_gamma2_of_trivial hΩ C.z_mem_B C.e0_mem_B (C.e0_sq hZ) C.e0_ne_one
    C.e0_ne_z.symm C.comm_ze hO hst.mem C.hs.hz (C.K_mem_tq_e0 hZ).2
  have hcomm' : z * (C.e0 * u) = (C.e0 * u) * z :=
    C.comm_W C.z_mem_W (W.mul_mem C.e0_mem C.u_mem_W)
  have hK' := le_gamma2_of_trivial hΩ C.z_mem_B C.e0u_mem_B (C.e0u_sq hZ) C.e0u_ne_one
    C.e0u_ne_z.symm hcomm' hO C.hs.hK'.1 hzK' (C.K'_mem_tq_e0u hZ).2
  intro c hc
  obtain ⟨q, hq, c₀, hc₀, hcomm, rfl⟩ :=
    T7K.centralizer_eq_sup_mul C.hs C.hd.hu.1 C.u_ne_one C.u_ne_z C.u_sq hc
  refine Subgroup.mul_mem _ ((sup_le hK hK') hq) ?_
  have hA : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair C.u_sq C.z_sq C.u_ne_one C.hs.hz.ne_one C.u_ne_z C.comm_uz
  have hAB : Subgroup.closure ({u, z} : Set G) ≤ C.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact C.u_mem_B
    · exact C.z_mem_B
  have hcz : z * c₀ = c₀ * z := (Subgroup.mem_centralizer_singleton_iff.mp hc₀).symm
  exact T7K.le_gamma2 hAB hA ⟨hc₀, T7B.mem_centralizer_closure_pair hcomm.symm hcz⟩

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
