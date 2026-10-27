module

public import CFSG.ClassicalInvolution.Asc77.AscT7K2
public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T7K

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

omit [Finite G] in
theorem le_gamma2 {B A H : Subgroup G} (hAB : A ≤ B) (hA : IsElemAbelian2 A 2) :
    H ⊓ Subgroup.centralizer (A : Set G) ≤ gamma2 B H :=
  le_iSup₂ (f := fun (A : Subgroup G) (_ : A ∈ {A : Subgroup G | A ≤ B ∧ IsElemAbelian2 A 2}) =>
    H ⊓ Subgroup.centralizer (A : Set G)) A ⟨hAB, hA⟩

omit [Finite G] in
theorem generators_mem_B (z u e : G) :
    z ∈ Subgroup.closure ({u * e, u, z} : Set G) ∧ u ∈ Subgroup.closure ({u * e, u, z} : Set G) ∧
      e ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
  have hz : z ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.subset_closure (by simp)
  have hu : u ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.subset_closure (by simp)
  have hue : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨hz, hu, ?_⟩
  have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hue
  simpa using h


theorem oddCore_le_gamma2 (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({z} : Set G)) := by
  have hB := B_isElemAbelian hs hd
  have hB8 := B_natCard hs hd
  have hBC : Subgroup.closure ({u * e, u, z} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_gen hs hd x hx z (by simp))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two (Subgroup.closure ({u * e, u, z} : Set G))
    (oddCoreOf (Subgroup.centralizer ({z} : Set G))) hB (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)).trans
    (le_gamma2 hE.1 hE2)

theorem le_gamma2_of_sylow (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hzL : IsUniqueInvolution L z) {R : Subgroup G}
    (hR : IsSylow2In R L) (hRN : R ≤ Subgroup.normalizer (W : Set G)) :
    L ≤ gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({z} : Set G)) := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hcl : IsClassicalMember p f L z := isClassicalMember_of_twin hΩ hLΩ hzL
  have he2 : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one hd.he2 hd.he1
  have hetq : e ∈ trivialOnQuot L :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ he2 hLΩ).mpr
      ⟨R, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hRN hr))⟩
  obtain ⟨hzB, huB, heB⟩ := generators_mem_B z u e
  have hze : z ≠ e := fun h => e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left hs.hz.mem)
  have hA : IsElemAbelian2 (Subgroup.closure ({z, e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hs.hz.sq hd.he2 hs.hz.ne_one hd.he1 hze
      (comm_e_of_mem_W hd hd.hzW)
  have hAB : Subgroup.closure ({z, e} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hzB
    · exact heB
  intro ℓ hℓ
  obtain ⟨i, hi, n, hn, rfl⟩ := exactCore_cover hcl he2 hetq ℓ hℓ
  refine Subgroup.mul_mem _ ?_ ?_
  · have hiL : i ∈ L := exactCore_le_left e L hi
    have hiC : i ∈ Subgroup.centralizer ({e} : Set G) := exactCore_le_centralizer e L hi
    have hzi : z * i = i * z := hzL.commute_of_mem hiL
    have hiz : i ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzi.symm
    have hie : e * i = i * e := (Subgroup.mem_centralizer_singleton_iff.mp hiC).symm
    exact le_gamma2 hAB hA ⟨hiz, T7B.mem_centralizer_closure_pair hzi hie⟩
  · exact oddCore_le_gamma2 hs hd
      (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
        (T7A.isSubnormal_centralizer hΩ hLΩ hzL) hn)


theorem centralizer_z_le_gamma2 (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) :
    Subgroup.centralizer ({z} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({z} : Set G)) := by
  intro c hc
  obtain ⟨q, hq, c₀, hc₀, hcomm, rfl⟩ :=
    centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', hR, hR', -, hRN, hR'N⟩ := exists_sylow_D hs hd
  have hK := le_gamma2_of_sylow hs hd hs.stand.mem hs.hz hR hRN
  have hK' := le_gamma2_of_sylow hs hd hs.hK'.1 hzK' hR' hR'N
  refine Subgroup.mul_mem _ ((sup_le hK hK') hq) ?_
  obtain ⟨hzB, huB, -⟩ := generators_mem_B z u e
  have hA : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.hu2 hs.hz.sq hd.hu1 hs.hz.ne_one hd.huz (comm_uz hs hd)
  have hAB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact hzB
  have hcz : z * c₀ = c₀ * z := (Subgroup.mem_centralizer_singleton_iff.mp hc₀).symm
  exact le_gamma2 hAB hA ⟨hc₀, T7B.mem_centralizer_closure_pair hcomm.symm hcz⟩

end T7K

end CFSG.ClassicalInvolution.Asc77
