module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23H02
public import CFSG.ClassicalInvolution.Q3.Q3T7P24HHyp51
public import CFSG.ClassicalInvolution.Q3.Q3T7P24V01
public import CFSG.ClassicalInvolution.Q3.Q3T7S23A01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem oddCore_le_gamma2
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e
    g) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({z} : Set G)) := by
  have hB := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  have hB8 := Q3T8.Asc77.T7K.B_natCard hs hd
  have hBC : Subgroup.closure ({u * e, u, z} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Q3T8.Asc77.T7K.comm_gen hs hd x hx z (by
        simp))
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

theorem le_gamma2_of_sylow
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e
    g)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hzL : IsUniqueInvolution L z) {R : Subgroup G}
    (hR : IsSylow2In R L) (hRN : R ≤ Subgroup.normalizer (W : Set G)) :
    L ≤ gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({z} : Set G)) := by
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hcl : Q3T8.Generic.IsClassicalMember L z := Q3T8.Asc77.isClassicalMember_of_twin hΩ hLΩ hzL
  have he2 : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one hd.he2 hd.he1
  have hetq : e ∈ trivialOnQuot L :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ he2 hLΩ).mpr
      ⟨R, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hRN hr))⟩
  obtain ⟨hzB, huB, heB⟩ := generators_mem_B z u e
  have hze : z ≠ e := fun h => Q3T8.Asc77.T7K.e_not_mem_sup hs hd (h ▸ Subgroup.mem_sup_left
      hs.hz.mem)
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
  obtain ⟨i, hi, n, hn, rfl⟩ := Q3T8.Asc77.ExactLayer.exactCore_cover hcl he2 hetq ℓ hℓ
  refine Subgroup.mul_mem _ ?_ ?_
  · have hiL : i ∈ L := Q3T8.Asc77.ExactLayer.exactCore_le_left e L hi
    have hiC : i ∈ Subgroup.centralizer ({e} : Set G) :=
        Q3T8.Asc77.ExactLayer.exactCore_le_centralizer e L hi
    have hzi : z * i = i * z := hzL.commute_of_mem hiL
    have hiz : i ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzi.symm
    have hie : e * i = i * e := (Subgroup.mem_centralizer_singleton_iff.mp hiC).symm
    exact le_gamma2 hAB hA ⟨hiz, T7B.mem_centralizer_closure_pair hzi hie⟩
  · exact Q3T8.Asc77.T7K.oddCore_le_gamma2 hs hd
      (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
        (Q3T8.Asc77.T7A.isSubnormal_centralizer hΩ hLΩ hzL) hn)

theorem centralizer_z_le_gamma2
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) :
    Subgroup.centralizer ({z} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({z} : Set G)) := by
  intro c hc
  obtain ⟨q, hq, c₀, hc₀, hcomm, rfl⟩ :=
    Q3T8.Asc77.T7K.centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', hR, hR', -, hRN, hR'N⟩ := Q3T8.Asc77.T7K.exists_sylow_D hs hd
  have hK := Q3T8.Asc77.T7K.le_gamma2_of_sylow hs hd hs.stand.mem hs.hz hR hRN
  have hK' := Q3T8.Asc77.T7K.le_gamma2_of_sylow hs hd hs.hK'.1 hzK' hR' hR'N
  refine Subgroup.mul_mem _ ((sup_le hK hK') hq) ?_
  obtain ⟨hzB, huB, -⟩ := generators_mem_B z u e
  have hA : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hd.hu2 hs.hz.sq hd.hu1 hs.hz.ne_one hd.huz
        (Q3T8.Asc77.T7K.comm_uz hs hd)
  have hAB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact hzB
  have hcz : z * c₀ = c₀ * z := (Subgroup.mem_centralizer_singleton_iff.mp hc₀).symm
  exact le_gamma2 hAB hA ⟨hc₀, T7B.mem_centralizer_closure_pair hcomm.symm hcz⟩
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
section Model
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twin_lifts
    (hΦ : Q3T7M.HM Φ) {tg : StatedLieTag}
    {k ee : ℕ} (M : Q3T8.Asc77.Ih8Model Φ tg k ee) (hG2 : tg ≠ .G2) (hD4 : tg ≠ .trialityD4)
    (hnpsl : ¬ (tg = .PSL ∧ k = 2)) {A A' : Subgroup X} {z a₀ b₀ : X} (hA : A ∈ Φ)
    (hA' : A' ∈ Φ) (hne : A ≠ A') (hzA : IsUniqueInvolution A z)
    (hzA' : IsUniqueInvolution A' z) (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ A') (ha₀sq : a₀ * a₀ = z)
    (hb₀sq : b₀ * b₀ = z) :
    ∃ (RA RA' : Subgroup (modelUniv tg k 3 ee Fact.out).K)
      (a b x x' : (modelUniv tg k 3 ee Fact.out).K),
      RA ∈ M.cls ∧ RA' ∈ M.cls ∧ RA ≠ RA' ∧ Commutes RA RA' ∧ x ∈ RA ∧ x * x = 1 ∧ x ≠ 1 ∧
        x' ∈ RA' ∧ x' * x' = 1 ∧ x' ≠ 1 ∧
        x * x' ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K ∧ a ∈ RA ∧ a * a = x ∧
        b ∈ RA' ∧ b * b = x' ∧ M.ψ a = a₀ ∧ M.ψ b = b₀ ∧ M.ψ x = z ∧ M.ψ x' = z := by
  classical
  have hee : ee = 1 := M.exp_eq_f hD4
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RA', hRA', rfl⟩ := (M.mem_iff A').mp hA'
  have hpA := M.gen3 hG2 hD4 hRA
  have hRR : RA ≠ RA' := fun h => hne (by rw [h])
  obtain ⟨hcommR, -⟩ := Uniform.ih8_twin_data3 hΦ (M.exactMembers3 hΦ hG2 hD4) M.ker_le_center
    (M.ker_pow_three hD4) hpA (M.map_mem hRA) (M.map_mem hRA') hne hzA hzA'
  obtain ⟨eA⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hRA
  obtain ⟨eA'⟩ := M.cls_equiv_sl2 (by norm_num) hG2 hD4 hRA'
  have hodd' := M.natCard_galoisField_odd (by norm_num)
  have hinjA := M.injOn_fund hnpsl (M.cls_sub hRA)
  have hinjA' := M.injOn_fund hnpsl (M.cls_sub hRA')
  have hxR : sl2Inv eA ∈ RA := sl2Inv_mem eA
  have hx'R : sl2Inv eA' ∈ RA' := sl2Inv_mem eA'
  have hx2 : sl2Inv eA * sl2Inv eA = 1 := sl2Inv_mul_self hodd' eA
  have hx'2 : sl2Inv eA' * sl2Inv eA' = 1 := sl2Inv_mul_self hodd' eA'
  have hx1 : sl2Inv eA ≠ 1 := sl2Inv_ne_one hodd' eA
  have hx'1 : sl2Inv eA' ≠ 1 := sl2Inv_ne_one hodd' eA'
  have hψx : M.ψ (sl2Inv eA) = z := by
    have hmem : M.ψ (sl2Inv eA) ∈ RA.map M.ψ := Subgroup.mem_map_of_mem _ hxR
    have hsq : M.ψ (sl2Inv eA) * M.ψ (sl2Inv eA) = 1 := by rw [← map_mul, hx2, map_one]
    rcases hzA.unique _ hmem hsq with h | h
    · exact absurd (hinjA _ hxR h) hx1
    · exact h
  have hψx' : M.ψ (sl2Inv eA') = z := by
    have hmem : M.ψ (sl2Inv eA') ∈ RA'.map M.ψ := Subgroup.mem_map_of_mem _ hx'R
    have hsq : M.ψ (sl2Inv eA') * M.ψ (sl2Inv eA') = 1 := by rw [← map_mul, hx'2, map_one]
    rcases hzA'.unique _ hmem hsq with h | h
    · exact absurd (hinjA' _ hx'R h) hx'1
    · exact h
  have hxx' : sl2Inv eA * sl2Inv eA' ∈ Subgroup.center (modelUniv tg k 3 ee Fact.out).K := by
    apply M.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, hψx, hψx']
    exact hzA.sq
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp ha₀
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp hb₀
  have hasq : a * a = sl2Inv eA := by
    have : a * a * (sl2Inv eA)⁻¹ = 1 := by
      apply hinjA _ (RA.mul_mem (RA.mul_mem haR haR) (RA.inv_mem hxR))
      rw [map_mul, map_mul, map_inv, hψa, hψx, ha₀sq, mul_inv_cancel]
    exact mul_inv_eq_one.mp this
  have hbsq : b * b = sl2Inv eA' := by
    have : b * b * (sl2Inv eA')⁻¹ = 1 := by
      apply hinjA' _ (RA'.mul_mem (RA'.mul_mem hbR hbR) (RA'.inv_mem hx'R))
      rw [map_mul, map_mul, map_inv, hψb, hψx', hb₀sq, mul_inv_cancel]
    exact mul_inv_eq_one.mp this
  exact ⟨RA, RA', a, b, _, _, hRA, hRA', hRR, hcommR, hxR, hx2, hx1, hx'R, hx'2, hx'1, hxx', haR,
    hasq, hbR, hbsq, hψa, hψb, hψx, hψx'⟩

theorem e4Tag_of_model
    (htcf : Q3T8.Asc77.TwinCentralFact3) (hΦ : Q3T7M.HM Φ) {tg : StatedLieTag} {k ee : ℕ}
    (M : Q3T8.Asc77.Ih8Model Φ tg k ee)
    (hsix : (tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4) ∨ (tg = .PSU ∧ k = 4) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4))
    {A A' : Subgroup X} {z a₀ b₀ w : X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hne : A ≠ A')
    (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z) (ha₀ : a₀ ∈ A)
    (hb₀ : b₀ ∈ A') (ha₀sq : a₀ * a₀ = z) (hb₀sq : b₀ * b₀ = z)
    (hw : w = a₀ * b₀ ∨ w = a₀⁻¹ * b₀) (hF : ∀ L ∈ Φ, ∃ m ∈ L, w * m ≠ m * w) :
    (tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4 ∧ 3 % 4 = 3) ∨
      (tg = .PSU ∧ k = 4 ∧ 3 % 4 = 1) := by
  classical
  have hodd : Odd (3) := by decide
  have hmod : 3 % 4 = 1 ∨ 3 % 4 = 3 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hsix with h | h | h | h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hsix with h | h | h | h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hsix with h | h | h | h | h | h <;> simp at h
  have hee : ee = 1 := M.exp_eq_f hD4
  have hne' : Φ.Nonempty := ⟨A, hA⟩

  have key : ((tg = .PSL ∧ k = 4 ∧ 3 % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ 3 % 4 = 3) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4)) →
      False := by
    intro hS4
    obtain ⟨RA, RA', a, b, x, x', hRA, hRA', hRR, hcommR, hxR, hx2, hx1, hx'R, hx'2, hx'1, hxx',
      haR, hasq, hbR, hbsq, hψa, hψb, hψx, hψx'⟩ :=
      Q3T8.Asc77.T7L.twin_lifts hΦ M hG2 hD4 hnpsl hA hA' hne hzA hzA' ha₀ hb₀ ha₀sq hb₀sq

    have hfund := fun (a' : (modelUniv tg k 3 ee Fact.out).K) (ha' : a' ∈ RA)
        (ha'sq : a' * a' = x) =>
      htcf tg k ee M.admissible (by rw [hee]; exact hS4) RA (M.cls_sub hRA) RA'
        (M.cls_sub hRA') hRR hcommR x hxR hx2 hx1 x' hx'R hx'2 hx'1 hxx' a' ha' ha'sq b hbR hbsq
    have hdone : ∀ a' : (modelUniv tg k 3 ee Fact.out).K, a' ∈ RA → a' * a' = x →
        M.ψ (a' * b) = w → False := by
      intro a' ha' ha'sq hψ
      obtain ⟨R'', hR'', hcR⟩ := hfund a' ha' ha'sq
      have hR''cls : R'' ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR''
      obtain ⟨m, hm, hmne⟩ := hF _ (M.map_mem hR''cls)
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hm
      apply hmne
      rw [← hψ, ← map_mul, ← map_mul, hcR r hr]
    rcases hw with hw | hw
    · exact hdone a haR hasq (by rw [map_mul, hψa, hψb, hw])
    · refine hdone a⁻¹ (RA.inv_mem haR) ?_ (by rw [map_mul, map_inv, hψa, hψb, hw])
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = x := by rw [hasq, hxinv]
  rcases hsix with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    rcases hmod with h | h
    · exact (key (Or.inl ⟨h1, h2, h⟩)).elim
    · exact h
  · refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
    rcases hmod with h | h
    · exact h
    · exact (key (Or.inr (Or.inl ⟨h1, h2, h⟩))).elim
  · exact (key (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
  · exact (key (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))).elim
  · exact (key (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))).elim
end Model
end T7L
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
theorem c23_4X_proved
    : Q3T8.Asc77.C23_4X :=
  Q3T8.Asc77.c23_4X_of_tsf Q3T7S23.twinSquareFact3_rows
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)
open scoped commutatorElement
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem hyp51At_of_twin_inner {K₀ : Subgroup G} (hst : Q3T8.Asc77.AscStand Ω K₀) {K K' : Subgroup
    G} {b d c : G}
    (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hne : K' ≠ K)
    (hbK : IsUniqueInvolution K b) (hbK' : IsUniqueInvolution K' b)
    (hMK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hMK' : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω
        c)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G))
    (hc1 : c ≠ 1) (hbc : b ≠ c) (hd1 : d ≠ 1) (hdb : d ≠ b) (hd2 : d * d = 1)
    (hdsup : d ∈ Q3T8.Asc77.ExactLayer.exactCore c K ⊔ Q3T8.Asc77.ExactLayer.exactCore c K') :
    Hyp51At B c := Q3T7P24.hyp51TwinInnerThree_proved hst hKΩ hK'Ω hne hbK hbK' hMK hMK' hB hbB hdB
        hcB
    hBgen hc1 hbc hd1 hdb hd2 hdsup
omit [IsSimpleGroup G] in

theorem hyp51At_of_twin_vertex_z
    [IsSimpleGroup G] {K₀ : Subgroup G} (hst : Q3T8.Asc77.AscStand Ω
    K₀)
    {K K' : Subgroup G} {z x y e₁ : G} (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hzB : z ∈ B)
    (hxK : x ∈ K) (hyK' : y ∈ K') (hxyB : x * y ∈ B) (hxy1 : x * y ≠ 1) (hxyz : x * y ≠ z)
    (he₁B : e₁ ∈ B) (he₁1 : e₁ ≠ 1) (he₁z : e₁ ≠ z)
    (he₁K : e₁ ∈ trivialOnQuot K) (he₁K' : e₁ ∈ trivialOnQuot K') :
    Hyp51At B z := Q3T7P24.hyp51VertexThree_proved hst hKΩ hK'Ω hzK hzK' hB hzB hxK hyK' hxyB hxy1
        hxyz
    he₁B he₁1 he₁z he₁K he₁B he₁1 he₁z he₁K'
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem sq_eq_of_mul_involution
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) {R R' : Subgroup G}
    (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hc : Commutes R R') {a b : G} (ha : a ∈ R)
    (hb : b ∈ R') (hu2 : (a * b) * (a * b) = 1) (hu1 : a * b ≠ 1) (huz : a * b ≠ z) :
    a * a = z ∧ b * b = z := by
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcab : a * b = b * a := hc a ha b hb
  have hsq : (a * a) * (b * b) = 1 := by
    calc (a * a) * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcab]
      _ = (a * b) * (a * b) := by group
      _ = 1 := hu2
  have haL : a ∈ K := hR.1 ha
  have hbL' : b ∈ K' := hR'.1 hb
  have hcard : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hKΩ hK'Ω hs.hne.symm (hR.2.1.to_le inf_le_left)
      (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
  have hA : ∀ x ∈ R ⊓ R', x * x = 1 := by
    intro x hx
    have hd : orderOf x ∣ Nat.card ↥(R ⊓ R') := Subgroup.orderOf_dvd_natCard _ hx
    have hpos : 0 < Nat.card ↥(R ⊓ R') := Nat.card_pos
    have h2 : orderOf x ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R ⊓ R')
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have haaA : a * a ∈ R ⊓ R' := by
    refine ⟨R.mul_mem ha ha, ?_⟩
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R'.inv_mem (R'.mul_mem hb hb)
  have haa2 : (a * a) * (a * a) = 1 := hA _ haaA
  have haa : a * a = z := by
    rcases hzK.unique (a * a) (K.mul_mem haL haL) haa2 with h | h
    · exfalso
      have hbb : b * b = 1 := by rwa [h, one_mul] at hsq
      have ha1 : a = 1 ∨ a = z := hzK.unique a haL h
      have hb1 : b = 1 ∨ b = z := hzK'.unique b hbL' hbb
      rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
      · exact hu1 (by rw [h1, h2, one_mul])
      · exact huz (by rw [h1, h2, one_mul])
      · exact huz (by rw [h1, h2, mul_one])
      · exact hu1 (by rw [h1, h2]; exact hzK.sq)
    · exact h
  refine ⟨haa, ?_⟩
  have h1 : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [haa] at hsq)
  rw [h1]
  exact inv_eq_of_mul_eq_one_right hzK.sq

theorem exists_decomp
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (R R' : Subgroup G) (a b r : G), IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      R ≤ Subgroup.normalizer (W : Set G) ∧ R' ≤ Subgroup.normalizer (W : Set G) ∧
      a ∈ R ∧ b ∈ R' ∧ a ∈ W ∧ b ∈ W ∧ u = a * b ∧ a * a = z ∧ b * b = z ∧
      r ∈ R ∧ r * u * r⁻¹ = u * z := by
  have hst := hs.stand
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := Q3T8.Asc77.T7D.exists_sylow_frame hs hd.hW hd.hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS (mem_RSet_of_isSylow2In hKΩ hR) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS (mem_RSet_of_isSylow2In hK'Ω hR') hR'S
  have h2 : IsPGroup 2 ↥(R ⊔ R') := (Sylow.isPGroup' S).to_le (sup_le hRS hR'S)
  have hc : Commutes R R' :=
    hΩ.commutes_of_twin_of_isPGroup hKΩ hK'Ω hs.hne.symm hzK hzK' hR.1 hR'.1 h2
  have hQ : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    Q3T8.Asc77.T7A.isSylow2In_sup_of_twin hΩ hKΩ hK'Ω hs.hne hzK hzK' hR hR' hc

  have hS2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ (K ⊔ K')) := (Sylow.isPGroup' S).to_le inf_le_left
  have heq : (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' :=
    hQ.eq_of_le hS2 inf_le_right (le_inf (sup_le hRS hR'S) hQ.1)
  have huRR' : u ∈ R ⊔ R' := by
    rw [← heq]
    exact ⟨hWS hd.huW, hd.hu⟩
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huRR'
  have hu2' : (a * b) * (a * b) = 1 := by rw [hab]; exact hd.hu2
  have hsq := Q3T8.Asc77.T7K.sq_eq_of_mul_involution hs hR hR' hc ha hb hu2' (by rw [hab]; exact
      hd.hu1)
    (by rw [hab]; exact hd.huz)
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW

  obtain ⟨hRW, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hd.hW hRD hKΩ hR
  have haW : a ∈ W := by
    by_contra haW
    obtain ⟨v, hv, hv2⟩ := Thompson.exists_sq_ne_one hcyc (by omega)
    have hvKW : v ∈ K ⊓ W := by rw [← hRW]; exact hv
    have hinv : a * v * a⁻¹ = v⁻¹ :=
      Q3CL.Thompson.conj_eq_inv_of_mem_inf_W hΩ hd.hW hKΩ hRD hR ha haW hvKW
    have hvu : Commute v u := hWab v hv.2 u hd.huW
    have hvb : Commute v b := hc v hv.1 b hb
    have hva : Commute v a := by
      have : a = u * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact hvu.mul_right hvb.inv_right
    have h5 : a * v * a⁻¹ = v := by
      rw [← hva.eq]
      group
    rw [h5] at hinv
    exact hv2 (by
      have : v * v = 1 := by
        calc v * v = v * v⁻¹ := by rw [← hinv]
          _ = 1 := mul_inv_cancel v
      exact this)
  have hbW : b ∈ W := by
    have : b = a⁻¹ * u := by rw [← hab]; group
    rw [this]
    exact W.mul_mem (W.inv_mem haW) hd.huW

  have hctx : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst hd.hW
  obtain ⟨ρ, hρK, hρR⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hd.hW hKΩ hR hRD
  obtain ⟨σ, hσK, hσR⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hd.hW hK'Ω hR' hR'D
  have hnbr : σ.K ∈ omegaNbr Ω ρ.K := by
    rw [hρK, hσK]
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rcases hperp with h | h
    · exact absurd h hs.hne
    · exact h
  have haK : a ∈ ρ.K ⊓ W := ⟨by rw [hρK]; exact hR.1 ha, haW⟩
  have hbK : b ∈ σ.K ⊓ W := ⟨by rw [hσK]; exact hR'.1 hb, hbW⟩
  have h1 : ρ.r * a * ρ.r⁻¹ = a⁻¹ := hctx.conj_inv ρ haK
  have h3 : ρ.r * b = b * ρ.r := hctx.centralizes ρ σ hnbr hbK
  have hainv : a⁻¹ = a * z := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    calc a * (a * z) = (a * a) * z := by group
      _ = z * z := by rw [hsq.1]
      _ = 1 := hzK.sq
  have hzb : z * b = b * z := hzK'.commute_of_mem (hR'.1 hb)
  refine ⟨R, R', a, b, ρ.r, hR, hR', hc, hRD.2, hR'D.2, ha, hb, haW, hbW, hab.symm, hsq.1, hsq.2,
    by rw [← hρR]; exact ρ.hr, ?_⟩
  have hrb : ρ.r * b * ρ.r⁻¹ = b := by
    rw [h3]
    group
  calc ρ.r * u * ρ.r⁻¹ = (ρ.r * a * ρ.r⁻¹) * (ρ.r * b * ρ.r⁻¹) := by rw [← hab]; group
    _ = (a * z) * b := by rw [h1, hrb, hainv]
    _ = a * (z * b) := by group
    _ = a * (b * z) := by rw [hzb]
    _ = u * z := by rw [← hab]; group
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinSection_cases (htcf : Q3T8.Asc77.TwinCentralFact3) {n : ℕ}
    (hBelow : Q3T8.Generic.CITBelowU n) (hlt : Nat.card X < n) (hS : Q3T8.Asc77.GenSection Φ)
    {A A' : Subgroup X} {z a₀ b₀ w : X} (T : TwinSect Φ A A' z a₀ b₀ w) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨
      ∃ (D : Q3T8.Asc77.OmegaLie Φ) (_ : D.card = 1) (i : Fin D.card),
        (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4 ∧ 3 % 4 = 3) ∨
          (D.tag i = .PSU ∧ D.rank i = 4 ∧ 3 % 4 = 1) := by
  classical
  have hΦ : Q3T7M.HM Φ := hS.hyp
  by_cases hconn : DConnected Φ
  · left
    have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N →
        N = A ∨ N = A' := by
      intro N hN
      induction hN with
      | refl => exact Or.inl rfl
      | tail hpre hstep ih =>
        rename_i M N'
        obtain ⟨hN'Φ, hadj⟩ := hstep
        have hMΦ : M ∈ Φ := by
          rcases ih with rfl | rfl
          · exact T.hA
          · exact T.hA'
        rcases ih with rfl | rfl
        · refine Or.inr (T.nbA N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΦ hN'Φ hMΦ h
        · refine Or.inl (T.nbA' N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΦ hN'Φ hMΦ h
    intro L hL
    exact hpath L (hconn _ T.hA L hL)
  · right
    have hNE : ¬ DEdgeless Φ := by
      intro h
      rcases CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΦ T.hA T.hA' T.hzA T.hzA' with h'
          | h'
      · exact T.ne h'
      · exact h _ T.hA' _ T.hA (Or.inl h')
    obtain ⟨d, ε, hd5, hd8, t', n', hortag, D, hcard, i, htag, hrank⟩ :=
      Q3T8.Asc77.thm8SectBelow'_of_citBelow hBelow X hlt Φ hS
        ⟨_, T.hA⟩ hNE hconn
    have hsix : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
        (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4) := by
      rw [htag, hrank]
      rcases hortag with ⟨-, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨hd7, hodd, ht, hn⟩ |
        ⟨hd8', hev, -, ht, hn⟩ | ⟨hd8', hev, -, ht, hn⟩
      · exact Or.inl ⟨ht, hn⟩
      · exact Or.inr (Or.inl ⟨ht, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))))
    let M := Q3T8.Asc77.T7L.toModelOfGen hΦ D hcard hS.gen i
    exact ⟨D, hcard, i, Q3T8.Asc77.T7L.e4Tag_of_model htcf hΦ M hsix T.hA T.hA' T.ne T.hzA T.hzA'
        T.ha₀
      T.hb₀ T.ha₀sq T.hb₀sq T.hw T.hF⟩
end T7L
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}
variable [IsSimpleGroup G]

theorem exists_three_gens
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e
    g) :
    ∃ x₁ x₂ x₃ : G, x₁ ∈ W ∧ x₂ ∈ W ∧ x₃ ∈ W ∧
      W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) := by
  have hst := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hctx : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst hd.hW
  obtain ⟨e', F, he, -, -, -, hab, hcomm, hac, -⟩ :=
    Q3T8.Asc77.T7E.exists_frame4 hs hd.hW hd.hzW hd.hS4
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens hctx
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure hctx he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  exact ⟨x₁, x₂, x₃, (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2,
    (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2,
    (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2, hgen⟩

theorem mem_B_of_involution
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e
    g)
    {w : G} (hw : w ∈ W) (hw2 : w * w = 1) : w ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
  have hst := hs.stand
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, hgen⟩ := Q3T8.Asc77.T7K.exists_three_gens hs hd
  have hB := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  exact mem_of_involution_of_card_eq_eight
    (Q3CL.Thompson.commutes_of_mem_WSet hst.hyp hd.hW) h₁ h₂ h₃ hgen (B_le_W hd)
    (fun s hs' => by simpa only [pow_two] using hB.2 s hs') (Q3T8.Asc77.T7K.B_natCard hs hd) hw hw2

theorem mem_normalizer_B
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g)
    {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    n ∈ Subgroup.normalizer ((Subgroup.closure ({u * e, u, z} : Set G) : Subgroup G) : Set G) := by
  have hB := Q3T8.Asc77.T7K.B_isElemAbelian hs hd
  have hBW := B_le_W hd
  have key : ∀ m ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G),
      m * x * m⁻¹ ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    intro m hm x hx
    refine Q3T8.Asc77.T7K.mem_B_of_involution hs hd ((Subgroup.mem_normalizer_iff.mp hm x).mp (hBW
        hx)) ?_
    have hx2 : x * x = 1 := by simpa only [pow_two] using hB.2 x hx
    calc m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  simpa [mul_assoc] using this
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected
namespace T7L
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7L
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_gen_of_model
    (hgen : Q3T8.Asc77.E4TwinGen3) (hΦ : Q3T7M.HM Φ) {tg : StatedLieTag} {k ee : ℕ} (M :
    Q3T8.Asc77.Ih8Model Φ tg k ee)
    (hE4 : (tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4 ∧ 3 % 4 = 3) ∨
      (tg = .PSU ∧ k = 4 ∧ 3 % 4 = 1))
    {A A' : Subgroup X} {z a₀ b₀ w : X} (T : TwinSect Φ A A' z a₀ b₀ w) :
    (⊤ : Subgroup X) = Subgroup.centralizer ({z} : Set X) ⊔
      Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) := by
  classical
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hE4 with h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hE4 with h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hE4 with h | h | h <;> simp at h
  have hee : ee = 1 := M.exp_eq_f hD4
  obtain ⟨RA, RA', a, b, x, x', hRA, hRA', hRR, hcommR, hxR, hx2, hx1, hx'R, hx'2, hx'1, hxx',
    haR, hasq, hbR, hbsq, hψa, hψb, hψx, hψx'⟩ :=
    Q3T8.Asc77.T7L.twin_lifts hΦ M hG2 hD4 hnpsl T.hA T.hA' T.ne T.hzA T.hzA' T.ha₀ T.hb₀ T.ha₀sq
        T.hb₀sq
  have hK := hgen tg k ee M.admissible (by rw [hee]; exact hE4) RA (M.cls_sub hRA) RA'
    (M.cls_sub hRA') hRR hcommR x hxR hx2 hx1 x' hx'R hx'2 hx'1 hxx' a haR hasq b hbR hbsq

  have hz2 : z * z = 1 := T.hzA.sq
  have hainv : a₀⁻¹ = z * a₀ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc a₀ * (z * a₀) = (a₀ * a₀) * (a₀ * a₀) := by rw [← T.ha₀sq]; simp only [mul_assoc]
      _ = 1 := by rw [T.ha₀sq, hz2]
  have hw₂ : a₀⁻¹ * b₀ = z * (a₀ * b₀) := by rw [hainv, mul_assoc]
  have hw₁ : a₀ * b₀ = z * (a₀⁻¹ * b₀) := by
    rw [hw₂, ← mul_assoc, ← mul_assoc, hz2, one_mul]

  have hcov : Subgroup.centralizer ({a₀ * b₀} : Set X) ⊔
      Subgroup.centralizer ({a₀⁻¹ * b₀} : Set X) ≤
      Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) := by
    rcases T.hw with h | h
    · subst h
      rw [← hw₂]
    · subst h
      rw [← hw₁, sup_comm]
  have hcov' : Subgroup.centralizer ({a₀ * b₀} : Set X) ⊔
      Subgroup.centralizer ({a₀⁻¹ * b₀} : Set X) ≤ Subgroup.centralizer ({z} : Set X) ⊔
        Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) :=
    hcov.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)

  have h0 : (Subgroup.center (modelUniv tg k 3 ee Fact.out).K).map M.ψ ≤
      Subgroup.centralizer ({z} : Set X) := by
    have := (Subgroup.map_mono (Subgroup.center_le_centralizer ({x} : Set _))).trans
      (map_centralizer_le M.ψ x)
    rwa [hψx] at this
  have h1 : (Subgroup.centralizer ({x} : Set (modelUniv tg k 3 ee Fact.out).K)).map M.ψ ≤
      Subgroup.centralizer ({z} : Set X) := by
    have := map_centralizer_le M.ψ x
    rwa [hψx] at this
  have h2 : (Subgroup.centralizer ({a * b} : Set (modelUniv tg k 3 ee Fact.out).K)).map M.ψ ≤
      Subgroup.centralizer ({a₀ * b₀} : Set X) := by
    have := map_centralizer_le M.ψ (a * b)
    rwa [map_mul, hψa, hψb] at this
  have h3 : (Subgroup.centralizer ({a⁻¹ * b} : Set (modelUniv tg k 3 ee Fact.out).K)).map M.ψ ≤
      Subgroup.centralizer ({a₀⁻¹ * b₀} : Set X) := by
    have := map_centralizer_le M.ψ (a⁻¹ * b)
    rwa [map_mul, map_inv, hψa, hψb] at this
  refine (eq_top_iff.mpr ?_).symm
  intro y _
  obtain ⟨k₀, rfl⟩ := M.surj y
  have hk : k₀ ∈ (⊤ : Subgroup (modelUniv tg k 3 ee Fact.out).K) := Subgroup.mem_top k₀
  rw [hK] at hk
  have hmem := Subgroup.mem_map_of_mem M.ψ hk
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup] at hmem
  have hz' : Subgroup.centralizer ({z} : Set X) ≤ Subgroup.centralizer ({z} : Set X) ⊔
      Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) :=
    le_sup_left.trans le_sup_left
  exact (sup_le (h0.trans hz') (sup_le (sup_le (h1.trans hz') (h2.trans (le_sup_left.trans hcov')))
    (h3.trans (le_sup_right.trans hcov')))) hmem

theorem twinSection_gen_conj (htcf : Q3T8.Asc77.TwinCentralFact3) (hgen : Q3T8.Asc77.E4TwinGen3) {n
    : ℕ} (hBelow :
    Q3T8.Generic.CITBelowU n) (hlt : Nat.card X < n)
    (hS : Q3T8.Asc77.GenSection Φ) {A A' : Subgroup X} {z a₀ b₀ w : X}
    (T : TwinSect Φ A A' z a₀ b₀ w) :
    (⊤ : Subgroup X) = Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({w} : Set X) ⊔
      Subgroup.centralizer ({z * w} : Set X) ∧ ConjTwinInv Φ z := by
  rcases Q3T8.Asc77.T7L.twinSection_cases htcf hBelow hlt hS T with hconn | ⟨D, hcard, i, hE4⟩
  · have hc := twinSection_central T.hzA T.hzA' hconn hS.gen
    have hCz : Subgroup.centralizer ({z} : Set X) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc y)
    refine ⟨?_, conjTwinInv_of_conn T.hzA T.hzA' hconn⟩
    rw [hCz, top_sup_eq, top_sup_eq]
  · let M := Q3T8.Asc77.T7L.toModelOfGen hS.hyp D hcard hS.gen i
    have hG2 : D.tag i ≠ .G2 := by
      intro h
      rcases hE4 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> simp at h
    have hD4 : D.tag i ≠ .trialityD4 := by
      intro h
      rcases hE4 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> simp at h
    exact ⟨Q3T8.Asc77.T7L.e4_gen_of_model hgen hS.hyp M hE4 T,
      conjTwinInv_of_model M hG2 hD4 T.hA T.hzA⟩
end T7L
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
