module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cPair3
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Elem
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Bar
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7E
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Local
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitCong
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDGeneric
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

omit [Finite X] in
theorem inv_conj_of_inv {w a b : X} (hw : w⁻¹ = w) (h : w * a * w⁻¹ = b) : w⁻¹ * a * w = b := by
  rw [hw] at h ⊢
  exact h

namespace VSide

variable (V : VSide S T₁)

theorem E_comm {e f : X} (he : e ∈ S.E V.yi) (hf : f ∈ S.E V.yi) : e * f = f * e :=
  V.F.elemAbelianTwo_E.comm _ he _ hf

theorem ki_mem_E : V.ki ∈ S.E V.yi := V.F.kF_mem_E V.yi

theorem exists_evE : ∃ φ : (Fin 4 → Multiplicative (ZMod 2)) →* X,
    φ (e4 0) = t ∧ φ (e4 1) = S.z ∧ φ (e4 2) = V.yi ∧ φ (e4 3) = V.ki := by
  have ht := Frame.t_mem_E (S := S) V.yi
  have hz := Frame.z_mem_E (S := S) V.yi
  have hy := Frame.yi_mem_E (S := S) V.yi
  have hk := V.ki_mem_E
  exact exists_evHom4 (V.E_comm ht hz) (V.E_comm ht hy) (V.E_comm ht hk) (V.E_comm hz hy)
    (V.E_comm hz hk) (V.E_comm hy hk) (tt (A := A)) (zz S) V.yi_sq V.ki_sq

theorem mem_normalizer_E0 {n : X} (hn : n ∈ normalizer (S.E V.yi : Set X)) :
    n ∈ normalizer (S.E0 V.yi V.ki : Set X) := by
  rw [mem_normalizer_iff]
  intro e
  refine ⟨fun he => V.conj_mem_E0 hn he, fun he => ?_⟩
  have := V.conj_mem_E0 (inv_mem hn) he
  rwa [show n⁻¹ * (n * e * n⁻¹) * n⁻¹⁻¹ = e by group] at this

theorem comm_mem {a b : X} (ha : a ∈ V.D.S₁) (hb : b ∈ V.D.S₁) :
    a * b * a⁻¹ * b⁻¹ ∈ S.E0 V.yi V.ki ⊔ zpowers V.D.w₁ :=
  V.D.S₁_commutator_mem a ha b hb

theorem mem_E0w {c : X} (hc : c ∈ S.E0 V.yi V.ki ⊔ zpowers V.D.w₁) :
    c ∈ S.E0 V.yi V.ki ∨ c * V.D.w₁⁻¹ ∈ S.E0 V.yi V.ki :=
  Sec7.mem_or_of_mem_sup_zpowers (V.mem_normalizer_E0 (V.D.S₁_le V.w₁_mem_S₁))
    (by rw [V.w₁_sq]; exact one_mem _) hc

theorem mem_E0_cases {e : X} (he : e ∈ S.E0 V.yi V.ki) :
    e ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) ∨
      e * V.yi ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  have he' : e ∈ S.E0 V.F.yF V.F.kF := he
  rw [V.F.E0_eq'] at he'
  exact Sec7.mem_or_of_mem_sup V.F.elemAbelianTwo_zk V.F.yF_sq
    (fun _ hb => V.F.yF_comm_zk hb) he'

theorem kappa_conj_t : (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹) * t *
    (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹)⁻¹ = t := by
  obtain ⟨φ, e0, e1, e2, e3⟩ := V.exists_evE
  have a1 := inv_conj_of_inv V.w₁_inv V.w₁_conj_t
  have hw₂z := inv_conj_of_inv V.w₂_inv V.w₂_conj_z
  have hw₂t := inv_conj_of_inv V.w₂_inv V.w₂_conj_t
  have hw₂k := inv_conj_of_inv V.w₂_inv V.w₂_conj_ki
  have a2 : V.D.w₂⁻¹ * (t * S.z * V.ki) * V.D.w₂ = t * V.yi * S.z * V.ki := by
    rw [show V.D.w₂⁻¹ * (t * S.z * V.ki) * V.D.w₂ = (V.D.w₂⁻¹ * t * V.D.w₂) *
      (V.D.w₂⁻¹ * S.z * V.D.w₂) * (V.D.w₂⁻¹ * V.ki * V.D.w₂) by group, hw₂t, hw₂z, hw₂k]
    elem_eq φ e1 e2 e3 e0
  have a3 : V.D.w₁ * (t * V.yi * S.z * V.ki) * V.D.w₁⁻¹ = t * V.yi * V.ki := by
    rw [show V.D.w₁ * (t * V.yi * S.z * V.ki) * V.D.w₁⁻¹ = (V.D.w₁ * t * V.D.w₁⁻¹) *
      (V.D.w₁ * V.yi * V.D.w₁⁻¹) * (V.D.w₁ * S.z * V.D.w₁⁻¹) * (V.D.w₁ * V.ki * V.D.w₁⁻¹) by
        group, V.w₁_conj_t, V.w₁_conj_yi, V.w₁_conj_z, V.w₁_conj_ki]
    elem_eq φ e1 e2 e3 e0
  have a4 : V.D.w₂ * (t * V.yi * V.ki) * V.D.w₂⁻¹ = t := by
    rw [show V.D.w₂ * (t * V.yi * V.ki) * V.D.w₂⁻¹ = (V.D.w₂ * t * V.D.w₂⁻¹) *
      (V.D.w₂ * V.yi * V.D.w₂⁻¹) * (V.D.w₂ * V.ki * V.D.w₂⁻¹) by group, V.w₂_conj_t,
      V.w₂_conj_yi, V.w₂_conj_ki]
    elem_eq φ e1 e2 e3 e0
  calc (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹) * t *
      (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹)⁻¹ =
      V.D.w₂ * (V.D.w₁ * (V.D.w₂⁻¹ * (V.D.w₁⁻¹ * t * V.D.w₁) * V.D.w₂) * V.D.w₁⁻¹) *
        V.D.w₂⁻¹ := by group
    _ = t := by rw [a1, a2, a3, a4]

theorem kappa_mem_E0 : V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ ∈ S.E0 V.yi V.ki := by
  rcases V.mem_E0w (V.comm_mem V.w₂_mem_S₁ V.w₁_mem_S₁) with h | h
  · exact h
  · exfalso
    set κ := V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ with hκ
    set e := κ * V.D.w₁⁻¹ with he
    have hκe : κ = e * V.D.w₁ := by rw [he]; group
    have heE : e ∈ S.E V.yi := V.E0_le_E h
    have h1 := V.kappa_conj_t
    rw [← hκ, hκe] at h1
    have hzk : t * S.z * V.ki ∈ S.E V.yi :=
      mul_mem (mul_mem (Frame.t_mem_E _) (Frame.z_mem_E _)) V.ki_mem_E
    rw [show e * V.D.w₁ * t * (e * V.D.w₁)⁻¹ = e * (V.D.w₁ * t * V.D.w₁⁻¹) * e⁻¹ by group,
      V.w₁_conj_t, V.E_comm heE hzk, mul_inv_cancel_right, mul_assoc] at h1
    have h2 : S.z * V.ki = 1 := mul_eq_left.mp h1
    exact V.ki_ne_z (by rw [eq_inv_of_mul_eq_one_right h2, z_inv S])

theorem kappa_eq : V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ = 1 ∨
    V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ = V.ki := by
  set κ := V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * V.D.w₁⁻¹ with hκ
  have hκw : V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ = κ * V.D.w₁ := by rw [hκ]; group
  have hw₁ := V.w₁_mul
  have hw₂ := V.w₂_mul
  have hb : κ * (V.D.w₁ * κ * V.D.w₁⁻¹) = 1 := by
    have : (κ * V.D.w₁) * (κ * V.D.w₁) = 1 := by
      rw [← hκw, show V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹ * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) =
        V.D.w₂ * (V.D.w₁ * V.D.w₁) * V.D.w₂⁻¹ by group, hw₁, mul_one, mul_inv_cancel]
    calc κ * (V.D.w₁ * κ * V.D.w₁⁻¹) = (κ * V.D.w₁) * (κ * V.D.w₁) * V.D.w₁⁻¹ * V.D.w₁⁻¹ := by
          group
      _ = 1 := by rw [this, one_mul, ← mul_inv_rev, hw₁, inv_one]
  have ha : (V.D.w₂ * κ * V.D.w₂⁻¹) * κ = 1 := by
    have h1 : V.D.w₂ * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) * V.D.w₂⁻¹ = V.D.w₁ := by
      rw [show V.D.w₂ * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) * V.D.w₂⁻¹ =
        (V.D.w₂ * V.D.w₂) * V.D.w₁ * (V.D.w₂ * V.D.w₂)⁻¹ by group, hw₂, one_mul, inv_one,
        mul_one]
    have h2 : V.D.w₂ * (κ * V.D.w₁) * V.D.w₂⁻¹ = V.D.w₁ := by rw [← hκw]; exact h1
    have h3 : (V.D.w₂ * κ * V.D.w₂⁻¹) * (κ * V.D.w₁) = V.D.w₁ := by
      calc (V.D.w₂ * κ * V.D.w₂⁻¹) * (κ * V.D.w₁) =
          (V.D.w₂ * κ * V.D.w₂⁻¹) * (V.D.w₂ * V.D.w₁ * V.D.w₂⁻¹) := by rw [hκw]
        _ = V.D.w₂ * (κ * V.D.w₁) * V.D.w₂⁻¹ := by group
        _ = V.D.w₁ := h2
    calc (V.D.w₂ * κ * V.D.w₂⁻¹) * κ = (V.D.w₂ * κ * V.D.w₂⁻¹) * (κ * V.D.w₁) * V.D.w₁⁻¹ := by
          group
      _ = 1 := by rw [h3, mul_inv_cancel]
  have hmem := V.kappa_mem_E0
  rw [← hκ] at hmem
  rcases V.mem_E0_cases hmem with h | h
  · rcases V.eq_of_mem_zk h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      rw [h1, V.w₂_conj_z] at ha
      exact V.ki_ne_one (by
        rw [mul_assoc, V.ki_comm (R_le_TE S (z_mem_R S)), ← mul_assoc, zz S, one_mul] at ha
        exact ha)
    · exact Or.inr h1
    · exfalso
      rw [h1, show V.D.w₂ * (S.z * V.ki) * V.D.w₂⁻¹ = (V.D.w₂ * S.z * V.D.w₂⁻¹) *
        (V.D.w₂ * V.ki * V.D.w₂⁻¹) by group, V.w₂_conj_z, V.w₂_conj_ki, mul_assoc S.z,
        V.ki_sq, mul_one, ← mul_assoc, zz S, one_mul] at ha
      exact V.ki_ne_one ha
  · exfalso
    set c := κ * V.yi with hc
    have hκc : κ = c * V.yi := by rw [hc, mul_assoc, V.yi_sq, mul_one]
    have hcw : V.D.w₁ * c * V.D.w₁⁻¹ = c := V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki h
    rw [hκc, show V.D.w₁ * (c * V.yi) * V.D.w₁⁻¹ = (V.D.w₁ * c * V.D.w₁⁻¹) *
      (V.D.w₁ * V.yi * V.D.w₁⁻¹) by group, hcw, V.w₁_conj_yi] at hb
    have hcB := V.zk_le_B h
    have hcy : c * V.yi = V.yi * c := central_of_mem_B S hcB V.yi_mem_TE
    have hcc : c * c = 1 := by rw [← pow_two, sq_of_mem_B S hcB]
    rw [show c * V.yi * (c * (V.yi * V.ki)) = (c * V.yi) * c * V.yi * V.ki by group, hcy,
      mul_assoc V.yi, hcc, mul_one, V.yi_sq, one_mul] at hb
    exact V.ki_ne_one hb

theorem yi_w₁ : V.yi * V.D.w₁ = V.D.w₁ * (V.yi * V.ki) := by
  have h := inv_conj_of_inv V.w₁_inv V.w₁_conj_yi
  calc V.yi * V.D.w₁ = V.D.w₁ * (V.D.w₁⁻¹ * V.yi * V.D.w₁) := by group
    _ = V.D.w₁ * (V.yi * V.ki) := by rw [h]

theorem zk_w₁ {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    c * V.D.w₁ = V.D.w₁ * c := by
  have h := inv_conj_of_inv V.w₁_inv (V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki hc)
  calc c * V.D.w₁ = V.D.w₁ * (V.D.w₁⁻¹ * c * V.D.w₁) := by group
    _ = V.D.w₁ * c := by rw [h]

theorem u_yi : V.D.u * V.yi = S.z * V.yi * V.D.u := by
  rw [← V.u_conj_yi]; group

end VSide

namespace CPair

variable (P : CPair S T₁)

theorem w₂_conj_vN : P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹ = P.V.vN * (P.V.yi * P.V.ki) := by
  set K := (zpowers P.V.ki ⊔ zpowers t : Subgroup X) with hK
  have hC₁ : ¬ P.V.D.C₁ ≤ K := by
    intro hle
    have heq : P.V.D.C₁ = K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [P.V.D.card_C₁, P.V.card_kt])
    have ht : t ∈ P.V.D.C₁ := heq ▸ mem_sup_right (mem_zpowers _)
    have h1 := P.V.D.C₁_comm t ht P.V.D.w₁ P.V.w₁_mem_Q0
    apply P.V.D.w₁_comm_t
    rw [← h1]; group
  obtain ⟨c, hc, hcK⟩ := IsConcreteLE.not_le_iff_exists.mp hC₁
  have hcC := P.V.D.C₁_le hc
  have hcw₁ := P.V.D.C₁_comm c hc P.V.D.w₁ P.V.w₁_mem_Q0
  have hcw₂ := P.V.D.C₁_comm c hc P.V.D.w₂ P.V.w₂_mem_Q0
  rcases P.V.mem_C hcC with h | h
  · exact absurd h hcK
  set d := c * P.V.vN⁻¹ with hd
  have hc' : c = d * P.V.vN := by rw [hd]; group
  rw [hc'] at hcw₁ hcw₂
  rcases Sec7.mem_or_of_mem_sup P.V.elemAbelianTwo_ki (SD.t_sq (A := A))
    (fun a ha => P.V.t_comm_ki ha) h with h' | h'
  ·
    exfalso
    have hdw : P.V.D.w₁ * d * P.V.D.w₁⁻¹ = d := by
      rcases P.V.eq_of_mem_ki h' with h1 | h1 <;> rw [h1]
      · group
      · exact P.V.w₁_conj_ki
    have hvw : P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹ = 1 := by
      calc P.V.D.w₁ * P.V.vN * P.V.D.w₁⁻¹ * P.V.vN⁻¹ =
          (P.V.D.w₁ * d * P.V.D.w₁⁻¹)⁻¹ * (P.V.D.w₁ * (d * P.V.vN)) * P.V.D.w₁⁻¹ * P.V.vN⁻¹ := by
            group
        _ = 1 := by rw [hdw, ← hcw₁]; group
    rw [P.w₁_comm_vN] at hvw
    apply P.V.ki_ne_z
    calc P.V.ki = S.z * (S.z * P.V.ki) := by rw [← mul_assoc, zz S, one_mul]
      _ = S.z := by rw [hvw, mul_one]
  ·
    set d' := d * t with hd'
    have hdd : d = d' * t := by rw [hd', mul_assoc, tt (A := A), mul_one]
    have hdw : P.V.D.w₂ * d' * P.V.D.w₂⁻¹ = d' := by
      rcases P.V.eq_of_mem_ki h' with h1 | h1 <;> rw [h1]
      · group
      · exact P.V.w₂_conj_ki
    rw [hdd] at hcw₂
    have h2 : P.V.D.w₂ * (d' * t * P.V.vN) * P.V.D.w₂⁻¹ = d' * t * P.V.vN := by
      rw [← hcw₂]; group
    rw [show P.V.D.w₂ * (d' * t * P.V.vN) * P.V.D.w₂⁻¹ = (P.V.D.w₂ * d' * P.V.D.w₂⁻¹) *
      (P.V.D.w₂ * t * P.V.D.w₂⁻¹) * (P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹) by group, hdw,
      P.V.w₂_conj_t] at h2
    have hyk : P.V.yi * P.V.ki = P.V.ki * P.V.yi := (P.V.ki_comm P.V.yi_mem_TE).symm
    calc P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹ = (d' * (t * P.V.yi * P.V.ki))⁻¹ *
        (d' * (t * P.V.yi * P.V.ki) * (P.V.D.w₂ * P.V.vN * P.V.D.w₂⁻¹)) := by group
      _ = (d' * (t * P.V.yi * P.V.ki))⁻¹ * (d' * t * P.V.vN) := by rw [h2]
      _ = (P.V.yi * P.V.ki)⁻¹ * P.V.vN := by group
      _ = P.V.vN * (P.V.yi * P.V.ki) := by
          rw [mul_inv_rev, P.V.ki_inv, P.V.yi_inv, ← hyk]
          have h3 : P.V.vN * (P.V.yi * P.V.ki) * P.V.vN⁻¹ = P.V.yi * P.V.ki := by
            rw [show P.V.vN * (P.V.yi * P.V.ki) * P.V.vN⁻¹ = (P.V.vN * P.V.yi * P.V.vN⁻¹) *
              (P.V.vN * P.V.ki * P.V.vN⁻¹) by group, P.V.vN_conj_yi, P.V.vN_conj_ki]
          calc P.V.yi * P.V.ki * P.V.vN = (P.V.vN * (P.V.yi * P.V.ki) * P.V.vN⁻¹) * P.V.vN := by
                rw [h3]
            _ = P.V.vN * (P.V.yi * P.V.ki) := by group

end CPair

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
