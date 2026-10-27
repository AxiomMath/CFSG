module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement

section Algebra

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ B ⊔ A) :
    ∃ b ∈ B, ∃ a ∈ A, x = b * a :=
  CFSG.ClassicalInvolution.Asc77.T7H.exists_mul_of_mem_sup_normalizer hB hx

theorem commutator_mem_of_mem_sup_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {x y : G} (hx : x ∈ B ⊔ A) (hy : y ∈ B ⊔ A) : ⁅x, y⁆ ∈ A := by
  obtain ⟨b₁, hb₁, a₁, ha₁, rfl⟩ := exists_mul_of_mem_sup_normalizer hB hx
  obtain ⟨b₂, hb₂, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_normalizer hB hy
  have hconj : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := fun b hb a ha =>
    (Subgroup.mem_normalizer_iff.mp (hB hb) a).mp ha
  have hconj' : ∀ b ∈ B, ∀ a ∈ A, b⁻¹ * a * b ∈ A := fun b hb a ha => by
    have := hconj b⁻¹ (B.inv_mem hb) a ha
    simpa using this
  have hc : b₂ * b₁ = b₁ * b₂ := hBc b₂ hb₂ b₁ hb₁
  have hxy : (b₁ * a₁) * (b₂ * a₂) = (b₁ * b₂) * ((b₂⁻¹ * a₁ * b₂) * a₂) := by group
  have hyx : (b₂ * a₂) * (b₁ * a₁) = (b₁ * b₂) * ((b₁⁻¹ * a₂ * b₁) * a₁) := by
    rw [← hc]
    group
  have key : ⁅b₁ * a₁, b₂ * a₂⁆ = (b₁ * b₂) *
      (((b₂⁻¹ * a₁ * b₂) * a₂) * ((b₁⁻¹ * a₂ * b₁) * a₁)⁻¹) * (b₁ * b₂)⁻¹ := by
    have h1 : ⁅b₁ * a₁, b₂ * a₂⁆ = ((b₁ * a₁) * (b₂ * a₂)) * ((b₂ * a₂) * (b₁ * a₁))⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h1, hxy, hyx]
    group
  rw [key]
  have hA : ((b₂⁻¹ * a₁ * b₂) * a₂) * ((b₁⁻¹ * a₂ * b₁) * a₁)⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (hconj' b₂ hb₂ a₁ ha₁) ha₂)
      (A.inv_mem (A.mul_mem (hconj' b₁ hb₁ a₂ ha₂) ha₁))
  exact hconj _ (B.mul_mem hb₁ hb₂) _ hA

theorem mem_normalizer_sup' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  CFSG.ClassicalInvolution.Asc77.T7H.mem_normalizer_sup' hA hB

theorem mem_normalizer_inf' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  CFSG.ClassicalInvolution.Asc77.T7H.mem_normalizer_inf' hA hB

end Algebra

section SL2Three

theorem sl2Three_commute_conj_central :
    ∀ x : SL(2, ZMod 3), (∀ g : SL(2, ZMod 3), x * (g * x * g⁻¹) = (g * x * g⁻¹) * x) →
      ∀ g : SL(2, ZMod 3), x * g = g * x := by
  decide +kernel

theorem sl2Three_le_center_of_normal_abelian {N : Subgroup SL(2, ZMod 3)} (hN : N.Normal)
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : N ≤ Subgroup.center SL(2, ZMod 3) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact (sl2Three_commute_conj_central x (fun g' => hab x hx _ (hN.conj_mem x hx g')) g).symm

end SL2Three


theorem c23_7_proved : Q3T8.Asc77.C23_7 := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := h.std.setting
  have hst : Q3T8.Asc77.AscStand Ω K := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hcl : Q3T8.Generic.IsClassicalMember K z :=
    Q3T8.Asc77.isClassicalMember_of_twin hΩ hK hz
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := Q3T8.Asc77.T7D.exists_sylow_frame hs h.hW h.hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ h.hW hWS (mem_RSet_of_isSylow2In hK hR) hRS
  obtain ⟨w, hwRW, hw4⟩ :=
    Q3T8.Asc77.Thompson.exists_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod Ω) h.hW hRD
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ h.hW
  have heW : e ∈ W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← h.he]
    exact Subgroup.mem_closure_singleton_self e
  have hec : ∀ x ∈ Subgroup.normalizer (W : Set G), e * x = x * e := by
    intro x hx
    obtain ⟨y, hy, hye⟩ := heW.2
    have := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
    have h2 : (x : G) * (y : G) = (y : G) * (x : G) := congrArg Subtype.val this
    rw [← hye]
    exact h2.symm
  have hcA : IsPGroup 2 (Subgroup.zpowers e) :=
    isPGroup_zpowers_of_mul_self_eq_one h.he2 h.he1
  have hRc : R ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec r (hRD.2 hr)).symm
  have hetq : e ∈ trivialOnQuot K :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hcA hK).mpr ⟨R, hR, hRc⟩
  have hKt : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e := ⟨hK, hetq⟩
  set E := Q3T8.Asc77.ExactLayer.exactLayer Ω e with hE
  set Ke := Q3T8.Asc77.ExactLayer.exactCore e K with hKe
  have hKeE : Ke ≤ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hKt
  have hKeK : Ke ≤ K := Q3T8.Asc77.ExactLayer.exactCore_le_left e K
  have hRKe : R ≤ Ke := le_inf hR.1 hRc
  obtain ⟨φ, hφ⟩ := (hcl.toQ3 (by norm_num)).exists_chart
  have hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K := fun x => by
    rw [← hφ.ker_eq]
    exact Iff.rfl
  intro hle
  set A := oddCoreOf E with hA
  have hAN : ∀ x ∈ E, x ∈ Subgroup.normalizer (A : Set G) := fun x hx =>
    CFSG.ClassicalInvolution.Asc77.mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hx)
  set W₁ : Subgroup G := W ⊓ E with hW₁
  have hW₁A : W₁ ≤ Subgroup.normalizer (A : Set G) := fun x hx => hAN x hx.2
  have hW₁ab : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y = y * x := fun x hx y hy => hWab x hx.1 y hy.1
  set V : Subgroup G := W₁ ⊔ A with hV
  have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
    refine hle.trans (sup_le ?_ ?_)
    · exact (le_sup_right : A ≤ V).trans Subgroup.le_normalizer
    · intro x hx
      refine mem_normalizer_sup' ?_ (hAN x hx.1)
      exact mem_normalizer_inf' hx.2 (Subgroup.le_normalizer hx.1)
  have hcover : ∀ s : SL(2, ZMod 3), ∃ (i : G) (hi : i ∈ K), i ∈ Ke ∧ φ ⟨i, hi⟩ = s := by
    intro s
    obtain ⟨x, rfl⟩ := hφ.surjective s
    obtain ⟨i, hi, n, hn, hxin⟩ :=
      Q3T8.Asc77.ExactLayer.exactCore_cover hcl hcA hetq (x : G) x.2
    have hiK : i ∈ K := hKeK hi
    have hnK : n ∈ K := oddCoreOf_le_self K hn
    refine ⟨i, hiK, hi, ?_⟩
    have h1 : φ ⟨n, hnK⟩ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp hn).2
    have h2 : x = ⟨i, hiK⟩ * ⟨n, hnK⟩ := Subtype.ext hxin
    rw [h2, map_mul, h1, mul_one]
  have hQ : Ke ⊓ A ≤ oddCoreOf K := by
    have h1 : Ke ⊓ A ≤ CFSG.ClassicalInvolution.Balance.oddCoreIn Ke :=
      CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes inf_le_left
        (fun x hx => mem_normalizer_inf' (Subgroup.le_normalizer hx) (hAN x (hKeE hx)))
        ((oddCoreOf_odd_natCard E).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    intro x hx
    have hxO := h1 hx
    rw [hKe, Q3NL.oddCoreIn_exactCore3 (hcl.toQ3 (by norm_num)) hcA hetq] at hxO
    exact hxO.2
  set P : Subgroup G := Ke ⊓ V with hP
  set N : Subgroup SL(2, ZMod 3) := (P.subgroupOf K).map φ with hN
  have hNnorm : N.Normal := by
    refine ⟨fun n hn s => ?_⟩
    obtain ⟨i, hiK, hiKe, rfl⟩ := hcover s
    obtain ⟨x, hx, rfl⟩ := hn
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have hconj : i * (x : G) * i⁻¹ ∈ P := by
      refine ⟨Ke.mul_mem (Ke.mul_mem hiKe hxP.1) (Ke.inv_mem hiKe), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hEV (hKeE hiKe)) (x : G)).mp hxP.2
    refine ⟨⟨i * (x : G) * i⁻¹, K.mul_mem (K.mul_mem hiK x.2) (K.inv_mem hiK)⟩,
      Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    have hmul : (⟨i * (x : G) * i⁻¹, K.mul_mem (K.mul_mem hiK x.2) (K.inv_mem hiK)⟩ : ↥K) =
        ⟨i, hiK⟩ * x * ⟨i, hiK⟩⁻¹ := rfl
    rw [hmul, map_mul, map_mul, map_inv]
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
    have hcomA : ⁅(x : G), (y : G)⁆ ∈ A :=
      commutator_mem_of_mem_sup_normalizer hW₁A hW₁ab hxP.2 hyP.2
    have hcomKe : ⁅(x : G), (y : G)⁆ ∈ Ke := by
      rw [commutatorElement_def]
      exact Ke.mul_mem (Ke.mul_mem (Ke.mul_mem hxP.1 hyP.1) (Ke.inv_mem hxP.1))
        (Ke.inv_mem hyP.1)
    have hO : ⁅(x : G), (y : G)⁆ ∈ oddCoreOf K := hQ ⟨hcomKe, hcomA⟩
    have h1 : φ ⁅x, y⁆ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp hO).2
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hNc : N ≤ Subgroup.center SL(2, ZMod 3) := sl2Three_le_center_of_normal_abelian hNnorm hNab
  have hwK : w ∈ K := hR.1 hwRW.1
  have hwP : w ∈ P :=
    ⟨hRKe hwRW.1, (le_sup_left : W₁ ≤ V) ⟨hwRW.2, hKeE (hRKe hwRW.1)⟩⟩
  have hφw : φ ⟨w, hwK⟩ ∈ Subgroup.center SL(2, ZMod 3) :=
    hNc ⟨⟨w, hwK⟩, Subgroup.mem_subgroupOf.mpr hwP, rfl⟩
  have hcomm : ∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K := by
    intro y hy
    have h1 : φ ⁅(⟨w, hwK⟩ : ↥K), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp hφw (φ ⟨y, hy⟩)).symm)
    exact mem_oddCoreOf_iff.mpr ⟨_, (hφk _).mp h1⟩
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hw4]; norm_num)
  rcases Q3T8.Asc77.HypOmegaModT.center_two hΩ hK hz w hwK hw2 hcomm with hh | hh
  · rw [hh, orderOf_one] at hw4
    omega
  · rw [hh] at hw4
    have : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    omega

end CFSG.ClassicalInvolution.Q3.Q3T7S23
