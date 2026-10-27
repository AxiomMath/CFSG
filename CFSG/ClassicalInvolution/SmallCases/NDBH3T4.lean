module

public import CFSG.ClassicalInvolution.SmallCases.NDBH3T3
import CFSG.ClassicalInvolution.SmallCases.NDBH1
import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral

public section

namespace CFSG.ClassicalInvolution.NDB.NDBH3

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

omit [Finite G] in
theorem commute_of_isUniqueInvolution {L : Subgroup G} {a : G} (hU : IsUniqueInvolution L a) :
    ∀ q ∈ L, a * q = q * a := by
  intro q hq
  have h1 : q * a * q⁻¹ ∈ L := L.mul_mem (L.mul_mem hq hU.mem) (L.inv_mem hq)
  have h2 : q * a * q⁻¹ * (q * a * q⁻¹) = 1 := by
    calc q * a * q⁻¹ * (q * a * q⁻¹) = q * (a * a) * q⁻¹ := by group
      _ = 1 := by rw [hU.sq]; group
  rcases hU.unique _ h1 h2 with h | h
  · exfalso
    apply hU.ne_one
    calc a = q⁻¹ * (q * a * q⁻¹) * q := by group
      _ = 1 := by rw [h]; group
  · calc a * q = (q * a * q⁻¹) * q := by rw [h]
      _ = q * a := by group

omit [Finite G] in
theorem comm_of_isElemAbelian {B : Subgroup G} (hB : IsElemAbelian 2 B) :
    ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun _ ha _ hb => CFSG.Open.IsElemAbelian.comm hB ha hb


theorem mem_modOdd_of_commutes (C : XCtx p f Ω z) {B : Subgroup G}
    (hBY : B ≤ exactLayer Ω z) (hzB : z ∈ B) (hsq : ∀ x ∈ B, x * x = 1)
    (hcm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {e : G} (heB : e ∈ B) (he1 : e ≠ 1) (hez : e ≠ z)
    {q : OddQuot z} (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) := by
  have hz1 : z ≠ 1 := C.hKz.ne_one
  have hesq : e * e = 1 := hsq e heB
  have hze : z * e = e * z := hcm z hzB e heB
  set F : Subgroup G := Subgroup.closure ({z, e} : Set G) with hF
  have hFB : F ≤ B := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzB
    · exact heB
  have hcard : Nat.card F = 4 :=
    card_closure_pair_eq_four C.hKz.sq hesq hz1 he1 (fun h => hez h.symm) hze
  have hFE : F ∈ signalizerFunctorEk 2 2 B := ⟨hFB, by rw [hcard]; norm_num⟩
  have hFY : F ≤ exactLayer Ω z := hFB.trans hBY
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => hsq x (hFB hx)
  have hcent : ∀ (x : G) (_ : x ∈ F) (hC : x ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨x, hC⟩ * q = q * oddQuotMk z ⟨x, hC⟩ := by
    refine ChainFrame.commutes_of_closure (oddQuotMk z) q (S := ({z, e} : Set G)) ?_ ?_
    · rintro s (rfl | rfl)
      · exact XCtx.hzC _
      · exact exactLayer_le_centralizer Ω z (hBY heB)
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central (XCtx.hzC _) q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (a := z) hF2 hFY hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) :=
    le_iSup₂ (f := fun F (_ : F ∈ signalizerFunctorEk 2 2 B) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

theorem generation_of_cover (C : XCtx p f Ω z) {B : Subgroup G}
    (hBY : B ≤ exactLayer Ω z) (hzB : z ∈ B) (hsq : ∀ x ∈ B, x * x = 1)
    (hcm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcov : ∀ j : Fin C.D.card, ∃ e ∈ B, e ≠ 1 ∧ e ≠ z ∧
      ∀ (he : e ∈ Subgroup.centralizer ({z} : Set G)) (k : (compModel C.D j).K),
        oddQuotMk z ⟨e, he⟩ * C.psi j k = C.psi j k * oddQuotMk z ⟨e, he⟩) :
    CentralizerGenerationStar Ω B z := by
  classical
  set H : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 B,
    (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) with hH
  have hHY : H ≤ exactLayer Ω z := iSup₂_le fun F _ => inf_le_right
  have hψ : ∀ (j : Fin C.D.card) (k : (compModel C.D j).K), C.psi j k ∈ modOdd z H := by
    intro j k
    obtain ⟨e, heB, he1, hez, hc⟩ := hcov j
    exact mem_modOdd_of_commutes C hBY hzB hsq hcm heB he1 hez (C.psi_mem_memberJoin j k)
      fun he => hc he k
  have hgen : ∀ x : ↥(exactLayer Ω z) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω z),
      sectionQuotientHom C.hs.normalizes x ∈ modOdd z H := by
    have hle : (⨆ i, (C.D.hom i).range) ≤
        (modOdd z H).comap (sectionQuotientHom C.hs.normalizes) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨k, rfl⟩
      exact hψ j k
    intro x
    exact hle (by rw [C.D.generate]; exact Subgroup.mem_top x)
  intro y hy
  obtain ⟨c, hcH, hc⟩ := hgen (QuotientGroup.mk' _ ⟨y, hy⟩)
  have hcH' : (c : G) ∈ H := Subgroup.mem_subgroupOf.mp hcH
  have hcY : (c : G) ∈ exactLayer Ω z := hHY hcH'
  have heq : oddQuotMk z ⟨y, exactLayer_le_centralizer Ω z hy⟩ =
      oddQuotMk z ⟨c, exactLayer_le_centralizer Ω z hcY⟩ := by
    have h1 : sectionQuotientHom C.hs.normalizes (QuotientGroup.mk' _ ⟨y, hy⟩) =
        oddQuotMk z ⟨y, exactLayer_le_centralizer Ω z hy⟩ := rfl
    rw [← h1, ← hc]
  have hker : (⟨y, hy⟩ : ↥(exactLayer Ω z)) * ⟨c, hcY⟩⁻¹ ∈
      (layerToOddQuot (exactFamily Ω z) z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    exact mul_inv_eq_one.mpr heq
  rw [ker_layerToOddQuot_of_normalizes C.hs.normalizes] at hker
  have hmem := mem_oddCoreIn_of_mem_classicalInvolutionOddCore hker
  have hmem' : y * (c : G)⁻¹ ∈ oddCoreIn (exactLayer Ω z) := by
    have : ((⟨y, hy⟩ * ⟨c, hcY⟩⁻¹ : ↥(exactLayer Ω z)) : G) = y * (c : G)⁻¹ := by simp
    rwa [this] at hmem
  have e : y = (y * (c : G)⁻¹) * c := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hmem') (Subgroup.mem_sup_right hcH')

theorem generation_of_pair (C : XCtx p f Ω z) (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2)
    {B : Subgroup G} (hBY : B ≤ exactLayer Ω z) (hzB : z ∈ B) (hsq : ∀ x ∈ B, x * x = 1)
    (hcm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {M₁ M₂ : Subgroup G} (h₁ : M₁ ∈ tqMembers Ω z)
    (h₂ : M₂ ∈ tqMembers Ω z) {e₀ : G} (he₀B : e₀ ∈ B) (he₀1 : e₀ ≠ 1) (he₀z : e₀ ≠ z)
    (hc₁ : ∀ (he : e₀ ∈ Subgroup.centralizer ({z} : Set G)), ∀ q ∈ modOdd z (exactCore z M₁),
      oddQuotMk z ⟨e₀, he⟩ * q = q * oddQuotMk z ⟨e₀, he⟩)
    (hc₂ : ∀ (he : e₀ ∈ Subgroup.centralizer ({z} : Set G)), ∀ q ∈ modOdd z (exactCore z M₂),
      oddQuotMk z ⟨e₀, he⟩ * q = q * oddQuotMk z ⟨e₀, he⟩)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ exactCore z M₁) (hx₂ : x₂ ∈ exactCore z M₂) (heB : x₁ * x₂ ∈ B)
    (he1 : x₁ * x₂ ≠ 1) (hez : x₁ * x₂ ≠ z) : CentralizerGenerationStar Ω B z := by
  obtain ⟨j₁, e₁⟩ := NDBG.exists_range_eq C hall h₁
  obtain ⟨j₂, e₂⟩ := NDBG.exists_range_eq C hall h₂
  refine generation_of_cover C hBY hzB hsq hcm fun j => ?_
  by_cases hj₁ : j = j₁
  · subst hj₁
    exact ⟨e₀, he₀B, he₀1, he₀z, fun he k => hc₁ he _ (by rw [e₁]; exact ⟨k, rfl⟩)⟩
  by_cases hj₂ : j = j₂
  · subst hj₂
    exact ⟨e₀, he₀B, he₀1, he₀z, fun he k => hc₂ he _ (by rw [e₂]; exact ⟨k, rfl⟩)⟩
  refine ⟨x₁ * x₂, heB, he1, hez, fun he k => ?_⟩
  have hx₁C : x₁ ∈ Subgroup.centralizer ({z} : Set G) := exactCore_le_centralizer z M₁ hx₁
  have hx₂C : x₂ ∈ Subgroup.centralizer ({z} : Set G) := exactCore_le_centralizer z M₂ hx₂
  have hbar : oddQuotMk z ⟨x₁ * x₂, he⟩ = oddQuotMk z ⟨x₁, hx₁C⟩ * oddQuotMk z ⟨x₂, hx₂C⟩ := by
    have e : (⟨x₁ * x₂, he⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨x₁, hx₁C⟩ * ⟨x₂, hx₂C⟩ := rfl
    rw [e, map_mul]
  obtain ⟨k₁, hk₁⟩ : oddQuotMk z ⟨x₁, hx₁C⟩ ∈ (C.psi j₁).range := by
    rw [← e₁]
    exact oddQuotMk_mem_modOdd hx₁ hx₁C
  obtain ⟨k₂, hk₂⟩ : oddQuotMk z ⟨x₂, hx₂C⟩ ∈ (C.psi j₂).range := by
    rw [← e₂]
    exact oddQuotMk_mem_modOdd hx₂ hx₂C
  rw [hbar, ← hk₁, ← hk₂]
  calc C.psi j₁ k₁ * C.psi j₂ k₂ * C.psi j k = C.psi j₁ k₁ * (C.psi j₂ k₂ * C.psi j k) := by
        group
    _ = C.psi j₁ k₁ * (C.psi j k * C.psi j₂ k₂) := by rw [C.psi_commute (Ne.symm hj₂) k₂ k]
    _ = (C.psi j₁ k₁ * C.psi j k) * C.psi j₂ k₂ := by group
    _ = (C.psi j k * C.psi j₁ k₁) * C.psi j₂ k₂ := by rw [C.psi_commute (Ne.symm hj₁) k₁ k]
    _ = C.psi j k * (C.psi j₁ k₁ * C.psi j₂ k₂) := by group

theorem zbar_not_mem (C : XCtx p f Ω z) {N : Subgroup G} (hN : N ∈ tqMembers Ω z) {n : G}
    (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    oddQuotMk z ⟨z, XCtx.hzC z⟩ ∉ modOdd z (exactCore z N) := by
  intro hmem
  have hU := C.isUniqueInvolution_modOdd hN hn
  have hz2 : oddQuotMk z ⟨z, XCtx.hzC z⟩ * oddQuotMk z ⟨z, XCtx.hzC z⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, XCtx.hzC z⟩ * ⟨z, XCtx.hzC z⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext C.hKz.sq
    rw [this, map_one]
  have hz1 : oddQuotMk z ⟨z, XCtx.hzC z⟩ ≠ 1 := fun h =>
    C.hKz.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h))
  have heq := (hU.unique _ hmem hz2).resolve_left hz1
  exact hnz (NDBH.eq_of_oddQuotMk_eq (C.involution_mem_centralizer hN hn) (XCtx.hzC z)
    hn.isCentralInvolution.sq C.hKz.sq heq.symm
    (fun o ho => NDBH.mul_comm_of_mem_involutionOddCore ho))

theorem commute_of_ne_involution (C : XCtx p f Ω z) (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2)
    {M N : Subgroup G} (hM : M ∈ tqMembers Ω z) (hMz : IsClassicalMember p f M z)
    (hN : N ∈ tqMembers Ω z) {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    ∀ (he : n ∈ Subgroup.centralizer ({z} : Set G)), ∀ q ∈ modOdd z (exactCore z M),
      oddQuotMk z ⟨n, he⟩ * q = q * oddQuotMk z ⟨n, he⟩ := by
  intro he q hq
  obtain ⟨jM, eM⟩ := NDBG.exists_range_eq C hall hM
  obtain ⟨jN, eN⟩ := NDBG.exists_range_eq C hall hN
  have hne : jN ≠ jM := by
    intro h
    apply zbar_not_mem C hN hn hnz
    rw [eN, h, ← eM]
    exact oddQuotMk_mem_modOdd (C.involution_mem_exactCore hM hMz) (XCtx.hzC z)
  obtain ⟨kN, hkN⟩ : oddQuotMk z ⟨n, he⟩ ∈ (C.psi jN).range := by
    rw [← eN]
    exact oddQuotMk_mem_modOdd (C.involution_mem_exactCore hN hn) he
  obtain ⟨kM, hkM⟩ : q ∈ (C.psi jM).range := by rw [← eM]; exact hq
  rw [← hkN, ← hkM]
  exact C.psi_commute hne kN kM

theorem generation_z (C : XCtx p f Ω z) (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2)
    {T N R R' : Subgroup G} {n u x y : G} (F : TwinA1Frame Ω C.K T N R R' z n u x y)
    (hN : N ∈ tqMembers Ω z) (hn : IsClassicalMember p f N n) (hnz : n ≠ z)
    (hTz : IsClassicalMember p f T z) :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, u, n} : Set G)) z := by
  have hBab := twinFrame_isElemAbelian C.hp C.hΩ F.data
  have hT : T ∈ tqMembers Ω z :=
    ⟨F.data.hK'.1, mem_trivialOnQuot_of_le_centralizer (le_centralizer_of_isClassicalMember hTz)⟩
  have hKY : C.K ≤ exactLayer Ω z :=
    TwinLiftCore.le_exactLayer_of_isClassicalMember C.hK C.K_cl
  have hTY : T ≤ exactLayer Ω z :=
    TwinLiftCore.le_exactLayer_of_isClassicalMember F.data.hK'.1 hTz
  have hxK : x ∈ C.K := F.syl.1 F.hx
  have hyT : y ∈ T := F.syl'.1 F.hy
  have hBY : Subgroup.closure ({z, u, n} : Set G) ≤ exactLayer Ω z := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl | rfl)
    · exact C.z_mem_exactLayer
    · rw [← F.hxy]
      exact mul_mem (hKY hxK) (hTY hyT)
    · exact exactCore_le_exactLayer hN (C.involution_mem_exactCore hN hn)
  have hTeq : exactCore z T = T :=
    exactCore_eq_self hTz.perfect (le_centralizer_of_isClassicalMember hTz)
  refine generation_of_pair C hall hBY (Subgroup.subset_closure (by simp))
    (fun w hw => Lemma52Proof.mul_self_eq_one_of_mem hBab hw) (comm_of_isElemAbelian hBab)
    C.K_tq hT (Subgroup.subset_closure (by simp)) hn.isCentralInvolution.ne_one hnz
    (commute_of_ne_involution C hall C.K_tq C.K_cl hN hn hnz)
    (commute_of_ne_involution C hall hT hTz hN hn hnz)
    (by rw [C.exactCore_K]; exact hxK) (by rw [hTeq]; exact hyT)
    (by rw [F.hxy]; exact Subgroup.subset_closure (by simp)) (by rw [F.hxy]; exact F.data.hu1)
    (by rw [F.hxy]; exact F.data.huz)

theorem generation_vertex (C : XCtx p f Ω z) (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2)
    {T N R R' : Subgroup G} {n u x y : G} (F : TwinA1Frame Ω C.K T N R R' z n u x y)
    (hTz : IsClassicalMember p f T z) {c g : G} (hgz : g * z * g⁻¹ = c)
    (hcB : c ∈ Subgroup.closure ({z, u, n} : Set G)) (hcz : c ≠ z) (huc : u ≠ c)
    (hKc : C.K ∈ tqMembers Ω c) (hTc : T ∈ tqMembers Ω c) (hxc : x ∈ exactCore c C.K)
    (hyc : y ∈ exactCore c T) (hBY : Subgroup.closure ({z, u, n} : Set G) ≤ exactLayer Ω c) :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, u, n} : Set G)) c := by
  set B := Subgroup.closure ({z, u, n} : Set G) with hB
  have hBab := twinFrame_isElemAbelian C.hp C.hΩ F.data
  have hΩc := C.hΩ.conjInvariant
  have hz' : g⁻¹ * c * g⁻¹⁻¹ = z := by rw [← hgz]; group
  have hmem : ∀ w : G, w ∈ conjSub g⁻¹ B ↔ g * w * g⁻¹ ∈ B := fun w => by
    rw [mem_conjSub_iff, inv_inv]
  have hBY' : conjSub g⁻¹ B ≤ exactLayer Ω z := by
    intro w hw
    have h1 : g * w * g⁻¹ ∈ exactLayer Ω c := hBY ((hmem w).mp hw)
    have h2 : w ∈ conjSub g⁻¹ (exactLayer Ω c) := by
      rw [mem_conjSub_iff, inv_inv]
      exact h1
    rw [← exactLayer_conj hΩc g⁻¹ c, hz'] at h2
    exact h2
  have hzB' : z ∈ conjSub g⁻¹ B := (hmem z).mpr (by rw [hgz]; exact hcB)
  have hsq' : ∀ w ∈ conjSub g⁻¹ B, w * w = 1 := by
    intro w hw
    have h := Lemma52Proof.mul_self_eq_one_of_mem hBab ((hmem w).mp hw)
    calc w * w = g⁻¹ * ((g * w * g⁻¹) * (g * w * g⁻¹)) * g := by group
      _ = 1 := by rw [h]; group
  have hcm' : ∀ v ∈ conjSub g⁻¹ B, ∀ w ∈ conjSub g⁻¹ B, v * w = w * v := by
    intro v hv w hw
    have h := comm_of_isElemAbelian hBab _ ((hmem v).mp hv) _ ((hmem w).mp hw)
    calc v * w = g⁻¹ * ((g * v * g⁻¹) * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h]
      _ = w * v := by group
  have hK' : conjSub g⁻¹ C.K ∈ tqMembers Ω z := by
    refine ⟨hΩc g⁻¹ C.K C.hK, ?_⟩
    have h := trivialOnQuot_conjSub hKc.2 g⁻¹
    rwa [hz'] at h
  have hT' : conjSub g⁻¹ T ∈ tqMembers Ω z := by
    refine ⟨hΩc g⁻¹ T F.data.hK'.1, ?_⟩
    have h := trivialOnQuot_conjSub hTc.2 g⁻¹
    rwa [hz'] at h
  have hKcl' : IsClassicalMember p f (conjSub g⁻¹ C.K) (g⁻¹ * z * g⁻¹⁻¹) := C.K_cl.conj g⁻¹
  have hTcl' : IsClassicalMember p f (conjSub g⁻¹ T) (g⁻¹ * z * g⁻¹⁻¹) := hTz.conj g⁻¹
  have haB' : g⁻¹ * z * g⁻¹⁻¹ ∈ conjSub g⁻¹ B := by
    refine (hmem _).mpr ?_
    have : g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z := by group
    rw [this]
    exact Subgroup.subset_closure (by simp)
  have ha1 : g⁻¹ * z * g⁻¹⁻¹ ≠ 1 := fun h => C.hKz.ne_one (by
    calc z = g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have haz : g⁻¹ * z * g⁻¹⁻¹ ≠ z := fun h => hcz (by
    rw [← hgz]
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ := by rw [h]
      _ = z := by group)
  have hcom : ∀ {M : Subgroup G}, M ∈ tqMembers Ω z →
      IsClassicalMember p f M (g⁻¹ * z * g⁻¹⁻¹) →
      ∀ (he : g⁻¹ * z * g⁻¹⁻¹ ∈ Subgroup.centralizer ({z} : Set G)),
        ∀ q ∈ modOdd z (exactCore z M),
          oddQuotMk z ⟨g⁻¹ * z * g⁻¹⁻¹, he⟩ * q = q * oddQuotMk z ⟨g⁻¹ * z * g⁻¹⁻¹, he⟩ :=
    fun hM hMa _ q hq => commute_of_isUniqueInvolution (C.isUniqueInvolution_modOdd hM hMa) q hq
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ exactCore z (conjSub g⁻¹ C.K) := by
    have := conj_mem_conjSub (n := g⁻¹) hxc
    rwa [← exactCore_conjSub, hz'] at this
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ exactCore z (conjSub g⁻¹ T) := by
    have := conj_mem_conjSub (n := g⁻¹) hyc
    rwa [← exactCore_conjSub, hz'] at this
  have hu' : g * (g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ = u := by
    rw [← F.hxy]
    group
  have hxyB' : g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) ∈ conjSub g⁻¹ B := by
    refine (hmem _).mpr ?_
    rw [hu']
    exact Subgroup.subset_closure (by simp)
  have hxy1 : g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) ≠ 1 := fun h => F.data.hu1 (by
    rw [← hu', h]
    group)
  have hxyz : g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) ≠ z := fun h => huc (by
    rw [← hu', h, hgz])
  have hgen' := generation_of_pair C hall hBY' hzB' hsq' hcm' hK' hT' haB' ha1 haz
    (hcom hK' hKcl') (hcom hT' hTcl') hx' hy' hxyB' hxy1 hxyz
  have hconj := centralizerGenerationStar_conj hΩc g hgen'
  rwa [conjSub_conjSub_inv, hgz] at hconj

end CFSG.ClassicalInvolution.NDB.NDBH3
