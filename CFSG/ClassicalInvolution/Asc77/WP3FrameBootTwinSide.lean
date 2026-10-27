module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinFrame
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.ModelFacts.Orth15SylowFrame
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Cases
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open scoped commutatorElement

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Conj

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem modOdd_conjSub_of_mem_centralizer {z c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    (K : Subgroup G) :
    modOdd z (conjSub c K) = conjSub (oddQuotMk z ⟨c, hc⟩) (modOdd z K) := by
  ext x
  rw [mem_modOdd_iff, mem_conjSub_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : c⁻¹ * (k : G) * c ∈ K := mem_conjSub_iff.mp hk
    have hkC : c⁻¹ * (k : G) * c ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem (inv_mem hc) k.2) hc
    refine (mem_modOdd_iff).mpr ⟨⟨c⁻¹ * (k : G) * c, hkC⟩, hk', ?_⟩
    have e : (⟨c⁻¹ * (k : G) * c, hkC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨c, hc⟩⁻¹ * k * ⟨c, hc⟩ := rfl
    rw [e, map_mul, map_mul, map_inv]
  · intro hx
    obtain ⟨k', hk', hk'x⟩ := (mem_modOdd_iff).mp hx
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hkC : c * (k' : G) * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem hc k'.2) (inv_mem hc)
    refine ⟨⟨c * (k' : G) * c⁻¹, hkC⟩, ?_, ?_⟩
    · rw [mem_conjSub_iff]
      have : c⁻¹ * (c * (k' : G) * c⁻¹) * c = k' := by group
      rw [this]
      exact hk'
    · have e : (⟨c * (k' : G) * c⁻¹, hkC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨c, hc⟩ * k' * ⟨c, hc⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hk'x]
      change oddQuotMk z ⟨c, hc⟩ * ((oddQuotMk z ⟨c, hc⟩)⁻¹ * oddQuotMk z x₀ *
        oddQuotMk z ⟨c, hc⟩) * (oddQuotMk z ⟨c, hc⟩)⁻¹ = oddQuotMk z x₀
      group

end Conj

section GenCore

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtxCore p f Ω z} (L : TwinLiftCore C)

namespace TwinLiftCore

theorem comm_gen (S : C.Spec) :
    ∀ a ∈ ({z, L.u, L.t} : Set G), ∀ b ∈ ({z, L.u, L.t} : Set G), a * b = b * a :=
  (L.frameData S).comm_gen C.hp C.hΩ

theorem sq_gen : ∀ a ∈ ({z, L.u, L.t} : Set G), a * a = 1 := by
  rintro a (rfl | rfl | rfl)
  · exact L.hK₁z.sq
  · exact L.hu2
  · exact (isCentralInvolution_of_isClassicalMember L.hJt).sq

theorem mem_modOdd_of_commutes (S : C.Spec) {e : G}
    (heB : e ∈ Subgroup.closure ({z, L.u, L.t} : Set G)) (he1 : e ≠ 1) (hez : e ≠ z)
    {q : OddQuot z} (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, L.u, L.t} : Set G)),
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) := by
  set B := Subgroup.closure ({z, L.u, L.t} : Set G) with hB
  have hcg := L.comm_gen S
  have hsq := L.sq_gen
  have hzB : z ∈ B := L.z_mem_B
  have hz1 : z ≠ 1 := C.hKz.ne_one
  have hcB := ChainFrame.commutes_closure hcg
  have hsqB : ∀ x ∈ B, x * x = 1 := ChainFrame.sq_closure hsq hcg
  have hesq : e * e = 1 := hsqB e heB
  have hze : z * e = e * z := hcB z hzB e heB
  set F : Subgroup G := Subgroup.closure ({z, e} : Set G) with hF
  have hFB : F ≤ B := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzB
    · exact heB
  have hcard : Nat.card F = 4 :=
    card_closure_pair_eq_four C.hKz.sq hesq hz1 he1 (fun h => hez h.symm) hze
  have hFE : F ∈ signalizerFunctorEk 2 2 B := ⟨hFB, by rw [hcard]; norm_num⟩
  have hFY : F ≤ exactLayer Ω z := hFB.trans L.B_le_exactLayer
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => hsqB x (hFB hx)
  have hcent : ∀ (x : G) (_ : x ∈ F) (hC : x ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨x, hC⟩ * q = q * oddQuotMk z ⟨x, hC⟩ := by
    refine ChainFrame.commutes_of_closure (oddQuotMk z) q (S := ({z, e} : Set G)) ?_ ?_
    · rintro s (rfl | rfl)
      · exact XCtx.hzC _
      · exact L.B_le_centralizer heB
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central (XCtx.hzC _) q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (a := z) hF2 hFY hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) :=
    le_iSup₂ (f := fun F (_ : F ∈ signalizerFunctorEk 2 2 B) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

theorem generation_z (S : C.Spec) :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, L.u, L.t} : Set G)) z := by
  classical
  set B := Subgroup.closure ({z, L.u, L.t} : Set G) with hB
  set H : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 B,
    (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) with hH
  have hHY : H ≤ exactLayer Ω z := iSup₂_le fun F _ => inf_le_right
  have hcomm : ∀ {i j : Fin C.D.card}, i ≠ j → ∀ x ∈ (C.psi i).range, ∀ y ∈ (C.psi j).range,
      x * y = y * x := by
    rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact C.psi_commute hij a b
  have ht1 : L.t ≠ 1 := (isCentralInvolution_of_isClassicalMember L.hJt).ne_one
  have hψ : ∀ (j : Fin C.D.card) (k : (compModel C.D j).K), C.psi j k ∈ modOdd z H := by
    intro j k
    have hthrough : j ≠ C.i₁ → C.psi j k ∈ modOdd z H := by
      intro hj
      refine L.mem_modOdd_of_commutes S L.t_mem_B ht1 L.t_ne_z (C.psi_mem_memberJoin j k)
        fun he => ?_
      exact hcomm hj.symm _ L.tbar_mem _ ⟨k, rfl⟩
    by_cases hj : j = C.i₁
    · subst hj
      exact L.mem_modOdd_of_commutes S L.u_mem_B L.hu1 L.huz (C.psi_mem_memberJoin _ k)
        fun he => L.hu_comm _ ⟨k, rfl⟩
    · exact hthrough hj
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

end TwinLiftCore

end GenCore

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtx p f Ω z} (L : TwinLift C)

namespace TwinLift

theorem comm_gen (S : C.Spec) :
    ∀ a ∈ ({z, L.u, L.t} : Set G), ∀ b ∈ ({z, L.u, L.t} : Set G), a * b = b * a :=
  L.toCore.comm_gen S.toCore

theorem sq_gen : ∀ a ∈ ({z, L.u, L.t} : Set G), a * a = 1 := L.toCore.sq_gen

theorem mem_modOdd_of_commutes (S : C.Spec) {e : G}
    (heB : e ∈ Subgroup.closure ({z, L.u, L.t} : Set G)) (he1 : e ≠ 1) (hez : e ≠ z)
    {q : OddQuot z} (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, L.u, L.t} : Set G)),
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) :=
  L.toCore.mem_modOdd_of_commutes S.toCore heB he1 hez hq hcomm

theorem generation_z (S : C.Spec) :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, L.u, L.t} : Set G)) z :=
  L.toCore.generation_z S.toCore

end TwinLift

end Gen

section BigLink

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

@[expose] def TwinShapeCtxCore.BigLink (C : TwinShapeCtxCore p f Ω z) : Prop :=
  ∀ R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D,
    ∀ R' ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D,
      ∀ x y : OddQuot z, IsUniqueInvolution (R.map (C.psi C.i₁)) x →
        IsUniqueInvolution (R'.map (C.psi C.i₁)) y →
          ∃ g : (compModel C.D C.i₁).K, x = C.psi C.i₁ g * y * (C.psi C.i₁ g)⁻¹

theorem TwinShapeCtxCore.bigLink_of_listed (C : TwinShapeCtxCore p f Ω z)
    (hL : ListedTwin (C.D.tag C.i₁) (C.D.rank C.i₁)) : C.BigLink := by
  intro R hR R' hR' x y hx hy
  have hG2D4 := C.listed_tag_ne hL
  obtain ⟨g, hg⟩ := C.single C.i₁ hG2D4.1 hG2D4.2 R' hR' R hR
  have hconj := hy.conj (C.psi C.i₁ g)
  rw [conjSub_map, ← hg] at hconj
  exact ⟨g, hx.eq hconj⟩

omit [Finite G] in
theorem center_modelUniv_G2_eq_bot {t : LTag} (ht : t = .G2) (n e : ℕ) :
    Subgroup.center (modelUniv t n p e Fact.out).K = ⊥ := by
  subst ht
  show Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField p e)) = ⊥
  exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

theorem TwinShapeCtxCore.bigLink (C : TwinShapeCtxCore p f Ω z) : C.BigLink := by
  rcases C.listed with hL | hG2
  · exact C.bigLink_of_listed hL
  intro R _ R' _ x y hx hy
  obtain ⟨x₀, -, hx₀⟩ := hx.mem
  obtain ⟨y₀, -, hy₀⟩ := hy.mem
  have hZ := center_modelUniv_G2_eq_bot (p := p) hG2 (C.D.rank C.i₁) (C.D.exp C.i₁)
  have hinj : Function.Injective (C.psi C.i₁) :=
    (MonoidHom.ker_eq_bot_iff _).1 (le_bot_iff.1 ((C.psi_ker C.i₁).trans hZ.le))
  have hx2 : x₀ * x₀ = 1 := hinj (by rw [map_mul, hx₀, hx.sq, map_one])
  have hy2 : y₀ * y₀ = 1 := hinj (by rw [map_mul, hy₀, hy.sq, map_one])
  have hx1 : x₀ ≠ 1 := fun h => hx.ne_one (by rw [← hx₀, h, map_one])
  have hy1 : y₀ ≠ 1 := fun h => hy.ne_one (by rw [← hy₀, h, map_one])
  obtain ⟨g, hg⟩ := g2_model_involutions_conj hG2 C.hp (C.D.admissible C.i₁) hy2 hx2 hy1 hx1
  refine ⟨g, ?_⟩
  rw [← hx₀, ← hy₀, ← hg, map_mul, map_mul, map_inv]

end BigLink

section LinkCore

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtxCore p f Ω z} (L : TwinLiftCore C)

namespace TwinLiftCore

theorem zbar_mem₀ (S : C.Spec) : oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi C.i₀).range := by
  rw [← S.hK₀]
  exact oddQuotMk_mem_modOdd (C.involution_mem_exactCore C.K_tq C.K_cl) (XCtx.hzC z)

theorem link_z (S : C.Spec) (hB : C.BigLink) {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) :
    ∃ h ∈ exactLayer Ω z, w = h * z * h⁻¹ ∨ w = h * L.t * h⁻¹ := by
  have hzC := XCtx.hzC z
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hN
  by_cases hj : j = C.i₁
  swap
  · have hmod' : modOdd z (exactCore z N) = (C.psi j).range := by
      rw [← hmod, C.fund_eq_top j (C.A1_of_ne hj) hR, Subgroup.map_top]
    exact ⟨1, one_mem _, Or.inl (by
      rw [TwinShapeCtxCore.classical_of_range hN hw hmod' (C.zbar_mem_of_ne S hj)]; group)⟩
  subst hj
  · have hUw := C.isUniqueInvolution_modOdd hN hw
    have hUt := C.isUniqueInvolution_modOdd L.hJ L.hJt
    rw [← hmod] at hUw
    rw [L.hJimg] at hUt
    obtain ⟨g, heq⟩ := hB R hR L.R₁ L.hR₁ _ _ hUw hUt
    obtain ⟨y, hy, hyψ⟩ := C.exists_lift_psi C.i₁ g
    have hyC := exactLayer_le_centralizer Ω z hy
    have hconjC : y * L.t * y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem hyC L.ht) (inv_mem hyC)
    have hconjY : y * L.t * y⁻¹ ∈ exactLayer Ω z :=
      mul_mem (mul_mem hy L.t_mem_exactLayer) (inv_mem hy)
    have hbar : oddQuotMk z ⟨y * L.t * y⁻¹, hconjC⟩ =
        C.psi C.i₁ g * oddQuotMk z ⟨L.t, L.ht⟩ * (C.psi C.i₁ g)⁻¹ := by
      have : (⟨y * L.t * y⁻¹, hconjC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨y, hyC⟩ * ⟨L.t, L.ht⟩ * ⟨y, hyC⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hyψ]
    have hsq : (y * L.t * y⁻¹) * (y * L.t * y⁻¹) = 1 := by
      have e : (y * L.t * y⁻¹) * (y * L.t * y⁻¹) = y * (L.t * L.t) * y⁻¹ := by group
      rw [e, (isCentralInvolution_of_isClassicalMember L.hJt).sq]
      group
    have hwY : w ∈ exactLayer Ω z :=
      exactCore_le_exactLayer hN (C.involution_mem_exactCore hN hw)
    obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hconjY
      (isCentralInvolution_of_isClassicalMember hw).sq hsq (heq.trans hbar.symm)
    refine ⟨o * y, mul_mem (oddCoreIn_le _ ho) hy, Or.inr ?_⟩
    rw [hwo]
    group

theorem t_sq : L.t * L.t = 1 := (isCentralInvolution_of_isClassicalMember L.hJt).sq

theorem exists_swap_zt (S : C.Spec) (hB : C.BigLink)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M) :
    ∃ s : G, s * z * s⁻¹ = L.t ∧ s * L.t * s⁻¹ = z := by
  have hKcl : IsClassicalMember p f L.K₁ z := isClassicalMember_of_twin C.hΩ L.hK₁ L.hK₁z
  obtain ⟨g₀, hg₀⟩ := htrans L.J L.hJ.1
  have hgz : g₀ * z * g₀⁻¹ = L.t := by
    have h1 : IsUniqueInvolution (conjSub g₀ L.K₁) (g₀ * z * g₀⁻¹) :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq (hKcl.conj g₀)
    rw [hg₀] at h1
    exact h1.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)
  have htK : L.t ∈ trivialOnQuot L.K₁ := (L.frameData S).tq_t_K C.hp C.hq C.hΩ
  have hK''tq : conjSub g₀⁻¹ L.K₁ ∈ tqMembers Ω z := by
    refine ⟨C.hΩ.conjInvariant g₀⁻¹ L.K₁ L.hK₁, ?_⟩
    have h := trivialOnQuot_conjSub htK g₀⁻¹
    have e : g₀⁻¹ * L.t * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
    rwa [e] at h
  obtain ⟨h, hh, hcase⟩ := L.link_z S hB hK''tq (hKcl.conj g₀⁻¹)
  have hhz : h * z * h⁻¹ = z :=
    conj_eq_of_mem_centralizer_singleton (exactLayer_le_centralizer Ω z hh)
  rcases hcase with hc | hc
  · exfalso
    have h2 : g₀⁻¹ * z * g₀⁻¹⁻¹ = z := hc.trans hhz
    apply L.t_ne_z
    rw [← hgz]
    calc g₀ * z * g₀⁻¹ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [h2]
      _ = z := by group
  · refine ⟨g₀ * h, ?_, ?_⟩
    · calc g₀ * h * z * (g₀ * h)⁻¹ = g₀ * (h * z * h⁻¹) * g₀⁻¹ := by group
        _ = g₀ * z * g₀⁻¹ := by rw [hhz]
        _ = L.t := hgz
    · calc g₀ * h * L.t * (g₀ * h)⁻¹ = g₀ * (h * L.t * h⁻¹) * g₀⁻¹ := by group
        _ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [hc]
        _ = z := by group

theorem link_z_star (S : C.Spec) (hB : C.BigLink) :
    InvolutionLinkStar p f Ω (Subgroup.closure ({z, L.u, L.t} : Set G))
      ({L.K₁, L.J} : Set (Subgroup G)) z := by
  intro N hN w hw hdisj
  have hKcl : IsClassicalMember p f L.K₁ z := isClassicalMember_of_twin C.hΩ L.hK₁ L.hK₁z
  have key : ActsTrivOnQuot N z ∨ w = z := by
    rcases hdisj with h | ⟨L', hL', hL'z, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq C.hp C.hq C.hΩ hN hL' hw hL'z hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwz
  · have hNtq : N ∈ tqMembers Ω z := ⟨hN, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩
    obtain ⟨h, hh, hcase⟩ := L.link_z S hB hNtq hw
    rcases hcase with hc | hc
    · exact ⟨L.K₁, Set.mem_insert _ _, z, L.z_mem_B, hKcl, h, hh, hc⟩
    · exact ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, h, hh, hc⟩
  · exact ⟨L.K₁, Set.mem_insert _ _, z, L.z_mem_B, hKcl, 1, one_mem _, by rw [hwz]; group⟩

theorem link_t_star (S : C.Spec) (hB : C.BigLink) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M) :
    InvolutionLinkStar p f Ω (Subgroup.closure ({z, L.u, L.t} : Set G))
      ({L.K₁, L.J} : Set (Subgroup G)) L.t := by
  obtain ⟨s, hsz, hst⟩ := L.exists_swap_zt S hB htrans
  have hKcl : IsClassicalMember p f L.K₁ z := isClassicalMember_of_twin C.hΩ L.hK₁ L.hK₁z
  have hYt : exactLayer Ω L.t = conjSub s (exactLayer Ω z) := by
    rw [← hsz]
    exact exactLayer_conj C.hΩ.conjInvariant s z
  have hstz : s⁻¹ * L.t * s = z := by rw [← hsz]; group
  intro N hN w hw hdisj
  have key : ActsTrivOnQuot N L.t ∨ w = L.t := by
    rcases hdisj with h | ⟨L', hL', hL'z, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq C.hp C.hq C.hΩ hN hL' hw hL'z hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwt
  · have hN'tq : conjSub s⁻¹ N ∈ tqMembers Ω z := by
      refine ⟨C.hΩ.conjInvariant s⁻¹ N hN, ?_⟩
      have h := trivialOnQuot_conjSub (mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq) s⁻¹
      have e : s⁻¹ * L.t * s⁻¹⁻¹ = z := by rw [inv_inv]; exact hstz
      rwa [e] at h
    obtain ⟨h, hh, hcase⟩ := L.link_z S hB hN'tq (hw.conj s⁻¹)
    have hh' : s * h * s⁻¹ ∈ exactLayer Ω L.t := by
      rw [hYt, mem_conjSub_iff]
      have e : s⁻¹ * (s * h * s⁻¹) * s = h := by group
      rw [e]
      exact hh
    have hwe : w = s * (s⁻¹ * w * s⁻¹⁻¹) * s⁻¹ := by group
    rcases hcase with hc | hc
    · refine ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, s * h * s⁻¹, hh', ?_⟩
      rw [hwe, hc]
      calc s * (h * z * h⁻¹) * s⁻¹ = (s * h * s⁻¹) * (s * z * s⁻¹) * (s * h * s⁻¹)⁻¹ := by group
        _ = (s * h * s⁻¹) * L.t * (s * h * s⁻¹)⁻¹ := by rw [hsz]
    · refine ⟨L.K₁, Set.mem_insert _ _, z, L.z_mem_B, hKcl, s * h * s⁻¹, hh', ?_⟩
      rw [hwe, hc]
      calc s * (h * L.t * h⁻¹) * s⁻¹ =
          (s * h * s⁻¹) * (s * L.t * s⁻¹) * (s * h * s⁻¹)⁻¹ := by group
        _ = (s * h * s⁻¹) * z * (s * h * s⁻¹)⁻¹ := by rw [hst]
  · refine ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, 1, one_mem _, ?_⟩
    rw [hwt]
    group

theorem A1_cover_of_ne (S : C.Spec) (hB : C.BigLink) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M)
    {j : Fin C.D.card} (hj : j ≠ C.i₁) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.u, L.t} : Set G)) ∧
      modOdd z (exactCore z (conjSub g L.J)) = (C.psi j).range := by
  obtain ⟨s, hsz, -⟩ := L.exists_swap_zt S hB htrans
  have hsz' : s⁻¹ * L.t * s⁻¹⁻¹ = z := by
    rw [inv_inv, ← hsz]
    group
  have hM₁cl : IsClassicalMember p f (conjSub s⁻¹ L.J) z := by
    have := L.hJt.conj s⁻¹
    rwa [hsz'] at this
  obtain ⟨M, hMΩ, hMz, hMimg⟩ := C.exists_member_of_ne S hj
  obtain ⟨g₁, hg₁⟩ := htrans _ (C.hΩ.conjInvariant s⁻¹ L.J L.hJ.1)
  obtain ⟨g₂, hg₂⟩ := htrans M hMΩ
  have hcM : conjSub (g₂ * g₁⁻¹) (conjSub s⁻¹ L.J) = M := by
    rw [← hg₁, conjSub_mul, conjSub_inv_conjSub, hg₂]
  have hcz : g₂ * g₁⁻¹ * z * (g₂ * g₁⁻¹)⁻¹ = z := by
    have h1 := hM₁cl.conj (g₂ * g₁⁻¹)
    rw [hcM] at h1
    exact ((ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hMz).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq h1)).symm
  have hc' : (g₂ * g₁⁻¹)⁻¹ * z * (g₂ * g₁⁻¹)⁻¹⁻¹ = z := by
    calc (g₂ * g₁⁻¹)⁻¹ * z * (g₂ * g₁⁻¹)⁻¹⁻¹
        = (g₂ * g₁⁻¹)⁻¹ * (g₂ * g₁⁻¹ * z * (g₂ * g₁⁻¹)⁻¹) * (g₂ * g₁⁻¹)⁻¹⁻¹ := by rw [hcz]
      _ = z := by group
  have hMeq : exactCore z M = M :=
    exactCore_eq_self hMz.perfect (le_centralizer_of_isClassicalMember hMz)
  refine ⟨g₂ * g₁⁻¹ * s⁻¹, ?_, ?_⟩
  · rw [mem_conjSub_iff]
    have e : (g₂ * g₁⁻¹ * s⁻¹)⁻¹ * z * (g₂ * g₁⁻¹ * s⁻¹) =
        s * ((g₂ * g₁⁻¹)⁻¹ * z * (g₂ * g₁⁻¹)⁻¹⁻¹) * s⁻¹ := by group
    rw [e, hc', hsz]
    exact L.t_mem_B
  · rw [conjSub_mul, hcM, hMeq]
    exact hMimg

theorem A1_cover (S : C.Spec) (hB : C.BigLink) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M)
    {j : Fin C.D.card} (hj : j = C.i₀ ∨ j = C.i₂) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.u, L.t} : Set G)) ∧
      modOdd z (exactCore z (conjSub g L.J)) = (C.psi j).range := by
  refine L.A1_cover_of_ne S hB htrans ?_
  rcases hj with rfl | rfl
  · exact C.ne₀₁
  · exact C.ne₁₂.symm

theorem cover_z (S : C.Spec) (hB : C.BigLink) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M)
    {N : Subgroup G} (hN : N ∈ centMembers Ω z) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.u, L.t} : Set G)) ∧
      InCommonComponent z N (exactCore z (conjSub g L.J)) := by
  classical
  have hNtq : N ∈ tqMembers Ω z := centMembers_subset_tqMembers hN
  have hNeq : exactCore z N = N := exactCore_eq_self_of_mem_centMembers C.hΩ.classical hN
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hNtq
  rw [hNeq] at hmod
  by_cases hj : j = C.i₁
  · subst hj
    refine ⟨1, ?_, (C.psi C.i₁).range, C.isComponent_range C.i₁, ?_, ?_⟩
    · rw [mem_conjSub_iff]
      simpa using L.z_mem_B
    · rw [← hmod]
      exact Subgroup.map_le_range _ _
    · rw [conjSub_one, L.hJimg]
      exact Subgroup.map_le_range _ _
  · obtain ⟨g, hg, himg⟩ := L.A1_cover_of_ne S hB htrans hj
    refine ⟨g, hg, (C.psi j).range, C.isComponent_range j, ?_, himg.le⟩
    rw [← hmod, C.fund_eq_top j (C.A1_of_ne hj) hR, Subgroup.map_top]

end TwinLiftCore

end LinkCore

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : TwinShapeCtx p f Ω z} (L : TwinLift C)

namespace TwinLift

theorem zbar_mem₀ (S : C.Spec) : oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi C.i₀).range :=
  TwinLiftCore.zbar_mem₀ S.toCore

theorem link_z (S : C.Spec) {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) :
    ∃ h ∈ exactLayer Ω z, w = h * z * h⁻¹ ∨ w = h * L.t * h⁻¹ :=
  L.toCore.link_z S.toCore (C.toCore.bigLink_of_listed C.listed) hN hw

theorem t_sq : L.t * L.t = 1 := L.toCore.t_sq

theorem exists_swap_zt (S : C.Spec) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M) :
    ∃ s : G, s * z * s⁻¹ = L.t ∧ s * L.t * s⁻¹ = z :=
  L.toCore.exists_swap_zt S.toCore (C.toCore.bigLink_of_listed C.listed) htrans

theorem link_z_star (S : C.Spec) :
    InvolutionLinkStar p f Ω (Subgroup.closure ({z, L.u, L.t} : Set G))
      ({L.K₁, L.J} : Set (Subgroup G)) z :=
  L.toCore.link_z_star S.toCore (C.toCore.bigLink_of_listed C.listed)

theorem link_t_star (S : C.Spec) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M) :
    InvolutionLinkStar p f Ω (Subgroup.closure ({z, L.u, L.t} : Set G))
      ({L.K₁, L.J} : Set (Subgroup G)) L.t :=
  L.toCore.link_t_star S.toCore (C.toCore.bigLink_of_listed C.listed) htrans

theorem A1_cover_of_ne (S : C.Spec) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M)
    {j : Fin C.D.card} (hj : j ≠ C.i₁) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.u, L.t} : Set G)) ∧
      modOdd z (exactCore z (conjSub g L.J)) = (C.psi j).range :=
  L.toCore.A1_cover_of_ne S.toCore (C.toCore.bigLink_of_listed C.listed) htrans hj

theorem A1_cover (S : C.Spec) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M)
    {j : Fin C.D.card} (hj : j = C.i₀ ∨ j = C.i₂) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.u, L.t} : Set G)) ∧
      modOdd z (exactCore z (conjSub g L.J)) = (C.psi j).range :=
  L.toCore.A1_cover S.toCore (C.toCore.bigLink_of_listed C.listed) htrans hj

theorem cover_z (S : C.Spec) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g L.K₁ = M) {N : Subgroup G}
    (hN : N ∈ centMembers Ω z) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.u, L.t} : Set G)) ∧
      InCommonComponent z N (exactCore z (conjSub g L.J)) :=
  L.toCore.cover_z S.toCore (C.toCore.bigLink_of_listed C.listed) htrans hN

end TwinLift

end Link

end CFSG.ClassicalInvolution.Asc77
