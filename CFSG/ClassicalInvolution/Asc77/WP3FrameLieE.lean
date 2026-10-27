module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieD
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3LayerConj

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace ChainFrame

theorem commutes_of_closure {G M : Type*} [Group G] [Group M] {Cz : Subgroup G} (φ : ↥Cz →* M)
    (q : M) {S : Set G} (hS : ∀ s ∈ S, s ∈ Cz)
    (h : ∀ s ∈ S, ∀ hs : s ∈ Cz, φ ⟨s, hs⟩ * q = q * φ ⟨s, hs⟩) :
    ∀ e ∈ Subgroup.closure S, ∀ he : e ∈ Cz, φ ⟨e, he⟩ * q = q * φ ⟨e, he⟩ := by
  have hP : Subgroup.closure S ≤
      ((Subgroup.centralizer ({q} : Set M)).comap φ).map Cz.subtype := by
    rw [Subgroup.closure_le]
    intro s hs
    refine ⟨⟨s, hS s hs⟩, ?_, rfl⟩
    show φ ⟨s, hS s hs⟩ ∈ Subgroup.centralizer ({q} : Set M)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h s hs (hS s hs)
  intro e he heC
  obtain ⟨x, hx, hxe⟩ := hP he
  have hxe' : x = ⟨e, heC⟩ := Subtype.ext hxe
  subst hxe'
  exact Subgroup.mem_centralizer_singleton_iff.mp hx

end ChainFrame

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : ChainCtx p f Ω z} (L : ChainLift C)

namespace ChainLift

theorem z'_mem_exactLayer : L.z' ∈ exactLayer Ω z :=
  exactCore_le_exactLayer L.hK' (C.involution_mem_exactCore L.hK' L.hK'z')

theorem B_le_exactLayer :
    Subgroup.closure ({z, L.t, L.z'} : Set G) ≤ exactLayer Ω z := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact C.z_mem_exactLayer
  · exact L.t_mem_exactLayer
  · exact L.z'_mem_exactLayer

theorem mem_modOdd_of_commutes {e : G}
    (heB : e ∈ Subgroup.closure ({z, L.t, L.z'} : Set G)) (he1 : e ≠ 1) (hez : e ≠ z)
    {q : OddQuot z} (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, L.t, L.z'} : Set G)),
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) := by
  set B := Subgroup.closure ({z, L.t, L.z'} : Set G) with hB
  have hfd := L.frameData
  have hcg := hfd.comm_gen C.hp C.hΩ
  have hsq := hfd.sq_gen
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
      · exact ChainLift.hzC
      · exact L.B_le_centralizer heB
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central ChainLift.hzC q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (a := z) hF2 hFY hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) :=
    le_iSup₂ (f := fun F (_ : F ∈ signalizerFunctorEk 2 2 B) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

end ChainLift

end Gen

section KComp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

namespace ChainCtx

include C

theorem fund_eq_top₀ {R : Subgroup (compModel C.D C.i₀).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag C.i₀) (compModel C.D C.i₀).D) : R = ⊤ := by
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), t = .PSL → n = 2 →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e →
      ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R = ⊤ := by
    intro t n e ht hn hadm R hR
    subst ht hn
    exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e Fact.out
      hadm R hR
  exact key (C.D.tag C.i₀) (C.D.rank C.i₀) (C.D.exp C.i₀) C.tag₀ C.rank₀ (C.D.admissible C.i₀) R hR

theorem modOdd_K_eq_range : modOdd z (exactCore z C.K) = (C.psi C.i₀).range := by
  obtain ⟨R_K, hR_K, hmodK⟩ := C.K_comp
  rw [hmodK, C.fund_eq_top₀ hR_K, Subgroup.map_top]

theorem K_quasisimple : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z C.K)) := by
  obtain ⟨R_K, hR_K, hmodK⟩ := C.K_comp
  rw [hmodK]
  exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₀)
    (fundQuasisimple_core C.hp (C.D.isFundTag C.i₀) (C.D.admissible C.i₀)
      (C.four_le C.i₀ (Or.inl C.tag₀)) R_K hR_K)

theorem centralizes_K {b : G} (hb : b ∈ trivialOnQuot C.K)
    (hbC : b ∈ Subgroup.centralizer ({z} : Set G)) :
    ∀ y ∈ (C.psi C.i₀).range, oddQuotMk z ⟨b, hbC⟩ * y = y * oddQuotMk z ⟨b, hbC⟩ := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  rw [← C.modOdd_K_eq_range]
  exact oddQuotMk_centralizes_modOdd_exactCore hKcl C.hc2 C.hKtq hb hbC C.K_quasisimple

theorem psi_mem_memberJoin (j : Fin C.D.card) (k : (compModel C.D j).K) :
    C.psi j k ∈ memberJoin (exactFamily Ω z) z := by
  rw [← range_sectionQuotientHom C.hs.normalizes]
  exact ⟨C.D.hom j k, rfl⟩

theorem psi_commute {i j : Fin C.D.card} (hij : i ≠ j) (x : (compModel C.D i).K)
    (y : (compModel C.D j).K) : C.psi i x * C.psi j y = C.psi j y * C.psi i x := by
  have h1 := map_mul (sectionQuotientHom C.hs.normalizes) (C.D.hom i x) (C.D.hom j y)
  have h2 := map_mul (sectionQuotientHom C.hs.normalizes) (C.D.hom j y) (C.D.hom i x)
  have h3 := congrArg (sectionQuotientHom C.hs.normalizes) (C.D.commute i j hij x y)
  exact h1.symm.trans (h3.trans h2)

theorem conj_psi_range (j : Fin C.D.card) {y : OddQuot z}
    (hy : y ∈ memberJoin (exactFamily Ω z) z) :
    ∀ n ∈ (C.psi j).range, y * n * y⁻¹ ∈ (C.psi j).range := by
  rw [← range_sectionQuotientHom C.hs.normalizes] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : x ∈ ⨆ i, (C.D.hom i).range := by
    rw [C.D.generate]
    exact Subgroup.mem_top x
  induction hx using Subgroup.iSup_induction' with
  | hp k y hy =>
    intro n hn
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hn
    have h2 : sectionQuotientHom C.hs.normalizes (C.D.hom k a) = C.psi k a := rfl
    rw [h2]
    by_cases hkj : k = j
    · subst hkj
      refine ⟨a * b * a⁻¹, ?_⟩
      simp
    · rw [C.psi_commute hkj a b, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨b, rfl⟩
  | h1 =>
    intro n hn
    rw [map_one, one_mul, inv_one, mul_one]
    exact hn
  | hmul a b _ _ ha hb =>
    intro n hn
    rw [map_mul]
    have e : ∀ u v : OddQuot z, u * v * n * (u * v)⁻¹ = u * (v * n * v⁻¹) * u⁻¹ :=
      fun u v => by group
    rw [e]
    exact ha _ (hb n hn)

theorem isComponentOf_range (j : Fin C.D.card) : IsComponentOf (C.psi j).range ⊤ := by
  have hJ : (memberJoin (exactFamily Ω z) z).Normal :=
    memberJoin_normal_of_normalizes C.hs.normalizes
  have hle : (C.psi j).range ≤ memberJoin (exactFamily Ω z) z := by
    rintro _ ⟨k, rfl⟩
    exact C.psi_mem_memberJoin j k
  refine ⟨le_top, ?_, ?_⟩
  · refine IsSubnormal.step hle ?_ ?_
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using C.conj_psi_range j g.2 _ hn
    · exact isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  · have hK : CFSG.Open.IsQuasisimple
        (modelUniv (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out).K :=
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (C.D.isFundTag j)
        (C.D.admissible j)).1
    have hq : CFSG.Open.IsQuasisimple ↥((⊤ : Subgroup (compModel C.D j).K).map (C.psi j)) :=
      isQuasisimple_map_of_ker_le_center _ (C.psi_ker j)
        (Components.quasisimple_of_equiv Subgroup.topEquiv hK)
    rwa [Subgroup.map_top] at hq

theorem isComponent_range (j : Fin C.D.card) : CFSG.IsComponent (C.psi j).range :=
  (CFSG.isComponent_iff_open _).mpr (C.isComponentOf_range j)

end ChainCtx

end KComp

section Generation

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : ChainCtx p f Ω z} (L : ChainLift C)

namespace ChainLift

theorem tz'_ne_one : L.t * L.z' ≠ 1 := by
  intro h
  apply L.z'_ne_t
  have h1 : L.z' = L.t⁻¹ := by
    have := congrArg (fun x => L.t⁻¹ * x) h
    simpa using this
  rw [h1]
  exact inv_eq_of_mul_eq_one_right L.t_sq

theorem tz'_ne_z : L.t * L.z' ≠ z := by
  intro h
  apply L.frameData.z'_ne_zt C.hp C.hq C.hΩ
  have h1 : L.z' = L.t⁻¹ * z := by
    have := congrArg (fun x => L.t⁻¹ * x) h
    simpa using this
  rw [h1, inv_eq_of_mul_eq_one_right L.t_sq]
  exact (L.frameData.comm_zt C.hp C.hΩ).symm

theorem generation_z :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, L.t, L.z'} : Set G)) z := by
  classical
  set B := Subgroup.closure ({z, L.t, L.z'} : Set G) with hB
  set H : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 B,
    (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) with hH
  have hfd := L.frameData
  have hHY : H ≤ exactLayer Ω z := iSup₂_le fun F _ => inf_le_right
  have hψ : ∀ (j : Fin C.D.card) (k : (compModel C.D j).K), C.psi j k ∈ modOdd z H := by
    intro j k
    rcases C.eq_i₀_or_i₁ j with rfl | rfl
    · have hk : C.psi C.i₀ k ∈ (C.psi C.i₀).range := ⟨k, rfl⟩
      exact L.mem_modOdd_of_commutes L.t_mem_B hfd.ht.ne_one L.t_ne_z
        (C.psi_mem_memberJoin C.i₀ k) fun he =>
        (C.centralizes_K (L.frameData.tq_t C.hp C.hq C.hΩ) he) _ hk
    · have hP : (⊤ : Subgroup (compModel C.D C.i₁).K) ≤
          (modOdd z H).comap (C.psi C.i₁) := by
        refine le_trans L.hd.gen (iSup₂_le fun R hR => iSup_le fun hcond => ?_)
        intro r hr
        show C.psi C.i₁ r ∈ modOdd z H
        have hq := C.psi_mem_memberJoin C.i₁ r
        rcases hcond with hc | hc | hc
        · have hr' := Subgroup.mem_centralizer_singleton_iff.mp (hc hr)
          refine L.mem_modOdd_of_commutes L.t_mem_B hfd.ht.ne_one L.t_ne_z hq fun he => ?_
          rw [show oddQuotMk z ⟨L.t, he⟩ = C.psi C.i₁ L.τ₁ from L.htbar, ← map_mul, ← map_mul,
            ← hr']
        · have hr' := Subgroup.mem_centralizer_singleton_iff.mp (hc hr)
          refine L.mem_modOdd_of_commutes L.z'_mem_B hfd.hz'.ne_one L.z'_ne_z hq fun he => ?_
          rw [show oddQuotMk z ⟨L.z', he⟩ = C.psi C.i₁ L.τ₂ from L.hz'bar, ← map_mul, ← map_mul,
            ← hr']
        · have hr' := Subgroup.mem_centralizer_singleton_iff.mp (hc hr)
          refine L.mem_modOdd_of_commutes (Subgroup.mul_mem _ L.t_mem_B L.z'_mem_B) L.tz'_ne_one
            L.tz'_ne_z hq fun he => ?_
          have e : oddQuotMk z ⟨L.t * L.z', he⟩ = C.psi C.i₁ (L.τ₁ * L.τ₂) := by
            have : (⟨L.t * L.z', he⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
                ⟨L.t, L.ht⟩ * ⟨L.z', L.hz'⟩ := rfl
            rw [this, map_mul, L.htbar, L.hz'bar, map_mul]
          rw [e, ← map_mul, ← map_mul, ← hr']
      exact hP (Subgroup.mem_top k)
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

end ChainLift

end Generation

section LinkStar

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem actsTriv_or_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {N L' : Subgroup G} {w a : G} (hN : N ∈ Ω) (hL' : L' ∈ Ω) (hw : IsClassicalMember p f N w)
    (ha : IsClassicalMember p f L' a) (htq : ActsTrivOnQuot L' w) :
    w = a ∨ ActsTrivOnQuot N a := by
  by_cases hNL : L' = N
  · subst hNL
    left
    exact (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hw).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha)
  · right
    have h1 : L' ∈ omegaNbr Ω N :=
      mem_omegaNbr_of_trivialOnQuot hp hq hΩ hN
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hw) hL' hNL
        (mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq)
    have h2 : N ∈ omegaNbr Ω L' := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hN hL' h1
    obtain ⟨a', ha', hNa'⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical hL' h2
    have : a' = a := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha').eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha)
    exact this ▸ hNa'

variable {z : G} {C : ChainCtx p f Ω z} (L : ChainLift C)

namespace ChainLift

theorem tbar_ne_zbar : oddQuotMk z ⟨L.t, L.ht⟩ ≠ oddQuotMk z ⟨z, ChainLift.hzC⟩ := by
  intro h
  obtain ⟨r, hr, hrc⟩ := L.psi_comm_ne
  apply hrc
  have hcen := oddQuotMk_central (ChainLift.hzC (z := z)) (C.psi C.i₁ r)
  rw [← h, L.htbar] at hcen
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact ChainFrame.commutator_eq_one_of_comm hcen

theorem link_z_star : InvolutionLinkStar p f Ω (Subgroup.closure ({z, L.t, L.z'} : Set G))
    ({C.K, L.J} : Set (Subgroup G)) z := by
  intro N hN w hw hdisj
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have key : ActsTrivOnQuot N z ∨ w = z := by
    rcases hdisj with h | ⟨L', hL', hL'z, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq C.hp C.hq C.hΩ hN hL' hw hL'z hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwz
  · have hNtq : N ∈ tqMembers Ω z := ⟨hN, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩
    obtain ⟨h, hh, hcase⟩ := L.link_z hNtq hw
    rcases hcase with hc | hc
    · exact ⟨C.K, Set.mem_insert _ _, z, L.z_mem_B, hKcl, h, hh, hc⟩
    · exact ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, h, hh, hc⟩
  · exact ⟨C.K, Set.mem_insert _ _, z, L.z_mem_B, hKcl, 1, one_mem _, by rw [hwz]; group⟩

theorem link_t_star (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M) :
    InvolutionLinkStar p f Ω (Subgroup.closure ({z, L.t, L.z'} : Set G))
      ({C.K, L.J} : Set (Subgroup G)) L.t := by
  obtain ⟨s, hsz, hst⟩ := L.exists_swap_zt htrans
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
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
    obtain ⟨h, hh, hcase⟩ := L.link_z hN'tq (hw.conj s⁻¹)
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
    · refine ⟨C.K, Set.mem_insert _ _, z, L.z_mem_B, hKcl, s * h * s⁻¹, hh', ?_⟩
      rw [hwe, hc]
      calc s * (h * L.t * h⁻¹) * s⁻¹ =
          (s * h * s⁻¹) * (s * L.t * s⁻¹) * (s * h * s⁻¹)⁻¹ := by group
        _ = (s * h * s⁻¹) * z * (s * h * s⁻¹)⁻¹ := by rw [hst]
  · refine ⟨L.J, Set.mem_insert_of_mem _ rfl, L.t, L.t_mem_B, L.hJt, 1, one_mem _, ?_⟩
    rw [hwt]
    group

theorem cover_z (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M) {M : Subgroup G}
    (hM : M ∈ centMembers Ω z) :
    ∃ g : G, z ∈ conjSub g (Subgroup.closure ({z, L.t, L.z'} : Set G)) ∧
      InCommonComponent z M (exactCore z (conjSub g C.K)) := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hKN : C.K ∈ tqMembers Ω z := ⟨C.hK, C.hKtq⟩
  have hMtq : M ∈ tqMembers Ω z := centMembers_subset_tqMembers hM
  have hMeq : exactCore z M = M := exactCore_eq_self_of_mem_centMembers C.hΩ.classical hM
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hMtq
  rw [hMeq] at hmod
  rcases C.eq_i₀_or_i₁ j with rfl | rfl
  · have h1 : conjSub 1 C.K = C.K := by
      ext x
      rw [mem_conjSub_iff]
      simp
    refine ⟨1, ?_, (C.psi C.i₀).range, C.isComponent_range C.i₀, ?_, ?_⟩
    · rw [mem_conjSub_iff]
      simpa using L.z_mem_B
    · rw [← hmod]
      exact Subgroup.map_le_range _ _
    · rw [h1, C.modOdd_K_eq_range]
  · obtain ⟨s, hsz, hst⟩ := L.exists_swap_zt htrans
    have hstz : s⁻¹ * z * s = L.t := by
      calc s⁻¹ * z * s = s⁻¹ * (s * L.t * s⁻¹) * s := by rw [hst]
        _ = L.t := by group
    have hNtq : conjSub s C.K ∈ tqMembers Ω z := by
      refine ⟨C.hΩ.conjInvariant s C.K C.hK, ?_⟩
      have h := trivialOnQuot_conjSub (L.frameData.tq_t C.hp C.hq C.hΩ) s
      rwa [hst] at h
    have hNcl : IsClassicalMember p f (conjSub s C.K) L.t := by
      have := hKcl.conj s
      rwa [hsz] at this
    obtain ⟨j', R', hR', hmod'⟩ := C.exists_fund_of_mem hNtq
    have hj' : j' = C.i₁ := by
      rcases C.eq_i₀_or_i₁ j' with rfl | h
      · exfalso
        have hq1 : modOdd z (exactCore z (conjSub s C.K)) = modOdd z (exactCore z C.K) := by
          rw [← hmod', C.fund_eq_top₀ hR', Subgroup.map_top, C.modOdd_K_eq_range]
        have hU1 := C.isUniqueInvolution_modOdd hNtq hNcl
        have hU2 := C.isUniqueInvolution_modOdd hKN hKcl
        rw [hq1] at hU1
        exact L.tbar_ne_zbar (hU1.eq hU2)
      · exact h
    subst hj'
    refine ⟨s, ?_, (C.psi C.i₁).range, C.isComponent_range C.i₁, ?_, ?_⟩
    · rw [mem_conjSub_iff, hstz]
      exact L.t_mem_B
    · rw [← hmod]
      exact Subgroup.map_le_range _ _
    · rw [← hmod']
      exact Subgroup.map_le_range _ _

end ChainLift

end LinkStar

end CFSG.ClassicalInvolution.Asc77
