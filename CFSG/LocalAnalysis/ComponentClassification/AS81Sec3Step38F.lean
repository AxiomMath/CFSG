module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Span
public import CFSG.LargeExtraspecial.S14C13Model
public import CFSG.LargeExtraspecial.S45QOmegaMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem F_le_N : sec3F (Q₀ ⊔ Q) ≤ H.xsub.N := Quasithin.perfectCore_le _

omit H in
theorem F_perfect : ⁅sec3F (Q₀ ⊔ Q), sec3F (Q₀ ⊔ Q)⁆ = sec3F (Q₀ ⊔ Q) :=
  Quasithin.perfectCore_perfect _

omit H in
theorem commutator_F : commutator ↥(sec3F (Q₀ ⊔ Q)) = ⊤ := by
  apply Subgroup.map_injective (sec3F (Q₀ ⊔ Q)).subtype_injective
  rw [Subgroup.map_subtype_commutator, F_perfect, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem N_le_normalizer_F : H.xsub.N ≤ normalizer (sec3F (Q₀ ⊔ Q) : Set G) := fun _ hn =>
  Quasithin.normalizer_le_normalizer_perfectCore _ (le_normalizer hn)

theorem B₀_le_F : B₀ ≤ sec3F (Q₀ ⊔ Q) := by
  have hB : ⁅B₀, B₀⁆ = B₀ := by
    rw [← Subgroup.map_subtype_commutator, H.B₀_perf, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  exact Quasithin.le_perfectCore_of_perfect H.B₀_le_N hB

noncomputable abbrev ρF : ↥(sec3F (Q₀ ⊔ Q)) →* (H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt) :=
  H.ρG.comp (Subgroup.inclusion H.F_le_N)

theorem ρF_mem_omega (f : ↥(sec3F (Q₀ ⊔ Q))) :
    H.ρF f ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  let φ : ↥(sec3F (Q₀ ⊔ Q)) →* Multiplicative (ZMod 2) :=
    (dicksonHom H.xsub.q H.xsub.q_nondegenerate).comp
      (H.xsub.ρ.comp (Subgroup.inclusion H.F_le_N))
  have hk : f ∈ φ.ker := by
    have h1 := Abelianization.commutator_subset_ker φ
    rw [commutator_F] at h1
    exact h1 (mem_top f)
  have hk' : H.xsub.ρ (Subgroup.inclusion H.F_le_N f) ∈
      (dicksonHom H.xsub.q H.xsub.q_nondegenerate).ker := hk
  rw [dicksonHom_ker, mem_subgroupOf] at hk'
  exact hk'

theorem omega_perfect :
    ⁅omegaGroup H.xsub.q H.xsub.q_nondegenerate, omegaGroup H.xsub.q H.xsub.q_nondegenerate⁆ =
      omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  have : IsSimpleGroup ↥(omegaGroup H.xsub.q H.xsub.q_nondegenerate) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_six_le H.xsub.q_nondegenerate
      (by rw [H.finrank_Qt]; norm_num)
  have hn : (commutator ↥(omegaGroup H.xsub.q H.xsub.q_nondegenerate)).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    have hbot : ⁅omegaGroup H.xsub.q H.xsub.q_nondegenerate,
        omegaGroup H.xsub.q H.xsub.q_nondegenerate⁆ = ⊥ := by
      rw [← Subgroup.map_subtype_commutator, h, Subgroup.map_bot]
    have hB : ⁅H.ρB₀, H.ρB₀⁆ = H.ρB₀ := by
      show ⁅H.ρB₀hom.range, H.ρB₀hom.range⁆ = H.ρB₀hom.range
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, H.B₀_perf]
    have hle : H.ρB₀ ≤ ⊥ := by
      rw [← hB, ← hbot]
      exact Subgroup.commutator_mono H.ρB₀_le_omega H.ρB₀_le_omega
    have hc := H.card_ρB₀
    rw [le_bot_iff.mp hle, card_bot] at hc
    exact absurd hc (by norm_num)
  · rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable (hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range)
include hΩ

theorem omega_le_range_ρF : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρF.range := by
  have h1 : (Quasithin.perfectCore (⊤ : Subgroup H.xsub.N)).map H.xsub.N.subtype =
      sec3F (Q₀ ⊔ Q) := by
    rw [Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have h2 : (Quasithin.perfectCore (⊤ : Subgroup H.xsub.N)).map H.ρG =
      Quasithin.perfectCore H.ρG.range := by
    rw [Quasithin.map_perfectCore, ← MonoidHom.range_eq_map]
  have h3 : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ Quasithin.perfectCore H.ρG.range :=
    Quasithin.le_perfectCore_of_perfect hΩ H.omega_perfect
  intro k hk
  rw [← h2] at h3
  obtain ⟨m, hm, rfl⟩ := h3 hk
  have hmF : (m : G) ∈ sec3F (Q₀ ⊔ Q) := h1 ▸ ⟨m, hm, rfl⟩
  exact ⟨⟨m, hmF⟩, rfl⟩

theorem exists_F_of_omega {k : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt}
    (hk : k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate) :
    ∃ f : ↥(sec3F (Q₀ ⊔ Q)), H.ρF f = k :=
  H.omega_le_range_ρF hΩ hk

theorem clSub_invariant {X : Subgroup G}
    (hX : ∀ f ∈ sec3F (Q₀ ⊔ Q), f ∈ normalizer (X : Set G)) :
    ∀ k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate, ∀ u ∈ H.xsub.clSub X,
      k u ∈ H.xsub.clSub X := by
  intro k hk u hu
  obtain ⟨f, rfl⟩ := H.exists_F_of_omega hΩ hk
  have h := H.xsub.map_ρ_clSub (Subgroup.inclusion H.F_le_N f) X
  have h2 : X.map (MulAut.conj (f : G)).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (hX f f.2)
  rw [show ((Subgroup.inclusion H.F_le_N f : H.xsub.N) : G) = f from rfl, h2] at h
  have hmem := Submodule.mem_map_of_mem (f := ((H.xsub.ρ (Subgroup.inclusion H.F_le_N f) :
    H.xsub.O) : H.xsub.Qt ≃ₗ[ZMod 2] H.xsub.Qt).toLinearMap) hu
  rw [h] at hmem
  exact hmem

theorem W₀_le_clSub {X : Subgroup G} (hXQ : X ≤ H.xsub.Q₁)
    (hcomm : ∀ f ∈ sec3F (Q₀ ⊔ Q), ∀ a ∈ Q₀, f * a * f⁻¹ * a⁻¹ ∈ X) :
    H.xsub.clSub Q₀ ≤ H.xsub.clSub X := by
  intro w hw
  obtain ⟨w', hw', hww'⟩ := H.exists_sub_W₀ hw
  obtain ⟨a, haQ₀, haQ, rfl⟩ := H.xsub.mem_clSub_iff.mp hw'
  obtain ⟨f, hf⟩ := H.exists_F_of_omega hΩ (H.ρX_le_omega (mem_zpowers _))
  rw [← hf] at hww'
  rw [← hww']
  change H.ρG (Subgroup.inclusion H.F_le_N f) (H.xsub.cl a) - H.xsub.cl a ∈ _
  rw [H.ρG_cl _ haQ, show ((Subgroup.inclusion H.F_le_N f : H.xsub.N) : G) = f from rfl]
  have hc := hcomm f f.2 a haQ₀
  have hfaQ : (f : G) * a * (f : G)⁻¹ ∈ H.xsub.Q₁ := H.xsub.conj_mem (H.F_le_N f.2) haQ
  have e : H.xsub.cl ((f : G) * a * (f : G)⁻¹) - H.xsub.cl a =
      H.xsub.cl ((f : G) * a * (f : G)⁻¹ * a⁻¹) := by
    rw [H.xsub.cl_mul hfaQ (inv_mem haQ), H.xsub.cl_inv haQ, sub_eq_add_neg,
      ZModModule.neg_eq_self]
  rw [e]
  exact H.xsub.cl_mem_clSub hc (hXQ hc)

omit hΩ in
theorem eq_of_clSub_eq_top {X : Subgroup G} (hXQ : X ≤ H.xsub.Q₁) (hzX : z ∈ X)
    (htop : H.xsub.clSub X = ⊤) : X = Q₀ ⊔ Q := by
  have h := H.xsub.clPre_clSub hXQ hzX
  rw [htop] at h
  rw [← h]
  ext a
  exact ⟨fun ha => ha.1, fun ha => ⟨ha, Submodule.mem_top⟩⟩

variable (htrans : ∀ L : Submodule (ZMod 2) H.xsub.Qt, finrank (ZMod 2) L = 2 →
  (∀ w ∈ L, H.xsub.q w = 0 → w = 0) → ∃ k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate,
    (H.xsub.clSub Q₀).map (k : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = L)
include htrans

theorem Q₁_le_F : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q) := by
  have hzX : z ∈ (Q₀ ⊔ Q) ⊓ sec3F (Q₀ ⊔ Q) :=
    mem_inf.mpr ⟨H.Q_le H.z_mem_Q, H.B₀_le_F (H.B₀_quot.1 H.z_mem_Q)⟩
  have hXQ : (Q₀ ⊔ Q) ⊓ sec3F (Q₀ ⊔ Q) ≤ H.xsub.Q₁ := inf_le_left
  have htop := H.eq_top_of_invariant htrans (W := H.xsub.clSub ((Q₀ ⊔ Q) ⊓ sec3F (Q₀ ⊔ Q)))
    (H.clSub_invariant hΩ fun f hf =>
      mem_normalizer_inf (H.F_le_N hf) (H.N_le_normalizer_F (H.F_le_N hf)))
    (H.W₀_le_clSub hΩ hXQ fun f hf a ha => by
      have haQ : a ∈ H.xsub.Q₁ := H.Q₀_le ha
      have hfN := H.F_le_N hf
      refine mem_inf.mpr ⟨mul_mem (H.xsub.conj_mem hfN haQ) (inv_mem haQ), ?_⟩
      have h1 : a * f⁻¹ * a⁻¹ ∈ sec3F (Q₀ ⊔ Q) :=
        (mem_normalizer_iff.mp (H.N_le_normalizer_F (H.xsub.le_N haQ)) _).mp (inv_mem hf)
      rw [show f * a * f⁻¹ * a⁻¹ = f * (a * f⁻¹ * a⁻¹) by group]
      exact mul_mem hf h1)
  exact (H.eq_of_clSub_eq_top hXQ hzX htop).symm.le.trans inf_le_right

omit hΩ htrans in
theorem le_zpowers_of_le_centralizer {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) : S ≤ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSQ₀ : S ≤ centralizer (Q₀ : Set G) :=
    hSC.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hSQ : S ≤ centralizer (Q : Set G) :=
    hSC.trans (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.of_card (n := 3) (by rw [H.card_Q₀]; norm_num)
  have hsup := hQ₀2.to_sup_of_normal_left' hS2 (hSQ₀.trans (centralizer_le_normalizer _))
  have hQ₀C : Q₀ ≤ centralizer (Q : Set G) := le_centralizer_iff.mp H.Q_le_centralizer
  have heq := H.sylow.eq_of_le le_sup_left (sup_le hQ₀C hSQ) hsup
  intro s hs
  have hsQ₀ : s ∈ Q₀ := heq ▸ mem_sup_right hs
  rw [← H.q0.dData.suz.Q_center, ← H.q0.center_Q₀]
  exact ⟨hsQ₀, hSQ₀ hs⟩

omit hΩ htrans in
theorem centralizer_le_sup_oddCoreIn :
    sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤
      (Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
        centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C₁ : Subgroup G := sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)
  let P : Sylow 2 ↥C₁ := default
  have hPz : (P : Subgroup ↥C₁).map C₁.subtype ≤ zpowers z :=
    H.le_zpowers_of_le_centralizer (P.isPGroup'.map _) ((map_subtype_le _).trans inf_le_right)
  have hPc : ∀ p ∈ (P : Subgroup ↥C₁), ∀ c : ↥C₁, c * p = p * c := by
    intro p hp c
    have hpz : (p : G) ∈ zpowers z := hPz ⟨p, hp, rfl⟩
    have hzc : z * (c : G) = (c : G) * z :=
      mem_centralizer_iff.mp (mem_inf.mp c.2).2 z (H.Q_le H.z_mem_Q)
    apply Subtype.ext
    rcases H.xsub.mem_zpowers_z_iff.mp hpz with h | h
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, h, mul_one, one_mul]
    · have h' : (p : G) = z := h
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h']
      exact hzc.symm
  have hP : normalizer ((P : Subgroup ↥C₁) : Set ↥C₁) ≤
      centralizer ((P : Subgroup ↥C₁) : Set ↥C₁) :=
    fun c _ => mem_centralizer_iff.mpr fun p hp => (hPc p hp c).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  have hodd : Odd (Nat.card (MonoidHom.transferSylow P hP).ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hP))
  have hKO : (MonoidHom.transferSylow P hP).ker ≤ CFSG.Assembly.oddCore ↥C₁ :=
    le_sSup ⟨inferInstance, hodd⟩
  intro c hc
  have hctop : (⟨c, hc⟩ : ↥C₁) ∈ (MonoidHom.transferSylow P hP).ker ⊔ (P : Subgroup ↥C₁) := by
    rw [hcomp.sup_eq_top]
    exact mem_top _
  have hmap := Subgroup.mem_map_of_mem C₁.subtype hctop
  rw [Subgroup.map_sup] at hmap
  refine (sup_le ((map_mono hKO).trans le_sup_right)
    (hPz.trans ((zpowers_le.mpr (H.Q_le H.z_mem_Q)).trans le_sup_left))) hmap

omit hΩ htrans in
theorem ker_ρF (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) :
    H.ρF.ker = ((Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
      centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G))).subgroupOf (sec3F (Q₀ ⊔ Q)) := by
  ext f
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hf
    have h1 : H.xsub.ρ (Subgroup.inclusion H.F_le_N f) = 1 := (H.ρG_eq_one_iff _).mp hf
    obtain ⟨c, hc, hcf⟩ := (H.xsub.ρ_eq_one_iff _).mp h1
    have hcQ : c ∈ Q₀ ⊔ Q := hc
    have hcfC : c⁻¹ * (f : G) ∈
        sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
      mem_inf.mpr ⟨mul_mem (inv_mem (hQF hcQ)) f.2, hcf⟩
    have h2 := H.centralizer_le_sup_oddCoreIn hcfC
    rw [show (f : G) = c * (c⁻¹ * f) by group]
    exact mul_mem (mem_sup_left hcQ) h2
  · intro hf
    show H.ρG (Subgroup.inclusion H.F_le_N f) = 1
    apply (H.ρG_eq_one_iff _).mpr
    have hQ₁K : Q₀ ⊔ Q ≤ (H.xsub.ρ.ker).map H.xsub.N.subtype := fun a ha =>
      ⟨⟨a, H.xsub.le_N ha⟩, MonoidHom.mem_ker.mpr (H.xsub.ρ_eq_one_of_mem ha), rfl⟩
    have hCK : sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) ≤
        (H.xsub.ρ.ker).map H.xsub.N.subtype := fun a ha =>
      ⟨⟨a, H.F_le_N (mem_inf.mp ha).1⟩,
        MonoidHom.mem_ker.mpr (H.xsub.ρ_eq_one_of_mem_centralizer (mem_inf.mp ha).2), rfl⟩
    have hOC : AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
        sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := map_subtype_le _
    have hle := sup_le hQ₁K (hOC.trans hCK)
    obtain ⟨n, hn, hnf⟩ := hle hf
    have e : n = Subgroup.inclusion H.F_le_N f := Subtype.ext hnf
    rw [← e]
    exact MonoidHom.mem_ker.mp hn

theorem step38_concl :
    Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q) ∧
      (∃ φ : ↥(sec3F (Q₀ ⊔ Q)) →* ↥(timmesfeldOmegaPlus 4), Function.Surjective φ ∧
        φ.ker = ((Q₀ ⊔ Q) ⊔ AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓
          centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G))).subgroupOf (sec3F (Q₀ ⊔ Q))) ∧
      ∀ B : Subgroup G, zpowers z ≤ B → B < Q₀ ⊔ Q →
        sec3F (Q₀ ⊔ Q) ≤ normalizer (B : Set G) → ∀ n : ℕ,
          ∃ k ∈ (derivedSeries ↥(sec3F (Q₀ ⊔ Q)) n).map (sec3F (Q₀ ⊔ Q)).subtype,
            ∃ w ∈ Q₀ ⊔ Q, k⁻¹ * w * k * w⁻¹ ∉ B := by
  have hQF := H.Q₁_le_F hΩ htrans
  refine ⟨hQF, ?_, ?_⟩
  · obtain ⟨e⟩ := CFSG.LargeExtraspecial.S14.nonempty_omegaGroup_equiv_omegaPlus
      H.xsub.q_nondegenerate (m := 4) (by rw [H.finrank_Qt]) (by norm_num) H.isPlusType
    let ρΩ : ↥(sec3F (Q₀ ⊔ Q)) →* ↥(omegaGroup H.xsub.q H.xsub.q_nondegenerate) :=
      H.ρF.codRestrict _ H.ρF_mem_omega
    refine ⟨e.toMonoidHom.comp ρΩ, fun k => ?_, ?_⟩
    · obtain ⟨f, hf⟩ := H.exists_F_of_omega hΩ (e.symm k).2
      refine ⟨f, ?_⟩
      have h1 : ρΩ f = e.symm k := Subtype.ext hf
      rw [MonoidHom.comp_apply, h1, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    · ext f
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, ← H.ker_ρF hQF, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · intro B hzB hBlt hFB n
    have hder : derivedSeries ↥(sec3F (Q₀ ⊔ Q)) n = ⊤ := by
      induction n with
      | zero => exact derivedSeries_zero _
      | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, commutator_F]
    by_contra hcon
    push Not at hcon
    rw [hder, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hcon
    have hBQ : B ≤ H.xsub.Q₁ := hBlt.le
    have hzB' : z ∈ B := hzB (mem_zpowers z)
    have htop := H.eq_top_of_invariant htrans (W := H.xsub.clSub B)
      (H.clSub_invariant hΩ fun f hf => hFB hf)
      (H.W₀_le_clSub hΩ hBQ fun f hf a ha => by
        have h := hcon f⁻¹ (inv_mem hf) a (H.Q₀_le ha)
        rwa [inv_inv] at h)
    exact hBlt.ne (H.eq_of_clSub_eq_top hBQ hzB' htop)

end Sec38Hyp

end CFSG.ComponentClassification.AS81
