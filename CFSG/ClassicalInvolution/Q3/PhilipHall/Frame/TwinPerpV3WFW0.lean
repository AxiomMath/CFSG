module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93WCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf71Alt2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped Pointwise

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem zstar_odd_structure (P : Subgroup G) [hPn : P.Normal] (hP : IsPGroup 2 P) (S : Sylow 2 G)
    (W U : Subgroup G) (w : G) (hwW : w ∈ W) (hWS : W ≤ (S : Subgroup G))
    (hWn : ∀ s ∈ (S : Subgroup G), ∀ a ∈ W, s * a * s⁻¹ ∈ W)
    (hWw : W ≤ P ⊔ Subgroup.zpowers w) (hw2 : w * w ∈ P)
    (hweak : ∀ g : G, (∀ a ∈ W, g⁻¹ * a * g ∈ (S : Subgroup G)) → ∀ a ∈ W, g⁻¹ * a * g ∈ W)
    (hUW : U ≤ W) :
    ∃ N : Subgroup G, N.Normal ∧ P ≤ N ∧ Odd (P.subgroupOf N).index ∧
      ∀ x ∈ Subgroup.normalClosure (U : Set G), Odd (orderOf x) → x ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hwP : w ∈ P
  · refine ⟨P, hPn, le_rfl, ?_, fun x hx _ => ?_⟩
    · simp
    · have hWP : W ≤ P := hWw.trans (sup_le le_rfl (Subgroup.zpowers_le.mpr hwP))
      exact Subgroup.normalClosure_le_normal (fun u hu => hWP (hUW hu)) hx
  have hPS : P ≤ (S : Subgroup G) := hP.le_sylow_of_normal S
  have hconjP : ∀ g x : G, x ∈ P ↔ g * x * g⁻¹ ∈ P := fun g x =>
    ⟨fun h => hPn.conj_mem x h g, fun h => by
      have := hPn.conj_mem _ h g⁻¹
      simpa [mul_assoc] using this⟩
  set π := QuotientGroup.mk' P with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hπ1 : ∀ x, π x = 1 ↔ x ∈ P := fun x => QuotientGroup.eq_one_iff x
  have hsq : π w * π w = 1 := by rw [← map_mul, hπ1]; exact hw2
  have hπw1 : π w ≠ 1 := fun h => hwP ((hπ1 w).mp h)
  have himg : ∀ a ∈ W, π a = 1 ∨ π a = π w := by
    have hle : P ⊔ Subgroup.zpowers w ≤ (Subgroup.zpowers (π w)).comap π :=
      sup_le (fun p hp => by rw [Subgroup.mem_comap, (hπ1 p).mpr hp]; exact one_mem _)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers (π w)))
    intro a ha
    exact eq_one_or_of_mem_zpowers_of_mul_self hsq (hle (hWw ha))
  have hconjw : ∀ s ∈ (S : Subgroup G), π s * π w = π w * π s := by
    intro s hs
    rcases himg _ (hWn s hs w hwW) with h | h
    · exact absurd ((hconjP s w).mpr ((hπ1 _).mp h)) hwP
    · have : π s * π w * (π s)⁻¹ = π w := by
        rw [← map_inv, ← map_mul, ← map_mul, h]
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
  let S' : Sylow 2 (G ⧸ P) := S.mapSurjective hπs
  have hS' : (S' : Subgroup (G ⧸ P)) = (S : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  let z : ↥(S' : Subgroup (G ⧸ P)) := ⟨π w, by rw [hS']; exact ⟨w, hWS hwW, rfl⟩⟩
  have hzZ : z ∈ Subgroup.center ↥(S' : Subgroup (G ⧸ P)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, hs, hsg⟩ := (hS' ▸ g.2 : (g : G ⧸ P) ∈ (S : Subgroup G).map π)
    apply Subtype.ext
    change (g : G ⧸ P) * π w = π w * (g : G ⧸ P)
    rw [← hsg]
    exact hconjw s hs
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change π w ^ 2 = 1
      rw [sq]; exact hsq
    · intro h
      exact hπw1 (congrArg Subtype.val h)
  have hwc : ∀ g : G ⧸ P, g⁻¹ * (z : G ⧸ P) * g ∈ (S' : Subgroup (G ⧸ P)) →
      g⁻¹ * (z : G ⧸ P) * g = z := by
    intro gb hmem
    obtain ⟨g, rfl⟩ := hπs gb
    have hmem' : (π g)⁻¹ * π w * π g ∈ (S : Subgroup G).map π := by
      rw [← hS']; exact hmem
    obtain ⟨s, hs, hsg⟩ := hmem'
    have hsm : s⁻¹ * (g⁻¹ * w * g) ∈ P := by
      rw [← hπ1, map_mul, map_inv, hsg]
      simp only [map_mul, map_inv]
      group
    have hgwS : g⁻¹ * w * g ∈ (S : Subgroup G) := by
      have : g⁻¹ * w * g = s * (s⁻¹ * (g⁻¹ * w * g)) := by group
      rw [this]
      exact Subgroup.mul_mem _ hs (hPS hsm)
    have hT : P ⊔ Subgroup.zpowers w ≤
        (S : Subgroup G).comap (MulAut.conj g⁻¹).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        change g⁻¹ * p * g⁻¹⁻¹ ∈ _
        exact hPS (hPn.conj_mem p hp g⁻¹)
      · rw [Subgroup.mem_comap]
        change g⁻¹ * w * g⁻¹⁻¹ ∈ _
        simpa using hgwS
    have hW' : ∀ a ∈ W, g⁻¹ * a * g ∈ (S : Subgroup G) := fun a ha => by
      have := hT (hWw ha)
      rw [Subgroup.mem_comap] at this
      simpa using this
    have hgW := hweak g hW' w hwW
    rcases himg _ hgW with h | h
    · exact absurd ((hconjP g⁻¹ w).mpr (by simpa using (hπ1 _).mp h)) hwP
    · change (π g)⁻¹ * π w * π g = π w
      rw [← map_inv, ← map_mul, ← map_mul, h]
  obtain ⟨-, hcent⟩ := Adapters.glauberman_zStar S' z hzZ hz2 hwc
  set ρ : G →* (G ⧸ P) ⧸ CFSG.oddCore (G ⧸ P) :=
    (QuotientGroup.mk' (CFSG.oddCore (G ⧸ P))).comp π with hρ
  have hρw : ρ w ∈ Subgroup.center ((G ⧸ P) ⧸ CFSG.oddCore (G ⧸ P)) := hcent
  have hρ_apply : ∀ x, ρ x = QuotientGroup.mk' (CFSG.oddCore (G ⧸ P)) (π x) := fun x => rfl
  have hρker : ∀ x, ρ x = 1 ↔ π x ∈ CFSG.oddCore (G ⧸ P) := fun x => by
    rw [hρ_apply]; exact QuotientGroup.eq_one_iff _
  have hρP : ∀ p ∈ P, ρ p = 1 := fun p hp => by
    rw [hρker, (hπ1 p).mpr hp]; exact one_mem _
  have hρsq : ρ w * ρ w = 1 := by rw [← map_mul]; exact hρP _ hw2
  set N2 : Subgroup G := (Subgroup.zpowers (ρ w)).comap ρ with hN2
  haveI hN2n : N2.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN2, Subgroup.mem_comap] at hn ⊢
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hρw) hn) (ρ g)
    have : ρ (g * n * g⁻¹) = ρ n := by
      rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
      exact hc
    rw [this]; exact hn
  have hPW : P ⊔ Subgroup.zpowers w ≤ N2 :=
    sup_le (fun p hp => by rw [hN2, Subgroup.mem_comap, hρP p hp]; exact one_mem _)
      (Subgroup.zpowers_le.mpr (by rw [hN2, Subgroup.mem_comap]; exact Subgroup.mem_zpowers _))
  set L : Subgroup G := Subgroup.normalClosure (U : Set G) with hL
  have hLN : L ≤ N2 := Subgroup.normalClosure_le_normal (fun u hu => hPW (hWw (hUW hu)))
  have hLsplit : ∀ x ∈ L, ρ x = 1 ∨ ρ x = ρ w := fun x hx =>
    eq_one_or_of_mem_zpowers_of_mul_self hρsq (hLN hx)
  refine ⟨ρ.ker, ρ.normal_ker, fun p hp => (MonoidHom.mem_ker).mpr (hρP p hp), ?_, ?_⟩
  · set f : ↥(ρ.ker) →* (G ⧸ P) := π.comp (ρ.ker).subtype with hf
    have hker : f.ker = P.subgroupOf ρ.ker := by
      ext x
      simp [hf, MonoidHom.mem_ker, hπ1, Subgroup.mem_subgroupOf]
    rw [← hker, Subgroup.index_ker]
    have hrange : f.range ≤ CFSG.oddCore (G ⧸ P) := by
      rintro _ ⟨x, rfl⟩
      exact (hρker _).mp x.2
    exact Odd.of_dvd_nat (odd_card_oddCore _) (Subgroup.card_dvd_of_le hrange)
  · intro x hxL hxo
    rw [MonoidHom.mem_ker]
    rcases hLsplit x hxL with h | h
    · exact h
    ·
      have h2 : ρ x ^ 2 = 1 := by rw [sq, h]; exact hρsq
      obtain ⟨j, hj⟩ := hxo
      have h1 : ρ x ^ (orderOf x) = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [hj, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
      exact h1

end ZStar

section W0Proof

variable {n : ℕ}

theorem wfW0_proved (n : ℕ) : WFW0 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC x hxo hxL hxP
  have hUP : ¬ ∃ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({t} : Set Y) ∧
      (Q.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal ∧ IsPGroup 2 Q ∧ U ≤ Q := by
    rintro ⟨Q, hQC, hQn, hQ2, hUQ⟩
    have hLQ : Balance.normalClosureIn (Subgroup.centralizer ({t} : Set Y)) U ≤ Q := by
      refine Balance.normalClosureIn_le fun g hg => ?_
      rintro _ ⟨u, hu, rfl⟩
      have := hQn.conj_mem ⟨u, hQC (hUQ hu)⟩ (Subgroup.mem_subgroupOf.mpr (hUQ hu)) ⟨g, hg⟩
      exact Subgroup.mem_subgroupOf.mp this
    have hxQ : x ∈ Q := hLQ hxL
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hxQ⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    have hi0 : i = 0 := by
      by_contra hne
      have : Even (orderOf x) := by rw [hi]; exact (Nat.even_pow.mpr ⟨even_two, hne⟩)
      exact (Nat.not_even_iff_odd.mpr hxo) this
    rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
    exact hxP (hi ▸ Subgroup.one_mem _)
  obtain ⟨W, hWΩ, htW, hUW, w, hwW, hWw, hw2⟩ :=
    v3WCore_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC hUP
  have hΩ := hin.1.datum.hyp
  have hab := Q3.Q3T6.abelian_of_mem_WSet3 hΩ hWΩ
  have hWC : W ≤ Subgroup.centralizer ({t} : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hab a ha t htW)
  have hA : V3WAlt2 n := v3WAlt2_proved
  have hin' := hin
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set P : Subgroup Y := ⨆ M ∈ twinSet Ω K, M with hPdef
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hPI : Q3CL.PartIHypG Ω := hCore.partIHypG
  have hPn : TC.IsNormalTwoIn P t := v3_P_normalTwo hStd h2g
  have htr0 : ∀ J ∈ Ω, ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : Y, conjSub g K₁ = J := by
    intro K₁ hK₁ J hJ
    obtain ⟨g₁, rfl⟩ := htr0 K₁ hK₁
    obtain ⟨g₂, rfl⟩ := htr0 J hJ
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  obtain ⟨η, ⟨S₀, hη, hinv⟩, hWη⟩ := hWΩ
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup Y) := fun U hU => (hη.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup Y) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have h612 := Q3.Q3T8.Disconnected.AschTight.Sec7.l6_12_mod Y Ω hPI htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  swap
  · obtain ⟨J, hJ, hJc, hJR⟩ := hA Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin' S₀ ⟨η, hη, hinv⟩
    exact absurd (h2 J hJ hJc) hJR
  have hMS₀ : (⨆ U ∈ {U : Subgroup Y | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup Y)}, U) ≤
      (S₀ : Subgroup Y) := iSup₂_le fun U hU => hU.2
  have hηeq : η = η₀ := huniq η ⟨S₀, hη, hinv⟩ fun m hm U hU => hinv m (hMS₀ hm) U hU
  subst hηeq
  have hW2 : IsPGroup 2 W := S₀.isPGroup'.to_le hWS₀
  have hW'2 : IsPGroup 2 (W.subgroupOf C) := hW2.comap_subtype
  obtain ⟨S_C, hS_C⟩ := hW'2.exists_le_sylow
  have hQ2 : IsPGroup 2 ((S_C : Subgroup ↥C).map C.subtype) := S_C.isPGroup'.map C.subtype
  obtain ⟨S₁, hS₁⟩ := hQ2.exists_le_sylow
  have hSC₁ : ∀ s ∈ (S_C : Subgroup ↥C), (s : Y) ∈ (S₁ : Subgroup Y) := fun s hs =>
    hS₁ ⟨s, hs, rfl⟩
  have hWS₁ : W ≤ (S₁ : Subgroup Y) := fun a ha =>
    hSC₁ ⟨a, hWC ha⟩ (hS_C (Subgroup.mem_subgroupOf.mpr ha))
  obtain ⟨hWn₁, hweak₁⟩ := weak_data_of_eta hη hinv hwc S₁ (hWη ▸ hWS₁)
  rw [← hWη] at hWn₁ hweak₁
  have hPC : P ≤ C := hPn.1
  have hwC : w ∈ C := hWC hwW
  have hP'n : (P.subgroupOf C).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hPn.2.2 g g.2 a ha
  have hP'2 : IsPGroup 2 (P.subgroupOf C) := hPn.2.1.comap_subtype
  have hWw' : W.subgroupOf C ≤ P.subgroupOf C ⊔ Subgroup.zpowers (⟨w, hwC⟩ : ↥C) := by
    intro a ha
    have h1 : (a : Y) ∈ P ⊔ Subgroup.zpowers w := hWw (Subgroup.mem_subgroupOf.mp ha)
    have h2 : (P.subgroupOf C ⊔ Subgroup.zpowers (⟨w, hwC⟩ : ↥C)).map C.subtype =
        P ⊔ Subgroup.zpowers w := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPC,
        MonoidHom.map_zpowers]
      rfl
    rw [← h2] at h1
    obtain ⟨b, hb, hba⟩ := h1
    have : b = a := Subtype.ext hba
    rwa [this] at hb
  have hw2' : (⟨w, hwC⟩ : ↥C) * ⟨w, hwC⟩ ∈ P.subgroupOf C := Subgroup.mem_subgroupOf.mpr hw2
  have hWn : ∀ s ∈ (S_C : Subgroup ↥C), ∀ a ∈ W.subgroupOf C, s * a * s⁻¹ ∈ W.subgroupOf C :=
    fun s hs a ha => Subgroup.mem_subgroupOf.mpr
      (hWn₁ s (hSC₁ s hs) a (Subgroup.mem_subgroupOf.mp ha))
  have hweak : ∀ g : ↥C, (∀ a ∈ W.subgroupOf C, g⁻¹ * a * g ∈ (S_C : Subgroup ↥C)) →
      ∀ a ∈ W.subgroupOf C, g⁻¹ * a * g ∈ W.subgroupOf C := by
    intro g hg a ha
    have := hweak₁ (g : Y)⁻¹ (fun b hb => by
      have := hSC₁ _ (hg ⟨b, hWC hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
      simpa using this) a (Subgroup.mem_subgroupOf.mp ha)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  haveI hP'nor : (P.subgroupOf C).Normal := hP'n
  obtain ⟨N', hN'n, hPN', hN'odd, hN'x⟩ := zstar_odd_structure (P.subgroupOf C) hP'2 S_C
    (W.subgroupOf C) (U.subgroupOf C) ⟨w, hwC⟩ (Subgroup.mem_subgroupOf.mpr hwW) hS_C hWn hWw' hw2'
    hweak (fun a ha => Subgroup.mem_subgroupOf.mpr (hUW (Subgroup.mem_subgroupOf.mp ha)))
  have hxC : x ∈ C := Balance.normalClosureIn_le_of_le hUC hxL
  have hxT : x ∈ ((Subgroup.normalClosure ((U.subgroupOf C : Subgroup ↥C) : Set ↥C)).map C.subtype) := by
    have hle : Balance.normalClosureIn C U ≤
        ((Subgroup.normalClosure ((U.subgroupOf C : Subgroup ↥C) : Set ↥C)).map C.subtype) := by
      refine Balance.normalClosureIn_le fun g hg => ?_
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨⟨g, hg⟩ * ⟨u, hUC hu⟩ * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      exact (Subgroup.normalClosure_normal).conj_mem _
        (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hu)) _
    exact hle hxL
  obtain ⟨z, hz, hzx⟩ := hxT
  have hzx' : z = ⟨x, hxC⟩ := Subtype.ext hzx
  rw [hzx'] at hz
  have hxN' : (⟨x, hxC⟩ : ↥C) ∈ N' := hN'x _ hz (by rw [← Subgroup.orderOf_coe]; exact hxo)
  refine ⟨N'.map C.subtype, ⟨Subgroup.map_subtype_le N', ?_, ?_, ?_⟩, ⟨_, hxN', rfl⟩⟩
  · have e : (N'.map C.subtype).subgroupOf C = N' :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective N'
    rw [e]; exact hN'n
  · intro p hp
    exact ⟨⟨p, hPC hp⟩, hPN' (Subgroup.mem_subgroupOf.mpr hp), rfl⟩
  · have h1 : (P.subgroupOf C).relIndex N' = P.relIndex (N'.map C.subtype) :=
      Subgroup.relIndex_comap P C.subtype N'
    show Odd (P.relIndex (N'.map C.subtype))
    rw [← h1]
    exact hN'odd

end W0Proof

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
