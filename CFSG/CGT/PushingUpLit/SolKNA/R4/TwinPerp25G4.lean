module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25GE8
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25GE29
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25GAE
public import CFSG.ClassicalInvolution.Q3.TL3T20
public import CFSG.ClassicalInvolution.Q3.Q3T6FusConj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25G2

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

structure Q8Sec (X : Type) [Group X] [Finite X] (K : Subgroup X) (t : X) : Prop where
  hyp : HypOmegaGen (CoreAssembly.conjClass K)
  uniq : IsUniqueInvolution K t
  tight : tightCore K = K
  gen : (⨆ g : X, conjSub g K) = ⊤
  oddFree : classicalInvolutionOddCore X = ⊥
  aEmpty : ∀ J ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) J
  quat : ∀ J ∈ CoreAssembly.conjClass K, ∀ P : Subgroup X, IsSylow2In P J →
    Nonempty (↥P ≃* QuaternionGroup 2)
  twin : ∃ K'' ∈ twinSet (CoreAssembly.conjClass K) K, K'' ≠ K

variable {X : Type} [Group X] [Finite X]

theorem oddCore_eq_bot_of_eq_top {Y : Subgroup X} (hY : Y = ⊤) (hO : classicalInvolutionOddCore X = ⊥) :
    classicalInvolutionOddCore ↥Y = ⊥ := by
  subst hY
  have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant
    (Subgroup.topEquiv (G := X)).symm
  have h2 : componentClassificationOddCore X = ⊥ := hO
  rw [h2, Subgroup.map_bot] at h1
  exact h1.symm

theorem central_of_wSet {K : Subgroup X} {t : X} (hS : Q8Sec X K t) (hTD : NoCentFour K t)
    (hW : ∃ W, WSet (CoreAssembly.conjClass K) = {W}) (hK2 : IsPGroup 2 K) (h8 : Nat.card K = 8) :
    ∀ g : X, g * t = t * g := by
  classical
  obtain ⟨W, hW⟩ := hW
  have hWmem : W ∈ WSet (CoreAssembly.conjClass K) := by rw [hW]; exact rfl
  have hWnorm : ∀ g : X, conjSub g W = W := fun g => by
    have := WSet.conj hS.hyp.conjInvariant hWmem g
    rw [hW] at this
    exact this
  have hWab := Q3T6.abelian_of_mem_WSet3 hS.hyp hWmem
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKs : IsSylow2In K K := ⟨le_rfl, hK2, fun V hVK _ hKV => le_antisymm hVK hKV⟩
  have hKD : K ∈ DSet (CoreAssembly.conjClass K) W :=
    ⟨mem_RSet_of_isSylow2In hKΩ hKs, fun x _ => mem_normalizer_iff_conjSub_eq.mpr (hWnorm x)⟩
  obtain ⟨-, -, hcyc, -, hcard⟩ := Q3.Q3CL.Thompson.inf_W_of_mem_D hS.hyp hWmem hKD hKΩ hKs
  have h4 : Nat.card ↥(K ⊓ W) = 4 := by omega
  obtain ⟨⟨k, hk⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥(K ⊓ W))
  have hk4 : orderOf k = 4 := by
    have := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [h4, Subgroup.orderOf_mk] at this
  have hksq : k ^ 2 = t := by
    have hk2 : k ^ 2 * k ^ 2 = 1 := by
      rw [← pow_add]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hk4])
    rcases hS.uniq.unique _ (K.pow_mem hk.1 2) hk2 with h | h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h
      rw [hk4] at this
      omega
    · exact h
  have htW : t ∈ W := by rw [← hksq]; exact W.pow_mem hk.2 2
  have hiso : ∀ g : X, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    have hsW : g * t * g⁻¹ ∈ W := by
      have := conj_mem_conjSub (n := g) htW
      rwa [hWnorm g] at this
    exact hTD g hne k hk.1 hk4 (hWab _ hsW k hk.2)
  haveI : Fintype X := Fintype.ofFinite X
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X t hS.uniq.ne_one hS.uniq.sq hiso
  have hNle : N ≤ classicalInvolutionOddCore X := le_sSup ⟨hNn, hNodd⟩
  intro g
  have h1 := hNle (hN g)
  rw [hS.oddFree, Subgroup.mem_bot] at h1
  have h2 := mul_inv_eq_one.mp h1
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [h2]

theorem central_of_inO2 {K : Subgroup X} {t : X} (hS : Q8Sec X K t) (hEC : OddEC t)
    (hTD : NoCentFour K t) (hD : TC.Thin.ThmDAbsAt 3 X) {P : Subgroup X} (hPn : P.Normal)
    (hP2 : IsPGroup 2 P) (htP : t ∈ P) : ∀ g : X, g * t = t * g := by
  classical
  have h2 := hEC.two_power_of_mem_normal hS.oddFree hPn hP2 htP
  set Ω := CoreAssembly.conjClass K with hΩdef
  have hKcomm : ∀ k ∈ K, k * t = t * k := fun k hk => TC.Thin.isUniqueInvolution_comm hS.uniq hk
  have hK2 : IsPGroup 2 K := (isPGroup_centralizer_of_two_power h2).to_le (fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKcomm k hk))
  have hKΩ : K ∈ Ω := CoreAssembly.mem_conjClass_self K
  have hΩ2 : ∀ J ∈ Ω, IsPGroup 2 J := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g hK2
  have hΩ8 : ∀ J ∈ Ω, Nat.card J = 2 ^ 3 := by
    intro J hJ
    have hJs : IsSylow2In J J := ⟨le_rfl, hΩ2 J hJ, fun V hVJ _ hJV => le_antisymm hVJ hJV⟩
    obtain ⟨e⟩ := hS.quat J hJ J hJs
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have h8K : Nat.card K = 8 := by rw [hΩ8 K hKΩ]; norm_num
  have hgen : TC.Thin.pSpan Ω = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hS.gen]
    exact iSup_le fun g => TC.Thin.le_pSpan ⟨g, rfl⟩
  have htrans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : X, conjSub g L = L' := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right]
  have hOpS : classicalInvolutionOddCore ↥(TC.Thin.pSpan Ω) = ⊥ :=
    oddCore_eq_bot_of_eq_top hgen hS.oddFree
  have hE2 : ∀ L ∈ Ω, ∀ u : X, IsUniqueInvolution L u →
      ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    rintro _ ⟨g, rfl⟩ u hu
    refine ⟨P, hPn, hP2, ?_⟩
    have : g * t * g⁻¹ = u := (hS.uniq.conj g).eq hu
    rw [← this]
    exact hPn.conj_mem t htP g
  rcases hD Ω hS.hyp hΩ2 hΩ8 hS.aEmpty hgen htrans hS.oddFree hE2 with
    hsingle | ⟨W, hW⟩ | ⟨E, hE⟩ | hI7 | ⟨n, hn, ⟨I⟩⟩ | hI8
  · exfalso
    obtain ⟨K'', hK''Ω, hne⟩ := hS.twin
    exact hne (hsingle K'' hK''Ω.1 K hKΩ)
  · exact central_of_wSet hS hTD ⟨W, hW⟩ hK2 h8K
  · exfalso
    exact false_of_e8Struct hE (hE.core P le_top (fun x _ q hq => hPn.conj_mem q hq x) hP2 htP)
      hS.uniq.ne_one h2
  · exfalso
    obtain ⟨I⟩ := hI7
    refine false_of_aeIdentOn (by norm_num) I hOpS (fun α hα h => ?_) hKΩ h8K hS.uniq h2
    obtain ⟨y, hy, hy3, hyz, -, hnc⟩ := AE.e64_yElt hα h
    obtain ⟨x, hx, hxne⟩ := hnc true
    exact ⟨y, hy, hy3, hyz, x, hx, hxne⟩
  · exfalso
    exact false_of_aeIdent hn I hOpS hKΩ h8K hS.uniq h2
  · exfalso
    obtain ⟨I⟩ := hI8
    refine false_of_aeIdentOn (by norm_num) I hOpS (fun α hα h => ?_) hKΩ h8K hS.uniq h2
    obtain ⟨y, hy, hy3, hyz, -, hnc⟩ := e29_yElt hα h
    obtain ⟨x, hx, hxne⟩ := hnc true
    exact ⟨y, hy, hy3, hyz, x, hx, hxne⟩

theorem central_of_sec {K : Subgroup X} {t : X} (hS : Q8Sec X K t) (hEC : OddEC t)
    (hTD : NoCentFour K t) (hD : TC.Thin.ThmDAbsAt 3 X)
    (hoddQ : ∀ (Q : Type) [Group Q] [Finite Q],
      (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) →
        ∀ w : Q, orderOf w = 2 → Balance.oddCoreIn (Subgroup.centralizer ({w} : Set Q)) = ⊥)
    (hM2 : ∀ (Q : Type) [Group Q] [Finite Q],
      (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) →
        ∀ w : Q, orderOf w = 2 → ¬ IsPGroup 2 (Subgroup.centralizer ({w} : Set Q)))
    (hOut : TightInO2 t ∨ TwinE4 X ∨ LongFundSetE3 K t) : ∀ g : X, g * t = t * g := by
  rcases hOut with ⟨P, hPn, hP2, htP⟩ | hE4 | hLF
  · exact central_of_inO2 hS hEC hTD hD hPn hP2 htP
  · obtain ⟨Q, hG, f, hf, hker, hmod⟩ := hE4
    letI := hG
    haveI : Finite Q := Finite.of_surjective f hf
    by_cases htN : t ∈ f.ker
    · exact central_of_inO2 hS hEC hTD hD (inferInstance : f.ker.Normal) hker htN
    · exact (false_of_twinE4 hS.hyp hS.uniq (hS.quat K (CoreAssembly.mem_conjClass_self K)) hEC hTD f
        hf hker htN (hoddQ Q hmod) (hM2 Q hmod)).elim
  · exfalso
    obtain ⟨Λ, hΛ, -, -⟩ := hLF
    have hmem : tightCore K ∈ twinSet (CoreAssembly.conjClass (tightCore K)) (tightCore K) :=
      tightCore_mem_twinSet_of_twin (by rw [hS.tight]; exact hS.twin)
    exact false_of_isClassicalMember3 hEC (hΛ _ hmem).2

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516.Four
