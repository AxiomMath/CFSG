module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf64Adapt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf63Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf9Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

section C22

variable {n : ℕ}

theorem holder22C_mem_zpowers_invol {T : Type*} [Group T] {b a : T} (hb : b * b = 1)
    (ha : a ∈ Subgroup.zpowers b) : a = 1 ∨ a = b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hb
  have hk : b ^ k = b ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, hb2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hk, h]; simp
  · right; rw [hk, h]; simp

theorem holder22C_isPGroup_zpowers {T : Type*} [Group T] {x : T} (h : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : T) ^ 2 ^ 1 = 1
  rw [← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  rw [show ((2 : ℕ) : ℤ) = 2 from rfl, this, one_zpow]

theorem v3_class_of_layer (h4 : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) {K₄ : Subgroup Y}
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    {c : Y} (hc : c ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y)) :
    ∃ γ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), c * t * c⁻¹ = γ * t * γ⁻¹ := by
  classical
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  have hz3 : IsUniqueInvolution K₃ t := hd.hzK₃
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have hM' : conjSub c K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hc hmem
  obtain ⟨htC, htY, hinv3⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem hz3
  obtain ⟨htC4, htY4, hinv4⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem4 hz4
  obtain ⟨htcC, htcY, hinvc⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hM' (hz3.conj c)
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  have hp3 := v3_perp_tq hStd hd.hK₃ hF.1 (Ne.symm hF.2.2.2.1) hd.hK₃K hd.hK₃K' hF.2.1 hF.2.2.1
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3 J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have h4' := h4 _ hlt _ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcA : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      (¬ ∃ g : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub g (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) = M) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hnot
    have hMA : M ≠ secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ :=
      fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA
      (h4' _ (secImg_mem_secFam hmem) M hM hnot))
  obtain ⟨xb, hxb⟩ : ∃ xb : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      (QuotientGroup.mk (⟨⟨c * t * c⁻¹, htcC⟩, htcY⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =
      xb * (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ :
          ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) * xb⁻¹ := by
    by_cases hconj : ∃ g : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub g (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) =
          secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) (conjSub c K₃)
    · obtain ⟨g, hg⟩ := hconj
      refine ⟨g, ?_⟩
      have h1 := hinv3.conj g
      rw [hg] at h1
      exact hinvc.eq h1
    · refine ⟨1, ?_⟩
      have hM'A' := hcA _ (secImg_mem_secFam hM') hconj
      have h1 := hinv4
      rw [← hM'A'] at h1
      rw [one_mul, inv_one, mul_one]
      exact hinvc.eq h1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  set t₂ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) := ⟨⟨t, htC⟩, htY⟩ with ht₂
  set tc₂ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    ⟨⟨c * t * c⁻¹, htcC⟩, htcY⟩ with htc₂
  have ht₂sq : t₂ * t₂ = 1 := Subtype.ext (Subtype.ext hz3.sq)
  have htc₂sq : tc₂ * tc₂ = 1 := Subtype.ext (Subtype.ext (hz3.conj c).sq)
  have htc₂ne : tc₂ ≠ 1 := by
    intro h
    exact (hz3.conj c).ne_one (congrArg (fun w : ↥(coreHull (CoreAssembly.conjClass (tightCore R))
      (u₁ * u₂)) => (((w : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y)) ) h)
  have hxtsq : (x * t₂ * x⁻¹) * (x * t₂ * x⁻¹) = 1 := by
    calc (x * t₂ * x⁻¹) * (x * t₂ * x⁻¹) = x * (t₂ * t₂) * x⁻¹ := by group
      _ = 1 := by rw [ht₂sq]; group
  have hP2 : IsPGroup 2 (Subgroup.zpowers tc₂) := holder22C_isPGroup_zpowers htc₂sq
  have hQ2 : IsPGroup 2 (Subgroup.zpowers (x * t₂ * x⁻¹)) := holder22C_isPGroup_zpowers hxtsq
  have hmk : (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) tc₂ =
      (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) (x * t₂ * x⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact hxb
  have hmapPQ : (Subgroup.zpowers tc₂).map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) =
      (Subgroup.zpowers (x * t₂ * x⁻¹)).map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hmk]
  obtain ⟨n, -, hn⟩ := exists_conj_of_isPGroup_map_eq hNodd hP2 hQ2 hmapPQ
  have hmem' : n * tc₂ * n⁻¹ ∈ Subgroup.zpowers (x * t₂ * x⁻¹) := by
    rw [← hn]
    exact conj_mem_conjSub (Subgroup.mem_zpowers tc₂)
  have hnx : n * tc₂ * n⁻¹ = x * t₂ * x⁻¹ := by
    rcases holder22C_mem_zpowers_invol hxtsq hmem' with h | h
    · exfalso
      apply htc₂ne
      have : tc₂ = n⁻¹ * (n * tc₂ * n⁻¹) * n := by group
      rw [this, h]; group
    · exact h
  have hfin : tc₂ = (n⁻¹ * x) * t₂ * (n⁻¹ * x)⁻¹ := by
    calc tc₂ = n⁻¹ * (n * tc₂ * n⁻¹) * n := by group
      _ = n⁻¹ * (x * t₂ * x⁻¹) * n := by rw [hnx]
      _ = (n⁻¹ * x) * t₂ * (n⁻¹ * x)⁻¹ := by group
  refine ⟨(((n⁻¹ * x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
      ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y), ?_, ?_⟩
  · exact coreHull_map_le_rLayer hΩ hc2
      ⟨((n⁻¹ * x : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
        ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))), (n⁻¹ * x).2, rfl⟩
  · have := congrArg (fun w : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =>
      (((w : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y))) hfin
    simpa [tc₂, t₂] using this

theorem centU3_of_layerNorm (h4 : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) {K₄ : Subgroup Y}
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (hNd : rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y)) :
    Subgroup.centralizer ({u₁ * u₂} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) := by
  intro c hc
  obtain ⟨γ, hγL, hct⟩ := v3_class_of_layer h4 hStd hF hc
  have hγC : γ ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    Asc77.rLayer_le_centralizer _ _ hγL
  have hcm : Commute (u₁ * u₂) c := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hcg : Commute (u₁ * u₂) γ := (Subgroup.mem_centralizer_singleton_iff.mp hγC).symm
  have hdt : (γ⁻¹ * c) * t * (γ⁻¹ * c)⁻¹ = t := by
    have : (γ⁻¹ * c) * t * (γ⁻¹ * c)⁻¹ = γ⁻¹ * (c * t * c⁻¹) * γ := by group
    rw [this, hct]; group
  have hdc : Commute (u₁ * u₂) (γ⁻¹ * c) := hcg.inv_right.mul_right hcm
  have hdu : (γ⁻¹ * c) * (u₁ * u₂) * (γ⁻¹ * c)⁻¹ = u₁ * u₂ := by
    have h := hdc.eq
    calc (γ⁻¹ * c) * (u₁ * u₂) * (γ⁻¹ * c)⁻¹ = ((u₁ * u₂) * (γ⁻¹ * c)) * (γ⁻¹ * c)⁻¹ := by
          rw [← h]
      _ = u₁ * u₂ := by group
  have hdN : (γ⁻¹ * c) ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) := by
    apply mem_normalizer_of_conjSub_eq
    rw [← alphaOf_conjSub, T7A.conjSub_closure_pair, hdu, hdt]
  have := Subgroup.mul_mem _ (hNd hγL) hdN
  simpa using this

@[expose] def V3LayerGenAllC (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₃ a₄ y : Y), V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), u₁ ∈ W → u₂ ∈ W → a₃ ∈ W → a₄ ∈ W →
          rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
            ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({t} : Set Y)) ⊔
              (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({y * t * y⁻¹} : Set Y))) ⊔
              oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))

theorem v3LayerNormFrAllC (hS : V3Hyp51StarF n) (hG : V3LayerGenAllC n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    {K₄ : Subgroup Y} {a₃ a₄ y : Y} (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y)
    {W : Subgroup Y} (hWs : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (hWu₁ : u₁ ∈ W)
    (hWu₂ : u₂ ∈ W) (hWa₃ : a₃ ∈ W) (hWa₄ : a₄ ∈ W) :
    rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) := by
  have hK₄ := fr.hK₄
  have h43 := fr.h43
  have h3 := fr.h3
  have o3 := fr.o3
  have h4' := fr.h4
  have o4 := fr.o4
  have c13 := fr.c13
  have c14 := fr.c14
  have c23 := fr.c23
  have c24 := fr.c24
  have c34 := fr.c34
  have hy := fr.hy
  have hne := fr.hne
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hz : IsUniqueInvolution K t := hd.hz
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hB := hS Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ u₁ u₂ a₃ a₄ y hK₄ fr.h41 fr.h42 fr.h43 hd.hu₁.1 hd.hu₁.2 hd.hu₂.1
    hd.hu₂.2 h3 o3 h4' o4 hd.comm₁₂ c13 c14 c23 c24 c34 hy hne fr.hyc fr.hj
  have hge := hG Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr W hWs hWu₁ hWu₂ hWa₃ hWa₄
  have e3 : a₃ * a₃ = t := T7A.sq_eq_of_orderOf_four hd.hzK₃ h3 o3
  have e4 : a₄ * a₄ = t := T7A.sq_eq_of_orderOf_four hz4 h4' o4
  have hv : a₃ * a₄ ≠ 1 := by
    intro h
    have hinv : a₄ = a₃⁻¹ := eq_inv_of_mul_eq_one_right h
    have : a₄ ∈ K₃ := hinv ▸ K₃.inv_mem h3
    exact A7T22.Hyp22Core.not_mem_of_orderOf_four hΩ hd.hK₃.1 hK₄.1 h43 o4 this h4'
  have hv2 : (a₃ * a₄) * (a₃ * a₄) = 1 := by
    calc (a₃ * a₄) * (a₃ * a₄) = (a₃ * a₃) * (a₄ * a₄) := by
          rw [mul_assoc, ← mul_assoc a₄, ← c34]; group
      _ = 1 := by rw [e3, e4, hz.sq]
  have hcu3 : Commute (u₁ * u₂) a₃ := (show Commute u₁ a₃ from c13).mul_left (show Commute u₂ a₃ from c23)
  have hcu4 : Commute (u₁ * u₂) a₄ := (show Commute u₁ a₄ from c14).mul_left (show Commute u₂ a₄ from c24)
  have cuv : (u₁ * u₂) * (a₃ * a₄) = (a₃ * a₄) * (u₁ * u₂) := (hcu3.mul_right hcu4).eq
  have cut : (u₁ * u₂) * t = t * (u₁ * u₂) := by
    have h1 : Commute t u₁ := hd.comm_z₁
    have h2 : Commute t u₂ := hd.comm_z₂
    exact ((h1.symm).mul_left (h2.symm)).eq
  have hut : u₁ * u₂ ≠ t := by
    intro h
    have h1 : u₁ * u₂ = u₁ * u₁ := by rw [h, hd.sq₁]
    have h2 : u₂ = u₁ := mul_left_cancel h1
    exact A7T22.Hyp22Core.not_mem_of_orderOf_four hΩ hd.mem hd.hK'.1 hd.hne hd.hu₁.2 hd.hu₁.1
      (h2 ▸ hd.hu₂.1)
  have ht'1 : y * t * y⁻¹ ≠ 1 := by
    intro e
    apply hz.ne_one
    have : t = y⁻¹ * (y * t * y⁻¹) * y := by group
    rw [this, e]; group
  have ht' : y * t * y⁻¹ = (u₁ * u₂) * (a₃ * a₄) := by rw [hy]; group
  have hvu : a₃ * a₄ ≠ u₁ * u₂ := by
    intro h
    apply ht'1
    rw [ht', h, hd.sq_12]
  have hα := alpha_eq_of_star hB hd.sq_12 hz.sq hv2 hd.mul_ne_one hz.ne_one hv hut hvu cut cuv
  exact rLayer_le_normalizer_alpha_of_gen hd (t' := y * t * y⁻¹) (by rw [ht']; exact hα) hge

theorem v3CentUFrAllC (h4 : Thm4RTwinBelow 3 n) (hαF : V3FourthAlphaF n) (hS : V3Hyp51StarF n)
    (hG : V3LayerGenAllC n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    {K₄ : Subgroup Y} {a₃ a₄ y : Y} (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y)
    {W : Subgroup Y} (hWs : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (hWu₁ : u₁ ∈ W)
    (hWu₂ : u₂ ∈ W) (hWa₃ : a₃ ∈ W) (hWa₄ : a₄ ∈ W) :
    Subgroup.centralizer ({u₁ * u₂} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) : Set Y) :=
  centU3_of_layerNorm h4 hStd (fr.fourthTwin hαF hStd)
    (v3LayerNormFrAllC hS hG hStd fr hWs hWu₁ hWu₂ hWa₃ hWa₄)

end C22

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
