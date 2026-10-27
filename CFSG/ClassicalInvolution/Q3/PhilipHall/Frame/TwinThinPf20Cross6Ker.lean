module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf20Cross6Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Iface
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossSetting

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

theorem conjSub_le_centralizer' {A B : Subgroup G} (n : G)
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    conjSub n A ≤ Subgroup.centralizer (conjSub n B : Set G) := by
  intro x hx y hy
  rw [mem_conjSub_iff] at hx
  have hy' : n⁻¹ * y * n ∈ B := mem_conjSub_iff.mp hy
  have h1 := Subgroup.mem_centralizer_iff.mp (h hx) _ hy'
  calc y * x = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
    _ = x * y := by group

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem eq_one_of_cent_both (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {y : G}
    (hyX : ∀ x ∈ piGen π, y * x = x * y) (hyX' : ∀ x ∈ conjSub g (piGen π), y * x = x * y) :
    y = 1 := by
  have hgen := (graph_17_10 S.hos.graph S.hK S.hπ).generate (iSup_conjClass_eq_top S.hs.gen) g S.hg
  have hle : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.centralizer {y} := by
    refine iSup₂_le fun M hM => ?_
    rcases hM with hM | ⟨M0, hM0, rfl⟩
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hyX x (le_piGen hM hx)).symm
    · have hMX : conjSub g M0 ≤ conjSub g (piGen π) := conjSub_mono (le_piGen hM0)
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hyX' x (hMX hx)).symm
  rw [hgen] at hle
  have hcz : y ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top x))
  rw [InductionBridge.center_eq_bot_of_fstar_simple hS hnab, Subgroup.mem_bot] at hcz
  exact hcz

theorem centralizes_of_trivial_action {P : Set (Subgroup G)}
    (hPΩ : P ⊆ CoreAssembly.conjClass K₀) {n : ℕ} (hn : 5 ≤ n) (I : AEIdent P n)
    (hk : IsPGroup 2 I.φ.ker) {y : G} (hyP : ∀ M ∈ P, conjSub y M ∈ P)
    (htriv : ∀ x y' : ↥(pSpan P), (y' : G) = y * x * y⁻¹ → I.φ y' = I.φ x) :
    ∀ M ∈ P, ∀ l ∈ M, y * l = l * y := by
  intro M hM l hl
  have hMy : conjSub y M = M := by
    refine S.eq_of_map_le_gen hPΩ hn I hk (hyP M hM) hM ?_
    rintro _ ⟨⟨x, hxP⟩, hx, rfl⟩
    have hx' : x ∈ conjSub y M := Subgroup.mem_subgroupOf.mp hx
    rw [mem_conjSub_iff] at hx'
    have hl'P : y⁻¹ * x * y ∈ pSpan P := le_pSpan hM hx'
    have := htriv ⟨y⁻¹ * x * y, hl'P⟩ ⟨x, hxP⟩ (by show x = y * (y⁻¹ * x * y) * y⁻¹; group)
    rw [this]
    exact I.mem_map hM hx'
  have hyl : y * l * y⁻¹ ∈ M := by
    have : y * l * y⁻¹ ∈ conjSub y M := conj_mem_conjSub hl
    rwa [hMy] at this
  have himg := htriv ⟨l, le_pSpan hM hl⟩ ⟨y * l * y⁻¹, le_pSpan hM hyl⟩ rfl
  obtain ⟨α, h, b, hlab⟩ := I.label M hM
  have heq : y * l * y⁻¹ = l :=
    I.injOn hn hM (S.card8 M (hPΩ hM)) hlab hyl hl himg
  calc y * l = (y * l * y⁻¹) * y := by group
    _ = l * y := by rw [heq]

theorem ker_of_chart (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {P : Set (Subgroup G)} {n : ℕ}
    (hn : 8 ≤ n) (hAut : TwinThinPf8.AEAut n) (hnb : NbrPiTwin K₀ K K' π g)
    (hPΩ : P ⊆ CoreAssembly.conjClass K₀) (I : AEIdent P n) (hkI : IsPGroup 2 I.φ.ker)
    (hconjP : ∀ M ∈ P, ∀ x ∈ pSpan P, conjSub x M ∈ P)
    (hπP : ∀ M ∈ π, M ∈ P) (hKg : conjSub g K ∈ P) {k : G} (hkmem : k ∈ conjSub g (piGen π))
    (hkX' : ∀ x ∈ conjSub g (piGen π), k * x = x * k)
    (hkN : k ∈ Subgroup.normalizer (pSpan P : Set G)) (hkP : ∀ M ∈ P, conjSub k M ∈ P) :
    k = 1 ∨ k = g * z * g⁻¹ := by
  classical
  have hn5 : 5 ≤ n := by omega
  obtain ⟨w, hw⟩ := Cross.exists_induced hn5 hAut I hkN hkP
  obtain ⟨β', hβ', c, hlabKg⟩ := I.label _ hKg
  have hKgC : conjSub g K ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) :=
    conjSub_le_centralizer' g S.pair_le_cent.1
  have hK'gC : conjSub g K' ≤ Subgroup.centralizer (conjSub g (piGen π) : Set G) :=
    conjSub_le_centralizer' g S.pair_le_cent.2
  have hcentK : ∀ l ∈ conjSub g K, k * l = l * k := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hKgC hl) _ hkmem
  have hcentM : ∀ M ∈ P,
      (∀ x ∈ (M.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ AE.memBar β' hβ' c, x * y = y * x) →
      ∀ l ∈ M, k * l = l * k := by
    intro M hM hcomm l hl
    by_cases hMK : M = conjSub g K
    · subst hMK
      exact hcentK l hl
    · have hc1 : ∀ x ∈ M, ∀ y ∈ conjSub g K, x * y = y * x :=
        S.commutes_of_map_comm_gen hPΩ I hkI hM hKg hMK (by
          intro x hx y hy
          rw [hlabKg] at hy
          exact hcomm x hx y hy)
      have hnbr : M ∈ omegaNbr (CoreAssembly.conjClass K₀) (conjSub g K) :=
        MuTab.mem_omegaNbr_of_commutes (hPΩ hM) hMK (fun a ha b hb => (hc1 b hb a ha).symm)
      have h1 := Asc77.omegaNbr_conj S.hs.hyp.conjInvariant hnbr g⁻¹
      rw [conjSub_inv_conjSub] at h1
      rcases hnb.1 _ h1 with h2 | h2
      · have hMX : M ≤ conjSub g (piGen π) := by
          have := conjSub_mono (n := g) (le_piGen h2)
          rwa [conjSub_conjSub_inv] at this
        exact hkX' l (hMX hl)
      · have hMeq : M = conjSub g K' :=
          calc M = conjSub g (conjSub g⁻¹ M) := (conjSub_conjSub_inv g M).symm
            _ = conjSub g K' := by rw [h2]
        rw [hMeq] at hl
        exact Subgroup.mem_centralizer_iff.mp (hK'gC hl) _ hkmem
  have hcentφ : ∀ M ∈ P, (∀ l ∈ M, k * l = l * k) →
      ∀ x ∈ (M.subgroupOf (pSpan P)).map I.φ, AE.mkQ n w * x = x * AE.mkQ n w := by
    intro M hM hMk x hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hM hx
    have := hw.cent (x := ⟨l, le_pSpan hM hl⟩) (hMk l hl)
    exact mul_inv_eq_iff_eq_mul.mp this
  have himgcomm : ∀ (δ : Finset (Fin n)) (hδ : δ.card = 4) (c' : Bool),
      (∀ x ∈ AE.memBar δ hδ c', ∀ y ∈ AE.memBar β' hβ' c, x * y = y * x) →
      ∀ x ∈ AE.memBar δ hδ c', AE.mkQ n w * x = x * AE.mkQ n w := by
    intro δ hδ c' hc x hx
    obtain ⟨M, hM, hlabM⟩ := I.label_surj δ hδ c'
    refine hcentφ M hM (hcentM M hM ?_) x (by rw [hlabM]; exact hx)
    rw [hlabM]
    exact hc
  have htwinc : ∀ c₁ c₂ : Bool, c₁ ≠ c₂ → ∀ x ∈ AE.memBar β' hβ' c₁, ∀ y ∈ AE.memBar β' hβ' c₂,
      x * y = y * x := by
    intro c₁ c₂ hne
    cases c₁ <;> cases c₂
    · exact absurd rfl hne
    · intro x hx y hy
      exact (comm_memBar_twin β' hβ' y hy x hx).symm
    · exact comm_memBar_twin β' hβ'
    · exact absurd rfl hne
  have hmain : AE.mkQ n w = 1 ∨ AE.mkQ n w = AE.zBar β' hβ' := by
    refine TwinThinPf20.eq_one_or_zBar_of_cent hn β' hβ' w ?_ ?_
    · intro c' x hx
      by_cases hcc : c' = c
      · subst hcc
        exact hcentφ _ hKg hcentK x (by rw [hlabKg]; exact hx)
      · exact himgcomm β' hβ' c' (htwinc c' c hcc) x hx
    · intro δ hδ hd c' x hx
      exact himgcomm δ hδ c' (AE.comm_memBar_of_disjoint hd c' c) x hx
  have hzg : g * z * g⁻¹ ∈ conjSub g K := conj_mem_conjSub S.hz.mem
  have hzgP : g * z * g⁻¹ ∈ pSpan P := le_pSpan hKg hzg
  have hφzg : I.φ ⟨g * z * g⁻¹, hzgP⟩ = AE.zBar β' hβ' :=
    I.map_eq_zBar hn5 hKg (S.card8 _ (hPΩ hKg)) hlabKg (S.hz.conj g)
  have hzgX' : ∀ x ∈ conjSub g (piGen π), (g * z * g⁻¹) * x = x * (g * z * g⁻¹) := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hKgC hzg) x hx).symm
  have hpi : piGen π ≤ pSpan P := iSup₂_le fun M hM => le_pSpan (hπP M hM)
  have hXall' : ∀ y : G, (∀ M ∈ P, ∀ l ∈ M, y * l = l * y) → ∀ x ∈ piGen π, y * x = x * y := by
    intro y hL x hx
    have hle : pSpan P ≤ Subgroup.centralizer {y} :=
      pSpan_le fun M hM l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hL M hM l hl).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (hpi hx))).symm
  rcases hmain with h1 | h1
  · left
    have hL : ∀ M ∈ P, ∀ l ∈ M, k * l = l * k :=
      S.centralizes_of_trivial_action hPΩ hn5 I hkI hkP (by
        intro x y' hy'
        rw [hw x y' hy', h1]
        simp)
    exact S.eq_one_of_cent_both hS hnab (hXall' _ hL) hkX'
  · right
    have hyP : ∀ M ∈ P, conjSub ((g * z * g⁻¹)⁻¹ * k) M ∈ P := by
      intro M hM
      rw [conjSub_mul]
      exact hconjP _ (hkP M hM) _ ((pSpan P).inv_mem hzgP)
    have htriv : ∀ x y' : ↥(pSpan P),
        (y' : G) = ((g * z * g⁻¹)⁻¹ * k) * x * ((g * z * g⁻¹)⁻¹ * k)⁻¹ → I.φ y' = I.φ x := by
      intro x y' hy'
      have hx₁ : k * x * k⁻¹ ∈ pSpan P := TwinThinPf.conj_mem_of_normalizer hkN x.2
      have e2 := hw x ⟨k * x * k⁻¹, hx₁⟩ rfl
      have e : y' = (⟨g * z * g⁻¹, hzgP⟩ : ↥(pSpan P))⁻¹ * ⟨k * x * k⁻¹, hx₁⟩ *
          ⟨g * z * g⁻¹, hzgP⟩ := by
        apply Subtype.ext
        rw [hy']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e, map_mul, map_mul, map_inv, e2, hφzg, h1]
      group
    have hL := S.centralizes_of_trivial_action hPΩ hn5 I hkI hyP htriv
    have hX'all : ∀ x ∈ conjSub g (piGen π),
        ((g * z * g⁻¹)⁻¹ * k) * x = x * ((g * z * g⁻¹)⁻¹ * k) := by
      intro x hx
      have hc : Commute (g * z * g⁻¹) x := hzgX' x hx
      calc ((g * z * g⁻¹)⁻¹ * k) * x = (g * z * g⁻¹)⁻¹ * (k * x) := by group
        _ = (g * z * g⁻¹)⁻¹ * (x * k) := by rw [hkX' x hx]
        _ = ((g * z * g⁻¹)⁻¹ * x) * k := by group
        _ = (x * (g * z * g⁻¹)⁻¹) * k := by rw [hc.inv_left.eq]
        _ = x * ((g * z * g⁻¹)⁻¹ * k) := by group
    have hy1 := S.eq_one_of_cent_both hS hnab (hXall' _ hL) hX'all
    exact (inv_mul_eq_one.mp hy1).symm

theorem ker_le_zpowers (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {m : ℕ} (hm : 8 ≤ m)
    (hAut : TwinThinPf8.AEAut m) (hnb : NbrPiTwin K₀ K K' π g)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    ∀ k ∈ J.φ.ker.map (pSpan (fam K (conjSub g (piGen π)))).subtype,
      k = 1 ∨ k = g * z * g⁻¹ := by
  classical
  have hm5 : 5 ≤ m := by omega
  rintro _ ⟨k₀, hk₀, rfl⟩
  have hkc := Subgroup.mem_center_iff.mp (J.ker_le hk₀)
  have hkX' : ∀ x ∈ conjSub g (piGen π), (k₀ : G) * x = x * (k₀ : G) := by
    intro x hx
    have hxp : x ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact hx
    exact (congrArg Subtype.val (hkc ⟨x, hxp⟩)).symm
  have hk₀X' : (k₀ : G) ∈ conjSub g (piGen π) := by
    exact (SetLike.ext_iff.mp S.fam_gen (k₀ : G)).mp k₀.2
  have hkC : (k₀ : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hkX' z (S.hKX S.hz.mem))
  have hQπ := S.Q_eq_pi
  have hPQ := S.pSpan_conj_fam
  have hPΩ : conjSub g⁻¹ '' fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ := by
    intro M hM
    rw [hQπ] at hM
    exact S.mem_conjClass_of_mem_pi hM
  have hOX : classicalInvolutionOddCore
      ↥(pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π)))) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (pSpanConj g⁻¹ _) S.hOdd
  have hk2 : IsPGroup 2 (J.conjX g⁻¹).φ.ker := (J.conjX g⁻¹).isPGroup_ker hOX
  have hvN : (k₀ : G) ∈ Subgroup.normalizer
      (pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))) : Set G) := by
    rw [hPQ]
    exact S.hos.centralizer_le_normalizer_piGen S.hK S.hπ S.hH1 S.hz hkC
  have hvP : ∀ M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)),
      conjSub (k₀ : G) M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
    intro M hM
    rw [hQπ] at hM ⊢
    exact S.conj_pi_of_cent hkC hM
  have hKg : conjSub g K ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
    rw [hQπ]; exact S.hg
  have hconjP : ∀ M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)),
      ∀ x ∈ pSpan (conjSub g⁻¹ '' fam K (conjSub g (piGen π))),
      conjSub x M ∈ conjSub g⁻¹ '' fam K (conjSub g (piGen π)) := by
    intro M hM x hx
    rw [hQπ] at hM ⊢
    rw [hPQ] at hx
    exact stable_of_maxOrb S.hos.graph S.hπ x hx M hM
  exact S.ker_of_chart hS hnab hm hAut hnb hPΩ (J.conjX g⁻¹) hk2 hconjP
    (fun M hM => by rw [hQπ]; exact hM) hKg hk₀X' hkX' hvN hvP

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
