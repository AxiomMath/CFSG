module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DQS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Bnd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265DL28Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6FixHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTDistinct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

@[expose] def CF28 : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω),
    QSNL p S B T x D K → p = 3 → catalogIs (PSimple p K) tyL28 →
      catalogIs (PSimple p S) (S10.isU6n 1)

theorem u6RankFact_holds :
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω), CFSG.Open.IsQuasisimple ↥S →
      GLAPPrimeCore 3 ↥S = ⊥ → catalogIs (PSimple 3 S) (S10.isU6n 1) →
      ∃ E : Subgroup Ω, E ≤ S ∧ IsElemAbelian 3 E ∧
        3 ^ 4 * Nat.card ↥(E ⊓ Subgroup.centralizer (S : Set Ω)) ≤ Nat.card E := by
  intro Ω _ _ S hS _ hS6
  obtain ⟨i, hi, ⟨θ⟩⟩ := hS6
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at hi
  | alternating m hm => simp [S10.isU6n, onLie] at hi
  | sporadic s => simp [S10.isU6n, onLie] at hi
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S10.isU6n, onLie] at hi
    split at hi
    · rename_i q
      exact S171.extremalRank_u6 hS hi.1 (hi.2 ▸ odd_one) θ
    · exact absurd hi id

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem exists_big_E {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hS6 : catalogIs (PSimple 3 S) (S10.isU6n 1)) :
    ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ E ≤ S ⊔ Subgroup.zpowers x ∧ 3 ^ 5 ≤ Nat.card E := by
  have hR := u6RankFact_holds
  have cfg := h.cfg
  obtain ⟨E₀, hE₀S, hE₀, hE₀c⟩ := hR Ω S cfg.quasi cfg.core hS6
  exact exists_big_elem_abelian hE₀S hE₀ (cfg.elem.2 x cfg.xB) cfg.x1 cfg.xcen hE₀c

theorem s265d_false_of_central_commutators {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hBle : Nat.card B ≤ 3 ^ 4) {E : Subgroup Ω}
    (hEel : IsElemAbelian 3 E) (hEle : E ≤ S ⊔ Subgroup.zpowers x) (hE5 : 3 ^ 5 ≤ Nat.card E)
    (hmax : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hcomm : ∀ t ∈ T, ∀ b ∈ B, ⁅t, b⁆ ∈ centModSubgroup 3 S) : False := by
  have cfg := h.cfg
  have hTB : (⁅T, B⁆ : Subgroup Ω) ≤ T := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    have hb' := (Subgroup.mem_normalizer_iff.1 (cfg.bnorm hb) t⁻¹).1 (T.inv_mem ht)
    rw [commutatorElement_def]
    have : t * b * t⁻¹ * b⁻¹ = t * (b * t⁻¹ * b⁻¹) := by group
    rw [this]
    exact T.mul_mem ht hb'
  have hTB2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) := cfg.two.to_le hTB
  have hTBc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro t ht b hb
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (S267.ModelGen.comm_of_mem_centMod cfg.normal cfg.core (hcomm t ht b hb) hs).symm
  have hSN : S ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.le_centralizer_iff.1 hTBc).trans (Subgroup.centralizer_le_normalizer _)
    · exact (Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 cfg.xcen)).trans
        (Subgroup.center_le_normalizer _)
  have h1 := card_le_pow_glaTwoLocalRank Nat.prime_three hEel hmax hTB2 (hEle.trans hSN)
  have h2 := cfg.rank
  omega

section Main


theorem not_l28_of_u4_or_u5 {R : Type} [Group R] [Finite R] (h1 : catalogIs R S10.isL2eight)
    (h2 : catalogIs R (fun i => S9.isU4two i ∨ S9.isU5two i)) : False := by
  have hb : CatDistinct.OrderBridge :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have c1 := KSubT.card_isL2eight hb h1
  obtain ⟨i, hi, ⟨e⟩⟩ := h2
  rcases hi with hi | hi
  · have c2 := CFSG.LocalAnalysis.GLTheoremA.CatB.U48.card_of_isU4two ⟨i, hi, ⟨e⟩⟩
    omega
  · have c2 := CatDistinct.card_isU5two hb ⟨i, hi, ⟨e⟩⟩
    omega

private theorem catalogIs_of_equiv {X Y : Type} [Group X] [Group Y] {Q : TauCeti.CFSGIndex → Prop}
    (e : X ≃* Y) (h : catalogIs X Q) : catalogIs Y Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem false_of_noncentral_commutator {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSNL 3 S B T x D K) (hS6 : catalogIs (PSimple 3 S) (S10.isU6n 1))
    (hL : catalogIs (PSimple 3 K) tyL28) (hBge : 3 ^ 4 ≤ Nat.card B)
    (hnc : ∃ t ∈ T, ∃ b ∈ B, ⁅t, b⁆ ∉ centModSubgroup 3 S) : False := by
  have cfg := h.cfg
  have hKdvd : 3 ∣ Nat.card K := three_dvd_card_of_l28 hL
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 cfg.normal) ▸ Subgroup.mem_top g
  let ι : Ω →* ↥(Subgroup.normalizer (S : Set Ω)) :=
    MonoidHom.codRestrict (MonoidHom.id Ω) (Subgroup.normalizer (S : Set Ω)) hSN
  let ψ : Ω →* MulAut (PSimple 3 S) := (chevAut 3 S).comp ι
  have hψ : ∀ g : Ω, ψ g = chevAut 3 S ⟨g, hSN g⟩ := fun g => rfl
  have hψ1 : ∀ g : Ω, ψ g = 1 ↔ g ∈ centModSubgroup 3 S := fun g => by
    rw [hψ, chevAut_eq_one_iff Nat.prime_three cfg.comp (hSN g), centMod_iff]
  have hT2 : IsPGroup 2 (T.map ψ) := cfg.two.map ψ
  have hAel : IsElemAbelian 3 (B.map ψ) := CFSG.SectionRank.isElemAbelian_map cfg.elem ψ
  have hnorm : ∀ a ∈ B.map ψ, ∀ τ ∈ T.map ψ, a * τ * a⁻¹ ∈ T.map ψ := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨b * t * b⁻¹, (Subgroup.mem_normalizer_iff.1 (cfg.bnorm hb) t).1 ht, ?_⟩
    simp [map_mul, map_inv]
  obtain ⟨t₀, ht₀, b₀, hb₀, hnc'⟩ := hnc
  have hnc2 : ∃ a ∈ B.map ψ, ∃ τ ∈ T.map ψ, a * τ ≠ τ * a := by
    refine ⟨ψ b₀, ⟨b₀, hb₀, rfl⟩, ψ t₀, ⟨t₀, ht₀, rfl⟩, fun hc => ?_⟩
    have h1 : ψ ⁅t₀, b₀⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc.symm
    exact hnc' ((hψ1 _).1 h1)
  have h4 : 4 ≤ Nat.card (T.map ψ) := four_le_card_of_noncomm hT2 hnorm hnc2
  obtain ⟨s, hs1, hsT⟩ := exists_conj_mem_two_subgroup hS6 (T.map ψ) hT2 h4
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian Nat.prime_three cfg.comp
  haveI := hsimple
  have hZ : Subgroup.center (PSimple 3 S) = ⊥ := chev_center_eq_bot_of_simple_nonabelian hnonab
  set T₀ : Subgroup (PSimple 3 S) :=
    (T.map ψ).comap (MulAut.conj : PSimple 3 S →* MulAut (PSimple 3 S)) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.InnerNormalizedAutomorphisms.isPGroup_comap_conj hZ hT2
  have hT₀ne : T₀ ≠ ⊥ :=
    (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨s, hsT⟩, fun h1 => hs1 (congrArg Subtype.val h1)⟩
  have hinv : ∀ α ∈ B.map ψ, ∀ y ∈ T₀, α y ∈ T₀ := by
    intro α hα y hy
    have hy' : (MulAut.conj y : MulAut (PSimple 3 S)) ∈ T.map ψ := hy
    show (MulAut.conj (α y) : MulAut (PSimple 3 S)) ∈ T.map ψ
    have e : (MulAut.conj (α y) : MulAut (PSimple 3 S)) = α * MulAut.conj y * α⁻¹ := by
      ext z
      simp [MulAut.conj_apply]
    rw [e]
    exact hnorm α hα _ hy'
  have hA27 : 3 ^ 3 ≤ Nat.card (B.map ψ) := by
    set φB : ↥B →* MulAut (PSimple 3 S) := ψ.comp B.subtype with hφB
    have hrange : φB.range = B.map ψ := by
      ext a
      simp [hφB, MonoidHom.mem_range, Subgroup.mem_map]
    have hmul := Subgroup.card_ker_mul_card_range φB
    rw [hrange] at hmul
    have hker : Nat.card φB.ker ≤ 3 := by
      have hle : φB.ker.map B.subtype ≤ Subgroup.zpowers x := by
        rintro _ ⟨b, hb, rfl⟩
        have h1 : ψ (b : Ω) = 1 := hb
        have hc : CentMod 3 S (b : Ω) := centMod_iff.2 ((hψ1 _).1 h1)
        exact (cfg.centB b b.2).1 hc
      calc Nat.card φB.ker = Nat.card (φB.ker.map B.subtype) :=
            (Subgroup.card_map_of_injective B.subtype_injective).symm
        _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
        _ ≤ 3 := by
          rw [Nat.card_zpowers]
          exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (cfg.elem.2 x cfg.xB))
    have h81 : 3 ^ 4 ≤ Nat.card φB.ker * Nat.card (B.map ψ) := hmul ▸ hBge
    have h2 := Nat.mul_le_mul_right (Nat.card (B.map ψ)) hker
    omega
  obtain ⟨d, hdD, hdx⟩ := S171.exists_y Nat.prime_three cfg.x1 cfg.std
  have hdB : d ∈ B := cfg.std.1 hdD
  have hαA : ψ d ∈ B.map ψ := ⟨d, hdB, rfl⟩
  have hα1 : ψ d ≠ 1 := fun h1 => hdx ((cfg.centB d hdB).1 (centMod_iff.2 ((hψ1 d).1 h1)))
  have hap : IsPGroup 3 (Subgroup.zpowers d) := isPGroup_zpowers_of_mem cfg.elem hdB
  have hLx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen s)
  have hJ : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d} : Set Ω)) K := by
    have hcomp := (h.nlAct hKdvd).comp
    rwa [S171.L_cs_eq Nat.prime_three cfg.x1 cfg.std hdD hdx hLx] at hcomp
  have hN : GLAPComponent 3 (fixSubgroup (ψ d)) (chevTransfer 3 S K) :=
    glaPComponent_chevTransfer Nat.prime_three (hSN d) hap hJ
  have hKU := kU6FixCompFact_holds (PSimple 3 S) hS6 (B.map ψ) T₀ hAel hA27 hT₀2 hT₀ne hinv
    (ψ d) hαA hα1 _ hN
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three (hSN d) hap hJ
  have hLN : catalogIs (PSimple 3 (chevTransfer 3 S K)) S10.isL2eight :=
    catalogIs_of_equiv e (catalogIs_imp (fun i hi => hi) hL)
  exact not_l28_of_u4_or_u5 hLN hKU

theorem qsFamDL28_of_cf28_rank (hC : CF28) : QSFamDL28 := by
  intro p Ω _ _ S B T x D K h hp3 hL
  subst hp3
  exfalso
  have cfg := h.cfg
  have hS6 := hC 3 Ω S B T x D K h rfl hL
  have hBle : Nat.card B ≤ 3 ^ 4 := card_B_le_of_l28 h hL
  obtain ⟨E, hEel, hEle, hE5⟩ := exists_big_E h hS6
  rcases cfg.maxc with hmax | ⟨hmaxE, -⟩
  · by_cases hcomm : ∀ t ∈ T, ∀ b ∈ B, ⁅t, b⁆ ∈ centModSubgroup 3 S
    · exact s265d_false_of_central_commutators h hBle hEel hEle hE5 hmax hcomm
    · push Not at hcomm
      exact false_of_noncentral_commutator h hS6 hL cfg.big hcomm
  · have := hmaxE E hEel
    omega

theorem qsFamDL28_of_cf28 (hC : CF28) : QSFamDL28 :=
  qsFamDL28_of_cf28_rank hC

theorem qsFamD_of_cf28_of_qsFamF3 (hC : CF28) (h : QSFamF3) : QSFamD :=
  qsFamD_of_L28_of_qsFamF3 (qsFamDL28_of_cf28 hC) h

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265D

end
