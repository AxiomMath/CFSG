module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalEightTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalEightThree

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Eight

open SectionSix SectionSix.BarTools SectionSix.Exclusion

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem not_altThree_eight (h3 : AschbacherTheorem3.Theorem3Statement)
    (hC : Counterexample G D r Abar) {a : Fin r} {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hTsyl : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G)))
    (hstar : ∀ y ∈ aschbacherThm5Preimage D (Abar a),
      y ∉ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G) →
      T ⊓ rightConjugate T y = ⊥)
    (hidx : ∀ Q : Subgroup G, Q ≤ aschbacherThm5Preimage D (Abar a) ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G) →
      IsPGroup 2 Q → Nat.card Q ≤ Nat.card T) :
    ¬ Thm3AltThree (bar D (aschbacherThm5Preimage D (Abar a))) (bar D T) := by
  intro halt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  obtain ⟨b, hba⟩ := Strong.exists_ne_index (two_le hC) a
  have hAD : A ≤ D := preimage_le D _
  have hAH : A ≤ H := hAD.trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hAb : A ≤ centralizing D (Abar b) := factor_le_centralizing hC.hyp.hcomm hba
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  have hTAg : T ≤ rightConjugate A g := hTsyl.le.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (A : Set G) := hTsyl.le.trans inf_le_right
  have hTH : T ≤ H := hTN.trans (normalizer_factor_le hC a)
  have hTA : T ⊓ A = ⊥ := inf_factor_eq_bot hC hg hTAg hT2
  have haq := quasisimple_of_altThree hC.hyp halt
  have hTC := bar_overlap_inf_centralizer hC hAb hg hTAg hT2 a
  have hTAbar : bar D T ⊓ bar D A = ⊥ := by
    rw [← bar_inf_of_core_le hOA, hTA, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  obtain ⟨n, hn, ⟨e⟩, Ob, Pb, hOb, hObcard, hObC, hObA, -, hPb, hPbcard, hTOP, hTcard⟩ :=
    Linear.decode_altThree haq (bar_le_normalizer hTN hAH) (isPGroup_bar hT2) hTAbar hTC halt
  obtain ⟨V, hTV, hVH, hVel, hVcard, hVbar, hPcard, hUcard, hTcard', hUP, hTU, hYU, htrans⟩ :=
    lifted_config hT2 hTH haq hn e hOb hObcard hObC hObA hPb hPbcard hTOP hTcard hTC
  set P := V ⊓ A with hPdef
  set U := V ⊓ centralizerIn D A with hUdef
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := n + n) (by rw [hVcard, pow_add])
  have hP2 : IsPGroup 2 P := hV2.to_le inf_le_left
  have hTP : T ⊓ P = ⊥ := le_bot_iff.mp ((inf_le_inf_left T inf_le_right).trans hTA.le)
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPH : P ≤ H := inf_le_left.trans hVH
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hTcard'
    omega
  have hPbar : bar D P = Pb := by
    have hOPb : Ob ≤ Subgroup.normalizer (Pb : Set (Bar D)) := by
      refine le_trans (fun o ho => ?_) (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.mem_centralizer_iff]
      exact fun p hp => (Subgroup.mem_centralizer_iff.mp (hObC ho)) p (hPb.le hp)
    rw [hPdef, bar_inf_of_core_le hOA, hVbar, sup_comm]
    exact Five.sup_inf_eq_of_le hPb.le hOPb hObA
  have : IsSimpleGroup (bar D A) := by
    have := psl_simple hn
    exact e.isSimpleGroup
  have hZ := center_eq_bot_of_simple haq
  obtain ⟨-, -, hself⟩ := Linear.psl_sylow_structure hn e hPb
  have hPHg : P ≤ rightConjugate H g := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hgtA : g * t * g⁻¹ ∈ A := (mem_rightConjugate_iff A g t).mp (hTAg t.2)
    obtain ⟨k, hk⟩ := hT2 t
    have hCH := centralizer_le hC b (t := g * t * g⁻¹) ⟨k, by
        rw [conj_pow, show ((t : G) ^ 2 ^ k) = 1 from congrArg Subtype.val hk]; group⟩
      (fun h => ht1' (by
        calc (t : G) = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group))
      (centralizes_of_mem_centralizing (hAb hgtA))
    intro x hx
    rw [mem_rightConjugate_iff]
    apply hCH
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxt := hVcomm x hx.1 t (hTV t.2)
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  have hTy : ∀ y ∈ V, rightConjugate T y = T := fun y hy => by
    apply (rightConjugate_eq_self_iff T y).mpr
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun t ht => hVcomm t (hTV ht) y hy
  have hPL : P ≤ Subgroup.normalizer (rightConjugate A g : Set G) := by
    intro p hp
    by_contra hpL
    have hbot := hstar p hp.2 hpL
    rw [hTy p hp.1, inf_idem] at hbot
    exact hT1 hbot
  have hPcard' : Nat.card P = Nat.card T := by rw [hPcard, hTcard']
  have hPsyl : IsSylowOf 2 P (A ⊓ Subgroup.normalizer (rightConjugate A g : Set G)) := by
    obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 (A ⊓ Subgroup.normalizer (rightConjugate A g : Set G))
    have hle : P ≤ A ⊓ Subgroup.normalizer (rightConjugate A g : Set G) :=
      le_inf inf_le_right hPL
    have h1 := AschbacherTheorem3.card_le_of_isSylowOf hQ hP2 hle
    have h2 := hidx Q hQ.le hQ.isPGroup
    refine isSylowOf_of_card hle ?_
    rw [← hQ.card_eq]
    omega
  have hPcyc : ¬ IsCyclic P := fun hcyc => by
    have := card_le_two_of_isCyclic hcyc (fun x hx => hVel.2 x hx.1)
    omega
  have hstar' : ∀ z ∈ rightConjugate A g, z ∉ Subgroup.normalizer (A : Set G) →
      P ⊓ rightConjugate P z = ⊥ := by
    intro z _ hzA
    rw [eq_bot_iff]
    intro p hp
    have hpP : p ∈ P := hp.1
    have hzp : z * p * z⁻¹ ∈ P := (mem_rightConjugate_iff P z p).mp hp.2
    rw [Subgroup.mem_bot]
    by_contra hp1
    obtain ⟨k, hk⟩ := hP2 ⟨p, hpP⟩
    have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hzH : z ∈ H := by
      refine mem_normalizer_of_fusion hC b b (t := z * p * z⁻¹) (g := z) ⟨k, ?_⟩ ?_
        (centralizes_of_mem_centralizing (hAb hzp.2)) ?_
      · rw [conj_pow, hpk]
        group
      · intro h
        apply hp1
        calc p = z⁻¹ * (z * p * z⁻¹) * z := by group
          _ = 1 := by rw [h]; group
      · rw [show z⁻¹ * (z * p * z⁻¹) * z = p by group]
        exact centralizes_of_mem_centralizing (hAb hpP.2)
    obtain ⟨j, hj⟩ := hC.hyp.hperm z⁻¹ (H.inv_mem hzH) a
    have hja : j ≠ a := by
      rintro rfl
      apply hzA
      exact (Subgroup.inv_mem_iff _).mp (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj)
    have hpj : p ∈ aschbacherThm5Preimage D (Abar j) := by
      rw [← hj]
      exact ⟨z * p * z⁻¹, hzp.2, by simp [mul_assoc]⟩
    have hpc := centralizes_of_mem_centralizing
      (factor_le_centralizing hC.hyp.hcomm (Ne.symm hja) hpj)
    have hpH : p ∈ H := hPH hpP
    have hpC := (centralizes_iff_mem_centralizer D A hAD ⟨p, hpH⟩).mp hpc
    have hcen : (⟨toBar D ⟨p, hpH⟩, toBar_mem_bar D (h := ⟨p, hpH⟩) hpP.2⟩ : bar D A) ∈
        Subgroup.center (bar D A) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hpC) w w.2)
    rw [hZ, Subgroup.mem_bot] at hcen
    have h1 : toBar D ⟨p, hpH⟩ = 1 := congrArg Subtype.val hcen
    exact hp1 (eq_one_of_mem_core_of_isPGroup hP2 hpP ((toBar_eq_one_iff D _).mp h1))
  have hidx' : ∀ Q : Subgroup G, Q ≤ rightConjugate A g ⊓ Subgroup.normalizer (A : Set G) →
      IsPGroup 2 Q → Nat.card Q ≤ Nat.card P := fun Q hQ hQ2 => by
    rw [hPcard']
    exact AschbacherTheorem3.card_le_of_isSylowOf hTsyl hQ2 hQ
  set D' := rightConjugate D g with hD'def
  set Abar' := conjFactors D Abar g with hAbar'def
  have hC' : Counterexample G D' r Abar' := hC.conj g
  set A' := aschbacherThm5Preimage D' (Abar' a) with hA'def
  have hA'eq : A' = rightConjugate A g := preimage_conjFactors D Abar g a
  have hA'g : rightConjugate A' g⁻¹ = A := by
    rw [hA'eq, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hH'eq : Subgroup.normalizer (D' : Set G) = rightConjugate H g :=
    normalizer_rightConjugate D g
  have hg' : g⁻¹ ∉ Subgroup.normalizer (D' : Set G) := by
    rw [hH'eq, mem_rightConjugate_iff, show g * g⁻¹ * g⁻¹ = g⁻¹ by group]
    intro h
    exact hg (by simpa using H.inv_mem h)
  have hPsyl' : IsSylowOf 2 P (rightConjugate A' g⁻¹ ⊓ Subgroup.normalizer (A' : Set G)) := by
    rw [hA'g, hA'eq]
    exact hPsyl
  have hstar'' : ∀ y ∈ A', y ∉ Subgroup.normalizer (rightConjugate A' g⁻¹ : Set G) →
      P ⊓ rightConjugate P y = ⊥ := by
    rw [hA'g, hA'eq]
    exact hstar'
  have hidx'' : ∀ Q : Subgroup G, Q ≤ A' ⊓ Subgroup.normalizer (rightConjugate A' g⁻¹ : Set G) →
      IsPGroup 2 Q → Nat.card Q ≤ Nat.card P := by
    rw [hA'g, hA'eq]
    exact hidx'
  have halt' : Thm3AltThree (bar D' A') (bar D' P) :=
    altThree_of_tight h3 hC' hg' hPsyl' hPcyc hstar'' hidx''
  have hA'H' : A' ≤ Subgroup.normalizer (D' : Set G) :=
    (preimage_le D' _).trans Subgroup.le_normalizer
  have hOA' : aschbacherThm5Core D' ≤ A' := core_le_preimage D' _
  have hA'b : A' ≤ centralizing D' (Abar' b) := factor_le_centralizing hC'.hyp.hcomm hba
  have haq' : CFSG.Open.IsQuasisimple (bar D' A') := quasisimple_conj haq g
  have hPH' : P ≤ Subgroup.normalizer (D' : Set G) := by
    rw [hH'eq]
    exact hPHg
  have hPA' : P ≤ Subgroup.normalizer (A' : Set G) := by
    rw [hA'eq]
    exact hPL
  have hPg : P ≤ rightConjugate A' g⁻¹ := by
    rw [hA'g]
    exact inf_le_right
  have hPA'bot : P ⊓ A' = ⊥ := inf_factor_eq_bot hC' hg' hPg hP2
  have hPC' := bar_overlap_inf_centralizer hC' hA'b hg' hPg hP2 a
  have hPAbar' : bar D' P ⊓ bar D' A' = ⊥ := by
    rw [← bar_inf_of_core_le hOA', hPA'bot, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  obtain ⟨n', hn', ⟨e'⟩, Ob', Pb', -, -, hOb'C, -, hPbdef', hPb', hPbcard', hPOP', hPcard''⟩ :=
    Linear.decode_altThree haq' (bar_le_normalizer hPA' hA'H') (isPGroup_bar hP2) hPAbar' hPC'
      halt'
  obtain ⟨-, -, hself'⟩ := Linear.psl_sylow_structure hn' e' hPb'
  have hTA' : T ≤ A' := by
    rw [hA'eq]
    exact hTAg
  have hTH' : T ≤ Subgroup.normalizer (D' : Set G) := hTA'.trans hA'H'
  have hTbar : bar D' T = Pb' := by
    have hOT' : Ob' ≤ Subgroup.centralizer (bar D' T : Set (Bar D')) :=
      hOb'C.trans (Subgroup.centralizer_le (bar_mono D' hTA'))
    have hPT' : bar D' P ≤ Subgroup.centralizer (bar D' T : Set (Bar D')) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := (mem_bar_iff D' P x).mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨t, ht, rfl⟩ := (mem_bar_iff D' T z).mp hz
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVcomm _ (hTV ht) _ hp.1)
    have hTC' : bar D' T ≤ Subgroup.centralizer (Pb' : Set (Bar D')) := by
      refine Subgroup.le_centralizer_iff.mpr ?_
      rw [hPbdef']
      exact inf_le_left.trans (sup_le hOT' hPT')
    have hle : bar D' T ≤ Pb' := (le_inf (bar_mono D' hTA') hTC').trans hself'
    apply Subgroup.eq_of_le_of_card_ge hle
    refine le_of_eq ?_
    rw [hPbcard', ← hPcard'', card_bar_of_isPGroup hP2 hPH', hPcard',
      card_bar_of_isPGroup hT2 hTH']
  set R := V ⊓ centralizerIn D' A' with hRdef
  have hPO' : Pb' ≤ Subgroup.normalizer (Ob' : Set (Bar D')) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact ((Subgroup.mem_centralizer_iff.mp (hOb'C ho)) q (hPb'.le hq)).symm
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    omega
  have hR1 : R ≠ ⊥ := by
    obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
    have hpH' : p ∈ Subgroup.normalizer (D' : Set G) := hPH' hp
    obtain ⟨o, ho, q, hq, hpoq⟩ :=
      product_mem_of_sup hPO' (hPOP' (toBar_mem_bar D' (h := ⟨p, hpH'⟩) hp))
    rw [← hTbar] at hq
    obtain ⟨t₀, ht₀, rfl⟩ := (mem_bar_iff D' T _).mp hq
    have hxH' : p * (t₀ : G)⁻¹ ∈ Subgroup.normalizer (D' : Set G) :=
      (Subgroup.normalizer (D' : Set G)).mul_mem hpH'
        ((Subgroup.normalizer (D' : Set G)).inv_mem t₀.2)
    have hx : toBar D' ⟨p * (t₀ : G)⁻¹, hxH'⟩ = o := by
      change toBar D' (⟨p, hpH'⟩ * t₀⁻¹) = o
      rw [map_mul, map_inv, hpoq, mul_inv_cancel_right]
    intro hbot
    have hmem : p * (t₀ : G)⁻¹ ∈ R :=
      ⟨V.mul_mem hp.1 (V.inv_mem (hTV ht₀)),
        (mem_centralizerIn_iff D' A' _).mpr ⟨hxH', hx ▸ hOb'C ho⟩⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    have hpTP : p ∈ T ⊓ P := ⟨by rw [hmem]; exact ht₀, hp⟩
    rw [hTP, Subgroup.mem_bot] at hpTP
    exact hp1' hpTP
  have hRU : R ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvV, hvR⟩, -, hvU⟩
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' v).mp hvR
    obtain ⟨hvH, hvc⟩ := (mem_centralizerIn_iff D A v).mp hvU
    have hc' := (centralizes_conj_iff D Abar g a v).mp
      ((centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨v, hvH'⟩).mpr hvc')
    have hc := (centralizes_iff_mem_centralizer D A (preimage_le D _) ⟨v, hvH⟩).mpr hvc
    obtain ⟨k, hk⟩ := hV2 ⟨v, hvV⟩
    apply hg
    refine mem_normalizer_of_fusion hC a a (t := g * v * g⁻¹) (g := g) ⟨k, ?_⟩ ?_ hc' ?_
    · rw [conj_pow, show v ^ 2 ^ k = 1 from congrArg Subtype.val hk]
      group
    · intro h
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
  have hRP : R ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvV, hvR⟩, -, hvA⟩
    rw [Subgroup.mem_bot]
    by_contra hv1
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' v).mp hvR
    have hc' := (centralizes_conj_iff D Abar g a v).mp
      ((centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨v, hvH'⟩).mpr hvc')
    have hc := centralizes_of_mem_centralizing (hAb hvA)
    obtain ⟨k, hk⟩ := hV2 ⟨v, hvV⟩
    apply hg
    refine mem_normalizer_of_fusion hC a b (t := g * v * g⁻¹) (g := g) ⟨k, ?_⟩ ?_ hc' ?_
    · rw [conj_pow, show v ^ 2 ^ k = 1 from congrArg Subtype.val hk]
      group
    · intro h
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
  have : IsSimpleGroup (bar D' A') := by
    have := psl_simple hn'
    exact e'.isSimpleGroup
  have hZ' := center_eq_bot_of_simple haq'
  have hRA' : ∀ v ∈ R, v ∈ A' → v = 1 := by
    intro v hv hvA'
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' _).mp hv.2
    have hc : (⟨toBar D' ⟨_, hvH'⟩, toBar_mem_bar D' hvA'⟩ : bar D' A') ∈
        Subgroup.center (bar D' A') := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hvc') z z.2)
    rw [hZ', Subgroup.mem_bot] at hc
    have h1 : toBar D' ⟨_, hvH'⟩ = 1 := congrArg Subtype.val hc
    exact eq_one_of_mem_core_of_isPGroup hV2 hv.1 ((toBar_eq_one_iff D' _).mp h1)
  have hRT0 : R ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.mpr (hRA' v hv.1 (hTA' hv.2))
  have hRcard : Nat.card R ≤ Nat.card T := by
    have h1 := card_mul_le_of_inf_eq_bot hVcomm inf_le_left hTV hRT0
    rw [hVcard, hTcard'] at h1
    rw [hTcard']
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hconjR : ∀ z ∈ Subgroup.normalizer (D' : Set G), z ∈ Subgroup.normalizer (V : Set G) →
      z ∉ Subgroup.normalizer (A' : Set G) → rightConjugate T z⁻¹ ≤ R := by
    intro z hzH' hzV hzA' x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have hxV : x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hzV (z⁻¹ * x * z)).mp (hTV hx)
      simpa [mul_assoc] using this
    obtain ⟨j, hj⟩ := hC'.hyp.hperm z hzH' a
    have hja : j ≠ a := by
      rintro rfl
      exact hzA' (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj)
    have hxj : x ∈ aschbacherThm5Preimage D' (Abar' j) := by
      rw [← hj]
      exact ⟨z⁻¹ * x * z, hTA' hx, by simp [mul_assoc]⟩
    have hxc := centralizes_of_mem_centralizing
      (factor_le_centralizing hC'.hyp.hcomm (Ne.symm hja) hxj)
    have hxH' : x ∈ Subgroup.normalizer (D' : Set G) :=
      ((preimage_le D' _).trans Subgroup.le_normalizer) hxj
    exact ⟨hxV, (mem_centralizerIn_iff D' A' x).mpr ⟨hxH',
      (centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨x, hxH'⟩).mp hxc⟩⟩
  have hyL : ∀ y ∈ A ⊓ Subgroup.normalizer (V : Set G),
      y ∈ Subgroup.normalizer (D' : Set G) → y ∈ Subgroup.normalizer (A' : Set G) := by
    rintro y ⟨hyA, hyNV⟩ hyH'
    by_contra hyA'
    have hyinvA' : y⁻¹ ∉ Subgroup.normalizer (A' : Set G) := fun h =>
      hyA' (by simpa using Subgroup.inv_mem _ h)
    have hR1' : rightConjugate T y⁻¹ = R := by
      refine Subgroup.eq_of_le_of_card_ge (hconjR y hyH' hyNV hyA') ?_
      rw [rightConjugate_card]
      exact hRcard
    have hR2' : rightConjugate T y = R := by
      have h := hconjR y⁻¹ (Subgroup.inv_mem _ hyH') (Subgroup.inv_mem _ hyNV) hyinvA'
      rw [inv_inv] at h
      refine Subgroup.eq_of_le_of_card_ge h ?_
      rw [rightConjugate_card]
      exact hRcard
    have hyyT : y * y ∈ Subgroup.normalizer (T : Set G) := by
      rw [← rightConjugate_eq_self_iff]
      calc rightConjugate T (y * y) = rightConjugate (rightConjugate T y) y :=
            (rightConjugate_mul T y y).symm
        _ = rightConjugate (rightConjugate T y⁻¹) y := by rw [hR2', hR1']
        _ = T := by rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    have hUT : Nat.card U * Nat.card T = Nat.card V := by rw [hUcard, hTcard', hVcard]
    have hcent := centralizes_of_sq_normalizes (a := a) hVH hV2 hVcomm inf_le_left hTV hTU hUT
      hTP (by rw [hPbar]; exact hPb) (by rw [hPbar]; exact hself) hyA hyNV
      (fun u hu => hYU y ⟨hyA, hyNV⟩ u hu) hyyT
    have hTyy : rightConjugate T y = T := by
      apply (rightConjugate_eq_self_iff T y).mpr
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
      have h1 := hcent t (hTV ht)
      calc t * y = (y * t * y⁻¹) * y := by rw [h1]
        _ = y * t := by group
    have hyL' : y ∉ Subgroup.normalizer (rightConjugate A g : Set G) := by
      rw [← hA'eq]
      exact hyA'
    have hbot := hstar y hyA hyL'
    rw [hTyy, inf_idem] at hbot
    exact hT1 hbot
  have hRT : ∀ y ∈ ((A ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G), ∀ t ∈ T,
      y * t * y⁻¹ ∈ R → y * t * y⁻¹ = 1 := by
    intro y hy t htT hv
    by_contra hv1
    obtain ⟨hvH', hvc'⟩ := (mem_centralizerIn_iff D' A' _).mp hv.2
    have hc'v := (centralizes_iff_mem_centralizer D' A' (preimage_le D' _) ⟨_, hvH'⟩).mpr hvc'
    have hgtA : g * t * g⁻¹ ∈ A := (mem_rightConjugate_iff A g t).mp (hTAg htT)
    have hct : aschbacherThm5Centralizes (aschbacherThm5Core D')
        (aschbacherThm5Preimage D' (Abar' b)) t :=
      (centralizes_conj_iff D Abar g b t).mpr (centralizes_of_mem_centralizing (hAb hgtA))
    obtain ⟨k, hk⟩ := hV2 ⟨_, hv.1⟩
    have hyH' : y ∈ Subgroup.normalizer (D' : Set G) :=
      mem_normalizer_of_fusion hC' a b (t := y * t * y⁻¹) (g := y) ⟨k, congrArg Subtype.val hk⟩
        hv1 hc'v (by rwa [show y⁻¹ * (y * t * y⁻¹) * y = t by group])
    have hvA' : y * t * y⁻¹ ∈ A' :=
      (Subgroup.mem_normalizer_iff.mp (hyL y hy hyH') t).mp (hTA' htT)
    exact hv1 (hRA' _ hv hvA')
  have hTcardP : Nat.card T * Nat.card P = Nat.card V := by rw [hTcard', hPcard, hVcard]
  have hUcardP : Nat.card U * Nat.card P = Nat.card V := by rw [hUcard, hPcard, hVcard]
  exact hR1 (spread_exclusion (Y := ((A ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G))
    hVel inf_le_left inf_le_left hTV hUcardP hTcardP hUP hTU hTP hYU htrans inf_le_left hRU hRP
    hRT)

end DeltaLocal.Eight

end CFSG.ComponentClassification.AschbacherTheorem5
