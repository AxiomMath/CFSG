module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveLift

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Eight

open SectionSix SectionSix.BarTools

theorem oTwoPrime_mono {X : Type} [Group X] {P Q : Subgroup X} (h : P ≤ Q) :
    AschbacherTheorem3.oTwoPrime P ≤ AschbacherTheorem3.oTwoPrime Q :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem quasisimple_of_altThree (hyp : Hyp61 G D r Abar) {a : Fin r} {Tb : Subgroup (Bar D)}
    (halt : Thm3AltThree (bar D (aschbacherThm5Preimage D (Abar a))) Tb) :
    CFSG.Open.IsQuasisimple (bar D (aschbacherThm5Preimage D (Abar a))) := by
  obtain ⟨n, hn, -, -, -, -, -, ⟨e⟩⟩ := halt
  obtain ⟨m, K, hm, hK, hcomm, hgen⟩ := bar_factor_components hyp a
  set B := bar D (aschbacherThm5Preimage D (Abar a)) with hBdef
  have hO : AschbacherTheorem3.oTwoPrime B = B := by
    refine le_antisymm (Linear.oTwoPrime_le B) ?_
    rw [← hgen]
    refine iSup_le fun l => ?_
    rw [← Linear.oTwoPrime_eq_of_quasisimple (hK l).1.2.2]
    exact oTwoPrime_mono (le_iSup K l)
  have e' : B ≃* PSL(2, GaloisField 2 n) := (MulEquiv.subgroupCongr hO.symm).trans e
  have : IsSimpleGroup B := by
    have := Exclusion.psl_simple hn
    exact e'.isSimpleGroup
  obtain ⟨l⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hle : K l ≤ B := (hK l).2
  have hn' : ((K l).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Five.le_normalizer_of_iSup hcomm hgen l)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K l).subgroupOf B) with h | h
  · exfalso
    apply component_ne_bot (hK l).1
    exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hle
  · have hKB : K l = B := le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)
    rw [← hKB]
    exact (hK l).1.2.2

theorem card_mul_le_of_inf_eq_bot {V R T : Subgroup G}
    (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hRV : R ≤ V) (hTV : T ≤ V) (hRT : R ⊓ T = ⊥) :
    Nat.card R * Nat.card T ≤ Nat.card V := by
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := by
    refine le_trans (fun t ht => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => hVcomm x (hRV hx) t (hTV ht)
  rw [← AschbacherTheorem3.card_sup_of_le_normalizer hTR hRT]
  exact Subgroup.card_le_of_le (sup_le hRV hTV)

theorem centralizes_of_sq_normalizes {a : Fin r} {V U T : Subgroup G}
    (hVH : V ≤ Subgroup.normalizer (D : Set G)) (hV2 : IsPGroup 2 V)
    (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hUV : U ≤ V) (hTV : T ≤ V) (hTU : T ⊓ U = ⊥)
    (hUT : Nat.card U * Nat.card T = Nat.card V)
    (hTP : T ⊓ (V ⊓ aschbacherThm5Preimage D (Abar a)) = ⊥)
    (hPsyl : IsSylowOf 2 (bar D (V ⊓ aschbacherThm5Preimage D (Abar a)))
      (bar D (aschbacherThm5Preimage D (Abar a))))
    (hself : bar D (aschbacherThm5Preimage D (Abar a)) ⊓
      Subgroup.centralizer (bar D (V ⊓ aschbacherThm5Preimage D (Abar a)) : Set (Bar D)) ≤
        bar D (V ⊓ aschbacherThm5Preimage D (Abar a)))
    {y : G} (hyA : y ∈ aschbacherThm5Preimage D (Abar a))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hyU : ∀ u ∈ U, y * u * y⁻¹ = u)
    (hyT : y * y ∈ Subgroup.normalizer (T : Set G)) : ∀ v ∈ V, y * v * y⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set P := V ⊓ A with hPdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hyH : y ∈ Subgroup.normalizer (D : Set G) := hAH hyA
  have hyP : y ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyV, Subgroup.le_normalizer hyA⟩
  have hTUn : T ≤ Subgroup.normalizer (U : Set G) := by
    refine le_trans (fun t ht => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => hVcomm x (hUV hx) t (hTV ht)
  have hVeq : U ⊔ T = V := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUV hTV) (le_of_eq ?_)
    rw [AschbacherTheorem3.card_sup_of_le_normalizer hTUn (by rw [inf_comm]; exact hTU), hUT]
  have hy2P : ∀ p ∈ P, (y * y) * p * (y * y)⁻¹ = p := by
    intro p hp
    have hpUT : p ∈ U ⊔ T := by
      rw [hVeq]
      exact hp.1
    obtain ⟨u, hu, t₀, ht₀, rfl⟩ := Exclusion.product_mem_of_sup hTUn hpUT
    have hu' : (y * y) * u * (y * y)⁻¹ = u := by
      calc (y * y) * u * (y * y)⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by group
        _ = u := by rw [hyU u hu, hyU u hu]
    have ht₁ : (y * y) * t₀ * (y * y)⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hyT t₀).mp ht₀
    have hkV : (y * y) * t₀ * (y * y)⁻¹ * t₀⁻¹ ∈ V :=
      V.mul_mem (hTV ht₁) (V.inv_mem (hTV ht₀))
    have hq : (y * y) * (u * t₀) * (y * y)⁻¹ * (u * t₀)⁻¹ ∈ T ⊓ P := by
      refine ⟨?_, ?_⟩
      · have hc := hVcomm u (hUV hu) _ hkV
        have h1 : (y * y) * (u * t₀) * (y * y)⁻¹ * (u * t₀)⁻¹ =
            (y * y) * t₀ * (y * y)⁻¹ * t₀⁻¹ := by
          calc (y * y) * (u * t₀) * (y * y)⁻¹ * (u * t₀)⁻¹ =
                ((y * y) * u * (y * y)⁻¹) * ((y * y) * t₀ * (y * y)⁻¹ * t₀⁻¹) * u⁻¹ := by group
            _ = u * ((y * y) * t₀ * (y * y)⁻¹ * t₀⁻¹) * u⁻¹ := by rw [hu']
            _ = ((y * y) * t₀ * (y * y)⁻¹ * t₀⁻¹) * u * u⁻¹ := by rw [hc]
            _ = (y * y) * t₀ * (y * y)⁻¹ * t₀⁻¹ := by group
        rw [h1]
        exact T.mul_mem ht₁ (T.inv_mem ht₀)
      · have hyyP : y * y ∈ Subgroup.normalizer (P : Set G) := Subgroup.mul_mem _ hyP hyP
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp hyyP _).mp hp) (P.inv_mem hp)
    rw [hTP, Subgroup.mem_bot, mul_inv_eq_one] at hq
    exact hq
  set yb := toBar D ⟨y, hyH⟩ with hybdef
  have hybA : yb ∈ bar D A := toBar_mem_bar D (h := ⟨y, hyH⟩) hyA
  have hybN : yb ∈ Subgroup.normalizer (bar D P : Set (Bar D)) :=
    toBar_mem_normalizer_bar (inf_le_left.trans hVH) hyP
  have hyb2 : yb * yb ∈ bar D P := by
    refine hself ⟨Subgroup.mul_mem _ hybA hybA, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    obtain ⟨p, hp, rfl⟩ := (mem_bar_iff D P z).mp hz
    rw [hybdef, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (p : G) * (y * y) = (y * y) * p
    have h1 := hy2P p hp
    calc (p : G) * (y * y) = ((y * y) * p * (y * y)⁻¹) * (y * y) := by rw [h1]
      _ = (y * y) * p := by group
  have hybP : yb ∈ bar D P := by
    obtain ⟨k, hk⟩ := hPsyl.isPGroup ⟨yb * yb, hyb2⟩
    have hk' : yb ^ (2 ^ (k + 1)) = 1 := by
      have h1 : (yb * yb) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [pow_succ', pow_mul, pow_two]
      exact h1
    have hZ2 := Five.isPGroup_zpowers_of_pow hk'
    have hPN : IsSylowOf 2 (bar D P) (bar D A ⊓ Subgroup.normalizer (bar D P : Set (Bar D))) :=
      hPsyl.of_le (le_inf hPsyl.le Subgroup.le_normalizer) inf_le_left
    obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hPN hZ2
      (Subgroup.zpowers_le.mpr ⟨hybA, hybN⟩)
    have h1 : c⁻¹ * yb * c ∈ bar D P :=
      hcle (AschbacherTheorem3.conj_mem_rightConjugate (Subgroup.mem_zpowers yb) c)
    have h2 := (Subgroup.mem_normalizer_iff.mp hc.2 _).mp h1
    simpa [mul_assoc] using h2
  obtain ⟨p₀, hp₀, hp₀y⟩ := (mem_bar_iff D P yb).mp hybP
  have hoO : toBar D (p₀⁻¹ * ⟨y, hyH⟩) = 1 := by rw [map_mul, map_inv, hp₀y, inv_mul_cancel]
  have hoO' := (toBar_eq_one_iff D _).mp hoO
  intro v hv
  have hp₀V : (p₀ : G) ∈ V := hp₀.1
  have hoV : (p₀ : G)⁻¹ * y ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hp₀V)) hyV
  have hovV : ((p₀ : G)⁻¹ * y) * v * ((p₀ : G)⁻¹ * y)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hoV v).mp hv
  have hovH : ((p₀ : G)⁻¹ * y) * v * ((p₀ : G)⁻¹ * y)⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    hVH hovV
  have hov : ((p₀ : G)⁻¹ * y) * v * ((p₀ : G)⁻¹ * y)⁻¹ = v := by
    have h1 := toBar_injOn_of_isPGroup hV2 (u := ⟨_, hovH⟩) (v := ⟨v, hVH hv⟩) hovV hv (by
      change toBar D ((p₀⁻¹ * ⟨y, hyH⟩) * ⟨v, hVH hv⟩ * (p₀⁻¹ * ⟨y, hyH⟩)⁻¹) = _
      rw [map_mul, map_mul, map_inv, hoO, one_mul, inv_one, mul_one])
    exact congrArg Subtype.val h1
  calc y * v * y⁻¹ = (p₀ : G) * (((p₀ : G)⁻¹ * y) * v * ((p₀ : G)⁻¹ * y)⁻¹) * (p₀ : G)⁻¹ := by
        group
    _ = (p₀ : G) * v * (p₀ : G)⁻¹ := by rw [hov]
    _ = v := by rw [hVcomm _ hp₀V v hv]; group

end DeltaLocal.Eight

end CFSG.ComponentClassification.AschbacherTheorem5
