module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Basic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSylow

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22

section Defs

variable {G : Type} [Group G]

@[expose] def sec3W (R T : Subgroup G) : Subgroup G :=
  ⨆ (y : G) (_ : rightConjugate R y ≤ centralizer ((R ⊔ T : Subgroup G) : Set G)),
    rightConjugate R y

@[expose] def sec3V (R T : Subgroup G) : Subgroup G :=
  ⨆ (x : G) (_ : rightConjugate R x ≤ centralizer (sec3W R T : Set G)), rightConjugate R x

theorem le_sec3W {R T : Subgroup G} {y : G}
    (h : rightConjugate R y ≤ centralizer ((R ⊔ T : Subgroup G) : Set G)) :
    rightConjugate R y ≤ sec3W R T :=
  le_iSup₂_of_le y h le_rfl

theorem le_sec3V {R T : Subgroup G} {x : G}
    (h : rightConjugate R x ≤ centralizer (sec3W R T : Set G)) :
    rightConjugate R x ≤ sec3V R T :=
  le_iSup₂_of_le x h le_rfl

theorem sec3V_le_centralizer (R T : Subgroup G) :
    sec3V R T ≤ centralizer (sec3W R T : Set G) :=
  iSup₂_le fun _ h => h

theorem le_centralizer_sup {H R T : Subgroup G} (hR : H ≤ centralizer (R : Set G))
    (hT : H ≤ centralizer (T : Set G)) : H ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
  rw [le_centralizer_iff] at hR hT ⊢
  exact sup_le hR hT

theorem le_centralizer_self_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    E ≤ centralizer (E : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)

variable {R T : Subgroup G}

theorem le_sec3W_of (hR : IsElemAbelian 2 R) (hTR : T ≤ centralizer (R : Set G))
    (hT : ∃ y, T = rightConjugate R y) : R ⊔ T ≤ sec3W R T := by
  obtain ⟨y, rfl⟩ := hT
  have hRT : R ≤ centralizer (rightConjugate R y : Set G) := le_centralizer_iff.mp hTR
  refine sup_le ?_ ?_
  · have h := le_sec3W (R := R) (T := rightConjugate R y) (y := 1)
      (by rw [rightConjugate_one]; exact le_centralizer_sup (le_centralizer_self_of_isElemAbelian hR) hRT)
    rwa [rightConjugate_one] at h
  · exact le_sec3W (le_centralizer_sup hTR
      (le_centralizer_self_of_isElemAbelian (isElemAbelian_rightConjugate hR y)))

theorem sec3W_le_centralizer (R T : Subgroup G) :
    sec3W R T ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
  iSup₂_le fun _ h => h

theorem sec3V_le_sec3W (hR : IsElemAbelian 2 R) (hTR : T ≤ centralizer (R : Set G))
    (hT : ∃ y, T = rightConjugate R y) : sec3V R T ≤ sec3W R T := by
  refine iSup₂_le fun x hx => le_sec3W (hx.trans (centralizer_le ?_))
  exact le_sec3W_of hR hTR hT

theorem le_sec3V_of (hT : ∃ y, T = rightConjugate R y) : R ⊔ T ≤ sec3V R T := by
  have hW : sec3W R T ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) := sec3W_le_centralizer R T
  have hRTW : R ⊔ T ≤ centralizer (sec3W R T : Set G) := le_centralizer_iff.mp hW
  obtain ⟨y, rfl⟩ := hT
  refine sup_le ?_ ?_
  · have h := le_sec3V (R := R) (T := rightConjugate R y) (x := 1)
      (by rw [rightConjugate_one]; exact le_sup_left.trans hRTW)
    rwa [rightConjugate_one] at h
  · exact le_sec3V (le_sup_right.trans hRTW)

theorem isElemAbelian_sec3V (hR : IsElemAbelian 2 R) (hTR : T ≤ centralizer (R : Set G))
    (hT : ∃ y, T = rightConjugate R y) : IsElemAbelian 2 (sec3V R T) := by
  have hVW := sec3V_le_sec3W hR hTR hT
  have hVC := sec3V_le_centralizer R T
  have hcomm : ∀ a ∈ sec3V R T, ∀ b ∈ sec3V R T, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hVC ha) b (hVW hb)).symm
  let E : Subgroup G :=
    { carrier := {v | v ∈ sec3V R T ∧ v ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hcomm a ha.1 b hb.1) 2), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hVE : sec3V R T ≤ E := iSup₂_le fun x hx v hv =>
    ⟨le_sec3V hx hv, (isElemAbelian_rightConjugate hR x).2 v hv⟩
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun v hv => (hVE hv).2⟩

end Defs

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_isSylowOf {A K R V : Subgroup G} (hKA : K ≤ normalizer (A : Set G))
    (hR : IsSylowOf 2 R K) (hRV : R ≤ V) (hV : IsPGroup 2 V) (hVAK : V ≤ A ⊔ K) :
    V ≤ R ⊔ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ K with hB
  have hAB : A ≤ B := le_sup_left
  have hKB : K ≤ B := le_sup_right
  have hBA : B ≤ normalizer (A : Set G) := sup_le le_normalizer hKA
  have : (A.subgroupOf B).Normal := (normal_subgroupOf_iff_le_normalizer hAB).mpr hBA
  set π := QuotientGroup.mk' (A.subgroupOf B) with hπ
  have hRB : R ≤ B := hR.le.trans hKB
  have hRK' : IsSylowOf 2 (R.subgroupOf B) (K.subgroupOf B) :=
    (Lemma37.isSylowOf_subgroupOf_iff hRB hKB).mpr hR
  have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaInputs.isSylowOf_map π hRK'
  have hKtop : (K.subgroupOf B).map π = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf B) q
    have hb : (b : G) ∈ ((A ⊔ K : Subgroup G) : Set G) := b.2
    rw [coe_mul_of_right_le_normalizer_left A K hKA] at hb
    obtain ⟨a, ha, k, hk, hak⟩ := hb
    have hak' : a * k = (b : G) := hak
    refine ⟨⟨k, hKB hk⟩, hk, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    rw [← hak']
    have h := (mem_normalizer_iff.mp (hKA (inv_mem hk)) a).mp ha
    have : k⁻¹ * (a * k) = k⁻¹ * a * k⁻¹⁻¹ := by group
    rw [this]
    exact h
  have hVp : IsPGroup 2 ↥((V.subgroupOf B).map π) :=
    (hV.of_equiv (subgroupOfEquivOfLe hVAK).symm).map π
  have hle : (R.subgroupOf B).map π ≤ (V.subgroupOf B).map π :=
    map_mono fun x hx => hRV hx
  have heq := h1.eq_of_le hle (by rw [hKtop]; exact le_top) hVp
  intro v hv
  have hv' : π ⟨v, hVAK hv⟩ ∈ (V.subgroupOf B).map π := ⟨⟨v, hVAK hv⟩, hv, rfl⟩
  rw [heq] at hv'
  obtain ⟨r, hr, hrv⟩ := hv'
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrv
  have hv'' : v = (r : G) * ((r⁻¹ * ⟨v, hVAK hv⟩ : B) : G) := by simp
  rw [hv'']
  exact mul_mem (mem_sup_left hr) (mem_sup_right hrv)

omit [Finite G] in
theorem eq_sup_inf_of_le_sup {R V A : Subgroup G} (hRV : R ≤ V) (hRA : R ≤ normalizer (A : Set G))
    (hV : V ≤ R ⊔ A) : V = R ⊔ (V ⊓ A) := by
  refine le_antisymm (fun v hv => ?_) (sup_le hRV inf_le_left)
  have hv' : v ∈ ((R ⊔ A : Subgroup G) : Set G) := hV hv
  rw [coe_mul_of_left_le_normalizer_right R A hRA] at hv'
  obtain ⟨r, hr, a, ha, rfl⟩ := hv'
  have haV : a ∈ V := by simpa using mul_mem (inv_mem (hRV hr)) hv
  exact mul_mem (mem_sup_left hr) (mem_sup_right ⟨haV, ha⟩)

end Sylow

section Lemma35

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_rightConjugate (X : Subgroup G) (g : G) :
    centralizer (rightConjugate X g : Set G) = rightConjugate (centralizer (X : Set G)) g :=
  centralizer_conj X g⁻¹

theorem conj_le_sup_centralizer (h332 : Lemma33Two) {A R Q : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hQ : ∃ x, Q = rightConjugate R x)
    (hQR : Q ≤ centralizer (R : Set G)) : Q ≤ A ⊔ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, rfl⟩ := hQ
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hR1 : R ≠ ⊥ := ne_bot_of_isSylowOf_of_tightlyEmbedded hKte hR
  have hQN : rightConjugate R x ≤ normalizer (A : Set G) := by
    rw [← normalizer_centralizer_eq hA.standard]
    exact hQR.trans (centralizer_two_subgroup_le _ R hKte hR.isPGroup hR.le hR1)
  have hQS := AschbacherTheorem3.isSylowOf_rightConjugate hR x
  by_cases hx : x ∈ normalizer (A : Set G)
  · have hKx : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
      rw [rightConjugate_eq_self_iff, normalizer_centralizer_eq hA.standard]
      exact hx
    rw [hKx] at hQS
    exact hQS.le.trans le_sup_right
  · have hQ1 : rightConjugate R x ≠ ⊥ := by
      intro h
      apply hR1
      have hc := rightConjugate_card R x
      rw [h, card_bot] at hc
      exact card_eq_one.mp hc.symm
    exact h332 G A hA R hR x hx _ (hQS.of_le (le_inf hQS.le hQN) inf_le_left) hQ1
      (hQR.trans (centralizer_le_normalizer _)) hQS

theorem lemma35 (h32 : Lemma32) (h332 : Lemma33Two) {A R T : Subgroup G} {g : G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTR : T ≤ centralizer (R : Set G)) :
    IsElemAbelian 2 (sec3V R T) ∧ sec3V R T = R ⊔ (sec3V R T ⊓ A) ∧
      sec3V R T = T ⊔ (sec3V R T ⊓ rightConjugate A g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hK
  have hRe : IsElemAbelian 2 R := h32 G A hA R hR
  have hTconj : ∃ y, T = rightConjugate R y := by
    obtain ⟨h, -, hh⟩ := exists_conj_eq_of_isSylowOf (AschbacherTheorem3.isSylowOf_rightConjugate hR g)
      hT
    refine ⟨g * h⁻¹, ?_⟩
    rw [hh, ← rightConjugate_mul]
    change (rightConjugate R g).map (MulAut.conj h).toMonoidHom =
      (rightConjugate R g).map (MulAut.conj h⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
  have hVe := isElemAbelian_sec3V hRe hTR hTconj
  have hVp : IsPGroup 2 ↥(sec3V R T) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hRTV := le_sec3V_of hTconj
  have hRTW := le_sec3W_of hRe hTR hTconj
  have hKA : K ≤ normalizer (A : Set G) := centralizer_le_normalizer _
  have hCW : centralizer (sec3W R T : Set G) ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
    centralizer_le fun x hx => hRTW hx
  have hVAK : sec3V R T ≤ A ⊔ K := iSup₂_le fun x hx =>
    conj_le_sup_centralizer h332 hA hR ⟨x, rfl⟩
      (hx.trans (hCW.trans (centralizer_le fun r hr => mem_sup_left hr)))
  have h1 : sec3V R T ≤ R ⊔ A := le_sup_of_isSylowOf hKA hR (le_sup_left.trans hRTV) hVp hVAK
  refine ⟨hVe, eq_sup_inf_of_le_sup (le_sup_left.trans hRTV) (hR.le.trans hKA) h1, ?_⟩
  set R₁ := rightConjugate T g⁻¹ with hR₁def
  have hR₁ : IsSylowOf 2 R₁ K := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hT g⁻¹
    rwa [rightConjugate_inv_cancel] at h
  obtain ⟨y, hy⟩ := hTconj
  have hVAKg : sec3V R T ≤ rightConjugate A g ⊔ rightConjugate K g := by
    refine iSup₂_le fun x hx => ?_
    have hQT : rightConjugate R x ≤ centralizer (T : Set G) :=
      hx.trans (hCW.trans (centralizer_le fun t ht => mem_sup_right ht))
    have hconj : ∃ z, rightConjugate (rightConjugate R x) g⁻¹ = rightConjugate R₁ z := by
      refine ⟨g * y⁻¹ * x * g⁻¹, ?_⟩
      rw [hR₁def, hy]
      simp only [rightConjugate_mul]
      congr 1
      group
    have hle := conj_le_sup_centralizer h332 hA hR₁ hconj (by
      rw [hR₁def, centralizer_rightConjugate]
      exact map_mono hQT)
    calc rightConjugate R x
        = rightConjugate (rightConjugate (rightConjugate R x) g⁻¹) g := by
          rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
      _ ≤ rightConjugate (A ⊔ K) g := map_mono hle
      _ = rightConjugate A g ⊔ rightConjugate K g := Subgroup.map_sup _ _ _
  have hKgA : rightConjugate K g ≤ normalizer (rightConjugate A g : Set G) := by
    intro x hx
    rw [mem_normalizer_rightConjugate_iff]
    rw [mem_rightConjugate_iff] at hx
    exact hKA hx
  have h2 : sec3V R T ≤ T ⊔ rightConjugate A g :=
    le_sup_of_isSylowOf hKgA hT (le_sup_right.trans hRTV) hVp hVAKg
  exact eq_sup_inf_of_le_sup (le_sup_right.trans hRTV) (hT.le.trans hKgA) h2

end Lemma35

end CFSG.ComponentClassification.AS76b
