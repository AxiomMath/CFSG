module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

structure Core49 (A T S Q H : Subgroup X) : Prop where
  sylowFrame : SylowFrame A T S
  hyp43 : Hyp43 A T Q H
  top : A ⊔ T = ⊤
  quasisimple : IsQuasisimple A
  oddCore : CFSG.oddCore A = ⊥
  pRank_lt : 1 < pRank 2 T
  not_le : ¬ A ≤ H
  rank : pRank 2 (centerOf A ⊓ Subgroup.centralizer (T : Set X)) ≤ pRank 2 T
  none : ∀ a ∈ A, (∃ k : ℕ, a ^ (2 ^ k) = 1) → a ∈ Subgroup.centralizer (T : Set X) →
    a ∈ centerOf A

namespace Core49

variable {A T S Q H : Subgroup X}

theorem frame (c : Core49 A T S Q H) : Frame A T := c.sylowFrame.toFrame

theorem normal (c : Core49 A T S Q H) : (⊤ : Subgroup X) ≤ Subgroup.normalizer (A : Set X) := by
  rw [← c.top]
  exact sup_le Subgroup.le_normalizer c.frame.le_normalizer

theorem le_S (c : Core49 A T S Q H) : T ≤ S := c.sylowFrame.le

theorem isPGroup_S (c : Core49 A T S Q H) : IsPGroup 2 S := c.sylowFrame.sylow.isPGroup

theorem ne_bot (c : Core49 A T S Q H) : T ≠ ⊥ := by
  rintro rfl
  have h := c.pRank_lt
  have h0 : pRank 2 (⊥ : Subgroup X) = 0 := by
    apply Nat.eq_zero_of_le_zero
    refine CFSG.SectionRank.pRank_le one_lt_two fun E hE _ => ?_
    rw [le_bot_iff.mp hE, Subgroup.card_bot]
    norm_num
  omega

theorem R_sylow (c : Core49 A T S Q H) : IsSylowOf 2 (S ⊓ A) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact c.sylowFrame.sylow.inf_of_le_normalizer le_sup_left (by rw [c.top]; exact c.normal)

theorem U_le_center (c : Core49 A T S Q H) :
    S ⊓ A ⊓ Subgroup.centralizer (T : Set X) ≤ centerOf A := by
  rintro u ⟨⟨huS, huA⟩, huC⟩
  refine c.none u huA ?_ huC
  obtain ⟨k, hk⟩ := c.isPGroup_S ⟨u, huS⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem U_central (c : Core49 A T S Q H) {u : X}
    (hu : u ∈ S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) (x : X) : x * u = u * x := by
  have hx : x ∈ A ⊔ T := c.top ▸ Subgroup.mem_top x
  have hxm : x ∈ (A : Set X) * (T : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A T c.frame.le_normalizer]
    exact hx
  obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.mp hxm
  have hua : a * u = u * a :=
    (Subgroup.mem_centralizer_iff.mp (c.U_le_center hu).2 a ha)
  have hut : t * u = u * t := (Subgroup.mem_centralizer_iff.mp hu.2 t ht)
  calc a * t * u = a * (t * u) := by group
    _ = a * (u * t) := by rw [hut]
    _ = (a * u) * t := by group
    _ = (u * a) * t := by rw [hua]
    _ = u * (a * t) := by group

theorem sup_inf_eq (c : Core49 A T S Q H) {U : Subgroup X} (hUA : U ≤ A)
    (hTU : T ≤ Subgroup.normalizer (U : Set X)) : (T ⊔ U) ⊓ A = U := by
  apply le_antisymm _ (le_inf le_sup_right hUA)
  rintro x ⟨hx, hxA⟩
  have hxm : x ∈ (T : Set X) * (U : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T U hTU]
    exact hx
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.mp hxm
  have htA : t ∈ A := by simpa using A.mul_mem hxA (A.inv_mem (hUA hu))
  have ht1 : t ∈ T ⊓ A := ⟨ht, htA⟩
  rw [c.frame.inf_eq_bot, Subgroup.mem_bot] at ht1
  rw [ht1, one_mul]
  exact hu

theorem conj_U (c : Core49 A T S Q H) {u : X}
    (hu : u ∈ S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) (x : X) : x * u * x⁻¹ = u := by
  rw [c.U_central hu x, mul_inv_cancel_right]

theorem U_normal (c : Core49 A T S Q H) :
    (S ⊓ A ⊓ Subgroup.centralizer (T : Set X) : Subgroup X).Normal :=
  ⟨fun n hn g => by rw [c.conj_U hn g]; exact hn⟩

theorem le_normalizer_U (c : Core49 A T S Q H) (K : Subgroup X) :
    K ≤ Subgroup.normalizer ((S ⊓ A ⊓ Subgroup.centralizer (T : Set X) : Subgroup X) : Set X) := by
  have := c.U_normal
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem R_not_le (c : Core49 A T S Q H) : ¬ S ⊓ A ≤ centerOf A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hR
  have hsyl := c.R_sylow
  obtain ⟨P, hP⟩ := hsyl
  have hPc : (P : Subgroup A) ≤ Subgroup.center A := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro a
    have hpR : (p : X) ∈ S ⊓ A := hP ▸ ⟨p, hp, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hR hpR).2 a a.2)
  have h := AschbacherToolkit.central_sylow_commutator P hPc P.isPGroup'
  rw [c.quasisimple.1, inf_top_eq] at h
  have hP'bot : commutator (P : Subgroup A) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hPc x.2) y)
  rw [hP'bot, Subgroup.map_bot, inf_bot_eq] at h
  have hRbot : S ⊓ A = ⊥ := by rw [← hP, h, Subgroup.map_bot]
  have hodd : Odd (Nat.card A) := by
    have hcard := c.R_sylow.card_eq
    rw [hRbot, Subgroup.card_bot] at hcard
    have hf : (Nat.card A).factorization 2 = 0 := by
      by_contra hne
      have : 2 ≤ 2 ^ (Nat.card A).factorization 2 :=
        Nat.le_self_pow hne 2 |>.trans' le_rfl
      omega
    rw [Nat.factorization_eq_zero_iff] at hf
    rcases hf with h1 | h1 | h1
    · exact absurd Nat.prime_two h1
    · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)
    · exact absurd h1 Nat.card_pos.ne'
  obtain ⟨E, hET, hE4, hEel⟩ := exists_four_le c.pRank_lt
  apply c.not_le
  apply le_of_centralizers_le hE4 hEel (hET.trans c.frame.le_normalizer) hodd
  intro e he he1
  exact (inf_le_inf_right _ le_sup_left).trans (c.hyp43.centralizer_le c.frame (hET he) he1)

theorem exists_r (c : Core49 A T S Q H) :
    ∃ r ∈ S ⊓ A, r ∉ S ⊓ A ⊓ Subgroup.centralizer (T : Set X) ∧
      r ∈ Subgroup.normalizer
        ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X) ∧
      r ^ 2 ∈ S ⊓ A ⊓ Subgroup.centralizer (T : Set X) := by
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X) with hUdef
  set R := S ⊓ A with hRdef
  have hTR : T ≤ Subgroup.normalizer (R : Set X) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (c.le_S ht), c.frame.le_normalizer ht⟩
  have hUR : U ≤ R := inf_le_left
  have hUA : U ≤ A := hUR.trans inf_le_right
  have hTU := c.le_normalizer_U T
  have hMN : T ⊔ U < T ⊔ R := by
    refine lt_of_le_of_ne (sup_le_sup_left hUR T) fun heq => c.R_not_le ?_
    have hRle : R ≤ (T ⊔ U) ⊓ A := le_inf (heq ▸ le_sup_right) inf_le_right
    rw [c.sup_inf_eq hUA hTU] at hRle
    exact hRle.trans c.U_le_center
  have hN2 : IsPGroup 2 (T ⊔ R : Subgroup X) :=
    c.isPGroup_S.to_le (sup_le c.le_S inf_le_left)
  obtain ⟨y, hyN, hyM, hyU, hy2⟩ := exists_sq_mem_of_lt hMN hN2
  have hym : y ∈ (T : Set X) * (R : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T R hTR]
    exact hyN
  obtain ⟨t, ht, r, hr, rfl⟩ := Set.mem_mul.mp hym
  have htM : t ∈ T ⊔ U := Subgroup.mem_sup_left ht
  have hrM : r ∈ Subgroup.normalizer ((T ⊔ U : Subgroup X) : Set X) := by
    have := Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.inv_mem _ htM)) hyM
    simpa using this
  refine ⟨r, hr, fun hrU => hyU (Subgroup.mul_mem _ htM (Subgroup.mem_sup_right hrU)), hrM, ?_⟩
  have hr2M : r ^ 2 ∈ T ⊔ U := by
    have h1 : (t * r) * t⁻¹ * (t * r)⁻¹ ∈ T ⊔ U :=
      (Subgroup.mem_normalizer_iff.mp hyM t⁻¹).mp (Subgroup.inv_mem _ htM)
    have h2 : r ^ 2 = t⁻¹ * ((t * r) * t⁻¹ * (t * r)⁻¹) * (t * r) ^ 2 := by
      simp only [pow_two]
      group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htM) h1) hy2
  have h3 : r ^ 2 ∈ (T ⊔ U) ⊓ A := ⟨hr2M, A.pow_mem hr.2 2⟩
  rw [c.sup_inf_eq hUA hTU] at h3
  exact h3

theorem centralizer_r (c : Core49 A T S Q H) {r : X} (hr : r ∈ S ⊓ A)
    (hrU : r ∉ S ⊓ A ⊓ Subgroup.centralizer (T : Set X))
    (hrN : r ∈ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X))
    {t : X} (ht : t ∈ T) (htr : t * r = r * t) : t = 1 := by
  by_contra ht1
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  have hrH : r ∈ H :=
    c.hyp43.centralizer_le c.frame ht ht1 ⟨Subgroup.mem_sup_left hr.2,
      Subgroup.mem_centralizer_singleton_iff.mpr htr.symm⟩
  have hTU2 : IsPGroup 2 (T ⊔ U : Subgroup X) :=
    c.isPGroup_S.to_le (sup_le c.le_S (inf_le_left.trans inf_le_left))
  have hrT : rightConjugate T r ≤ T := by
    have h1 : rightConjugate T r ≤ T ⊔ U := by
      have h := rightConjugate_le_rightConjugate (le_sup_left : T ≤ T ⊔ U) r
      rwa [(rightConjugate_eq_self_iff _ r).mpr hrN] at h
    have h2 : rightConjugate T r ≤ Q := by
      have h := rightConjugate_le_rightConjugate c.hyp43.le_Q r
      rwa [(rightConjugate_eq_self_iff _ r).mpr (c.hyp43.le_normalizer hrH)] at h
    have hle := le_inf h1 h2
    rwa [c.hyp43.inf_eq hTU2 le_sup_left] at hle
  have hrNT : r ∈ Subgroup.normalizer (T : Set X) := by
    rw [← rightConjugate_eq_self_iff]
    exact Subgroup.eq_of_le_of_card_ge hrT (rightConjugate_card T r).ge
  apply hrU
  refine ⟨hr, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
  have hcomm : s * r * s⁻¹ * r⁻¹ ∈ T ⊓ A := by
    refine ⟨?_, ?_⟩
    · have h1 : r * s⁻¹ * r⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hrNT _).mp (T.inv_mem hs)
      simpa [mul_assoc] using T.mul_mem hs h1
    · have h1 : s * r * s⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer hs) _).mp hr.2
      exact A.mul_mem h1 (A.inv_mem hr.2)
  rw [c.frame.inf_eq_bot, Subgroup.mem_bot] at hcomm
  calc s * r = s * r * s⁻¹ * r⁻¹ * (r * s) := by group
    _ = r * s := by rw [hcomm, one_mul]

theorem elem_and_embedding (c : Core49 A T S Q H) :
    Open.IsElemAbelian 2 T ∧ ∃ φ : T →* X, Function.Injective φ ∧
      ∀ t, φ t ∈ S ⊓ A ⊓ Subgroup.centralizer (T : Set X) := by
  obtain ⟨r, hr, hrU, hrN, hr2⟩ := c.exists_r
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X) with hUdef
  have hUA : U ≤ A := inf_le_left.trans inf_le_right
  have hmem : ∀ t ∈ T, t⁻¹ * (r⁻¹ * t * r) ∈ U := by
    intro t ht
    have h1 : r⁻¹ * t * r ∈ T ⊔ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) t).mp
        (Subgroup.mem_sup_left ht)
      simpa using this
    have h2 : t⁻¹ * (r⁻¹ * t * r) ∈ (T ⊔ U) ⊓ A := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left ht)) h1, ?_⟩
      have h3 : t⁻¹ * r⁻¹ * t⁻¹⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer (T.inv_mem ht)) _).mp
          (A.inv_mem hr.2)
      simpa [mul_assoc] using A.mul_mem h3 hr.2
    rwa [c.sup_inf_eq hUA (c.le_normalizer_U T)] at h2
  let φ : T →* X :=
    { toFun := fun t => (t : X)⁻¹ * (r⁻¹ * t * r)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Subgroup.coe_mul]
        have hc' := c.U_central (hmem a a.2) ((b : X)⁻¹)
        calc ((a : X) * b)⁻¹ * (r⁻¹ * (a * b) * r)
            = (b : X)⁻¹ * ((a : X)⁻¹ * (r⁻¹ * a * r)) * (r⁻¹ * b * r) := by group
          _ = (a : X)⁻¹ * (r⁻¹ * a * r) * (b : X)⁻¹ * (r⁻¹ * b * r) := by rw [hc']
          _ = (a : X)⁻¹ * (r⁻¹ * a * r) * ((b : X)⁻¹ * (r⁻¹ * b * r)) := by group }
  have hφ : ∀ t : T, φ t = (t : X)⁻¹ * (r⁻¹ * t * r) := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    rw [hφ] at ht
    have htr : (t : X) * r = r * t := by
      have h1 : r⁻¹ * (t : X) * r = t := by
        calc r⁻¹ * (t : X) * r = (t : X) * ((t : X)⁻¹ * (r⁻¹ * t * r)) := by group
          _ = t := by rw [ht, mul_one]
      calc (t : X) * r = r * (r⁻¹ * t * r) := by group
        _ = r * t := by rw [h1]
    exact Subtype.ext (c.centralizer_r hr hrU hrN t.2 htr)
  have hsq : ∀ t : T, (t : X) ^ 2 = 1 := by
    intro t
    have hr2C : r * r ∈ Subgroup.centralizer (T : Set X) := by
      have := hr2.2
      rwa [pow_two] at this
    have hinv : r⁻¹ * φ t * r = (φ t)⁻¹ := by
      rw [hφ]
      have h1 : r⁻¹ * r⁻¹ * (t : X) * r * r = t := by
        have hc := Subgroup.mem_centralizer_iff.mp hr2C t t.2
        calc r⁻¹ * r⁻¹ * (t : X) * r * r = (r * r)⁻¹ * ((t : X) * (r * r)) := by group
          _ = (r * r)⁻¹ * ((r * r) * t) := by rw [hc]
          _ = t := by group
      calc r⁻¹ * ((t : X)⁻¹ * (r⁻¹ * t * r)) * r
          = (r⁻¹ * t * r)⁻¹ * (r⁻¹ * r⁻¹ * t * r * r) := by group
        _ = (r⁻¹ * t * r)⁻¹ * t := by rw [h1]
        _ = ((t : X)⁻¹ * (r⁻¹ * t * r))⁻¹ := by group
    have hcent : r⁻¹ * φ t * r = φ t := by
      have hc := c.conj_U (hmem t t.2) r⁻¹
      rwa [inv_inv] at hc
    have h2 : φ t * φ t = 1 := by
      have h3 : φ t = (φ t)⁻¹ := hcent.symm.trans hinv
      calc φ t * φ t = φ t * (φ t)⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel _
    have h4 : φ (t ^ 2) = 1 := by rw [map_pow, pow_two, h2]
    have h5 : t ^ 2 = 1 := by
      rw [← map_one φ] at h4
      exact hinj h4
    rw [← Subgroup.coe_pow, h5, Subgroup.coe_one]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hsq ⟨x, hx⟩⟩, φ, hinj, fun t => hmem t t.2⟩
  apply hinj
  rw [map_mul, map_mul]
  exact c.U_central (hmem b b.2) (φ a)

end Core49

end CFSG.ComponentClassification.AschbacherTheorem3
