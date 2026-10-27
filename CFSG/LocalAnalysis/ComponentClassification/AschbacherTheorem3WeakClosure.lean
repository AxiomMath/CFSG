module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.LocalAnalysis.SignalizerFunctor.RelativeWeakClosure
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X]

theorem rightConjugate_le_relativeWeakClosure {G T B : Subgroup X} {g : X} (hg : g ∈ G)
    (hle : rightConjugate T g ≤ B) : rightConjugate T g ≤ relativeWeakClosure G T B :=
  le_iSup_of_le (⟨g⁻¹, G.inv_mem hg⟩ : G) (le_iSup_of_le hle le_rfl)

theorem inf_normalizer_le_centralizer {G A R : Subgroup X} (hF : Frame G A) (hR : R ≤ G ⊔ A)
    (hAR : A ≤ R) (hA : IsMulCommutative A) :
    R ⊓ Subgroup.normalizer (A : Set X) ≤ Subgroup.centralizer (A : Set X) := by
  obtain ⟨heq, -, hc⟩ := lemma_4_1 hF hR hAR
  rw [heq]
  refine sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA) ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hc

structure Hyp45 (G T S Q H : Subgroup X) (g : X) : Prop where
  sylowFrame : SylowFrame G T S
  hyp43 : Hyp43 G T Q H
  mem : g ∈ G
  ne : rightConjugate T g ≠ T
  weakClosure : relativeWeakClosure G T (H ⊓ S) = T ⊔ rightConjugate T g

namespace Hyp45

variable {G T S Q H : Subgroup X} {g : X}

theorem frame (h : Hyp45 G T S Q H g) : Frame G T := h.sylowFrame.toFrame

theorem le_sup (h : Hyp45 G T S Q H g) : S ≤ G ⊔ T := h.sylowFrame.sylow.le

theorem le_S [Finite X] (h : Hyp45 G T S Q H g) : T ≤ S := h.sylowFrame.le

theorem isPGroup_S (h : Hyp45 G T S Q H g) : IsPGroup 2 S := h.sylowFrame.sylow.isPGroup

theorem W_le (h : Hyp45 G T S Q H g) : T ⊔ rightConjugate T g ≤ H ⊓ S :=
  h.weakClosure ▸ relative_weak_closure_le _ _ _

theorem conj_le (h : Hyp45 G T S Q H g) : rightConjugate T g ≤ H ⊓ S :=
  le_sup_right.trans h.W_le

theorem facts [Finite X] (h : Hyp45 G T S Q H g) :
    g ∉ H ∧ T ⊓ rightConjugate T g = ⊥ ∧ ⁅T, rightConjugate T g⁆ = ⊥ ∧
      IsMulCommutative (T ⊔ rightConjugate T g : Subgroup X) :=
  lemma_4_4_two h.frame h.hyp43 h.isPGroup_S h.le_S h.mem (by rw [inf_comm]; exact h.conj_le)
    h.ne

theorem isMulCommutative [Finite X] (h : Hyp45 G T S Q H g) : IsMulCommutative T :=
  isMulCommutative_of_le le_sup_left h.facts.2.2.2

theorem isMulCommutative_conj [Finite X] (h : Hyp45 G T S Q H g) :
    IsMulCommutative (rightConjugate T g) :=
  isMulCommutative_of_le le_sup_right h.facts.2.2.2

theorem ne_bot (h : Hyp45 G T S Q H g) : T ≠ ⊥ := fun hT => h.ne (by rw [hT, rightConjugate_bot])

theorem inf_eq_normalizer [Finite X] (h : Hyp45 G T S Q H g) :
    H ⊓ S = S ⊓ Subgroup.normalizer (T : Set X) := by
  apply le_antisymm
  · exact le_inf inf_le_right (h.hyp43.le_normalizer_of_le h.isPGroup_S.to_inf_right
      (le_inf h.hyp43.le_H h.le_S) inf_le_left)
  · exact le_inf ((inf_le_inf_right _ h.le_sup).trans (h.hyp43.normalizer_le h.frame h.ne_bot))
      inf_le_left

theorem le_centralizer [Finite X] (h : Hyp45 G T S Q H g) :
    H ⊓ S ≤ Subgroup.centralizer (T : Set X) := by
  rw [h.inf_eq_normalizer]
  exact inf_normalizer_le_centralizer h.frame h.le_sup h.le_S h.isMulCommutative

theorem le_normalizer_W [Finite X] (h : Hyp45 G T S Q H g) :
    H ⊓ S ≤ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  have hdec := (lemma_4_1 h.frame h.le_sup h.le_S).1
  have hG : S ⊓ Subgroup.normalizer (T : Set X) ⊓ G ≤
      Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
    rw [← h.weakClosure]
    intro x hx
    apply relative_weak_closure_parent_normalizer G T (H ⊓ S)
    refine ⟨hx.2, ?_⟩
    rw [h.inf_eq_normalizer]
    exact Subgroup.le_normalizer hx.1
  rw [h.inf_eq_normalizer, hdec]
  exact sup_le (le_sup_left.trans Subgroup.le_normalizer) hG

theorem le_normalizer_G (h : Hyp45 G T S Q H g) : H ⊓ S ≤ Subgroup.normalizer (G : Set X) :=
  inf_le_right.trans (h.le_sup.trans (sup_le Subgroup.le_normalizer h.frame.le_normalizer))

theorem conj_le_normalizer [Finite X] (h : Hyp45 G T S Q H g) :
    rightConjugate T g ≤ Subgroup.normalizer (T : Set X) :=
  h.conj_le.trans (h.inf_eq_normalizer.le.trans inf_le_right)

theorem card_W [Finite X] (h : Hyp45 G T S Q H g) :
    Nat.card (T ⊔ rightConjugate T g : Subgroup X) = Nat.card T * Nat.card T := by
  rw [card_sup_of_le_normalizer h.conj_le_normalizer h.facts.2.1, rightConjugate_card]

theorem W_decomp [Finite X] (h : Hyp45 G T S Q H g) :
    T ⊔ rightConjugate T g = T ⊔ ((T ⊔ rightConjugate T g) ⊓ G) ∧
      T ⊓ ((T ⊔ rightConjugate T g) ⊓ G) = ⊥ := by
  have hWN : T ⊔ rightConjugate T g ≤ Subgroup.normalizer (T : Set X) :=
    sup_le Subgroup.le_normalizer h.conj_le_normalizer
  obtain ⟨hdec, hinf, -⟩ :=
    lemma_4_1 h.frame (h.W_le.trans (inf_le_right.trans h.le_sup)) (le_sup_left :
      T ≤ T ⊔ rightConjugate T g)
  rw [inf_eq_left.mpr hWN] at hdec hinf
  exact ⟨hdec, hinf⟩

theorem card_W_inf_G [Finite X] (h : Hyp45 G T S Q H g) :
    Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) = Nat.card T := by
  obtain ⟨hdec, hinf⟩ := h.W_decomp
  have hN : (T ⊔ rightConjugate T g) ⊓ G ≤ Subgroup.normalizer (T : Set X) :=
    inf_le_left.trans (sup_le Subgroup.le_normalizer h.conj_le_normalizer)
  have hc := card_sup_of_le_normalizer hN hinf
  rw [← hdec, h.card_W] at hc
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

theorem W_inf_G_ne_bot [Finite X] (h : Hyp45 G T S Q H g) : (T ⊔ rightConjugate T g) ⊓ G ≠ ⊥ := by
  intro hbot
  have hc := h.card_W_inf_G
  rw [hbot, Subgroup.card_bot] at hc
  exact h.ne_bot ((Subgroup.card_eq_one).mp hc.symm)

end Hyp45

theorem lemma_4_5_one [Finite X] {G T S Q H : Subgroup X} {g : X} (h : Hyp45 G T S Q H g) {t : X}
    (ht : t ∈ T) (ht1 : t ≠ 1) : H ⊓ S = S ⊓ Subgroup.centralizer {t} := by
  apply le_antisymm
  · exact le_inf inf_le_right
      (h.le_centralizer.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht)))
  · exact le_inf ((inf_le_inf_right _ h.le_sup).trans (h.hyp43.centralizer_le h.frame ht ht1))
      inf_le_left

theorem lemma_4_5_two [Finite X] {G T S Q H : Subgroup X} {g : X} (h : Hyp45 G T S Q H g) :
    H ⊓ S = S ⊓ Subgroup.centralizer (rightConjugate T g : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := rightConjugate T g with hKdef
  have hFK := h.frame.rightConjugate_frame h.mem
  have h43K := h.hyp43.rightConjugate_hyp h.mem
  have hSK : S ≤ G ⊔ K := by rw [sup_rightConjugate h.mem]; exact h.le_sup
  have hKS : K ≤ S := h.conj_le.trans inf_le_right
  have hP2 : IsPGroup 2 (H ⊓ S : Subgroup X) := h.isPGroup_S.to_inf_right
  have hWGP : (T ⊔ K) ⊓ G ≤ H ⊓ S := inf_le_left.trans h.W_le
  have hNnormal : (((T ⊔ K) ⊓ G).subgroupOf (H ⊓ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWGP]
    exact (le_inf h.le_normalizer_W h.le_normalizer_G).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hNne : ((T ⊔ K) ⊓ G).subgroupOf (H ⊓ S) ≠ ⊥ := by
    intro hbot
    apply h.W_inf_G_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hWGP hx⟩ : (H ⊓ S : Subgroup X)) ∈ ((T ⊔ K) ⊓ G).subgroupOf (H ⊓ S) := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  have : Group.IsNilpotent (H ⊓ S : Subgroup X) := hP2.isNilpotent
  obtain ⟨⟨z, hzN, hzC⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne)
  have hzW : (z : X) ∈ (T ⊔ K) ⊓ G := Subgroup.mem_subgroupOf.mp hzN
  have hz1' : (z : X) ≠ 1 := fun h1 => hz1 (Subtype.ext (Subtype.ext h1))
  have hzC' : ∀ y ∈ H ⊓ S, y * (z : X) = (z : X) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨y, hy⟩)
  have hTK : T ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1).trans
      (Subgroup.centralizer_le_normalizer _)
  have hzmem : (z : X) ∈ (T : Set X) * (K : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T K hTK]
    exact hzW.1
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hzmem
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    have hmem : (z : X) ∈ T ⊓ G := ⟨hab ▸ ha, hzW.2⟩
    rw [h.frame.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hz1' hmem
  have hbC : H ⊓ S ≤ Subgroup.centralizer {b} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hya : a * y = y * a := Subgroup.mem_centralizer_iff.mp (h.le_centralizer hy) a ha
    have hyz := hzC' y hy
    have hb' : b = a⁻¹ * z := by rw [← hab]; group
    rw [hb']
    calc y * (a⁻¹ * z) = (y * a⁻¹) * z := by group
      _ = (a⁻¹ * y) * z := by
        rw [show y * a⁻¹ = a⁻¹ * y by
          calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
            _ = a⁻¹ * (y * a) * a⁻¹ := by rw [hya]
            _ = a⁻¹ * y := by group]
      _ = a⁻¹ * (y * z) := by group
      _ = a⁻¹ * (z * y) := by rw [hyz]
      _ = (a⁻¹ * z) * y := by group
  have hPHg : H ⊓ S ≤ rightConjugate H g := fun y hy =>
    h43K.centralizer_le hFK hb hb1 ⟨hSK hy.2, hbC hy⟩
  have hPNK : H ⊓ S ≤ S ⊓ Subgroup.normalizer (K : Set X) :=
    le_inf inf_le_right ((le_inf hPHg inf_le_right).trans
      (h43K.le_normalizer_of_le h.isPGroup_S.to_inf_right (le_inf h43K.le_H hKS) inf_le_left))
  have hL : rightConjugate ((G ⊔ T) ⊓ Subgroup.normalizer (T : Set X)) g =
      (G ⊔ T) ⊓ Subgroup.normalizer (K : Set X) := by
    rw [rightConjugate_inf, rightConjugate_normalizer,
      rightConjugate_eq_of_mem (Subgroup.mem_sup_left h.mem)]
  have hsyl := isSylowOf_rightConjugate h.sylowFrame.sylow_normalizer g
  rw [hL] at hsyl
  have hcard : Nat.card (S ⊓ Subgroup.normalizer (K : Set X) : Subgroup X) ≤
      Nat.card (H ⊓ S : Subgroup X) := by
    have h1 := card_le_of_isSylowOf hsyl h.isPGroup_S.to_inf_left (inf_le_inf_right _ h.le_sup)
    rwa [rightConjugate_card, ← h.inf_eq_normalizer] at h1
  have hPeq : H ⊓ S = S ⊓ Subgroup.normalizer (K : Set X) :=
    Subgroup.eq_of_le_of_card_ge hPNK hcard
  have hNC : S ⊓ Subgroup.normalizer (K : Set X) ≤ Subgroup.centralizer (K : Set X) :=
    inf_normalizer_le_centralizer hFK hSK hKS h.isMulCommutative_conj
  rw [hPeq]
  exact le_antisymm (le_inf inf_le_left hNC)
    (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))

namespace Hyp45

variable {G T S Q H : Subgroup X} {g : X}

theorem inf_eq_centralizer_W [Finite X] (h : Hyp45 G T S Q H g) :
    H ⊓ S = S ⊓ Subgroup.centralizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) := by
  apply le_antisymm
  · refine le_inf inf_le_right ?_
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← Subgroup.le_centralizer_iff]
      exact h.le_centralizer
    · rw [← Subgroup.le_centralizer_iff, lemma_4_5_two h]
      exact inf_le_right
  · rw [lemma_4_5_two h]
    exact inf_le_inf_left S (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))

theorem normalizer_W_le [Finite X] (h : Hyp45 G T S Q H g) :
    S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X) := by
  rw [h.inf_eq_centralizer_W]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx.1, normalizer_le_normalizer_centralizer _ hx.2⟩

theorem commutator_map [Finite X] (h : Hyp45 G T S Q H g) {x : X} (hxS : x ∈ S)
    (hxN : x ∈ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X)) (hxH : x ∉ H)
    (hx2 : x ^ 2 ∈ H) :
    (∀ t ∈ T, t⁻¹ * (x⁻¹ * t * x) ∈ (T ⊔ rightConjugate T g) ⊓ G) ∧
      (∀ s ∈ T, ∀ t ∈ T, s⁻¹ * (x⁻¹ * s * x) = t⁻¹ * (x⁻¹ * t * x) → s = t) ∧
      (∀ w ∈ (T ⊔ rightConjugate T g) ⊓ G, ∃ t ∈ T, w = t⁻¹ * (x⁻¹ * t * x)) ∧
      (∀ w ∈ (T ⊔ rightConjugate T g) ⊓ G, x⁻¹ * w * x = w⁻¹) := by
  set W := T ⊔ rightConjugate T g with hWdef
  obtain ⟨t₀, ht₀, h₀, hh₀, hx₀, hrc⟩ := h.frame.exists_rightConjugate_eq (h.le_sup hxS)
  have hT'HS : rightConjugate T x ≤ H ⊓ S := by
    rw [← (rightConjugate_eq_self_iff _ x).mpr hxN]
    exact rightConjugate_le_rightConjugate (le_inf h.hyp43.le_H h.le_S) x
  have hT'W : rightConjugate T x ≤ W := by
    rw [hrc, hWdef, ← h.weakClosure]
    exact rightConjugate_le_relativeWeakClosure hh₀ (hrc ▸ hT'HS)
  have hT'ne : rightConjugate T h₀ ≠ T := by
    rw [← hrc]
    intro heq
    exact hxH (h.hyp43.normalizer_le h.frame h.ne_bot
      ⟨h.le_sup hxS, (rightConjugate_eq_self_iff T x).mp heq⟩)
  obtain ⟨-, hinf', -, -⟩ := lemma_4_4_two h.frame h.hyp43 h.isPGroup_S h.le_S hh₀
    (by rw [inf_comm, ← hrc]; exact hT'HS) hT'ne
  rw [← hrc] at hinf'
  have hTW : T ≤ W := le_sup_left
  have hWG : W ≤ Subgroup.normalizer (G : Set X) :=
    h.W_le.trans h.le_normalizer_G
  have hx2C : ∀ t ∈ T, x⁻¹ * (x⁻¹ * t * x) * x = t := by
    intro t ht
    have hc : t * (x * x) = (x * x) * t := by
      have := Subgroup.mem_centralizer_iff.mp (h.le_centralizer ⟨hx2, S.pow_mem hxS 2⟩) t ht
      rwa [pow_two] at this
    calc x⁻¹ * (x⁻¹ * t * x) * x = (x * x)⁻¹ * (t * (x * x)) := by group
      _ = (x * x)⁻¹ * ((x * x) * t) := by rw [hc]
      _ = t := by group
  have hmap : ∀ t ∈ T, t⁻¹ * (x⁻¹ * t * x) ∈ W ⊓ G := by
    intro t ht
    refine ⟨W.mul_mem (W.inv_mem (hTW ht)) (hT'W (conj_mem_rightConjugate ht x)), ?_⟩
    have hcomm : t₀ * t = t * t₀ := by
      have := Subgroup.mem_centralizer_iff.mp
        (h.le_centralizer (le_inf h.hyp43.le_H h.le_S ht₀)) t ht
      exact this.symm
    have heq : t⁻¹ * (x⁻¹ * t * x) = (t⁻¹ * h₀⁻¹ * t) * h₀ := by
      rw [← hx₀]
      calc t⁻¹ * ((t₀ * h₀)⁻¹ * t * (t₀ * h₀)) = t⁻¹ * (h₀⁻¹ * (t₀⁻¹ * (t * t₀)) * h₀) := by
            group
        _ = t⁻¹ * (h₀⁻¹ * (t₀⁻¹ * (t₀ * t)) * h₀) := by rw [hcomm]
        _ = (t⁻¹ * h₀⁻¹ * t) * h₀ := by group
    rw [heq]
    have h1 : t⁻¹ * h₀⁻¹ * t⁻¹⁻¹ ∈ G :=
      (Subgroup.mem_normalizer_iff.mp (h.frame.le_normalizer (T.inv_mem ht)) _).mp
        (G.inv_mem hh₀)
    rw [inv_inv] at h1
    exact G.mul_mem h1 hh₀
  have hinj : ∀ s ∈ T, ∀ t ∈ T, s⁻¹ * (x⁻¹ * s * x) = t⁻¹ * (x⁻¹ * t * x) → s = t := by
    intro s hs t ht hst
    have hu : x⁻¹ * (t * s⁻¹) * x = t * s⁻¹ := by
      have ht' : x⁻¹ * t * x = t * (s⁻¹ * (x⁻¹ * s * x)) := by
        rw [hst]
        group
      calc x⁻¹ * (t * s⁻¹) * x = (x⁻¹ * t * x) * (x⁻¹ * s * x)⁻¹ := by group
        _ = t * s⁻¹ := by rw [ht']; group
    have hmem : t * s⁻¹ ∈ T ⊓ rightConjugate T x := by
      refine ⟨T.mul_mem ht (T.inv_mem hs), ?_⟩
      rw [← hu]
      exact conj_mem_rightConjugate (T.mul_mem ht (T.inv_mem hs)) x
    rw [hinf', Subgroup.mem_bot] at hmem
    exact (mul_inv_eq_one.mp hmem).symm
  have hsurj : ∀ w ∈ W ⊓ G, ∃ t ∈ T, w = t⁻¹ * (x⁻¹ * t * x) := by
    let φ : T → (W ⊓ G : Subgroup X) := fun t =>
      ⟨(t : X)⁻¹ * (x⁻¹ * t * x), hmap t t.2⟩
    have hφ : Function.Injective φ := fun s t hst =>
      Subtype.ext (hinj s s.2 t t.2 (congrArg Subtype.val hst))
    have hbij := hφ.bijective_of_nat_card_le h.card_W_inf_G.le
    intro w hw
    obtain ⟨t, ht⟩ := hbij.2 ⟨w, hw⟩
    exact ⟨t, t.2, (congrArg Subtype.val ht).symm⟩
  refine ⟨hmap, hinj, hsurj, ?_⟩
  intro w hw
  obtain ⟨t, ht, rfl⟩ := hsurj w hw
  calc x⁻¹ * (t⁻¹ * (x⁻¹ * t * x)) * x = (x⁻¹ * t * x)⁻¹ * (x⁻¹ * (x⁻¹ * t * x) * x) := by
        group
    _ = (x⁻¹ * t * x)⁻¹ * t := by rw [hx2C t ht]
    _ = (t⁻¹ * (x⁻¹ * t * x))⁻¹ := by group

end Hyp45

theorem lemma_4_5_three [Finite X] {G T S Q H : Subgroup X} {g : X} (h : Hyp45 G T S Q H g)
    (hq : QuotientRankTwo (S ⊓ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X)) (H ⊓ S)) :
    IsElemAbelian 2 T := by
  set W := T ⊔ rightConjugate T g with hWdef
  obtain ⟨u, hu, v, hv, huH, hvH, huvH, hu2, hv2, hc⟩ := hq
  have hnotH : ∀ {y : X}, y ∈ S → y ∉ H ⊓ S → y ∉ H := fun hyS hy hyH => hy ⟨hyH, hyS⟩
  have huv2 : (u * v) ^ 2 ∈ H ⊓ S := by
    have hc' : u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
    have hvu : v * u ^ 2 * v⁻¹ ∈ H ⊓ S :=
      (Subgroup.mem_normalizer_iff.mp hv.2 _).mp hu2
    have heq : (u * v) ^ 2 = (u * v * u⁻¹ * v⁻¹) * (v * u ^ 2 * v⁻¹) * v ^ 2 := by
      simp only [pow_two]; group
    rw [heq]
    exact (H ⊓ S).mul_mem ((H ⊓ S).mul_mem hc hvu) hv2
  have huvN : u * v ∈ S ⊓ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X) :=
    (S ⊓ _).mul_mem hu hv
  obtain ⟨hmapu, hinju, -, hinvu⟩ := h.commutator_map hu.1 hu.2 (hnotH hu.1 huH) hu2.1
  obtain ⟨-, -, -, hinvv⟩ := h.commutator_map hv.1 hv.2 (hnotH hv.1 hvH) hv2.1
  obtain ⟨-, -, -, hinvuv⟩ := h.commutator_map huvN.1 huvN.2 (hnotH huvN.1 huvH) huv2.1
  have hexp : ∀ w ∈ W ⊓ G, w ^ 2 = 1 := by
    intro w hw
    have h1 := hinvuv w hw
    have h2 : (u * v)⁻¹ * w * (u * v) = w := by
      calc (u * v)⁻¹ * w * (u * v) = v⁻¹ * (u⁻¹ * w * u) * v := by group
        _ = v⁻¹ * w⁻¹ * v := by rw [hinvu w hw]
        _ = (v⁻¹ * w * v)⁻¹ := by group
        _ = w := by rw [hinvv w hw, inv_inv]
    rw [h2] at h1
    calc w ^ 2 = w * w := pow_two w
      _ = w * w⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel w
  have hWcomm : W ≤ Subgroup.centralizer (W : Set X) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr h.facts.2.2.2
  refine ⟨h.isMulCommutative, fun t ht => ?_⟩
  have htW : t ∈ W := Subgroup.mem_sup_left ht
  have hytW : u⁻¹ * t * u ∈ W := (hmapu t ht).1 |> fun hw =>
    by simpa using W.mul_mem htW hw
  have hcomm : t⁻¹ * (u⁻¹ * t * u) = (u⁻¹ * t * u) * t⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (hWcomm hytW) _ (W.inv_mem htW))
  have hsq : (t ^ 2)⁻¹ * (u⁻¹ * t ^ 2 * u) = (t⁻¹ * (u⁻¹ * t * u)) ^ 2 := by
    calc (t ^ 2)⁻¹ * (u⁻¹ * t ^ 2 * u) = t⁻¹ * (t⁻¹ * (u⁻¹ * t * u)) * (u⁻¹ * t * u) := by
          simp only [pow_two]; group
      _ = t⁻¹ * ((u⁻¹ * t * u) * t⁻¹) * (u⁻¹ * t * u) := by rw [hcomm]
      _ = (t⁻¹ * (u⁻¹ * t * u)) ^ 2 := by simp only [pow_two]; group
  have h1 : (t ^ 2)⁻¹ * (u⁻¹ * t ^ 2 * u) = (1 : X)⁻¹ * (u⁻¹ * 1 * u) := by
    rw [hsq, hexp _ (hmapu t ht)]
    group
  exact hinju (t ^ 2) (T.pow_mem ht 2) 1 T.one_mem h1

theorem lemma_4_5_four [Finite X] {G T S Q H : Subgroup X} {g : X} (h : Hyp45 G T S Q H g) :
    omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤
      omegaOne (S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X)) ⊓
        Subgroup.centralizer (omegaOne (S ⊓ Subgroup.normalizer
          ((T ⊔ rightConjugate T g : Subgroup X) : Set X)) : Set X) := by
  set W := T ⊔ rightConjugate T g with hWdef
  have hWNW : W ≤ S ⊓ Subgroup.normalizer (W : Set X) :=
    le_inf (h.W_le.trans inf_le_right) Subgroup.le_normalizer
  refine le_inf (omegaOne_mono (inf_le_left.trans hWNW)) ?_
  rw [Subgroup.le_centralizer_iff]
  refine (Subgroup.closure_le _).mpr fun y hy => ?_
  obtain ⟨hyN, hy2⟩ := hy
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  have hwC : w ∈ Subgroup.centralizer {y} := by
    refine ((Subgroup.closure_le _).mpr fun w' hw' => ?_) hw
    obtain ⟨hw'W, hw'2⟩ := hw'
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    by_cases hyH : y ∈ H
    · have hyC := (h.inf_eq_centralizer_W.le ⟨hyH, hyN.1⟩).2
      exact (Subgroup.mem_centralizer_iff.mp hyC w' hw'W.1)
    · have hinv := (h.commutator_map hyN.1 (h.normalizer_W_le hyN) hyH
        (by rw [hy2]; exact H.one_mem)).2.2.2 w' hw'W
      have hw'inv : w'⁻¹ = w' := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hw'2]
      rw [hw'inv] at hinv
      calc w' * y = y * (y⁻¹ * w' * y) := by group
        _ = y * w' := by rw [hinv]
  exact Subgroup.mem_centralizer_singleton_iff.mp hwC

theorem exists_two_ne_one [Finite X] {E : Subgroup X} (hE : 4 ≤ Nat.card E) :
    ∃ u ∈ E, ∃ v ∈ E, u ≠ 1 ∧ v ≠ 1 ∧ v ≠ u := by
  have hcard : 2 < (E : Set X).ncard := by
    have : Nat.card E = (E : Set X).ncard := Nat.card_coe_set_eq _
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcard
  by_cases ha1 : a = 1
  · subst ha1
    exact ⟨b, hb, c, hc, Ne.symm hab, Ne.symm hac, Ne.symm hbc⟩
  · by_cases hb1 : b = 1
    · subst hb1
      exact ⟨a, ha, c, hc, ha1, Ne.symm hbc, Ne.symm hac⟩
    · exact ⟨a, ha, b, hb, ha1, hb1, Ne.symm hab⟩

theorem lemma_4_5_five [Finite X] {G T S Q H : Subgroup X} {g : X} (h : Hyp45 G T S Q H g)
    (hm : 1 < pRank 2 T) {y : X} (hy : y ∈ G)
    (hVS : rightConjugate (omegaOne T) y ≤
      S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X))
    (hVW : ¬ rightConjugate (omegaOne T) y ≤ T ⊔ rightConjugate T g) :
    rightConjugate (omegaOne T) y ⊓ H = ⊥ ∧ omegaOne T = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := T ⊔ rightConjugate T g with hWdef
  set V := rightConjugate (omegaOne T) y with hVdef
  have hVH : V ⊓ H = ⊥ := by
    by_contra hne
    obtain ⟨⟨v, hvV, hvH⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    have hvS : v ∈ S := (hVS hvV).1
    have hvCW : v ∈ Subgroup.centralizer (W : Set X) :=
      (h.inf_eq_centralizer_W.le ⟨hvH, hvS⟩).2
    have hF₁ := h.frame.rightConjugate_frame hy
    have h43₁ := h.hyp43.rightConjugate_hyp hy
    have hVT₁ : V ≤ rightConjugate T y := rightConjugate_le_rightConjugate (omegaOne_le T) y
    have hGT₁ : G ⊔ rightConjugate T y = G ⊔ T := sup_rightConjugate hy
    have hWS : W ≤ S := h.W_le.trans inf_le_right
    have hWH₁ : W ≤ rightConjugate H y := fun w hw =>
      h43₁.centralizer_le hF₁ (hVT₁ hvV) hv1' ⟨hGT₁ ▸ h.le_sup (hWS hw),
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hvCW w hw)⟩
    have hVH₁ : V ≤ rightConjugate H y := hVT₁.trans h43₁.le_H
    have hW2 : IsPGroup 2 W := h.isPGroup_S.to_le hWS
    have hV2 : IsPGroup 2 V := h.isPGroup_S.to_le (hVS.trans inf_le_left)
    have hR₀2 : IsPGroup 2 (W ⊔ V : Subgroup X) :=
      IsPGroup.to_sup_of_normal_left' hW2 hV2 (hVS.trans inf_le_right)
    obtain ⟨R, hR, hR₀R⟩ := exists_isSylowOf_le hR₀2 (sup_le hWH₁ hVH₁)
    have hRQ := hR.inf_of_le_normalizer h43₁.le h43₁.le_normalizer
    obtain ⟨c, hcQ, hcT⟩ := exists_rightConjugate_eq_of_isSylowOf hRQ h43₁.sylow
    have hycGT : y * c ∈ G ⊔ T :=
      (G ⊔ T).mul_mem (Subgroup.mem_sup_left hy)
        (hGT₁ ▸ h43₁.le_sup (h43₁.le hcQ))
    obtain ⟨-, -, g₂, hg₂, -, hrc₂⟩ := h.frame.exists_rightConjugate_eq hycGT
    have hT₂eq : R ⊓ rightConjugate Q y = rightConjugate T g₂ := by
      rw [← hcT, rightConjugate_mul, hrc₂]
    have hF₂ := h.frame.rightConjugate_frame hg₂
    have hT₂comm : IsMulCommutative (rightConjugate T g₂) :=
      isMulCommutative_rightConjugate h.isMulCommutative g₂
    have hVT₂ : V ≤ rightConjugate T g₂ := by
      rw [← hT₂eq]
      exact le_inf (le_sup_right.trans hR₀R) (hVT₁.trans h43₁.le_Q)
    have hRN : R ≤ Subgroup.normalizer (rightConjugate T g₂ : Set X) := by
      rw [← hT₂eq]
      intro r hr
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hr, h43₁.le_normalizer (hR.le hr)⟩
    have hRGT : R ≤ G ⊔ T := hR.le.trans (h43₁.le_sup.trans hGT₁.le)
    have hT₂R : rightConjugate T g₂ ≤ R := hT₂eq ▸ inf_le_left
    have hRC : R ≤ Subgroup.centralizer (rightConjugate T g₂ : Set X) := by
      have hle := inf_normalizer_le_centralizer hF₂
        (by rw [sup_rightConjugate hg₂]; exact hRGT) hT₂R hT₂comm
      rwa [inf_eq_left.mpr hRN] at hle
    have hT₂C : rightConjugate T g₂ ≤ Subgroup.centralizer (W : Set X) := by
      rw [Subgroup.le_centralizer_iff]
      exact (le_sup_left.trans hR₀R).trans hRC
    have hT₂GT : rightConjugate T g₂ ≤ G ⊔ T := hT₂R.trans hRGT
    have hCN : (G ⊔ T) ⊓ Subgroup.centralizer (W : Set X) ≤
        (G ⊔ T) ⊓ Subgroup.normalizer (T : Set X) :=
      inf_le_inf_left _ ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)).trans
        (Subgroup.centralizer_le_normalizer _))
    have hSC : S ⊓ Subgroup.normalizer (T : Set X) ≤
        (G ⊔ T) ⊓ Subgroup.centralizer (W : Set X) := by
      rw [← h.inf_eq_normalizer, h.inf_eq_centralizer_W]
      exact inf_le_inf_right _ h.le_sup
    have hsylC := h.sylowFrame.sylow_normalizer.of_le hSC hCN
    obtain ⟨c', hc'C, hc'le⟩ := exists_rightConjugate_le_of_isSylowOf hsylC
      (isPGroup_rightConjugate h.frame.isPGroup g₂) (le_inf hT₂GT hT₂C)
    have hg₂c' : g₂ * c' ∈ G ⊔ T := (G ⊔ T).mul_mem (Subgroup.mem_sup_left hg₂) hc'C.1
    obtain ⟨-, -, g₃, hg₃, -, hrc₃⟩ := h.frame.exists_rightConjugate_eq hg₂c'
    have hT₃ : rightConjugate (rightConjugate T g₂) c' = rightConjugate T g₃ := by
      rw [rightConjugate_mul, hrc₃]
    have hT₃W : rightConjugate (rightConjugate T g₂) c' ≤ W := by
      rw [hT₃, hWdef, ← h.weakClosure]
      apply rightConjugate_le_relativeWeakClosure hg₃
      rw [← hT₃, h.inf_eq_normalizer]
      exact hc'le
    apply hVW
    have hc'W : rightConjugate W c'⁻¹ = W :=
      (rightConjugate_eq_self_iff W c'⁻¹).mpr
        (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hc'C.2))
    have hle : rightConjugate V c' ≤ W := (rightConjugate_le_rightConjugate hVT₂ c').trans hT₃W
    calc V = rightConjugate (rightConjugate V c') c'⁻¹ := by
          rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
      _ ≤ rightConjugate W c'⁻¹ := rightConjugate_le_rightConjugate hle _
      _ = W := hc'W
  refine ⟨hVH, ?_⟩
  obtain ⟨E, hET, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) T
  have hEΩ : E ≤ omegaOne T := fun x hx => mem_omegaOne (hET hx) (hE.2 x hx)
  have hE'V : rightConjugate E y ≤ V := rightConjugate_le_rightConjugate hEΩ y
  have hE'card : 4 ≤ Nat.card (rightConjugate E y) := by
    rw [rightConjugate_card, hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 T := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨u, hu, v, hv, hu1, hv1, hvu⟩ := exists_two_ne_one hE'card
  have hE'2 : ∀ x ∈ rightConjugate E y, x ^ 2 = 1 := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := hE.2 _ hx
    have heq : x ^ 2 = y⁻¹ * (y * x * y⁻¹) ^ 2 * y := by simp only [pow_two]; group
    rw [heq, h1]
    group
  have hE'comm : IsMulCommutative (rightConjugate E y) := isMulCommutative_rightConjugate hE.1 y
  have hNV : V ≤ S ⊓ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X) :=
    le_inf (hVS.trans inf_le_left) (hVS.trans h.normalizer_W_le)
  have hnot : ∀ x ∈ V, x ≠ 1 → x ∉ H ⊓ S := by
    intro x hx hx1 hxHS
    have hmem : x ∈ V ⊓ H := ⟨hx, hxHS.1⟩
    rw [hVH, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have huv1 : u * v ≠ 1 := by
    intro h1
    apply hvu
    have hu2 := hE'2 u hu
    calc v = u⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      _ = u := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hu2]
  have hcomm : u * v = v * u :=
    congrArg Subtype.val (hE'comm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hel : IsElemAbelian 2 T := by
    refine lemma_4_5_three h ⟨u, hNV (hE'V hu), v, hNV (hE'V hv), hnot u (hE'V hu) hu1,
      hnot v (hE'V hv) hv1, hnot (u * v) (V.mul_mem (hE'V hu) (hE'V hv)) huv1, ?_, ?_, ?_⟩
    · rw [hE'2 u hu]; exact (H ⊓ S).one_mem
    · rw [hE'2 v hv]; exact (H ⊓ S).one_mem
    · rw [hcomm, show v * u * u⁻¹ * v⁻¹ = (1 : X) by group]; exact (H ⊓ S).one_mem
  exact le_antisymm (omegaOne_le T) (le_omegaOne hel.2)

theorem lemma_4_5_five_weakClosure [Finite X] {G T S Q H : Subgroup X} {g : X}
    (h : Hyp45 G T S Q H g) (hm : 1 < pRank 2 T)
    (hWS : relativeWeakClosure G T S = T ⊔ rightConjugate T g) :
    relativeWeakClosure G (omegaOne T) S = omegaOne (T ⊔ rightConjugate T g) := by
  set W := T ⊔ rightConjugate T g with hWdef
  have hSN : S ≤ Subgroup.normalizer (W : Set X) := by
    intro s hs
    obtain ⟨t₀, ht₀, h₀, hh₀, rfl⟩ := h.frame.mem_sup_iff.mp (h.le_sup hs)
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.mem_sup_left ht₀)) ?_
    rw [← hWS]
    apply relative_weak_closure_parent_normalizer G T S
    refine ⟨hh₀, Subgroup.le_normalizer ?_⟩
    simpa using S.mul_mem (S.inv_mem (h.le_S ht₀)) hs
  apply le_antisymm
  · apply iSup_le
    intro c
    apply iSup_le
    intro hc
    have hV : conjugateSubgroup c.val (omegaOne T) = rightConjugate (omegaOne T) c.val⁻¹ := by
      unfold rightConjugate
      rw [inv_inv]
    rw [hV] at hc ⊢
    have hcG : c.val⁻¹ ∈ G := G.inv_mem c.2
    have hVW : rightConjugate (omegaOne T) c.val⁻¹ ≤ W := by
      by_contra hVW
      have hΩ := (lemma_4_5_five h hm hcG (le_inf hc (hc.trans hSN)) hVW).2
      apply hVW
      rw [hΩ, ← hWS]
      rw [hΩ] at hc
      exact rightConjugate_le_relativeWeakClosure hcG hc
    rw [rightConjugate_omegaOne]
    refine (Subgroup.closure_le _).mpr fun x hx' => ?_
    obtain ⟨hx, hx2⟩ := hx'
    refine mem_omegaOne ?_ hx2
    apply hVW
    rw [rightConjugate_omegaOne]
    exact mem_omegaOne hx hx2
  · refine (Subgroup.closure_le _).mpr fun w hw' => ?_
    obtain ⟨hw, hw2⟩ := hw'
    have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1).trans
        (Subgroup.centralizer_le_normalizer _)
    have hwmem : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hwmem
    have hab : a * b = b * a :=
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1 ha) b hb).symm
    have ha2 : a ^ 2 = 1 := by
      have h1 : a ^ 2 * b ^ 2 = 1 := by
        rw [← hw2]
        calc a ^ 2 * b ^ 2 = a * (a * b) * b := by simp only [pow_two, mul_assoc]
          _ = a * (b * a) * b := by rw [hab]
          _ = (a * b) ^ 2 := by simp only [pow_two, mul_assoc]
      have hmem : a ^ 2 ∈ T ⊓ rightConjugate T g := by
        refine ⟨T.pow_mem ha 2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 2)
      rw [h.facts.2.1, Subgroup.mem_bot] at hmem
      exact hmem
    have hb2 : b ^ 2 = 1 := by
      have h1 : a ^ 2 * b ^ 2 = 1 := by
        rw [← hw2]
        calc a ^ 2 * b ^ 2 = a * (a * b) * b := by simp only [pow_two, mul_assoc]
          _ = a * (b * a) * b := by rw [hab]
          _ = (a * b) ^ 2 := by simp only [pow_two, mul_assoc]
      rwa [ha2, one_mul] at h1
    refine Subgroup.mul_mem _ ?_ ?_
    · have h1 : omegaOne T ≤ relativeWeakClosure G (omegaOne T) S := by
        have := rightConjugate_le_relativeWeakClosure (G := G) (T := omegaOne T) (B := S)
          G.one_mem (by rw [rightConjugate_one]; exact (omegaOne_le T).trans h.le_S)
        rwa [rightConjugate_one] at this
      exact h1 (mem_omegaOne ha ha2)
    · have hbΩ : b ∈ rightConjugate (omegaOne T) g := by
        rw [rightConjugate_omegaOne]
        exact mem_omegaOne hb hb2
      refine rightConjugate_le_relativeWeakClosure h.mem ?_ hbΩ
      rw [rightConjugate_omegaOne]
      exact (omegaOne_le _).trans (h.conj_le.trans inf_le_right)

end CFSG.ComponentClassification.AschbacherTheorem3
