module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexBasic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_normalizer_relativeWeakClosure {G T S : Subgroup X} (hF : Frame G T)
    (hSGT : S ≤ G ⊔ T) (hTS : T ≤ S) :
    S ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X) := by
  intro s hs
  obtain ⟨t₀, ht₀, h₀, hh₀, rfl⟩ := hF.mem_sup_iff.mp (hSGT hs)
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer
    (subgroup_le_relative_weak_closure G T S hTS ht₀)) ?_
  apply relative_weak_closure_parent_normalizer G T S
  refine ⟨hh₀, Subgroup.le_normalizer ?_⟩
  simpa using S.mul_mem (S.inv_mem (hTS ht₀)) hs

theorem rightConjugate_eq_of_inf_ne_bot {G T S Q H : Subgroup X} (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) (hab : IsMulCommutative T) {c d : X} (hc : c ∈ G) (hd : d ∈ G)
    (hcS : rightConjugate T c ≤ S) (hdS : rightConjugate T d ≤ S)
    (hne : rightConjugate T c ⊓ rightConjugate T d ≠ ⊥) :
    rightConjugate T c = rightConjugate T d := by
  obtain ⟨⟨t, htc, htd⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have hFd := h.toFrame.rightConjugate_frame hd
  have h43d := h43.rightConjugate_hyp hd
  have hcomm : IsMulCommutative (rightConjugate T c) := isMulCommutative_rightConjugate hab c
  rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hcomm
  have hcC : rightConjugate T c ≤ Subgroup.centralizer {t} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hcomm hx) t htc).symm
  have hcH : rightConjugate T c ≤ rightConjugate H d := fun x hx =>
    h43d.centralizer_le hFd htd ht1' ⟨by rw [sup_rightConjugate hd]; exact h.sylow.le (hcS hx),
      hcC hx⟩
  by_contra hcd
  have hdc : d⁻¹ * c ∈ G := G.mul_mem (G.inv_mem hd) hc
  have hrc : rightConjugate (rightConjugate T d) (d⁻¹ * c) = rightConjugate T c := by
    rw [rightConjugate_mul, mul_inv_cancel_left]
  obtain ⟨-, hinf, -, -⟩ := lemma_4_4_two hFd h43d h.sylow.isPGroup hdS hdc
    (by rw [hrc]; exact le_inf hcS hcH) (by rw [hrc]; exact hcd)
  rw [hrc] at hinf
  have hmem : t ∈ rightConjugate T d ⊓ rightConjugate T c := ⟨htd, htc⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact ht1' hmem

structure Elem47 (G T S Q H : Subgroup X) (g y : X) : Prop where
  hyp45 : Hyp45 G T S Q H g
  inf_eq : H ⊓ S = T ⊔ rightConjugate T g
  pRank_lt : 1 < pRank 2 T
  mem : y ∈ G
  le_normalizer : rightConjugate T y ≤
    S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X)
  not_le : ¬ rightConjugate T y ≤ T ⊔ rightConjugate T g

namespace Elem47

variable {G T S Q H : Subgroup X} {g y : X}

theorem inf_H (e : Elem47 G T S Q H g y) : rightConjugate T y ⊓ H = ⊥ :=
  e.hyp45.inf_eq_bot_of_not_le e.mem le_rfl e.le_normalizer e.not_le

theorem le_S (e : Elem47 G T S Q H g y) : rightConjugate T y ≤ S :=
  e.le_normalizer.trans inf_le_left

theorem M_le_S (e : Elem47 G T S Q H g y) : T ⊔ rightConjugate T g ≤ S :=
  e.hyp45.W_le.trans inf_le_right

theorem elem (e : Elem47 G T S Q H g y) : IsElemAbelian 2 T := by
  have h := e.hyp45
  have hΩV : rightConjugate (omegaOne T) y ≤ rightConjugate T y :=
    rightConjugate_le_rightConjugate (omegaOne_le T) y
  have hnot : ¬ rightConjugate (omegaOne T) y ≤ T ⊔ rightConjugate T g := by
    intro hle
    have hbot : rightConjugate (omegaOne T) y = ⊥ := by
      rw [eq_bot_iff, ← e.inf_H]
      exact le_inf hΩV (hle.trans (e.inf_eq ▸ inf_le_left))
    rw [rightConjugate_eq_bot_iff] at hbot
    obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution h.frame.isPGroup h.ne_bot
    have hmem : t₀ ∈ omegaOne T := mem_omegaOne ht₀ (by rw [← ht₀2]; exact pow_orderOf_eq_one t₀)
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at ht₀2
    omega
  have hΩ := (lemma_4_5_five h e.pRank_lt e.mem (hΩV.trans e.le_normalizer) hnot).2
  refine ⟨h.isMulCommutative, fun x hx => ?_⟩
  rw [← hΩ] at hx
  exact ((mem_omegaOne_iff h.isMulCommutative).mp hx).2

theorem sq_T (e : Elem47 G T S Q H g y) : ∀ t ∈ T, t ^ 2 = 1 := e.elem.2

theorem sq_M (e : Elem47 G T S Q H g y) : ∀ w ∈ T ⊔ rightConjugate T g, w ^ 2 = 1 := by
  have h := e.hyp45
  have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1).trans
      (Subgroup.centralizer_le_normalizer _)
  intro w hw
  have hwmem : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
    exact hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hwmem
  have hab : a * b = b * a :=
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1 ha) b hb).symm
  have hb2 : b ^ 2 = 1 := by
    have hb' : g * b * g⁻¹ ∈ T := (mem_rightConjugate_iff T g b).mp hb
    have h1 := e.sq_T _ hb'
    rw [show b ^ 2 = g⁻¹ * (g * b * g⁻¹) ^ 2 * g by simp only [pow_two]; group, h1]
    group
  calc (a * b) ^ 2 = a * (b * a) * b := by simp only [pow_two, mul_assoc]
    _ = a * (a * b) * b := by rw [hab]
    _ = a ^ 2 * b ^ 2 := by simp only [pow_two, mul_assoc]
    _ = 1 := by rw [e.sq_T a ha, hb2, one_mul]

theorem sq_V (e : Elem47 G T S Q H g y) : ∀ v ∈ rightConjugate T y, v ^ 2 = 1 := by
  intro v hv
  rw [mem_rightConjugate_iff] at hv
  have h1 := e.sq_T _ hv
  rw [show v ^ 2 = y⁻¹ * (y * v * y⁻¹) ^ 2 * y by simp only [pow_two]; group, h1]
  group

omit [Finite X] in
theorem inv_eq_of_sq {x : X} (hx : x ^ 2 = 1) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, hx]

theorem comm_map (e : Elem47 G T S Q H g y) {v : X} (hv : v ∈ rightConjugate T y)
    (hv1 : v ≠ 1) :
    (∀ t ∈ T, t⁻¹ * (v⁻¹ * t * v) ∈ (T ⊔ rightConjugate T g) ⊓ G) ∧
      (∀ s ∈ T, ∀ t ∈ T, s⁻¹ * (v⁻¹ * s * v) = t⁻¹ * (v⁻¹ * t * v) → s = t) ∧
      (∀ w ∈ (T ⊔ rightConjugate T g) ⊓ G, ∃ t ∈ T, w = t⁻¹ * (v⁻¹ * t * v)) ∧
      (∀ w ∈ (T ⊔ rightConjugate T g) ⊓ G, v⁻¹ * w * v = w⁻¹) := by
  have hvS : v ∈ S := e.le_S hv
  have hvN : v ∈ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X) := by
    rw [e.inf_eq]
    exact (e.le_normalizer hv).2
  have hvH : v ∉ H := by
    intro hvH
    have hmem : v ∈ rightConjugate T y ⊓ H := ⟨hv, hvH⟩
    rw [e.inf_H, Subgroup.mem_bot] at hmem
    exact hv1 hmem
  have hv2 : v ^ 2 ∈ H := by rw [e.sq_V v hv]; exact H.one_mem
  exact e.hyp45.commutator_map hvS hvN hvH hv2

theorem V_centralizes_Z (e : Elem47 G T S Q H g y) {v : X} (hv : v ∈ rightConjugate T y)
    {z : X} (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) : v * z = z * v := by
  by_cases hv1 : v = 1
  · rw [hv1, one_mul, mul_one]
  have hinv := (e.comm_map hv hv1).2.2.2 z hz
  rw [inv_eq_of_sq (e.sq_M z hz.1)] at hinv
  calc v * z = v * (v⁻¹ * z * v) := by rw [hinv]
    _ = z * v := by group

theorem V_le_normalizer_M (e : Elem47 G T S Q H g y) :
    rightConjugate T y ≤ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) :=
  e.le_normalizer.trans inf_le_right

theorem A_le_S (e : Elem47 G T S Q H g y) :
    rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ≤ S :=
  sup_le e.le_S e.M_le_S

theorem V_inf_M (e : Elem47 G T S Q H g y) :
    (T ⊔ rightConjugate T g) ⊓ rightConjugate T y = ⊥ := by
  rw [eq_bot_iff, ← e.inf_H, inf_comm]
  exact inf_le_inf_left _ (le_inf_iff.mpr ⟨by rw [← e.inf_eq]; exact inf_le_left,
    le_rfl⟩ |>.trans inf_le_left)

theorem card_A (e : Elem47 G T S Q H g y) :
    Nat.card (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) : Subgroup X) =
      Nat.card T ^ 3 := by
  rw [sup_comm, card_sup_of_le_normalizer e.V_le_normalizer_M e.V_inf_M, e.hyp45.card_W,
    rightConjugate_card]
  ring

theorem card_Z (e : Elem47 G T S Q H g y) :
    Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) = Nat.card T :=
  e.hyp45.card_W_inf_G

theorem M_comm (e : Elem47 G T S Q H g y) :
    T ⊔ rightConjugate T g ≤ Subgroup.centralizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) :=
  Subgroup.le_centralizer_iff_isMulCommutative.mpr e.hyp45.facts.2.2.2

theorem Z_centralizes_A (e : Elem47 G T S Q H g y) :
    rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ≤
      Subgroup.centralizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
  refine sup_le (fun v hv => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (e.V_centralizes_Z hv hz).symm) ?_
  exact (e.M_comm.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)))

theorem mem_A (e : Elem47 G T S Q H g y) {a : X}
    (ha : a ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) :
    ∃ v ∈ rightConjugate T y, ∃ t ∈ T, ∃ z ∈ (T ⊔ rightConjugate T g) ⊓ G, a = v * t * z := by
  have hamem : a ∈ (rightConjugate T y : Set X) * ((T ⊔ rightConjugate T g : Subgroup X) :
      Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ e.V_le_normalizer_M]
    exact ha
  obtain ⟨v, hv, m, hm, rfl⟩ := Set.mem_mul.mp hamem
  obtain ⟨hdec, -⟩ := e.hyp45.W_decomp
  have hTZ : T ≤ Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) :=
    (le_sup_left.trans (e.M_comm.trans (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr inf_le_left)))).trans (Subgroup.centralizer_le_normalizer _)
  have hmmem : m ∈ (T : Set X) * (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTZ, ← hdec]
    exact hm
  obtain ⟨t, ht, z, hz, rfl⟩ := Set.mem_mul.mp hmmem
  exact ⟨v, hv, t, ht, z, hz, by group⟩

theorem sq_vtz (e : Elem47 G T S Q H g y) {v t z : X} (hv : v ∈ rightConjugate T y)
    (ht : t ∈ T) (hz : z ∈ (T ⊔ rightConjugate T g) ⊓ G) :
    (v * t * z) ^ 2 = t⁻¹ * (v⁻¹ * t * v) := by
  have hzA : z ∈ Subgroup.centralizer (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) :
      Subgroup X) : Set X) :=
    (Subgroup.le_centralizer_iff.mp e.Z_centralizes_A) hz
  have hvtA : v * t ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right (Subgroup.mem_sup_left ht))
  have hzc : (v * t) * z = z * (v * t) := Subgroup.mem_centralizer_iff.mp hzA _ hvtA
  have hc : t⁻¹ * (v⁻¹ * t * v) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    by_cases hv1 : v = 1
    · rw [hv1]
      simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    · exact (e.comm_map hv hv1).1 t ht
  have hcA : t⁻¹ * (v⁻¹ * t * v) ∈ Subgroup.centralizer
      (((rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) : Subgroup X) : Set X) :=
    (Subgroup.le_centralizer_iff.mp e.Z_centralizes_A) hc
  have htA : t ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left ht)
  have htc : t * (t⁻¹ * (v⁻¹ * t * v)) = (t⁻¹ * (v⁻¹ * t * v)) * t :=
    Subgroup.mem_centralizer_iff.mp hcA t htA
  have hv' : v⁻¹ = v := inv_eq_of_sq (e.sq_V v hv)
  have hz2 : z ^ 2 = 1 := e.sq_M z hz.1
  have ht2 : t ^ 2 = 1 := e.sq_T t ht
  calc (v * t * z) ^ 2 = (v * t) * (v * t) * (z * z) := by
        rw [pow_two]
        calc v * t * z * (v * t * z) = (v * t) * (z * (v * t)) * z := by group
          _ = (v * t) * ((v * t) * z) * z := by rw [hzc]
          _ = (v * t) * (v * t) * (z * z) := by group
    _ = (v * t) * (v * t) := by rw [← pow_two z, hz2, mul_one]
    _ = t * (t⁻¹ * (v⁻¹ * t * v)) * t := by
        rw [hv']
        group
    _ = (t⁻¹ * (v⁻¹ * t * v)) * (t * t) := by rw [htc]; group
    _ = t⁻¹ * (v⁻¹ * t * v) := by rw [← pow_two t, ht2, mul_one]

theorem VZ_comm (e : Elem47 G T S Q H g y) :
    IsMulCommutative (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G : Subgroup X) := by
  refine isMulCommutative_sup (isMulCommutative_rightConjugate e.elem.1 y)
    (isMulCommutative_of_le inf_le_left e.hyp45.facts.2.2.2) ?_
  exact fun v hv => Subgroup.mem_centralizer_iff.mpr fun z hz => (e.V_centralizes_Z hv hz).symm

theorem card_VZ (e : Elem47 G T S Q H g y) :
    Nat.card (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G : Subgroup X) =
      Nat.card T * Nat.card T := by
  have hZN : rightConjugate T y ≤
      Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (e.V_centralizes_Z hv hz).symm)
  have hinf : (T ⊔ rightConjugate T g) ⊓ G ⊓ rightConjugate T y = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans e.V_inf_M.le)
  rw [sup_comm, card_sup_of_le_normalizer hZN hinf, e.card_Z, rightConjugate_card]

theorem sq_eq_one_mem (e : Elem47 G T S Q H g y) {a : X}
    (ha : a ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (ha2 : a ^ 2 = 1) :
    a ∈ ((T ⊔ rightConjugate T g : Subgroup X) : Set X) ∪
      ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
  obtain ⟨v, hv, t, ht, z, hz, rfl⟩ := e.mem_A ha
  rw [e.sq_vtz hv ht hz] at ha2
  by_cases hv1 : v = 1
  · left
    rw [hv1, one_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) hz.1
  · right
    have ht1 : t = 1 := (e.comm_map hv hv1).2.1 t ht 1 T.one_mem (by rw [ha2]; group)
    rw [ht1, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hz)

theorem V_ne_bot (e : Elem47 G T S Q H g y) : rightConjugate T y ≠ ⊥ := by
  rw [Ne, rightConjugate_eq_bot_iff]
  exact e.hyp45.ne_bot

theorem comm_mem_Z (e : Elem47 G T S Q H g y) {v t : X} (hv : v ∈ rightConjugate T y)
    (ht : t ∈ T) : t⁻¹ * (v⁻¹ * t * v) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
  by_cases hv1 : v = 1
  · rw [hv1]
    simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · exact (e.comm_map hv hv1).1 t ht

theorem conj_eq (e : Elem47 G T S Q H g y) {c : X} (hc : c ∈ G)
    (hcM : rightConjugate T c ≤ T ⊔ rightConjugate T g) :
    ∃ v ∈ rightConjugate T y, rightConjugate T c = rightConjugate T v := by
  have h := e.hyp45
  obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution h.frame.isPGroup h.ne_bot
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht₀2
    omega
  have hφinj : ∀ v ∈ rightConjugate T y, ∀ v' ∈ rightConjugate T y,
      t₀⁻¹ * (v⁻¹ * t₀ * v) = t₀⁻¹ * (v'⁻¹ * t₀ * v') → v = v' := by
    intro v hv v' hv' heq
    have heq' : v⁻¹ * t₀ * v = v'⁻¹ * t₀ * v' := mul_left_cancel heq
    have hvv' : v' * v⁻¹ ∈ Subgroup.centralizer {t₀} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc v' * v⁻¹ * t₀ = v' * (v⁻¹ * t₀ * v) * v⁻¹ := by group
        _ = v' * (v'⁻¹ * t₀ * v') * v⁻¹ := by rw [heq']
        _ = t₀ * (v' * v⁻¹) := by group
    have hvGT : v' * v⁻¹ ∈ G ⊔ T :=
      (G ⊔ T).mul_mem (h.le_sup (e.le_S hv')) ((G ⊔ T).inv_mem (h.le_sup (e.le_S hv)))
    have hvH := h.hyp43.centralizer_le h.frame ht₀ ht₀1 ⟨hvGT, hvv'⟩
    have hmem : v' * v⁻¹ ∈ rightConjugate T y ⊓ H :=
      ⟨Subgroup.mul_mem _ hv' (Subgroup.inv_mem _ hv), hvH⟩
    rw [e.inf_H, Subgroup.mem_bot] at hmem
    exact (mul_inv_eq_one.mp hmem).symm
  have hφsurj : ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, ∃ v ∈ rightConjugate T y,
      t₀⁻¹ * (v⁻¹ * t₀ * v) = z := by
    let φ : rightConjugate T y → ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) :=
      fun v => ⟨t₀⁻¹ * ((v : X)⁻¹ * t₀ * v), e.comm_mem_Z v.2 ht₀⟩
    have hinj : Function.Injective φ := fun v v' hvv =>
      Subtype.ext (hφinj v v.2 v' v'.2 (congrArg Subtype.val hvv))
    have hcard : Nat.card ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) ≤
        Nat.card (rightConjugate T y) := by
      rw [e.card_Z, rightConjugate_card]
    have hbij := hinj.bijective_of_nat_card_le hcard
    intro z hz
    obtain ⟨v, hv⟩ := hbij.2 ⟨z, hz⟩
    exact ⟨v, v.2, congrArg Subtype.val hv⟩
  have hFc := h.frame.rightConjugate_frame hc
  have hTcZ : rightConjugate T c ⊓ ((T ⊔ rightConjugate T g) ⊓ G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left _ inf_le_right).trans hFc.inf_eq_bot.le)
  have hZN : (T ⊔ rightConjugate T g) ⊓ G ≤ Subgroup.normalizer (rightConjugate T c : Set X) :=
    (inf_le_left.trans (e.M_comm.trans (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr hcM)))).trans (Subgroup.centralizer_le_normalizer _)
  have hMeq : rightConjugate T c ⊔ ((T ⊔ rightConjugate T g) ⊓ G) = T ⊔ rightConjugate T g := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hcM inf_le_left)
    rw [card_sup_of_le_normalizer hZN hTcZ, rightConjugate_card, e.card_Z, h.card_W]
  have ht₀mem : t₀ ∈ (rightConjugate T c : Set X) *
      (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN, hMeq]
    exact Subgroup.mem_sup_left ht₀
  obtain ⟨t', ht', z', hz', ht₀eq⟩ := Set.mem_mul.mp ht₀mem
  obtain ⟨v, hv, hvz⟩ := hφsurj z'⁻¹ (Subgroup.inv_mem _ hz')
  have ht'v : v⁻¹ * t₀ * v = t' := by
    calc v⁻¹ * t₀ * v = t₀ * (t₀⁻¹ * (v⁻¹ * t₀ * v)) := by group
      _ = t₀ * z'⁻¹ := by rw [hvz]
      _ = t' := by rw [← ht₀eq]; group
  have ht'1 : t' ≠ 1 := by
    intro h1
    rw [h1, one_mul] at ht₀eq
    apply ht₀1
    have hmem : t₀ ∈ T ⊓ G := ⟨ht₀, ht₀eq ▸ hz'.2⟩
    rw [h.frame.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨-, -, d, hd, -, hrcv⟩ := h.frame.exists_rightConjugate_eq (h.le_sup (e.le_S hv))
  have hvM : rightConjugate T v ≤ T ⊔ rightConjugate T g := by
    rw [← (rightConjugate_eq_self_iff _ v).mpr (e.V_le_normalizer_M hv)]
    exact rightConjugate_le_rightConjugate le_sup_left v
  refine ⟨v, hv, ?_⟩
  rw [hrcv]
  apply rightConjugate_eq_of_inf_ne_bot h.sylowFrame h.hyp43 h.isMulCommutative hc hd
    (hcM.trans e.M_le_S) (hrcv ▸ hvM.trans e.M_le_S)
  intro hbot
  have hmem : t' ∈ rightConjugate T c ⊓ rightConjugate T d :=
    ⟨ht', hrcv ▸ (ht'v ▸ conj_mem_rightConjugate ht₀ v)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ht'1 hmem

theorem normalizer_M (e : Elem47 G T S Q H g y) :
    S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) =
      rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  have h := e.hyp45
  apply le_antisymm
  · rintro n ⟨hnS, hnN⟩
    have hTn : rightConjugate T n ≤ T ⊔ rightConjugate T g := by
      rw [← (rightConjugate_eq_self_iff _ n).mpr hnN]
      exact rightConjugate_le_rightConjugate le_sup_left n
    obtain ⟨-, -, c, hc, -, hrc⟩ := h.frame.exists_rightConjugate_eq (h.le_sup hnS)
    obtain ⟨v, hv, hcv⟩ := e.conj_eq hc (hrc ▸ hTn)
    have hnv : n * v⁻¹ ∈ Subgroup.normalizer (T : Set X) := by
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hrc, hcv, rightConjugate_mul,
        mul_inv_cancel, rightConjugate_one]
    have hnvM : n * v⁻¹ ∈ T ⊔ rightConjugate T g := by
      rw [← e.inf_eq, h.inf_eq_normalizer]
      exact ⟨S.mul_mem hnS (S.inv_mem (e.le_S hv)), hnv⟩
    have heq : n = (n * v⁻¹) * v := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hnvM) (Subgroup.mem_sup_left hv)
  · exact le_inf e.A_le_S (sup_le e.V_le_normalizer_M Subgroup.le_normalizer)

theorem big_eq (e : Elem47 G T S Q H g y) {B : Subgroup X}
    (hBA : B ≤ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hcard : Nat.card T * Nat.card T ≤ Nat.card B) :
    B = T ⊔ rightConjugate T g ∨ B = rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G := by
  have hsub : (B : Set X) ⊆ ((T ⊔ rightConjugate T g : Subgroup X) : Set X) ∪
      ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) :=
    fun b hb => e.sq_eq_one_mem (hBA hb) (hB2 b hb)
  rcases (SubgroupClass.subset_union).mp hsub with hle | hle
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [e.hyp45.card_W]; exact hcard))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle (by rw [e.card_VZ]; exact hcard))

theorem conj_M_eq (e : Elem47 G T S Q H g y) {n : X}
    (hn : n ∈ Subgroup.normalizer
      ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g) : Subgroup X) : Set X)) :
    rightConjugate (T ⊔ rightConjugate T g) n = T ⊔ rightConjugate T g ∨
      rightConjugate (T ⊔ rightConjugate T g) n =
        rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G := by
  apply e.big_eq
  · rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
    exact rightConjugate_le_rightConjugate le_sup_right n
  · intro b hb
    have hb' : n * b * n⁻¹ ∈ T ⊔ rightConjugate T g := (mem_rightConjugate_iff _ n b).mp hb
    have h1 := e.sq_M _ hb'
    rw [show b ^ 2 = n⁻¹ * (n * b * n⁻¹) ^ 2 * n by simp only [pow_two]; group, h1]
    group
  · rw [rightConjugate_card, e.hyp45.card_W]

theorem VZ_ne_M (e : Elem47 G T S Q H g y) :
    rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G ≠ T ⊔ rightConjugate T g := by
  intro heq
  exact e.not_le (le_sup_left.trans heq.le)

theorem relIndex_ne_zero_of_finite (K L : Subgroup X) : K.relIndex L ≠ 0 := by
  intro h0
  have h1 := Subgroup.relIndex_mul_card K L
  rw [h0, zero_mul] at h1
  exact (Nat.card_pos (α := L)).ne h1

theorem relIndex_le_two {K L : Subgroup X} (hKL : K ≤ L)
    (h : ∀ x ∈ L, ∀ x' ∈ L, x ∉ K → x' ∉ K → x * x'⁻¹ ∈ K) : K.relIndex L ≤ 2 := by
  by_cases hLK : L ≤ K
  · rw [Subgroup.relIndex_eq_one.mpr hLK]
    norm_num
  obtain ⟨n₀, hn₀L, hn₀K⟩ := Set.not_subset.mp hLK
  have hsub : (L : Set X) ⊆ (K : Set X) ∪ (fun k => k * n₀) '' (K : Set X) := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨x * n₀⁻¹, h x hx n₀ hn₀L hxK hn₀K, by group⟩
  have hcardL : Nat.card L ≤ 2 * Nat.card K := by
    have hL : Nat.card L = (L : Set X).ncard := Nat.card_coe_set_eq _
    have hK : Nat.card K = (K : Set X).ncard := Nat.card_coe_set_eq _
    rw [hL, hK]
    calc (L : Set X).ncard ≤ ((K : Set X) ∪ (fun k => k * n₀) '' (K : Set X)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (K : Set X).ncard + ((fun k => k * n₀) '' (K : Set X)).ncard :=
          Set.ncard_union_le _ _
      _ ≤ (K : Set X).ncard + (K : Set X).ncard :=
          Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
      _ = 2 * (K : Set X).ncard := by ring
  have h1 := Subgroup.relIndex_mul_card K L
  rw [inf_eq_left.mpr hKL] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : 3 * Nat.card K ≤ K.relIndex L * Nat.card K := Nat.mul_le_mul_right _ hlt
  omega

theorem four_le_card (e : Elem47 G T S Q H g y) : 4 ≤ Nat.card T := by
  obtain ⟨E, hET, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) T
  have h1 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 T := Nat.pow_le_pow_right (by norm_num) e.pRank_lt
  exact h1.trans (Subgroup.card_le_of_le hET)

theorem mem_A_of_conj_eq (e : Elem47 G T S Q H g y) {n : X} (hn : n ∈ S)
    (hMn : rightConjugate (T ⊔ rightConjugate T g) n = T ⊔ rightConjugate T g) :
    n ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  rw [← e.normalizer_M]
  exact ⟨hn, (rightConjugate_eq_self_iff _ n).mp hMn⟩

theorem conj_le_A (e : Elem47 G T S Q H g y) {c : X} (hc : c ∈ G)
    (hcN : rightConjugate T c ≤ S ⊓ Subgroup.normalizer
      ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g) : Subgroup X) : Set X)) :
    rightConjugate T c ≤ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  have h := e.hyp45
  set K := rightConjugate T c with hKdef
  have hKA : K ⊓ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) ≠ ⊥ := by
    intro hbot
    have hK4 : 4 ≤ Nat.card K := by rw [rightConjugate_card]; exact e.four_le_card
    obtain ⟨k₁, hk₁, k₂, hk₂, hk₁1, hk₂1, hk₂₁⟩ := exists_two_ne_one hK4
    have hnotA : ∀ k ∈ K, k ≠ 1 → k ∉ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
      intro k hk hk1 hkA
      have hmem : k ∈ K ⊓ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) := ⟨hk, hkA⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hk1 hmem
    have hVZ : ∀ k ∈ K, k ≠ 1 → rightConjugate (T ⊔ rightConjugate T g) k =
        rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G := by
      intro k hk hk1
      rcases e.conj_M_eq (hcN hk).2 with h1 | h1
      · exact absurd (e.mem_A_of_conj_eq (hcN hk).1 h1) (hnotA k hk hk1)
      · exact h1
    have hk : k₂ * k₁⁻¹ ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
      apply e.mem_A_of_conj_eq (S.mul_mem (hcN hk₂).1 (S.inv_mem (hcN hk₁).1))
      rw [← rightConjugate_mul, hVZ k₂ hk₂ hk₂1, ← hVZ k₁ hk₁ hk₁1, rightConjugate_mul,
        mul_inv_cancel, rightConjugate_one]
    exact hnotA _ (K.mul_mem hk₂ (K.inv_mem hk₁)) (fun h1 => hk₂₁ (mul_inv_eq_one.mp h1)) hk
  have hK2 : ∀ k ∈ K ⊓ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)), k ^ 2 = 1 := by
    intro k hk
    have hk' : c * k * c⁻¹ ∈ T := (mem_rightConjugate_iff T c k).mp hk.1
    rw [show k ^ 2 = c⁻¹ * (c * k * c⁻¹) ^ 2 * c by simp only [pow_two]; group, e.sq_T _ hk']
    group
  have hsub : ((K ⊓ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) : Subgroup X) : Set X) ⊆
      ((T ⊔ rightConjugate T g : Subgroup X) : Set X) ∪
        ((rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) :=
    fun k hk => e.sq_eq_one_mem hk.2 (hK2 k hk)
  have hKS : K ≤ S := hcN.trans inf_le_left
  have hNT : S ⊓ Subgroup.normalizer (T : Set X) = T ⊔ rightConjugate T g := by
    rw [← h.inf_eq_normalizer, e.inf_eq]
  rcases (SubgroupClass.subset_union).mp hsub with hle | hle
  · have hne : K ⊓ (T ⊔ rightConjugate T g) ≠ ⊥ := fun hbot =>
      hKA (le_bot_iff.mp ((le_inf inf_le_left hle).trans hbot.le))
    exact (le_of_inf_ne_bot h.sylowFrame h.hyp43 hc hKS e.M_le_S h.facts.2.2.2
      (by rw [hNT]) hne).trans le_sup_right
  · have hne : K ⊓ (rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G) ≠ ⊥ := fun hbot =>
      hKA (le_bot_iff.mp ((le_inf inf_le_left hle).trans hbot.le))
    have hVZS : rightConjugate T y ⊔ (T ⊔ rightConjugate T g) ⊓ G ≤ S :=
      sup_le e.le_S (inf_le_left.trans e.M_le_S)
    exact (le_of_inf_ne_bot h.sylowFrame h.hyp43 hc hKS hVZS e.VZ_comm
      (by rw [hNT, e.card_VZ, h.card_W]) hne).trans
      (sup_le le_sup_left (inf_le_left.trans le_sup_right))

theorem weakClosure_eq (e : Elem47 G T S Q H g y) :
    relativeWeakClosure G T S = rightConjugate T y ⊔ (T ⊔ rightConjugate T g) := by
  have h := e.hyp45
  apply le_antisymm
  · apply relativeWeakClosure_le_of_normalizer h.frame h.isPGroup_S h.le_sup e.A_le_S
    · apply le_antisymm (relative_weak_closure_le _ _ _)
      refine sup_le ?_ (sup_le ?_ ?_)
      · exact rightConjugate_le_relativeWeakClosure e.mem le_sup_left
      · exact subgroup_le_relative_weak_closure _ _ _ (le_sup_left.trans le_sup_right)
      · exact rightConjugate_le_relativeWeakClosure h.mem (le_sup_right.trans le_sup_right)
    · intro c hc hle
      exact e.conj_le_A hc hle
  · refine sup_le ?_ (sup_le ?_ ?_)
    · exact rightConjugate_le_relativeWeakClosure e.mem e.le_S
    · exact subgroup_le_relative_weak_closure _ _ _ h.le_S
    · exact rightConjugate_le_relativeWeakClosure h.mem (h.conj_le.trans inf_le_right)

theorem Z_comm (e : Elem47 G T S Q H g y) {w : X} (hw : w ∈ (T ⊔ rightConjugate T g) ⊓ G)
    {x : X} (hx : x ∈ rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) : w * x = x * w :=
  (Subgroup.mem_centralizer_iff.mp ((Subgroup.le_centralizer_iff.mp e.Z_centralizes_A) hw) x
    hx).symm

theorem center_eq (e : Elem47 G T S Q H g y) :
    centerOf (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) =
      (T ⊔ rightConjugate T g) ⊓ G := by
  have h := e.hyp45
  apply le_antisymm
  · rintro x ⟨hxA, hxC⟩
    have hxS : x ∈ S := e.A_le_S hxA
    have hxCM : x ∈ Subgroup.centralizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hxC
    have hxM : x ∈ T ⊔ rightConjugate T g := by
      rw [← e.inf_eq, h.inf_eq_centralizer_W]
      exact ⟨hxS, hxCM⟩
    obtain ⟨hdec, -⟩ := h.W_decomp
    have hTZ : T ≤ Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) :=
      (le_sup_left.trans (e.M_comm.trans (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr inf_le_left)))).trans (Subgroup.centralizer_le_normalizer _)
    have hxmem : x ∈ (T : Set X) * (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTZ, ← hdec]
      exact hxM
    obtain ⟨t, ht, z, hz, rfl⟩ := Set.mem_mul.mp hxmem
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp e.V_ne_bot
    have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    have hxv : v * (t * z) = (t * z) * v :=
      Subgroup.mem_centralizer_iff.mp hxC v (Subgroup.mem_sup_left hv)
    have hzv : v * z = z * v := e.V_centralizes_Z hv hz
    have htv : v * t = t * v := by
      have h1 : v * t * z = t * v * z := by
        calc v * t * z = v * (t * z) := by group
          _ = (t * z) * v := hxv
          _ = t * (z * v) := by group
          _ = t * (v * z) := by rw [hzv]
          _ = t * v * z := by group
      exact mul_right_cancel h1
    have hvt : v⁻¹ * t * v = t := by
      calc v⁻¹ * t * v = v⁻¹ * (t * v) := by group
        _ = v⁻¹ * (v * t) := by rw [htv]
        _ = t := by group
    have ht1 : t = 1 := (e.comm_map hv hv1').2.1 t ht 1 T.one_mem (by rw [hvt]; group)
    rw [ht1, one_mul]
    exact hz
  · exact le_inf (inf_le_left.trans le_sup_right)
      (Subgroup.le_centralizer_iff.mp e.Z_centralizes_A)

theorem commutator_eq (e : Elem47 G T S Q H g y) :
    ⁅rightConjugate T y ⊔ (T ⊔ rightConjugate T g),
      rightConjugate T y ⊔ (T ⊔ rightConjugate T g)⁆ = (T ⊔ rightConjugate T g) ⊓ G := by
  set A := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hAdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  have hZA : Z ≤ A := inf_le_left.trans le_sup_right
  have hTA : T ≤ A := le_sup_left.trans le_sup_right
  have hVA : rightConjugate T y ≤ A := le_sup_left
  have hVcomm : IsMulCommutative (rightConjugate T y) := isMulCommutative_rightConjugate e.elem.1 y
  have hTcomm := e.elem.1
  rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hVcomm hTcomm
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨v₁, hv₁, t₁, ht₁, z₁, hz₁, rfl⟩ := e.mem_A ha
    obtain ⟨v₂, hv₂, t₂, ht₂, z₂, hz₂, rfl⟩ := e.mem_A hb
    set c₁ := t₁⁻¹ * (v₂⁻¹ * t₁ * v₂) with hc₁def
    set c₂ := t₂⁻¹ * (v₁⁻¹ * t₂ * v₁) with hc₂def
    have hc₁ : c₁ ∈ Z := e.comm_mem_Z hv₂ ht₁
    have hc₂ : c₂ ∈ Z := e.comm_mem_Z hv₁ ht₂
    have e₁ : t₁ * v₂ = v₂ * t₁ * c₁ := by rw [hc₁def]; group
    have e₂ : t₂ * v₁ = v₁ * t₂ * c₂ := by rw [hc₂def]; group
    have hvv : v₂ * v₁ = v₁ * v₂ := Subgroup.mem_centralizer_iff.mp (hVcomm hv₁) v₂ hv₂
    have htt : t₂ * t₁ = t₁ * t₂ := Subgroup.mem_centralizer_iff.mp (hTcomm ht₁) t₂ ht₂
    set a := v₁ * t₁ with hadef
    set b := v₂ * t₂ with hbdef
    have haA : a ∈ A := A.mul_mem (hVA hv₁) (hTA ht₁)
    have hbA : b ∈ A := A.mul_mem (hVA hv₂) (hTA ht₂)
    have hab : a * b = b * a * (c₂⁻¹ * c₁) := by
      have h1 : a * b = v₁ * v₂ * (t₁ * t₂) * c₁ := by
        calc a * b = v₁ * (t₁ * v₂) * t₂ := by rw [hadef, hbdef]; group
          _ = v₁ * (v₂ * t₁ * c₁) * t₂ := by rw [e₁]
          _ = v₁ * v₂ * t₁ * (c₁ * t₂) := by group
          _ = v₁ * v₂ * t₁ * (t₂ * c₁) := by rw [e.Z_comm hc₁ (hTA ht₂)]
          _ = v₁ * v₂ * (t₁ * t₂) * c₁ := by group
      have h2 : b * a = v₁ * v₂ * (t₁ * t₂) * c₂ := by
        calc b * a = v₂ * (t₂ * v₁) * t₁ := by rw [hadef, hbdef]; group
          _ = v₂ * (v₁ * t₂ * c₂) * t₁ := by rw [e₂]
          _ = v₂ * v₁ * t₂ * (c₂ * t₁) := by group
          _ = v₂ * v₁ * t₂ * (t₁ * c₂) := by rw [e.Z_comm hc₂ (hTA ht₁)]
          _ = (v₂ * v₁) * (t₂ * t₁) * c₂ := by group
          _ = v₁ * v₂ * (t₁ * t₂) * c₂ := by rw [hvv, htt]
      rw [h1, h2]
      group
    have hXZ : c₂⁻¹ * c₁ ∈ Z := Z.mul_mem (Z.inv_mem hc₂) hc₁
    have hcomm_ab : ⁅a, b⁆ = c₂⁻¹ * c₁ := by
      rw [commutatorElement_def, hab]
      have hX : (c₂⁻¹ * c₁) * (b * a) = (b * a) * (c₂⁻¹ * c₁) :=
        e.Z_comm hXZ (A.mul_mem hbA haA)
      calc b * a * (c₂⁻¹ * c₁) * a⁻¹ * b⁻¹ = (b * a * (c₂⁻¹ * c₁)) * (b * a)⁻¹ := by group
        _ = ((c₂⁻¹ * c₁) * (b * a)) * (b * a)⁻¹ := by rw [hX]
        _ = c₂⁻¹ * c₁ := by group
    have hz_remove : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have hz₁b : z₁ * b = b * z₁ := e.Z_comm hz₁ hbA
      have hz₂a : z₂ * a⁻¹ = a⁻¹ * z₂ := e.Z_comm hz₂ (A.inv_mem haA)
      have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := e.Z_comm hz₁ (hZA hz₂)
      calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ =
            a * (z₁ * b) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
        _ = a * (b * z₁) * z₂ * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [hz₁b]
        _ = a * b * (z₁ * z₂) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
        _ = a * b * (z₂ * z₁) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [hz₁z₂]
        _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * z₂) * z₂⁻¹ * b⁻¹ := by rw [hz₂a]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rw [hz_remove, hcomm_ab]
    exact hXZ
  · intro z hz
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp e.V_ne_bot
    have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    obtain ⟨t, ht, rfl⟩ := (e.comm_map hv hv1').2.2.1 z hz
    have hc : t⁻¹ * (v⁻¹ * t * v) = ⁅t⁻¹, v⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [hc]
    exact Subgroup.commutator_mem_commutator (A.inv_mem (hTA ht)) (A.inv_mem (hVA hv))

theorem frattini_eq (e : Elem47 G T S Q H g y) :
    frattiniOf (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)) =
      (T ⊔ rightConjugate T g) ⊓ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hAdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  have hZA : Z ≤ A := inf_le_left.trans le_sup_right
  have hA2 : IsPGroup 2 A := e.hyp45.isPGroup_S.to_le e.A_le_S
  have hNc : Z.subgroupOf A ≤ Subgroup.center A := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (e.Z_comm hz x.2).symm
  have : (Z.subgroupOf A).Normal := Subgroup.normal_of_le_center hNc
  have hsq : ∀ a ∈ A, a ^ 2 ∈ Z := by
    intro a ha
    obtain ⟨v, hv, t, ht, z, hz, rfl⟩ := e.mem_A ha
    rw [e.sq_vtz hv ht hz]
    exact e.comm_mem_Z hv ht
  have hle : frattini A ≤ Z.subgroupOf A := by
    refine CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 2) _ (fun a b => ?_)
      (fun a => ?_)
    · have hc := Subgroup.commutator_mem_commutator a.2 b.2
      rw [e.commutator_eq] at hc
      exact hc
    · exact hsq a a.2
  have hge : Z.subgroupOf A ≤ frattini A := by
    intro z hz
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp e.V_ne_bot
    have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    obtain ⟨t, ht, hzt⟩ := (e.comm_map hv hv1').2.2.1 (z : X) hz
    have hvtA : v * t ∈ A := A.mul_mem (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right (Subgroup.mem_sup_left ht))
    have hzeq : z = (⟨v * t, hvtA⟩ : A) ^ 2 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hzt]
      have := e.sq_vtz hv ht Z.one_mem
      rw [mul_one] at this
      exact this.symm
    rw [hzeq]
    exact CFSG.SectionRank.Ccomm.pow_mem_frattini hA2 _
  unfold frattiniOf
  rw [le_antisymm hle hge, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZA]

omit [Finite X] in
theorem le_normalizer_of_commutator_le {A B : Subgroup X} (hBA : B ≤ A) (hAB : ⁅A, A⁆ ≤ B) :
    A ≤ Subgroup.normalizer (B : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hc : ⁅a, x⁆ ∈ B := hAB (Subgroup.commutator_mem_commutator ha (hBA hx))
    have heq : a * x * a⁻¹ = ⁅a, x⁆ * x := by rw [commutatorElement_def]; group
    rw [heq]
    exact B.mul_mem hc hx
  · intro hx
    have hc : ⁅a⁻¹, a * x * a⁻¹⁆ ∈ B :=
      hAB (Subgroup.commutator_mem_commutator (A.inv_mem ha) (hBA hx))
    have heq : x = ⁅a⁻¹, a * x * a⁻¹⁆ * (a * x * a⁻¹) := by rw [commutatorElement_def]; group
    rw [heq]
    exact B.mul_mem hc hx

theorem index_eq (e : Elem47 G T S Q H g y) :
    (rightConjugate T y ⊔ (T ⊔ rightConjugate T g)).relIndex S = 2 := by
  have h := e.hyp45
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := rightConjugate T y ⊔ (T ⊔ rightConjugate T g) with hAdef
  set M := T ⊔ rightConjugate T g with hMdef
  set Z := (T ⊔ rightConjugate T g) ⊓ G with hZdef
  set VZ := rightConjugate T y ⊔ Z with hVZdef
  have hW := e.weakClosure_eq
  have hSN : S ≤ Subgroup.normalizer (A : Set X) := by
    have h1 := le_normalizer_relativeWeakClosure h.frame h.le_sup h.le_S
    rwa [hW] at h1
  have hAS : A ≤ S := e.A_le_S
  have hcoset : ∀ L : Subgroup X, L ≤ Subgroup.normalizer (A : Set X) →
      ∀ x ∈ L, ∀ x' ∈ L, x ∉ L ⊓ Subgroup.normalizer (M : Set X) →
        x' ∉ L ⊓ Subgroup.normalizer (M : Set X) →
          x * x'⁻¹ ∈ L ⊓ Subgroup.normalizer (M : Set X) := by
    intro L hL x hx x' hx' hxM hx'M
    have hVx : rightConjugate M x = VZ := by
      rcases e.conj_M_eq (hL hx) with h1 | h1
      · exact absurd ⟨hx, (rightConjugate_eq_self_iff M x).mp h1⟩ hxM
      · exact h1
    have hVx' : rightConjugate M x' = VZ := by
      rcases e.conj_M_eq (hL hx') with h1 | h1
      · exact absurd ⟨hx', (rightConjugate_eq_self_iff M x').mp h1⟩ hx'M
      · exact h1
    refine ⟨L.mul_mem hx (L.inv_mem hx'), (rightConjugate_eq_self_iff M _).mp ?_⟩
    rw [← rightConjugate_mul, hVx, ← hVx', rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hSM : S ⊓ Subgroup.normalizer (M : Set X) = A := e.normalizer_M
  have hle : A.relIndex S ≤ 2 := by
    have h2 := relIndex_le_two (K := S ⊓ Subgroup.normalizer (M : Set X)) (L := S) inf_le_left
      (fun x hx x' hx' hxM hx'M => hcoset S hSN x hx x' hx' hxM hx'M)
    rwa [hSM] at h2
  have hne : A.relIndex S ≠ 1 := by
    intro h1
    have hSA : S ≤ A := Subgroup.relIndex_eq_one.mp h1
    have hSeq : S = A := le_antisymm hSA hAS
    have hcommA := e.commutator_eq
    have hMS : S ≤ Subgroup.normalizer (M : Set X) := hSeq ▸
      le_normalizer_of_commutator_le le_sup_right (hcommA.le.trans inf_le_left)
    have hVZA : VZ ≤ A := sup_le le_sup_left (inf_le_left.trans le_sup_right)
    have hVZS : S ≤ Subgroup.normalizer (VZ : Set X) := hSeq ▸
      le_normalizer_of_commutator_le hVZA (hcommA.le.trans le_sup_right)
    have hNT : S ⊓ Subgroup.normalizer (T : Set X) = M := by rw [← h.inf_eq_normalizer, e.inf_eq]
    have hyGT : y ∈ G ⊔ T := Subgroup.mem_sup_left e.mem
    have hL : rightConjugate ((G ⊔ T) ⊓ Subgroup.normalizer (T : Set X)) y =
        (G ⊔ T) ⊓ Subgroup.normalizer (rightConjugate T y : Set X) := by
      rw [rightConjugate_inf, rightConjugate_normalizer, rightConjugate_eq_of_mem hyGT]
    have hsyly := isSylowOf_rightConjugate h.sylowFrame.sylow_normalizer y
    rw [hL, hNT] at hsyly
    have hVZsyl : IsSylowOf 2 VZ ((G ⊔ T) ⊓ Subgroup.normalizer (rightConjugate T y : Set X)) := by
      apply isSylowOf_of_card
      · refine le_inf ((hVZA.trans hAS).trans h.le_sup) ?_
        have hc := e.VZ_comm
        rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hc
        exact hc.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)).trans
          (Subgroup.centralizer_le_normalizer _))
      · rw [← hsyly.card_eq, rightConjugate_card, e.card_VZ, h.card_W]
    obtain ⟨c, hc, hcVZ⟩ := exists_rightConjugate_eq_of_isSylowOf hVZsyl hsyly
    set d := y * c with hddef
    have hdGT : d ∈ G ⊔ T := (G ⊔ T).mul_mem hyGT hc.1
    have hMd : rightConjugate M d = VZ := by rw [hddef, ← rightConjugate_mul, hcVZ]
    have hSL : S ≤ (G ⊔ T) ⊓ Subgroup.normalizer (VZ : Set X) := le_inf h.le_sup hVZS
    have hSdL : rightConjugate S d ≤ (G ⊔ T) ⊓ Subgroup.normalizer (VZ : Set X) := by
      refine le_inf (rightConjugate_le_of_mem h.le_sup hdGT) ?_
      rw [← hMd, ← rightConjugate_normalizer]
      exact rightConjugate_le_rightConjugate hMS d
    have hSsyl : IsSylowOf 2 S ((G ⊔ T) ⊓ Subgroup.normalizer (VZ : Set X)) :=
      h.sylowFrame.sylow.of_le hSL inf_le_left
    have hSdsyl : IsSylowOf 2 (rightConjugate S d)
        ((G ⊔ T) ⊓ Subgroup.normalizer (VZ : Set X)) := by
      have hs := isSylowOf_rightConjugate h.sylowFrame.sylow d
      rw [rightConjugate_eq_of_mem hdGT] at hs
      exact hs.of_le hSdL inf_le_left
    obtain ⟨c', hc', hc'S⟩ := exists_rightConjugate_eq_of_isSylowOf hSsyl hSdsyl
    set n := d * c' with hndef
    have hnGT : n ∈ G ⊔ T := (G ⊔ T).mul_mem hdGT hc'.1
    have hnS : rightConjugate S n = S := by rw [hndef, ← rightConjugate_mul, hc'S]
    have hMn : rightConjugate M n = VZ := by
      rw [hndef, ← rightConjugate_mul, hMd]
      exact (rightConjugate_eq_self_iff _ c').mpr hc'.2
    set L' := (G ⊔ T) ⊓ Subgroup.normalizer (S : Set X) with hL'def
    have hL'A : L' ≤ Subgroup.normalizer (A : Set X) := by
      rw [← hSeq]
      exact inf_le_right
    have hnL' : n ∈ L' := ⟨hnGT, (rightConjugate_eq_self_iff S n).mp hnS⟩
    have hnK : n ∉ L' ⊓ Subgroup.normalizer (M : Set X) := by
      intro hn
      have := (rightConjugate_eq_self_iff M n).mpr hn.2
      rw [hMn] at this
      exact e.VZ_ne_M this
    have hidx2 : (L' ⊓ Subgroup.normalizer (M : Set X)).relIndex L' = 2 := by
      have hle2 := relIndex_le_two (K := L' ⊓ Subgroup.normalizer (M : Set X)) (L := L')
        inf_le_left (fun x hx x' hx' hxM hx'M => hcoset L' hL'A x hx x' hx' hxM hx'M)
      have hne1 : (L' ⊓ Subgroup.normalizer (M : Set X)).relIndex L' ≠ 1 := by
        intro h1
        exact hnK (Subgroup.relIndex_eq_one.mp h1 hnL')
      have hne0 : (L' ⊓ Subgroup.normalizer (M : Set X)).relIndex L' ≠ 0 :=
        relIndex_ne_zero_of_finite _ _
      omega
    have hSK : S ≤ L' ⊓ Subgroup.normalizer (M : Set X) :=
      le_inf (le_inf h.le_sup Subgroup.le_normalizer) hMS
    have hSL'syl : IsSylowOf 2 S L' := h.sylowFrame.sylow.of_le (hSK.trans inf_le_left) inf_le_left
    obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.mp hSL'syl
    apply hdvd
    rw [← Subgroup.relIndex_mul_relIndex S _ L' hSK inf_le_left, hidx2]
    exact dvd_mul_left 2 _
  have hne0 : A.relIndex S ≠ 0 := relIndex_ne_zero_of_finite _ _
  omega

theorem conclusion (e : Elem47 G T S Q H g y) :
    IsElemAbelian 2 T ∧ Nat.card (relativeWeakClosure G T S) = Nat.card T ^ 3 ∧
      centerOf (relativeWeakClosure G T S) =
        ⁅relativeWeakClosure G T S, relativeWeakClosure G T S⁆ ∧
      centerOf (relativeWeakClosure G T S) = frattiniOf (relativeWeakClosure G T S) ∧
      (relativeWeakClosure G T S).relIndex S = 2 := by
  rw [e.weakClosure_eq]
  exact ⟨e.elem, e.card_A, by rw [e.center_eq, e.commutator_eq],
    by rw [e.center_eq, e.frattini_eq], e.index_eq⟩

end Elem47

end CFSG.ComponentClassification.AschbacherTheorem3
