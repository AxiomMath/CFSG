module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

variable {X : Type} [Group X]

theorem component_le_or_commute {K M : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKM : K ≤ Subgroup.normalizer (M : Set X)) (hMK : M ≤ Subgroup.normalizer (K : Set X)) :
    K ≤ M ∨ ∀ x ∈ K, ∀ y ∈ M, x * y = y * x := by
  set N : Subgroup K := M.subgroupOf K with hNdef
  have hN : N.Normal := ⟨fun n hn k => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hKM k.2) n).mp hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK.2.2 N with
    hc | ht
  · right
    have hMKle : ⁅M, K⁆ ≤ M ⊓ K := by
      rw [Subgroup.commutator_le]
      intro m hm k hk
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have h1 : k * m⁻¹ * k⁻¹ ∈ M :=
          (Subgroup.mem_normalizer_iff.mp (hKM hk) m⁻¹).mp (M.inv_mem hm)
        have e : m * k * m⁻¹ * k⁻¹ = m * (k * m⁻¹ * k⁻¹) := by group
        rw [e]
        exact M.mul_mem hm h1
      · have h1 : m * k * m⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hMK hm) k).mp hk
        exact K.mul_mem h1 (K.inv_mem hk)
    have hC : ⁅⁅M, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      obtain ⟨hxM, hxK⟩ := hMKle hx
      have hxN : (⟨x, hxK⟩ : K) ∈ N := Subgroup.mem_subgroupOf.mpr hxM
      have h1 := Subgroup.mem_center_iff.mp (hc hxN) ⟨k, hk⟩
      exact congrArg Subtype.val h1
    have h3 : ⁅⁅K, K⁆, M⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate
      (by rw [Subgroup.commutator_comm K M]; exact hC) hC
    have hKK : ⁅K, K⁆ = K := by
      rw [← Subgroup.map_subtype_commutator, hK.2.2.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [hKK, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (h3 hx) y hy).symm
  · left
    intro x hx
    have h1 : (⟨x, hx⟩ : K) ∈ N := ht ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp h1

theorem comm_of_comm_mem {K M : Subgroup X} (hK : IsComponentOf K ⊤)
    (hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hKM : ∀ x ∈ K, ∀ y ∈ M, x * y = y * x) {t : X}
    (ht : ∀ k ∈ K, k⁻¹ * t⁻¹ * k * t ∈ M) : ∀ k ∈ K, k * t = t * k := by
  let f : K →* M :=
    { toFun := fun k => ⟨(k : X)⁻¹ * t⁻¹ * k * t, ht k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k k' => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hc := hKM _ (K.inv_mem k'.2) _ (ht k k.2)
        calc ((k : X) * k')⁻¹ * t⁻¹ * (k * k') * t
            = (k' : X)⁻¹ * ((k : X)⁻¹ * t⁻¹ * k * t) * (t⁻¹ * k' * t) := by group
          _ = ((k : X)⁻¹ * t⁻¹ * k * t) * (k' : X)⁻¹ * (t⁻¹ * k' * t) := by rw [hc]
          _ = (k : X)⁻¹ * t⁻¹ * k * t * ((k' : X)⁻¹ * t⁻¹ * k' * t) := by group }
  have hker : commutator K ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
    apply Subtype.ext
    have hab := hMab _ (f a).2 _ (f b).2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hab]
    group
  rw [hK.2.2.1, top_le_iff] at hker
  intro k hk
  have h1 : f ⟨k, hk⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_top _
  have h2 : k⁻¹ * t⁻¹ * k * t = 1 := congrArg Subtype.val h1
  have h3 : t⁻¹ * k * t = k := by
    calc t⁻¹ * k * t = k * (k⁻¹ * t⁻¹ * k * t) := by group
      _ = k := by rw [h2, mul_one]
  calc k * t = t * (t⁻¹ * k * t) := by group
    _ = t * k := by rw [h3]

theorem comm_of_comm_mem_simple {K B : Subgroup X}
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → z = 1) (hKB : ∀ x ∈ K, ∀ y ∈ B, x * y = y * x)
    {t : X} (htB : t ∈ Subgroup.normalizer (B : Set X)) (ht : ∀ k ∈ K, k⁻¹ * t⁻¹ * k * t ∈ B) :
    ∀ k ∈ K, k * t = t * k := by
  intro k hk
  have h1 : k⁻¹ * t⁻¹ * k * t = 1 := by
    refine hZ _ (ht k hk) fun b hb => ?_
    have htb : t * b * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp htB b).mp hb
    have hkb := hKB k hk _ htb
    have hkb' := hKB k hk b hb
    calc k⁻¹ * t⁻¹ * k * t * b = k⁻¹ * (t⁻¹ * (k * (t * b * t⁻¹)) * t) := by group
      _ = k⁻¹ * (t⁻¹ * ((t * b * t⁻¹) * k) * t) := by rw [hkb]
      _ = (k⁻¹ * b) * (t⁻¹ * k * t) := by group
      _ = (b * k⁻¹) * (t⁻¹ * k * t) := by
          rw [show k⁻¹ * b = b * k⁻¹ from by
            calc k⁻¹ * b = k⁻¹ * (b * k) * k⁻¹ := by group
              _ = k⁻¹ * (k * b) * k⁻¹ := by rw [hkb']
              _ = b * k⁻¹ := by group]
      _ = b * (k⁻¹ * t⁻¹ * k * t) := by group
  have h3 : t⁻¹ * k * t = k := by
    calc t⁻¹ * k * t = k * (k⁻¹ * t⁻¹ * k * t) := by group
      _ = k := by rw [h1, mul_one]
  calc k * t = t * (t⁻¹ * k * t) := by group
    _ = t * k := by rw [h3]

theorem isSylowOf_sup_of_commute [Finite X] {B C P Q : Subgroup X} (hP : IsSylowOf 2 P B)
    (hQ : IsSylowOf 2 Q C) (hBC : B ⊓ C = ⊥) (hcomm : ∀ x ∈ B, ∀ y ∈ C, x * y = y * x) :
    IsSylowOf 2 (P ⊔ Q) (B ⊔ C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCB : C ≤ Subgroup.normalizer (B : Set X) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hcomm x hx y hy)
  have hQP : Q ≤ Subgroup.normalizer (P : Set X) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hcomm x (hP.le hx) y (hQ.le hy))
  have hPQ : P ⊓ Q = ⊥ := le_bot_iff.mp ((inf_le_inf hP.le hQ.le).trans hBC.le)
  have hle : P ⊔ Q ≤ B ⊔ C := sup_le_sup hP.le hQ.le
  rw [isSylowOf_iff] at hP hQ ⊢
  obtain ⟨hPB, hP2, hPidx⟩ := hP
  obtain ⟨hQC, hQ2, hQidx⟩ := hQ
  refine ⟨hle, IsPGroup.to_sup_of_normal_left' hP2 hQ2 hQP, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (P ⊔ Q) (B ⊔ C)
  rw [inf_eq_left.mpr hle, AschbacherTheorem3.card_sup_of_le_normalizer hQP hPQ,
    AschbacherTheorem3.card_sup_of_le_normalizer hCB hBC] at h1
  have h2 := Subgroup.relIndex_mul_card P B
  rw [inf_eq_left.mpr hPB] at h2
  have h3 := Subgroup.relIndex_mul_card Q C
  rw [inf_eq_left.mpr hQC] at h3
  have h4 : (P ⊔ Q).relIndex (B ⊔ C) = P.relIndex B * Q.relIndex C := by
    have hpos : 0 < Nat.card P * Nat.card Q := Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (P ⊔ Q).relIndex (B ⊔ C) * (Nat.card P * Nat.card Q) = Nat.card B * Nat.card C := h1
      _ = P.relIndex B * Nat.card P * (Q.relIndex C * Nat.card Q) := by rw [h2, h3]
      _ = P.relIndex B * Q.relIndex C * (Nat.card P * Nat.card Q) := by ring
  rw [h4]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
  · exact hPidx h
  · exact hQidx h

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
