module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInvol
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDQ

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKP

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_conjugate {H : Subgroup X} {g x : X} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

omit [Finite X] in
theorem conjugate_eq_self {H : Subgroup X} {g : X} (h : H ≤ centralizer ({g} : Set X)) :
    conjugate H g = H := by
  ext x
  rw [mem_conjugate]
  constructor
  · intro hx
    have hc := mem_centralizer_singleton_iff.mp (h hx)
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hx
  · intro hx
    have hc := mem_centralizer_singleton_iff.mp (h hx)
    rw [← hc, mul_inv_cancel_right]
    exact hx

omit [Finite X] in
theorem conjugate_conjugate {H : Subgroup X} {a : X} (ha : a * a = 1) :
    conjugate (conjugate H a) a = H := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  ext x
  rw [mem_conjugate, mem_conjugate]
  have e : a * (a * x * a⁻¹) * a⁻¹ = x := by
    rw [hinv]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha, one_mul, mul_one]
  rw [e]

omit [Finite X] in
theorem isComponent_conjugate {C J : Subgroup X} (hJ : IsComponent (J.subgroupOf C)) {g : X}
    (hg : g ∈ C) : IsComponent ((conjugate J g).subgroupOf C) := by
  have h := LocalCores.isComponent_map_mulEquiv (MulAut.conj (⟨g, hg⟩ : ↥C)⁻¹) hJ
  convert h using 1
  ext x
  rw [mem_subgroupOf, mem_conjugate, mem_map]
  constructor
  · intro hx
    refine ⟨⟨g, hg⟩ * x * (⟨g, hg⟩ : ↥C)⁻¹, ?_, ?_⟩
    · rw [mem_subgroupOf]
      simpa using hx
    · simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_subgroupOf] at hy
    simpa [mul_assoc] using hy

theorem commute_of_components {C J K : Subgroup X} (hJC : J ≤ C) (hKC : K ≤ C)
    (hJ : IsComponent (J.subgroupOf C)) (hK : IsComponent (K.subgroupOf C)) (hne : J ≠ K) :
    ∀ x ∈ J, ∀ y ∈ K, x * y = y * x := by
  rcases LocalCores.distinct_components_commute hJ hK with h | h
  · exfalso
    apply hne
    have h' := subgroupOf_inj.mp h
    rwa [inf_of_le_left hJC, inf_of_le_left hKC] at h'
  · intro x hx y hy
    have hm := commutator_mem_commutator (show (⟨x, hJC hx⟩ : ↥C) ∈ J.subgroupOf C from hx)
      (show (⟨y, hKC hy⟩ : ↥C) ∈ K.subgroupOf C from hy)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact congrArg Subtype.val hm

omit [Finite X] in
theorem commutator_mul_eq {z₁ z₂ c₁ c₂ : X} (hz : z₁ * z₂ = z₂ * z₁)
    (h11 : z₁ * c₁ = c₁ * z₁) (h12 : z₁ * c₂ = c₂ * z₁) (h21 : z₂ * c₁ = c₁ * z₂)
    (h22 : z₂ * c₂ = c₂ * z₂) :
    z₁ * c₁ * (z₂ * c₂) * (z₁ * c₁)⁻¹ * (z₂ * c₂)⁻¹ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by
  have e1 : z₁ * c₁ * (z₂ * c₂) = z₁ * z₂ * (c₁ * c₂) := by
    calc z₁ * c₁ * (z₂ * c₂) = z₁ * (c₁ * z₂) * c₂ := by group
      _ = z₁ * (z₂ * c₁) * c₂ := by rw [h21]
      _ = z₁ * z₂ * (c₁ * c₂) := by group
  have e2 : z₂ * c₂ * (z₁ * c₁) = z₁ * z₂ * (c₂ * c₁) := by
    calc z₂ * c₂ * (z₁ * c₁) = z₂ * (c₂ * z₁) * c₁ := by group
      _ = z₂ * (z₁ * c₂) * c₁ := by rw [h12]
      _ = z₂ * z₁ * (c₂ * c₁) := by group
      _ = z₁ * z₂ * (c₂ * c₁) := by rw [hz]
  have hZ1 : Commute (z₁ * z₂) c₁ := Commute.mul_left h11 h21
  have hZ2 : Commute (z₁ * z₂) c₂ := Commute.mul_left h12 h22
  have hw : Commute (z₁ * z₂) (c₁ * c₂ * (c₂ * c₁)⁻¹) :=
    (hZ1.mul_right hZ2).mul_right (hZ2.mul_right hZ1).inv_right
  calc z₁ * c₁ * (z₂ * c₂) * (z₁ * c₁)⁻¹ * (z₂ * c₂)⁻¹
      = z₁ * c₁ * (z₂ * c₂) * (z₂ * c₂ * (z₁ * c₁))⁻¹ := by group
    _ = z₁ * z₂ * (c₁ * c₂) * (z₁ * z₂ * (c₂ * c₁))⁻¹ := by rw [e1, e2]
    _ = z₁ * z₂ * (c₁ * c₂ * (c₂ * c₁)⁻¹) * (z₁ * z₂)⁻¹ := by group
    _ = c₁ * c₂ * (c₂ * c₁)⁻¹ * (z₁ * z₂) * (z₁ * z₂)⁻¹ := by rw [hw.eq]
    _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by group

theorem false_of_hom
    {L : Subgroup X} (hset : HeldEndSetting X L) {a : X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) {u : X} (hu : HeldTwoA L u) {J : Subgroup X}
    (hJq : IsQuasisimple ↥J) (f : ↥J →* X) (hfa : ∀ j, f j ∈ centralizer ({a} : Set X))
    (hfK : ∀ j, ∀ k ∈ gsFixedLayer L u, f j * k = k * f j)
    (hker : ∀ j, f j = 1 → j ∈ center ↥J) {w₁ w₂ : ↥J} (h₁ : w₁ * w₁ = 1) (h₂ : w₂ * w₂ = 1)
    (hc : w₁ * w₂ = w₂ * w₁) (hn₁ : w₁ ∉ center ↥J) (hn₂ : w₂ ∉ center ↥J)
    (hn₃ : w₁ * w₂ ∉ center ↥J) : False := by
  obtain ⟨-, -, hstd, ⟨e⟩, hrank⟩ := hset
  set K := gsFixedLayer L u with hK
  set CL := centralizer (L : Set X) with hCL
  set Zk := (center ↥K).map K.subtype with hZk
  have hKL : K ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hZK : Zk ≤ K := map_subtype_le _
  have haL : a ∈ CL :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLa hl)
  have hCN := HeZ.centralizer_le_normalizer hstd haL ha
  have hcard : Nat.card K = 80640 :=
    HeZ.card_gsFixedLayer heldTwoALayerFact heldTwoAKFact ⟨e⟩ hu
  obtain ⟨-, -, hAK⟩ := heldTwoAKFact X L ⟨e⟩ u hu
  have hinv : ∀ j : ↥J, j * j = 1 → f j ∈ Zk ⊔ CL := by
    intro j hj
    have hfj2 : f j * f j = 1 := by rw [← map_mul, hj, map_one]
    by_cases hjC : f j ∈ CL
    · exact mem_sup_right hjC
    rcases heldInvolAutFact X L ⟨e⟩ (f j) (hCN (hfa j)) (by rw [hfj2]; exact one_mem _) hjC with
      ⟨y, hyL, -, hyc⟩ | ⟨-, -, hS, -⟩
    · have hyK : ∀ k ∈ K, y * k = k * y := by
        intro k hk
        have hck : Commute k (y⁻¹ * f j) := mem_centralizer_iff.mp hyc k (hKL hk)
        have hfk : Commute k (f j) := (hfK j k hk).symm
        have hy : y = f j * (y⁻¹ * f j)⁻¹ := by group
        have h' : Commute k y := by
          rw [hy]
          exact hfk.mul_right hck.inv_right
        exact h'.eq.symm
      have hyZ : y ∈ Zk := by
        rcases hAK y hyL hyK with rfl | ⟨-, h⟩
        · exact one_mem _
        · exact h
      have h := mul_mem (mem_sup_left hyZ : y ∈ Zk ⊔ CL) (mem_sup_right hyc)
      rwa [mul_inv_cancel_left] at h
    · have h := hS K hKL fun k hk => mem_centralizer_singleton_iff.mpr (hfK j k hk).symm
      omega
  set S : Set ↥J := {j | j * j = 1} with hSdef
  have hNC : normalClosure S ≤ (Zk ⊔ CL).comap f := by
    show closure (Group.conjugatesOfSet S) ≤ _
    rw [closure_le]
    intro x hx
    obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hbx
    apply hinv
    have hb' : b * b = 1 := hb
    calc c * b * c⁻¹ * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
      _ = 1 := by rw [hb']; group
  have htop : normalClosure S = ⊤ := by
    rcases LocalCores.quasisimple_normal_subgroups hJq (normalClosure_normal (s := S)) with h | h
    · exact h
    · exact absurd (h (subset_normalClosure h₁)) hn₁
  have hall : f.range ≤ Zk ⊔ CL := by
    rintro _ ⟨j, rfl⟩
    exact hNC (htop ▸ mem_top j)
  have hZC : ∀ z ∈ Zk, ∀ c ∈ CL, z * c = c * z := fun z hz c hc =>
    mem_centralizer_iff.mp hc z (hKL (hZK hz))
  have hZZ : ∀ z₁ ∈ Zk, ∀ z₂ ∈ Zk, z₁ * z₂ = z₂ * z₁ := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, -, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hy₁ y₂).symm
  have hcomm : ⁅Zk ⊔ CL, Zk ⊔ CL⁆ ≤ CL := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨z₁, hz₁, c₁, hc₁, rfl⟩ := HeDQ.exists_mul_of_mem_sup hZC hg₁
    obtain ⟨z₂, hz₂, c₂, hc₂, rfl⟩ := HeDQ.exists_mul_of_mem_sup hZC hg₂
    rw [commutatorElement_def, commutator_mul_eq (hZZ z₁ hz₁ z₂ hz₂) (hZC z₁ hz₁ c₁ hc₁)
      (hZC z₁ hz₁ c₂ hc₂) (hZC z₂ hz₂ c₁ hc₁) (hZC z₂ hz₂ c₂ hc₂)]
    exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
  have hperf : ⁅f.range, f.range⁆ = f.range := by
    have hJp : ⁅(⊤ : Subgroup ↥J), ⊤⁆ = ⊤ := hJq.1.commutator_eq_top
    rw [MonoidHom.range_eq_map, ← map_commutator, hJp]
  have hrange : f.range ≤ CL := hperf ▸ (commutator_mono hall hall).trans hcomm
  have hf₁ : f w₁ ∈ CL := hrange ⟨w₁, rfl⟩
  have hf₂ : f w₂ ∈ CL := hrange ⟨w₂, rfl⟩
  refine HeZ.false_of_pair hrank hf₁ hf₂ (by rw [← map_mul, h₁, map_one])
    (by rw [← map_mul, h₂, map_one]) (fun h => hn₁ (hker _ h)) (fun h => hn₂ (hker _ h))
    (fun h => hn₃ (hker _ ?_)) (by rw [← map_mul, hc, map_mul])
  rw [map_mul, h, ← map_mul, h₂, map_one]

end HeKP

end CFSG.ComponentClassification.GrSLit
