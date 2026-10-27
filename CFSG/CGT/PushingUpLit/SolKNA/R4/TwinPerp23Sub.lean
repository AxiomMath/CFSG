module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscBSCModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic

namespace Perp23

section Sub

variable {Y : Type} [Group Y] [Finite Y]

theorem mk_eq_one_iff {C : Subgroup Y} {x : Y} (hx : x ∈ C) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨x, hx⟩ = 1 ↔ x ∈ oddCoreIn C := by
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [this] at hy
    exact (QuotientGroup.eq_one_iff _).mpr hy

theorem le_normalizer_of_conj {G : Type*} [Group G] {A H : Subgroup G}
    (h : ∀ a ∈ A, ∀ x ∈ H, a * x * a⁻¹ ∈ H) : A ≤ Subgroup.normalizer (H : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h a ha x hx, fun hx => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hx
  simpa [mul_assoc] using this

theorem isPGroup_map_of_pow {A Q : Type*} [Group A] [Group Q] (π : A →* Q) (H : Subgroup A)
    (h : ∀ a ∈ H, ∃ k : ℕ, π (a ^ 2 ^ k) = 1) : IsPGroup 2 (H.map π) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨k, hk⟩ := h a ha
  exact ⟨k, Subtype.ext (by simpa [map_pow] using hk)⟩

theorem tightInO2_of_trans {z : Y} {K K' W : Subgroup Y}
    (hKC : K ≤ Subgroup.centralizer ({z} : Set Y)) (hK'C : K' ≤ Subgroup.centralizer ({z} : Set Y))
    (hWC : W ≤ Subgroup.centralizer ({z} : Set Y)) (hW2 : IsPGroup 2 W)
    (hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Y)))
    (hK'2 : ∀ x ∈ K', ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Y)))
    (hcomm : ∀ a ∈ K, ∀ b ∈ K',
      a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Y)))
    (hnorm : ∀ c ∈ Subgroup.centralizer ({z} : Set Y), ∀ x ∈ K ⊔ K', c * x * c⁻¹ ∈ K ⊔ K')
    (htrans : ∀ c ∈ Subgroup.centralizer ({z} : Set Y),
      ∃ x ∈ (K ⊔ K') ⊔ oddCoreIn (Subgroup.centralizer ({z} : Set Y)), conjSub x W = conjSub c W) :
    ∃ Pb : Subgroup (↥(Subgroup.centralizer ({z} : Set Y)) ⧸
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y))),
      Pb.Normal ∧ IsPGroup 2 Pb ∧ ∀ (w : Y) (hw : w ∈ W),
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)))
          ⟨w, hWC hw⟩ ∈ Pb := by
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hC
  set N : Subgroup ↥C := classicalInvolutionOddCore ↥C with hN
  set π : ↥C →* ↥C ⧸ N := QuotientGroup.mk' N with hπ
  have hKK : K ⊔ K' ≤ C := sup_le hKC hK'C
  set O : Subgroup Y := oddCoreIn C with hOdef
  have hOC : O ≤ C := oddCoreIn_le C
  have hKKO : (K ⊔ K') ⊔ O ≤ C := sup_le hKK hOC
  set P₀ : Subgroup Y := W ⊔ ((K ⊔ K') ⊔ O) with hP₀
  have hP₀C : P₀ ≤ C := sup_le hWC hKKO
  have hcore : ∀ c ∈ C, ∀ p ∈ P₀, c * p * c⁻¹ ∈ P₀ := by
    intro c hc p hp
    obtain ⟨x, hx, hxW⟩ := htrans c hc
    have hxC : x ∈ C := hKKO hx
    have hnC : x⁻¹ * c ∈ C := C.mul_mem (C.inv_mem hxC) hc
    have hnW : ∀ w ∈ W, x⁻¹ * c * w * (x⁻¹ * c)⁻¹ ∈ W := by
      intro w hw
      have h1 : c * w * c⁻¹ ∈ conjSub c W := conj_mem_conjSub hw
      rw [← hxW, mem_conjSub_iff] at h1
      have : x⁻¹ * c * w * (x⁻¹ * c)⁻¹ = x⁻¹ * (c * w * c⁻¹) * x := by group
      rw [this]
      exact h1
    have hnX : ∀ y ∈ K ⊔ K', x⁻¹ * c * y * (x⁻¹ * c)⁻¹ ∈ K ⊔ K' := fun y hy => hnorm _ hnC y hy
    have hnO : ∀ y ∈ O, x⁻¹ * c * y * (x⁻¹ * c)⁻¹ ∈ O := fun y hy => conj_mem_oddCoreIn hnC hy
    have hnP : x⁻¹ * c * p * (x⁻¹ * c)⁻¹ ∈ P₀ := by
      have : P₀ ≤ P₀.comap (MulAut.conj (x⁻¹ * c)).toMonoidHom := by
        refine sup_le (fun w hw => ?_) (sup_le (fun y hy => ?_) (fun y hy => ?_))
        · exact Subgroup.mem_sup_left (hnW w hw)
        · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (hnX y hy))
        · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (hnO y hy))
      exact this hp
    have hxP : x ∈ P₀ := Subgroup.mem_sup_right hx
    have := P₀.mul_mem (P₀.mul_mem hxP hnP) (P₀.inv_mem hxP)
    have e : c * p * c⁻¹ = x * (x⁻¹ * c * p * (x⁻¹ * c)⁻¹) * x⁻¹ := by group
    rw [e]
    exact this
  set P : Subgroup ↥C := P₀.subgroupOf C with hP
  have hPn : P.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hcore g g.2 n hn
  set K₁ : Subgroup ↥C := K.subgroupOf C with hK₁
  set K₁' : Subgroup ↥C := K'.subgroupOf C with hK₁'
  set W₁ : Subgroup ↥C := W.subgroupOf C with hW₁
  set O₁ : Subgroup ↥C := O.subgroupOf C with hO₁
  have hPeq : P = W₁ ⊔ ((K₁ ⊔ K₁') ⊔ O₁) := by
    rw [hP, hP₀, hW₁, hK₁, hK₁', hO₁, ← Subgroup.subgroupOf_sup hKC hK'C,
      ← Subgroup.subgroupOf_sup hKK hOC]
    exact Subgroup.subgroupOf_sup hWC hKKO
  have hmk : ∀ x (hx : x ∈ C), π ⟨x, hx⟩ = 1 ↔ x ∈ oddCoreIn C := fun x hx => mk_eq_one_iff hx
  have hOb : O₁.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker]
    exact (hmk y.1 y.2).mpr (Subgroup.mem_subgroupOf.mp hy)
  have hKb : IsPGroup 2 (K₁.map π) := by
    refine isPGroup_map_of_pow π K₁ fun a ha => ?_
    obtain ⟨k, hk⟩ := hK2 (a : Y) (Subgroup.mem_subgroupOf.mp ha)
    exact ⟨k, (hmk _ _).mpr (by simpa using hk)⟩
  have hKb' : IsPGroup 2 (K₁'.map π) := by
    refine isPGroup_map_of_pow π K₁' fun a ha => ?_
    obtain ⟨k, hk⟩ := hK'2 (a : Y) (Subgroup.mem_subgroupOf.mp ha)
    exact ⟨k, (hmk _ _).mpr (by simpa using hk)⟩
  have hWb : IsPGroup 2 (W₁.map π) := (hW2.comap_subtype).map π
  have hcommb : K₁.map π ≤ Subgroup.normalizer ((K₁'.map π : Subgroup _) : Set _) := by
    refine le_normalizer_of_conj fun y hy x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : (a : Y) * (b : Y) * (a : Y)⁻¹ * (b : Y)⁻¹ ∈ oddCoreIn C :=
      hcomm a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb)
    have h2 : π (a * b * a⁻¹ * b⁻¹) = 1 := (hmk _ _).mpr (by simpa using h1)
    have h3 : π a * π b * (π a)⁻¹ = π b := by
      have : π a * π b * (π a)⁻¹ * (π b)⁻¹ = 1 := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]; exact h2
      calc π a * π b * (π a)⁻¹ = (π a * π b * (π a)⁻¹ * (π b)⁻¹) * π b := by group
        _ = π b := by rw [this, one_mul]
    rw [h3]
    exact Subgroup.mem_map_of_mem _ hb
  have hKKb : IsPGroup 2 ((K₁.map π) ⊔ (K₁'.map π) : Subgroup _) :=
    hKb.to_sup_of_normal_right' hKb' hcommb
  have hWnb : W₁.map π ≤ Subgroup.normalizer (((K₁.map π) ⊔ (K₁'.map π) : Subgroup _) : Set _) := by
    refine le_normalizer_of_conj fun y hy x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← Subgroup.map_sup] at hx ⊢
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hb' : (b : Y) ∈ K ⊔ K' := by
      have : b ∈ K₁ ⊔ K₁' := hb
      rw [hK₁, hK₁', ← Subgroup.subgroupOf_sup hKC hK'C] at this
      exact Subgroup.mem_subgroupOf.mp this
    have hab : (a : Y) * (b : Y) * (a : Y)⁻¹ ∈ K ⊔ K' :=
      hnorm a a.2 b hb'
    refine Subgroup.mem_map.mpr ⟨a * b * a⁻¹, ?_, by simp⟩
    have h5 : a * b * a⁻¹ ∈ (K ⊔ K').subgroupOf C := Subgroup.mem_subgroupOf.mpr (by simpa using hab)
    rw [hK₁, hK₁', ← Subgroup.subgroupOf_sup hKC hK'C]
    exact h5
  have hPb2 : IsPGroup 2 (W₁.map π ⊔ ((K₁.map π) ⊔ (K₁'.map π)) : Subgroup _) :=
    hWb.to_sup_of_normal_right' hKKb hWnb
  refine ⟨P.map π, hPn.map π (QuotientGroup.mk'_surjective N), ?_, fun w hw => ?_⟩
  · rw [hPeq, Subgroup.map_sup, Subgroup.map_sup, hOb, sup_bot_eq, Subgroup.map_sup]
    exact hPb2
  · refine Subgroup.mem_map.mpr ⟨⟨w, hWC hw⟩, ?_, rfl⟩
    rw [hP, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hw

end Sub

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
