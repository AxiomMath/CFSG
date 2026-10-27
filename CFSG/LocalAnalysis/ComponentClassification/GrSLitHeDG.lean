module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDQ
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeDG

variable {Q : Type} [Group Q]

private theorem commutator_mul_eq {z₁ z₂ c₁ c₂ : Q} (hz : z₁ * z₂ = z₂ * z₁)
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

variable {A B : Subgroup Q} {α : Q}

theorem commute_of_mem_inf (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {i : Q} (hi : i ∈ A ⊓ B)
    {g : Q} (hg : g ∈ A ⊔ B) : i * g = g * i :=
  HeUC.commute_of_le_sup (fun x hx => (hAB x hx i (mem_inf.mp hi).2).symm)
    (fun y hy => hAB i (mem_inf.mp hi).1 y hy) hg

theorem delta_mem (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (x : ↥A) :
    HeDQ.delta hAB hαA x ∈ (A ⊔ B) ⊓ centralizer ({α} : Set Q) := by
  have hainv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  rw [HeDQ.delta_apply]
  refine mem_inf.mpr ⟨mul_mem (mem_sup_left x.2) (mem_sup_right (hαA x x.2)), ?_⟩
  rw [mem_centralizer_singleton_iff]
  have h := hAB x x.2 _ (hαA x x.2)
  calc (x : Q) * (α * x * α⁻¹) * α = (α * x * α⁻¹) * x * α := by rw [h]
    _ = α * ((x : Q) * (α * x * α⁻¹)) := by rw [hainv]; group

theorem exists_delta_mul (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A) {k : Q}
    (hk : k ∈ (A ⊔ B) ⊓ centralizer ({α} : Set Q)) :
    ∃ x : ↥A, ∃ i ∈ A ⊓ B, k = HeDQ.delta hAB hαA x * i := by
  have hainv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  obtain ⟨hk, hkα⟩ := hk
  obtain ⟨m, hm, n, hn, rfl⟩ := HeDQ.exists_mul_of_mem_sup hAB hk
  have hc : m * n * α = α * (m * n) := mem_centralizer_singleton_iff.mp hkα
  have h1 : (α * n * α⁻¹) * (α * m * α⁻¹) = m * n := by
    have h2 : (α * m * α⁻¹) * (α * n * α⁻¹) = m * n := by
      calc (α * m * α⁻¹) * (α * n * α⁻¹) = α * (m * n) * α⁻¹ := by group
        _ = m * n * α * α⁻¹ := by rw [hc]
        _ = m * n := by group
    rw [← h2]
    exact hAB _ (hαB n hn) _ (hαA m hm)
  set i := (α * n * α⁻¹)⁻¹ * m with hi
  have hiAB : i ∈ A ⊓ B := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem (hαB n hn)) hm, ?_⟩
    have : i = (α * m * α⁻¹) * n⁻¹ := by
      calc i = (α * n * α⁻¹)⁻¹ * (m * n) * n⁻¹ := by rw [hi]; group
        _ = (α * n * α⁻¹)⁻¹ * ((α * n * α⁻¹) * (α * m * α⁻¹)) * n⁻¹ := by rw [h1]
        _ = (α * m * α⁻¹) * n⁻¹ := by group
    rw [this]
    exact mul_mem (hαA m hm) (inv_mem hn)
  refine ⟨⟨α * n * α⁻¹, hαB n hn⟩, i, hiAB, ?_⟩
  rw [HeDQ.delta_apply]
  have hin : i * n = n * i := hAB i (mem_inf.mp hiAB).1 n hn
  have hnn : α * (α * n * α⁻¹) * α⁻¹ = n := by
    rw [hainv]
    calc α * (α * n * α) * α = (α * α) * n * (α * α) := by group
      _ = n := by rw [hα, one_mul, mul_one]
  show m * n = α * n * α⁻¹ * (α * (α * n * α⁻¹) * α⁻¹) * i
  rw [hnn]
  calc m * n = (α * n * α⁻¹) * i * n := by rw [hi]; group
    _ = (α * n * α⁻¹) * (i * n) := by group
    _ = α * n * α⁻¹ * n * i := by rw [hin]; group

theorem commutator_le_range (hα : α * α = 1) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A) :
    ⁅(A ⊔ B) ⊓ centralizer ({α} : Set Q), (A ⊔ B) ⊓ centralizer ({α} : Set Q)⁆ ≤
      (HeDQ.delta hAB hαA).range := by
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨x₁, i₁, hi₁, rfl⟩ := exists_delta_mul hα hAB hαA hαB hg₁
  obtain ⟨x₂, i₂, hi₂, rfl⟩ := exists_delta_mul hα hAB hαA hαB hg₂
  have hd : ∀ x : ↥A, HeDQ.delta hAB hαA x ∈ A ⊔ B := fun x =>
    (mem_inf.mp (delta_mem hα hAB hαA x)).1
  have hc : ∀ {i : Q}, i ∈ A ⊓ B → ∀ x : ↥A,
      HeDQ.delta hAB hαA x * i = i * HeDQ.delta hAB hαA x := fun hi x =>
    (commute_of_mem_inf hAB hi (hd x)).symm
  rw [hc hi₁, hc hi₂, commutatorElement_def,
    commutator_mul_eq (commute_of_mem_inf hAB hi₁ (mem_sup_left (mem_inf.mp hi₂).1))
      (commute_of_mem_inf hAB hi₁ (hd x₁)) (commute_of_mem_inf hAB hi₁ (hd x₂))
      (commute_of_mem_inf hAB hi₂ (hd x₁)) (commute_of_mem_inf hAB hi₂ (hd x₂))]
  refine ⟨x₁ * x₂ * x₁⁻¹ * x₂⁻¹, ?_⟩
  simp only [map_mul, map_inv]

theorem ker_le_center (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) : (HeDQ.delta hAB hαA).ker ≤ center ↥A := by
  intro x hx
  rw [MonoidHom.mem_ker, HeDQ.delta_apply] at hx
  have hxB : (x : Q)⁻¹ ∈ B := by
    rw [← eq_inv_of_mul_eq_one_right hx]
    exact hαA x x.2
  refine mem_center_iff.mpr fun g => Subtype.ext ?_
  have h := hAB g g.2 _ hxB
  show (g : Q) * x = x * g
  calc (g : Q) * x = (x : Q) * ((x : Q)⁻¹ * g) * x := by group
    _ = (x : Q) * (g * (x : Q)⁻¹) * x := by rw [← h]
    _ = (x : Q) * g := by group

theorem isQuasisimple_range (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hAq : IsQuasisimple ↥A) :
    IsQuasisimple ↥(HeDQ.delta hAB hαA).range :=
  LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center hAq _
    (ker_le_center hAB hαA)

theorem gsFixedLayer_eq_range [Finite Q] (hα : α * α = 1)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B)
    (hαB : ∀ y ∈ B, α * y * α⁻¹ ∈ A) (hAq : IsQuasisimple ↥A)
    (hne : gsFixedLayer (A ⊔ B) α ≠ ⊥) :
    gsFixedLayer (A ⊔ B) α = (HeDQ.delta hAB hαA).range := by
  set D := (A ⊔ B) ⊓ centralizer ({α} : Set Q) with hD
  set R := (HeDQ.delta hAB hαA).range with hR
  set T := gsFixedLayer (A ⊔ B) α with hT
  have hTdef : T = (pLayer ↥D 2).map D.subtype := rfl
  have hTD : T ≤ D := gsFixedLayer_le_inf _ _
  have hRD : R ≤ D := by
    rintro _ ⟨x, rfl⟩
    exact delta_mem hα hAB hαA x
  have hTp : ⁅T, T⁆ = T := by
    rw [hTdef, ← map_commutator, UnbalancedCorr.pLayer_two_isPerfect]
  have hTR : T ≤ R := by
    rw [← hTp]
    exact (commutator_mono hTD hTD).trans (commutator_le_range hα hAB hαA hαB)
  have hTn : (T.subgroupOf R).Normal := by
    have hN : (pLayer ↥D 2).Normal := inferInstance
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨t, ht, htn⟩ := hn
    have hg : (g : Q) ∈ D := hRD g.2
    have h := hN.conj_mem t ht ⟨g, hg⟩
    refine ⟨⟨g, hg⟩ * t * (⟨g, hg⟩ : ↥D)⁻¹, h, ?_⟩
    simp only [coe_subtype, coe_mul, coe_inv] at htn ⊢
    rw [htn]
  rcases LocalCores.quasisimple_normal_subgroups (isQuasisimple_range hAB hαA hAq) hTn with h | h
  · apply le_antisymm hTR
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥R) ∈ T.subgroupOf R := h ▸ mem_top _
    exact hx'
  · exfalso
    apply hne
    rw [← hTp, commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := mem_center_iff.mp (h (show (⟨x, hTR hx⟩ : ↥R) ∈ T.subgroupOf R from hx))
      ⟨y, hTR hy⟩
    exact congrArg Subtype.val h1

theorem mem_center_of_delta (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) (hAq : IsQuasisimple ↥A) {x : ↥A}
    (hx : ∀ y : ↥A, HeDQ.delta hAB hαA x * HeDQ.delta hAB hαA y =
      HeDQ.delta hAB hαA y * HeDQ.delta hAB hαA x) :
    x ∈ center ↥A := by
  have hker := ker_le_center hAB hαA
  have hcomm : ∀ y : ↥A, x * y * x⁻¹ * y⁻¹ ∈ center ↥A := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hx y]
    group
  have hperf : commutator ↥A = ⊤ := hAq.1.commutator_eq_top
  have h := HeUC.commute_of_commutator_central (M := A) hperf (x := (x : Q))
    (le_normalizer x.2) (fun m hm n hn => by
      have h1 := mem_center_iff.mp (hcomm ⟨m, hm⟩) ⟨n, hn⟩
      exact (congrArg Subtype.val h1).symm)
  exact mem_center_iff.mpr fun g => Subtype.ext (h g g.2).symm

theorem delta_commute_conj (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ B) {x y : ↥A} (hxy : x * y = y * x) :
    HeDQ.delta hAB hαA y * (α * x * α⁻¹) = (α * x * α⁻¹) * HeDQ.delta hAB hαA y := by
  rw [HeDQ.delta_apply]
  have h1 : (y : Q) * (α * x * α⁻¹) = (α * x * α⁻¹) * y := hAB y y.2 _ (hαA x x.2)
  have hyx : (y : Q) * x = x * y := (congrArg Subtype.val hxy).symm
  have h2 : (α * y * α⁻¹) * (α * x * α⁻¹) = (α * x * α⁻¹) * (α * y * α⁻¹) := by
    calc (α * y * α⁻¹) * (α * x * α⁻¹) = α * ((y : Q) * x) * α⁻¹ := by group
      _ = α * ((x : Q) * y) * α⁻¹ := by rw [hyx]
      _ = (α * x * α⁻¹) * (α * y * α⁻¹) := by group
  calc (y : Q) * (α * y * α⁻¹) * (α * x * α⁻¹)
      = y * ((α * y * α⁻¹) * (α * x * α⁻¹)) := by group
    _ = y * ((α * x * α⁻¹) * (α * y * α⁻¹)) := by rw [h2]
    _ = (y * (α * x * α⁻¹)) * (α * y * α⁻¹) := by group
    _ = ((α * x * α⁻¹) * y) * (α * y * α⁻¹) := by rw [h1]
    _ = (α * x * α⁻¹) * (y * (α * y * α⁻¹)) := by group

end HeDG

end CFSG.ComponentClassification.GrSLit
