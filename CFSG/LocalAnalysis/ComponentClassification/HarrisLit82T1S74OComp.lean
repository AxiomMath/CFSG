module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74OSetup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

namespace SetupOdd

variable {G : Type} [Group G] [Finite G] (S : SetupOdd G)

abbrev IsJ (J : Subgroup S.X) : Prop := J = spinJ₁ S.K ∨ J = spinJ₂ S.K ∨ J = spinJ₃ S.K

theorem map_le_D {A : Subgroup S.X} (hA : A ≤ centralizer {tSeven S.K}) : A.map S.φ ≤ S.D := by
  rintro _ ⟨x, hx, rfl⟩
  have h := (S.map_centralizer (tSeven S.K)).le ⟨x, hA hx, rfl⟩
  exact ⟨S.hLH (mem_inf.mp h).1, (mem_inf.mp h).2⟩

theorem conj_mem_L_inf_D {d x : G} (hd : d ∈ S.D) (hx : x ∈ S.L ⊓ S.D) :
    d * x * d⁻¹ ∈ S.L ⊓ S.D :=
  mem_inf.mpr ⟨S.hLn d (mem_inf.mp hd).1 x (mem_inf.mp hx).1,
    mul_mem (mul_mem hd (mem_inf.mp hx).2) (inv_mem hd)⟩

theorem odd_relIndex_L_inf_D : Odd ((S.L ⊓ S.D).relIndex S.D) := by
  have hDH : S.D ≤ S.H := inf_le_left
  let L' := S.L.subgroupOf S.H
  let D' := S.D.subgroupOf S.H
  have hL' : L'.Normal := ⟨fun n hn h => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact S.hLn h h.2 n hn⟩
  have h1 : L'.relIndex (L' ⊔ D') = L'.relIndex D' := relIndex_sup_left D' L'
  have h2 : L'.relIndex (L' ⊔ D') ∣ L'.index := relIndex_dvd_index_of_le le_sup_left
  have h3 : L'.relIndex D' = S.L.relIndex S.D := relIndex_subgroupOf hDH
  have h4 : (S.L ⊓ S.D).relIndex S.D = S.L.relIndex S.D := inf_relIndex_right S.L S.D
  rw [h4, ← h3, ← h1]
  exact Odd.of_dvd_nat S.hodd h2

theorem map_centralizer_tSeven :
    (centralizer ({tSeven S.K} : Set S.X)).map S.φ = S.L ⊓ S.D := by
  rw [S.map_centralizer]
  ext x
  constructor
  · intro hx
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, mem_inf.mpr ⟨S.hLH (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩⟩
  · intro hx
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).2⟩

theorem conj_mem_map_centralizer {d x : G} (hd : d ∈ S.D)
    (hx : x ∈ (centralizer ({tSeven S.K} : Set S.X)).map S.φ) :
    d * x * d⁻¹ ∈ (centralizer ({tSeven S.K} : Set S.X)).map S.φ := by
  rw [S.map_centralizer_tSeven] at hx ⊢
  exact S.conj_mem_L_inf_D hd hx

theorem odd_relIndex_map_centralizer :
    Odd (((centralizer ({tSeven S.K} : Set S.X)).map S.φ).relIndex S.D) := by
  rw [S.map_centralizer_tSeven]
  exact S.odd_relIndex_L_inf_D

theorem mem_normalizer_D_of_swap {n : G} (h1 : n * S.t * n⁻¹ = S.z)
    (h2 : n * S.z * n⁻¹ = S.t) : n ∈ normalizer (S.D : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  have key : ∀ a b : G, n * a * n⁻¹ = b → (x * a = a * x ↔
      n * x * n⁻¹ * b = b * (n * x * n⁻¹)) := by
    intro a b hab
    rw [← hab]
    constructor
    · intro h
      calc n * x * n⁻¹ * (n * a * n⁻¹) = n * (x * a) * n⁻¹ := by group
        _ = n * (a * x) * n⁻¹ := by rw [h]
        _ = n * a * n⁻¹ * (n * x * n⁻¹) := by group
    · intro h
      calc x * a = n⁻¹ * (n * x * n⁻¹ * (n * a * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * a * n⁻¹ * (n * x * n⁻¹)) * n := by rw [h]
        _ = a * x := by group
  rw [key S.z S.t h2, key S.t S.z h1]
  exact and_comm

theorem map_conj_J_of_mem_D {d : G} (hd : d ∈ S.D) {J : Subgroup S.X} (hJ : S.IsJ J) :
    (J.map S.φ).map (MulAut.conj d).toMonoidHom = J.map S.φ := by
  have hdz : d * S.φ (spinZ S.K) * d⁻¹ = S.φ (spinZ S.K) := by
    rw [S.hφz, mem_centralizer_singleton_iff.mp (mem_inf.mp hd).1, mul_inv_cancel_right]
  have hdt : d * S.φ (tSeven S.K) * d⁻¹ = S.φ (tSeven S.K) := by
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2, mul_inv_cancel_right]
  exact map_conj_spinJ_of_fix S.hp S.hp2 S.hK S.hφ (S.map_le_D le_rfl)
    (fun _ hd' _ hx => S.conj_mem_map_centralizer hd' hx) S.odd_relIndex_map_centralizer
    (le_normalizer hd) hdz hdt hJ

theorem map_conj_swap {n : G} (h1 : n * S.t * n⁻¹ = S.z) (h2 : n * S.z * n⁻¹ = S.t) :
    ((spinJ₁ S.K).map S.φ).map (MulAut.conj n).toMonoidHom = (spinJ₂ S.K).map S.φ ∧
      ((spinJ₂ S.K).map S.φ).map (MulAut.conj n).toMonoidHom = (spinJ₁ S.K).map S.φ ∧
      ((spinJ₃ S.K).map S.φ).map (MulAut.conj n).toMonoidHom = (spinJ₃ S.K).map S.φ := by
  have h1' : n * S.φ (tSeven S.K) * n⁻¹ = S.φ (spinZ S.K) := by rw [S.hφz]; exact h1
  have h2' : n * S.φ (spinZ S.K) * n⁻¹ = S.φ (tSeven S.K) := by rw [S.hφz]; exact h2
  exact map_conj_spinJ_of_swap S.hp S.hp2 S.hK S.hφ (S.map_le_D le_rfl)
    (fun _ hd' _ hx => S.conj_mem_map_centralizer hd' hx) S.odd_relIndex_map_centralizer
    (S.mem_normalizer_D_of_swap h1 h2) h1' h2'

end SetupOdd

end CFSG.ComponentClassification.HarrisLit.T1.S74
