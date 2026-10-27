module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18a

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

set_option quotPrecheck false in
local notation "D1" => (t1G ()).tab
set_option quotPrecheck false in
local notation "I1" => idx1 (t1G ()).tab

theorem z_mem_A (m : G23Model G) : (frameOf m).z ∈ (frameOf m).A :=
  pow_mem (subset_closure (by simp)) 2

theorem z_mem_EF (m : G23Model G) : (frameOf m).z ∈ (frameOf m).E ⊔ (frameOf m).F :=
  mem_sup_left (subset_closure (by simp))

theorem G23LCtx.card_T1 (X : G23LCtx m) : Nat.card (g23T1 m) = 1152 := X.f1.card_T1

theorem G23LCtx.T1_le_cent (X : G23LCtx m) : g23T1 m ≤ centEl ⊤ (frameOf m).z := X.f1.T1_le_cent

theorem G23LCtx.T1_eq_cent (X : G23LCtx m) : g23T1 m = centEl ⊤ (frameOf m).z := by
  have hΓ : Nat.card G = 2 * Nat.card m.L := by rw [m.card_G, m.card_L]
  have hinf : (m.L ⊓ centEl ⊤ (frameOf m).z : Subgroup G) = centEl m.L (frameOf m).z := by
    ext g
    simp [centEl]
  refine eq_of_card_two_mul hΓ X.T1_le_cent ?_
  rw [X.card_T1, hinf, m.card_cent (frameOf m).z X.z_mem_invols]

theorem G23LCtx.mem_T1_of_comm (X : G23LCtx m) {g : G}
    (hg : ⁅(frameOf m).z, g⁆ ∈ (frameOf m).Z) : g ∈ g23T1 m := by
  rw [X.T1_eq_cent]
  refine ⟨mem_top g, ?_⟩
  change g ∈ Subgroup.centralizer ({(frameOf m).z} : Set G)
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_of_comm_mem X.z_ne_one X.z_sq hg
  calc g * (frameOf m).z = (g * (frameOf m).z * g⁻¹) * g := by group
    _ = (frameOf m).z * g := by rw [h]

theorem G23LCtx.T1_S3S3 (X : G23LCtx m) :
    SecProp (g23T1 m) (frameOf m).A
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := X.f1.T1_S3S3

theorem G23LCtx.commMod_A (X : G23LCtx m) :
    {g : G | g ∈ g23T1 m ∧ ∀ a ∈ (frameOf m).A, ⁅a, g⁆ ∈ (frameOf m).Z} =
      ((frameOf m).A : Set G) := X.f1.commMod_A

theorem G23LCtx.commMod_EF (X : G23LCtx m) :
    {g : G | g ∈ g23T1 m ∧ ∀ y ∈ (frameOf m).E ⊔ (frameOf m).F, ⁅y, g⁆ ∈ (frameOf m).Z} =
      ((frameOf m).A : Set G) := X.f1.commMod_EF

theorem G23LCtx.F_cent_sigma (X : G23LCtx m) :
    ∀ f ∈ (frameOf m).F, (frameOf m).σ * f = f * (frameOf m).σ := X.f1.F_cent_sigma

theorem sup_sigma_eq_top (m : G23Model G) : m.L ⊔ closure {(frameOf m).σ} = ⊤ :=
  sup_closure_eq_top (by rw [m.card_G, m.card_L]) (frame_sigma_not_mem m)

theorem G23LCtx.fact110 (X : G23LCtx m) : (frameOf m).Fact110 m.L := by
  have hsup := sup_sigma_eq_top m
  refine ⟨⟨?_, ?_, ?_⟩, fact110_two_of_centIn m.normal (frame_sigma_sq m) X.centIn_F
    X.F_cent_sigma⟩
  · rw [X.normIn_A, g23H_sup_sigma]
    exact X.T1_S3S3
  · ext g
    constructor
    · rintro ⟨-, hP⟩
      exact X.commMod_A.subset ⟨X.mem_T1_of_comm (hP _ (z_mem_A m)), hP⟩
    · intro hg
      obtain ⟨-, hP⟩ := X.commMod_A.superset hg
      exact ⟨by rw [hsup]; exact mem_top g, hP⟩
  · ext g
    constructor
    · rintro ⟨-, hP⟩
      exact X.commMod_EF.subset ⟨X.mem_T1_of_comm (hP _ (z_mem_EF m)), hP⟩
    · intro hg
      obtain ⟨-, hP⟩ := X.commMod_EF.superset hg
      exact ⟨by rw [hsup]; exact mem_top g, hP⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
