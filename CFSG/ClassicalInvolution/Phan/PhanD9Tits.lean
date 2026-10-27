module

public import CFSG.ClassicalInvolution.Phan.PhanD8Phi
public import CFSG.ClassicalInvolution.Phan.TitsChamber
import CFSG.ClassicalInvolution.Phan.Parabolic.Generation

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
open CFSG.Timmesfeld (edgeD)
open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {Y : Type} [Group Y] (S : PhanFamilyD4 K p f G)

@[expose] noncomputable def phanSystem : ChamberSystem (Fin 4) (G ⧸ torusSub S) :=
  cosetSystem (torusSub S) (fun i => parab S {i}) (fun i => torusSub_le_parab {i})

variable {S}

theorem phanSystem_adj_mk {i : Fin 4} {a b : G} :
    (phanSystem S).adj i (a : G ⧸ torusSub S) b ↔ a⁻¹ * b ∈ parab S {i} :=
  cosetSystem_adj_mk _

theorem smul_mk (g a : G) : g • (a : G ⧸ torusSub S) = ((g * a : G) : G ⧸ torusSub S) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]

theorem phanSystem_isMorphism_smul (g : G) : IsMorphism (phanSystem S) (phanSystem S) (g • ·) := by
  intro i x y h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [phanSystem_adj_mk] at h
  show (phanSystem S).adj i (g • (a : G ⧸ torusSub S)) (g • (b : G ⧸ torusSub S))
  rw [smul_mk, smul_mk, phanSystem_adj_mk]
  simpa [mul_assoc] using h

variable (S) in
@[expose] noncomputable def stabSub (J : Set (Fin 4)) : Subgroup G where
  carrier := {g | (g : G ⧸ torusSub S) ∈ (phanSystem S).residue J ((1 : G) : G ⧸ torusSub S)}
  mul_mem' {a b} ha hb := by
    have h1 : a • (b : G ⧸ torusSub S) ∈
        (phanSystem S).residue J (a • ((1 : G) : G ⧸ torusSub S)) :=
      (phanSystem_isMorphism_smul (S := S) a).mapsTo_residue J ((1 : G) : G ⧸ torusSub S) hb
    rw [smul_mk, smul_mk, mul_one, residue_eq_of_mem ha] at h1
    exact h1
  one_mem' := self_mem_residue _ _
  inv_mem' {a} ha := by
    have h1 : a⁻¹ • (a : G ⧸ torusSub S) ∈
        (phanSystem S).residue J (a⁻¹ • ((1 : G) : G ⧸ torusSub S)) :=
      (phanSystem_isMorphism_smul (S := S) a⁻¹).mapsTo_residue J ((1 : G) : G ⧸ torusSub S) ha
    rw [smul_mk, smul_mk, inv_mul_cancel, mul_one] at h1
    exact mem_residue_symm h1

theorem mem_stabSub (J : Set (Fin 4)) (g : G) :
    g ∈ stabSub S J ↔
      (g : G ⧸ torusSub S) ∈ (phanSystem S).residue J ((1 : G) : G ⧸ torusSub S) :=
  Iff.rfl

theorem mem_parab_iff (J : Set (Fin 4)) (g : G) :
    g ∈ parab S J ↔ (g : G ⧸ torusSub S) ∈
      (phanSystem S).residue J ((1 : G) : G ⧸ torusSub S) := by
  constructor
  · have hle : parab S J ≤ stabSub S J := by
      refine sup_le (fun x hx => ?_) (iSup₂_le fun j hj => ?_)
      · rw [mem_stabSub, show (x : G ⧸ torusSub S) = ((1 : G) : G ⧸ torusSub S) from
          QuotientGroup.eq.2 (by simpa using inv_mem hx)]
        exact self_mem_residue _ _
      · rintro _ ⟨A, rfl⟩
        rw [mem_stabSub]
        refine ChamberSystem.residue_mono (Set.singleton_subset_iff.2 hj) _ ?_
        rw [mem_residue_singleton, phanSystem_adj_mk (S := S), inv_one, one_mul]
        exact Lsup_le_parab {j} (ι_mem_Lsup (Set.mem_singleton j) A)
    exact fun hg => hle hg
  · intro hg
    obtain ⟨s, hs, hsg⟩ := exists_mem_of_mem_residue (fun i => torusSub_le_parab {i})
      (parab S J) (fun j hj => parab_mono (Set.singleton_subset_iff.2 hj)) 1 hg
    have h1 : s⁻¹ * g ∈ torusSub S := by
      have := QuotientGroup.eq.1 hsg
      simpa using inv_mem this
    have : g = s * (s⁻¹ * g) := by group
    rw [this]
    exact mul_mem hs (torusSub_le_parab J h1)

variable (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S) (h2 : (2 : K) ≠ 0)

include hK hq hg h2 in
theorem universal_of_geometry (hconn : (phanSystem S).Connected)
    (hsc : (phanSystem S).SimplyTwoConnected) (F : PhanFamilyD4 K p f Y) :
    ∃ ψ : G →* Y, (∀ i, ψ.comp (S.ι i) = F.ι i) ∧ ∀ e, ψ.comp (S.θ e) = F.θ e := by
  obtain ⟨φ, hφ, hcompat⟩ := exists_phi_family F hK (by omega) hg h2
  have hsmul : ∀ g : G, (g • ((1 : G) : G ⧸ torusSub S) : G ⧸ torusSub S) = (g : G ⧸ torusSub S) :=
    fun g => by rw [smul_mk, mul_one]
  obtain ⟨ψ, hψ, -⟩ := tits_chamber_universal_completion_of_family (phanSystem S)
    (fun J => J.encard ≤ 2) (by simp) (fun i => by simp) hconn
    ((simplyTwoConnected_iff _).1 hsc) (G := G)
    (fun g i x y h => phanSystem_isMorphism_smul g i x y h) ((1 : G) : G ⧸ torusSub S)
    (fun c => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
      exact ⟨a, hsmul a⟩)
    (parab S) (fun J _ g => by rw [hsmul g]; exact mem_parab_iff J g)
    (fun J hJ => φ J hJ)
    (fun J J' hJ hJ' hJJ' g hgJ' hgJ => hcompat J J' hJ hJ' hJJ' g hgJ' hgJ)
  have hι : ∀ (i : Fin 4) (A : Su K p f 2), ψ (S.ι i A) = F.ι i A := by
    intro i A
    have hJ : ({i} : Set (Fin 4)).encard ≤ 2 := by simp
    have := hψ {i} hJ ⟨S.ι i A, Lsup_le_parab {i} (ι_mem_Lsup (Set.mem_singleton i) A)⟩
    exact this.trans ((hφ {i} hJ).2 i (Set.mem_singleton i) A)
  refine ⟨ψ, fun i => MonoidHom.ext fun A => hι i A, fun e => ?_⟩
  have hle : B12 K p f ⊔ B23 K p f ≤ MonoidHom.eqLocus (ψ.comp (S.θ e)) (F.θ e) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      show ψ (S.θ e (embSUid (unitaryInvolution K p f) 2 A)) =
        F.θ e (embSUid (unitaryInvolution K p f) 2 A)
      rw [← ι_src, ← ι_src, hι]
    · rintro _ ⟨A, rfl⟩
      show ψ (S.θ e (embSUid (unitaryInvolution K p f) 0 A)) =
        F.θ e (embSUid (unitaryInvolution K p f) 0 A)
      rw [← ι_tgt, ← ι_tgt, hι]
  rw [B12_sup_B23_eq_top hK (by omega)] at hle
  exact MonoidHom.ext fun B => hle (Subgroup.mem_top B)

end CFSG.ClassicalInvolution.PhanD4
