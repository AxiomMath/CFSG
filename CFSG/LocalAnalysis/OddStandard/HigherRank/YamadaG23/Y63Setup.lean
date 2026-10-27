module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Tr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63SSub

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem y63_setup {D : Data} [Group Y63TG] (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hI : D.InvSpec) (hM : D.MSpec) (hS : D.SSpec)
    (hτ : ∀ k < 4, D.TauSpec k) (gen : Fin 5 → Y63TG)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hg0 : (gen 0).val = D.T 0 0) (hg1 : (gen 1).val = D.T 0 2) (hg2 : (gen 2).val = D.T 0 4)
    (hg3 : (gen 3).val = D.T 0 6) (hg4 : (gen 4).val = D.T 0 8)
    {G : Type} [Group G] {P M S : Subgroup G} {t : G} (ψ : ↥P ≃* Y63TG)
    (hMP : M ≤ P) (hPN : P ≤ normalizer (M : Set G))
    (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hMcard : Nat.card ↥M = 64)
    (hM4 : ∀ m ∈ M, m ^ 4 = 1) (hSP : S ≤ P) (hScard : Nat.card ↥S = 64) (hSM : S ⊔ M = P)
    (hΩ : omega1 M ≤ S) (hSt : ∀ x ∈ S, t * x * t⁻¹ = x)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ = m⁻¹) :
    ∃ k < 4, ∃ φ : ↥P ≃* Y63TG, ∀ x : ↥P, ∃ hx : t * (x : G) * t⁻¹ ∈ P,
      (φ ⟨t * (x : G) * t⁻¹, hx⟩).val = D.tau k (φ x).val := by
  haveI hMn : (y63Img ψ M).Normal := y63Img_normal ψ hMP hPN
  have hMset : ∀ x : Y63TG, x ∈ y63Img ψ M ↔ x.val ∈ D.m0 :=
    y63_M_eq hmul h1 hM (y63Img ψ M) (by rw [y63Img_card ψ hMP]; exact hMcard)
      (y63Img_exp ψ hM4) (y63Img_comm ψ hMc)
  have hBcard : Nat.card ↥(y63Img ψ S) = 64 := by rw [y63Img_card ψ hSP]; exact hScard
  have hN : ∀ x : Y63TG, x.val ∈ D.nn → x ∈ y63Img ψ S := by
    intro x hx
    simp only [Y63Chk.Data.nn, List.mem_filter, beq_iff_eq] at hx
    exact y63Img_omega ψ hΩ ((hMset x).mpr hx.1) (Y63TG.ext (by rw [hmul, h1]; exact hx.2))
  obtain ⟨k, hk, g, hg⟩ := y63_S_classify hmul h1 hI hM hS gen hgen hg0 hg1 hg2 hg3 hg4
    (y63Img ψ M) hMset (y63Img ψ S) hBcard hN (y63Img_sup ψ hSP hMP hPN hSM)
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥P ≃* Y63TG, ∀ y, φ y = g⁻¹ * ψ y * g :=
    ⟨ψ.trans (MulAut.conj g⁻¹), fun y => by simp [MulAut.conj_apply]⟩
  refine ⟨k, hk, φ, fun x => ?_⟩
  obtain ⟨s, hs, m, hm, hxsm⟩ := y63_decomp hSP hMP hPN hSM x.1 x.2
  have hxt : t * (x : G) * t⁻¹ = s * m⁻¹ := by
    rw [hxsm]
    calc t * (s * m) * t⁻¹ = (t * s * t⁻¹) * (t * m * t⁻¹) := by group
      _ = s * m⁻¹ := by rw [hSt s hs, hMt m hm]
  have hxP : t * (x : G) * t⁻¹ ∈ P := by
    rw [hxt]
    exact P.mul_mem (hSP hs) (P.inv_mem (hMP hm))
  refine ⟨hxP, ?_⟩
  have hx : x = (⟨s, hSP hs⟩ : ↥P) * ⟨m, hMP hm⟩ := Subtype.ext hxsm
  have hxt' : (⟨t * (x : G) * t⁻¹, hxP⟩ : ↥P) = (⟨s, hSP hs⟩ : ↥P) * (⟨m, hMP hm⟩ : ↥P)⁻¹ :=
    Subtype.ext hxt
  have hsB : ψ ⟨s, hSP hs⟩ ∈ y63Img ψ S := by
    rw [mem_y63Img, ψ.symm_apply_apply]
    exact hs
  have hmM : ψ ⟨m, hMP hm⟩ ∈ y63Img ψ M := by
    rw [mem_y63Img, ψ.symm_apply_apply]
    exact hm
  have h1' : (φ ⟨s, hSP hs⟩).val ∈ D.sk k := by
    rw [hφ]
    exact (hg _).mp hsB
  have h2' : (φ ⟨m, hMP hm⟩).val ∈ D.m0 := by
    rw [hφ]
    exact (hMset _).mp (hMn.conj_mem' _ hmM g)
  rw [hxt', hx, map_mul, map_mul, map_inv, hmul, y63_inv_val hmul h1 hI, hmul]
  exact ((hτ k hk).2 _ h1' _ h2').symm

end CFSG.OddStandard.HigherRank.YamadaG23
