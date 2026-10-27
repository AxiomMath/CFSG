module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.M12Rows

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

variable {Y : Type} [Group Y] {τ : Y}

private theorem card_centralizerIn_m12_involution
    {v : Equiv.Perm (Fin 12)}
    (hv : v ∈ NativeSporadic.M12) (h2 : orderOf v = 2) :
    Nat.card (centralizerIn NativeSporadic.M12 v) = 192 ∨
      Nat.card (centralizerIn NativeSporadic.M12 v) = 240 := by
  obtain ⟨r, hr, c, hc, rfl⟩ := m12_involution_cover.1 v (by rw [inv_one, one_mul]; exact hv) h2
  rw [← Nat.card_congr (centralizerInConjEquiv NativeSporadic.M12 hc r).toEquiv]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl card_centralizerIn_m12Rep1
  · exact Or.inr card_centralizerIn_m12Rep2

theorem z2a5_not_M12
    [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y}
    (hS : FixedData Y S) : ¬ NativeSporadic.IsSporadic ↥S .M12 := by
  intro hM12
  have h120 : Nat.card ↥(centralizer ({τ} : Set Y)) = 120 := by
    obtain ⟨e0⟩ := h.2.1
    rw [Nat.card_congr e0.toEquiv, Nat.card_prod]
    have halt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [halt5]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [h2]
  obtain ⟨ψ₀⟩ := hM12
  by_cases htop : S = ⊤
  ·
    subst S
    let ψ : ↥(⊤ : Subgroup Y) ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := ψ₀
    let e : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := Subgroup.topEquiv.symm.trans ψ
    have hmem : (e τ : Equiv.Perm (Fin 12)) ∈ NativeSporadic.M12 := (e τ).2
    have h2e : orderOf (e τ : Equiv.Perm (Fin 12)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h.1]
    have hcard2 : Nat.card ↥(centralizer ({τ} : Set Y)) =
        Nat.card (centralizerIn NativeSporadic.M12 (e τ : Equiv.Perm (Fin 12))) :=
      Nat.card_congr ((centralizerEquiv e τ).trans
        (centralizerSubgroupEquiv NativeSporadic.M12 (e τ))).toEquiv
    rw [h120] at hcard2
    rcases card_centralizerIn_m12_involution hmem h2e with h' | h' <;> rw [h'] at hcard2 <;> omega
  ·
    let ψ : ↥S ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := ψ₀
    haveI := hS.normal
    obtain ⟨r, hr, κ, hκi, hκs⟩ := exists_rep_map S ψ hS.cent h.1
    have hbij := m12Rho_bijective_of_ne_top S ψ hS.cent htop
    have hκb : Function.Bijective κ := ⟨hκi, hκs hbij.2⟩
    have hcard2 : Nat.card ↥(centralizer ({τ} : Set Y)) =
        Nat.card ↥(centralizerIn autModel r) :=
      Nat.card_congr (Equiv.ofBijective κ hκb)
    rw [h120] at hcard2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨h1, h2, -⟩ := q2Q_spec
      rw [← h1, h2] at hcard2
      omega
    · obtain ⟨h1, h2, -⟩ := q4Q_spec
      rw [← h1, h2] at hcard2
      omega
    · obtain ⟨h1, h2, -⟩ := q5Q_spec
      rw [← h1, h2] at hcard2
      omega

end CFSG.OddStandard.SmallF3.Omega
