module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311u
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.NF
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Plane

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311x

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

set_option linter.unusedSectionVars false

theorem exists_mul_zpow_of_mem_closure_inputs2311x {G : Type*} [Group G] {S : Set G} {w : G}
    (h1 : ∀ s ∈ S, w * s * w⁻¹ ∈ S) (h2 : ∀ s ∈ S, w⁻¹ * s * w⁻¹⁻¹ ∈ S) {g : G}
    (hg : g ∈ Subgroup.closure (S ∪ {w})) :
    ∃ m ∈ Subgroup.closure S, ∃ k : ℤ, g = m * w ^ k := by
  set M := Subgroup.closure S with hM
  have key : ∀ u : G, (∀ s ∈ S, u * s * u⁻¹ ∈ S) → ∀ m ∈ M, u * m * u⁻¹ ∈ M := by
    intro u hu m hm
    have hle : M ≤ M.comap (MulAut.conj u).toMonoidHom := by
      rw [hM, Subgroup.closure_le]
      intro s hs
      simpa [MulAut.conj_apply] using Subgroup.subset_closure (hu s hs)
    simpa [MulAut.conj_apply] using hle hm
  have hwN : w ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · exact key w h1 m
    · intro hm
      have h3 := key w⁻¹ h2 _ hm
      have e : w⁻¹ * (w * m * w⁻¹) * w⁻¹⁻¹ = m := by group
      rwa [e] at h3
  have hconj : ∀ k : ℤ, ∀ m ∈ M, w ^ k * m * (w ^ k)⁻¹ ∈ M := fun k m hm =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ hwN k) m).1 hm
  let P : Subgroup G :=
    { carrier := {g | ∃ m ∈ M, ∃ k : ℤ, g = m * w ^ k}
      mul_mem' := by
        rintro _ _ ⟨m₁, hm₁, k₁, rfl⟩ ⟨m₂, hm₂, k₂, rfl⟩
        refine ⟨m₁ * (w ^ k₁ * m₂ * (w ^ k₁)⁻¹), M.mul_mem hm₁ (hconj k₁ m₂ hm₂), k₁ + k₂, ?_⟩
        group
      one_mem' := ⟨1, M.one_mem, 0, by rw [zpow_zero, one_mul]⟩
      inv_mem' := by
        rintro _ ⟨m, hm, k, rfl⟩
        refine ⟨w ^ (-k) * m⁻¹ * (w ^ (-k))⁻¹, hconj (-k) _ (M.inv_mem hm), -k, ?_⟩
        group }
  have hle : Subgroup.closure (S ∪ {w}) ≤ P := by
    rw [Subgroup.closure_le]
    rintro z (hz | hz)
    · exact ⟨z, Subgroup.subset_closure hz, 0, by rw [zpow_zero, mul_one]⟩
    · rw [Set.mem_singleton_iff] at hz
      exact ⟨1, M.one_mem, 1, by rw [hz, zpow_one, one_mul]⟩
  exact hle hg

section Main

theorem exists_moving_rElt_minus_inputs2311x (hEsc : Inputs2311u.TriOddA2Escape) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (E : Subgroup (MulAut (C0 σ))) (x : C0 σ)
    (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E ≤ innerAut (C0 σ)) (hng : ¬ TriOddHasGLine σ E)
    (hnc : ∀ γ : MulAut (C0 σ), TriOddIsGLine σ γ → ¬ ∀ α ∈ E, α * γ = γ * α)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hcx : MulAut.conj x ∈ E) :
    ∃ β ∈ E, β ≠ 1 ∧ ∃ y ∈ Subgroup.closure {y : C0 σ | β y = y ∧ ∃ n : ℕ, y ^ (ℓ ^ n) = 1},
      y * x * y⁻¹ ∉ Subgroup.zpowers x ∧ (y * x * y⁻¹) * x = x * (y * x * y⁻¹) := by
  classical
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  haveI : Finite (C0 σ) := by
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    exact Finite.of_injective (fun x : C0 σ => (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, β ∉ innerAut (C0 σ) := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have hβ3 : β ^ 3 = 1 := elemAb_cube hE β hβE
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
  have hβcx : β * MulAut.conj x = MulAut.conj x * β := elemAb_comm hE β hβE _ hcx
  have hβx : β x = x := apply_eq_of_commute_conj hinj hβcx
  have hβG : ¬ TriOddIsGLine σ β := fun h => hng ⟨β, hβE, h⟩
  obtain ⟨s, hsβ, hs3, hsG⟩ :=
    Parrott.ClosingMinus.Escape.outerToralForm_holds ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ β hβ3 hβout hβG
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcx1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (h.trans (map_one MulAut.conj).symm))
  have hcx3 : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hEcl : E = Subgroup.closure ({MulAut.conj x, β} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcx hβE hcx1 hcx3 hβ1 (fun h => hβout ⟨x, h.symm⟩)
      (fun h => hβout ⟨x ^ 2, by rw [map_pow]; exact h.symm⟩)
  set Y : Subgroup (C0 σ) := fixedSubgroup β with hY
  rcases Parrott.ClosingMinus.Escape.exists_conj_comm_or_fusion (G := Y) (x := ⟨x, hβx⟩)
      (s := ⟨s, hsβ⟩) (Subtype.ext (by simpa using hx3)) (fun h => hx1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hs3)) with ⟨g, hg⟩ | ⟨g, hg1, hg2⟩
  ·
    exfalso
    set t : C0 σ := (g : C0 σ) * s * (g : C0 σ)⁻¹ with ht
    have htx : t * x = x * t := by
      have := congrArg Subtype.val hg
      simpa [ht] using this
    have hgβ : β (g : C0 σ) = g := g.2
    have hcg : β * MulAut.conj (g : C0 σ) = MulAut.conj (g : C0 σ) * β := by
      have h2 := aut_conj_conj β (g : C0 σ)
      rw [hgβ] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    have htβ : β t = t := by
      rw [ht, map_mul, map_mul, map_inv, hgβ, hsβ]
    have hct : β * MulAut.conj t = MulAut.conj t * β := by
      have h2 := aut_conj_conj β t
      rw [htβ] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hctx : MulAut.conj t * MulAut.conj x = MulAut.conj x * MulAut.conj t := by
      rw [← map_mul, ← map_mul, htx]
    refine hnc ((MulAut.conj t)⁻¹ * β) ?_ ?_
    ·
      have e : (MulAut.conj t)⁻¹ * β =
          MulAut.conj (g : C0 σ) * ((MulAut.conj s)⁻¹ * β) * (MulAut.conj (g : C0 σ))⁻¹ := by
        have e1 : MulAut.conj t = MulAut.conj (g : C0 σ) * MulAut.conj s *
            (MulAut.conj (g : C0 σ))⁻¹ := by
          rw [ht, map_mul, map_mul, map_inv]
        have e2 : β * (MulAut.conj (g : C0 σ))⁻¹ = (MulAut.conj (g : C0 σ))⁻¹ * β :=
          (Commute.inv_right (show Commute β (MulAut.conj (g : C0 σ)) from hcg)).eq
        rw [e1]
        calc (MulAut.conj (g : C0 σ) * MulAut.conj s * (MulAut.conj (g : C0 σ))⁻¹)⁻¹ * β
            = MulAut.conj (g : C0 σ) * (MulAut.conj s)⁻¹ * ((MulAut.conj (g : C0 σ))⁻¹ * β) := by
              group
          _ = MulAut.conj (g : C0 σ) * (MulAut.conj s)⁻¹ * (β * (MulAut.conj (g : C0 σ))⁻¹) := by
              rw [e2]
          _ = _ := by group
      rw [e]
      exact Parrott.ClosingMinus.Escape.isGLine_conj hsG _
    ·
      have h1 : MulAut.conj x * (MulAut.conj t)⁻¹ = (MulAut.conj t)⁻¹ * MulAut.conj x :=
        (Commute.inv_right (show Commute (MulAut.conj x) (MulAut.conj t) from hctx.symm)).eq
      have h2 : β * (MulAut.conj t)⁻¹ = (MulAut.conj t)⁻¹ * β :=
        (Commute.inv_right (show Commute β (MulAut.conj t) from hct)).eq
      have hle : E ≤ Subgroup.centralizer {(MulAut.conj t)⁻¹ * β} := by
        rw [hEcl, Subgroup.closure_le]
        rintro a (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        · calc MulAut.conj x * ((MulAut.conj t)⁻¹ * β)
              = (MulAut.conj t)⁻¹ * (MulAut.conj x * β) := by rw [← mul_assoc, h1, mul_assoc]
            _ = (MulAut.conj t)⁻¹ * β * MulAut.conj x := by rw [← hβcx, mul_assoc]
        · rw [← mul_assoc, h2, mul_assoc]
      exact fun α hα => Subgroup.mem_centralizer_singleton_iff.1 (hle hα)
  ·
    have hcomm : ((g : C0 σ) * x * (g : C0 σ)⁻¹) * x = x * ((g : C0 σ) * x * (g : C0 σ)⁻¹) := by
      have := congrArg Subtype.val hg1
      simpa using this
    have hnot : (g : C0 σ) * x * (g : C0 σ)⁻¹ ∉ Subgroup.zpowers x := by
      intro hmem
      apply hg2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext ?_⟩
      simpa using hn
    obtain ⟨w, hβw, hwx, hgen⟩ := hEsc ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ β hβ3 hβout hβG x hβx hx3
    have hSinv : ∀ u : C0 σ, β u = u → ∀ z ∈ {y : C0 σ | β y = y ∧ ∃ n : ℕ, y ^ (ℓ ^ n) = 1},
        u * z * u⁻¹ ∈ {y : C0 σ | β y = y ∧ ∃ n : ℕ, y ^ (ℓ ^ n) = 1} := by
      rintro u hu z ⟨hz, n, hn⟩
      refine ⟨?_, n, ?_⟩
      · rw [map_mul, map_mul, map_inv, hu, hz]
      · rw [conj_pow, hn, mul_one, mul_inv_cancel]
    have hgβ : β (g : C0 σ) = g := g.2
    obtain ⟨m, hm, k, hgm⟩ := exists_mul_zpow_of_mem_closure_inputs2311x (hSinv w hβw)
      (hSinv w⁻¹ (by rw [map_inv, hβw])) (hgen _ hgβ)
    have hwkx : w ^ k * x * (w ^ k)⁻¹ = x := by
      rw [((show Commute w x from hwx).zpow_left k).eq, mul_inv_cancel_right]
    have hmx : m * x * m⁻¹ = (g : C0 σ) * x * (g : C0 σ)⁻¹ := by
      rw [hgm]
      calc m * x * m⁻¹ = m * (w ^ k * x * (w ^ k)⁻¹) * m⁻¹ := by rw [hwkx]
        _ = m * w ^ k * x * (m * w ^ k)⁻¹ := by group
    refine ⟨β, hβE, hβ1, m, hm, ?_, ?_⟩
    · rw [hmx]
      exact hnot
    · rw [hmx]
      exact hcomm

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311x
