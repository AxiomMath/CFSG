module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneAlt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneSmall

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

abbrev jhatSub {K : Type} [Group K] (α : MulAut K) : Subgroup K :=
  Subgroup.closure {x | x ∈ AhatData.fixSub α ∧ x * x = 1}

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem Sec5S.exists_alt_quot (hS : Sec5S X n z Z S s) (hn12 : 12 ≤ n) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) :
    ∃ (k : ℕ) (Cyc : Type) (_ : Fintype Cyc) (_ : DecidableEq Cyc)
      (π : ↥(hGrp s A) →* Perm Cyc), 5 ≤ k ∧ Fintype.card Cyc = k ∧ 2 * k ≤ n ∧
        n ≤ 2 * k + 3 ∧ alternatingGroup Cyc ≤ π.range := by
  have hn : 8 ≤ n := by omega
  have hsA := hS.norm A hA
  set M : AhatModel X n A := AhatModel.ofCover hA.2 with hM
  have : Finite M.K := inferInstanceAs (Finite (↥A ⧸ pPrimeCore 2 ↥A))
  obtain ⟨hσ2, k, hk4, hk⟩ := hS.exists_k hA M
  obtain ⟨hfix, -⟩ := hS.frac A hA hsA M
  have hadd := fixCount_add_support (M.perm s hsA)
  have hk5 : 5 ≤ k := by omega
  have hkn : 2 * k ≤ n := by omega
  have hnk : n ≤ 2 * k + 3 := by omega
  obtain ⟨Cyc, hF, hD, π, hcard, halt⟩ :=
    exists_act_alt hn M.C (M.induces_perm hn s hsA) hσ2 hk hk5
  have hHA : hGrp s A ≤ A := (hGrp_le s A).trans inf_le_left
  let qH0 : ↥(hGrp s A) →* M.K :=
    M.e.toMonoidHom.comp ((QuotientGroup.mk' (pPrimeCore 2 ↥A)).comp (Subgroup.inclusion hHA))
  have hqH0 : ∀ (x : X) (hx : x ∈ hGrp s A),
      qH0 ⟨x, hx⟩ = M.e (QuotientGroup.mk (⟨x, hHA hx⟩ : ↥A)) := fun x hx => rfl
  have hfixr : ∀ r (hr : r ∈ invsOf s A),
      M.autOf s hsA (M.e (QuotientGroup.mk (⟨r, hr.1⟩ : ↥A))) =
        M.e (QuotientGroup.mk (⟨r, hr.1⟩ : ↥A)) := by
    intro r hr
    have h := M.autOf_mk hsA ⟨r, hr.1⟩
    have e : conjAut hsA ⟨r, hr.1⟩ = ⟨r, hr.1⟩ := Subtype.ext (by
      rw [coe_conjAut]
      show s * r * s⁻¹ = r
      have h1 : s * r = r * s := hr.2.2.2.symm
      rw [h1]; group)
    rw [e] at h
    exact h
  have key : ∀ x : X, x ∈ hGrp s A →
      ∃ hx : x ∈ hGrp s A, qH0 ⟨x, hx⟩ ∈ jhatSub (M.autOf s hsA) := by
    intro x hx
    have hx' : x ∈ Subgroup.closure (invsOf s A) := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem r hr =>
      refine ⟨subset_hGrp hr, Subgroup.subset_closure ⟨hfixr r hr, ?_⟩⟩
      rw [hqH0, ← map_mul, ← QuotientGroup.mk_mul]
      have : (⟨r, hr.1⟩ : ↥A) * ⟨r, hr.1⟩ = 1 := Subtype.ext hr.2.2.1
      rw [this]
      simp
    | one =>
      refine ⟨one_mem _, ?_⟩
      have h1 : qH0 ⟨1, one_mem _⟩ = 1 := map_one qH0
      rw [h1]
      exact (jhatSub (M.autOf s hsA)).one_mem
    | mul a b _ _ ha hb =>
      obtain ⟨haH, ha'⟩ := ha
      obtain ⟨hbH, hb'⟩ := hb
      refine ⟨mul_mem haH hbH, ?_⟩
      have : qH0 ⟨a * b, mul_mem haH hbH⟩ = qH0 ⟨a, haH⟩ * qH0 ⟨b, hbH⟩ :=
        map_mul qH0 ⟨a, haH⟩ ⟨b, hbH⟩
      rw [this]
      exact (jhatSub (M.autOf s hsA)).mul_mem ha' hb'
    | inv a _ ha =>
      obtain ⟨haH, ha'⟩ := ha
      refine ⟨inv_mem haH, ?_⟩
      have : qH0 ⟨a⁻¹, inv_mem haH⟩ = (qH0 ⟨a, haH⟩)⁻¹ := map_inv qH0 ⟨a, haH⟩
      rw [this]
      exact (jhatSub (M.autOf s hsA)).inv_mem ha'
  have hmemq : ∀ x : ↥(hGrp s A), qH0 x ∈ jhatSub (M.autOf s hsA) := fun x => (key x.1 x.2).2
  let qJ : ↥(hGrp s A) →* ↥(jhatSub (M.autOf s hsA)) :=
    qH0.codRestrict (jhatSub (M.autOf s hsA)) hmemq
  have hsurj : ∀ y : M.K, y ∈ jhatSub (M.autOf s hsA) → ∃ x : ↥(hGrp s A), qH0 x = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      by_cases hx1 : x = 1
      · exact ⟨1, by rw [hx1]; exact map_one _⟩
      · obtain ⟨r, hr, hrA, hrx⟩ :=
          exists_inv_lift hA.2 hsA hS.inv.sq (AhatData.mem_fixSub.1 hx.1) hx.2 hx1
        exact ⟨⟨r, subset_hGrp hr⟩, hrx⟩
    | one => exact ⟨1, map_one _⟩
    | mul a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x * y, by rw [map_mul, hx, hy]⟩
    | inv a _ ha =>
      obtain ⟨x, hx⟩ := ha
      exact ⟨x⁻¹, by rw [map_inv, hx]⟩
  refine ⟨k, Cyc, hF, hD, π.comp qJ, hk5, hcard, hkn, hnk, ?_⟩
  intro a ha
  obtain ⟨j, hj⟩ := halt ha
  obtain ⟨x, hx⟩ := hsurj j.1 j.2
  refine ⟨x, ?_⟩
  have : qJ x = j := Subtype.ext hx
  show π (qJ x) = a
  rw [this]
  exact hj

end CFSG.OddStandard.Solomon75
