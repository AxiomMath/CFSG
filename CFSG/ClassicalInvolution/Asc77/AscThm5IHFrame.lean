module

public import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHRed

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Prod

variable {Y : Type} [Group Y] [Finite Y]

structure CentralizerProd (R₀ : Subgroup Y) (f : Y) (A B : Subgroup Y) : Prop where
  A_le : A ≤ R₀ ⊓ Subgroup.centralizer ({f} : Set Y)
  B_le : B ≤ R₀ ⊓ Subgroup.centralizer ({f} : Set Y)
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  A_odd : ∀ M : Subgroup Y, M ≤ A → (∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M) → Odd (Nat.card M) →
    M = ⊥
  B_odd : ∀ M : Subgroup Y, M ≤ B → (∀ b ∈ B, ∀ m ∈ M, b * m * b⁻¹ ∈ M) → Odd (Nat.card M) →
    M = ⊥
  center_odd : ∀ a ∈ A, ∀ b ∈ B, (∀ a' ∈ A, a * a' = a' * a) → (∀ b' ∈ B, b * b' = b' * b) →
    Odd (orderOf (a * b)) → a * b = 1
  sq_mem : ∀ g ∈ R₀ ⊓ Subgroup.centralizer ({f} : Set Y), g * g ∈ A ⊔ B

theorem thm5IH_oddCore_centralizes_of_prod {R₀ : Subgroup Y} (hR₀ : R₀.Normal) {f : Y}
    {A B : Subgroup Y} (h : CentralizerProd R₀ f A B) {d : Y} (hd : d ∈ involutionOddCore f)
    {g : Y} (hg : g ∈ R₀ ⊓ Subgroup.centralizer ({f} : Set Y)) : d * g = g * d := by
  classical
  set O : Subgroup Y := involutionOddCore f with hO
  set N : Subgroup Y := O ⊓ R₀ with hN
  have hNodd : Odd (Nat.card N) :=
    (CFSG.Assembly.Dichotomy.odd_card_involutionOddCore f).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hNnorm : ∀ c ∈ R₀ ⊓ Subgroup.centralizer ({f} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    exact ⟨conj_mem_involutionOddCore hc.2 hn.1, hR₀.conj_mem n hn.2 c⟩
  have hNle : ∀ n ∈ N, n ∈ R₀ ⊓ Subgroup.centralizer ({f} : Set Y) := fun n hn =>
    ⟨hn.2, CFSG.ClassicalInvolution.Balance.involutionOddCore_le_centralizer f hn.1⟩
  have hN1 : ∀ n ∈ N, n = 1 := by
    intro n hn
    have hodd : Odd (orderOf n) := hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
    obtain ⟨m, hm⟩ := hodd
    have hnm : n = (n * n) ^ (m + 1) := by
      have h1 : n ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one n
      calc n = n ^ (2 * m + 1) * n := by rw [h1, one_mul]
        _ = n ^ (2 * (m + 1)) := by rw [← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
        _ = (n * n) ^ (m + 1) := by rw [pow_mul, pow_two]
    have hnP : n ∈ A ⊔ B := by
      rw [hnm]
      exact (A ⊔ B).pow_mem (h.sq_mem n (hNle n hn)) _
    obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes h.comm hnP
    subst hab
    have hacomm : ∀ b' ∈ B, a * b' = b' * a := fun b' hb' => h.comm a ha b' hb'
    have hbcomm : ∀ a' ∈ A, b * a' = a' * b := fun a' ha' => (h.comm a' ha' b hb).symm
    have hMA : (A ⊓ N) = ⊥ := by
      refine h.A_odd (A ⊓ N) inf_le_left (fun a' ha' m hm' => ⟨A.mul_mem (A.mul_mem ha' hm'.1)
        (A.inv_mem ha'), hNnorm a' (h.A_le ha') m hm'.2⟩) ?_
      exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hMB : (B ⊓ N) = ⊥ := by
      refine h.B_odd (B ⊓ N) inf_le_left (fun b' hb' m hm' => ⟨B.mul_mem (B.mul_mem hb' hm'.1)
        (B.inv_mem hb'), hNnorm b' (h.B_le hb') m hm'.2⟩) ?_
      exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hnA : ∀ a' ∈ A, a * b * a' = a' * (a * b) := by
      intro a' ha'
      have h1 : (a * b) * a' * (a * b)⁻¹ * a'⁻¹ ∈ A ⊓ N := by
        refine ⟨?_, ?_⟩
        · have e : (a * b) * a' * (a * b)⁻¹ * a'⁻¹ = (a * a' * a⁻¹) * a'⁻¹ := by
            calc (a * b) * a' * (a * b)⁻¹ * a'⁻¹ = a * (b * a') * b⁻¹ * a⁻¹ * a'⁻¹ := by group
              _ = a * (a' * b) * b⁻¹ * a⁻¹ * a'⁻¹ := by rw [hbcomm a' ha']
              _ = (a * a' * a⁻¹) * a'⁻¹ := by group
          rw [e]
          exact A.mul_mem (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (A.inv_mem ha')
        · have e : (a * b) * a' * (a * b)⁻¹ * a'⁻¹ = (a * b) * (a' * (a * b)⁻¹ * a'⁻¹) := by group
          rw [e]
          exact N.mul_mem hn (hNnorm a' (h.A_le ha') _ (N.inv_mem hn))
      rw [hMA, Subgroup.mem_bot] at h1
      have h2 : (a * b) * a' * (a * b)⁻¹ = a' := mul_inv_eq_one.mp h1
      exact mul_inv_eq_iff_eq_mul.mp h2
    have hnB : ∀ b' ∈ B, a * b * b' = b' * (a * b) := by
      intro b' hb'
      have h1 : (a * b) * b' * (a * b)⁻¹ * b'⁻¹ ∈ B ⊓ N := by
        refine ⟨?_, ?_⟩
        · have e : (a * b) * b' * (a * b)⁻¹ * b'⁻¹ = (b * b' * b⁻¹) * b'⁻¹ := by
            calc (a * b) * b' * (a * b)⁻¹ * b'⁻¹ = a * (b * b' * b⁻¹) * a⁻¹ * b'⁻¹ := by group
              _ = (b * b' * b⁻¹) * a * a⁻¹ * b'⁻¹ := by
                  rw [h.comm a ha (b * b' * b⁻¹) (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb))]
              _ = (b * b' * b⁻¹) * b'⁻¹ := by group
          rw [e]
          exact B.mul_mem (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)) (B.inv_mem hb')
        · have e : (a * b) * b' * (a * b)⁻¹ * b'⁻¹ = (a * b) * (b' * (a * b)⁻¹ * b'⁻¹) := by group
          rw [e]
          exact N.mul_mem hn (hNnorm b' (h.B_le hb') _ (N.inv_mem hn))
      rw [hMB, Subgroup.mem_bot] at h1
      have h2 : (a * b) * b' * (a * b)⁻¹ = b' := mul_inv_eq_one.mp h1
      exact mul_inv_eq_iff_eq_mul.mp h2
    refine h.center_odd a ha b hb (fun a' ha' => ?_) (fun b' hb' => ?_) ⟨m, hm⟩
    · have h3 : (a * a') * b = (a' * a) * b := by
        calc (a * a') * b = a * (a' * b) := by group
          _ = a * (b * a') := by rw [hbcomm a' ha']
          _ = a * b * a' := by group
          _ = a' * (a * b) := hnA a' ha'
          _ = (a' * a) * b := by group
      exact mul_right_cancel h3
    · have h3 : a * (b * b') = a * (b' * b) := by
        calc a * (b * b') = a * b * b' := by group
          _ = b' * (a * b) := hnB b' hb'
          _ = (b' * a) * b := by group
          _ = (a * b') * b := by rw [← hacomm b' hb']
          _ = a * (b' * b) := by group
      exact mul_left_cancel h3
  have hdg : d * g * d⁻¹ * g⁻¹ ∈ N := by
    refine ⟨?_, ?_⟩
    · have e : d * g * d⁻¹ * g⁻¹ = d * (g * d⁻¹ * g⁻¹) := by group
      rw [e]
      exact O.mul_mem hd (conj_mem_involutionOddCore hg.2 (O.inv_mem hd))
    · exact R₀.mul_mem (hR₀.conj_mem g hg.1 d) (R₀.inv_mem hg.1)
  have h1 := hN1 _ hdg
  have h2 : d * g * d⁻¹ = g := mul_inv_eq_one.mp h1
  exact mul_inv_eq_iff_eq_mul.mp h2


theorem thm5IH_commutator_eq_bot_of_prod {R₀ : Subgroup Y} (hR₀ : R₀.Normal) {F : Subgroup Y}
    (hF2 : ∀ f ∈ F, f * f = 1) (hFR : F ≤ R₀)
    (hprod : ∀ f ∈ F, f ≠ 1 → ∃ A B : Subgroup Y, CentralizerProd R₀ f A B) :
    ∀ a ∈ F, a ≠ 1 → ⁅involutionOddCore a, F⁆ = ⊥ := by
  have hFcomm := thm5IH_comm_of_sq hF2
  intro a ha ha1
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro d hd b hb
  obtain ⟨A, B, h⟩ := hprod a ha ha1
  have hbC : b ∈ R₀ ⊓ Subgroup.centralizer ({a} : Set Y) :=
    ⟨hFR hb, Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm b hb a ha)⟩
  have hdb := thm5IH_oddCore_centralizes_of_prod hR₀ h hd hbC
  rw [Subgroup.mem_bot, commutatorElement_def, hdb]
  group

theorem thm5IH_alphaOf_eq_bot_of_prod {R₀ : Subgroup Y} (hR₀ : R₀.Normal)
    (hcent : ∀ y : Y, (∀ r ∈ R₀, y * r = r * y) → y = 1) {F : Subgroup Y}
    (hF2 : ∀ f ∈ F, f * f = 1) (hFR : F ≤ R₀)
    (hprod : ∀ f ∈ F, f ≠ 1 → ∃ A B : Subgroup Y, CentralizerProd R₀ f A B)
    (hgen : R₀ ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), R₀ ⊓ Subgroup.centralizer ({f} : Set Y)) :
    alphaOf F = ⊥ := by
  rw [alphaOf_eq_bot_iff]
  refine ⟨thm5IH_commutator_eq_bot_of_prod hR₀ hF2 hFR hprod, ?_⟩
  change deltaCore F = ⊥
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  refine hcent d fun r hr => ?_
  have hle : (⨆ f ∈ F, ⨆ (_ : f ≠ 1), R₀ ⊓ Subgroup.centralizer ({f} : Set Y)) ≤
      Subgroup.centralizer ({d} : Set Y) := by
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    intro g hg
    obtain ⟨A, B, h⟩ := hprod f hf hf1
    have hdf : d ∈ involutionOddCore f := mem_deltaCore_iff.mp hd f hf hf1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (thm5IH_oddCore_centralizes_of_prod hR₀ h hdf hg).symm
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen hr))
  exact h1.symm

theorem thm5IH_alphaOf_eq_bot_of_prod_layers {R₀ : Subgroup Y} (hR₀ : R₀.Normal)
    (hcent : ∀ y : Y, (∀ r ∈ R₀, y * r = r * y) → y = 1) {F : Subgroup Y}
    (hF2 : ∀ f ∈ F, f * f = 1) (hFR : F ≤ R₀)
    (hprod : ∀ f ∈ F, f ≠ 1 → ∃ A B : Subgroup Y, CentralizerProd R₀ f A B)
    (hgen : R₀ ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f) : alphaOf F = ⊥ := by
  rw [alphaOf_eq_bot_iff]
  refine ⟨thm5IH_commutator_eq_bot_of_prod hR₀ hF2 hFR hprod, ?_⟩
  change deltaCore F = ⊥
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  refine hcent d fun r hr => ?_
  exact (Subgroup.mem_centralizer_iff.mp (deltaCore_le_centralizer_iSup_centralizerLayer F hd) r
    (hgen hr)).symm

end Prod

end CFSG.ClassicalInvolution.Asc77
