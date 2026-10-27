module

public import CFSG.LargeExtraspecial.A2ModCfgARS
public import CFSG.LargeExtraspecial.A2ModCfg
public import CFSG.Timmesfeld.ARS.Induction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Timmesfeld.ARS CFSG.LieType
  CFSG.LieType.Universal
open CFSG.Timmesfeld (sroot edgeE)

@[expose] def chainE (r : ℕ) (hr : 6 ≤ r) (j : Fin 5) : Fin r :=
  ⟨j.val + min j.val 1, by omega⟩

theorem val_chainE {r : ℕ} (hr : 6 ≤ r) (j : Fin 5) :
    (chainE r hr j).val = j.val + min j.val 1 :=
  rfl

theorem chainE_injective {r : ℕ} (hr : 6 ≤ r) : Function.Injective (chainE r hr) := by
  intro i j h
  have h' := congrArg Fin.val h
  rw [val_chainE, val_chainE] at h'
  ext
  omega

theorem edgeA_iff_edgeE_chainE {r : ℕ} (hr : 6 ≤ r) (i j : Fin 5) :
    CFSG.Timmesfeld.ARS.edgeA 5 i j ↔ edgeE r (chainE r hr i) (chainE r hr j) := by
  unfold CFSG.Timmesfeld.ARS.edgeA edgeE
  rw [val_chainE, val_chainE]
  omega

variable {X : Type} [Group X] {R : Set (Subgroup X)} {D : Set X}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem typeE_false_of_isConfig [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {r : ℕ} (hr : 6 ≤ r) {A B : Fin r → Subgroup X}
    (hX : IsConfig R (edgeE r) A B) : False := by
  choose gA hgA hA' using fun j => hRD (A j) (hX.memA j)
  choose gB hgB hB' using fun j => hRD (B j) (hX.memB j)
  have hchain := isConfig_comp hX (chainE_injective hr) (edgeA_iff_edgeE_chainE hr)
  obtain ⟨Ψ, hΨA, hΨB⟩ :=
    exists_levi_zmodTwo hR hiso (card_eq_two_of_forall_eq_zpowers hR hRD) (by norm_num) hchain
  have hvA : ∀ p : Fin 5, Ψ (elemTv p.castSucc p.succ) = gA (chainE r hr p) := fun p =>
    map_elemTv_castSucc_succ Ψ p (mul_self_and_ne_one_of_mem hR (hX.memA _) (hA' _)).2
      ((hΨA p).trans (hA' _))
  have hvB : ∀ p : Fin 5, Ψ (elemTv p.succ p.castSucc) = gB (chainE r hr p) := fun p =>
    map_elemTv_succ_castSucc Ψ p (mul_self_and_ne_one_of_mem hR (hX.memB _) (hB' _)).2
      ((hΨB p).trans (hB' _))
  obtain ⟨n₁, hn₁⟩ : ∃ n : Fin r, n.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨n₃, hn₃⟩ : ∃ n : Fin r, n.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  have he₁₃ : edgeE r n₁ n₃ := Or.inr (Or.inl ⟨hn₁, hn₃⟩)
  have h₂ : chainE r hr 2 = n₃ := Fin.ext (by rw [val_chainE, hn₃]; decide)
  have hcomm : ∀ i j : Fin (5 + 1), j.val + 1 = i.val → Commute (gA n₁) (Ψ (elemTv i j)) := by
    intro i j hij
    obtain ⟨p, rfl, rfl⟩ : ∃ p : Fin 5, p.succ = i ∧ p.castSucc = j :=
      ⟨⟨j.val, by omega⟩, Fin.ext (by simp; omega), Fin.ext rfl⟩
    rw [hvB]
    by_cases hp : p.val = 2
    · obtain rfl : p = 2 := Fin.ext hp
      rw [h₂]
      obtain ⟨-, -, -, c, -⟩ := hX.edge _ _ he₁₃
      exact c _ (mem_of_eq_zpowers (hA' _)) _ (mem_of_eq_zpowers (hB' _))
    · have hne : n₁ ≠ chainE r hr p := fun h => by
        have := congrArg Fin.val h
        rw [hn₁, val_chainE] at this
        omega
      have h1 : ¬ edgeE r n₁ (chainE r hr p) := by
        unfold edgeE
        rw [hn₁, val_chainE]
        omega
      have h2 : ¬ edgeE r (chainE r hr p) n₁ := by
        unfold edgeE
        rw [hn₁, val_chainE]
        omega
      exact (hX.nonadj _ _ hne h1 h2).2.1 _ (mem_of_eq_zpowers (hA' _)) _
        (mem_of_eq_zpowers (hB' _))
  have hcoll : gA n₁ * Ψ (elemTv (2 : Fin 5).succ (2 : Fin 5).castSucc) ∈ D := by
    rw [hvB, h₂]
    exact (mul_mem_of_isConfig_adj hR hiso hX (isRootedTree_E (by omega)) hDc he₁₃ (hA' _)
      (hB' _) (hA' _) (hB' _) (hgA _) (hgB _) (hgB _)).2.2
  have hΨ := map_mem_of_elemTv_mem hDc Ψ (Fin.castSucc_lt_succ (i := (0 : Fin 5))).ne
    (by rw [hvA]; exact hgA _)
  exact false_of_node hA hΨ (hgA n₁) hcomm (by simp) (by simp) (by simp) hcoll

theorem typeE_false [Finite X] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {r : ℕ} (hr : r = 6 ∨ r = 7 ∨ r = 8) (hX : HasGenConfig R (edgeE r)) :
    False := by
  obtain ⟨A, B, hX, -⟩ := hX
  exact typeE_false_of_isConfig hR hiso hRD hDc hA (by omega) hX

end CFSG.LargeExtraspecial.A2Mod
