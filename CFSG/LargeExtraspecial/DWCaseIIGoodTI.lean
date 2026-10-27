module

public import CFSG.LargeExtraspecial.DWTransConj
public import CFSG.LargeExtraspecial.DWTransFaith
public import CFSG.GroupTheory.CommutantOfInvolution

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

private theorem conjSub_mul (g k : G) :
    conjSub A (g * k) = conjSub (conjSub A k) g := by
  ext b
  simp only [mem_conjSub]
  have e : (g * k)⁻¹ * b * (g * k) = k⁻¹ * (g⁻¹ * b * g) * k := by group
  rw [e]

theorem conjSub_eq_self_of_good (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hconj : ∀ a ∈ A, a ≠ 1 → ∃ g : G, g * S.z * g⁻¹ = a)
    (hgood : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) {g : G}
    (hg : g * S.z * g⁻¹ ∈ A) : conjSub A g = A := by
  have hle : A ≤ conjSub A g := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem (conjSub A g)
    · obtain ⟨k, hk⟩ := hconj a ha ha1
      have haQ : a ∈ S.Qa g := hgood g hg ha
      have hqQ : g⁻¹ * a * g ∈ S.QG := by
        rw [S.Qa_eq_map] at haQ
        obtain ⟨q, hq, hqa⟩ := Subgroup.mem_map.mp haQ
        have hqa' : g * q * g⁻¹ = a := by simpa [MulAut.conj_apply] using hqa
        rw [← hqa']
        simpa [mul_assoc] using hq
      have hQ : (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ ∈ S.QG := by
        rw [show (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ = g⁻¹ * a * g by rw [← hk]; group]
        exact hqQ
      rw [mem_conjSub,
        show g⁻¹ * a * g = (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ by rw [← hk]; group]
      exact hII (g⁻¹ * k) hQ
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hcard : Nat.card (conjSub A g) = Nat.card A := by
    rw [conjSub]
    exact Subgroup.card_map_of_injective
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  simpa [hcard]

theorem conjSub_eq_or_inf_eq_bot (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hconj : ∀ a ∈ A, a ≠ 1 → ∃ g : G, g * S.z * g⁻¹ = a)
    (hgood : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) (g : G) :
    conjSub A g = A ∨ A ⊓ conjSub A g = ⊥ := by
  by_cases h : A ⊓ conjSub A g = ⊥
  · exact Or.inr h
  · left
    obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    have hcA : (c : G) ∈ A := c.2.1
    have hcB : (c : G) ∈ conjSub A g := c.2.2
    have hgcA : g⁻¹ * (c : G) * g ∈ A := mem_conjSub.mp hcB
    have hgc1 : g⁻¹ * (c : G) * g ≠ 1 := by
      intro e
      apply hc1
      apply Subtype.ext
      exact (by simpa [mul_assoc] using congrArg (fun x => g * x * g⁻¹) e)
    obtain ⟨k, hk⟩ := hconj (g⁻¹ * (c : G) * g) hgcA hgc1
    have hkA : k * S.z * k⁻¹ ∈ A := by rw [hk]; exact hgcA
    have hkB : conjSub A k = A := conjSub_eq_self_of_good hA hM hII hconj hgood hkA
    have hgk_mem : (g * k) * S.z * (g * k)⁻¹ ∈ A := by
      rw [show (g * k) * S.z * (g * k)⁻¹ = g * (k * S.z * k⁻¹) * g⁻¹ by group, hk]
      simpa [mul_assoc] using hcA
    have hgk : conjSub A (g * k) = A :=
      conjSub_eq_self_of_good hA hM hII hconj hgood hgk_mem
    have hgk' : conjSub (conjSub A k) g = A := by
      rw [← conjSub_mul (A := A) g k]
      exact hgk
    rwa [hkB] at hgk'

theorem centralizer_conjSub_eq (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) (h : G) :
    centralizer (conjSub A h : Set G) = conjSub A h := by
  refine le_antisymm (fun g hg => mem_conjSub.mpr ?_) (fun b hb => ?_)
  · have hmem : h⁻¹ * g * h ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have hb : h * a * h⁻¹ ∈ conjSub A h := conj_mem_conjSub ha
      have hga := (mem_centralizer_iff.mp hg) (h * a * h⁻¹) hb
      have := congrArg (fun x => h⁻¹ * x * h) hga
      simpa [mul_assoc] using this
    rwa [hA.centralizer_eq hM] at hmem
  · rw [mem_centralizer_iff]
    intro a ha
    exact (comm_of_mem hb ha).symm

theorem conjSub_inf_QG_eq_bot (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hconj : ∀ a ∈ A, a ≠ 1 → ∃ g : G, g * S.z * g⁻¹ = a)
    (hgood : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) {h : G}
    (hyQ : h * S.z * h⁻¹ ∉ S.QG) : conjSub A h ⊓ S.QG = ⊥ := by
  have hyB : h * S.z * h⁻¹ ∈ conjSub A h := conj_mem_conjSub hA.z_mem
  have hyA : h * S.z * h⁻¹ ∉ A := fun hy => hyQ (hA.le_QG hy)
  have hne : conjSub A h ≠ A := fun e => hyA (e ▸ hyB)
  have hdisj : A ⊓ conjSub A h = ⊥ :=
    (conjSub_eq_or_inf_eq_bot hA hM hII hconj hgood h).resolve_left hne
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  by_contra hb1
  have hbB : b ∈ conjSub A h := hb.1
  have hbQ : b ∈ S.QG := hb.2
  have hhbA : h⁻¹ * b * h ∈ A := mem_conjSub.mp hbB
  have hhb1 : h⁻¹ * b * h ≠ 1 := by
    intro e
    apply hb1
    have := congrArg (fun x => h * x * h⁻¹) e
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hconj (h⁻¹ * b * h) hhbA hhb1
  have hbA : b ∈ A := by
    have hQ : (h * k) * S.z * (h * k)⁻¹ ∈ S.QG := by
      rw [show (h * k) * S.z * (h * k)⁻¹ = h * (k * S.z * k⁻¹) * h⁻¹ by group, hk]
      simpa [mul_assoc] using hbQ
    have := hII (h * k) hQ
    rwa [show (h * k) * S.z * (h * k)⁻¹ = b by rw [show (h * k) * S.z * (h * k)⁻¹
      = h * (k * S.z * k⁻¹) * h⁻¹ by group, hk]; group] at this
  have hmem : b ∈ A ⊓ conjSub A h := ⟨hbA, hbB⟩
  rw [hdisj] at hmem
  exact hb1 (Subgroup.mem_bot.mp hmem)

theorem commute_and_mul_self_of_mem_QG_inf_centralizer
    (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
    (hconj : ∀ a ∈ A, a ≠ 1 → ∃ g : G, g * S.z * g⁻¹ = a)
    (hgood : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) {h : G}
    (hyM : h * S.z * h⁻¹ ∈ S.M) (hyQ : h * S.z * h⁻¹ ∉ S.QG) :
    (∀ k ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G),
      ∀ k' ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G), k * k' = k' * k) ∧
    ∀ k ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G), k * k = 1 := by
  have hBcomm : ∀ a ∈ conjSub A h, ∀ b ∈ conjSub A h, a * b = b * a :=
    fun a ha b hb => comm_of_mem (A := conjSub A h) ha hb
  have hB2 : ∀ b ∈ conjSub A h, b * b = 1 :=
    fun b hb => mul_self_of_mem (A := conjSub A h) hb
  have hτB : ∀ b ∈ conjSub A h, S.z * b * S.z⁻¹ ∈ conjSub A h := by
    intro b hb
    have hzM : S.z ∈ (S.conjBy h).M := by
      rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
      exact (S.z_comm hyM).symm
    exact (mem_normalizer_iff.mp (conjBy_M_le_normalizer hM h hzM) b).mp hb
  have hKB : ∀ k ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G),
      ∀ b ∈ conjSub A h, k * b * k⁻¹ ∈ conjSub A h := by
    intro k hk b hb
    have hkM : k ∈ (S.conjBy h).M := by
      rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
      exact mem_centralizer_singleton_iff.mp hk.2
    exact (mem_normalizer_iff.mp (conjBy_M_le_normalizer hM h hkM) b).mp hb
  have hKτ : ∀ k ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G), k * S.z = S.z * k :=
    fun k hk => S.z_comm_QG hk.1
  have hKU : ∀ k ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G),
      ∀ b ∈ conjSub A h, b * S.z = S.z * b → k * b = b * k := by
    intro k hk b hb hbz
    have hbM : b ∈ S.M := S.mem_M_iff.mpr hbz
    have hcommB : k * b * k⁻¹ * b⁻¹ ∈ conjSub A h :=
      (conjSub A h).mul_mem (hKB k hk b hb) ((conjSub A h).inv_mem hb)
    have hcommQ : k * b * k⁻¹ * b⁻¹ ∈ S.QG := by
      have h1 : b * k⁻¹ * b⁻¹ ∈ S.QG := S.conj_mem_QG hbM (S.QG.inv_mem hk.1)
      have h2 : k * (b * k⁻¹ * b⁻¹) ∈ S.QG := S.QG.mul_mem hk.1 h1
      simpa [mul_assoc] using h2
    have hbot : k * b * k⁻¹ * b⁻¹ ∈ conjSub A h ⊓ S.QG := ⟨hcommB, hcommQ⟩
    rw [conjSub_inf_QG_eq_bot hA hM hII hconj hgood hyQ] at hbot
    have h1 : k * b * k⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have h2 : k * b * k⁻¹ = b := mul_inv_eq_one.mp h1
    calc k * b = (k * b * k⁻¹) * k := by group
      _ = b * k := by rw [h2]
  have hKfaith : ∀ k ∈ S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G),
      (∀ b ∈ conjSub A h, k * b = b * k) → k = 1 := by
    intro k hk hcent
    have hkcent : k ∈ centralizer (conjSub A h : Set G) :=
      mem_centralizer_iff.mpr fun b hb => (hcent b hb).symm
    have hkB : k ∈ conjSub A h := by
      rwa [centralizer_conjSub_eq hA hM h] at hkcent
    have hbot : k ∈ conjSub A h ⊓ S.QG := ⟨hkB, hk.1⟩
    rw [conjSub_inf_QG_eq_bot hA hM hII hconj hgood hyQ] at hbot
    exact Subgroup.mem_bot.mp hbot
  exact CFSG.GroupTheory.commute_and_mul_self_of_commute_involution
    hBcomm hB2 S.z_mul_z hτB hKB hKτ hKU hKfaith

end MaxEA

end CFSG.LargeExtraspecial.DW
