module

public import CFSG.GH74.GLS.LU.Local.FiveFacts
public import CFSG.GH74.GLS.LU.Local.FiveUtil

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Gen83

variable {G : Type} [Group G]

omit [Group G] in
theorem odd_mem_of_two_normalizes [Group G] {A T : Subgroup G}
    (hTA : ∀ τ ∈ T, ∀ a ∈ A, τ * a * τ⁻¹ ∈ A) (hT2 : ∀ τ ∈ T, τ * τ = 1) {w : G} (hw : w ∈ A ⊔ T)
    {m : ℕ} (hm : Odd m) (hwm : w ^ m = 1) : w ∈ A := by
  obtain ⟨a, ha, τ, hτ, rfl⟩ := mem_sup_of_normalizes (E := A) (L := T)
    (fun l hl e he => hTA l hl e he) hw
  have hsq : (a * τ) * (a * τ) ∈ A := by
    have e : (a * τ) * (a * τ) = a * (τ * a * τ⁻¹) * (τ * τ) := by group
    rw [e, hT2 τ hτ, mul_one]
    exact mul_mem ha (hTA τ hτ a ha)
  obtain ⟨k, hk⟩ := hm
  have hw' : a * τ = ((a * τ) * (a * τ)) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    have h2 : 2 * (k + 1) = m + 1 := by omega
    rw [h2, pow_succ, hwm, one_mul]
  rw [hw']
  exact pow_mem hsq (k + 1)

theorem card_eq_fixed_mul_inv5 [Finite G] {A B I : Subgroup G} {g : G} (hg2 : g * g = 1)
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h5 : ∀ a ∈ A, a ^ 5 = 1) (hB : ∀ a, a ∈ B ↔ a ∈ A ∧ g * a * g⁻¹ = a)
    (hI : ∀ a, a ∈ I ↔ a ∈ A ∧ g * a * g⁻¹ = a⁻¹) :
    Nat.card ↥A = Nat.card ↥B * Nat.card ↥I := by
  have hBc : ∀ b ∈ B, ∀ i ∈ I, b * i = i * b := fun b hb i hi =>
    hcomm b ((hB b).1 hb).1 i ((hI i).1 hi).1
  have hdisj : B ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxI⟩ := hx
    have h1 := ((hB x).1 hxB).2
    have h2 := ((hI x).1 hxI).2
    have hxx : x = x⁻¹ := h1.symm.trans h2
    have hx5 : x ^ 5 = 1 := h5 x ((hB x).1 hxB).1
    have hsq : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← hxx]
        _ = 1 := mul_inv_cancel x
    have : x = 1 := by
      calc x = x ^ 5 * ((x * x)⁻¹) ^ 2 := by group
        _ = 1 := by rw [hx5, hsq]; simp
    rw [this]; exact Subgroup.one_mem _
  have hsup : B ⊔ I = A := by
    apply le_antisymm
    · exact sup_le (fun b hb => ((hB b).1 hb).1) (fun i hi => ((hI i).1 hi).1)
    · intro a ha
      have ha'A : g * a * g⁻¹ ∈ A := hgA a ha
      have hgg : g * (g * a * g⁻¹) * g⁻¹ = a := by
        calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g⁻¹ * g⁻¹) := by group
          _ = a := by
            have : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hg2, inv_one]
            rw [hg2, this]; group
      have hcom : a * (g * a * g⁻¹) = (g * a * g⁻¹) * a := hcomm a ha _ ha'A
      have hb : (a * (g * a * g⁻¹)) ^ 3 ∈ B := by
        rw [hB]
        refine ⟨pow_mem (mul_mem ha ha'A) 3, ?_⟩
        have e1 : g * (a * (g * a * g⁻¹)) * g⁻¹ = a * (g * a * g⁻¹) := by
          calc g * (a * (g * a * g⁻¹)) * g⁻¹ = (g * a * g⁻¹) * (g * (g * a * g⁻¹) * g⁻¹) := by group
            _ = (g * a * g⁻¹) * a := by rw [hgg]
            _ = a * (g * a * g⁻¹) := hcom.symm
        calc g * (a * (g * a * g⁻¹)) ^ 3 * g⁻¹ = (g * (a * (g * a * g⁻¹)) * g⁻¹) ^ 3 := by
              rw [conj_pow]
          _ = (a * (g * a * g⁻¹)) ^ 3 := by rw [e1]
      have hi : (a * (g * a * g⁻¹)⁻¹) ^ 3 ∈ I := by
        rw [hI]
        refine ⟨pow_mem (mul_mem ha (inv_mem ha'A)) 3, ?_⟩
        have e1 : g * (a * (g * a * g⁻¹)⁻¹) * g⁻¹ = (a * (g * a * g⁻¹)⁻¹)⁻¹ := by
          calc g * (a * (g * a * g⁻¹)⁻¹) * g⁻¹
              = (g * a * g⁻¹) * (g * (g * a * g⁻¹) * g⁻¹)⁻¹ := by group
            _ = (g * a * g⁻¹) * a⁻¹ := by rw [hgg]
            _ = (a * (g * a * g⁻¹)⁻¹)⁻¹ := by group
        calc g * (a * (g * a * g⁻¹)⁻¹) ^ 3 * g⁻¹
            = (g * (a * (g * a * g⁻¹)⁻¹) * g⁻¹) ^ 3 := by rw [conj_pow]
          _ = ((a * (g * a * g⁻¹)⁻¹)⁻¹) ^ 3 := by rw [e1]
          _ = ((a * (g * a * g⁻¹)⁻¹) ^ 3)⁻¹ := by rw [inv_pow]
      have hbc : (a * (g * a * g⁻¹)) * (a * (g * a * g⁻¹)⁻¹) = a * a := by
        calc (a * (g * a * g⁻¹)) * (a * (g * a * g⁻¹)⁻¹)
            = a * ((g * a * g⁻¹) * a) * (g * a * g⁻¹)⁻¹ := by group
          _ = a * (a * (g * a * g⁻¹)) * (g * a * g⁻¹)⁻¹ := by rw [hcom]
          _ = a * a := by group
      have hcb : Commute (a * (g * a * g⁻¹)) (a * (g * a * g⁻¹)⁻¹) :=
        hcomm _ (mul_mem ha ha'A) _ (mul_mem ha (inv_mem ha'A))
      have hcube : a = (a * (g * a * g⁻¹)) ^ 3 * (a * (g * a * g⁻¹)⁻¹) ^ 3 := by
        rw [← hcb.mul_pow, hbc]
        calc a = a ^ 5 * a := by rw [h5 a ha, one_mul]
          _ = a ^ 6 := (pow_succ a 5).symm
          _ = (a * a) ^ 3 := by rw [← pow_two, ← pow_mul]
      rw [hcube]
      exact mul_mem_sup hb hi
  have := card_sup_of_commute_disjoint hBc hdisj
  rwa [hsup] at this

theorem pPrimeCoreOf_cjL (g : G) (K : Subgroup G) :
    pPrimeCoreOf 2 (cjL g K) = cjL g (pPrimeCoreOf 2 K) := by
  show pPrimeCoreOf 2 (K.map (MulAut.conj g).toMonoidHom) =
    (pPrimeCoreOf 2 K).map (MulAut.conj g).toMonoidHom
  unfold pPrimeCoreOf
  let ψ : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap K
  rw [← pPrimeCore_map_iso 2 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem odd_card_pPrimeCoreOf [Finite G] (K : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 K)) := by
  have h := pPrimeCore_coprime_card (p := 2) (G := ↥K)
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
  exact Nat.coprime_two_left.1 h

theorem le_pPrimeCoreOf_of_normal {K N : Subgroup G} (hNK : N ≤ K) (hnorm : (N.subgroupOf K).Normal)
    (hodd : Odd (Nat.card ↥N)) : N ≤ pPrimeCoreOf 2 K := by
  have hcard : Nat.card ↥(N.subgroupOf K) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf K)) := by
    rw [hcard]; exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf K ≤ pPrimeCore 2 ↥K := le_sSup ⟨hnorm, hcop⟩
  rw [pPrimeCoreOf, ← Subgroup.map_subgroupOf_eq_of_le hNK]
  exact Subgroup.map_mono hle

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA y).mp hy.1, (Subgroup.mem_normalizer_iff.mp hB y).mp hy.2⟩
  · intro hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA y).mpr hy.1, (Subgroup.mem_normalizer_iff.mp hB y).mpr hy.2⟩

theorem cjL_centralizer (g : G) (A : Subgroup G) :
    cjL g (centralizer (A : Set G)) = centralizer ((cjL g A : Subgroup G) : Set G) := by
  ext x
  rw [mem_cjL, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    have hb' : g⁻¹ * b * g ∈ A := mem_cjL.mp hb
    have h1 := h _ hb'
    calc b * x = g * ((g⁻¹ * b * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
      _ = x * b := by group
  · intro h a ha
    have h1 := h (g * a * g⁻¹) (mem_cjL_self ha)
    calc a * (g⁻¹ * x * g) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * a := by group

omit [Group G] in
theorem pPrimeCoreOf_le' [Group G] (K : Subgroup G) : pPrimeCoreOf 2 K ≤ K :=
  Subgroup.map_subtype_le _

theorem pow_card_eq_one_of_mem [Finite G] {K : Subgroup G} {w : G} (hw : w ∈ K) :
    w ^ Nat.card ↥K = 1 :=
  congrArg Subtype.val (pow_card_eq_one' (G := ↥K) (x := ⟨w, hw⟩))

end Gen83

end CFSG.GH74.GLS.LU.Local.Five
