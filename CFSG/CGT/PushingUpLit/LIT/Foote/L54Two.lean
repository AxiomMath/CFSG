module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L55Group
public import CFSG.CGT.PushingUpLit.LIT.Foote.L53C
public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Basic

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fourGroup_pair {B : Subgroup G} (hB : QBlock B) {y : G} (hy : y * y = 1)
    (hcomm : B = rightConjugate B y ∨ ∀ a ∈ B, ∀ b ∈ rightConjugate B y, a * b = b * a) :
    ∃ E : Subgroup G, (∀ e ∈ E, ∃ a ∈ blockU B, ∃ b ∈ blockU (rightConjugate B y), e = a * b) ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 4 ∧ ∀ e ∈ E, e * y = y * e := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hBy : QBlock (rightConjugate B y) := hB.conj y
  have hU₂ : blockU (rightConjugate B y) = rightConjugate (blockU B) y := blockU_rightConjugate B y
  have hcommUU : ∀ a ∈ blockU B, ∀ b ∈ blockU (rightConjugate B y), a * b = b * a := by
    intro a ha b hb
    rcases hcomm with h | h
    · have hb' : b ∈ blockU B := by rw [h]; exact hb
      exact hB.blockU_comm a ha b hb'
    · exact h a (blockU_le B ha) b (blockU_le _ hb)
  set V := blockU B ⊔ blockU (rightConjugate B y) with hV
  have hVel : CFSG.Open.IsElemAbelian 2 V :=
    L54.isElemAbelian_sup hB.isElemAbelian_blockU hBy.isElemAbelian_blockU hcommUU
  have htV : ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcommUU).1 hv
    have h1 : y * a * y⁻¹ ∈ blockU (rightConjugate B y) := by
      rw [hU₂, mem_rightConjugate_iff]
      have e : y * (y * a * y⁻¹) * y⁻¹ = a := by
        rw [hyi]
        calc y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = a := by rw [hy]; group
      rw [e]
      exact ha
    have h2 : y * b * y⁻¹ ∈ blockU B := by
      rw [hU₂, mem_rightConjugate_iff] at hb
      exact hb
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e]
    exact V.mul_mem (le_sup_right (a := blockU B) h1) (le_sup_left (b := blockU _) h2)
  have hcard : 8 ≤ Nat.card V := hB.eight_le_card_blockU.trans (Subgroup.card_le_of_le le_sup_left)
  obtain ⟨E, hEV, hEel, hE4, hEy⟩ := exists_fourGroup_centralizer hVel hy htV hcard
  exact ⟨E, fun e he => by simpa using (mem_sup_iff_of_commute hcommUU).1 (hEV he), hEel, hE4, hEy⟩

@[expose] def Good (M J : Subgroup G) (g : G) (T : Subgroup G) : Prop :=
  IsPGroup 2 T ∧ T ≤ rightConjugate J g ⊓ M ∧
    ∃ b ∈ M, ∀ s ∈ T, rightConjugate J s ≠ rightConjugate J b

@[expose] def MaxGood (M J : Subgroup G) (g : G) (T : Subgroup G) : Prop :=
  Good M J g T ∧ ∀ T' : Subgroup G, Good M J g T' → Nat.card T' ≤ Nat.card T

theorem exists_maxGood {M J : Subgroup G} {g : G} (h : ∃ T, Good M J g T) :
    ∃ T, MaxGood M J g T := by
  obtain ⟨T₀, hT₀⟩ := h
  obtain ⟨T, hT, hmax⟩ := Set.exists_max_image {T : Subgroup G | Good M J g T}
    (fun T => Nat.card T) (Set.toFinite _) ⟨T₀, hT₀⟩
  exact ⟨T, hT, fun T' hT' => hmax T' hT'⟩

@[expose] def Lgen (J T : Subgroup G) : Subgroup G := ⨆ s ∈ T, rightConjugate J s

omit [Finite G] in
theorem rightConjugate_le_Lgen {J T : Subgroup G} {s : G} (hs : s ∈ T) :
    rightConjugate J s ≤ Lgen J T := by
  unfold Lgen
  exact le_iSup₂ (f := fun s (_ : s ∈ T) => rightConjugate J s) s hs

omit [Finite G] in
theorem le_Lgen (J T : Subgroup G) : J ≤ Lgen J T := by
  have := rightConjugate_le_Lgen (J := J) (T := T) T.one_mem
  rwa [rightConjugate_one] at this

omit [Finite G] in
theorem le_normalizer_Lgen (J T : Subgroup G) : T ≤ Subgroup.normalizer (Lgen J T : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ Lgen J T, t * x * t⁻¹ ∈ Lgen J T := by
    intro t ht x hx
    have hle : Lgen J T ≤ (Lgen J T).comap (MulAut.conj t).toMonoidHom := by
      unfold Lgen
      refine iSup₂_le fun s hs y hy => ?_
      show t * y * t⁻¹ ∈ Lgen J T
      have hst : s * t⁻¹ ∈ T := T.mul_mem hs (T.inv_mem ht)
      refine rightConjugate_le_Lgen hst ?_
      rw [mem_rightConjugate_iff]
      have e : s * t⁻¹ * (t * y * t⁻¹) * (s * t⁻¹)⁻¹ = s * y * s⁻¹ := by group
      rw [e]
      exact (mem_rightConjugate_iff _ _ _).1 hy
    exact hle hx
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key t ht x hx, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_blockU_conj {K : Subgroup G} {y v : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hv : v ∈ blockU K) : y * v * y⁻¹ ∈ blockU K := by
  have h1 : blockU (rightConjugate K y) = rightConjugate (blockU K) y := blockU_rightConjugate K y
  rw [(rightConjugate_eq_self_iff K y).2 hy] at h1
  rw [h1] at hv
  exact (mem_rightConjugate_iff _ _ _).1 hv

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem Lgen_comm {T : Subgroup G} (hTM : T ≤ M) {b : G} (hb : b ∈ M)
    (hnd : ∀ s ∈ T, rightConjugate J s ≠ rightConjugate J b) :
    ∀ x ∈ Lgen J T, ∀ y ∈ rightConjugate J b, x * y = y * x := by
  have hle : Lgen J T ≤ Subgroup.centralizer ((rightConjugate J b : Subgroup G) : Set G) := by
    unfold Lgen
    refine iSup₂_le fun s hs x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (c.comm_conj (hTM hs) hb (hnd s hs) hx hy).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem Lgen_le_normalizer {T : Subgroup G} (hTM : T ≤ M) :
    Lgen J T ≤ Subgroup.normalizer (J : Set G) := by
  unfold Lgen
  refine iSup₂_le fun s hs x hx => ?_
  by_cases hJ : rightConjugate J s = J
  · rw [hJ] at hx
    exact Subgroup.le_normalizer hx
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact c.comm_J (hTM hs) hJ hy hx

theorem exists_two_noncentral (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀)
    {g : G} (hg : g ∉ M) {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTJ : T ≤ rightConjugate J g)
    (hTM : T ≤ M) (hT0 : T ≠ ⊥) {b : G} (hb : b ∈ M)
    (hnd : ∀ s ∈ T, rightConjugate J s ≠ rightConjugate J b) :
    (∃ a ∈ J, a * a = 1 ∧ a ∈ rightConjugate M g ∧ ∃ k ∈ J, a * k ≠ k * a) ∧
    (∃ a' ∈ rightConjugate J g, a' * a' = 1 ∧ a' ∈ M ∧
      ∃ k ∈ rightConjugate J g, a' * k ≠ k * a') := by
  obtain ⟨t₁, ht₁T, ht₁1, ht₁2⟩ := L54.exists_involution_of_isPGroup hT2 hT0
  have ht₁M : t₁ ∈ M := hTM ht₁T
  have ht₁J : t₁ ∈ rightConjugate J g := hTJ ht₁T
  have ht₁2' : ∃ n : ℕ, t₁ ^ 2 ^ n = 1 := twoElem_of_mul_self ht₁2
  obtain ⟨F, hFV, hFel, hF4, hFt⟩ := exists_fourGroup_pair c.block ht₁2 (by
    by_cases h : rightConjugate J t₁ = J
    · exact Or.inl h.symm
    · exact Or.inr fun a ha b hb' => c.comm_J ht₁M h ha hb')
  have hne1 : rightConjugate J b ≠ J := by
    have := hnd 1 T.one_mem
    rw [rightConjugate_one] at this
    exact fun h => this h.symm
  have hne2 : rightConjugate J t₁ ≠ rightConjugate J b := hnd t₁ ht₁T
  have hFg : F ≤ rightConjugate M g := fun e he =>
    c.centralizer_le_conj ht₁J ht₁2' ht₁1 (Subgroup.mem_centralizer_singleton_iff.2 (hFt e he))
  have hFC : ∀ w ∈ F, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ M := by
    intro w hw hw1
    obtain ⟨a', ha', b', hb', rfl⟩ := hFV w hw
    refine c.centralizer_le_of_centralizes hw1 (twoElem_of_mul_self (by
      have := hFel.2 _ hw
      simpa [pow_two] using this)) hb ?_
    intro y hy
    have h1 : a' * y = y * a' := c.comm_J hb hne1 (blockU_le J ha') hy
    have h2 : b' * y = y * b' := c.comm_conj ht₁M hb hne2 (blockU_le _ hb') hy
    calc y * (a' * b') = (y * a') * b' := by group
      _ = (a' * y) * b' := by rw [h1]
      _ = a' * (y * b') := by group
      _ = a' * (b' * y) := by rw [h2]
      _ = a' * b' * y := by group
  have hFN : F ≤ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) :=
    c.fourGroup_normalizes_g hA hz₀ hg hFg hFel hF4 hFC
  obtain ⟨w₁, hw₁, -, -, hw₁1, -, -⟩ := exists_two_ne_one (W := F) (by omega)
  have hw₁2 : w₁ * w₁ = 1 := by simpa [pow_two] using hFel.2 w₁ hw₁
  have hBg : QBlock (rightConjugate J g) := c.block.conj g
  have hw₁C : Subgroup.centralizer ({w₁} : Set G) ≤ M := hFC w₁ hw₁ hw₁1
  obtain ⟨E, hEV, hEel, hE4, hEw⟩ := exists_fourGroup_centralizer hBg.isElemAbelian_blockU hw₁2
    (fun v hv => mem_blockU_conj (hFN hw₁) hv) hBg.eight_le_card_blockU
  have hEM : E ≤ M := fun e he => hw₁C (Subgroup.mem_centralizer_singleton_iff.2 (hEw e he))
  have hEJ : E ≤ rightConjugate J g := fun e he => blockU_le _ (hEV he)
  have hEN : E ≤ Subgroup.normalizer (J : Set G) :=
    c.normalizes_of_le_conj hA hz₀ hg (le_inf hEJ hEM) hEel hE4
  obtain ⟨u, hu, -, -, hu1, -, -⟩ := exists_two_ne_one (W := E) (by omega)
  have hu2 : u * u = 1 := by simpa [pow_two] using hEel.2 u hu
  constructor
  · obtain ⟨a, haU, hau, k, hk, hak⟩ := hA G J c.block u (hEN hu) (twoElem_of_mul_self hu2)
      (by rw [hu2]; exact Subgroup.one_mem _)
    exact ⟨a, blockU_le J haU, c.block.blockU_sq_eq_one a haU,
      c.centralizer_le_conj (hEJ hu) (twoElem_of_mul_self hu2) hu1
        (Subgroup.mem_centralizer_singleton_iff.2 hau), k, hk, hak⟩
  · obtain ⟨a', ha'U, ha'w, k', hk', hak'⟩ := hA G _ hBg w₁ (hFN hw₁) (twoElem_of_mul_self hw₁2)
      (by rw [hw₁2]; exact Subgroup.one_mem _)
    exact ⟨a', blockU_le _ ha'U, hBg.blockU_sq_eq_one a' ha'U,
      hw₁C (Subgroup.mem_centralizer_singleton_iff.2 ha'w), k', hk', hak'⟩

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
