module

public import CFSG.GH74.GLS.Balance.Bender.Stmts
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG
open scoped commutatorElement

section Q326

variable {H : Type*} [Group H]

theorem aux52_simple_le_or_le_centralizer {N S M : Subgroup H} (hSN : S ≤ N) (hMN : M ≤ N)
    (hS : (S.subgroupOf N).Normal) (hM : (M.subgroupOf N).Normal) (hsimple : IsSimpleGroup S) :
    S ≤ M ∨ S ≤ centralizer (M : Set H) := by
  have hMS : (M.subgroupOf S).Normal := by
    refine ⟨fun t ht s => ?_⟩
    exact hM.conj_mem ⟨t, hSN t.2⟩ ht ⟨s, hSN s.2⟩
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf S)) with h | h
  · right
    intro s hs
    rw [mem_centralizer_iff]
    intro m hm
    have h1 : m * s⁻¹ * m⁻¹ ∈ S := by
      have := hS.conj_mem ⟨s⁻¹, hSN (inv_mem hs)⟩ (inv_mem hs) ⟨m, hMN hm⟩
      exact this
    have h2 : s * m * s⁻¹ ∈ M := by
      have := hM.conj_mem ⟨m, hMN hm⟩ hm ⟨s, hSN hs⟩
      exact this
    have hc : (⟨s * (m * s⁻¹ * m⁻¹), mul_mem hs h1⟩ : S) ∈ M.subgroupOf S := by
      show s * (m * s⁻¹ * m⁻¹) ∈ M
      have : s * (m * s⁻¹ * m⁻¹) = s * m * s⁻¹ * m⁻¹ := by group
      rw [this]
      exact mul_mem h2 (inv_mem hm)
    rw [h, Subgroup.mem_bot] at hc
    have hc' : s * (m * s⁻¹ * m⁻¹) = 1 := congrArg Subtype.val hc
    have hc'' : ⁅s, m⁆ = 1 := by
      rw [commutatorElement_def, ← hc']; group
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc'').symm
  · left
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ M.subgroupOf S := by rw [h]; exact mem_top _
    exact this

theorem aux52_le_iSup {N : Subgroup H} {r : ℕ} {S : Fin r → Subgroup H}
    (e : ((i : Fin r) → S i) ≃* N)
    (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : H) = x i) :
    N ≤ ⨆ i, S i := by
  classical
  intro x hx
  set K : Subgroup ((i : Fin r) → S i) := (⨆ i, S i).comap (N.subtype.comp e.toMonoidHom) with hK
  have hmem : ∀ y : (i : Fin r) → S i, y ∈ K := by
    intro y
    refine Subgroup.pi_mem_of_mulSingle_mem y fun i => ?_
    show (e (Pi.mulSingle i (y i)) : H) ∈ ⨆ j, S j
    rw [he i _ (fun j hj => Pi.mulSingle_eq_of_ne hj _), Pi.mulSingle_eq_same]
    exact mem_iSup_of_mem i (y i).2
  have := hmem (e.symm ⟨x, hx⟩)
  simpa [hK] using this

theorem aux52_commute_of_mem_conjugate {A : Subgroup H} (g : H)
    (hA : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s) :
    ∀ x ∈ CFSG.conjugate A g, ∀ y ∈ CFSG.conjugate A g, x * y = y * x := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul, hA s hs t ht]

theorem aux52_factors_nonabelian {N : Subgroup H} {r : ℕ} {S : Fin r → Subgroup H}
    (hconj : ∀ i j, ∃ g : H, S j = CFSG.conjugate (S i) g)
    (e : ((i : Fin r) → S i) ≃* N)
    (hnonab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) :
    ∀ i, ∃ a ∈ S i, ∃ b ∈ S i, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  have hall : ∀ j, ∀ a b : S j, a * b = b * a := by
    intro j a b
    obtain ⟨g, hg⟩ := hconj i₀ j
    apply Subtype.ext
    have ha : (a : H) ∈ CFSG.conjugate (S i₀) g := hg ▸ a.2
    have hb : (b : H) ∈ CFSG.conjugate (S i₀) g := hg ▸ b.2
    exact aux52_commute_of_mem_conjugate g hi₀ _ ha _ hb
  obtain ⟨a, ha, b, hb, hab⟩ := hnonab
  apply hab
  obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
  obtain ⟨y, hy⟩ := e.surjective ⟨b, hb⟩
  have h1 : (⟨a, ha⟩ : N) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    funext j
    exact hall j (x j) (y j)
  exact congrArg Subtype.val h1

theorem bender_q326 : BenderQ326 := by
  intro H _ _ N A hN hN1 hmin hnonab
  obtain ⟨r, S, -, hSN, hsimple, hconj, hSnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN hN1 (fun M hM hle => hmin M hle hM)
  have hNle : N ≤ ⨆ i, S i := aux52_le_iSup e he
  have hSnab := aux52_factors_nonabelian hconj e hnonab
  have hZ : N ⊓ centralizer (N : Set H) = ⊥ := by
    have hZn : (N ⊓ centralizer (N : Set H)).Normal := by
      refine ⟨fun z hz g => Subgroup.mem_inf.mpr ⟨hN.conj_mem z hz.1 g, ?_⟩⟩
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ N := by
        simpa using hN.conj_mem y hy g⁻¹
      have hcomm := mem_centralizer_iff.mp hz.2 _ hy'
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = g * z * g⁻¹ * y := by group
    rcases hmin _ inf_le_left hZn with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hnonab
      have hle : N ≤ centralizer (N : Set H) := fun x hx => by
        have : x ∈ N ⊓ centralizer (N : Set H) := by rw [h]; exact hx
        exact this.2
      exact hab (mem_centralizer_iff.mp (hle ha) b hb).symm
  have hB : ∀ B : Subgroup H, B ≤ N → (B.subgroupOf N).Normal →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → B = ⊥ := by
    intro B hBN hBn hBab
    have hcent : ∀ i, S i ≤ centralizer (B : Set H) := by
      intro i
      rcases aux52_simple_le_or_le_centralizer (hSN i) hBN (hSnorm i) hBn (hsimple i) with h | h
      · exfalso
        obtain ⟨a, ha, b, hb, hab⟩ := hSnab i
        exact hab (hBab a (h ha) b (h hb))
      · exact h
    have hNc : N ≤ centralizer (B : Set H) := hNle.trans (iSup_le hcent)
    have hBZ : B ≤ N ⊓ centralizer (N : Set H) := fun b hb => Subgroup.mem_inf.mpr ⟨hBN hb, by
      rw [mem_centralizer_iff]
      intro n hn
      exact (mem_centralizer_iff.mp (hNc hn) b hb).symm⟩
    rw [hZ] at hBZ
    exact le_bot_iff.mp hBZ
  set M : Subgroup H := ⁅N, A⁆ with hM
  have hMN : M ≤ N := Subgroup.commutator_le_left N A
  have hAM : A ≤ normalizer (M : Set H) := Subgroup.normalizer_commutator_ge_right N A
  have hMnorm : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mpr (Subgroup.normalizer_commutator_ge_left N A)
  have h1 : N ≤ M ⊔ (N ⊓ centralizer (M : Set H)) := by
    refine hNle.trans (iSup_le fun i => ?_)
    rcases aux52_simple_le_or_le_centralizer (hSN i) hMN (hSnorm i) hMnorm (hsimple i) with h | h
    · exact h.trans le_sup_left
    · exact (le_inf (hSN i) h).trans le_sup_right
  have h2 : N ⊓ centralizer (M : Set H) ≤ centralizer (A : Set H) := by
    rintro c ⟨hcN, hcC⟩
    rw [mem_centralizer_iff]
    intro a ha
    have hdM : ⁅c, a⁆ ∈ M := Subgroup.commutator_mem_commutator hcN ha
    have hdC : ⁅c, a⁆ ∈ centralizer (M : Set H) := by
      have hacM : ∀ m ∈ M, a⁻¹ * m * a ∈ M := fun m hm => by
        have := (mem_normalizer_iff.mp (hAM (inv_mem ha)) m).mp hm
        simpa using this
      have hc1 : ⁅c, a⁆ = c * (a * c⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]; group
      rw [hc1]
      refine mul_mem hcC ?_
      rw [mem_centralizer_iff]
      intro m hm
      have hm' := hacM m hm
      have hcomm : (a⁻¹ * m * a) * c⁻¹ = c⁻¹ * (a⁻¹ * m * a) :=
        mem_centralizer_iff.mp (inv_mem hcC) _ hm'
      calc m * (a * c⁻¹ * a⁻¹) = a * ((a⁻¹ * m * a) * c⁻¹) * a⁻¹ := by group
        _ = a * (c⁻¹ * (a⁻¹ * m * a)) * a⁻¹ := by rw [hcomm]
        _ = a * c⁻¹ * a⁻¹ * m := by group
    have hdN : ⁅c, a⁆ ∈ N := hMN hdM
    have hBn : ((M ⊓ centralizer (M : Set H)).subgroupOf N).Normal := by
      refine ⟨fun b hb n => ?_⟩
      have hb' : (b : H) ∈ M ⊓ centralizer (M : Set H) := hb
      show (n : H) * b * (n : H)⁻¹ ∈ M ⊓ centralizer (M : Set H)
      refine Subgroup.mem_inf.mpr ⟨hMnorm.conj_mem ⟨b, hMN hb'.1⟩ hb'.1 n, ?_⟩
      rw [mem_centralizer_iff]
      intro m hm
      have hm' : (n : H)⁻¹ * m * (n : H) ∈ M := by
        have h := hMnorm.conj_mem ⟨m, hMN hm⟩ hm n⁻¹
        have h' : ((n⁻¹ * ⟨m, hMN hm⟩ * n⁻¹⁻¹ : N) : H) ∈ M := h
        simpa using h'
      have hcomm : ((n : H)⁻¹ * m * (n : H)) * b = b * ((n : H)⁻¹ * m * (n : H)) :=
        mem_centralizer_iff.mp hb'.2 _ hm'
      calc m * ((n : H) * b * (n : H)⁻¹) = (n : H) * (((n : H)⁻¹ * m * (n : H)) * b) * (n : H)⁻¹ := by group
        _ = (n : H) * (b * ((n : H)⁻¹ * m * (n : H))) * (n : H)⁻¹ := by rw [hcomm]
        _ = (n : H) * b * (n : H)⁻¹ * m := by group
    have hBab : ∀ x ∈ M ⊓ centralizer (M : Set H), ∀ y ∈ M ⊓ centralizer (M : Set H), x * y = y * x :=
      fun x hx y hy => (mem_centralizer_iff.mp hy.2 x hx.1)
    have hbot := hB (M ⊓ centralizer (M : Set H)) (inf_le_left.trans hMN) hBn hBab
    have hmem : ⁅c, a⁆ ∈ M ⊓ centralizer (M : Set H) := ⟨hdM, hdC⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  exact h1.trans (sup_le_sup_left (le_inf inf_le_left h2) M)

end Q326
end CFSG.GH74.GLS.Balance
