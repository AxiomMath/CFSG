module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.Gen

open CFSG.Open

variable {K : Type*} [Group K] [Finite K]

theorem isElemAbelian_map_hom' {G' : Type*} [Group G'] (p : ℕ) (φ : K →* G') {E : Subgroup K}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map φ) := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    change (a : G') * (b : G') = (b : G') * (a : G')
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    have hc : (⟨x, hx⟩ : E) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hcomm.is_comm.comm _ _
    exact congrArg Subtype.val hc
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hexp z' hz', map_one]

theorem le_pRank_of_card {H E : Subgroup K} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : k ≤ CFSG.Open.pRank 3 H := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card H, ?_⟩
    rintro j ⟨E', hE'H, -, hcard⟩
    have hlt : j < 3 ^ j := Nat.lt_pow_self (by norm_num)
    have hle : 3 ^ j ≤ Nat.card H := by
      rw [← hcard]
      exact Subgroup.card_le_of_le hE'H
    omega
  · exact ⟨E, hEH, hE, hk⟩

theorem card_eq_three_pow' {E : Subgroup K} (hE : IsElemAbelian 3 E) :
    ∃ k : ℕ, Nat.card E = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    exact hE.2 g.1 g.2
  exact hP.exists_card_eq

theorem two_le_pRank_of_pair {H : Subgroup K} {a b : K} (ha : a ∈ H) (hb : b ∈ H)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hinj : ∀ s t s' t' : Fin 3, a ^ (s : ℕ) * b ^ (t : ℕ) = a ^ (s' : ℕ) * b ^ (t' : ℕ) →
      s = s' ∧ t = t') :
    2 ≤ CFSG.Open.pRank 3 H := by
  have hcomm : ∀ x ∈ ({a, b} : Set K), ∀ y ∈ ({a, b} : Set K), Commute x y := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hT : IsMulCommutative (Subgroup.closure ({a, b} : Set K)) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy hxy => hcomm x hx y hy)
  have hTle : Subgroup.closure ({a, b} : Set K) ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hexp : ∀ x ∈ Subgroup.closure ({a, b} : Set K), x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha3
      · exact hb3
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hc : Commute x y := by
        have := hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx =>
      rw [inv_pow, ihx, inv_one]
  let T := Subgroup.closure ({a, b} : Set K)
  have hTel : IsElemAbelian 3 T := by
    refine ⟨hT, fun x hx => hexp x hx⟩
  have hcardT : 9 ≤ Nat.card T := by
    have hinjF : Function.Injective (fun p : Fin 3 × Fin 3 =>
        (⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), by
          refine T.mul_mem (T.pow_mem (Subgroup.subset_closure (by simp)) _)
            (T.pow_mem (Subgroup.subset_closure (by simp)) _)⟩ : T)) := by
      intro p q hpq
      have h := congrArg Subtype.val hpq
      obtain ⟨h1, h2⟩ := hinj p.1 p.2 q.1 q.2 h
      exact Prod.ext h1 h2
    have := Nat.card_le_card_of_injective _ hinjF
    simpa using this
  obtain ⟨k, hk⟩ := card_eq_three_pow' hTel
  have hk2 : 2 ≤ k := by
    rw [hk] at hcardT
    by_contra hlt
    push_neg at hlt
    interval_cases k <;> norm_num at hcardT
  exact le_trans hk2 (le_pRank_of_card hTle hTel hk)

theorem isSubnormal_le {Γ : Type*} [Group Γ] {A B : Subgroup Γ} (h : CFSG.Open.IsSubnormal A B) :
    A ≤ B := by
  induction h with
  | refl H => exact le_rfl
  | step hHM _ _ ih => exact le_trans hHM ih

theorem isSubnormal_subgroupOf {Γ : Type*} [Group Γ] (G : Subgroup Γ) {A B : Subgroup Γ}
    (h : CFSG.Open.IsSubnormal A B) : B ≤ G →
      CFSG.Open.IsSubnormal (A.subgroupOf G) (B.subgroupOf G) := by
  induction h with
  | refl H => intro _; exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hHM hn hMK ih =>
    intro hKG
    have hMG : M ≤ G := le_trans (isSubnormal_le hMK) hKG
    have hHG : H ≤ G := le_trans hHM hMG
    have hsub : H.subgroupOf G ≤ M.subgroupOf G := fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hHM hx
    refine CFSG.Open.IsSubnormal.step hsub ?_ (ih hKG)
    have key : ∀ (m h : Γ), m ∈ M → h ∈ H → m * h * m⁻¹ ∈ H := by
      intro m h hm hh
      have hhM : h ∈ M := hHM hh
      have := Subgroup.mem_subgroupOf.1
        (Subgroup.Normal.conj_mem hn ⟨h, hhM⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩)
      simpa using this
    constructor
    intro n hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact key _ _ (Subgroup.mem_subgroupOf.1 g.2) hn'

theorem exists_card_of_two_le_pRank {H : Subgroup K} (h : 2 ≤ CFSG.Open.pRank 3 H) :
    ∃ E : Subgroup K, E ≤ H ∧ IsElemAbelian 3 E ∧ ∃ k : ℕ, 2 ≤ k ∧ Nat.card E = 3 ^ k := by
  classical
  let S : Set ℕ := {k | ∃ E : Subgroup K, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}
  have hbdd : BddAbove S := by
    refine ⟨Nat.card H, ?_⟩
    rintro j ⟨E', hE'H, -, hcard⟩
    have hlt : j < 3 ^ j := Nat.lt_pow_self (by norm_num)
    have hle : 3 ^ j ≤ Nat.card H := by
      rw [← hcard]
      exact Subgroup.card_le_of_le hE'H
    omega
  have hbot : IsElemAbelian 3 (⊥ : Subgroup K) :=
    ⟨⟨⟨fun a b => by rw [Subsingleton.elim a b]⟩⟩, fun x hx => by
      rw [Subgroup.mem_bot.1 hx]
      simp⟩
  have hne : S.Nonempty := ⟨0, ⊥, bot_le, hbot, by simp⟩
  have hmem : CFSG.Open.pRank 3 H ∈ S := by
    unfold CFSG.Open.pRank
    exact Nat.sSup_mem hne hbdd
  obtain ⟨E, hEH, hE, hcard⟩ := hmem
  exact ⟨E, hEH, hE, _, by
    unfold CFSG.Open.pRank at h
    exact h, hcard⟩

theorem two_le_pRank_map_injective {G' : Type*} [Group G'] [Finite G'] (φ : K →* G') (hφ : Function.Injective φ)
    {H : Subgroup K} (h : 2 ≤ CFSG.Open.pRank 3 H) : 2 ≤ CFSG.Open.pRank 3 (H.map φ) := by
  obtain ⟨E, hEH, hE, k, hk2, hcard⟩ := exists_card_of_two_le_pRank h
  have hEφ : IsElemAbelian 3 (E.map φ) := isElemAbelian_map_hom' 3 φ hE
  have hc : Nat.card (E.map φ) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective hφ, hcard]
  exact le_trans hk2 (le_pRank_of_card (Subgroup.map_mono hEH) hEφ hc)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.Gen

end
