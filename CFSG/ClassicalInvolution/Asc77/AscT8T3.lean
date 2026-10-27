module

public import CFSG.ClassicalInvolution.Asc77.AscT8T2
public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T8T

section Alpha

variable {G : Type} [Group G] {B α₀ : Subgroup G}

theorem centralizer_le_normalizer_of_alphaOf_eq {A : Subgroup G} (h : alphaOf A = α₀) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (α₀ : Set G) := by
  intro c hc
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  have h1 : conjSub c A = A := T7A.conjSub_eq_self_of_mem_centralizer hc
  have h2 := alphaOf_conjSub c A
  rw [h1, h] at h2
  exact h2.symm

variable [Finite G]

theorem oddCoreOf_centralizer_le_normalizer {b : G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hbB : b ∈ B)
    (h3 : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) :
    oddCoreOf (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (α₀ : Set G) := by
  have hBC : B ≤ Subgroup.centralizer ({b} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact DeltaClosure.comm_of_mem_elemAbelian hB hy hbB
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B (oddCoreOf (Subgroup.centralizer ({b} : Set G))) hB
    (by rw [hB8]; norm_num)
    (fun c hc => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hc))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({b} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => inf_le_right.trans ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun y hy => by rw [← pow_two]; exact hB.2 y (hE.1 hy)⟩
  exact centralizer_le_normalizer_of_alphaOf_eq (h3 E hE.1 hE2)

end Alpha

section Members

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {R : Fin 3 → Subgroup G} {α₀ : Subgroup G}


theorem TriFrame.le_normalizer_alpha (hF : TriFrame Ω M x R) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hB : IsElemAbelian 2 (Subgroup.closure ({x 0, x 1, x 2} : Set G)))
    (hB8 : Nat.card ↥(Subgroup.closure ({x 0, x 1, x 2} : Set G)) = 8)
    (h3 : ∀ A : Subgroup G, A ≤ Subgroup.closure ({x 0, x 1, x 2} : Set G) →
      IsElemAbelian2 A 2 → alphaOf A = α₀) (i j : Fin 3) (hij : i ≠ j) :
    M i ≤ Subgroup.normalizer (α₀ : Set G) := by
  have hxB : ∀ k, x k ∈ Subgroup.closure ({x 0, x 1, x 2} : Set G) := by
    intro k
    apply Subgroup.subset_closure
    fin_cases k <;> simp
  have hA : IsElemAbelian2 (Subgroup.closure ({x i, x j} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair (hF.sq i) (hF.sq j) (hF.ne_one i) (hF.ne_one j)
      (hF.x_ne hnt hij) (hF.comm hp hΩ i j)
  have hAB : Subgroup.closure ({x i, x j} : Set G) ≤
      Subgroup.closure ({x 0, x 1, x 2} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hxB i
    · exact hxB j
  have hMi : IsSubnormal (M i) (Subgroup.centralizer ({x i} : Set G)) :=
    T7A.isSubnormal_centralizer hΩ (hF.mem i) (hF.inv i)
  have hOle : oddCoreOf (Subgroup.centralizer ({x i} : Set G)) ≤ Subgroup.normalizer (α₀ : Set G) :=
    oddCoreOf_centralizer_le_normalizer hB hB8 (hxB i) h3
  have hxj : x j ∈ trivialOnQuot (M i) :=
    hF.le_trivialOnQuot hp hq hΩ hnt i (hxB j)
  intro k hk
  obtain ⟨h, hh, n, hn, rfl⟩ := cover_centralizer (isPGroup_zpowers_of_sq_eq_one (hF.sq j)) hxj k hk
  have hhM : h ∈ M i := hh.1
  have hhx : h ∈ Subgroup.centralizer ({x j} : Set G) := hh.2
  have hhy : h ∈ Subgroup.centralizer ({x i} : Set G) := isSubnormal_le hMi hhM
  have hhA : h ∈ Subgroup.centralizer ((Subgroup.closure ({x i, x j} : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : Subgroup.closure ({x i, x j} : Set G) ≤ Subgroup.centralizer ({h} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hhy).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hhx).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hhN : h ∈ Subgroup.normalizer (α₀ : Set G) :=
    centralizer_le_normalizer_of_alphaOf_eq (h3 _ hAB hA) hhA
  have hnN : n ∈ Subgroup.normalizer (α₀ : Set G) :=
    hOle (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hMi hn)
  exact Subgroup.mul_mem _ hhN hnN

end Members

section Layer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem oddCoreOf_layerJoin_le_oddCoreOf_centralizer (hΩ : HypOmegaMod p f Ω) (a : G) :
    oddCoreOf (T8.layerJoin Ω a) ≤ oddCoreOf (Subgroup.centralizer ({a} : Set G)) := by
  have hYC : T8.layerJoin Ω a ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ _
  intro x hx
  exact T8.oddCoreOf_le_oddCoreOf_of_normalized hYC
    (fun c hc => T8.layerJoin_conjSub_eq hΩ (by rw [T8.cenZ_eq_centralizer]; exact hc)) hx

end Layer

end T8T

end CFSG.ClassicalInvolution.Asc77
