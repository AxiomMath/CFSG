module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2D2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

namespace EndN

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x : G} {q : ℕ} {W D₁ D₂ : Subgroup G}

structure Data (T M H S L D : Subgroup G) (n : ℕ) (t : G) (M₀ : Subgroup G) (x : G) (q : ℕ)
    (W D₁ D₂ : Subgroup G) : Prop where
  B : S2Base T M H S L D n t M₀ x q W
  h246 : Lemma246Double
  hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n
  hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n
  hD : D = D₁ ⊔ D₂
  hC : baumD S L = ⊥
  hDx : conjR D x = D
  hRJ : thompsonJ M₀ = thompsonJ S
  hA4 : Set.ncard {A : Subgroup G | IsMaxElemAbelian (thompsonJ S) A} = 4
  hlt : ¬ (T ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ M₀)

namespace Data

variable (E : Data T M H S L D n t M₀ x q W D₁ D₂)
include E

theorem cs : ConstrainedSetting G T M H S L := E.B.cs

theorem pCore_eq : pCoreOf 2 H = blockU L ⊔ conjSubgroup (blockU L) t := E.B.pCore_eq_UU E.hC

theorem x_normalizer_R : x ∈ Subgroup.normalizer (thompsonJ S : Set G) :=
  conjR_eq_self_iff.1 E.B.conjR_R_x₀

theorem Q_isMax : IsMaxElemAbelian (thompsonJ S) (pCoreOf 2 H) := by
  have h := E.B.su.isMax_DU
  rw [E.hC, bot_sup_eq] at h
  rw [E.pCore_eq]
  exact (isMaxElemAbelian_iff_of_thompsonJ_le (thompsonJ_le_self S) le_rfl).mpr h

theorem Qx_isMax : IsMaxElemAbelian (thompsonJ S) (conjR (pCoreOf 2 H) x) :=
  C56.isMaxElemAbelian_conjSubgroup E.Q_isMax E.x_normalizer_R

theorem U₁_le_Q : blockU L ≤ pCoreOf 2 H := by
  rw [E.pCore_eq]
  exact le_sup_left

theorem Qx_ne_Q : conjR (pCoreOf 2 H) x ≠ pCoreOf 2 H := by
  intro h
  apply C56.not_conj_le_of_mem_diff E.cs E.B.hSM E.B.hMT E.B.h2 E.B.hx₀ E.B.hx₀S
  have h1 := conjR_mono E.U₁_le_Q x
  rwa [h] at h1

theorem odd_orderOf {d : G} (hd : d ∈ D) : Odd (orderOf d) := by
  have hodd : Odd (Nat.card D) := E.B.cfg.hall.2.1
  have h1 : orderOf d ∣ Nat.card D := by
    rw [← Subgroup.orderOf_mk d hd]
    exact orderOf_dvd_natCard _
  exact hodd.of_dvd_nat h1

theorem D_fix {A : Subgroup G} (hA : IsMaxElemAbelian (thompsonJ S) A) {d : G} (hd : d ∈ D) :
    conjR A d = A := by
  classical
  by_contra hne
  set R := thompsonJ S with hR
  set 𝒜 : Set (Subgroup G) := {A | IsMaxElemAbelian R A} with h𝒜
  have hdR : d ∈ Subgroup.normalizer (R : Set G) := E.B.D_le_normalizer_R hd
  have hmap : ∀ {A' : Subgroup G}, A' ∈ 𝒜 → conjR A' d ∈ 𝒜 := fun hA' =>
    C56.isMaxElemAbelian_conjSubgroup hA' hdR
  have hinj : ∀ {A₁ A₂ : Subgroup G}, conjR A₁ d = conjR A₂ d → A₁ = A₂ := fun h =>
    conjR_inj_right h
  have hQfix : conjR (pCoreOf 2 H) d = pCoreOf 2 H :=
    conjR_eq_of_mem_normalizer (E.B.D_le_normalizer_pCore hd)
  have hQxfix : conjR (conjR (pCoreOf 2 H) x) d = conjR (pCoreOf 2 H) x :=
    conjR_eq_of_mem_normalizer (E.B.D_le_normalizer_conj_pCore hd)
  set Q := pCoreOf 2 H with hQ
  set Qx := conjR Q x with hQx
  have hQ𝒜 : Q ∈ 𝒜 := E.Q_isMax
  have hQx𝒜 : Qx ∈ 𝒜 := E.Qx_isMax
  have hQQx : Qx ≠ Q := E.Qx_ne_Q
  have hA𝒜 : A ∈ 𝒜 := hA
  have hAQ : A ≠ Q := fun h => hne (by rw [h, hQfix])
  have hAQx : A ≠ Qx := fun h => hne (by rw [h, hQxfix])
  set A' := conjR A d with hA'
  have hA'𝒜 : A' ∈ 𝒜 := hmap hA𝒜
  have hA'Q : A' ≠ Q := fun h => hAQ (hinj (by rw [← hA', h, hQfix]))
  have hA'Qx : A' ≠ Qx := fun h => hAQx (hinj (by rw [← hA', h, hQxfix]))
  have hA'A : A' ≠ A := hne
  have hset : 𝒜 = {Q, Qx, A, A'} := by
    have hsub : ({Q, Qx, A, A'} : Set (Subgroup G)) ⊆ 𝒜 := by
      intro X hX
      rcases hX with rfl | rfl | rfl | rfl
      · exact hQ𝒜
      · exact hQx𝒜
      · exact hA𝒜
      · exact hA'𝒜
    have hcard : ({Q, Qx, A, A'} : Set (Subgroup G)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [hQQx.symm, hAQ.symm, hA'Q.symm]),
        Set.ncard_insert_of_notMem (by simp [hAQx.symm, hA'Qx.symm]),
        Set.ncard_insert_of_notMem (by simp [hA'A.symm]), Set.ncard_singleton]
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, E.hA4]) (Set.toFinite _)).symm
  have hA'' : conjR A' d = A := by
    have hmem : conjR A' d ∈ ({Q, Qx, A, A'} : Set (Subgroup G)) := by
      rw [← hset]
      exact hmap hA'𝒜
    rcases hmem with h | h | h | h
    · exact absurd (hinj (by rw [h, hQfix])) hA'Q
    · exact absurd (hinj (by rw [h, hQxfix])) hA'Qx
    · exact h
    · exact absurd (hinj (by rw [h, ← hA'])) hA'A
  have hdd : d * d ∈ Subgroup.normalizer (A : Set G) := by
    rw [← conjR_eq_self_iff, conjR_mul, ← hA', hA'']
  obtain ⟨k, hk⟩ := E.odd_orderOf hd
  have hdpow : (d * d) ^ (k + 1) = d := by
    calc (d * d) ^ (k + 1) = d ^ (2 * (k + 1)) := by rw [← sq, ← pow_mul]
      _ = d ^ (orderOf d + 1) := by rw [hk]; ring_nf
      _ = d := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
  have hdN : d ∈ Subgroup.normalizer (A : Set G) := by
    rw [← hdpow]
    exact Subgroup.pow_mem _ hdd _
  exact hne (conjR_eq_self_iff.2 hdN)

end Data

end EndN

end CFSG.QuasithinUnique.Lin2
