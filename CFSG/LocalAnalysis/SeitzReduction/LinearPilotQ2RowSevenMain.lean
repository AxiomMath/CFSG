module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowSeven
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowD2c
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldRow_two_of_seven_le (hset : SeitzSetting G L) {m : ℕ} (hm : 6 ≤ m)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {X₀ : Fin (m + 1) → Fin (m + 1) → Subgroup (LinearFlag.projectiveSL (m + 1) K)}
    (hX₀ : ∀ a b, X₀ a b ≤ rootSL2 a b)
    (hX₀c : ∀ a b, a ≠ b → Nat.card (X₀ a b) = Nat.card K + 1)
    (P : ∀ a b : Fin (m + 1), a ≠ b →
      FieldNeighbourParam e t ι σ (modelToG e (X₀ a b)) ({a, b}ᶜ : Finset (Fin (m + 1)))) :
    False := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  exact false_of_fieldRow_compl_of_seven_le hset hm hK1 le_rfl e ht hKt ι hσ1 hσσ hfix hX₀
    (fun a b hab => order3Elt_mem_of_card_eq_three hK (by omega) hab (hX₀ a b)
      (by rw [hX₀c a b hab, hK])) P

theorem false_of_fieldRow_two_of_one_of_seven_le (hset : SeitzSetting G L) {m : ℕ} (hm : 6 ≤ m)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a b : Fin (m + 1)} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL (m + 1) K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e X₀)
      ({a, b}ᶜ : Finset (Fin (m + 1))))) : False := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hσι : ∀ c : K, σ (ι c) = ι c := fun c => (hfix (ι c)).2 ⟨c, rfl⟩
  have key : ∀ a' b' : Fin (m + 1), a' ≠ b' → ∃ Y : Subgroup (LinearFlag.projectiveSL (m + 1) K),
      Y ≤ rootSL2 a' b' ∧ Nat.card Y = Nat.card X₀ ∧
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e Y) ({a', b'}ᶜ : Finset (Fin (m + 1)))) :=
    fun a' b' hab' => exists_fieldNeighbourParam_of_one e htC ι hσι hab hX₀ hP hab'
  choose! Y hY1 hY2 hY3 using key
  classical
  set X₁ : Fin (m + 1) → Fin (m + 1) → Subgroup (LinearFlag.projectiveSL (m + 1) K) :=
    fun a' b' => if a' = b' then ⊥ else Y a' b' with hX₁
  have hX₁eq : ∀ a' b', a' ≠ b' → X₁ a' b' = Y a' b' := fun a' b' h => by simp [hX₁, h]
  have hX₁bot : ∀ a' b', a' = b' → X₁ a' b' = ⊥ := fun a' b' h => by simp [hX₁, h]
  exact false_of_fieldRow_two_of_seven_le hset hm hK e ht hKt ι hσ1 hσσ hfix (X₀ := X₁)
    (fun a' b' => by
      by_cases h : a' = b'
      · rw [hX₁bot a' b' h]
        exact bot_le
      · rw [hX₁eq a' b' h]
        exact hY1 a' b' h)
    (fun a' b' h => by rw [hX₁eq a' b' h, hY2 a' b' h, hX₀c])
    (fun a' b' h => (show Nonempty (FieldNeighbourParam e t ι σ (modelToG e (X₁ a' b'))
      ({a', b'}ᶜ : Finset (Fin (m + 1)))) by rw [hX₁eq a' b' h]; exact hY3 a' b' h).some)

theorem false_of_fieldKind_two_of_seven_le (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 7 ≤ n) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hZ : center (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = ⊥)
    {Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
      oddCore (centralizer (modelToG e X₀ : Set G)))} (hKcomp : IsComponent Kc)
    (hDK : ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G)))))
    (hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .PSL (n - 2) 2 (2 * 1)) : False := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact false_of_fieldRow_two_of_one_of_seven_le hset (by omega) hK e ht hKt ι hσ1 hσσ hfix hab
    hX₀ hX₀c (nonempty_fieldNeighbourParam_of_fieldKind_two hset hK e (by omega) htC ht ι hσ1 hσσ
      hfix hab hX₀ hX₀c htX hZ hKcomp hDK hsN hτ hmodel)

theorem swapRow_of_linear_two_of_seven_le (hset : SeitzSetting G L) {n : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) (hdet : SLmEvenTypeDetAt (n - 2)) {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 7 ≤ n) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1)
    (htX : t ∈ centralizer (modelToG e X₀ : Set G)) :
    ∃ Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G))),
      IsComponent Kc ∧
      ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e X₀ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e X₀ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := exists_subfield_involution (F := GaloisField 2 (2 * 1)) le_rfl
    hK1 (GaloisField.card 2 (2 * 1) (by norm_num))
  obtain ⟨⟨Kc, hKcomp, hDKK, hrow⟩, hZ⟩ := neighbour_overgroup_linear_two_field hset hcat hdet hK e
    hn htC ht hab hX₀ hX₀c rfl htX rfl
  rcases hrow with ⟨-, hDK, -, hsN, hτ, -, hmodel, -⟩ | ⟨hKt', hcomm, hZK, hiso⟩
  · exact (false_of_fieldKind_two_of_seven_le hset hK e hn ht hKt ι hσ1 hσσ hfix hab hX₀ hX₀c htX
      hZ hKcomp hDK.le hsN hτ hmodel).elim
  · exact ⟨Kc, hKcomp, hDKK, hKt', hcomm, hZK, hiso⟩

end CFSG.SeitzReduction.LinearPilot
