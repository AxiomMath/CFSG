module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowFixed

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin
open scoped commutatorElement

theorem index_lt_of_not_three_dvd (hJ : JordanPrimeCycle) {N : ℕ} (hN : N = 12 ∨ N = 16)
    (Y : Subgroup (alternatingGroup (Fin N))) (h3 : ¬ 3 ∣ Nat.card Y) :
    2 ^ (N - 2) * Nat.card Y < Nat.card (alternatingGroup (Fin N)) := by
  by_contra hge
  push Not at hge
  have : Nontrivial (Fin N) :=
    Fin.nontrivial_iff_two_le.mpr (by rcases hN with rfl | rfl <;> omega)
  set H : Subgroup (Equiv.Perm (Fin N)) := Y.map (alternatingGroup (Fin N)).subtype with hH
  have hHcard : Nat.card H = Nat.card Y :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin N)).subtype_injective
  have hHle : H ≤ alternatingGroup (Fin N) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hd : Nat.card H ∣ Nat.card (alternatingGroup (Fin N)) := Subgroup.card_dvd_of_le hHle
  have hAcard : ∀ M : ℕ, Fintype.card (Fin N) = M → Nat.card (alternatingGroup (Fin N)) =
      M.factorial / 2 := by
    intro M hM
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hM]
  rcases hN with rfl | rfl
  · have hA : Nat.card (alternatingGroup (Fin 12)) = 239500800 := by
      rw [hAcard 12 (by simp)]; decide
    rw [hA] at hd hge
    exact no_small_index_12 hJ H (by rwa [hHcard]) hd (by rw [hHcard]; simpa using hge)
  · have hA : Nat.card (alternatingGroup (Fin 16)) = 10461394944000 := by
      rw [hAcard 16 (by simp)]; decide
    rw [hA] at hd hge
    exact no_small_index_16 hJ H (by rwa [hHcard]) hd (by rw [hHcard]; simpa using hge)

theorem mul_card_lt_card_of_surjective_index {A Γ : Type*} [Group A] [Finite A] [Group Γ]
    (F : A →* Γ) (hF : Function.Surjective F) {n : ℕ}
    (hidx : ∀ H : Subgroup Γ, ¬ 3 ∣ Nat.card H → n * Nat.card H < Nat.card Γ)
    (Y : Subgroup A) (hY : ¬ 3 ∣ Nat.card Y) : n * Nat.card Y < Nat.card A := by
  have hA : Nat.card F.ker * Nat.card F.range = Nat.card A := Subgroup.card_ker_mul_card_range F
  have hrange : Nat.card F.range = Nat.card Γ := by
    rw [F.range_eq_top_of_surjective hF, Subgroup.card_top]
  have hYle : Nat.card Y ≤ Nat.card F.ker * Nat.card (Y.map F) := by
    have h1 : Nat.card (F.comp Y.subtype).ker * Nat.card (F.comp Y.subtype).range = Nat.card Y :=
      Subgroup.card_ker_mul_card_range (F.comp Y.subtype)
    have h2 : (F.comp Y.subtype).range = Y.map F := by
      ext z; simp [MonoidHom.mem_range, Subgroup.mem_map]
    have h3 : Nat.card (F.comp Y.subtype).ker ≤ Nat.card F.ker := by
      have hinj : Function.Injective
          (fun x : (F.comp Y.subtype).ker => (⟨(x : Y).1, x.2⟩ : F.ker)) := by
        intro a b hab
        have : (((a : (F.comp Y.subtype).ker) : Y) : A) = (((b : (F.comp Y.subtype).ker) : Y) : A) :=
          congrArg (fun z : F.ker => (z : A)) hab
        exact Subtype.ext (Subtype.ext this)
      exact Nat.card_le_card_of_injective _ hinj
    rw [h2] at h1
    rw [← h1]
    exact Nat.mul_le_mul_right _ h3
  have hFY : ¬ 3 ∣ Nat.card (Y.map F) := fun h => hY (h.trans (Subgroup.card_map_dvd Y F))
  have hFYc := hidx _ hFY
  have hker : 0 < Nat.card F.ker := Nat.card_pos
  rw [hrange] at hA
  calc n * Nat.card Y ≤ n * (Nat.card F.ker * Nat.card (Y.map F)) := Nat.mul_le_mul_left _ hYle
    _ = Nat.card F.ker * (n * Nat.card (Y.map F)) := by ring
    _ < Nat.card F.ker * Nat.card Γ := Nat.mul_lt_mul_of_pos_left hFYc hker
    _ = Nat.card A := hA

variable {G : Type} [Group G]

theorem three_dvd_of_socleLE_alt_big [Finite G] (hJ : JordanPrimeCycle) {N : ℕ}
    (hN : N = 12 ∨ N = 16) {M L V : Subgroup G} (hLM : L ≤ M)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (e : ↥(barM M L) ≃* alternatingGroup (Fin N))
    (hn : SocleLE L V (2 ^ (N - 2))) {y : G} (hy : y ∈ V) :
    3 ∣ Nat.card (L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  obtain ⟨F, hF⟩ := exists_surjective_barM hLM
  refine three_dvd_card_inf_centralizer_of_relIndex_bound hLV hV2 hVc hy hn fun Y hYL hY3 => ?_
  have h := mul_card_lt_card_of_surjective_index (e.toMonoidHom.comp F) (e.surjective.comp hF)
    (fun H hH => index_lt_of_not_three_dvd hJ hN H hH) (Y.subgroupOf L)
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv])
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv] at h

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
