module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapPentagon
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapBlocks
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowSevenMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SwapPair

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

@[expose] def LinearTwoSwapRowSevenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → 7 ≤ n →
    ∀ (e : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G),
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
                (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))))) → False

section Main

theorem linearTwoSwapRowSevenInput_holds : LinearTwoSwapRowSevenInput := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt hswap
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : Finite K := finite_of_card_eq_two_pow hK1
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set i₀ : Fin (m + 1) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (m + 1) := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin (m + 1) := ⟨3, by omega⟩ with hi₃
  set i₄ : Fin (m + 1) := ⟨4, by omega⟩ with hi₄
  set i₅ : Fin (m + 1) := ⟨5, by omega⟩ with hi₅
  set i₆ : Fin (m + 1) := ⟨6, by omega⟩ with hi₆
  have v₀ : (i₀ : ℕ) = 0 := rfl
  have v₁ : (i₁ : ℕ) = 1 := rfl
  have v₂ : (i₂ : ℕ) = 2 := rfl
  have v₃ : (i₃ : ℕ) = 3 := rfl
  have v₄ : (i₄ : ℕ) = 4 := rfl
  have v₅ : (i₅ : ℕ) = 5 := rfl
  have v₆ : (i₆ : ℕ) = 6 := rfl
  have hne : ∀ x y : Fin (m + 1), (x : ℕ) ≠ y → x ≠ y := fun x y h hxy => h (by rw [hxy])
  have h01 : i₀ ≠ i₁ := hne _ _ (by omega)
  have h23 : i₂ ≠ i₃ := hne _ _ (by omega)
  have h45 : i₄ ≠ i₅ := hne _ _ (by omega)
  have h24 : i₂ ≠ i₄ := hne _ _ (by omega)
  have h03 : i₀ ≠ i₃ := hne _ _ (by omega)
  have h16 : i₁ ≠ i₆ := hne _ _ (by omega)
  have h65 : i₆ ≠ i₅ := hne _ _ (by omega)
  have h63 : i₆ ≠ i₃ := hne _ _ (by omega)
  have h15 : i₁ ≠ i₅ := hne _ _ (by omega)
  have h13 : i₁ ≠ i₃ := hne _ _ (by omega)
  have hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b)
      (Y : Subgroup (LinearFlag.projectiveSL (m + 1) K)),
      Y ≤ rootSL2 a b → Nat.card Y = Nat.card K + 1 →
      ∃ P : SwapParam t (modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin (m + 1))))),
        Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore (modelToG e Y) := by
    intro a b hab Y hY hYc
    have htX : t ∈ centralizer (modelToG e Y : Set G) := mem_centralizer_map_symm e Y htC
    obtain ⟨Kc, hKc, hDKK, hne', hcomm, -, hiso⟩ := hswap a b hab Y hY hYc htX
    exact exists_swapParam_linear_two hset hK e (by omega) htC ht hab hY hYc htX hKc hDKK hne'
      hcomm hiso
  obtain ⟨Y₁, hY₁, -, hY₁c⟩ := exists_torusQ1 (K := K) h01
  obtain ⟨Y₂, hY₂, -, hY₂c⟩ := exists_torusQ1 (K := K) h23
  obtain ⟨Y₃, hY₃, -, hY₃c⟩ := exists_torusQ1 (K := K) h45
  obtain ⟨Y₄, hY₄, -, hY₄c⟩ := exists_torusQ1 (K := K) h24
  obtain ⟨Y₅, hY₅, -, hY₅c⟩ := exists_torusQ1 (K := K) h03
  obtain ⟨P₁, hinj₁, hrange₁⟩ := hparam i₀ i₁ h01 Y₁ hY₁ hY₁c
  obtain ⟨P₂, hinj₂, hrange₂⟩ := hparam i₂ i₃ h23 Y₂ hY₂ hY₂c
  obtain ⟨P₃, hinj₃, hrange₃⟩ := hparam i₄ i₅ h45 Y₃ hY₃ hY₃c
  obtain ⟨P₄, hinj₄, hrange₄⟩ := hparam i₂ i₄ h24 Y₄ hY₄ hY₄c
  obtain ⟨P₅, hinj₅, hrange₅⟩ := hparam i₀ i₃ h03 Y₅ hY₅ hY₅c
  have hmemc : ∀ x a b : Fin (m + 1), (x : ℕ) ≠ a → (x : ℕ) ≠ b →
      x ∈ ({a, b} : Finset (Fin (m + 1)))ᶜ := by
    intro x a b hxa hxb
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff]
    exact ⟨hxa, hxb⟩
  have hle : ∀ (Y : Subgroup (LinearFlag.projectiveSL (m + 1) K)) (c d a b : Fin (m + 1)),
      Y ≤ rootSL2 c d → (c : ℕ) ≠ a → (c : ℕ) ≠ b → (d : ℕ) ≠ a → (d : ℕ) ≠ b →
      modelToG e Y ≤ modelToG e (blockSL (K := K) ({a, b} : Finset (Fin (m + 1)))ᶜ) :=
    fun Y c d a b hY hca hcb hda hdb => modelToG_mono e (hY.trans
      (rootSL2_le_blockSL (hmemc c a b hca hcb) (hmemc d a b hda hdb)))
  have hov : ∀ (a b c d : Fin (m + 1)) (Y : Subgroup (LinearFlag.projectiveSL (m + 1) K)),
      a ≠ b → c ≠ d → (c : ℕ) ≠ a → (c : ℕ) ≠ b → (d : ℕ) ≠ a → (d : ℕ) ≠ b →
      Y ≤ rootSL2 c d → Nat.card Y = Nat.card K + 1 →
      perfectCore (modelToG e (blockSL (K := K) ({a, b} : Finset (Fin (m + 1)))ᶜ) ⊓
          centralizer (modelToG e Y : Set G)) =
        modelToG e (blockSL (K := K) (({a, b} : Finset (Fin (m + 1)))ᶜ \ {c, d})) ∧
      IsSimpleGroup (perfectCore (modelToG e (blockSL (K := K)
          ({a, b} : Finset (Fin (m + 1)))ᶜ) ⊓ centralizer (modelToG e Y : Set G))) ∧
      center (perfectCore (modelToG e (blockSL (K := K) ({a, b} : Finset (Fin (m + 1)))ᶜ) ⊓
          centralizer (modelToG e Y : Set G))) = ⊥ := by
    intro a b c d Y hab hcd hca hcb hda hdb hY hYc
    have hcard := card_sdiff_pair_of_disjoint_pair hab hcd (hne _ _ hca) (hne _ _ hcb)
      (hne _ _ hda) (hne _ _ hdb)
    have h3 : 3 ≤ (({a, b} : Finset (Fin (m + 1)))ᶜ \ {c, d}).card := by rw [hcard]; omega
    have hlt : (({a, b} : Finset (Fin (m + 1)))ᶜ \ {c, d}).card < m + 1 := by rw [hcard]; omega
    have hYc' : Nat.card Y = 3 := by rw [hYc, hK]
    have hO := perfectCore_modelToG_blockSL_inf_centralizer (L := L) hK (by omega) e
      (S := ({a, b} : Finset (Fin (m + 1)))ᶜ) hcd h3 hY hYc'
    have hS := isSimpleGroup_modelToG_blockSL_of_card_two (L := L) hK e h3 hlt
    rw [hO]
    exact ⟨rfl, hS.1, hS.2⟩
  obtain ⟨hO₁₂, hS₁₂, hZ₁₂⟩ := hov i₀ i₁ i₂ i₃ Y₂ h01 h23 (by omega) (by omega) (by omega)
    (by omega) hY₂ hY₂c
  obtain ⟨hO₁₃, hS₁₃, hZ₁₃⟩ := hov i₀ i₁ i₄ i₅ Y₃ h01 h45 (by omega) (by omega) (by omega)
    (by omega) hY₃ hY₃c
  obtain ⟨hO₂₃, hS₂₃, hZ₂₃⟩ := hov i₂ i₃ i₄ i₅ Y₃ h23 h45 (by omega) (by omega) (by omega)
    (by omega) hY₃ hY₃c
  obtain ⟨hO₁₄, hS₁₄, hZ₁₄⟩ := hov i₀ i₁ i₂ i₄ Y₄ h01 h24 (by omega) (by omega) (by omega)
    (by omega) hY₄ hY₄c
  obtain ⟨hO₃₅, hS₃₅, hZ₃₅⟩ := hov i₄ i₅ i₀ i₃ Y₅ h45 h03 (by omega) (by omega) (by omega)
    (by omega) hY₅ hY₅c
  obtain ⟨hO₄₅, hS₄₅, hZ₄₅⟩ := hov i₂ i₄ i₀ i₃ Y₅ h24 h03 (by omega) (by omega) (by omega)
    (by omega) hY₅ hY₅c
  have hmemT : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (p q r s : Fin (m + 1)),
      (i : ℕ) ≠ p → (i : ℕ) ≠ q → (i : ℕ) ≠ r → (i : ℕ) ≠ s → (j : ℕ) ≠ p → (j : ℕ) ≠ q →
      (j : ℕ) ≠ r → (j : ℕ) ≠ s →
      ((e.symm (LinearFlag.proj (m + 1) K (SpecialLinearGroup.transvection hij (1 : K))) : L) :
        G) ∈ modelToG e (blockSL (K := K) (({p, q} : Finset (Fin (m + 1)))ᶜ \ {r, s})) := by
    intro i j hij p q r s h1 h2 h3 h4 h5 h6 h7 h8
    exact symm_mem_modelToG e (proj_mem_blockSL (transvection_mem_blockSpecialLinear hij
      (mem_compl_pair_sdiff_pair_iff.2 ⟨h1, h2, h3, h4⟩)
      (mem_compl_pair_sdiff_pair_iff.2 ⟨h5, h6, h7, h8⟩) 1))
  have hb₁₂ := hmemT i₆ i₅ h65 i₀ i₁ i₂ i₃ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hb₁₄ := hmemT i₆ i₅ h65 i₀ i₁ i₂ i₄ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hc₁₃ := hmemT i₆ i₃ h63 i₀ i₁ i₄ i₅ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hc₁₄ := hmemT i₆ i₃ h63 i₀ i₁ i₂ i₄ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have ha₂₃ := hmemT i₁ i₆ h16 i₂ i₃ i₄ i₅ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have ha₃₅ := hmemT i₁ i₆ h16 i₄ i₅ i₀ i₃ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have ha₄₅ := hmemT i₁ i₆ h16 i₂ i₄ i₀ i₃ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [← hO₁₂] at hb₁₂
  rw [← hO₁₄] at hb₁₄ hc₁₄
  rw [← hO₁₃] at hc₁₃
  rw [← hO₂₃] at ha₂₃
  rw [← hO₃₅] at ha₃₅
  rw [← hO₄₅] at ha₄₅
  have hgen : perfectCore (modelToG e (blockSL (K := K) ({i₀, i₁} : Finset (Fin (m + 1)))ᶜ) ⊓
        centralizer (modelToG e Y₂ : Set G)) ⊔
      perfectCore (modelToG e (blockSL (K := K) ({i₀, i₁} : Finset (Fin (m + 1)))ᶜ) ⊓
        centralizer (modelToG e Y₃ : Set G)) ⊔
      perfectCore (modelToG e (blockSL (K := K) ({i₂, i₃} : Finset (Fin (m + 1)))ᶜ) ⊓
        centralizer (modelToG e Y₃ : Set G)) = L := by
    rw [hO₁₂, hO₁₃, hO₂₃, ← modelToG_sup_sup, blockSL_sup_sup_eq_top_seven K v₀ v₁ v₂ v₃ v₄ v₅ v₆,
      modelToG_top]
  exact false_of_swapParam_pentagon hset (isSolvable_outer_of_mulEquiv (by omega) e) e
    (swapPairExclusion_projectiveSL_two (by omega) hK) ht hKt P₁ P₂ P₃ P₄ P₅ hinj₁ hinj₂ hinj₃
    hinj₄ hinj₅ hrange₁ hrange₂ hrange₃ hrange₄ hrange₅ (modelToG_le e _) (modelToG_le e _)
    (modelToG_le e _)
    (hle Y₂ i₂ i₃ i₀ i₁ hY₂ (by omega) (by omega) (by omega) (by omega))
    (hle Y₃ i₄ i₅ i₀ i₁ hY₃ (by omega) (by omega) (by omega) (by omega))
    (hle Y₁ i₀ i₁ i₂ i₃ hY₁ (by omega) (by omega) (by omega) (by omega))
    (hle Y₃ i₄ i₅ i₂ i₃ hY₃ (by omega) (by omega) (by omega) (by omega))
    (hle Y₁ i₀ i₁ i₄ i₅ hY₁ (by omega) (by omega) (by omega) (by omega))
    (hle Y₂ i₂ i₃ i₄ i₅ hY₂ (by omega) (by omega) (by omega) (by omega))
    (hle Y₄ i₂ i₄ i₀ i₁ hY₄ (by omega) (by omega) (by omega) (by omega))
    (hle Y₁ i₀ i₁ i₂ i₄ hY₁ (by omega) (by omega) (by omega) (by omega))
    (hle Y₅ i₀ i₃ i₄ i₅ hY₅ (by omega) (by omega) (by omega) (by omega))
    (hle Y₃ i₄ i₅ i₀ i₃ hY₃ (by omega) (by omega) (by omega) (by omega))
    (hle Y₅ i₀ i₃ i₂ i₄ hY₅ (by omega) (by omega) (by omega) (by omega))
    (hle Y₄ i₂ i₄ i₀ i₃ hY₄ (by omega) (by omega) (by omega) (by omega))
    hS₁₂ hS₁₃ hS₂₃ hS₁₄ hS₃₅ hS₄₅ hZ₁₂ hZ₁₃ hZ₂₃ hZ₁₄ hZ₃₅ hZ₄₅ hb₁₂ hb₁₄ hc₁₃ hc₁₄ ha₂₃ ha₃₅
    ha₄₅ (not_commute_symm_proj_transvection hK e h16 h65 h15)
    (not_commute_symm_proj_transvection hK e h16 h63 h13) hgen

theorem false_of_linear_two_of_seven_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {n : ℕ} (hcat : SLmCatalogueClausesAt (n - 2))
    (hdet : SLmEvenTypeDetAt (n - 2)) {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 7 ≤ n) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False :=
  linearTwoSwapRowSevenInput_holds G L hset n K hK hn e t ht hKt fun _ _ hab _ hX₀ hX₀c htX =>
    swapRow_of_linear_two_of_seven_le hset hcat hdet hK e hn ht hKt hab hX₀ hX₀c htX

end Main

end CFSG.SeitzReduction.LinearPilot
