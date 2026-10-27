module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Red
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

@[expose] def Core1297_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ V₂ K₁ : Subgroup G, IsTSub T V V₁ 1 → IsTSub T V V₂ 2 → V₁ ≤ V₂ → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      (K₁ ⊔ T) ⊓ Subgroup.normalizer (V₂ : Set G) ≤ lOne L V₁ ⊔ T

namespace L1297

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem centralizerMod_le_normalizer_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T L V : Subgroup G} {n : ℕ}
    (hcx : Cx1291 G T L V n) {V₁ K₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hLK : lOne L V₁ ≤ K₁) (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hDM : centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (V₁ : Set G)) K₁ ≤
      Subgroup.normalizer (L : Set G))
    {W : Subgroup G} (hV₁W : V₁ ≤ W) (hWV : W ≤ V) :
    centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (V₁ : Set G)) K₁ ≤
      Subgroup.normalizer (W : Set G) := by
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  intro d hd
  have hdM := hDM hd
  obtain ⟨hdG₁, -, hdc⟩ := hd

  have hdV : d ∈ Subgroup.normalizer (V : Set G) := by
    rcases hyp.ti_of_1222_F4 h1222 hdM with h1 | h1
    · exact SteinbergBS.mem_normalizer_of_conjugate_eq h1
    · exfalso
      have h2 : V₁ ≤ V ⊓ CFSG.conjugate V d := le_inf hV₁.1 fun x hx => by
        rw [SteinbergBS.mem_conjugate_iff]
        exact hV₁.1 ((Subgroup.mem_normalizer_iff.1 hdG₁ x).1 hx)
      rw [h1, le_bot_iff] at h2
      have h3 := hV₁.2.1
      rw [h2, Subgroup.card_bot] at h3
      norm_num at h3

  have hA := lemma12_8_4_one_F4 h1222 h hV₁ (isHzOne_normalizer_F4 h12213 h hV₁)
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hK₁n := normalizer_le_of_lOne_le_F4 h1222 h37 h38 h hn hV₁ hLK hK
  have hO₂ : pCoreOf 2 K₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁G₁)
      (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hVQ : ∀ y ∈ pCoreOf 2 K₁, ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ V₁ := by
    intro y hy v hv
    have h1 := V₁.inv_mem (commutator_mem_of_mem_pCoreOf hA (le_conjClosure V _ hv) (hO₂ hy))
    rwa [show (v * y * v⁻¹ * y⁻¹)⁻¹ = y * v * y⁻¹ * v⁻¹ by group] at h1

  have hkey := commutator_mem_of_commutator_mem h hn4 hV₁ hdV hdG₁
    (fun l hl v hv => hVQ _ (hdc l (hLK hl)) v hv)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have h1 := W.mul_mem (hV₁W (hkey w (hWV hw))) hw
    rwa [inv_mul_cancel_right] at h1
  · intro hw
    have hwV : w ∈ V := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hdV) _).1 (hWV hw)
      rwa [show d⁻¹ * (d * w * d⁻¹) * d⁻¹⁻¹ = w by group] at h1
    have h1 := W.mul_mem (W.inv_mem (hV₁W (hkey w hwV))) hw
    rwa [show (d * w * d⁻¹ * w⁻¹)⁻¹ * (d * w * d⁻¹) = w by group] at h1

end L1297

theorem claim12_9_7_of_core_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h1295 : Lemma12_9_5_F4) (hOut : OutFact1297)
    (hCore : Core1297_F4) : Claim12_9_7_F4 := by
  intro G _ _ T L V n hcx V₂ hV₂ x hx
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega

  obtain ⟨V₁, hV₁⟩ := exists_v1_of_hyp1281One_F4 h1222 h
  have hV₁₂ : V₁ ≤ V₂ := by
    rcases tinv_comparable_of_hyp1281One_F4 h1222 h hV₁.1 hV₂.1 hV₁.2.2 hV₂.2.2 with hle | hle
    · exact hle
    · exfalso
      have h1 := Subgroup.card_le_of_le hle
      rw [hV₁.2.1, hV₂.2.1] at h1
      norm_num at h1

  obtain ⟨K₁, hLK, hK, hK₁n⟩ := exists_cComp_normalizer_ge_lOne_F4 h1222 h37 h38 h39 h hn hV₁
  obtain ⟨⟨hDM, -⟩, hiso, -⟩ := h1295 G T L V n hcx V₁ K₁ hV₁ hLK hK
  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)

  have hxG₁ : x ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV₁₂ hx)
  obtain ⟨d, hd, hdx⟩ := hOut G (Subgroup.normalizer (V₁ : Set G)) K₁ T hK₁G₁ hK₁n
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hV₁.2.2) hiso x hxG₁
  have hdV₂ := L1297.centralizerMod_le_normalizer_F4 h1222 h12213 h37 h38 hcx hV₁ hLK hK hDM hV₁₂
    hV₂.1 hd

  have hy : d⁻¹ * x ∈ (K₁ ⊔ T) ⊓ Subgroup.normalizer (V₂ : Set G) :=
    ⟨hdx, Subgroup.mul_mem _ (Subgroup.inv_mem _ hdV₂)
      (Subgroup.centralizer_le_normalizer _ hx)⟩
  have hyM := hCore G T L V n hcx V₁ V₂ K₁ hV₁ hV₂ hV₁₂ hLK hK hy
  have hL₁T : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)) hyp.normalizes
  rw [show x = d * (d⁻¹ * x) by group]
  exact Subgroup.mul_mem _ (hDM hd) (hL₁T hyM)

end CFSG.Quasithin.H13
