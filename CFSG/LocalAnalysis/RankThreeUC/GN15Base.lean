module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.EmptyFaithful.S1412
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open
open scoped Pointwise commutatorElement

section Absorption

variable {X : Type} [Group X] {T T₁ T₂ : Subgroup X}

@[expose] def gnM (T T₁ T₂ : Subgroup X) : Set X :=
  (Subgroup.centralizer (T₁ : Set X) : Set X) * (Y0 T T₁ T₂ : Set X) *
    (Subgroup.normalizer (T₂ : Set X) : Set X)

theorem mem_gnM_iff {x : X} : x ∈ gnM T T₁ T₂ ↔
    ∃ a ∈ Subgroup.centralizer (T₁ : Set X), ∃ y ∈ Y0 T T₁ T₂,
      ∃ b ∈ Subgroup.normalizer (T₂ : Set X), x = a * y * b := by
  constructor
  · rintro ⟨p, ⟨a, ha, y, hy, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, y, hy, b, hb, rfl⟩
  · rintro ⟨a, ha, y, hy, b, hb, rfl⟩
    exact ⟨a * y, ⟨a, ha, y, hy, rfl⟩, b, hb, rfl⟩

@[expose] def GNAbsorbs (T T₁ T₂ : Subgroup X) (N : Subgroup X) : Prop :=
  ∀ n ∈ N, ∀ m ∈ gnM T T₁ T₂, n * m ∈ gnM T T₁ T₂

theorem GNAbsorbs.mul_right {B : Subgroup X} (hB : B.Normal) (h : GNAbsorbs T T₁ T₂ B)
    {m : X} (hm : m ∈ gnM T T₁ T₂) {b : X} (hb : b ∈ B) : m * b ∈ gnM T T₁ T₂ := by
  obtain ⟨c, hc, y, hy, n, hn, rfl⟩ := mem_gnM_iff.mp hm
  have hb₃ : c * (y * (n * b * n⁻¹) * y⁻¹) * c⁻¹ ∈ B := by
    have h1 : n * b * n⁻¹ ∈ B := hB.conj_mem b hb n
    have h2 : y * (n * b * n⁻¹) * y⁻¹ ∈ B := hB.conj_mem _ h1 y
    exact hB.conj_mem _ h2 c
  have := h _ hb₃ _ (mem_gnM_iff.mpr ⟨c, hc, y, hy, n, hn, rfl⟩)
  convert this using 1
  group

theorem GNAbsorbs.of_cover_centralizer {A B : Subgroup X} (hBabs : GNAbsorbs T T₁ T₂ B)
    (hB : B.Normal)
    (hcov : A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X))) : GNAbsorbs T T₁ T₂ A := by
  intro a ha m hm
  obtain ⟨b, hb, k, hk, hbk⟩ := Subgroup.mem_sup_of_normal_left.mp (hcov ha)
  obtain ⟨c, hc, y, hy, n, hn, rfl⟩ := mem_gnM_iff.mp hm
  have hkm : k * (c * y * n) ∈ gnM T T₁ T₂ :=
    mem_gnM_iff.mpr ⟨k * c, mul_mem hk.2 hc, y, hy, n, hn, by group⟩
  rw [← hbk, mul_assoc]
  exact hBabs b hb _ hkm

theorem GNAbsorbs.of_cover_normalizer {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal)
    (hBabs : GNAbsorbs T T₁ T₂ B)
    (hcov : A ≤ B ⊔ (A ⊓ Subgroup.normalizer (T₂ : Set X))) : GNAbsorbs T T₁ T₂ A := by
  intro a ha m hm
  obtain ⟨c, hc, y, hy, n, hn, rfl⟩ := mem_gnM_iff.mp hm
  have ha'' : (c * y * n)⁻¹ * a * (c * y * n) ∈ A := by
    simpa using hA.conj_mem a ha (c * y * n)⁻¹
  rw [sup_comm] at hcov
  obtain ⟨k, hk, b, hb, hkb⟩ := Subgroup.mem_sup_of_normal_right.mp (hcov ha'')
  have hmem : c * y * (n * k) ∈ gnM T T₁ T₂ :=
    mem_gnM_iff.mpr ⟨c, hc, y, hy, n * k, mul_mem hn hk.2, by group⟩
  have := GNAbsorbs.mul_right hB hBabs hmem hb
  have hae : a * (c * y * n) = c * y * (n * k) * b := by
    calc a * (c * y * n) = (c * y * n) * ((c * y * n)⁻¹ * a * (c * y * n)) := by group
      _ = c * y * (n * k) * b := by rw [← hkb]; group
  rw [hae]
  exact this

theorem GNAbsorbs.sup {A B : Subgroup X} (hA : A.Normal) (hAabs : GNAbsorbs T T₁ T₂ A)
    (hBabs : GNAbsorbs T T₁ T₂ B) : GNAbsorbs T T₁ T₂ (A ⊔ B) := by
  intro x hx m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  rw [mul_assoc]
  exact hAabs a ha _ (hBabs b hb m hm)

end Absorption

section Frattini

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem normalizer_thompsonJ_subset_mul (hX : GNSetting X T) (h1 : T₁ ≤ omegaOneCenterOf T)
    (h2 : T₂ ≤ baum T) (h2c : (T₂.subgroupOf (baum T)).Characteristic) :
    (Subgroup.normalizer (thompsonJ T : Set X) : Set X) ⊆
      (Subgroup.centralizer (T₁ : Set X) : Set X) * (Subgroup.normalizer (T₂ : Set X) : Set X) := by
  set J : Subgroup X := thompsonJ T
  set E : Subgroup X := omegaOneCenterOf J
  set N : Subgroup X := Subgroup.normalizer (J : Set X)
  set K : Subgroup X := N ⊓ Subgroup.centralizer (E : Set X)
  have hTN : T ≤ N := Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hNE : N ≤ Subgroup.normalizer (E : Set X) :=
    normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv J
  have hNK : N ≤ Subgroup.normalizer (K : Set X) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hn,
      CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup E (hNE hn)⟩
  have hKN : K ≤ N := inf_le_left
  have hTsyl : IsSylowTwoOf T N := B6.isSylowTwoOf_mono hX.sylow hTN le_top
  have hKsyl : IsSylowTwoOf (T ⊓ K) K := B6.isSylowTwoOf_inf_normal hTsyl hKN hNK
  have hTK : T ⊓ K = baum T := by
    ext x
    simp only [Subgroup.mem_inf, K, baum, E, J]
    constructor
    · rintro ⟨hxT, -, hxc⟩
      exact ⟨hxT, hxc⟩
    · rintro ⟨hxT, hxc⟩
      exact ⟨hxT, hTN hxT, hxc⟩
  intro x hx
  have hfr := B6.frattini_two hKN hNK hKsyl
  have hxs : x ∈ K ⊔ (N ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)) := hfr hx
  have hle : N ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X) ≤
      Subgroup.normalizer (K : Set X) := fun n hn => hNK hn.1
  have hmem : x ∈ ((K ⊔ (N ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup X) : Set X)) :
      Subgroup X) : Set X) := hxs
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K _ hle] at hmem
  obtain ⟨k, hk, n, hn, rfl⟩ := hmem
  refine ⟨k, ?_, n, ?_, rfl⟩
  · exact Subgroup.centralizer_le
      (h1.trans (CFSG.AGLEmbeddingD2.GN.omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ T)) hk.2
  · rw [hTK] at hn
    exact normalizer_le_normalizer_of_characteristic_subgroupOf h2 h2c
      (Subgroup.mem_normalizer_iff.mpr (fun z => by
        simpa using (Subgroup.mem_normalizer_iff.mp hn.2 z)))

theorem frattini_of_normal_thompsonJ_le (hX : GNSetting X T) {W : Subgroup X} (hW : W.Normal)
    (hJ : thompsonJ T ≤ W) (x : X) :
    ∃ w ∈ W, ∃ n ∈ Subgroup.normalizer (thompsonJ T : Set X), x = w * n := by
  have hWn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := fun g _ =>
    Subgroup.normalizer_eq_top_iff.mpr hW |>.symm ▸ Subgroup.mem_top g
  have hsyl : IsSylowTwoOf (T ⊓ W) W := B6.isSylowTwoOf_inf_normal hX.sylow le_top hWn
  have hfr := B6.frattini_two (H := ⊤) le_top hWn hsyl
  have hx : x ∈ W ⊔ ((⊤ : Subgroup X) ⊓ Subgroup.normalizer ((T ⊓ W : Subgroup X) : Set X)) :=
    hfr (Subgroup.mem_top x)
  obtain ⟨w, hw, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  refine ⟨w, hw, n, ?_, rfl⟩
  have hJTW : thompsonJ T ≤ T ⊓ W := le_inf (B6.thompsonJ_le T) hJ
  have hEq : thompsonJ (T ⊓ W) = thompsonJ T := B6.thompsonJ_eq_of_le hJTW inf_le_left
  have := normalizer_le_normalizer_thompsonJ (T ⊓ W) hn.2
  rwa [hEq] at this

theorem gnFactor_of_normal (hX : GNSetting X T) (h1 : T₁ ≤ omegaOneCenterOf T)
    (h2 : T₂ ≤ baum T) (h2c : (T₂.subgroupOf (baum T)).Characteristic)
    {W : Subgroup X} (hW : W.Normal) (hJ : thompsonJ T ≤ W)
    (hWM : ∀ w ∈ W, ∃ a ∈ Subgroup.centralizer (T₁ : Set X), ∃ y ∈ Y0 T T₁ T₂,
      ∃ b ∈ Subgroup.normalizer (T₂ : Set X), w = a * y * b) :
    GNFactor T T₁ T₂ := by
  intro x
  obtain ⟨w, hw, n, hn, rfl⟩ := frattini_of_normal_thompsonJ_le hX hW hJ x
  obtain ⟨c, hc, m, hm, rfl⟩ := normalizer_thompsonJ_subset_mul hX h1 h2 h2c hn
  have hw' : c⁻¹ * w * c ∈ W := by
    have := hW.conj_mem w hw c⁻¹
    simpa [mul_assoc] using this
  obtain ⟨a, ha, y, hy, b, hb, hab⟩ := hWM _ hw'
  refine ⟨c * a, mul_mem hc ha, y, hy, b * m, mul_mem hb hm, ?_⟩
  have : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
  calc w * (c * m) = c * (c⁻¹ * w * c) * m := by group
    _ = c * (a * y * b) * m := by rw [hab]
    _ = c * a * y * (b * m) := by group

end Frattini

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
