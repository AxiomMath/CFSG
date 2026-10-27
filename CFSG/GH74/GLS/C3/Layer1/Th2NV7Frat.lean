module

public import CFSG.GH74.GLS.C3.Layer1.Th2P812Frat
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GH74.GLS.Th2.NV7

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P812
open scoped commutatorElement

variable {G : Type} [Group G]

theorem frattini_core' [Finite G] {N H M U V S₀ : Subgroup G} (hHN : H ≤ N)
    (hHnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hHM : H ≤ M)
    (hO : pPrimeCoreOf 2 N ≤ M) (hUH : U ≤ H)
    (hVnorm : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V)
    (hF2 : IsPGroup 2 ↥(U ⊔ V)) (hFN : U ⊔ V ≤ N)
    (hFM : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M)
    (hS : IsSylowOf 2 S₀ (H ⊔ (N ⊓ centralizerSection H (pPrimeCoreOf 2 N))))
    (hS₀M : ∀ m ∈ N, m ∈ normalizer (S₀ : Set G) → m ∈ M) : N ≤ M := by
  set O := pPrimeCoreOf 2 N with hOdef
  set Y : Subgroup G := N ⊓ centralizerSection H O with hY
  have hNH : ∀ n ∈ N, n ∈ normalizer (H : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hHnorm n hn h hh, fun hh => ?_⟩
    have := hHnorm n⁻¹ (N.inv_mem hn) _ hh
    simpa [mul_assoc] using this
  have hNO : ∀ n ∈ N, n ∈ normalizer (O : Set G) := fun n hn =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hn)
  have hOnorm : ∀ n ∈ N, ∀ o ∈ O, n * o * n⁻¹ ∈ O := fun n hn o ho =>
    (Subgroup.mem_normalizer_iff.1 (hNO n hn) o).1 ho
  have hYM : Y ≤ M := by
    intro y hy
    obtain ⟨hyN, hyc⟩ := hy
    have hycomm : ∀ k ∈ H, ⁅k, y⁆ ∈ O := hyc.2.2
    refine mem_of_normalizes_sup hFN hF2 hFM hO (y := y) (fun f hf => ?_)
    have hle : (U ⊔ V).map (MulAut.conj y).toMonoidHom ≤ (U ⊔ V) ⊔ O := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        have h1 : ⁅u, y⁆ ∈ O := hycomm u (hUH hu)
        have e : (MulAut.conj y).toMonoidHom u = (⁅u, y⁆)⁻¹ * u := by
          change y * u * y⁻¹ = (⁅u, y⁆)⁻¹ * u
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (O.inv_mem h1))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu))
      · rintro _ ⟨v, hv, rfl⟩
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hVnorm y hyN v hv))
    exact hle ⟨f, hf, by simp [MulAut.conj_apply]⟩
  have hYnorm : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    intro n hn y hy
    obtain ⟨hyN, hyc⟩ := hy
    have hycomm : ∀ k ∈ H, ⁅k, y⁆ ∈ O := hyc.2.2
    have hnyN : n * y * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hn hyN) (N.inv_mem hn)
    refine ⟨hnyN, hNH _ hnyN, hNO _ hnyN, fun k hk => ?_⟩
    have e : ⁅k, n * y * n⁻¹⁆ = n * ⁅n⁻¹ * k * n, y⁆ * n⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hOnorm n hn _ (hycomm _ (by simpa [mul_assoc] using hHnorm n⁻¹ (N.inv_mem hn) k hk))
  have hWnorm : ∀ n ∈ N, (H ⊔ Y).map (MulAut.conj n).toMonoidHom ≤ H ⊔ Y := by
    intro n hn
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact hHnorm n hn h hh
    · rintro _ ⟨y, hy, rfl⟩
      exact hYnorm n hn y hy
  intro n hn
  obtain ⟨w, hw, hwn⟩ := exists_mul_normalizer_of_conj_le hS
    ((Subgroup.map_mono hS.le).trans (hWnorm n hn))
  have hwM : w ∈ M := (sup_le hHM hYM) hw
  have hwN : w ∈ N := (sup_le hHN inf_le_left) hw
  have e : n = w * (w⁻¹ * n) := by group
  rw [e]
  exact M.mul_mem hwM (hS₀M _ (N.mul_mem (N.inv_mem hwN) hn) hwn)

end CFSG.GH74.GLS.Th2.NV7
