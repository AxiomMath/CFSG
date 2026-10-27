module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.P812

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSylowOf_sup_of_le_normalizer [Finite G] {O F : Subgroup G}
    (hO : Nat.Coprime 2 (Nat.card O)) (hF : IsPGroup 2 ↥F) (hFO : F ≤ normalizer (O : Set G)) :
    IsSylowOf 2 F (F ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := F ⊔ O with hW
  have hOW : O ≤ W := le_sup_right
  have hFW : F ≤ W := le_sup_left
  have hWN : W ≤ normalizer (O : Set G) := sup_le hFO Subgroup.le_normalizer
  have : (O.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOW).2 hWN
  have hcard : Nat.Coprime 2 (Nat.card (O.subgroupOf W)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOW).toEquiv]
    exact hO
  have hF' : IsPGroup 2 ↥(F.subgroupOf W) := hF.comap_subtype
  have h1 := isSylowOf_sup_of_coprime hcard hF'
  have htop : O.subgroupOf W ⊔ F.subgroupOf W = ⊤ := by
    have := Subgroup.subgroupOf_sup (A := O) (A' := F) (B := W) hOW hFW
    rw [← this, sup_comm O F, ← hW, Subgroup.subgroupOf_self]
  rw [htop] at h1
  have h2 := (isSylowOf_map_subtype_iff W (A := F.subgroupOf W) (B := ⊤)).2 h1
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hFW, Subgroup.map_top,
    Subgroup.range_subtype] at h2

theorem exists_mul_normalizer_of_conj_le [Finite G] {W S : Subgroup G} (hS : IsSylowOf 2 S W)
    {n : G} (hSn : S.map (MulAut.conj n).toMonoidHom ≤ W) :
    ∃ w ∈ W, w⁻¹ * n ∈ normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup G := S.map (MulAut.conj n).toMonoidHom with hS'
  have hS'S : IsSylowOf 2 S' W := by
    refine isSylowOf_of_card hSn ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hS.card_eq
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'S
  refine ⟨k, hk, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have e1 : s ∈ S ↔ n * s * n⁻¹ ∈ S' := by
    constructor
    · intro hs
      exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
    · rintro ⟨t, ht, hts⟩
      have h1 : t = s := by
        have := congrArg (fun z => n⁻¹ * z * n) hts
        simpa [MulAut.conj_apply, mul_assoc] using this
      rwa [← h1]
  have e2 := hconj (n * s * n⁻¹)
  have e3 : (k⁻¹ * n) * s * (k⁻¹ * n)⁻¹ = k⁻¹ * (n * s * n⁻¹) * k := by group
  rw [e3, ← e2, ← e1]

theorem mem_of_normalizes_sup [Finite G] {N M F : Subgroup G} (hFN : F ≤ N)
    (hF2 : IsPGroup 2 ↥F) (hFM : normalizer (F : Set G) ≤ M) (hO : pPrimeCoreOf 2 N ≤ M)
    {y : G} (hyF : ∀ f ∈ F, y * f * y⁻¹ ∈ F ⊔ pPrimeCoreOf 2 N) : y ∈ M := by
  set O := pPrimeCoreOf 2 N with hOdef
  have hNO : N ≤ normalizer (O : Set G) := fun n hn =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hn)
  have hSyl : IsSylowOf 2 F (F ⊔ O) :=
    isSylowOf_sup_of_le_normalizer (Nat.coprime_two_left.2 (TwoThin.card_pPrimeCoreOf_odd N)) hF2
      (hFN.trans hNO)
  have hconj : F.map (MulAut.conj y).toMonoidHom ≤ F ⊔ O := by
    rintro _ ⟨f, hf, rfl⟩
    exact hyF f hf
  obtain ⟨w, hw, hwy⟩ := exists_mul_normalizer_of_conj_le hSyl hconj
  have hwM : w ∈ M := (sup_le (Subgroup.le_normalizer.trans hFM) hO) hw
  have e : y = w * (w⁻¹ * y) := by group
  rw [e]
  exact M.mul_mem hwM (hFM hwy)

theorem frattini_core [Finite G] {N H M U V S₀ : Subgroup G}
    (hHnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hHM : H ≤ M)
    (hO : pPrimeCoreOf 2 N ≤ M) (hUH : U ≤ H)
    (hVnorm : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V)
    (hF2 : IsPGroup 2 ↥(U ⊔ V)) (hFN : U ⊔ V ≤ N)
    (hFM : normalizer ((U ⊔ V : Subgroup G) : Set G) ≤ M)
    (hS : IsSylowOf 2 S₀ (H ⊔ (N ⊓ centralizerSection H (pPrimeCoreOf 2 N))))
    (hS₀M : normalizer (S₀ : Set G) ≤ M) : N ≤ M := by
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
  have e : n = w * (w⁻¹ * n) := by group
  rw [e]
  exact M.mul_mem hwM (hS₀M hwn)

end CFSG.GH74.GLS.Th2.P812

