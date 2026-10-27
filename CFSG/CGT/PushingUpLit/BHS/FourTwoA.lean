module

public import CFSG.CGT.PushingUpLit.BHS.FourOneA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

namespace FourTwoTools

section GroupTools

variable {Γ : Type*} [Group Γ]

theorem conjSub_inv_conjSub (g : Γ) (A : Subgroup Γ) : conjSub g⁻¹ (conjSub g A) = A :=
  Glauberman.map_conj_inv_map_conj g A

theorem conjSub_conjSub_inv (g : Γ) (A : Subgroup Γ) : conjSub g (conjSub g⁻¹ A) = A :=
  Glauberman.map_conj_map_conj_inv g A

theorem conjSub_injective (g : Γ) : Function.Injective (conjSub g) :=
  fun _ _ e => (conjSub_inj g).1 e

theorem mem_normalizer_of_conjSub_le {a : Γ} {H : Subgroup Γ} (h₁ : conjSub a H ≤ H)
    (h₂ : conjSub a⁻¹ H ≤ H) : a ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h₁ (mem_conjSub_of_mem hx), fun hx => ?_⟩
  have := h₂ (mem_conjSub_of_mem (g := a⁻¹) hx)
  simpa [mul_assoc] using this

theorem conjSub_image_eq_of_subset [Finite Γ] {S : Set (Subgroup Γ)} (m : Γ)
    (h : S ⊆ conjSub m '' S) : conjSub m '' S = S :=
  (Set.eq_of_subset_of_ncard_le h (Set.ncard_image_of_injective S (conjSub_injective m)).le).symm

theorem exists_conjSub_ge [Finite Γ] {K T R : Subgroup Γ} (hT : IsSylowOf 2 T K)
    (hR : IsPGroup 2 R) (hRK : R ≤ K) : ∃ m ∈ K, R ≤ conjSub m T := by
  obtain ⟨k, hk, hkR⟩ := Glauberman.exists_conj_le_of_isSylowOf hT hR hRK
  refine ⟨k⁻¹, K.inv_mem hk, ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hkR
  rwa [Glauberman.map_conj_inv_map_conj] at this

theorem isSylowOf_inf_of_le_normalizer [Finite Γ] {K N T : Subgroup Γ} (hT : IsSylowOf 2 T K)
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set Γ)) : IsSylowOf 2 (N ⊓ T) N := by
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 T K := CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  rw [inf_comm]
  exact CFSG.ABGLocalTools.isSylowOf_iff.1 (hS.inf_of_le_normalizer hNK hKN)

theorem mem_setNormalizer_of_comm {P : Subgroup Γ} {S : Set (Subgroup Γ)} {g : Γ} (hgP : g ∈ P)
    (hg : ∀ B ∈ S, ∀ b ∈ B, g * b = b * g) : g ∈ setNormalizer P S := by
  refine ⟨hgP, fun B => ⟨fun hB => ?_, fun hB => ?_⟩⟩
  · rwa [FourOneTools.conjSub_eq_of_comm (hg B hB)]
  · have e : B = conjSub g B := by
      have e' : conjSub g⁻¹ (conjSub g B) = conjSub g B :=
        FourOneTools.conjSub_eq_of_comm fun x hx =>
          (Commute.inv_left (show Commute g x from hg _ hB x hx)).eq
      rwa [conjSub_inv_conjSub] at e'
    rw [e]
    exact hB

end GroupTools

section DInter

variable {V : Type} [CommGroup V]

theorem dInter_dInter_of_le {D : Set (Subgroup (MulAut V))} {H U : Subgroup (MulAut V)}
    (hUH : U ≤ H) : dInter (dInter D H) U = dInter D U := by
  ext A
  exact ⟨fun hA => ⟨hA.1.1, hA.2⟩, fun hA => ⟨⟨hA.1, hA.2.trans hUH⟩, hA.2⟩⟩

end DInter

end FourTwoTools

namespace Hyp41

section NoFinite

variable {V : Type} [CommGroup V] {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

theorem restrict (h : Hyp41 P D) {P' : Subgroup (MulAut V)} {D' : Set (Subgroup (MulAut V))}
    (hD : D' ⊆ D) (hle : ∀ A ∈ D', A ≤ P') (hconj : ∀ A ∈ D', ∀ g ∈ P', conjSub g A ∈ D') :
    Hyp41 P' D' where
  le := hle
  ne_bot A hA := h.ne_bot A (hD hA)
  elemAb A hA := h.elemAb A (hD hA)
  conj_mem := hconj
  quad A hA := h.quad A (hD hA)
  card_eq A hA := h.card_eq A (hD hA)
  fixV_eq A hA := h.fixV_eq A (hD hA)
  card_prod A hA B hB := h.card_prod A (hD hA) B (hD hB)

theorem dInter_restrict (h : Hyp41 P D) {H : Subgroup (MulAut V)} (hHP : H ≤ P) :
    Hyp41 H (dInter D H) :=
  h.restrict (fun _ hA => hA.1) (fun _ hA => hA.2) fun A hA g hg =>
    ⟨h.conj_mem A hA.1 g (hHP hg), Glauberman.map_conj_le hg hA.2⟩

theorem mem_setNormalizer_dInter (h : Hyp41 P D) {U : Subgroup (MulAut V)} {g : MulAut V}
    (hgP : g ∈ P) (hgU : g ∈ U) : g ∈ setNormalizer P (dInter D U) := by
  refine ⟨hgP, fun A => ⟨fun hA => ⟨h.conj_mem A hA.1 g hgP, Glauberman.map_conj_le hgU hA.2⟩,
    fun hA => ?_⟩⟩
  have h1 := h.conj_mem _ hA.1 g⁻¹ (P.inv_mem hgP)
  have h2 : conjSub g⁻¹ (conjSub g A) ≤ U := Glauberman.map_conj_le (U.inv_mem hgU) hA.2
  rw [FourTwoTools.conjSub_inv_conjSub] at h1 h2
  exact ⟨h1, h2⟩

theorem dInter_conjSub (h : Hyp41 P D) {m : MulAut V} (hm : m ∈ P) (U : Subgroup (MulAut V)) :
    dInter D (conjSub m U) = conjSub m '' dInter D U := by
  ext B
  constructor
  · rintro ⟨hBD, hBU⟩
    refine ⟨conjSub m⁻¹ B, ⟨h.conj_mem B hBD m⁻¹ (P.inv_mem hm), ?_⟩,
      FourTwoTools.conjSub_conjSub_inv m B⟩
    have := conjSub_mono m⁻¹ hBU
    rwa [FourTwoTools.conjSub_inv_conjSub] at this
  · rintro ⟨B', ⟨hB'D, hB'U⟩, rfl⟩
    exact ⟨h.conj_mem B' hB'D m hm, conjSub_mono m hB'U⟩

end NoFinite

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))}

theorem dInter_conjSub_eq_of_subset (h : Hyp41 P D) {m : MulAut V} (hm : m ∈ P)
    {U : Subgroup (MulAut V)} (hsub : dInter D U ⊆ dInter D (conjSub m U)) :
    dInter D (conjSub m U) = dInter D U := by
  rw [h.dInter_conjSub hm] at hsub ⊢
  exact FourTwoTools.conjSub_image_eq_of_subset m hsub

end Hyp41

end CFSG.CGT.PushingUpLit.BHS
