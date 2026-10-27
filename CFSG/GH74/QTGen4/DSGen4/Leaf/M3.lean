module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open Certificates.A5GL42 (Mat4 Vec4 commSet fixSet klein normSet invSubspaces NatFacts OrthFacts)
open scoped commutatorElement Matrix

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

section Aux

variable {G : Type} [Group G] [Finite G] {P L E K T : Subgroup G} {H : Finset Mat4}

theorem commSupK_le (h : A5Pre P L E K) (hTP : T ≤ P) {Y : Subgroup G} (hYE : Y ≤ E) :
    ⁅Y, T⁆ ⊔ K ≤ E :=
  sup_le (Subgroup.commutator_le.mpr fun y hy t ht =>
    ElemFrame.comm_right_mem h.norm_E (hTP ht) (hYE hy)) h.sec.1

theorem fixes_of_comm_mem {M : A5Model P L E K H} (h : A5Pre P L E K) (hTP : T ≤ P)
    (sd : SylowData M T) {e : G} (he : e ∈ E) (hall : ∀ t ∈ T, ⁅e, t⁆ ∈ K) :
    Multiplicative.toAdd (M.F.φ ⟨e, he⟩) ∈ fixSet (klein sd.x sd.y) := by
  unfold fixSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
  obtain ⟨t, htT, rfl⟩ := sd.ofA a ha
  exact (comm_mem_K_iff h.norm_E (hTP htT) he).mp (hall t htT)

theorem comm_mem_of_fixes {M : A5Model P L E K H} (h : A5Pre P L E K) (hTP : T ≤ P)
    (sd : SylowData M T) {e : G} (he : e ∈ E)
    (hv : Multiplicative.toAdd (M.F.φ ⟨e, he⟩) ∈ fixSet (klein sd.x sd.y)) {t : G} (ht : t ∈ T) :
    ⁅e, t⁆ ∈ K := by
  unfold fixSet at hv
  rw [Finset.mem_filter] at hv
  exact (comm_mem_K_iff h.norm_E (hTP ht) he).mpr (hv.2 _ (sd.toA ⟨t, hTP ht⟩ ht))

theorem m3_nat (hF : Certificates.A5GL42.Facts) (h : A5Pre P L E K) (hT : IsSylowTwoOf T L)
    (M : A5Model P L E K H) (sd : SylowData M T)
    (hA : NatFacts H (klein sd.x sd.y) (commSet (klein sd.x sd.y) Finset.univ)) :
    (∀ X : Subgroup G, K ≤ X → X ≤ E →
        L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
          X = K ∨ X = ⁅E, T⁆ ⊔ K ∨ X = E) ∧
      K.relIndex (⁅E, T⁆ ⊔ K) = 4 ∧
      (∀ t ∈ T, ∀ f ∈ ⁅E, T⁆ ⊔ K, ⁅f, t⁆ ∈ K) ∧
      (∀ e ∈ E, (∀ t ∈ T, ⁅e, t⁆ ∈ K) → e ∈ ⁅E, T⁆ ⊔ K) ∧
      (∀ s ∈ T ⊔ pCoreOf 2 P, s ∉ pCoreOf 2 P → ∀ e ∈ E, e ∉ ⁅E, T⁆ ⊔ K → ⁅e, s⁆ ∉ K) := by
  obtain ⟨⟨h0, hadd, hc4, hfix, hne1⟩, ⟨hlat, -⟩⟩ := hA
  have hTP : T ≤ P := hT.1.trans h.le
  have hKE : K ≤ E := h.sec.1
  have hCE : ⁅E, T⁆ ⊔ K ≤ E := commSupK_le h hTP le_rfl
  have hKC : K ≤ ⁅E, T⁆ ⊔ K := le_sup_right
  have hX : img M.F (⁅E, T⁆ ⊔ K) = commSet (klein sd.x sd.y) Finset.univ := by
    have := img_comm_sup h.norm_E hKE le_rfl hTP sd.toA sd.ofA (by rw [img_top]; exact h0)
      (by rw [img_top]; exact hadd)
    rwa [img_top] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X hKX hXE hXN
    have hW := img_mem_invSubspaces hF h M sd hXN
    rw [hlat] at hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with hW | hW | hW
    · left
      exact ext_of_img M.F hKX hXE le_rfl hKE (by rw [hW, img_bot_of_ker])
    · right; left
      exact ext_of_img M.F hKX hXE hKC hCE (by rw [hW, hX])
    · right; right
      exact ext_of_img M.F hKX hXE hKE le_rfl (by rw [hW, img_top])
  · rw [relIndex_eq_card_img M.F hKC hCE, hX, hc4]
  · intro t ht f hf
    have hfE := hCE hf
    have hv : Multiplicative.toAdd (M.F.φ ⟨f, hfE⟩) ∈ fixSet (klein sd.x sd.y) := by
      rw [← hfix, ← hX]
      exact (mem_iff_img M.F hKC ⟨f, hfE⟩).mp hf
    exact (comm_mem_of_fixes h hTP sd hfE hv ht)
  · intro e he hall
    have hv := fixes_of_comm_mem h hTP sd he hall
    rw [← hfix, ← hX] at hv
    exact (mem_iff_img M.F hKC ⟨e, he⟩).mpr hv
  · intro s hs hsQ e he hne hK
    have hQnorm : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
      (Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf P)
    obtain ⟨t, htT, hst⟩ := exists_mul_inv_mem_of_mem_sup hTP hQnorm s hs
    have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
    have hsP : s ∈ P := (sup_le hTP hQP) hs
    have hMs : M.F.M ⟨s, hsP⟩ = M.F.M ⟨t, hTP htT⟩ := by
      have h1 := M.core ⟨s * t⁻¹, P.mul_mem hsP (P.inv_mem (hTP htT))⟩ hst
      have h2 : (⟨s, hsP⟩ : ↥P) = ⟨s * t⁻¹, P.mul_mem hsP (P.inv_mem (hTP htT))⟩ * ⟨t, hTP htT⟩ :=
        Subtype.ext (by simp)
      rw [h2, map_mul, h1, one_mul]
    have hmem : glMat (M.F.M ⟨s, hsP⟩) ∈ klein sd.x sd.y := by
      rw [hMs]; exact sd.toA _ htT
    have hne1' : glMat (M.F.M ⟨s, hsP⟩) ≠ 1 := by
      intro h1
      apply hsQ
      have hM1 : M.F.M ⟨t, hTP htT⟩ = 1 := by rw [← hMs]; exact Units.ext h1
      have htQ : t ∈ pCoreOf 2 P :=
        pCoreOf_le_pCoreOf h.le h.norm_L ((M.kerL ⟨t, hTP htT⟩ (hT.1 htT)).mp hM1)
      have : s = (s * t⁻¹) * t := by simp
      rw [this]
      exact (pCoreOf 2 P).mul_mem hst htQ
    have hfixed := (comm_mem_K_iff (F := M.F) h.norm_E hsP he).mp hK
    have hvC := hne1 _ hmem hne1' _ hfixed
    apply hne
    rw [← hX] at hvC
    exact (mem_iff_img M.F hKC ⟨e, he⟩).mpr hvC

theorem m3_orth (hF : Certificates.A5GL42.Facts) (h : A5Pre P L E K) (hT : IsSylowTwoOf T L)
    (M : A5Model P L E K H) (sd : SylowData M T)
    (hA : OrthFacts H (klein sd.x sd.y) (commSet (klein sd.x sd.y) Finset.univ)
      (commSet (klein sd.x sd.y) (commSet (klein sd.x sd.y) Finset.univ))) :
    (∀ X : Subgroup G, K ≤ X → X ≤ E →
        L ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
          X = K ∨ X = ⁅⁅E, T⁆, T⁆ ⊔ K ∨ X = ⁅E, T⁆ ⊔ K ∨ X = E) ∧
      K.relIndex (⁅⁅E, T⁆, T⁆ ⊔ K) = 2 ∧ K.relIndex (⁅E, T⁆ ⊔ K) = 8 ∧
      (∀ t ∈ T, ∀ f ∈ ⁅⁅E, T⁆, T⁆ ⊔ K, ⁅f, t⁆ ∈ K) ∧
      (∀ e ∈ E, (∀ t ∈ T, ⁅e, t⁆ ∈ K) → e ∈ ⁅⁅E, T⁆, T⁆ ⊔ K) ∧
      (∀ d ∈ L ⊓ Subgroup.normalizer (T : Set G), orderOf d = 3 →
        FixFree (⁅⁅E, T⁆, T⁆ ⊔ K) (⁅E, T⁆ ⊔ K) d) := by
  obtain ⟨⟨h02, hadd2, hc8, h01, hadd1, hc2, hfix1⟩, ⟨hlat, hfpf, -⟩⟩ := hA
  have hTP : T ≤ P := hT.1.trans h.le
  have hKE : K ≤ E := h.sec.1
  have hCE2 : ⁅E, T⁆ ⊔ K ≤ E := commSupK_le h hTP le_rfl
  have hKC2 : K ≤ ⁅E, T⁆ ⊔ K := le_sup_right
  have hYE : ⁅E, T⁆ ≤ E := le_trans le_sup_left hCE2
  have hCE1 : ⁅⁅E, T⁆, T⁆ ⊔ K ≤ E := commSupK_le h hTP hYE
  have hKC1 : K ≤ ⁅⁅E, T⁆, T⁆ ⊔ K := le_sup_right
  have hX2 : img M.F (⁅E, T⁆ ⊔ K) = commSet (klein sd.x sd.y) Finset.univ := by
    have := img_comm_sup h.norm_E hKE le_rfl hTP sd.toA sd.ofA (by rw [img_top]; exact h02)
      (by rw [img_top]; exact hadd2)
    rwa [img_top] at this
  have hY : img M.F ⁅E, T⁆ = commSet (klein sd.x sd.y) Finset.univ := by
    have := img_comm h.norm_E le_rfl hTP sd.toA sd.ofA (by rw [img_top]; exact h02)
      (by rw [img_top]; exact hadd2)
    rwa [img_top] at this
  have hX1 : img M.F (⁅⁅E, T⁆, T⁆ ⊔ K) =
      commSet (klein sd.x sd.y) (commSet (klein sd.x sd.y) Finset.univ) := by
    have := img_comm_sup h.norm_E hKE hYE hTP sd.toA sd.ofA (by rw [hY]; exact h01)
      (by rw [hY]; exact hadd1)
    rwa [hY] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hKX hXE hXN
    have hW := img_mem_invSubspaces hF h M sd hXN
    rw [hlat] at hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with hW | hW | hW | hW
    · left
      exact ext_of_img M.F hKX hXE le_rfl hKE (by rw [hW, img_bot_of_ker])
    · right; left
      exact ext_of_img M.F hKX hXE hKC1 hCE1 (by rw [hW, hX1])
    · right; right; left
      exact ext_of_img M.F hKX hXE hKC2 hCE2 (by rw [hW, hX2])
    · right; right; right
      exact ext_of_img M.F hKX hXE hKE le_rfl (by rw [hW, img_top])
  · rw [relIndex_eq_card_img M.F hKC1 hCE1, hX1, hc2]
  · rw [relIndex_eq_card_img M.F hKC2 hCE2, hX2, hc8]
  · intro t ht f hf
    have hfE := hCE1 hf
    have hv : Multiplicative.toAdd (M.F.φ ⟨f, hfE⟩) ∈ fixSet (klein sd.x sd.y) := by
      rw [← hfix1, ← hX1]
      exact (mem_iff_img M.F hKC1 ⟨f, hfE⟩).mp hf
    exact comm_mem_of_fixes h hTP sd hfE hv ht
  · intro e he hall
    have hv := fixes_of_comm_mem h hTP sd he hall
    rw [← hfix1, ← hX1] at hv
    exact (mem_iff_img M.F hKC1 ⟨e, he⟩).mpr hv
  · intro d hd hd3 e he hK
    have heE := hCE2 he
    have hdP : d ∈ P := h.le hd.1
    have ho := M.order3 hd.1 hdP hd3
    have hB : glMat (M.F.M ⟨d, hdP⟩) ∈ normSet H (klein sd.x sd.y) := sd.toB ⟨d, hdP⟩ hd
    have hv2 : Multiplicative.toAdd (M.F.φ ⟨e, heE⟩) ∈ commSet (klein sd.x sd.y) Finset.univ := by
      rw [← hX2]
      exact (mem_iff_img M.F hKC2 ⟨e, heE⟩).mp he
    have hcE : ⁅e, d⁆ ∈ E := ElemFrame.comm_right_mem h.norm_E hdP heE
    have hv1 : Multiplicative.toAdd (M.F.φ ⟨⁅e, d⁆, hcE⟩) ∈
        commSet (klein sd.x sd.y) (commSet (klein sd.x sd.y) Finset.univ) := by
      rw [← hX1]
      exact (mem_iff_img M.F hKC1 ⟨⁅e, d⁆, hcE⟩).mp hK
    have hφc := M.F.phi_comm h.norm_E ⟨d, hdP⟩ ⟨e, heE⟩ ⟨⁅e, d⁆, hcE⟩ rfl
    rw [hφc] at hv1
    have hres := hfpf _ hB ho.2.1 ho.2.2 _ hv2 hv1
    rw [← hX1] at hres
    exact (mem_iff_img M.F hKC1 ⟨e, heE⟩).mpr hres

end Aux

theorem leafM3 : LeafM3 := by
  intro G _ _ P L E K T hc hT
  have h := hc.toPre
  have hF := a5Facts
  rcases h.exists_model hF with ⟨hnat, ⟨M⟩⟩ | ⟨hnat, ⟨M⟩⟩
  · obtain ⟨sd⟩ := M.exists_sylowData hF.groupN h hT
    have hmem : klein sd.x sd.y ∈ Certificates.A5GL42.kleinGroups Certificates.A5GL42.HN :=
      sd.mem_kleinGroups
    have hA := hF.kleinN _ hmem
    exact ⟨fun _ => m3_nat hF h hT M sd hA, fun hn => absurd hnat hn⟩
  · obtain ⟨sd⟩ := M.exists_sylowData hF.groupO h hT
    have hmem : klein sd.x sd.y ∈ Certificates.A5GL42.kleinGroups Certificates.A5GL42.HO :=
      sd.mem_kleinGroups
    have hA := hF.kleinO _ hmem
    exact ⟨fun hn => absurd hn hnat, fun _ => m3_orth hF h hT M sd hA⟩

end CFSG.GH74.QTGen4.DSGen4
