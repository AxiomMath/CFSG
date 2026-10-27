module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFix
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem iSup₂_subgroupOf {Q : Type} [Group Q] {H : Subgroup Q} {ι : Type} (p : ι → Prop)
    (A : ι → Subgroup Q) (hA : ∀ i, p i → A i ≤ H) :
    (⨆ i, ⨆ (_ : p i), A i).subgroupOf H = ⨆ i, ⨆ (_ : p i), (A i).subgroupOf H := by
  have e : (⨆ i, ⨆ (_ : p i), A i) = (⨆ i, ⨆ (_ : p i), (A i).subgroupOf H).map H.subtype := by
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun i => iSup_congr fun hi =>
      (Subgroup.map_subgroupOf_eq_of_le (hA i hi)).symm
  rw [e]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem secAct_eq_conj_of_mem_layerY (hcl : ConjInvariant Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) (hyY : y ∈ layerY Ω x) (w : SecQuot Ω x) :
    secAct hcl hy w =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨y, hyY⟩ * w *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)) ⟨y, hyY⟩)⁻¹ := by
  obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
  have hyw : y * (w' : G) * y⁻¹ ∈ layerY Ω x :=
    (layerY Ω x).mul_mem ((layerY Ω x).mul_mem hyY w'.2) ((layerY Ω x).inv_mem hyY)
  have e := s26Act_mk (layerY Ω x) ⟨y, mem_normalizer_layerY hcl hy⟩ w' ⟨y * w' * y⁻¹, hyw⟩ rfl
  have e2 : (⟨y * w' * y⁻¹, hyw⟩ : ↥(layerY Ω x)) = ⟨y, hyY⟩ * w' * ⟨y, hyY⟩⁻¹ := rfl
  change s26Act (layerY Ω x) ⟨y, mem_normalizer_layerY hcl hy⟩ (w' : SecQuot Ω x) = _
  rw [e, e2]
  show QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))
    ((⟨y, hyY⟩ : ↥(layerY Ω x)) * w' * ⟨y, hyY⟩⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

theorem not_xMem_of_not_inner (h : TypeRFam r Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) {J₁ : Subgroup G}
    (hJ₁s : IsUniqueInvolution J₁ s)
    (hout : ¬ ∃ w : SecQuot Ω x, ∀ v, secAct h.hyp.conjInvariant hs v = w * v * w⁻¹) :
    ¬ XMem Ω x J₁ := fun hX =>
  hout ⟨_, secAct_eq_conj_of_mem_layerY h.hyp.conjInvariant hs
    (mem_layerY_of_isUniqueInvolution h hX hJ₁s)⟩

theorem exists_lift_mem_omegaNbr (h : TypeRFam r Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : s * s = 1) {J₁ : Subgroup G}
    (hJ₁ : J₁ ∈ Ω) (hJ₁s : IsUniqueInvolution J₁ s) (hnX : ¬ XMem Ω x J₁)
    {Mb : Subgroup (SecQuot Ω x)} (hMb : Mb ∈ secFam Ω x)
    (hfix : ∀ m ∈ Mb, secAct h.hyp.conjInvariant hs m = m) :
    ∃ M, XMem Ω x M ∧ secImg Ω x M = Mb ∧ M ∈ omegaNbr Ω J₁ := by
  obtain ⟨M, hM, hMb', Q, hQ, -, hQs⟩ := E3S3O.exists_xMem_of_fixed h hs hs2 hMb hfix
  exact ⟨M, hM, hMb', hM.1, fun e => hnX (e ▸ hM), Q, mem_RSet_of_isSylow2In hM.1 hQ, hQ.1,
    hQs.trans (h.tight J₁ hJ₁ s hJ₁s)⟩

theorem exists_fixGen_lift (h : TypeRFam r Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : s * s = 1) {J₁ : Subgroup G}
    (hJ₁ : J₁ ∈ Ω) (hJ₁s : IsUniqueInvolution J₁ s) (hnX : ¬ XMem Ω x J₁)
    {Kb : Subgroup (SecQuot Ω x)} (hKb : Kb ∈ secFam Ω x) :
    ∃ L : Subgroup G, L ≤ omegaNbrGen Ω J₁ ∧ L ≤ Subgroup.centralizer ({x} : Set G) ∧
      L ≤ layerY Ω x ∧
      (L.subgroupOf (layerY Ω x)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) =
        sigmaFixGen Kb (secAct h.hyp.conjInvariant hs) := by
  set σ := secAct h.hyp.conjInvariant hs with hσ
  set P : Subgroup G → Prop := fun M => M ∈ omegaNbr Ω J₁ ∧ XMem Ω x M ∧
    secImg Ω x M ∈ CoreAssembly.conjClass Kb ∧ ∀ m ∈ secImg Ω x M, σ m = m with hP
  refine ⟨⨆ M, ⨆ (_ : P M), coreAt x M,
    iSup₂_le fun M hM => (coreAt_le x M).trans (le_omegaNbrGen hM.1),
    iSup₂_le fun M _ => coreAt_le_centralizer x M,
    iSup₂_le fun M hM => coreAt_le_layerY hM.2.1, ?_⟩
  rw [iSup₂_subgroupOf P (fun M => coreAt x M) fun M hM => coreAt_le_layerY hM.2.1]
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    exact le_iSup₂ (f := fun (Mb : Subgroup (SecQuot Ω x))
      (_ : Mb ∈ {Mb : Subgroup (SecQuot Ω x) | Mb ∈ CoreAssembly.conjClass Kb ∧
        ∀ y ∈ Mb, σ y = y}) => Mb) (secImg Ω x M) ⟨hM.2.2.1, hM.2.2.2⟩
  · refine iSup₂_le fun Mb hMb => ?_
    obtain ⟨hMbK, hMbf⟩ := hMb
    obtain ⟨g, rfl⟩ := hMbK
    have hMbF : conjSub g Kb ∈ secFam Ω x := (h.secFam (x := x)).hyp.conjInvariant g Kb hKb
    obtain ⟨M, hMX, hMe, hMΩ⟩ := exists_lift_mem_omegaNbr h hs hs2 hJ₁ hJ₁s hnX hMbF hMbf
    have hPM : P M := ⟨hMΩ, hMX, hMe ▸ ⟨g, rfl⟩, hMe ▸ hMbf⟩
    show conjSub g Kb ≤ _
    rw [← hMe]
    exact le_iSup₂ (f := fun M (_ : P M) => ((coreAt x M).subgroupOf (layerY Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))) M hPM

end CFSG.ClassicalInvolution.Q3.TL4
