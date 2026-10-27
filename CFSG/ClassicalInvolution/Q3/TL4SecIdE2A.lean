module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2D
public import CFSG.ClassicalInvolution.Q3.TL3TwistStep

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2D (isPGroup_mem card_mem pSpan_eq_top)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem mem_center_of_comm (hc : TightCls Y R S t) {x : Y}
    (h : ∀ I ∈ CoreAssembly.conjClass (tightCore R), ∀ y ∈ I, x * y = y * x) :
    x ∈ Subgroup.center Y := by
  have hle : pSpan (CoreAssembly.conjClass (tightCore R)) ≤
      Subgroup.centralizer ({x} : Set Y) :=
    iSup₂_le fun I hI y hy => Subgroup.mem_centralizer_singleton_iff.mpr (h I hI y hy).symm
  rw [pSpan_eq_top hc, top_le_iff] at hle
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.centralizer ({x} : Set Y) := hle ▸ Subgroup.mem_top y
  exact Subgroup.mem_centralizer_singleton_iff.mp hy

theorem not_edgeless_of_twin_one (hd : TightDatum R S t) {y : Y} (hy : y * t * y⁻¹ = t)
    (hne : conjSub y (tightCore R) ≠ tightCore R) : ¬ TightEdgeless R := by
  intro hE
  have hJΩ : conjSub y (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨y, rfl⟩
  refine hE _ (CoreAssembly.mem_conjClass_self (tightCore R)) _ hJΩ
    (Or.inl ⟨hJΩ, hne, conjSub y ((S : Subgroup R).map R.subtype),
      mem_RSet_of_isSylow2In hJΩ (hd.sylow_core.conj y), conjSub_mono hd.sylow_core.1, ?_⟩)
  intro x hx
  apply hd.le_normalizer_core
  rw [mem_conjSub_iff] at hx
  have hs := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (hd.S₀_le hx))
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * t = x * (y * t * y⁻¹) := by rw [hy]
    _ = y * ((y⁻¹ * x * y) * t) * y⁻¹ := by group
    _ = y * (t * (y⁻¹ * x * y)) * y⁻¹ := by rw [hs]
    _ = (y * t * y⁻¹) * x := by group
    _ = t * x := by rw [hy]

theorem not_edgeless_of_mul_mem_center (hd : TightDatum R S t) {g g' : Y}
    (hne : conjSub g (tightCore R) ≠ conjSub g' (tightCore R))
    (hc : (g * t * g⁻¹) * (g' * t * g'⁻¹) ∈ Subgroup.center Y) : ¬ TightEdgeless R := by
  set c := (g * t * g⁻¹) * (g' * t * g'⁻¹) with hcdef
  have htt : t * t = 1 := hd.isUniqueInvolution_core.sq
  have hy : (g⁻¹ * g') * t * (g⁻¹ * g')⁻¹ = t * c := by
    have h1 : g' * t * g'⁻¹ = (g * t * g⁻¹) * c := by
      rw [hcdef, ← mul_assoc]
      calc g' * t * g'⁻¹ = (g * (t * t) * g⁻¹) * (g' * t * g'⁻¹) := by rw [htt]; group
        _ = g * t * g⁻¹ * (g * t * g⁻¹) * (g' * t * g'⁻¹) := by group
    calc (g⁻¹ * g') * t * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * t * g'⁻¹) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [h1]
      _ = t * (g⁻¹ * c * g) := by group
      _ = t * c := by rw [show g⁻¹ * c * g = c by
          rw [Subgroup.mem_center_iff.mp hc g⁻¹]; group]
  by_cases hc1 : c = 1
  · rw [hc1, mul_one] at hy
    refine not_edgeless_of_twin_one hd hy fun h => hne ?_
    rw [conjSub_mul] at h
    calc conjSub g (tightCore R) = conjSub g (conjSub g⁻¹ (conjSub g' (tightCore R))) := by
          rw [h]
      _ = conjSub g' (tightCore R) := conjSub_conjSub_inv g _
  · exact TightDatum.not_edgeless_of_twin hd hc hc1 hy

theorem not_edgeless_of_twins_phi (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    {L L' : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hL' : L' ∈ CoreAssembly.conjClass (tightCore R)) {α : Finset (Fin m)} {h : α.card = 4}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h true)
    (hlab' : (L'.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h false) : ¬ TightEdgeless R := by
  have h8 : ∀ J ∈ CoreAssembly.conjClass (tightCore R), Nat.card ↥J = 8 := fun J hJ =>
    (card_mem hd hc hO2 J hJ).trans (by norm_num)
  obtain ⟨M, hM, M', hM', hne, u, u', hu, hu', hcomm⟩ := twins_of_phi hm φ hker h8 hL hL' hlab
    hlab' fun J hJ => Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hJ
  obtain ⟨g, rfl⟩ := hM
  obtain ⟨g', rfl⟩ := hM'
  have hcZ := mem_center_of_comm hc (x := u * u') fun I hI y hy => hcomm I hI y hy
  rw [← (hd.isUniqueInvolution_core.conj g).eq hu,
    ← (hd.isUniqueInvolution_core.conj g').eq hu'] at hcZ
  exact not_edgeless_of_mul_mem_center hd hne hcZ

theorem not_edgeless_of_aeIdent (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m)
    (I : AEIdent (CoreAssembly.conjClass (tightCore R)) m) : ¬ TightEdgeless R := by
  set α : Finset (Fin m) := (Finset.univ : Finset (Fin 4)).map (Fin.castLEEmb (by omega))
  have hα : α.card = 4 := by simp [α]
  obtain ⟨L, hL, hlab⟩ := I.label_surj α hα true
  obtain ⟨L', hL', hlab'⟩ := I.label_surj α hα false
  exact not_edgeless_of_twins_phi hd hc hO2 hm I.φ I.ker_le hL hL' hlab hlab'

theorem not_edgeless_of_aeIdentOn (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) {𝒜 : Set (Finset (Fin m))}
    {H : Subgroup (AE.AEQ m)} (I : AEIdentOn (CoreAssembly.conjClass (tightCore R)) m 𝒜 H)
    {α : Finset (Fin m)} (hα𝒜 : α ∈ 𝒜) (hα : α.card = 4) : ¬ TightEdgeless R := by
  obtain ⟨L, hL, hlab⟩ := I.label_surj α hα𝒜 hα true
  obtain ⟨L', hL', hlab'⟩ := I.label_surj α hα𝒜 hα false
  exact not_edgeless_of_twins_phi hd hc hO2 hm I.φ I.ker_le hL hL' hlab hlab'

theorem mem_e64Sets : ({0, 1, 3} : Finset (Fin 7))ᶜ ∈ AE.e64Sets :=
  ⟨{0, 1, 3}, by decide, rfl⟩

theorem mem_e29Sets : ({0, 2, 4, 6} : Finset (Fin 8)) ∈ AE.e29Sets := by
  show ({0, 2, 4, 6} : Finset (Fin 8)) ∈ AE.affinePlanes
  decide

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
