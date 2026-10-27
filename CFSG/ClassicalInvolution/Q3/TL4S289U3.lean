module

public import CFSG.ClassicalInvolution.Q3.TL4S289U1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight

namespace S289

section Transport

variable {G : Type} [Group G]

theorem conj_inv_mem_centralizer {g c x : G}
    (hx : x ∈ Subgroup.centralizer ({g * c * g⁻¹} : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.centralizer ({c} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc g⁻¹ * x * g * c = g⁻¹ * (x * (g * c * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * c * g⁻¹) * x) * g := by rw [hx]
    _ = c * (g⁻¹ * x * g) := by group

theorem oddQuotConj_symm_oddQuotMk (g c : G) {x : G}
    (hx : x ∈ Subgroup.centralizer ({g * c * g⁻¹} : Set G))
    (hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({c} : Set G)) :
    (ExactLayer.oddQuotConj g c).symm (oddQuotMk (g * c * g⁻¹) ⟨x, hx⟩) =
      oddQuotMk c ⟨g⁻¹ * x * g, hx'⟩ := by
  rw [MulEquiv.symm_apply_eq, ExactLayer.oddQuotConj_oddQuotMk]
  congr 1
  apply Subtype.ext
  rw [ExactLayer.coe_centralizerConj]
  group

theorem mem_normalizer_of_map_mulEquiv {H : Type} [Group H] (e : G ≃* H) {L : Subgroup G}
    {x : G} (h : e x ∈ Subgroup.normalizer ((L.map e.toMonoidHom : Subgroup H) : Set H)) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hm : ∀ z : G, e z ∈ L.map e.toMonoidHom ↔ z ∈ L := fun z =>
    ⟨fun ⟨v, hv, hvz⟩ => (e.injective hvz) ▸ hv, fun hz => ⟨z, hz, rfl⟩⟩
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  have h1 := h (e y)
  rw [show e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) by rw [map_mul, map_mul, map_inv], hm, hm] at h1
  exact h1

end Transport

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem vertexU_cps (hL : TightLargeHypR r n Y R S t) {J K'' : Subgroup Y} {u w : Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hu : IsUniqueInvolution J u)
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hw : IsUniqueInvolution K'' w) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (hwu : w ∈ Subgroup.centralizer ({u} : Set Y)) {L : Subgroup (OddQuot u)}
    (hLc : IsComponent L)
    (hmt : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩)
    (hmw : ∃ y ∈ L, oddQuotMk u ⟨w, hwu⟩ * y ≠ y * oddQuotMk u ⟨w, hwu⟩)
    (hmtw : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩ * y ≠
      y * (oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩)) {C : Prop}
    (hT : ∀ (J' K''' : Subgroup Y) (t' w' : Y),
      J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      IsUniqueInvolution J' t' → K''' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J' →
      IsUniqueInvolution K''' w' → ∀ (ht'C : t' ∈ Subgroup.centralizer ({t} : Set Y))
      (hwt : w' ∈ Subgroup.centralizer ({t} : Set Y)) (L' : Subgroup (OddQuot t)),
      IsComponent L' → (∃ y ∈ L', oddQuotMk t ⟨t', ht'C⟩ * y ≠ y * oddQuotMk t ⟨t', ht'C⟩) →
      (∃ y ∈ L', oddQuotMk t ⟨w', hwt⟩ * y ≠ y * oddQuotMk t ⟨w', hwt⟩) →
      (∃ y ∈ L', oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩ * y ≠
        y * (oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩)) →
      (Q3NM.AutOddFree ↥L' → Q3NM.AutOddFree ↥L) →
      (oddQuotMk t ⟨t', ht'C⟩ ∈ Subgroup.normalizer (L' : Set (OddQuot t)) →
        oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u))) → C) : C := by
  have hΩ := hL.datum.hypOmegaGen
  have hc := hΩ.conjInvariant
  have ht := hL.datum.isUniqueInvolution_core
  obtain ⟨g, hgJ'⟩ := hJ.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgu : g * t * g⁻¹ = u := by
    have h1 := ht.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  subst hgu
  have hK₀J := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ (CoreAssembly.mem_conjClass_self _)
    hJ.1 hJ
  have hJ' : conjSub g⁻¹ (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    have h1 := omegaNbr_conj hc hK₀J g⁻¹
    rwa [← hgJ, conjSub_inv_conjSub] at h1
  have ht' : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) (g⁻¹ * t * g) := by
    have h1 := ht.conj g⁻¹
    rwa [inv_inv] at h1
  have hw' : IsUniqueInvolution (conjSub g⁻¹ K'') (g⁻¹ * w * g) := by
    have h1 := hw.conj g⁻¹
    rwa [inv_inv] at h1
  have ht'C := conj_inv_mem_centralizer htu
  have hwt := conj_inv_mem_centralizer hwu
  set ψ := (ExactLayer.oddQuotConj g t).symm with hψ
  have hψt : ψ (oddQuotMk (g * t * g⁻¹) ⟨t, htu⟩) = oddQuotMk t ⟨g⁻¹ * t * g, ht'C⟩ :=
    oddQuotConj_symm_oddQuotMk g t htu ht'C
  have hψw : ψ (oddQuotMk (g * t * g⁻¹) ⟨w, hwu⟩) = oddQuotMk t ⟨g⁻¹ * w * g, hwt⟩ :=
    oddQuotConj_symm_oddQuotMk g t hwu hwt
  have hmov : ∀ a : OddQuot (g * t * g⁻¹), (∃ y ∈ L, a * y ≠ y * a) →
      ∃ y ∈ L.map ψ.toMonoidHom, ψ a * y ≠ y * ψ a := by
    rintro a ⟨y, hy, hne⟩
    refine ⟨ψ y, ⟨y, hy, rfl⟩, fun h => hne (ψ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  refine hT _ _ _ _ hJ' ht' (omegaNbr_conj hc hK g⁻¹) hw' ht'C hwt
    (L.map ψ.toMonoidHom) (LocalCores.isComponent_map_mulEquiv ψ hLc)
    (by rw [← hψt]; exact hmov _ hmt) (by rw [← hψw]; exact hmov _ hmw)
    (by rw [← hψt, ← hψw, ← map_mul]; exact hmov _ hmtw)
    (fun hA => Q3NM.AutOddFree.of_mulEquiv
      (L.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm hA) fun hN => ?_
  rw [← hψt] at hN
  exact mem_normalizer_of_map_mulEquiv ψ hN

theorem false_of_linkDich_at_u (hL : TightLargeHypR r n Y R S t) (hD : LinkDichSyl R t)
    {J K'' : Subgroup Y} {u w : Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hu : IsUniqueInvolution J u)
    (hK : K'' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hw : IsUniqueInvolution K'' w) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (hwu : w ∈ Subgroup.centralizer ({u} : Set Y)) {L : Subgroup (OddQuot u)}
    (hLc : IsComponent L)
    (hmt : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩)
    (hmw : ∃ y ∈ L, oddQuotMk u ⟨w, hwu⟩ * y ≠ y * oddQuotMk u ⟨w, hwu⟩)
    (hmtw : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩ * y ≠
      y * (oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩)) : False :=
  vertexU_cps hL hJ hu hK hw htu hwu hLc hmt hmw hmtw
    fun _ _ _ _ hJ' ht' hK' hw' ht'C hwt _ hL'c hmt' hmw' hmtw' _ _ =>
      false_of_linkDich hL hD hJ' ht' hK' hw' ht'C hwt hL'c hmt' hmw' hmtw'

end Cit3

end S289

end CFSG.ClassicalInvolution.Q3.TL4
