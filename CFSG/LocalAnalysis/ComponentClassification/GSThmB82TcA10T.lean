module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82TcA10TDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82TcA10
import CFSG.LocalAnalysis.ComponentClassification.GSThmB82TcRed
import CFSG.LocalAnalysis.ComponentClassification.FooteLitGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SidePgl
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideS6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA1

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.A10Side
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X] [Finite X]

namespace Setting0

variable (s : Setting0 X)

theorem exists_unbalancing_mem_of_transfer
    (hNS : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X))
    {M : Subgroup X} (hMS : M ≤ s.h.S) (hM : M.relIndex s.h.S = 2)
    (hZ : ∀ k : X, k⁻¹ * s.h.x * k ∈ M → GrSLit.IsExtremalIn s.h.S (k⁻¹ * s.h.x * k) →
      (∀ u ∈ s.h.S ⊓ centralizer ({s.h.x} : Set X),
        k⁻¹ * u * k ∈ s.h.S ⊓ centralizer ({k⁻¹ * s.h.x * k} : Set X)) →
      k * s.h.a * k⁻¹ ∈ coreActionKernel s.h.J) :
    ∃ w ∈ M, GSUnbalancingTriple s.h.a w s.h.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := s.isSimpleGroup
  have hU := s.unbalTriple
  obtain ⟨R, hR⟩ := isSylow_S_of_caseA s.S_sylow hNS
  have hx2 : orderOf s.h.x = 2 := hU.2.1
  have hxR : s.h.x ∈ (R : Subgroup X) := by
    rw [hR]
    exact s.h.x_mem
  rcases GrSLit.goldschmidtTransferInput_holds X R s.h.x hxR hx2 with hall | hres
  swap
  · exact absurd (mem_twoResidualOf_top_of_isSimpleGroup s.nonab _) hres
  obtain ⟨g, hgM, hext⟩ := hall M (by rw [hR]; exact hMS) (by rw [hR]; exact hM)
  set y := g⁻¹ * s.h.x * g with hy
  obtain ⟨hyS, P, hP⟩ := hext
  rw [hR] at hyS hP
  set E := conjugate (s.h.S ⊓ centralizer ({s.h.x} : Set X)) g with hE
  have hEC : E ≤ centralizer ({y} : Set X) := by
    intro u hu
    rw [hE, mem_conjugate_iff] at hu
    have hux := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
    rw [mem_centralizer_singleton_iff]
    calc u * y = g⁻¹ * (g * u * g⁻¹ * s.h.x) * g := by rw [hy]; group
      _ = g⁻¹ * (s.h.x * (g * u * g⁻¹)) * g := by rw [hux]
      _ = y * u := by rw [hy]; group
  have hE2 : IsPGroup 2 ↥E := by
    rw [hE]
    exact (s.h.isPGroup_S.to_le inf_le_left).map _
  obtain ⟨c, hcy, hcE⟩ := exists_conjugate_le_of_sylow ⟨P, hP⟩ hEC hE2
  have hcy' : c * y = y * c := mem_centralizer_singleton_iff.mp hcy
  set k := g * c with hk
  have hky : k⁻¹ * s.h.x * k = y := by
    calc k⁻¹ * s.h.x * k = c⁻¹ * y * c := by rw [hk, hy]; group
      _ = y := by rw [mul_assoc, ← hcy', inv_mul_cancel_left]
  have hkC : ∀ u ∈ s.h.S ⊓ centralizer ({s.h.x} : Set X),
      k⁻¹ * u * k ∈ s.h.S ⊓ centralizer ({y} : Set X) := by
    intro u hu
    have h1 : g⁻¹ * u * g ∈ E := by
      rw [hE, mem_conjugate_iff]
      rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
    have h2 : c⁻¹ * (g⁻¹ * u * g) * c ∈ conjugate E c := by
      rw [mem_conjugate_iff]
      rwa [show c * (c⁻¹ * (g⁻¹ * u * g) * c) * c⁻¹ = g⁻¹ * u * g by group]
    have h3 := hcE h2
    rwa [show c⁻¹ * (g⁻¹ * u * g) * c = k⁻¹ * u * k by rw [hk]; group] at h3
  set T := conjugate (s.h.S ⊓ centralizer ({y} : Set X)) k⁻¹ with hT
  have hmemT : ∀ t, t ∈ T ↔ k⁻¹ * t * k ∈ s.h.S ⊓ centralizer ({y} : Set X) := by
    intro t
    rw [hT, mem_conjugate_iff, inv_inv]
  have hTsyl : Seven.IsSylowIn T (centralizer ({s.h.x} : Set X)) := by
    have hSy : Seven.IsSylowIn (s.h.S ⊓ centralizer ({y} : Set X)) (centralizer ({y} : Set X)) :=
      ⟨inf_le_right, P, hP⟩
    have h1 := isSylowIn_conjugate hSy k⁻¹
    rw [hT]
    rwa [conjugate_centralizer_singleton, inv_inv,
      show k * y * k⁻¹ = s.h.x by rw [← hky]; group] at h1
  have hCT : s.h.S ⊓ centralizer ({s.h.x} : Set X) ≤ T := fun u hu => (hmemT u).mpr (hkC u hu)
  set b := k * s.h.a * k⁻¹ with hb
  have haS := s.h.a_mem_S
  have hay : s.h.a * y = y * s.h.a := (s.h.comm_a hyS).symm
  have hbT : b ∈ T := by
    rw [hmemT, show k⁻¹ * b * k = s.h.a by rw [hb]; group]
    exact mem_inf.mpr ⟨haS, mem_centralizer_singleton_iff.mpr hay⟩
  have hbc : ∀ t ∈ T, t * b = b * t := by
    intro t ht
    have h1 := s.h.comm_a (mem_inf.mp ((hmemT t).mp ht)).1
    calc t * b = k * ((k⁻¹ * t * k) * s.h.a) * k⁻¹ := by rw [hb]; group
      _ = k * (s.h.a * (k⁻¹ * t * k)) * k⁻¹ := by rw [h1]
      _ = b * t := by rw [hb]; group
  have hbK : b ∈ coreActionKernel s.h.J := by
    have hext' : GrSLit.IsExtremalIn s.h.S (k⁻¹ * s.h.x * k) := by
      rw [hky]
      exact ⟨hyS, P, hP⟩
    have hkC' : ∀ u ∈ s.h.S ⊓ centralizer ({s.h.x} : Set X),
        k⁻¹ * u * k ∈ s.h.S ⊓ centralizer ({k⁻¹ * s.h.x * k} : Set X) := by
      rw [hky]
      exact hkC
    exact hZ k (by rw [hky]; exact hgM) hext' hkC'
  have hb2 : orderOf b = 2 := by
    rw [hb, ← MulAut.conj_apply, MulEquiv.orderOf_eq, s.h.orderOf_a]
  have hxC : s.h.x ∈ s.h.S ⊓ centralizer ({s.h.x} : Set X) :=
    mem_inf.mpr ⟨s.h.x_mem, mem_centralizer_singleton_iff.mpr rfl⟩
  have haC : s.h.a ∈ s.h.S ⊓ centralizer ({s.h.x} : Set X) :=
    mem_inf.mpr ⟨haS, mem_centralizer_singleton_iff.mpr (s.h.comm_a s.h.x_mem).symm⟩
  obtain ⟨K, hKc, hKU⟩ := s.isoAt s.h.x b (s.h.S_le s.h.x_mem) hU hb2 (hbc _ (hCT haC))
    (hbc _ (hCT hxC)) hbK
  have hKU' := gsUnbalancingTriple_conjugate hKU k
  rw [show k⁻¹ * b * k = s.h.a by rw [hb]; group, hky] at hKU'
  have hZK : center (OddBar K) = ⊥ := by
    obtain ⟨-, -, -, -, ⟨e₁, -⟩, ⟨e₂, -⟩, -⟩ :=
      isomorphic_correspondence_sylow_growth hKc rfl rfl rfl rfl
    exact center_eq_bot_of_mulEquiv (e₁.symm.trans e₂) s.center_J
  have hKJ : conjugate K k = s.h.J := by
    by_contra hne
    have hL := hKU'.2.2.2.1
    have hLp := hKU'.2.2.2.2.1
    exact s.h.a_not_mem_orbit_of_center_eq_bot hL hLp (center_oddBar_conjugate hZK k)
      (s.h.a_mem_orbit s.C_eq hL hLp hne)
  rw [hKJ] at hKU'
  exact ⟨y, hgM, hKU'⟩

end Setting0

end Eight2

theorem gs82CaseA10EpsZeroInput_of_transfer
    (hZ : GS82CentXA10TransferInput) : GS82CaseA10EpsZeroInput := by
  intro X _ _ s hNS hA hle
  obtain ⟨e, -⟩ := s.exists_isSymSixType hA
  obtain ⟨M6, hM6S, hmem⟩ : ∃ M6 : Subgroup X, M6 ≤ s.h.S ∧ ∀ u (hu : u ∈ s.h.S),
      u ∈ M6 ↔ IsSymSixType e (Eight.oddBarAction s.h.J ⟨u, s.h.S_le_normalizer hu⟩) := by
    refine ⟨s.h.S ⊓ ((((MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.comap
      (MulAut.congr e).toMonoidHom).comap (Eight.oddBarAction s.h.J)).map
      (normalizer (s.h.J : Set X)).subtype), inf_le_left, fun u hu => ?_⟩
    rw [mem_inf, mem_map]
    constructor
    · rintro ⟨-, n, hn, rfl⟩
      rw [mem_comap, mem_comap, MonoidHom.mem_range] at hn
      obtain ⟨σ, hσ⟩ := hn
      exact ⟨σ, hσ.symm⟩
    · rintro ⟨σ, hσ⟩
      refine ⟨hu, ⟨u, s.h.S_le_normalizer hu⟩, ?_, rfl⟩
      rw [mem_comap, mem_comap, MonoidHom.mem_range]
      exact ⟨σ, hσ.symm⟩
  have hxM : s.h.x ∉ M6 := fun h =>
    not_isSymSixType_of_unbalancing s.unbalTriple e
      (Eight.oddBarAction s.h.J ⟨s.h.x, s.h.S_le_normalizer s.h.x_mem⟩) (fun j => rfl)
      ((hmem _ s.h.x_mem).mp h)
  have hidx : M6.relIndex s.h.S = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨s.h.x, s.h.x_mem, hxM, fun u hu => ?_⟩
    by_cases huM : u ∈ M6
    · exact Or.inr huM
    · left
      have hux := mul_mem hu s.h.x_mem
      rw [hmem _ hux]
      have hmul : Eight.oddBarAction s.h.J ⟨u * s.h.x, s.h.S_le_normalizer hux⟩ =
          Eight.oddBarAction s.h.J ⟨u, s.h.S_le_normalizer hu⟩ *
            Eight.oddBarAction s.h.J ⟨s.h.x, s.h.S_le_normalizer s.h.x_mem⟩ := by
        rw [← map_mul]
        rfl
      rw [hmul]
      exact isSymSixType_mul_of_not e (fun h => huM ((hmem _ hu).mpr h))
        (fun h => hxM ((hmem _ s.h.x_mem).mpr h))
  obtain ⟨w, hwM, hUw⟩ := s.exists_unbalancing_mem_of_transfer hNS hM6S hidx
    fun k hkM hext hkC => hZ X s hNS hA hle e k hext ((hmem _ hext.1).mp hkM) hkC
  have hwS := hM6S hwM
  exact not_isSymSixType_of_unbalancing hUw e
    (Eight.oddBarAction s.h.J ⟨w, s.h.S_le_normalizer hwS⟩) (fun j => rfl)
    ((hmem w hwS).mp hwM)

end CFSG.ComponentClassification.GSThmB
