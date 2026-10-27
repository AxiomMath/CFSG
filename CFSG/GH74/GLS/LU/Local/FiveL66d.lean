module

public import CFSG.GH74.GLS.LU.Local.FiveL66c
public import CFSG.GH74.GLS.LU.Local.FiveW
public import CFSG.GH74.GLS.LU.Local.FiveL66b

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section PsiLemmas

variable {G Gs : Type*} [Group G] [Group Gs] {X : Subgroup G} {X' : Subgroup Gs}

abbrev pe (ψ : ↥X ≃* ↥X') (x : G) (hx : x ∈ X) : Gs := ((ψ ⟨x, hx⟩ : ↥X') : Gs)

theorem pe_mul (ψ : ↥X ≃* ↥X') {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    pe ψ (x * y) (X.mul_mem hx hy) = pe ψ x hx * pe ψ y hy := psi_mul ψ hx hy

theorem pe_inv (ψ : ↥X ≃* ↥X') {x : G} (hx : x ∈ X) :
    pe ψ x⁻¹ (X.inv_mem hx) = (pe ψ x hx)⁻¹ := psi_inv ψ hx

theorem pe_eq_iff (ψ : ↥X ≃* ↥X') {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    pe ψ x hx = pe ψ y hy ↔ x = y := psi_eq_iff ψ hx hy

theorem pe_conj (ψ : ↥X ≃* ↥X') {g x : G} (hg : g ∈ X) (hx : x ∈ X) :
    pe ψ (g * x * g⁻¹) (X.mul_mem (X.mul_mem hg hx) (X.inv_mem hg)) =
      pe ψ g hg * pe ψ x hx * (pe ψ g hg)⁻¹ := by
  have h1 := pe_mul ψ (X.mul_mem hg hx) (X.inv_mem hg)
  have h2 := pe_mul ψ hg hx
  have h3 := pe_inv ψ hg
  rw [h1, h2, h3]

theorem pe_comm_iff (ψ : ↥X ≃* ↥X') {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    x * y = y * x ↔ pe ψ x hx * pe ψ y hy = pe ψ y hy * pe ψ x hx := by
  rw [← pe_mul ψ hx hy, ← pe_mul ψ hy hx, pe_eq_iff]

end PsiLemmas

section Five66W

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t u : G} {K₁ K₂ : Subgroup G}
  {ht : t ∈ Cz z} {hu : u ∈ Cz z} {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

omit [Finite G] in
theorem ModelPic.five66W (pic : ModelPic z t u K₁ K₂ ht hu z' S' K₁' K₂' t' u' ψ)
    (hzt : z * t = t * z) (hut : u * t = t * u)
    (htL : ∀ g : G, g * z * g⁻¹ = u →
      cjL t (cjL g K₁) = cjL g K₁ ∧ cjL t (cjL g K₂) = cjL g K₂) :
    ∃ (H : Subgroup G) (w₁ : G), Five66W z t u K₁ K₂ H w₁ := by
  classical
  obtain ⟨H', hT⟩ := pic.facts.torus_exists
  obtain ⟨hz'H, hu'H, hPnorm, hP2⟩ := pic.facts.torus_facts H' hT
  obtain ⟨w', hw'K, hw'sq, hw'u⟩ := pic.facts.w_exists
  have hzC : z ∈ Cz z := mem_Cz_self z
  have hH'le : H' ≤ Cz z' := by
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mem_PP.mp (hT.1 hh)).1
  have hP'le : centralizer ((UU z' u' : Subgroup Gs) : Set Gs) ≤ Cz z' := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mem_PP.mp hh).1
  have hw'C : w' ∈ Cz z' := pic.K₁'_le hw'K
  obtain ⟨w₁, hw₁C, hψw₁⟩ := exists_psi_eq ψ hw'C
  have ht'z : t' * z' = z' * t' := by
    have h : ((ψ ⟨t, ht⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) =
        ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨t, ht⟩ : ↥(Cz z')) : Gs) :=
      (pe_comm_iff ψ ht hzC).mp hzt.symm
    rwa [pic.psi_t, pic.psi_z] at h
  have ht'u : t' * u' = u' * t' := by
    have h : ((ψ ⟨t, ht⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) =
        ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨t, ht⟩ : ↥(Cz z')) : Gs) :=
      (pe_comm_iff ψ ht hu).mp hut.symm
    rwa [pic.psi_t, pic.psi_u] at h
  have ht'P : t' ∈ centralizer ((UU z' u' : Subgroup Gs) : Set Gs) := mem_PP.mpr ⟨ht'z, ht'u⟩
  refine ⟨pull ψ H', w₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htL⟩
  · refine (mem_pull ψ H' hzC).mpr ?_
    rw [show ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) = z' from pic.psi_z]
    exact hz'H
  · refine (mem_pull ψ H' hu).mpr ?_
    rw [show ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) = u' from pic.psi_u]
    exact hu'H
  · intro h hh
    have hhC : h ∈ Cz z := pull_le ψ H' hh
    have hm : ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs) ∈ H' := (mem_pull ψ H' hhC).mp hh
    obtain ⟨c1, c2⟩ := mem_PP.mp (hT.1 hm)
    constructor
    · refine (pe_comm_iff ψ hhC hzC).mpr ?_
      show ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) =
        ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs)
      rw [pic.psi_z]; exact c1
    · refine (pe_comm_iff ψ hhC hu).mpr ?_
      show ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) =
        ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs)
      rw [pic.psi_u]; exact c2
  · exact ⟨(pullEquiv ψ hH'le).trans hT.2.1.some⟩
  · intro h hh
    have hhC : h ∈ Cz z := pull_le ψ H' hh
    have hm : ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs) ∈ H' := (mem_pull ψ H' hhC).mp hh
    obtain ⟨n1, n2⟩ := hT.2.2 _ hm
    have n1' : K₁'.map (MulAut.conj ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs)).toMonoidHom = K₁' := n1
    have n2' : K₂'.map (MulAut.conj ((ψ ⟨h, hhC⟩ : ↥(Cz z')) : Gs)).toMonoidHom = K₂' := n2
    constructor
    · rw [← pic.K₁_eq]
      show (pull ψ K₁').map (MulAut.conj h).toMonoidHom = pull ψ K₁'
      rw [pull_map_conj ψ hhC, n1']
    · rw [← pic.K₂_eq]
      show (pull ψ K₂').map (MulAut.conj h).toMonoidHom = pull ψ K₂'
      rw [pull_map_conj ψ hhC, n2']
  · show (pull ψ H').map (MulAut.conj t).toMonoidHom = pull ψ H'
    rw [pull_map_conj ψ ht]
    have : H'.map (MulAut.conj ((ψ ⟨t, ht⟩ : ↥(Cz z')) : Gs)).toMonoidHom = H' := by
      rw [pic.psi_t]; exact hPnorm t' ht'P
    rw [this]
  · have e : centralizer ((UU z u : Subgroup G) : Set G) =
        pull ψ (centralizer ((UU z' u' : Subgroup Gs) : Set Gs)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨h1, h2⟩ := mem_PP.mp hx
        have hxC : x ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr h1
        rw [mem_pull ψ _ hxC]
        refine mem_PP.mpr ⟨?_, ?_⟩
        · have h := (pe_comm_iff ψ hxC hzC).mp h1
          have h' : ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) =
              ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) := h
          rwa [pic.psi_z] at h'
        · have h := (pe_comm_iff ψ hxC hu).mp h2
          have h' : ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) =
              ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) := h
          rwa [pic.psi_u] at h'
      · intro hx
        have hxC : x ∈ Cz z := pull_le ψ _ hx
        have hm := (mem_pull ψ _ hxC).mp hx
        obtain ⟨c1, c2⟩ := mem_PP.mp hm
        refine mem_PP.mpr ⟨?_, ?_⟩
        · refine (pe_comm_iff ψ hxC hzC).mpr ?_
          show ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) =
            ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs)
          rw [pic.psi_z]; exact c1
        · refine (pe_comm_iff ψ hxC hu).mpr ?_
          show ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) =
            ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨x, hxC⟩ : ↥(Cz z')) : Gs)
          rw [pic.psi_u]; exact c2
    rw [e]
    exact pic.facts.P_two.of_equiv (pullEquiv ψ hP'le).symm
  · rw [← pic.K₁_eq]
    refine (mem_pull ψ K₁' hw₁C).mpr ?_
    rw [hψw₁]; exact hw'K
  · rw [pow_two]
    refine (pe_eq_iff ψ ((Cz z).mul_mem hw₁C hw₁C) hzC).mp ?_
    rw [pe_mul ψ hw₁C hw₁C]
    show ((ψ ⟨w₁, hw₁C⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨w₁, hw₁C⟩ : ↥(Cz z')) : Gs) =
      ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs)
    rw [hψw₁, pic.psi_z]; exact hw'sq
  · refine (pe_eq_iff ψ ((Cz z).mul_mem ((Cz z).mul_mem hw₁C hu) ((Cz z).inv_mem hw₁C))
      ((Cz z).mul_mem hu hzC)).mp ?_
    rw [pe_conj ψ hw₁C hu, pe_mul ψ hu hzC]
    show ((ψ ⟨w₁, hw₁C⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) *
        ((ψ ⟨w₁, hw₁C⟩ : ↥(Cz z')) : Gs)⁻¹ =
      ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) * ((ψ ⟨z, hzC⟩ : ↥(Cz z')) : Gs)
    rw [hψw₁, pic.psi_u, pic.psi_z]; exact hw'u

end Five66W

end CFSG.GH74.GLS.LU.Local.Five
