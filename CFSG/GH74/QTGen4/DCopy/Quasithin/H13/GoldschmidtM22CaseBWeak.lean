module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBTriv

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace BCtx_F4

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)

include c in
theorem conj_V_eq (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) {g' : G}
    (hle : conjSubgroup V g' ≤ T) : conjSubgroup V g' = V := by
  have hA : conjSubgroup V g' ∈ gammaSet V 0 T := ⟨hle, g', le_rfl, mQuot_self _⟩
  have hw : conjSubgroup V g' ≤ wClos V 0 T :=
    le_iSup₂ (f := fun A (_ : A ∈ gammaSet V 0 T) => A) _ hA
  have hQ' : conjSubgroup V g' ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp ((c.hl.h627 G T M L V c.h).1 (hw hx))).2
  have hVQ : V ≤ Subgroup.centralizer (V : Set G) := V_le_centralizer_V c.h
  have hV16 : Nat.card V = 16 := KData.card_V c.h
  have hV'16 : Nat.card (conjSubgroup V g') = 16 := by
    rw [CFSG.QuasithinUnique.C5.card_conjSubgroup, hV16]
  have hQ32 : Nat.card (Subgroup.centralizer (V : Set G)) = 32 := by
    have h1 := Subgroup.relIndex_mul_card (H := V) (K := Subgroup.centralizer (V : Set G))
    rw [inf_eq_left.mpr hVQ, h2, hV16] at h1
    omega
  have hV'2 : (conjSubgroup V g').relIndex (Subgroup.centralizer (V : Set G)) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := conjSubgroup V g')
      (K := Subgroup.centralizer (V : Set G))
    rw [inf_eq_left.mpr hQ', hV'16, hQ32] at h1
    omega
  have h3 : (V ⊓ conjSubgroup V g').relIndex V ≤ 2 := by
    have h4 : (V ⊓ conjSubgroup V g').relIndex (Subgroup.centralizer (V : Set G)) ≤
        V.relIndex (Subgroup.centralizer (V : Set G)) *
          (conjSubgroup V g').relIndex (Subgroup.centralizer (V : Set G)) :=
      Subgroup.relIndex_inf_le
    have h5 := Subgroup.relIndex_mul_relIndex (V ⊓ conjSubgroup V g') V
      (Subgroup.centralizer (V : Set G)) inf_le_left hVQ
    rw [h2, hV'2] at h4
    rw [h2] at h5
    omega
  have h6 : (V ⊓ conjSubgroup V g').relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain h7 | h7 : (V ⊓ conjSubgroup V g').relIndex V = 1 ∨
      (V ⊓ conjSubgroup V g').relIndex V = 2 := by omega
  · have hle' : V ≤ conjSubgroup V g' := fun x hx =>
      (Subgroup.mem_inf.mp (Subgroup.relIndex_eq_one.mp h7 hx)).2
    exact (Subgroup.eq_of_le_of_card_ge hle' (by rw [hV'16, hV16])).symm
  · exact (c.hl.h625 G T M L V c.h).2.2.2.2.2.2 (V ⊓ conjSubgroup V g') inf_le_left h7 g'
      inf_le_right

include c in
theorem weakly_closed_Q (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) :
    IsWeaklyClosedIn (Subgroup.centralizer (V : Set G)) T := by
  intro g' hle
  have hVQ : V ≤ Subgroup.centralizer (V : Set G) := V_le_centralizer_V c.h
  have h1 : conjSubgroup V g' ≤ T := fun x hx =>
    hle (mem_conjSubgroup_iff.mpr (hVQ (mem_conjSubgroup_iff.mp hx)))
  rw [CFSG.QuasithinUnique.C5.conjSubgroup_centralizer, c.conj_V_eq h2 h1]

include c in
theorem normalizer_Q_le_N (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) {n : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G)) :
    n ∈ Subgroup.normalizer (V : Set G) := by
  have hQn : conjSubgroup (Subgroup.centralizer (V : Set G)) n = Subgroup.centralizer (V : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hn
  have hVQ : V ≤ Subgroup.centralizer (V : Set G) := V_le_centralizer_V c.h
  have h1 : conjSubgroup V n ≤ T := fun x hx =>
    c.Q_le_T (hQn ▸ mem_conjSubgroup_iff.mpr (hVQ (mem_conjSubgroup_iff.mp hx)))
  exact conjSubgroup_eq_iff_mem_normalizer.mp (c.conj_V_eq h2 h1)

include c in
theorem not_conj_V (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) {r : G}
    (hrQ : r ∈ Subgroup.centralizer (V : Set G)) (hrV : r ∉ V) (g' v : G) (hv : v ∈ V) :
    g'⁻¹ * r * g' ≠ v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hconj
  have hrC : r ∈ Subgroup.centralizer (Subgroup.centralizer (V : Set G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => c.Q_comm hh hrQ
  have hvC : v ∈ Subgroup.centralizer (Subgroup.centralizer (V : Set G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (Subgroup.mem_centralizer_iff.mp hh v hv).symm
  obtain ⟨n, hnQ, hn⟩ := burnside_fusion_lemma_centralizer (c.h.sylow.1.toSylow c.h.sylow.2)
    c.Q_le_T (c.weakly_closed_Q h2) hrC hvC hconj
  have hnV : n ∈ Subgroup.normalizer (V : Set G) := c.normalizer_Q_le_N h2 hnQ
  apply hrV
  have : r = n * v * n⁻¹ := by rw [← hn]; group
  rw [this]
  exact conj_mem hnV hv

end BCtx_F4

end CFSG.Quasithin.H13.GM22
