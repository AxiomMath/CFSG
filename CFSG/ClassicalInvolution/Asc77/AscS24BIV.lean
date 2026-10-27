module

public import CFSG.ClassicalInvolution.Asc77.AscS24BFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7L4
public import CFSG.ClassicalInvolution.Asc77.AscT7K2
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RConj

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem ne_conj_z {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J) {zJ : G}
    (hzJ : IsUniqueInvolution J zJ) {t : G} (htT : T ≤ Subgroup.centralizer ({t} : Set G))
    (ht : t ≠ zJ) (g : G) : g * z * g⁻¹ ≠ t := by
  intro hg
  have hst := C.hs.stand
  have hΩ := hst.hyp
  have hJ' : conjSub g K ∈ Ω := hΩ.conjInvariant g K hst.mem
  have hzJ' : IsUniqueInvolution (conjSub g K) t := hg ▸ C.hzK.conj g
  by_cases hJJ : J = conjSub g K
  · subst hJJ
    exact ht (hzJ'.eq hzJ)
  · have hTR : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hT
    have h8 := hΩ.eight_le_of_mem_RSet hst.odd hTR
    have hTN := hΩ.le_normalizer_of_le_centralizer hst.odd hst.five hJ' hJ (Ne.symm hJJ) hzJ'
      hT.1 hT.2.1 (by omega) htT
    have hnbr : J ∈ omegaNbr Ω (conjSub g K) := ⟨hJ, hJJ, T, hTR, hT.1, hTN⟩
    have hperp : J ∈ KPerp Ω (conjSub g K) := Set.mem_insert_of_mem _ hnbr
    rw [T7L.kPerp_conj_pair hΩ.conjInvariant C.hs.perp g] at hperp
    rcases hperp with h | h
    · exact hJJ h
    · have h2 : IsUniqueInvolution J (g * z * g⁻¹) := h ▸ C.hzK'.conj g
      exact ht (hg ▸ (h2.eq hzJ))

include C in
theorem conj_z_of_mem_sup [IsSimpleGroup G] {t : G} (ht : t ∈ K ⊔ K') (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : ∃ g : G, g * z * g⁻¹ = t := by
  by_cases htz : t = z
  · exact ⟨1, by rw [htz]; group⟩
  obtain ⟨g₀, -, hg₀⟩ := T7C2.exists_g0 C.hs C.hd
  obtain ⟨c, -, hc⟩ := T7K.exists_conj_of_involution C.hs C.hd.hu.1 C.hd.hu.2.2.2.1
    C.hd.hu.2.2.2.2 C.hd.hu.2.2.1 ht ht1 htz ht2
  refine ⟨c * g₀⁻¹, ?_⟩
  rw [← hc, ← hg₀]
  group

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
