module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Odd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem D_le_normalizer_K_of_odd_F4 (h515 : Stmt5_1_15_F4) (hn : Odd n) :
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  rcases h515 G T M L V H B D n h.hyp h.notation59 h.module h.l34 with
    hD | ⟨h2, -⟩ | ⟨h24, -⟩ | ⟨h48, -⟩
  · exact hD
  all_goals exfalso
  · subst h2; exact absurd hn (by decide)
  · rcases h24 with rfl | rfl <;> exact absurd hn (by decide)
  · rcases h48 with rfl | rfl <;> exact absurd hn (by decide)

theorem D_le_centralizerModO2_of_odd_F4 (hI : L2OddInnerFact) (hL : L34SylowNormFact)
    (hF : L2TorusFact) (h515 : Stmt5_1_15_F4) (hn : Odd n) :
    D ≤ centralizerModO2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  have hDK := h.D_le_normalizer_K_of_odd_F4 h515 hn
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    h.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI hn)
  have hTH : T ≤ H := h.hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf hTH) (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  set π : ↥K →* O2Q K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS := isSylowTwoOf_map_hom' hTK π
  rw [MonoidHom.range_eq_top_of_surjective π hπs] at hS
  set S := ((T ⊓ K).subgroupOf K).map π with hSdef
  have hcop := h.coprime_card_D_of_odd hF hn
  intro d hd
  have hdK : d ∈ Subgroup.normalizer (K : Set G) := hDK hd
  set φ := quotConjAut K ⟨d, hdK⟩ with hφ

  have hφS : S.map φ.toMonoidHom = S := by
    have hdT : d ∈ Subgroup.normalizer (T : Set G) := hDT hd
    have hle : S.map φ.toMonoidHom ≤ S := by
      rintro _ ⟨_, ⟨x, hx', rfl⟩, rfl⟩
      have hx : (x : G) ∈ T ⊓ K := hx'
      have hxK : d * (x : G) * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdK x).mp x.2
      refine ⟨⟨d * x * d⁻¹, hxK⟩, ?_, ?_⟩
      · show d * (x : G) * d⁻¹ ∈ T ⊓ K
        exact ⟨(Subgroup.mem_normalizer_iff.mp hdT x).mp hx.1, hxK⟩
      · show π ⟨d * x * d⁻¹, hxK⟩ = quotConjAut K ⟨d, hdK⟩ (π x)
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, quotConjAut_mk]
    have hinj : Function.Injective φ.toMonoidHom := φ.injective
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hinj])

  have hord : Nat.Coprime (orderOf φ) 6 := by
    have h1 : orderOf φ ∣ orderOf (⟨d, hd⟩ : ↥D) := by
      apply orderOf_dvd_of_pow_eq_one
      have : (⟨d, hdK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf (⟨d, hd⟩ : ↥D) = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one (⟨d, hd⟩ : ↥D)
        simp
      rw [hφ, ← map_pow, this, map_one]
    exact Nat.Coprime.coprime_dvd_left (h1.trans (orderOf_dvd_natCard _)) hcop
  have hφ1 := hL (O2Q K) h.l34 S hS φ hφS hord
  refine ⟨hdK, normalizer_le_normalizer_pCoreOf 2 K hdK, fun u hu => ?_⟩
  exact commutator_mem_of_quotConjAut_eq_one hφ1 ⟨u, hu⟩

end Hyp5_1_14

end CFSG.Quasithin.H13
