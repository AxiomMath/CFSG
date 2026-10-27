module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUCosetAct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentU

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open Equiv CFSG.Sporadic.Th.Max3

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

@[expose] noncomputable def phiBar : QuasiQuotient u →* Perm (Fin 9) :=
  permNine.comp (d.rho4.prod d.rho5)

theorem phiBar_apply (g : QuasiQuotient u) : d.phiBar g = permNine (d.rho4 g, d.rho5 g) := rfl

theorem sign_rho4_eq (g : QuasiQuotient u) : Perm.sign (d.rho4 g) = Perm.sign (d.rho5 g) := by
  have hKn := d.oneComponent.centralizer_normal
  have hLK : ∀ {w : QuasiQuotient u}, w ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) →
      Perm.sign (d.rho4 w) = 1 := fun hw => by
    obtain ⟨l, hl, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    rw [map_mul, d.rho4_of_mem hl, one_mul]
    exact d.sign_rho4_of_mem_centralizer hk
  rcases d.mem_sup_or_mul_inv_mem_sup g with h | h
  · rw [hLK h, d.sign_rho5_of_mem_sup h]
  · have hg : g = g * d.yBar⁻¹ * d.yBar := by group
    have h4 : Perm.sign (d.rho4 g) = -1 := by
      rw [hg, map_mul, Perm.sign_mul, hLK h, d.rho4_yBar, fourList_facts.2.2, one_mul]
    have h5 : Perm.sign (d.rho5 g) = -1 := by
      rw [hg, map_mul, Perm.sign_mul, d.sign_rho5_of_mem_sup h, d.sign_rho5_yBar, one_mul]
    rw [h4, h5]

theorem sign_phiBar (g : QuasiQuotient u) : Perm.sign (d.phiBar g) = 1 := by
  rw [phiBar_apply, sign_permNine, d.sign_rho4_eq]
  exact Int.units_mul_self _

@[expose] noncomputable def phiBarA : QuasiQuotient u →* alternatingGroup (Fin 9) :=
  d.phiBar.codRestrict _ fun g => Perm.mem_alternatingGroup.mpr (d.sign_phiBar g)

theorem coe_phiBarA (g : QuasiQuotient u) :
    ((d.phiBarA g : alternatingGroup (Fin 9)) : Perm (Fin 9)) = d.phiBar g := rfl

theorem phiBar_quasiCentral : d.phiBar (quasiCentral u) = 1 := by
  rw [phiBar_apply, d.rho4_of_mem d.quasiCentral_mem,
    d.rho5_of_mem_centralizer d.quasiCentral_mem_centralizer, Prod.mk_one_one, map_one]

theorem phiBar_eq_one_iff {g : QuasiQuotient u} : d.phiBar g = 1 ↔ g = 1 ∨ g = quasiCentral u := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [phiBar_apply, ← map_one permNine, Prod.one_eq_mk] at h
    obtain ⟨h4, h5⟩ := Prod.mk.inj (permNine_injective h)
    exact d.eq_of_mem_centralizer_of_mem_lyGroup (d.mem_centralizer_of_rho5_eq_one h5)
      (d.mem_lyGroup_of_rho4 h4)
  · rintro (rfl | rfl)
    · exact map_one _
    · exact d.phiBar_quasiCentral

theorem phiBar_quasiBar : d.phiBar (quasiBar u) = altRep2 := by
  rw [phiBar_apply, d.rho4_quasiBar, d.rho5_of_mem_centralizer d.quasiBar_mem_centralizer,
    altRep2_eq_permNine]

theorem conj_quasiBar (g : QuasiQuotient u) :
    g * quasiBar u * g⁻¹ = quasiBar u ∨ g * quasiBar u * g⁻¹ = quasiBar u * quasiCentral u := by
  have hconj : g * quasiBar u * g⁻¹ ∈ Subgroup.zpowers (quasiBar u) :=
    (zpowers_quasiBar_normal u).conj_mem _ (Subgroup.mem_zpowers _) g
  have hord : orderOf (g * quasiBar u * g⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g) (quasiBar u)
    rw [MulAut.conj_apply] at h1
    rw [h1, d.orderOf_quasiBar]
  rcases d.eq_of_mem_zpowers_quasiBar hconj with h | h | h | h
  · rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  · rw [h, d.baseConfig.order] at hord
    exact absurd hord (by decide)
  · exact Or.inl h
  · exact Or.inr h

theorem phiBar_commute (g : QuasiQuotient u) : d.phiBar g * altRep2 = altRep2 * d.phiBar g := by
  have h : d.phiBar (g * quasiBar u * g⁻¹) = d.phiBar (quasiBar u) := by
    rcases d.conj_quasiBar g with h | h
    · rw [h]
    · rw [h, map_mul, d.phiBar_quasiCentral, mul_one]
  rw [map_mul, map_mul, map_inv, d.phiBar_quasiBar] at h
  calc d.phiBar g * altRep2 = d.phiBar g * altRep2 * (d.phiBar g)⁻¹ * d.phiBar g := by group
    _ = altRep2 * d.phiBar g := by rw [h]

theorem card_range_phiBar : Nat.card d.phiBar.range = 480 := by
  have hker : Nat.card d.phiBar.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, d.phiBar.ker.one_mem⟩, ⟨quasiCentral u, d.phiBar_quasiCentral⟩,
      fun h => d.quasiCentral_ne_one (congrArg Subtype.val h).symm, ?_⟩
    ext ⟨g, hg⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases d.phiBar_eq_one_iff.mp hg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h := Subgroup.card_mul_index d.phiBar.ker
  rw [Subgroup.index_ker, hker, d.card_quasiQuotient] at h
  omega

theorem range_phiBarA : d.phiBarA.range = Subgroup.centralizer {altRep2A} := by
  have hle : d.phiBarA.range ≤ Subgroup.centralizer {altRep2A} := by
    rintro _ ⟨g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (d.phiBar_commute g))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_centralizer_altRep2, ← d.card_range_phiBar]
  have : d.phiBarA.range.map (alternatingGroup (Fin 9)).subtype = d.phiBar.range := by
    rw [MonoidHom.map_range]
    rfl
  rw [← this, Subgroup.card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective]

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
