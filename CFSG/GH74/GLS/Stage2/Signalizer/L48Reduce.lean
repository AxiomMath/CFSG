module

public import CFSG.GH74.GLS.Stage2.Signalizer.L48Glue
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One
public import CFSG.GH74.GLS.Stage2.Signalizer.L48StarStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Bender.Thm2
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section TypeOne

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem transOn_of_typeOne (ctx : Stage2Ctx G z k S) (hone : TypeOneCase G k) {U : Subgroup G}
    (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U) (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) : TransOn U := by
  by_cases hk : k = Kind.m12
  · subst hk
    have hd := ctx.data
    cases hd with
    | m12 h =>
      obtain ⟨U', -, -, -, -, -, huniq, hAut⟩ := h.four_group
      have hUU : U = U' := huniq U hUS hU4 hUn
      subst hUU
      exact transOn_of_three_dvd hU4 (by rw [hAut]; exact ⟨2, rfl⟩)
  · have hone' : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := hone.resolve_right hk
    obtain ⟨-, hAut⟩ := ctx.prop22a hone' (not_comm_S ctx) U hUS hU4 hUn
    exact transOn_of_three_dvd hU4 (by rw [hAut]; exact ⟨2, rfl⟩)

end TypeOne

theorem lemma4_8w_of_star (h19 : B_signalizer_19_9) (hstar : Star48) : Lemma4_8w := by
  intro G _ _ z k S ctx hone t H X p hU4 hUS hUn hCt htZ hSig _
  have hz1 : z ≠ 1 := fun h => by
    have := ctx.orderOf_z
    rw [h, orderOf_one] at this
    omega
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [ctx.orderOf_z] at this
    simpa [pow_two] using this
  set U : Subgroup G := zpowers z ⊔ zpowers t with hU
  have hzU : z ∈ U := Subgroup.mem_sup_left (mem_zpowers z)
  have htU : t ∈ U := Subgroup.mem_sup_right (mem_zpowers t)
  have ht2 : t * t = 1 := sq_eq_one_of_isFour hU4 htU
  have hzt : z * t = t * z := mul_comm_of_isFour hU4 hzU htU
  have hcardU : Nat.card ↥U = 4 := hU4.2
  have hz2o : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, ctx.orderOf_z]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [hU, Subgroup.zpowers_one_eq_bot, sup_bot_eq, hz2o] at hcardU
    omega
  have htz : t ≠ z := by
    rintro rfl
    rw [hU, sup_idem, hz2o] at hcardU
    omega
  obtain ⟨n, hnN, hnz⟩ := transOn_of_typeOne ctx hone hUS hU4 hUn z hzU hz1 t htU ht1
  have hnU' : ∀ u ∈ U, n⁻¹ * u * n ∈ U := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnN) u).mp hu
    simpa using this
  set φ : G ≃* G := MulAut.conj n⁻¹ with hφ
  have hφx : ∀ x, φ x = n⁻¹ * x * n := fun x => by simp [hφ]
  have hφt : φ t = z := by rw [hφx, ← hnz]; group
  set H' : Subgroup G := H.map φ.toMonoidHom with hH'
  set X' : Subgroup G := X.map φ.toMonoidHom with hX'
  have hmemH' : ∀ x, x ∈ H' ↔ n * x * n⁻¹ ∈ H := fun x => by
    rw [hH', hφ, mem_map_conj_iff]
    simp
  have hzstar : z ∈ zStar H' := by
    have := zStar_map_of_mem φ htZ
    rwa [hφt] at this
  have hc : CentMod H' z := centMod_of_mem_zStar hzstar
  have hcen : Cen z ≤ H' := by
    intro c hc'
    rw [hmemH']
    apply hCt
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc'
    calc n * c * n⁻¹ * t = n * (c * z) * n⁻¹ := by rw [← hnz]; group
      _ = n * (z * c) * n⁻¹ := by rw [hcz]
      _ = t * (n * c * n⁻¹) := by rw [← hnz]; group
  set t₂ : G := n⁻¹ * z * n with ht₂def
  have ht₂U : t₂ ∈ U := hnU' z hzU
  have ht₂2 : t₂ * t₂ = 1 := sq_eq_one_of_isFour hU4 ht₂U
  have hzt₂ : z * t₂ = t₂ * z := mul_comm_of_isFour hU4 hzU ht₂U
  have hnt₂ : n * t₂ * n⁻¹ = z := by rw [ht₂def]; group
  have ht₂1 : t₂ ≠ 1 := by
    intro h1
    apply hz1
    rw [← hnt₂, h1]
    group
  have hzt₂ne : z ≠ t₂ := by
    intro h1
    apply htz
    rw [← hnz]
    calc n * z * n⁻¹ = n * t₂ * n⁻¹ := by rw [← h1]
      _ = z := hnt₂
  have ht₂mem : t₂ ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hzt₂.symm
  have hXH' : X' ≤ H' := Subgroup.map_mono hSig.A.X_le
  have hXp' : IsPGroup p ↥X' := hSig.A.pgroup.map _
  have hXinv' : ∀ c ∈ H', c ∈ centralizer ({t₂} : Set G) → c ∈ normalizer (X' : Set G) := by
    intro c hcH hct
    have hct' : c * t₂ = t₂ * c := Subgroup.mem_centralizer_singleton_iff.mp hct
    have h1 : n * c * n⁻¹ ∈ H := (hmemH' c).mp hcH
    have h2 : n * c * n⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * c * n⁻¹ * z = n * (c * t₂) * n⁻¹ := by rw [← hnt₂]; group
        _ = n * (t₂ * c) * n⁻¹ := by rw [hct']
        _ = z * (n * c * n⁻¹) := by rw [← hnt₂]; group
    have h3 := hSig.A.inv _ h1 h2
    have h4 := (mem_normalizer_map_iff φ X (n * c * n⁻¹)).mpr h3
    have h5 : φ (n * c * n⁻¹) = c := by rw [hφx]; group
    rwa [h5] at h4
  have hcomm' : ⁅X', zpowers t₂⁆ = X' := by
    have h1 : zpowers t₂ = (zpowers z).map φ.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp [hφx, ht₂def]
    rw [h1, hX', ← Subgroup.map_commutator, hSig.A.comm]
  have hfour := eq_zpowers_sup_of_isFour hU4 hzU ht₂U hz1 ht₂1 hzt₂ne
  have hU4' : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t₂) := by rw [← hfour]; exact hU4
  have hUS' : zpowers z ⊔ zpowers t₂ ≤ S := by rw [← hfour]; exact hUS
  have hUn' : ∀ s ∈ S, ∀ u ∈ zpowers z ⊔ zpowers t₂, s * u * s⁻¹ ∈ zpowers z ⊔ zpowers t₂ := by
    rw [← hfour]; exact hUn
  have hodd : X' ≤ pPrimeCoreOf 2 H' :=
    le_oddCore_of_star hz2 ht₂2 hcen hc ht₂mem hXH' hXp' hXinv' hcomm'
      (fun Y hY hN hC => hstar G z k S ctx t₂ ht₂mem p hSig.A.prime hSig.A.odd hU4' hUS' hUn' Y hY hN hC)
  have hXodd : X ≤ pPrimeCoreOf 2 H := by
    intro x hx
    have h1 : φ x ∈ X' := Subgroup.mem_map_of_mem _ hx
    have h2 := hodd h1
    rw [hH', pPrimeCoreOf_map] at h2
    exact (Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).mp h2
  exact (signalizer_sub h19 ctx.orderOf_z hSig).2 hXodd

end CFSG.GH74.GLS.Stage2.Signalizer.L48
