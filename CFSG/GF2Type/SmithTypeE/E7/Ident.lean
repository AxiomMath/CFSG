module

public import CFSG.GF2Type.SmithTypeE.DMod.Card
public import CFSG.GF2Type.SmithTypeE.DMod.StabOrbit
public import CFSG.GF2Type.SmithTypeE.E7.Compat
public import CFSG.LargeExtraspecial.S14SMHLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GF2Type.SmithTypeE.DMod

section TD6Card


theorem card_stabilizer_TD6_all (k : Fin 365211) :
    Nat.card ↥(MulAction.stabilizer ↥TD6 k) = Nat.card ↥TD6 / 365211 := by
  have horb : MulAction.orbit ↥TD6 k = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    obtain ⟨g, hg, hga⟩ := exists_mem_TD6_apply_zero_eq a
    obtain ⟨g', hg', hg'k⟩ := exists_mem_TD6_apply_zero_eq k
    refine ⟨⟨g * g'⁻¹, TD6.mul_mem hg (TD6.inv_mem hg')⟩, ?_⟩
    show (g * g'⁻¹) k = a
    rw [← hg'k]
    simp [hga]
  have h := (MulAction.stabilizer ↥TD6 k).card_mul_index
  rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card (α := Fin 365211),
    Fintype.card_fin] at h
  omega

end TD6Card

variable {G : Type} [Group G] [Finite G]

theorem card_eq_two_of_isPGroup_E7 {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hp : IsPGroup 2 K) : Nat.card K = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent K := hp.isNilpotent
  letI : CommGroup K := instCommGroupOfIsSimpleGroupOfIsNilpotent
  have hpr : (Nat.card K).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  rw [hn] at hpr ⊢
  rcases n with _ | n
  · exact absurd hpr (by norm_num)
  · rcases n with _ | n
    · rfl
    · exfalso
      have hd : 2 ∣ 2 ^ (n + 1 + 1) := dvd_pow_self 2 (by omega)
      rcases hpr.eq_one_or_self_of_dvd 2 hd with h | h
      · norm_num at h
      · have : 4 ≤ 2 ^ (n + 1 + 1) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega

theorem toMbar_injective_of_simple (S : Setting G) {K : Subgroup G} (hKM : K ≤ S.M)
    [IsSimpleGroup K] (h2 : 2 < Nat.card K) : Function.Injective (SMH.toMbar S hKM) := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  have hker : (SMH.toMbar S hKM).ker = ⊥ := by
    rcases (SMH.toMbar S hKM).normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hKQ : ∀ k : K, (k : G) ∈ S.QG := fun k => by
        have h1 : k ∈ (SMH.toMbar S hKM).ker := by rw [h]; exact mem_top _
        rw [MonoidHom.mem_ker] at h1
        exact (S.ρ_eq_one_iff ⟨k, hKM k.2⟩).mp (congrArg Subtype.val h1)
      have hp : IsPGroup 2 K := fun k => by
        obtain ⟨n, hn⟩ := S.isPGroup_QG ⟨k, hKQ k⟩
        exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
      rw [card_eq_two_of_isPGroup_E7 hp] at h2
      exact lt_irrefl _ h2
  exact (MonoidHom.ker_eq_bot_iff _).mp hker

section Ident


theorem nonempty_mulEquiv_omega_of_card_centralizer (hC : SmithE7Compat) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {K : Subgroup G} (hKM : K ≤ S.M) [IsSimpleGroup K] (h2 : 2 < Nat.card K)
    {x : G} (hxK : x ∈ K) (hx : IsConj S.z x) (hxQ : x ∉ S.QG)
    (hcard : 136982613196800 ≤ Nat.card ↥(K ⊓ centralizer ({x} : Set G))) :
    Nonempty (K ≃* timmesfeldOmegaPlus 6) := by
  classical
  obtain ⟨φ, ψ, -, -, -, h2', -⟩ := hC G S hw hU
  have hinj := toMbar_injective_of_simple S hKM h2
  let e₂ : K →* ↥TD6 := ψ.toMonoidHom.comp (SMH.toMbar S hKM)
  have he₂ : Function.Injective e₂ := ψ.injective.comp hinj
  let e : K →* Equiv.Perm (Fin 365211) := TD6.subtype.comp e₂
  have he : Function.Injective e := Subtype.val_injective.comp he₂
  have heT : ∀ k : K, e k ∈ TD6 := fun k => (e₂ k).2
  have hK''T : e.range ≤ TD6 := by rintro _ ⟨k, rfl⟩; exact heT k
  haveI : IsSimpleGroup e.range := (MonoidHom.ofInjective he).symm.isSimpleGroup
  obtain ⟨k₀, hk₀⟩ := h2' x (hKM hxK) hx hxQ
  have hex : e ⟨x, hxK⟩ = tvP k₀ := congrArg Subtype.val hk₀
  have hfix : ∀ a : K, (a : G) * x = x * a → e a k₀ = k₀ := fun a ha => by
    have hc : e a * tvP k₀ * (e a)⁻¹ = tvP k₀ := by
      rw [← hex, ← map_mul, ← map_inv, ← map_mul,
        show a * ⟨x, hxK⟩ * a⁻¹ = ⟨x, hxK⟩ from Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [ha]; group)]
    rw [mul_tvP_mul_inv (heT a)] at hc
    exact tvP_injective hc
  let f : ↥(K ⊓ centralizer ({x} : Set G)) → ↥(MulAction.stabilizer ↥TD6 k₀) := fun a =>
    ⟨⟨e ⟨a, (mem_inf.mp a.2).1⟩, heT _⟩, by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix _ (mem_centralizer_singleton_iff.mp (mem_inf.mp a.2).2)⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg
      (fun w : ↥(MulAction.stabilizer ↥TD6 k₀) => ((w : ↥TD6) : Equiv.Perm (Fin 365211))) hab
    have h1 := he this
    exact Subtype.ext (congrArg (fun w : K => (w : G)) h1)
  have hfs : Function.Surjective f := by
    refine (Function.Injective.bijective_of_nat_card_le hf ?_).2
    rw [card_stabilizer_TD6_all, card_TD6]
    have hord : CFSG.Open.ordD 6 2 / 365211 = 136982613196800 := by
      norm_num [CFSG.Open.ordD, Finset.prod_Icc_succ_top]
    rw [hord]
    exact hcard
  have hstab : ∀ g ∈ TD6, g k₀ = k₀ → g ∈ e.range := by
    intro g hg hgk
    obtain ⟨a, ha⟩ := hfs ⟨⟨g, hg⟩, by rw [MulAction.mem_stabilizer_iff]; exact hgk⟩
    exact ⟨_, congrArg (fun w : ↥(MulAction.stabilizer ↥TD6 k₀) =>
      ((w : ↥TD6) : Equiv.Perm (Fin 365211))) ha⟩
  have hT := eq_TD6_of_stabilizer_le hK''T k₀ hstab
  exact ⟨(MonoidHom.ofInjective he).trans ((MulEquiv.subgroupCongr hT).trans omegaTD6.symm)⟩

end Ident

end CFSG.GF2Type.SmithTypeE.E7
