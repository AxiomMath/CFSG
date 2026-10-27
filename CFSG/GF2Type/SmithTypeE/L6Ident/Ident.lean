module

public import CFSG.GF2Type.SmithTypeE.L6Ident.StabOrbit
public import CFSG.GF2Type.SmithTypeE.L6.Compat
public import CFSG.GF2Type.SmithTypeE.E6Order
public import CFSG.LargeExtraspecial.S14SMHLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.GF2Type.SmithTypeE.L6
  CFSG.GF2Type.SmithTypeE.LMod
open scoped MatrixGroups

section T6Card


theorem card_T6 : Nat.card T6 = 20158709760 := by
  rw [← Nat.card_congr pslT6.toEquiv, card_PSL_six_two]

theorem card_stabilizer_T6 (k : Fin 1953) :
    Nat.card (MulAction.stabilizer T6 k) = 10321920 := by
  have horb : MulAction.orbit T6 k = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    obtain ⟨g, hg, hga⟩ := exists_mem_T6_apply_zero_eq a
    obtain ⟨g', hg', hg'k⟩ := exists_mem_T6_apply_zero_eq k
    refine ⟨⟨g * g'⁻¹, T6.mul_mem hg (T6.inv_mem hg')⟩, ?_⟩
    show (g * g'⁻¹) k = a
    rw [← hg'k]
    simp [hga]
  have h := (MulAction.stabilizer T6 k).card_mul_index
  rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card (α := Fin 1953),
    Fintype.card_fin, card_T6] at h
  omega

end T6Card

variable {G : Type} [Group G] [Finite G]

theorem card_eq_two_of_isPGroup {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
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

theorem toMbar_injective_of_simple (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {K : Subgroup G} (hKM : K ≤ S.M)
    [IsSimpleGroup K] (h2 : 2 < Nat.card K) :
    Function.Injective (SMH.toMbar S hKM) ∧ (SMH.toMbar S hKM).range ≤ Mbar0 S := by
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
      rw [card_eq_two_of_isPGroup hp] at h2
      exact lt_irrefl _ h2
  have hinj : Function.Injective (SMH.toMbar S hKM) := (MonoidHom.ker_eq_bot_iff _).mp hker
  refine ⟨hinj, ?_⟩
  have hidx : (Mbar0 S).index ∣ 2 := (card_M_of_L6 S hw hU).1
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  rcases ((QuotientGroup.mk' (Mbar0 S)).comp (SMH.toMbar S hKM)).normal_ker.eq_bot_or_eq_top
    with h | h
  · exfalso
    have h1 := Nat.card_le_card_of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp h)
    have h2' : (Mbar0 S).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    rw [← Subgroup.index_eq_card] at h1
    omega
  · rintro _ ⟨n, rfl⟩
    have h1 : n ∈ ((QuotientGroup.mk' (Mbar0 S)).comp (SMH.toMbar S hKM)).ker := by
      rw [h]
      exact mem_top _
    rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1

section Ident


theorem nonempty_mulEquiv_psl_of_card_centralizer (hC : SmithL6Compat) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    {K : Subgroup G} (hKM : K ≤ S.M) [IsSimpleGroup K] (h2 : 2 < Nat.card K)
    {x : G} (hxK : x ∈ K) (hx : IsConj S.z x) (hxQ : x ∉ S.QG)
    (hcard : 10321920 ≤ Nat.card ↥(K ⊓ centralizer ({x} : Set G))) :
    Nonempty (K ≃* PSL(6, ZMod 2)) := by
  classical
  obtain ⟨φ, ψ, -, -, -, h2', -⟩ := hC G S hw hU
  obtain ⟨hinj, hle⟩ := toMbar_injective_of_simple S hw hU hKM h2
  let e₁ : K →* Mbar0 S := (SMH.toMbar S hKM).codRestrict (Mbar0 S) (fun k => hle ⟨k, rfl⟩)
  have he₁ : Function.Injective e₁ := fun a b hab => hinj (congrArg Subtype.val hab)
  let e₂ : K →* T6 := ψ.toMonoidHom.comp e₁
  have he₂ : Function.Injective e₂ := ψ.injective.comp he₁
  let e : K →* Equiv.Perm (Fin 1953) := T6.subtype.comp e₂
  have he : Function.Injective e := Subtype.val_injective.comp he₂
  have heT : ∀ k : K, e k ∈ T6 := fun k => (e₂ k).2
  have hK''T : e.range ≤ T6 := by rintro _ ⟨k, rfl⟩; exact heT k
  haveI : IsSimpleGroup e.range := (MonoidHom.ofInjective he).symm.isSimpleGroup
  obtain ⟨k₀, h0, hk₀⟩ := h2' x (hKM hxK) hx hxQ
  have hex : e ⟨x, hxK⟩ = tvP k₀ := congrArg Subtype.val hk₀
  have hfix : ∀ a : K, (a : G) * x = x * a → e a k₀ = k₀ := fun a ha => by
    have hc : e a * tvP k₀ * (e a)⁻¹ = tvP k₀ := by
      rw [← hex, ← map_mul, ← map_inv, ← map_mul,
        show a * ⟨x, hxK⟩ * a⁻¹ = ⟨x, hxK⟩ from Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [ha]; group)]
    rw [mul_tvP_mul_inv (heT a)] at hc
    exact tvP_injective hc
  let f : ↥(K ⊓ centralizer ({x} : Set G)) → ↥(MulAction.stabilizer T6 k₀) := fun a =>
    ⟨⟨e ⟨a, (mem_inf.mp a.2).1⟩, heT _⟩, by
      rw [MulAction.mem_stabilizer_iff]
      exact hfix _ (mem_centralizer_singleton_iff.mp (mem_inf.mp a.2).2)⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg (fun w : ↥(MulAction.stabilizer T6 k₀) => ((w : T6) : Equiv.Perm (Fin 1953)))
      hab
    have h1 := he this
    exact Subtype.ext (congrArg (fun w : K => (w : G)) h1)
  have hfs : Function.Surjective f := by
    refine (Function.Injective.bijective_of_nat_card_le hf ?_).2
    rw [card_stabilizer_T6]
    exact hcard
  have hstab : ∀ g ∈ T6, g k₀ = k₀ → g ∈ e.range := by
    intro g hg hgk
    obtain ⟨a, ha⟩ := hfs ⟨⟨g, hg⟩, by rw [MulAction.mem_stabilizer_iff]; exact hgk⟩
    exact ⟨_, congrArg (fun w : ↥(MulAction.stabilizer T6 k₀) =>
      ((w : T6) : Equiv.Perm (Fin 1953))) ha⟩
  have hT := eq_T6_of_stabilizer_le hK''T k₀ hstab
  exact ⟨(MonoidHom.ofInjective he).trans ((MulEquiv.subgroupCongr hT).trans pslT6.symm)⟩

end Ident

end CFSG.GF2Type.SmithTypeE.L6Ident
