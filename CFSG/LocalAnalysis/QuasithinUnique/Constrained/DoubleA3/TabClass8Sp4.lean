module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabClass8Split
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabClass8Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Syl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519
open CFSG.QuasithinUnique.Id2519.Tab
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b

theorem tabClass8Sp4 : TabClass8Sp4 := by
  intro G _ _ X K t hXq htN ht2 hcomm hKc hpat P hP _
  obtain ⟨⟨eK⟩, hmodel⟩ := hpat
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have hF22 : Nat.card F = 2 ^ 2 := by simpa using hcard
  have hF4 : Nat.card F = 4 := by rw [hF22]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF22])
  let e' : ↥X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) := e
  let ψ : ↥X ≃* antiSp F := e'.trans (antiProjEquiv F).symm
  have hψe : ∀ x, antiProjEquiv F (ψ x) = e' x := fun x =>
    (antiProjEquiv F).apply_symm_apply (e' x)
  have hZ : Subgroup.center ↥X = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : ψ a ∈ Subgroup.center (antiSp F) := (mem_center_iff_equiv ψ a).2 ha
    have h2 : (MulAut.conj (ψ a) : MulAut (antiSp F)) = 1 := by
      apply MulEquiv.ext
      intro g
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hcg := Subgroup.mem_center_iff.mp h1 g
      calc ψ a * g * (ψ a)⁻¹ = (g * ψ a) * (ψ a)⁻¹ := by rw [hcg]
        _ = g := by group
    have h3 : ψ a = 1 :=
      conj_injective (h2.trans (map_one (MulAut.conj : antiSp F →* MulAut (antiSp F))).symm)
    exact Subgroup.mem_bot.2 (ψ.injective (by rw [h3, map_one]))
  set π : ↥X →* antiSp F := ψ.toMonoidHom with hπdef
  have hπapp : ∀ x, π x = ψ x := fun x => rfl
  have hπ : Function.Surjective π := ψ.surjective
  have hker : π.ker = Subgroup.center ↥X := by
    rw [hZ]
    exact (MonoidHom.ker_eq_bot_iff π).2 ψ.injective
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hKc.1
  have hKX : K ≤ X := hKXt.trans inf_le_left
  have hα2 := quotAct_mul_self π hπ hker htN ht2
  have hα1 := quotAct_ne_one π hπ hker htN hXq hcomm
  set α := quotAct π hπ hker htN with hαdef
  have hfixK : ∀ k : ↥K, α (π (Subgroup.inclusion hKX k)) = π (Subgroup.inclusion hKX k) := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply π hπ hker htN _ _ hy
  have hKcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hαinn : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp F) := by
    rintro ⟨g, hg⟩
    have hg2 : g * g = 1 := by
      apply conj_injective (K := F)
      rw [map_mul, map_one, hg]
      exact hα2
    have hg1 : g ≠ 1 := by
      rintro rfl
      apply hα1
      rw [← hg, map_one]
    have hcommK : ∀ k : ↥K,
        g * ψ (Subgroup.inclusion hKX k) = ψ (Subgroup.inclusion hKX k) * g := by
      intro k
      have h1 := hfixK k
      rw [← hg, MulAut.conj_apply] at h1
      calc g * ψ (Subgroup.inclusion hKX k)
          = (g * π (Subgroup.inclusion hKX k) * g⁻¹) * g := by rw [hπapp]; group
        _ = ψ (Subgroup.inclusion hKX k) * g := by rw [h1, hπapp]
    let f : ↥K →* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
      e'.toMonoidHom.comp (Subgroup.inclusion hKX)
    have hf : Function.Injective f := e'.injective.comp (Subgroup.inclusion_injective hKX)
    have h9 : 9 ∣ Nat.card f.range := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hKcard]
      norm_num
    have hs : (antiProjEquiv F g) ^ 2 = 1 := by rw [← map_pow, pow_two, hg2, map_one]
    have hc : ∀ k ∈ f.range, antiProjEquiv F g * k = k * antiProjEquiv F g := by
      rintro _ ⟨k, rfl⟩
      have h1 := congrArg (antiProjEquiv F) (hcommK k)
      rw [map_mul, map_mul, hψe] at h1
      exact h1
    have h1 := USp4.eq_one_of_centralizes_of_nine_dvd hF4 h9 hs hc
    exact hg1 ((antiProjEquiv F).injective (by rw [h1, map_one]))
  obtain ⟨c, hc⟩ := outer_involution_conj (n := 2) le_rfl hF22 α hα2 hαinn
  have hfix : fixedSubgroup α =
      (fixedSubgroup (minorAut F ^ 2)).map (MulAut.conj c).toMonoidHom := by
    rw [hc]
    exact fixedSubgroup_conj (MulAut.conj c) (minorAut F ^ 2)
  obtain ⟨k, hk, lift, hkcard, hlift, hrange⟩ :=
    exists_even_fixed (K := F) (m := 1) le_rfl (by rw [hF22])
  have hkcard' : Nat.card k = 2 := by simpa using hkcard
  have hrange' : lift.range = fixedSubgroup (minorAut F ^ 2) := by simpa using hrange
  have hB : Nat.card (fixedSubgroup α) = 720 := by
    rw [hfix,
      Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective,
      ← hrange',
      ← Nat.card_congr (MonoidHom.ofInjective hlift).toEquiv, card_antiSp hkcard']
    norm_num
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  have hAX : (C ⊓ P) ≤ X := inf_le_right.trans hP.1
  let f0 : ↥(C ⊓ P) →* antiSp F := π.comp (Subgroup.inclusion hAX)
  have hf0 : ∀ a, f0 a ∈ fixedSubgroup α := by
    intro a
    have hat : (a : G) * t = t * (a : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp a.2.1
    have hy : ((Subgroup.inclusion hAX a : X) : G) =
        t * ((Subgroup.inclusion hAX a : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (a : G) = (a * t) * t⁻¹ := by group
        _ = (t * a) * t⁻¹ := by rw [hat]
    exact quotAct_apply π hπ hker htN _ _ hy
  let f1 : ↥(C ⊓ P) →* ↥(fixedSubgroup α) := f0.codRestrict (fixedSubgroup α) hf0
  have hf1 : Function.Injective f1 := by
    intro a b hab
    exact (ψ.injective.comp (Subgroup.inclusion_injective hAX)) (congrArg Subtype.val hab)
  have hX : Nat.card ↥X = 2 ^ 8 * 3825 := by
    rw [Nat.card_congr ψ.toEquiv, card_antiSp hF4]
    norm_num
  exact Class8.eight_le_relIndex C hP f1 hf1 (e := 4) (u := 45) (by norm_num) (by rw [hB]; norm_num)
    (m := 8) (v := 3825) hX (by norm_num)

end CFSG.QuasithinUnique.DoubleA3
