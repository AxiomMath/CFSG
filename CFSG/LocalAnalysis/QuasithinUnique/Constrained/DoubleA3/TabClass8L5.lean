module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabClass8Split
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabClass8Orth
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabClass8Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Key

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519
open CFSG.QuasithinUnique.Id2519.Tab CFSG.QuasithinUnique.Id2519.Tab.L5
open scoped Matrix

theorem tabClass8L5 : TabClass8L5 := by
  intro G _ _ X K t hXq htN ht2 hcomm hKc hpat P hP _
  obtain ⟨⟨eK⟩, hmodel⟩ := hpat
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have hcard2 : Nat.card F = 2 := by simpa using hcard
  obtain ⟨φ⟩ : Nonempty (↥X ≃* S) :=
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 5 F hcard2)⟩
  have hZ : Subgroup.center ↥X = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : φ a ∈ Subgroup.center S := (mem_center_iff_equiv φ a).2 ha
    rw [center_S, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (φ.injective (by rw [h1, map_one]))
  set π : ↥X →* S := φ.toMonoidHom with hπdef
  have hπapp : ∀ x, π x = φ x := fun x => rfl
  have hπ : Function.Surjective π := φ.surjective
  have hker : π.ker = Subgroup.center ↥X := by
    rw [hZ]
    exact (MonoidHom.ker_eq_bot_iff π).2 φ.injective
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hKc.1
  have hKX : K ≤ X := hKXt.trans inf_le_left
  have hα2 := quotAct_mul_self π hπ hker htN ht2
  have hα1 := quotAct_ne_one π hπ hker htN hXq hcomm
  have hfixK : ∀ k : ↥K, quotAct π hπ hker htN (π (Subgroup.inclusion hKX k)) =
      π (Subgroup.inclusion hKX k) := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact quotAct_apply π hπ hker htN _ _ hy
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hKcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 (by rw [hKcard]; norm_num)
  have hz : orderOf (π (Subgroup.inclusion hKX z₀)) = 5 := by
    rw [orderOf_injective π φ.injective, orderOf_injective _ (Subgroup.inclusion_injective hKX),
      hz₀]
  set τ := quotAct π hπ hker htN with hτdef
  obtain ⟨Q, hQ⟩ := key_involution τ hα2 hα1 _ hz (hfixK z₀)
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  have hAX : (C ⊓ P) ≤ X := inf_le_right.trans hP.1
  let κ : ↥(C ⊓ P) →* S :=
    (MulAut.conj Q⁻¹).toMonoidHom.comp (π.comp (Subgroup.inclusion hAX))
  have hκ : Function.Injective κ :=
    (MulAut.conj Q⁻¹).injective.comp (φ.injective.comp (Subgroup.inclusion_injective hAX))
  have horth : ∀ a, (κ a : M5) * (κ a : M5)ᵀ = 1 := by
    intro a
    apply orth_of_dl_fixed
    have hat : (a : G) * t = t * (a : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp a.2.1
    have hy : ((Subgroup.inclusion hAX a : X) : G) =
        t * ((Subgroup.inclusion hAX a : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (a : G) = (a * t) * t⁻¹ := by group
        _ = (t * a) * t⁻¹ := by rw [hat]
    have hfix : τ (π (Subgroup.inclusion hAX a)) = π (Subgroup.inclusion hAX a) :=
      quotAct_apply π hπ hker htN _ _ hy
    set g : S := π (Subgroup.inclusion hAX a) with hg
    have h1 : g = Q * dl (Q⁻¹ * g * Q) * Q⁻¹ := by
      have := hQ g
      rw [hfix] at this
      exact this
    have h2 : dl (Q⁻¹ * g * Q) = Q⁻¹ * g * Q := by
      calc dl (Q⁻¹ * g * Q) = Q⁻¹ * (Q * dl (Q⁻¹ * g * Q) * Q⁻¹) * Q := by group
        _ = Q⁻¹ * g * Q := by rw [← h1]
    have h3 : κ a = Q⁻¹ * g * Q := by
      show (MulAut.conj Q⁻¹) g = Q⁻¹ * g * Q
      rw [MulAut.conj_apply, inv_inv]
    rw [h3]
    exact h2
  exact Class8.eight_le_relIndex C hP (orthHom κ horth) (orthHom_injective κ hκ horth)
    (e := 6) (u := 315) (by norm_num) (by rw [card_GL_four]; norm_num) (m := 10) (v := 9765)
    (by rw [Nat.card_congr φ.toEquiv, card_S]; norm_num) (by norm_num)

end CFSG.QuasithinUnique.DoubleA3
