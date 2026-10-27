module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem ker_frattiniConj_le_pCore {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsCharacteristicP 2 X) :
    ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥(CFSG.pCore 2 X))).comp
      (CFSG.GH74.QTGen4.conjHom (CFSG.pCore 2 X))).ker ≤ CFSG.pCore 2 X := by
  set Q := CFSG.pCore 2 X
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hK : IsPGroup 2 ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥Q)).comp (CFSG.GH74.QTGen4.conjHom Q)).ker := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨g, hg⟩
    have hker : CFSG.GH74.QTGen4.conjHom Q g ∈
        (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q)).ker := hg
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2 hQp))
      ⟨CFSG.GH74.QTGen4.conjHom Q g, hker⟩
    rw [Subgroup.orderOf_mk] at ha
    have hpow := pow_orderOf_eq_one (CFSG.GH74.QTGen4.conjHom Q g)
    rw [ha] at hpow
    have hxker : CFSG.GH74.QTGen4.conjHom Q (g ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact hpow
    have hc : ∀ q ∈ (Q : Set X), q * g ^ 2 ^ a = g ^ 2 ^ a * q := by
      intro q hq
      have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : X)) hxker
      simp only [CFSG.GH74.QTGen4.conjHom_apply_coe, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    have hx : g ^ 2 ^ a ∈ Q := hX (Subgroup.mem_centralizer_iff.2 hc)
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨g ^ 2 ^ a, hx⟩
    rw [Subgroup.orderOf_mk] at hb
    have hxpow := pow_orderOf_eq_one (g ^ 2 ^ a)
    rw [hb] at hxpow
    have hdiv : orderOf g ∣ 2 ^ (a + b) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_add, pow_mul, hxpow]
    obtain ⟨c, -, hc'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
    refine ⟨c, ?_⟩
    rw [Subgroup.orderOf_mk]
    exact hc'
  exact le_sSup ⟨inferInstance, hK⟩

theorem frattiniFaithful_dsFrattini_eq {G : Type} [Group G] (X : Subgroup G) :
    dsFrattini X = (frattini ↥X).map X.subtype := rfl

theorem mem_frattini_pCore_iff {G : Type} [Group G] (P : Subgroup G) (z : ↥(CFSG.pCore 2 ↥P)) :
    z ∈ frattini ↥(CFSG.pCore 2 ↥P) ↔
      ((z : ↥P) : G) ∈ dsFrattini (CFSG.Open.pCoreOf 2 P) := by
  let e : ↥(CFSG.pCore 2 ↥P) ≃* ↥(CFSG.Open.pCoreOf 2 P) :=
    Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥P) P.subtype P.subtype_injective
  have hfr : (frattini ↥(CFSG.pCore 2 ↥P)).map e.toMonoidHom = frattini ↥(CFSG.Open.pCoreOf 2 P) :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  have he : ∀ w : ↥(CFSG.pCore 2 ↥P), ((e w : ↥(CFSG.Open.pCoreOf 2 P)) : G) = ((w : ↥P) : G) :=
    fun _ => rfl
  rw [frattiniFaithful_dsFrattini_eq]
  constructor
  · intro hz
    refine Subgroup.mem_map.2 ⟨e z, ?_, he z⟩
    rw [← hfr]
    exact Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
    have hwe : w = e z := Subtype.ext (hwz.trans (he z).symm)
    have hez : e z ∈ (frattini ↥(CFSG.pCore 2 ↥P)).map e.toMonoidHom := by
      rw [hfr, ← hwe]
      exact hw
    obtain ⟨z', hz', hz'e⟩ := Subgroup.mem_map.1 hez
    have hzz : z' = z := e.injective hz'e
    rw [← hzz]
    exact hz'

theorem leafFrattiniFaithful : LeafFrattiniFaithful := by
  intro G _ _ P hP p hp hcomm
  have hchar : CFSG.IsCharacteristicP 2 ↥P := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hcent : (x : G) ∈ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1
        (show g ∈ (CFSG.pCore 2 ↥P).map P.subtype from hg)
      have h1 := congrArg (fun y : ↥P => (y : G)) (hx q hq)
      simpa using h1
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1
      (show (x : G) ∈ (CFSG.pCore 2 ↥P).map P.subtype from hP (Subgroup.mem_inf.2 ⟨x.2, hcent⟩))
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  have hχ : ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥(CFSG.pCore 2 ↥P))).comp (CFSG.GH74.QTGen4.conjHom (CFSG.pCore 2 ↥P)))
      (⟨p, hp⟩ : ↥P) = 1 := by
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥(CFSG.pCore 2 ↥P)) z
    have hmem : ((y : ↥P) : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 P := by
      show ((y : ↥P) : G)⁻¹ ∈ (CFSG.pCore 2 ↥P).map P.subtype
      exact Subgroup.mem_map.2 ⟨(y : ↥P)⁻¹, (CFSG.pCore 2 ↥P).inv_mem y.2, rfl⟩
    have hz : (CFSG.GH74.QTGen4.conjHom (CFSG.pCore 2 ↥P) (⟨p, hp⟩ : ↥P) y)⁻¹ * y ∈
        frattini ↥(CFSG.pCore 2 ↥P) := by
      refine (mem_frattini_pCore_iff P _).2 ?_
      have hval : ((((CFSG.GH74.QTGen4.conjHom (CFSG.pCore 2 ↥P) (⟨p, hp⟩ : ↥P) y)⁻¹ * y :
          ↥(CFSG.pCore 2 ↥P)) : ↥P) : G) = ⁅p, ((y : ↥P) : G)⁻¹⁆ := by
        simp [CFSG.GH74.QTGen4.conjHom_apply_coe, commutatorElement_def, mul_assoc]
      rw [hval]
      exact hcomm _ hmem
    rw [MonoidHom.comp_apply, MulAut.one_apply,
      CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply]
    exact QuotientGroup.eq.2 hz
  have hpQ : (⟨p, hp⟩ : ↥P) ∈ CFSG.pCore 2 ↥P :=
    ker_frattiniConj_le_pCore hchar (MonoidHom.mem_ker.2 hχ)
  show p ∈ (CFSG.pCore 2 ↥P).map P.subtype
  exact Subgroup.mem_map.2 ⟨⟨p, hp⟩, hpQ, rfl⟩

end CFSG.GH74.QTGen4.DSGen4
