module

public import CFSG.GH74.E2.CaseIINoComp
public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.GH74.QTGen4

variable {X : Type*} [Group X]

noncomputable def conjHom (Q : Subgroup X) [Q.Normal] : X →* MulAut Q :=
  Q.normalizerMonoidHom.comp
    (MonoidHom.codRestrict (MonoidHom.id X) (Subgroup.normalizer (Q : Set X))
      fun x => by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top x)

theorem conjHom_apply_coe (Q : Subgroup X) [Q.Normal] (x : X) (q : Q) :
    ((conjHom Q x q : Q) : X) = x * q * x⁻¹ := by
  simp [conjHom]

noncomputable def quotientConj (Q : Subgroup X) [Q.Normal] :
    X →* MulAut (Q ⧸ frattini Q) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini Q)).comp (conjHom Q)

theorem exists_injective_quotient_pCore_to_mulAut_frattini {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsCharacteristicP 2 X) :
    ∃ ψ : X ⧸ CFSG.pCore 2 X →* MulAut (↥(CFSG.pCore 2 X) ⧸ frattini ↥(CFSG.pCore 2 X)),
      Function.Injective ψ := by
  set Q := CFSG.pCore 2 X with hQdef
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hcomm : ∀ a b : Q ⧸ frattini Q, a * b = b * a := fun a b =>
    (CFSG.GroupTheory.frattini_elementary_quotient hQp).2.1.is_comm.comm a b
  set χ := quotientConj Q with hχ
  have hQle : Q ≤ χ.ker := by
    intro q hq
    have hmem : conjHom Q q ∈
        (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini Q)).ker := by
      refine (CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel
        (frattini Q) (conjHom Q q)).2 fun y => ?_
      have hconj : conjHom Q q y = (⟨q, hq⟩ : Q) * y * (⟨q, hq⟩ : Q)⁻¹ :=
        Subtype.ext (by rw [conjHom_apply_coe]; simp)
      rw [hconj, map_mul, map_mul, map_inv,
        hcomm (QuotientGroup.mk' (frattini Q) ⟨q, hq⟩) (QuotientGroup.mk' (frattini Q) y)]
      simp
    exact hmem
  have hKle : χ.ker ≤ Q := by
    have hK : IsPGroup 2 χ.ker := by
      rw [IsPGroup.iff_orderOf]
      rintro ⟨g, hg⟩
      have hker : conjHom Q g ∈
          (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini Q)).ker := hg
      obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp
        (CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2 hQp))
        ⟨conjHom Q g, hker⟩
      rw [Subgroup.orderOf_mk] at ha
      have hpow := pow_orderOf_eq_one (conjHom Q g)
      rw [ha] at hpow
      have hxker : conjHom Q (g ^ 2 ^ a) = 1 := by
        rw [map_pow]
        exact hpow
      have hc : ∀ q ∈ (Q : Set X), q * g ^ 2 ^ a = g ^ 2 ^ a * q := by
        intro q hq
        have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : X)) hxker
        simp only [conjHom_apply_coe, MulAut.one_apply] at h1
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
  refine ⟨QuotientGroup.lift Q χ hQle, ?_⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q a
  have hg : χ g = 1 := ha
  exact (QuotientGroup.eq_one_iff g).2 (hKle hg)

theorem card_quotient_pCore_dvd_20160 {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsCharacteristicP 2 X) (hgen : CFSG.GH74.Gen4 X) :
    Nat.card (X ⧸ CFSG.pCore 2 X) ∣ 20160 := by
  obtain ⟨ψ, hψ⟩ := exists_injective_quotient_pCore_to_mulAut_frattini hX
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hrank : Group.rank ↥(CFSG.pCore 2 X) ≤ 4 := by
    have h := CFSG.GH74.E2.rank_le_four_of_subgroup hgen hQp ⊤
    rw [← Group.rank_congr (Subgroup.topEquiv (G := ↥(CFSG.pCore 2 X)))]
    exact h
  exact (Subgroup.card_dvd_of_injective ψ hψ).trans
    (CFSG.RankThree.PartOne.SectionalRank.card_mulAut_frattini_quotient_dvd hQp hrank)

end CFSG.GH74.QTGen4
