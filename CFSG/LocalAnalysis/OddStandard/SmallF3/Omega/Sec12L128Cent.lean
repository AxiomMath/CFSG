module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentPsi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_cent_two_nat {G : Type} [Group G] [Finite G] {V V1 V2 X : Subgroup G}
    {phi1 phi2 : (Fin 5 → ZMod 2) → G} (hV : IsElemAb2 V 8) (hsup : V1 ⊔ V2 = V)
    (hinf : V1 ⊓ V2 = ⊥) (hc1 : Sec127NatCoord V1 X phi1) (hc2 : Sec127NatCoord V2 X phi2) :
    Nat.card ↥(Subgroup.centralizer (autIn X V : Set (MulAut ↥V))) ∣ 6 ∧
      ∀ c ∈ Subgroup.centralizer (autIn X V : Set (MulAut ↥V)), c ^ 3 = 1 → c ≠ 1 →
        ∀ v : ↥V, c v = v → v = 1 := by
  classical
  have hd : Sec128Two V V1 V2 X phi1 phi2 :=
    ⟨fun x hx y hy => hV.1.comm hx hy, hsup, hinf, hc1, hc2⟩
  obtain ⟨s1, hs1, onto1⟩ := sec128_exists_act hc1
  obtain ⟨s2, hs2, onto2⟩ := sec128_exists_act hc2
  have hrho : ∀ (h : ↥X) (p : EvW × EvW),
      ((hd.coord.Ψ (s1 h p.1, s2 h p.2) : ↥V) : G) =
        (h : G) * (hd.coord.Ψ p : G) * (h : G)⁻¹ := by
    intro h p
    rw [Sec128Two.coord_Ψ, Sec128Two.coord_Ψ, Sec128Two.psiE_val, Sec128Two.psiE_val]
    show phi1 (s1 h p.1).1 * phi2 (s2 h p.2).1 = (h : G) * (phi1 p.1.1 * phi2 p.2.1) * (h : G)⁻¹
    rw [← hs1, ← hs2]
    group
  by_cases hiso : ∃ g0 : EvW →+ EvW, Function.Bijective g0 ∧ ∀ i a, g0 (s2 i a) = s1 i (g0 a)
  ·
    obtain ⟨g0, hb0, hg0⟩ := hiso
    let e0 : EvW ≃+ EvW := AddEquiv.ofBijective g0 hb0
    have hsw : ∀ (h : ↥X) (b : EvW), e0.symm (s1 h b) = s2 h (e0.symm b) := by
      intro h b
      rw [AddEquiv.symm_apply_eq]
      show s1 h b = g0 (s2 h (e0.symm b))
      rw [hg0, show g0 (e0.symm b) = b from e0.apply_symm_apply b]
    let K' : AddCoord V :=
      { Ψ := (Equiv.prodCongr (Equiv.refl EvW) e0.symm.toEquiv).trans hd.psiE
        add := fun p q => by
          have hq : ((p + q).1, e0.symm (p + q).2) =
              (p.1, e0.symm p.2) + (q.1, e0.symm q.2) :=
            Prod.ext rfl (map_add e0.symm p.2 q.2)
          show hd.psiE ((p + q).1, e0.symm (p + q).2) =
            hd.psiE (p.1, e0.symm p.2) * hd.psiE (q.1, e0.symm q.2)
          rw [hq]
          exact hd.psiE_add _ _ }
    have hrho' : ∀ (h : ↥X) (p : EvW × EvW),
        ((K'.Ψ (s1 h p.1, s1 h p.2) : ↥V) : G) = (h : G) * (K'.Ψ p : G) * (h : G)⁻¹ := by
      intro h p
      have := hrho h (p.1, e0.symm p.2)
      rw [← hsw h p.2, Sec128Two.coord_Ψ, Sec128Two.coord_Ψ] at this
      exact this
    have hex : ∀ c : ↥(Subgroup.centralizer (autIn X V : Set (MulAut ↥V))),
        ∃ e : Matrix (Fin 2) (Fin 2) (ZMod 2), K'.kapW c.1 = thetaW e := fun c =>
      sec128_exists_theta onto1 _ (fun i p => K'.kapW_comm (fun h p => (s1 h p.1, s1 h p.2))
        hrho' c.2 i p)
    choose ε hε using hex
    have ε_one : ε 1 = 1 := by
      apply sec128_thetaW_injective
      rw [← hε, sec128_thetaW_one]
      exact K'.kapW_one
    have ε_mul : ∀ c c' : ↥(Subgroup.centralizer (autIn X V : Set (MulAut ↥V))),
        ε (c * c') = ε c * ε c' := by
      intro c c'
      apply sec128_thetaW_injective
      rw [sec128_thetaW_mul, ← hε, ← hε, ← hε]
      exact K'.kapW_mul c.1 c'.1
    let εhom : ↥(Subgroup.centralizer (autIn X V : Set (MulAut ↥V))) →*
        Matrix (Fin 2) (Fin 2) (ZMod 2) :=
      { toFun := ε, map_one' := ε_one, map_mul' := ε_mul }
    have ε_inj : Function.Injective εhom := by
      intro c c' h
      apply Subtype.ext
      apply K'.kapW_inj
      rw [hε c, hε c']
      exact congrArg thetaW h
    refine ⟨?_, ?_⟩
    · have hu : Function.Injective (εhom.toHomUnits) := by
        intro c c' h
        exact ε_inj (congrArg Units.val h)
      exact (Subgroup.card_dvd_of_injective _ hu).trans (sec128_card_GL2 ▸ dvd_refl _)
    · intro c hc h3 hne v hv
      let cc : ↥(Subgroup.centralizer (autIn X V : Set (MulAut ↥V))) := ⟨c, hc⟩
      have h3' : cc ^ 3 = 1 := Subtype.ext h3
      have hne' : cc ≠ 1 := fun h => hne (congrArg Subtype.val h)
      have hε3 : ε cc * ε cc * ε cc = 1 := by
        have h1 : εhom (cc ^ 3) = 1 := by rw [h3', map_one]
        rw [map_pow, pow_three'] at h1
        exact h1
      have hεne : ε cc ≠ 1 := fun h => hne' (ε_inj (h.trans ε_one.symm))
      have hfix : K'.kapW c (K'.Ψ.symm v) = K'.Ψ.symm v := by
        apply K'.Ψ.injective
        rw [K'.kapW_spec, Equiv.apply_symm_apply, hv]
      rw [hε cc] at hfix
      have h0 := sec128_theta_fix (ε cc) hε3 hεne _ hfix
      calc v = K'.Ψ (K'.Ψ.symm v) := (K'.Ψ.apply_symm_apply v).symm
        _ = 1 := by rw [h0]; exact K'.zero
  ·
    have hall : ∀ c ∈ Subgroup.centralizer (autIn X V : Set (MulAut ↥V)), c = 1 := by
      intro c hc
      have hf : ∀ (i : ↥X) (p : EvW × EvW), hd.coord.kapW c (s1 i p.1, s2 i p.2) =
          (s1 i (hd.coord.kapW c p).1, s2 i (hd.coord.kapW c p).2) := fun i p =>
        hd.coord.kapW_comm (fun h p => (s1 h p.1, s2 h p.2)) hrho hc i p
      have h1 := sec128_noiso_id onto1 onto2 hiso (hd.coord.kapW c) hf
        (hd.coord.kapW_injective c)
      exact hd.coord.kapW_inj (h1.trans hd.coord.kapW_one.symm)
    refine ⟨?_, fun c hc _ hne => absurd (hall c hc) hne⟩
    have hbot : Subgroup.centralizer (autIn X V : Set (MulAut ↥V)) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hall
    rw [hbot, Subgroup.card_bot]
    exact one_dvd _

end CFSG.OddStandard.SmallF3.Omega
