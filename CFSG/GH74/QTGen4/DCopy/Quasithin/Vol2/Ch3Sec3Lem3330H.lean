module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330H

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem stmt3_3_30_of_h_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h25 : Stmt3_3_25_F4) (h28 : Stmt3_3_28G2_F4) (h29 : Stmt3_3_29_F4) (hI : Insp3_3_30H) :
    Stmt3_3_30_F4 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  rcases (h25 G T M L D h).1 with hA6 | hG2 | hLn
  · exact hA6
  · exfalso
    obtain ⟨hTC, hQV⟩ := h28 G T M L D h hG2
    obtain ⟨ha, hb, hc⟩ := hI G T M L D h hG2 hTL hTC hQV
    have hred := Hyp331.vPlus_reduced h.toSetup331
    have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
      (h.centralizer_vPlus h38 h39).2.1
    rw [hQV] at hCQ
    have hVe := hred.2.1
    have hVab : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb => by
      have := hVe.1
      exact setLike_mul_comm ha hb
    have hVT : vPlus L T ≤ T :=
      (hred.1.trans inf_le_left).trans (pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf)
    have hHV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
    have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hHV
    have hVmax : IsMaxElemAbelian T (vPlus L T) := ⟨hVT, hVe, ha⟩
    have hperm : ∀ g ∈ D, ∀ B, IsMaxElemAbelian T B → T ≤ Subgroup.normalizer (B : Set G) →
        IsMaxElemAbelian T (B.map (MulAut.conj g).toMonoidHom) ∧
          T ≤ Subgroup.normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      intro g hg B hB hTB
      have hgT : g ∈ Subgroup.normalizer (T : Set G) := h.DN hg
      have hTg : T.map (MulAut.conj g).toMonoidHom = T := A38.map_conj_eq_iff.mpr hgT
      refine ⟨?_, le_normalizer_map_conj hgT hTB⟩
      have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr hB
      rwa [hTg] at this
    have hVne : vPlus L T ≠ ⊥ := by
      intro hb'
      apply h.not_L_le_centralizer h38 h39
      rw [hb']
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    have hDV : ¬ D ≤ Subgroup.normalizer (vPlus L T : Set G) :=
      h.not_le_normalizer h38 h39 hVne (hVT.trans le_sup_right) hHV
    obtain ⟨d, hdD, hdV⟩ := IsConcreteLE.not_le_iff_exists.mp hDV
    have hnot : ∀ g : G, g ∉ Subgroup.normalizer (vPlus L T : Set G) →
        ¬ (vPlus L T).map (MulAut.conj g).toMonoidHom ≤ vPlus L T := by
      intro g hg hle
      apply hg
      refine A38.map_conj_eq_iff.mp (Subgroup.eq_of_le_of_card_ge hle ?_)
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    obtain ⟨hV₁, hTV₁⟩ := hperm d hdD _ hVmax hTV
    obtain ⟨hV₂, hTV₂⟩ := hperm d hdD _ hV₁ hTV₁
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat h.Dodd h1
    have hd2 : d ^ 2 ∈ Subgroup.normalizer (vPlus L T : Set G) := by
      by_contra hd2
      have h2 : ¬ ((vPlus L T).map (MulAut.conj d).toMonoidHom).map (MulAut.conj d).toMonoidHom ≤
          vPlus L T := by
        rw [map_conj_map_conj, ← pow_two]
        exact hnot _ hd2
      have hsup := hc _ _ hV₁ hV₂ hTV₁ hTV₂ (hnot d hdV) h2
      obtain ⟨b, hbV₁, hbC⟩ := hb _ hV₁ hTV₁ (hnot d hdV)
      have hauto : autI hVe ((vPlus L T).map (MulAut.conj d).toMonoidHom) =
          autI hVe (((vPlus L T).map (MulAut.conj d).toMonoidHom).map
            (MulAut.conj d).toMonoidHom) := by
        rw [autI_eq_autOn, autI_eq_autOn, ← autOn_sup_eq_of_comm hVab (hV₁.1.trans hTV), hsup,
          autOn_sup_eq_of_comm hVab (hV₂.1.trans hTV)]
      have heq := B2_21 hVe hVT hTV hCQ hV₁ hbV₁ hbC hV₂ hauto
      apply hdV
      refine A38.map_conj_eq_iff.mp ?_
      have h1 := congrArg (fun X : Subgroup G => X.map (MulAut.conj d⁻¹).toMonoidHom) heq
      simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one, inv_mul_cancel_left] at h1
      exact h1
    exact hdV ((Subgroup.zpowers_le.mpr hd2) (mem_zpowers_sq_of_odd hodd))
  · exact absurd (h.isPSL_of_isLnBlock h38 h39 hTL hLn) (h29 G T M L D h)

end CFSG.Quasithin.H13
