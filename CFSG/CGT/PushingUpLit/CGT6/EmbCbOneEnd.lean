module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbNat
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd
public import CFSG.CGT.PushingUpLit.CGT6.EmbLift

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] [Finite V]

theorem EndCfg4.false_of_natural_lift {G T Y L Z : Subgroup (MulAut V)} (hNL : NatLiftStatement)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) (hYL : Y ≤ L) (hLG : L ≤ G) (hLn : (L.subgroupOf G).Normal)
    (hLperf : ⁅L, L⁆ = L) (hLcen : Subgroup.center ↥L = ⊥) {a : ℕ} (ha : 2 ≤ a)
    (θ : ↥Z ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV Z) ⊥) (hZL : Z ≠ L)
    (hlift : Lift4 L Z L) : False := by
  classical
  have hZ2 : ¬ IsPGroup 2 ↥Z := (classX4_of_natSection hV ha θ hnat).not_isPGroup hV
  obtain ⟨hXL, harr⟩ := Lift4.inClassX_of_natSection hV ha θ hnat hlift
  have harr' := harr
  rcases harr with heq | ⟨aL, b, φ, F₀, -, hnatL, -, -, -, -⟩
  · exact hZL (yuHol_inj heq)
  have hsimple := arrowNat_top_simple_of_perfect hV hZ2 hLperf hZL harr'
  have haL : 2 ≤ aL := by
    by_contra hlt
    have hs : Group.IsSolvable (alternatingGroup (Fin (2 * aL + 1))) :=
      alternatingGroup.isSolvable (by simp; omega)
    have hs' : Group.IsSolvable (↥(yuHol L) ⧸ pCore 2 ↥(yuHol L)) :=
      Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    obtain ⟨hS, a₁, b₁, hab⟩ := hsimple
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable
      (G := ↥(yuHol L) ⧸ pCore 2 ↥(yuHol L))).mpr hs'
    exact hab (hcomm a₁ b₁)
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
  obtain ⟨θL, hθL⟩ := natSection_of_isNaturalAltModule hV hLcen hXL.1 haL ⟨φ, hnatL⟩
  obtain ⟨θY, hθY⟩ := h.exists_natSection hV hm hodd hY
  obtain ⟨e, he⟩ := hodd
  subst he
  have he2 : 2 ≤ e := by omega
  obtain ⟨F, hF, hFY⟩ := natSection_stab_of_natSection hV haL he2 θL hθL hYL θY hθY
  have heL : e ≤ aL := by
    by_contra hlt
    have hlt' : aL < e := not_le.mp hlt
    have hcard := Subgroup.card_le_of_le hYL
    have : Nontrivial (Fin (2 * e + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Nontrivial (Fin (2 * aL + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr θY.toEquiv, Nat.card_congr θL.toEquiv, nat_card_alternatingGroup,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin] at hcard
    have h1 : (2 * aL + 1).factorial < (2 * e + 1).factorial :=
      (Nat.factorial_lt (by omega)).mpr (by omega)
    have h2 : 2 ∣ (2 * e + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : 2 ∣ (2 * aL + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    omega
  obtain ⟨hX2, harr2⟩ := hNL V hV L Y aL e haL (by omega) heL θL hθL F hF hYL hFY
  exact h.nolift ⟨L, hYL, hLG, hLn.isSubnormal, Or.inl ⟨hX2, harr2⟩⟩

end CFSG.CGT.PushingUpLit.CGT6
