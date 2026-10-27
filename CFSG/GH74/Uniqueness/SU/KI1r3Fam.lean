module

public import CFSG.GH74.Uniqueness.SU.KI1r3FamDefs
public import CFSG.GH74.Uniqueness.SU.KI1r3Main

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74

section Bridge

variable {H : Type} [Group H] [Finite H]

theorem generalizedFitting_normal' (H : Type) [Group H] [Finite H] :
    (generalizedFitting H).Normal :=
  (CFSG.LocalCores.generalized_fitting_characteristic).2

attribute [local instance] generalizedFitting_normal'

omit [Finite H] in
theorem conjNormal_injective_of_centralizer_eq_bot (N : Subgroup H) [N.Normal]
    (hcen : centralizer (N : Set H) = ⊥) :
    Function.Injective (MulAut.conjNormal : H →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro h hh
  rw [MonoidHom.mem_ker] at hh
  have hcent : h ∈ centralizer (N : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : h * l * h⁻¹ = l := by
      have := congrArg (fun a : MulAut N => ((a ⟨l, hl⟩ : N) : H)) hh
      simpa [MulAut.conjNormal_apply] using this
    calc l * h = (h * l * h⁻¹) * h := by rw [h1]
      _ = h * l := by group
  rw [hcen] at hcent
  exact hcent

theorem no_fixed_four_group {x : H}
    (hrk : Open.pRank 2 (centralizer ({x} : Set H) ⊓ generalizedFitting H) = 1) :
    ¬ ∃ V : Subgroup ↥(generalizedFitting H),
      (∀ v ∈ V, (MulAut.conjNormal x : MulAut ↥(generalizedFitting H)) v = v) ∧
        Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  rintro ⟨V, hV, hVel, hVc⟩
  set W : Subgroup H := V.map (generalizedFitting H).subtype with hW
  have hWel : Open.IsElemAbelian 2 W := SU4.isElemAbelian_map _ hVel
  have hWc : Nat.card W = 4 := by
    rw [hW, Subgroup.card_map_of_injective (generalizedFitting H).subtype_injective]; exact hVc
  have hWle : W ≤ centralizer ({x} : Set H) ⊓ generalizedFitting H := by
    rintro _ ⟨v, hv, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, v.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hV v hv
    have h2 : x * (v : H) * x⁻¹ = v := by
      have := congrArg Subtype.val h1
      simpa [MulAut.conjNormal_apply] using this
    show (v : H) * x = x * (v : H)
    calc (v : H) * x = x * (v : H) * x⁻¹ * x := by rw [h2]
      _ = x * v := by group
  have := SU1.le_pRank (p := 2) (by norm_num) hWle hWel (k := 2) (by rw [hWc]; norm_num)
  omega

theorem no_four_le_twoRank (hrank : Open.twoRank H = 3)
    (h4 : 4 ≤ Open.twoRank ↥(generalizedFitting H)) : False := by
  have h1 := SU4.pRank_map_of_injective (generalizedFitting H).subtype
    (generalizedFitting H).subtype_injective (⊤ : Subgroup ↥(generalizedFitting H))
  have h2 : (⊤ : Subgroup ↥(generalizedFitting H)).map (generalizedFitting H).subtype =
      generalizedFitting H := by
    rw [Subgroup.map_top]; exact Subgroup.range_subtype _
  have h3 := SU1.pRank_mono (p := 2) (by norm_num) (le_top : generalizedFitting H ≤ ⊤)
  unfold Open.twoRank at h4 hrank
  rw [h2] at h1
  omega

theorem conjNormal_not_inner {x : H}
    (hcen : centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥)
    (hxK : x ∉ generalizedFitting H) :
    (MulAut.conjNormal x : MulAut ↥(generalizedFitting H)) ∉
      (MulAut.conj : ↥(generalizedFitting H) →* MulAut ↥(generalizedFitting H)).range := by
  rintro ⟨g, hg⟩
  apply hxK
  have hinj := conjNormal_injective_of_centralizer_eq_bot (generalizedFitting H) hcen
  have : (MulAut.conjNormal (g : H) : MulAut ↥(generalizedFitting H)) = MulAut.conjNormal x := by
    rw [← hg]
    ext l
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have := hinj this
  rw [← this]
  exact g.2

theorem isPGL2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : IsPGL2 Y p f) : IsPGL2 X p f := by
  obtain ⟨F, hF, hFin, hc, ⟨eY⟩⟩ := h
  exact ⟨F, hF, hFin, hc, ⟨e.trans eY⟩⟩

theorem isPGL2_sup_zpowers_of_aut {x : H}
    (hcen : centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥) {p f : ℕ}
    (h : IsPGL2 ↥((MulAut.conj : ↥(generalizedFitting H) →* MulAut ↥(generalizedFitting H)).range ⊔
      Subgroup.zpowers (MulAut.conjNormal x : MulAut ↥(generalizedFitting H))) p f) :
    IsPGL2 ↥(generalizedFitting H ⊔ zpowers x) p f := by
  let ρ : H →* MulAut ↥(generalizedFitting H) := MulAut.conjNormal
  have hρinj := conjNormal_injective_of_centralizer_eq_bot (generalizedFitting H) hcen
  have hρL : ∀ k : ↥(generalizedFitting H), ρ (k : H) = MulAut.conj k :=
    fun k => MulAut.conjNormal_val
  have hKmap : (generalizedFitting H).map ρ =
      (MulAut.conj : ↥(generalizedFitting H) →* MulAut ↥(generalizedFitting H)).range := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, (hρL ⟨l, hl⟩).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨(k : H), k.2, hρL k⟩
  have hmap : (generalizedFitting H ⊔ zpowers x).map ρ =
      (MulAut.conj : ↥(generalizedFitting H) →* MulAut ↥(generalizedFitting H)).range ⊔
        Subgroup.zpowers (ρ x) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hKmap]
  let e := Subgroup.equivMapOfInjective (generalizedFitting H ⊔ zpowers x) ρ hρinj
  exact isPGL2_of_mulEquiv (e.trans (MulEquiv.subgroupCongr hmap)) h


theorem no_fourFix {x : H} (hrank : Open.twoRank H = 3) (hx2 : orderOf x = 2)
    (hrk : Open.pRank 2 (centralizer ({x} : Set H) ⊓ generalizedFitting H) = 1)
    (hFF : FourFix ↥(generalizedFitting H)) : False := by
  have hx : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hα2 : (MulAut.conjNormal x : MulAut ↥(generalizedFitting H)) ^ 2 = 1 := by
    rw [← map_pow, hx, map_one]
  rcases hFF _ hα2 with h | h4
  · exact no_fixed_four_group hrk h
  · exact no_four_le_twoRank hrank h4

end Bridge

section Assembly

structure FamFacts : Prop where
  l2 : FamL2
  alt : FamAlt
  m11 : FamSp .M11
  m12 : FamSp .M12
  m22 : FamSp .M22
  m23 : FamSp .M23
  j1 : FamSp .J1
  j2 : FamSp .J2
  j3 : FamSp .J3
  mcl : FamSp .McL
  ly : FamSp .Ly
  psl3 : FamLie .PSL 3
  psl4 : FamLie .PSL 4
  psl5 : FamLie .PSL 5
  psu3 : FamLie .PSU 3
  psu4 : FamLie .PSU 4
  psu5 : FamLie .PSU 5
  psp2 : FamLie .PSp 2
  g2 : FamLie .G2 0
  d4 : FamLie .trialityD4 0
  ree : FamRee
  bender : FamBender

theorem f61r3_of_famFacts (F : FamFacts) : F61r3 := by
  intro H _ _ hGH hrank hsimple hnab hcen x hx2 hxK hrk
  have hGHL : GHList ↥(generalizedFitting H) :=
    hGH.ghList_of_surjection (A := generalizedFitting H) (MonoidHom.id _) Function.surjective_id
      hsimple hnab
  have hx : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hα2 : (MulAut.conjNormal x : MulAut ↥(generalizedFitting H)) ^ 2 = 1 := by
    rw [← map_pow, hx, map_one]
  have hno : FourFix ↥(generalizedFitting H) → False := fun hFF => no_fourFix hrank hx2 hrk hFF
  unfold GHList at hGHL
  rcases hGHL with ⟨n, hn7, hn11, ⟨e⟩⟩ | hsp | ⟨p, f, hp, hf, hcases⟩
  · exact (hno (FourFix.of_mulEquiv e.symm (F.alt n hn7 hn11))).elim
  · rcases hsp with h | h | h | h | h | h | h | h | h
    · exact (hno (F.m11 _ h)).elim
    · exact (hno (F.m12 _ h)).elim
    · exact (hno (F.m22 _ h)).elim
    · exact (hno (F.m23 _ h)).elim
    · exact (hno (F.j1 _ h)).elim
    · exact (hno (F.j2 _ h)).elim
    · exact (hno (F.j3 _ h)).elim
    · exact (hno (F.mcl _ h)).elim
    · exact (hno (F.ly _ h)).elim
  · rcases hcases with ⟨hp2, hL⟩ | ⟨hp2, -, hL⟩ | ⟨hp2, -, hL⟩ | ⟨h4, hL⟩ | ⟨h4, hL⟩ | hL | ⟨-, hL⟩
    · rcases hL with hL | hL | hL | hL | hL | hL
      · exact ⟨p, f, hp, hp2, hL, isPGL2_sup_zpowers_of_aut hcen
          (F.l2 _ p f hp hp2 hL hsimple _ hα2 (conjNormal_not_inner hcen hxK)
            (no_fixed_four_group hrk))⟩
      · exact (hno (F.psl3 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (F.psu3 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (F.psp2 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (F.g2 _ hsimple hnab p f hp hp2 hL)).elim
      · exact (hno (F.d4 _ hsimple hnab p f hp hp2 hL)).elim
    · exact (hno (F.psl4 _ hsimple hnab p f hp hp2 hL)).elim
    · exact (hno (F.psu4 _ hsimple hnab p f hp hp2 hL)).elim
    · have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      exact (hno (F.psl5 _ hsimple hnab p f hp hp2 hL)).elim
    · have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        omega
      exact (hno (F.psu5 _ hsimple hnab p f hp hp2 hL)).elim
    · exact (hno (F.ree _ hsimple hnab f hL)).elim
    · exact (hno (F.bender _ hsimple hnab hL)).elim

end Assembly
end CFSG.GH74.Uniqueness.SU.K.R3
