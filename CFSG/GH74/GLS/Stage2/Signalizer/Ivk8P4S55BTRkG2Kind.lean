module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L2Card

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkG2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped Nat IsMulCommutative

theorem exists_alt_seven_hom :
    ∃ j : ↥(alternatingGroup (Fin 7)) →* ↥(alternatingGroup (Fin 8)), Function.Injective j := by
  classical
  let f : Fin 7 ≃ Set.range (Fin.castSucc : Fin 7 → Fin 8) :=
    Equiv.ofInjective _ (Fin.castSucc_injective 7)
  let ι : Equiv.Perm (Fin 7) →* Equiv.Perm (Fin 8) := Equiv.Perm.extendDomainHom f
  have hι : Function.Injective ι := Equiv.Perm.extendDomainHom_injective f
  refine ⟨(ι.comp (alternatingGroup (Fin 7)).subtype).codRestrict _ fun σ => ?_,
    fun a b hab => Subtype.ext (hι (congrArg Subtype.val hab))⟩
  have h1 : ι σ = (σ : Equiv.Perm (Fin 7)).extendDomain f := rfl
  rw [Equiv.Perm.mem_alternatingGroup, MonoidHom.comp_apply, Subgroup.coe_subtype, h1,
    Equiv.Perm.sign_extendDomain]
  exact Equiv.Perm.mem_alternatingGroup.mp σ.2

theorem isSection_alt_eight_of_seven {Y : Type} [Group Y]
    (h : IsSection Y (alternatingGroup (Fin 7))) : IsSection Y (alternatingGroup (Fin 8)) := by
  obtain ⟨U, χ, hχ⟩ := h
  obtain ⟨j, hj⟩ := exists_alt_seven_hom
  exact ⟨U.map j, χ.comp (U.equivMapOfInjective j hj).symm.toMonoidHom,
    hχ.comp (U.equivMapOfInjective j hj).symm.surjective⟩

theorem not_kindFactorAll_classical {k : Kind} (hk : IsClassicalKind k) {T : Type} [Group T]
    (hL2 : ¬ IVK.IsL2 T (fun r => Odd r ∧ 5 ≤ r))
    (hA7 : ¬ IsSection T (alternatingGroup (Fin 7))) : ¬ KindFactorAll k T := by
  rcases hk with rfl | ⟨ε, rfl⟩
  · exact hL2
  · rintro (h | h)
    · exact hL2 h
    · exact hA7 h

theorem not_kindFactorAll_of_not_kindFactor {k : Kind} (hk : IsClassicalKind k) {T : Type}
    [Group T] (h : ∀ k' : Kind, ¬ KindFactor k' T) : ¬ KindFactorAll k T :=
  not_kindFactorAll_classical hk (h Kind.psp4)
    (fun hA => h Kind.mcl ⟨8, le_rfl, by norm_num, isSection_alt_eight_of_seven hA⟩)

theorem not_isSection_alt_seven_of_card {Z : Type} [Group Z] [Finite Z]
    (h1 : 360 < Nat.card Z) (h2 : Nat.card Z ≠ 2520) :
    ¬ IsSection Z (alternatingGroup (Fin 7)) := by
  rintro ⟨U, χ, hχ⟩
  have hA : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  have hcA : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hZU : Nat.card Z ≤ Nat.card ↥U :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_surjective hχ)
  have hmul := Subgroup.card_mul_index U
  rw [hcA] at hmul
  by_cases hU : U = ⊤
  · subst hU
    have : IsSimpleGroup ↥(⊤ : Subgroup ↥(alternatingGroup (Fin 7))) :=
      Subgroup.topEquiv.isSimpleGroup
    rw [Subgroup.index_top, mul_one] at hmul
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal χ.ker with hk | hk
    · have hinj : Function.Injective χ := (MonoidHom.ker_eq_bot_iff χ).mp hk
      have := Nat.card_congr (Equiv.ofBijective χ ⟨hinj, hχ⟩)
      omega
    · have hZ1 : Nat.card Z = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
        obtain ⟨u, rfl⟩ := hχ a
        obtain ⟨v, rfl⟩ := hχ b
        have hu : u ∈ χ.ker := by rw [hk]; exact Subgroup.mem_top u
        have hv : v ∈ χ.ker := by rw [hk]; exact Subgroup.mem_top v
        rw [MonoidHom.mem_ker.mp hu, MonoidHom.mem_ker.mp hv]
      omega
  · have hidx : U.index < 7 := by
      by_contra hi
      push Not at hi
      have h3 : Nat.card ↥U * 7 ≤ 2520 :=
        calc Nat.card ↥U * 7 ≤ Nat.card ↥U * U.index := Nat.mul_le_mul_left _ hi
          _ = 2520 := hmul
      omega
    have hcore : U.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U.normalCore with h | h
      · exact h
      · exact (hU (eq_top_iff.mpr (h ▸ U.normalCore_le))).elim
    have hle := Subgroup.index_normalCore_le_factorial_index U
    rw [hcore, Subgroup.index_bot, hcA] at hle
    have h6 : U.index ! ≤ 6 ! := Nat.factorial_le (by omega)
    have h720 : (6 : ℕ)! = 720 := by decide
    omega

theorem not_isL2_of_card_eq_504 {Z : Type} [Group Z] (h : Nat.card Z = 504) :
    ¬ IVK.IsL2 Z (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩
  have hc := card_L2_mul_two_of_odd (F := F) hodd
  rw [← Nat.card_congr e.toEquiv, h] at hc
  generalize Nat.card F = r at hc h5
  have hr : r < 11 := by
    by_contra hr
    push Not at hr
    have h121 : 121 ≤ r ^ 2 := by nlinarith
    have h1 : 11 * 120 ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul hr (by omega)
    omega
  interval_cases r <;> norm_num at hc

theorem not_kindFactorAll_of_card_eq_504 {k : Kind} (hk : IsClassicalKind k) {Z : Type}
    [Group Z] [Finite Z] (h : Nat.card Z = 504) : ¬ KindFactorAll k Z :=
  not_kindFactorAll_classical hk (not_isL2_of_card_eq_504 h)
    (not_isSection_alt_seven_of_card (by omega) (by omega))

theorem not_isSolvable_of_exists_ne {Q : Type} [Group Q] [IsSimpleGroup Q]
    (h : ∃ a b : Q, a * b ≠ b * a) : ¬ Group.IsSolvable Q := fun hs => by
  obtain ⟨a, b, hab⟩ := h
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem conj_injective_of_center {Y : Type} [Group Y] (h : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← h, Subgroup.mem_center_iff]
  intro y
  have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) y
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * g = (g * y * g⁻¹) * g := by rw [h1]
    _ = g * y := by group

theorem admAut_congr {k : Kind} {Y P : Type} [Group Y] [Group P] (e : Y ≃* P) {x : MulAut Y}
    (h : AdmAut k x) : AdmAut k (MulAut.congr e x) := by
  intro Z _ _ hns hsec
  refine h Z hns ?_
  have hmap : (fixSub (MulAut.congr e x)).map e.symm.toMonoidHom ≤ fixSub x := by
    rintro _ ⟨q, hq, rfl⟩
    have h1 : e (x (e.symm q)) = q := hq
    show x (e.symm q) = e.symm q
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact h1
  exact IsSection.of_le_le hmap (IsSection.of_equiv
    ((fixSub (MulAut.congr e x)).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).symm hsec)

theorem admRank3_of_equiv {k : Kind} {Y P : Type} [Group Y] [Group P] (e : Y ≃* P)
    (h : AdmRank3 k P) : AdmRank3 k Y := by
  intro E hE hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hE
  have hcE : Nat.card ↥(E.map (MulAut.congr e).toMonoidHom) = Nat.card ↥E :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  rw [← hcE]
  refine h _ (IsElementaryAbelian.map _) ?_
  rintro _ ⟨x, hxE, rfl⟩ hx1
  exact admAut_congr e (hadm x hxE fun h1 => hx1 (by rw [h1, map_one]))

theorem not_admAut_of_le {k : Kind} {Y : Type} [Group Y] {x : MulAut Y} {K : Subgroup Y}
    (hK : ∀ y ∈ K, x y = y) [IsSimpleGroup ↥K] (hns : ¬ Group.IsSolvable ↥K)
    (hbad : ¬ KindFactorAll k ↥K) : ¬ AdmAut k x := fun h =>
  hbad (h ↥K hns (IsSection.of_le_le (fun y hy => hK y hy)
    ⟨⊤, (⊤ : Subgroup ↥K).subtype, fun v => ⟨⟨v, Subgroup.mem_top v⟩, rfl⟩⟩))

theorem isElementaryAbelian_comap {A B : Type} [Group A] [Group B] {ψ : A →* B}
    (hψ : Function.Injective ψ) {I : Subgroup B} (hI : IsElementaryAbelian 2 ↥I) :
    IsElementaryAbelian 2 ↥(I.comap ψ) := by
  have := hI
  refine { is_comm := ⟨fun a b => Subtype.ext (hψ ?_)⟩, exponent_dvd_p := ?_ }
  · have h := congrArg Subtype.val
      (mul_comm (⟨ψ a, Subgroup.mem_comap.mp a.2⟩ : ↥I) ⟨ψ b, Subgroup.mem_comap.mp b.2⟩)
    simpa only [Subgroup.coe_mul, map_mul] using h
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext (hψ ?_)
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := I) _ (Subgroup.mem_comap.mp x.2)

theorem admRank3_of_inner {k : Kind} {Y : Type} [Group Y]
    (hconj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hrank : ∀ W : Subgroup Y, IsElementaryAbelian 2 ↥W → Nat.card ↥W ≤ 8)
    (hout : ∀ x : MulAut Y, x * x = 1 → x ∉ (MulAut.conj : Y →* MulAut Y).range →
      ¬ AdmAut k x) : AdmRank3 k Y := by
  intro E hE hadm
  have := hE
  have hle : E ≤ (MulAut.conj : Y →* MulAut Y).range := by
    intro x hx
    by_contra hnot
    have hx1 : x ≠ 1 := fun h => hnot (by rw [h]; exact Subgroup.one_mem _)
    have hxx : x * x = 1 := by
      rw [← pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    exact hout x hxx hnot (hadm x hx hx1)
  have hcard : Nat.card ↥(E.comap (MulAut.conj : Y →* MulAut Y)) = Nat.card ↥E := by
    rw [← Subgroup.card_map_of_injective hconj, Subgroup.map_comap_eq_self hle]
  rw [← hcard]
  exact hrank _ (isElementaryAbelian_comap hconj hE)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkG2
