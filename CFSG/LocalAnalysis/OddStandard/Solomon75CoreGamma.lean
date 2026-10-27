module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Balance
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreBalance
public import CFSG.Milestones.SG_two_signalizer_completeness

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

variable {G : Type} [Group G]

@[expose] def Wsub (U : Subgroup G) : Subgroup G :=
  ⨆ u ∈ U, ⨆ (_ : u ≠ 1), oddCoreOf (cen u)

namespace CoreAux

theorem oddCoreOf_cen_le_Wsub {U : Subgroup G} {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    oddCoreOf (cen u) ≤ Wsub U :=
  le_iSup₂_of_le u hu (le_iSup_of_le hu1 le_rfl)

theorem Wsub_mono {U V : Subgroup G} (h : U ≤ V) : Wsub U ≤ Wsub V :=
  iSup₂_le fun _ hu => iSup_le fun hu1 => oddCoreOf_cen_le_Wsub (h hu) hu1

theorem Wsub_map_conj (g : G) (U : Subgroup G) :
    (Wsub U).map (MulAut.conj g).toMonoidHom = Wsub (U.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [Wsub, Subgroup.map_iSup]
    refine iSup_le fun u => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hu => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hu1 => ?_
    have h1 : (oddCoreOf (cen u)).map (MulAut.conj g).toMonoidHom =
        oddCoreOf (cen (g * u * g⁻¹)) := by
      rw [cen_conj, oddCoreOf_map_equiv (MulAut.conj g) (cen u)]
    rw [h1]
    refine oddCoreOf_cen_le_Wsub ⟨u, hu, by simp [MulAut.conj_apply]⟩ ?_
    intro h
    apply hu1
    have : (MulAut.conj g) u = (MulAut.conj g) 1 := by
      simpa [MulAut.conj_apply] using h
    exact (MulAut.conj g).injective this
  · refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
    obtain ⟨u, hu, rfl⟩ := hv
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hv1 (map_one _)
    have h1 : (oddCoreOf (cen u)).map (MulAut.conj g).toMonoidHom =
        oddCoreOf (cen ((MulAut.conj g).toMonoidHom u)) := by
      rw [show (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ by simp [MulAut.conj_apply], cen_conj,
        oddCoreOf_map_equiv (MulAut.conj g) (cen u)]
    rw [← h1]
    exact Subgroup.map_mono (oddCoreOf_cen_le_Wsub hu hu1)

section Coprime

theorem le_iSup_inf_cen_of_four {U N : Subgroup G} (hU : Open.IsElemAbelian 2 U)
    (hU4 : 4 ≤ Nat.card U) (hUN : U ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N ≤ ⨆ a ∈ U, ⨆ (_ : a ≠ 1), N ⊓ cen a := by
  classical
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Finite N :=
    Nat.finite_of_card_ne_zero (fun h => by rw [h] at hodd; exact Nat.not_odd_zero hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 U :=
    { toIsMulCommutative := hU.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hU.2 x x.2) }
  let _ : MulDistribMulAction U N := Subgroup.conjMulDistribMulActionOfLeNormalizer U N hUN
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := U) (H := N)
    (by simpa using hU4) (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
  intro x hx
  have hmem : (⟨x, hx⟩ : N) ∈ ⨆ (a : U) (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) N := hgen ▸ Subgroup.mem_top _
  have hle : (⨆ (a : U) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) N) ≤
      (⨆ a ∈ U, ⨆ (_ : a ≠ 1), N ⊓ cen a).comap N.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hya : (a : G) * y * (a : G)⁻¹ = y := congrArg Subtype.val hy
    have hyc : (y : G) ∈ cen (a : G) := by
      rw [mem_centralizer_singleton_iff]
      calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hya]
        _ = a * y := by group
    have hinc : N ⊓ cen (a : G) ≤ ⨆ b ∈ U, ⨆ (_ : b ≠ 1), N ⊓ cen b :=
      le_iSup₂_of_le (a : G) a.2 (le_iSup_of_le (fun h => ha (Subtype.ext h)) le_rfl)
    exact hinc ⟨y.2, hyc⟩
  exact hle hmem

end Coprime

theorem fourSub_conj {Q : Subgroup G} {U : Subgroup G} (hUQ : U ≤ Q)
    (hU : Open.IsElemAbelian 2 U) (hU4 : Nat.card U = 4) {g : G}
    (hg : g ∈ normalizer (Q : Set G)) :
    U.map (MulAut.conj g).toMonoidHom ≤ Q ∧
      Open.IsElemAbelian 2 (U.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (U.map (MulAut.conj g).toMonoidHom) = 4 := by
  refine ⟨?_, CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2
    (MulAut.conj g).toMonoidHom U hU, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg u).mp (hUQ hu)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hU4]

end CoreAux

open CoreAux

section Signalizer

variable [Finite G]

@[expose] def OddCoreBalanced (G : Type) [Group G] : Prop :=
  ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x ≠ y →
    oddCoreOf (cen x) ⊓ cen y ≤ oddCoreOf (cen y)

theorem Wsub_complete (hbal : OddCoreBalanced G) {E : Subgroup G} (hE : Open.IsElemAbelian 2 E)
    (hE8 : 8 ≤ Nat.card E) :
    Odd (Nat.card (Wsub E)) ∧ (∀ a ∈ E, a ≠ 1 → Wsub E ⊓ cen a ≤ oddCoreOf (cen a)) ∧
      E ≤ normalizer (Wsub E : Set G) := by
  have hE2 : ∀ b ∈ E, b ^ 2 = 1 := (isElemAbelian_iff.mp hE).2
  have hcommE := (isElemAbelian_iff.mp hE).1
  let _ : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := fun x y => Subtype.ext (hcommE x x.2 y y.2) }
  have hexp : ∀ a : E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hE2 a a.2)
  have hord : ∀ a : E, a ≠ 1 → orderOf (a : G) = 2 := fun a ha =>
    orderOf_eq_prime (by simpa using hE2 a a.2) (fun h => ha (Subtype.ext h))
  have key := CFSG.Milestones.sg_two_signalizer_completeness G E hexp hE8
    ((MulAut.conj : G →* MulAut G).comp E.subtype) (fun b => oddCoreOf (cen (b : G)))
    (fun a _ b => map_conj_eq_of_mem_normalizer (le_normalizer_oddCore_cen hE2 a.2 b.2))
    (fun a _ => CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreOf _))
    (fun a _ => odd_card_oddCoreOf _)
    (fun a _ g hg => by
      have hga : g ∈ cen (a : G) := oddCoreOf_le _ hg
      have hc : (a : G) * g = g * a := (mem_centralizer_iff.mp hga) (a : G) rfl
      show (a : G) * g * (a : G)⁻¹ = g
      rw [hc]
      simp)
    (fun a b ha hb g hg hgb => by
      have hgb' : (b : G) * g * (b : G)⁻¹ = g := hgb
      have hcb : g ∈ cen (b : G) := by
        rw [mem_centralizer_singleton_iff]
        calc g * (b : G) = (b : G) * g * (b : G)⁻¹ * (b : G) := by rw [hgb']
          _ = (b : G) * g := by group
      by_cases hab : a = b
      · subst hab
        exact hg
      · exact hbal (a : G) (b : G) (hord a ha) (hord b hb)
          (congrArg Subtype.val (mul_comm a b)) (fun h => hab (Subtype.ext h)) ⟨hg, hcb⟩)
  obtain ⟨hinv, -, hodd, hcomp⟩ := key
  have hW : Wsub E = ⨆ (a : E) (_ : a ≠ 1), oddCoreOf (cen (a : G)) := by
    apply le_antisymm
    · refine iSup₂_le fun u hu => iSup_le fun hu1 => ?_
      exact le_iSup₂_of_le ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h)) le_rfl
    · refine iSup₂_le fun a ha => ?_
      exact oddCoreOf_cen_le_Wsub a.2 (fun h => ha (Subtype.ext h))
  rw [hW]
  refine ⟨hodd, fun a ha ha1 g hg => ?_, fun b hb => ?_⟩
  · have ha1' : (⟨a, ha⟩ : E) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    refine (hcomp ⟨a, ha⟩ ha1' g).mp ⟨hg.1, ?_⟩
    have hga : (a : G) * g = g * a := (mem_centralizer_singleton_iff.mp hg.2).symm
    show a * g * a⁻¹ = g
    rw [hga]
    simp
  · exact mem_normalizer_of_map_conj_eq (hinv ⟨b, hb⟩)

theorem Wsub_eq_of_le (hbal : OddCoreBalanced G) {U E : Subgroup G} (hE : Open.IsElemAbelian 2 E)
    (hE8 : 8 ≤ Nat.card E) (hUE : U ≤ E) (hU4 : Nat.card U = 4) : Wsub U = Wsub E := by
  refine le_antisymm (Wsub_mono hUE) ?_
  obtain ⟨hodd, hcen, hnorm⟩ := Wsub_complete hbal hE hE8
  have hgen := le_iSup_inf_cen_of_four (isElemAbelian_mono hUE hE) hU4.ge
    (hUE.trans hnorm) hodd
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
  exact (hcen a (hUE ha) ha1).trans (oddCoreOf_cen_le_Wsub ha ha1)

theorem Wsub_eq_of_reach (hbal : OddCoreBalanced G) {P : Subgroup G} (U V : FourSub P)
    (h : Relation.ReflTransGen (FourAdj P) U V) : Wsub U.1 = Wsub V.1 := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    obtain ⟨E, -, hEab, hE8, hbE, hcE⟩ := hbc
    rw [ih, Wsub_eq_of_le hbal hEab hE8 hbE (by rename_i b c _; exact b.2.2.2),
      Wsub_eq_of_le hbal hEab hE8 hcE (by rename_i b c _; exact c.2.2.2)]

theorem gamma_le_normalizer_W (hbal : OddCoreBalanced G) {P : Subgroup G}
    (hconn : ∀ U V : FourSub P, Relation.ReflTransGen (FourAdj P) U V) (U₀ : FourSub P) :
    Open.properTwoGenCoreGamma P 2 ≤ normalizer (Wsub U₀.1 : Set G) := by
  rw [CFSG.ProperTwoGeneratedCore.gamma_le_iff]
  intro Q hQP hQ g hg
  obtain ⟨U, hUQ, hUab, hU4⟩ := exists_fourSub_of_two_le_pRank hQ
  obtain ⟨hU'Q, hU'ab, hU'4⟩ := fourSub_conj hUQ hUab hU4 hg
  have h1 : Wsub U = Wsub U₀.1 :=
    Wsub_eq_of_reach hbal (⟨U, hUQ.trans hQP, hUab, hU4⟩ : FourSub P) U₀ (hconn _ _)
  have h2 : Wsub (U.map (MulAut.conj g).toMonoidHom) = Wsub U₀.1 :=
    Wsub_eq_of_reach hbal (⟨U.map (MulAut.conj g).toMonoidHom, hU'Q.trans hQP, hU'ab, hU'4⟩ :
      FourSub P) U₀ (hconn _ _)
  refine mem_normalizer_of_map_conj_eq ?_
  rw [← h1, Wsub_map_conj, h2, h1]

end Signalizer

end CFSG.OddStandard.Solomon75
