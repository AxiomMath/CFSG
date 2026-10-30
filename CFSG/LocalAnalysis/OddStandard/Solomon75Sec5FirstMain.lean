module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatFourInE8
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstHull
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstGamma
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstZStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAschbacherFive

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.OddStandard.Solomon75.Sec5Two

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

private theorem oddCoreOf_cen_le_W1 {A : Subgroup X} {b : X} (hb : b ∈ A) (hb2 : orderOf b = 2) :
    oddCoreOf (centralizer ({b} : Set X)) ≤ W1 A :=
  le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb2 le_rfl))

private theorem map_conj_oddCoreOf_cen (g b : X) :
    (oddCoreOf (cen b)).map (MulAut.conj g).toMonoidHom = oddCoreOf (cen (g * b * g⁻¹)) := by
  rw [CoreAux.cen_conj, CoreAux.oddCoreOf_map_equiv (MulAut.conj g) (cen b)]

private theorem map_conj_W1_le {A : Subgroup X} {y : X} (hy : y ∈ normalizer (A : Set X)) :
    (W1 A).map (MulAut.conj y).toMonoidHom ≤ W1 A := by
  unfold W1
  rw [Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb2 => ?_
  rw [map_conj_oddCoreOf_cen y b]
  have hyb : y * b * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hy b).1 hb
  have hyb2 : orderOf (y * b * y⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) b
    rw [hb2] at this
    exact this
  exact le_iSup_of_le (y * b * y⁻¹) (le_iSup_of_le hyb (le_iSup_of_le hyb2 le_rfl))

private theorem normalizer_le_normalizer_W1 (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer ((W1 A : Subgroup X) : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact map_conj_W1_le hy ⟨w, hw, rfl⟩
  · intro hw
    have := map_conj_W1_le (Subgroup.inv_mem _ hy) ⟨y * w * y⁻¹, hw, rfl⟩
    have e : (MulAut.conj y⁻¹).toMonoidHom (y * w * y⁻¹) = w := by
      simp [MulAut.conj_apply, mul_assoc]
    rwa [e] at this

open CFSG.ComponentClassification.HarrisLit.T1.S74.L38 in
private theorem exists_fourSub_not_mem {E : Subgroup X} (hE : Open.IsElemAbelian 2 E)
    (h8 : 8 ≤ Nat.card E) {w : X} (hw2 : orderOf w = 2) :
    ∃ U : Subgroup X, U ≤ E ∧ Open.IsElemAbelian 2 U ∧ Nat.card U = 4 ∧ w ∉ U := by
  by_cases hwE : w ∈ E
  · have hww : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hw2, pow_two] at this
    have hw1 : w ≠ 1 := fun e => by
      rw [e, orderOf_one] at hw2
      omega
    have hnle : ¬ E ≤ zpowers w := by
      intro hle
      have h2 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hw2] at h2
      omega
    obtain ⟨x, hxE, hxw⟩ := SetLike.not_le_iff_exists.1 hnle
    have hx1 : x ≠ 1 := fun e => hxw (by rw [e]; exact Subgroup.one_mem _)
    have hxx : x * x = 1 := mul_self_eq_one_of_isElemAbelian hE hxE
    have hwx : w ≠ x := fun e => hxw (by rw [← e]; exact Subgroup.mem_zpowers w)
    have hcwx : Commute w x := commute_of_isElemAbelian hE hwE hxE
    have hF4 : Nat.card (four w x hww hxx hcwx) = 4 := card_four hww hxx hcwx hw1 hx1 hwx
    have hnleF : ¬ E ≤ four w x hww hxx hcwx := by
      intro hle
      have h2 := Subgroup.card_le_of_le hle
      omega
    obtain ⟨y, hyE, hyF⟩ := SetLike.not_le_iff_exists.1 hnleF
    have hxF : x ∈ four w x hww hxx hcwx := right_mem_four
    have hwF : w ∈ four w x hww hxx hcwx := left_mem_four
    have hy1 : y ≠ 1 := fun e => hyF (by rw [e]; exact Subgroup.one_mem _)
    have hyy : y * y = 1 := mul_self_eq_one_of_isElemAbelian hE hyE
    have hxy : x ≠ y := fun e => hyF (by rw [← e]; exact hxF)
    have hcxy : Commute x y := commute_of_isElemAbelian hE hxE hyE
    refine ⟨four x y hxx hyy hcxy, four_le hxE hyE, isElemAbelian_four x y hxx hyy hcxy,
      card_four hxx hyy hcxy hx1 hy1 hxy, fun hwU => ?_⟩
    rcases mem_four.1 hwU with e | e | e | e
    · apply hyF
      have hy : y = x * w := by rw [e, ← mul_assoc, hxx, one_mul]
      rw [hy]
      exact Subgroup.mul_mem _ hxF hwF
    · exact hxw (by rw [← e]; exact Subgroup.mem_zpowers w)
    · exact hyF (by rw [← e]; exact hwF)
    · exact hw1 e
  · obtain ⟨U, hUE, hU, hU4⟩ := exists_fourSub_of_le_card hE (by omega)
    exact ⟨U, hUE, hU, hU4, fun hw => hwE (hUE hw)⟩

private theorem exists_fourSub_not_z (h : Sec5Data X n z (zpowers z) S) (hR : AhatFourInE8 n)
    {A Q : Subgroup X} (hA : Sec5Comp X n (centralizer ({z} : Set X)) A) (hQ : IsSylowOf 2 Q A) :
    ∃ U : Subgroup X, U ≤ Q ∧ Open.IsElemAbelian 2 U ∧ Nat.card U = 4 ∧ z ∉ U := by
  obtain ⟨E, hEQ, hE, hE4⟩ := exists_four_le_sylow h.maxdeg.1 hA hQ
  obtain ⟨U₀, hU₀E, hU₀, hU₀4⟩ := exists_fourSub_of_le_card hE hE4
  obtain ⟨E', hE'Q, hE', hE'8, -⟩ :=
    fourInE8_of_ahat hR hA (isSylowOf_iff.1 hQ) U₀ (hU₀E.trans hEQ) hU₀ hU₀4
  obtain ⟨U, hUE', hU, hU4, hzU⟩ := exists_fourSub_not_mem hE' hE'8 h.orderOf_z
  exact ⟨U, hUE'.trans hE'Q, hU, hU4, hzU⟩

theorem oddCore_le_normalizer_W1 (h : Sec5Data X n z (zpowers z) S) (hR : AhatFourInE8 n)
    {A₁ : Subgroup X} (hA₁ : Sec5Comp X n (centralizer ({z} : Set X)) A₁) {b : X}
    (hb : CompInv X n z b) :
    oddCoreOf (centralizer ({b} : Set X)) ≤ normalizer ((W1 A₁ : Subgroup X) : Set X) := by
  obtain ⟨A, hA, hbA, hb2⟩ := hb
  by_cases hbA₁ : b ∈ A₁
  · exact (oddCoreOf_cen_le_W1 hbA₁ hb2).trans Subgroup.le_normalizer
  have hne : A ≠ A₁ := fun e => hbA₁ (e ▸ hbA)
  have hbC : b ∈ centralizer ({z} : Set X) := comp_le hA hbA
  obtain ⟨hnorm, hcomm⟩ := normalizes_of_comm hA₁ (Subgroup.le_normalizer hbC) fun a ha =>
    comm_mem_of_ne hA₁ hA hne.symm a ha b hbA
  obtain ⟨Q, hQ, hQb⟩ := exists_sylow_le_cen hb2 hnorm hcomm
  obtain ⟨U, hUQ, hU, hU4, hzU⟩ := exists_fourSub_not_z h hR hA₁ hQ
  have hUN : U ≤ normalizer (oddCoreOf (centralizer ({b} : Set X)) : Set X) :=
    (hUQ.trans hQb).trans (le_normalizer_oddCoreOf _)
  have hgen := CoreAux.le_iSup_inf_cen_of_four hU hU4.ge hUN (odd_card_oddCoreOf _)
  refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => inf_le_right.trans ?_)
  have haA₁ : a ∈ A₁ := hQ.le (hUQ ha)
  have ha2 : a * a = 1 := AhatData.sq_of_isElemAbelian hU a ha
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have haz : a ≠ z := fun e => hzU (e ▸ ha)
  have haC : a ∈ centralizer ({z} : Set X) := comp_le hA₁ haA₁
  have hcomm_a : ∀ x ∈ A, ⁅x, a⁆ ∈ oddCoreOf A :=
    (normalizes_of_comm hA (Subgroup.le_normalizer haC) fun x hx =>
      comm_mem_of_ne hA hA₁ hne x hx a haA₁).2
  refine (cen_eq_oddCoreOf_sup_of_comm h hA hao haC hcomm_a).le.trans
    (sup_le ((oddCoreOf_cen_le_W1 haA₁ hao).trans Subgroup.le_normalizer) ?_)
  intro y hy
  exact normalizer_le_normalizer_W1 A₁
    (mem_normalizer_comp_of_mem_cen h hA₁ haA₁ hao haz hy.1 hy.2)

theorem zHull_le_oddCore (h : Sec5Data X n z (zpowers z) S) {M : Subgroup X}
    (hzM : ∀ m ∈ M, ⁅m, z⁆ ∈ oddCoreOf M)
    (hb : ∀ b : X, CompInv X n z b → oddCoreOf (centralizer ({b} : Set X)) ≤ M) :
    zHull X n z ≤ oddCoreOf M := by
  unfold zHull
  refine iSup₂_le fun b hbI => ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rcases zpowers_eq_of_orderOf_two h.orderOf_z y hy with rfl | rfl
  · simp only [commutatorElement_one_right]
    exact Subgroup.one_mem _
  · exact hzM x (hb b hbI hx)

private theorem comm_le_zHull {b : X} (hb : CompInv X n z b) :
    ⁅oddCoreOf (centralizer ({b} : Set X)), zpowers z⁆ ≤ zHull X n z :=
  le_iSup₂_of_le b hb le_rfl

private theorem compInv_conj {c b : X} (hc : c ∈ centralizer ({z} : Set X))
    (hb : CompInv X n z b) : CompInv X n z (c * b * c⁻¹) := by
  obtain ⟨A, hA, hbA, hb2⟩ := hb
  refine ⟨A.map (MulAut.conj c).toMonoidHom, Sec5Comp.map_conj hA (Subgroup.le_normalizer hc),
    ⟨b, hbA, by simp [MulAut.conj_apply]⟩, ?_⟩
  have := MulEquiv.orderOf_eq (MulAut.conj c) b
  rw [hb2] at this
  exact this

private theorem map_conj_zpowers {c : X} (hc : c ∈ centralizer ({z} : Set X)) :
    (zpowers z).map (MulAut.conj c).toMonoidHom = zpowers z := by
  rw [MonoidHom.map_zpowers]
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 hc
  have : (MulAut.conj c).toMonoidHom z = z := by
    simp [MulAut.conj_apply, hcz]
  rw [this]

private theorem map_conj_zHull_le {c : X} (hc : c ∈ centralizer ({z} : Set X)) :
    (zHull X n z).map (MulAut.conj c).toMonoidHom ≤ zHull X n z := by
  unfold zHull
  rw [Subgroup.map_iSup]
  refine iSup_le fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hb => ?_
  rw [Subgroup.map_commutator, map_conj_oddCoreOf_cen c b, map_conj_zpowers hc]
  exact le_iSup₂_of_le (c * b * c⁻¹) (compInv_conj hc hb) le_rfl

private theorem le_normalizer_zHull :
    centralizer ({z} : Set X) ≤ normalizer ((zHull X n z : Subgroup X) : Set X) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact map_conj_zHull_le hc ⟨w, hw, rfl⟩
  · intro hw
    have := map_conj_zHull_le (Subgroup.inv_mem _ hc) ⟨c * w * c⁻¹, hw, rfl⟩
    have e : (MulAut.conj c⁻¹).toMonoidHom (c * w * c⁻¹) = w := by
      simp [MulAut.conj_apply, mul_assoc]
    rwa [e] at this

private theorem oddCoreOf_cen_le_zHull_sup (h : Sec5Data X n z (zpowers z) S) {b : X}
    (hb : CompInv X n z b) :
    oddCoreOf (centralizer ({b} : Set X)) ≤ zHull X n z ⊔ centralizer ({z} : Set X) := by
  have hzb : z ∈ centralizer ({b} : Set X) := by
    obtain ⟨A, hA, hbA, -⟩ := hb
    exact mem_centralizer_singleton_iff.2 (comm_z_of_mem_comp hA hbA).symm
  have hVN : zpowers z ≤ normalizer (oddCoreOf (centralizer ({b} : Set X)) : Set X) :=
    (Subgroup.zpowers_le.2 hzb).trans (le_normalizer_oddCoreOf _)
  have hfact := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers z) (oddCoreOf (centralizer ({b} : Set X))) h.isPGroup_Z hVN
    (Nat.coprime_two_left.mpr (odd_card_oddCoreOf _))
  have hcen : centralizer ((zpowers z : Subgroup X) : Set X) ≤ centralizer ({z} : Set X) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers z))
  calc oddCoreOf (centralizer ({b} : Set X))
      = ⁅oddCoreOf (centralizer ({b} : Set X)), zpowers z⁆ ⊔
        (oddCoreOf (centralizer ({b} : Set X)) ⊓ centralizer ((zpowers z : Subgroup X) : Set X)) :=
        hfact.symm
    _ ≤ _ := sup_le (le_sup_of_le_left (comm_le_zHull hb))
        (inf_le_right.trans (hcen.trans le_sup_right))

theorem oddHull_zHull (h : Sec5Data X n z (zpowers z) S)
    (hodd : Odd (Nat.card (zHull X n z))) : OddHull X n z (zHull X n z) :=
  ⟨hodd, le_normalizer_zHull, fun _ hb => oddCoreOf_cen_le_zHull_sup h hb⟩

theorem oddHull_bot
    (hall : ∀ b : X, CompInv X n z b →
      oddCoreOf (centralizer ({b} : Set X)) ≤ centralizer ({z} : Set X)) :
    OddHull X n z ⊥ := by
  refine ⟨?_, fun x _ => ?_, fun b hb => (hall b hb).trans le_sup_right⟩
  · rw [Subgroup.card_bot]
    exact odd_one
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hy
      have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [this, hy]
      group

theorem exists_oddHull
    (h : Sec5Data X n z (zpowers z) S) (hne : TwoComps X n z) :
    ∃ O : Subgroup X, OddHull X n z O := by
  have hR : AhatFourInE8 n := ahatFourInE8_holds n h.maxdeg.1
  by_cases hall : ∀ b : X, CompInv X n z b →
      oddCoreOf (centralizer ({b} : Set X)) ≤ centralizer ({z} : Set X)
  · exact ⟨⊥, oddHull_bot hall⟩
  push Not at hall
  obtain ⟨b₀, ⟨A₁, hA₁, hb₀A, hb₀2⟩, hb₀⟩ := hall
  obtain ⟨A₂, hA₂, hA₂ne⟩ := exists_comp_ne A₁ hne
  have hM : normalizer ((W1 A₁ : Subgroup X) : Set X) ≠ ⊤ :=
    normalizer_W1_ne_top h hR hne hA₁ ⟨b₀, hb₀A, hb₀2, hb₀⟩
  have hZ := zStar_of_two_comps h hM hA₁ hA₂ (Ne.symm hA₂ne) (comp_le_normalizer_W1 hA₁ hA₁)
    (comp_le_normalizer_W1 hA₁ hA₂)
  have hle := zHull_le_oddCore h hZ fun b hb => oddCore_le_normalizer_W1 h hR hA₁ hb
  exact ⟨zHull X n z, oddHull_zHull h
    (Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le hle))⟩

theorem twoComp_of_pieces
    (h5 : ComponentClassification.GSThmB.AschbacherTheorem5Input) : Solomon75TwoComp := by
  intro X _ _ n z S h hne
  obtain ⟨O, hO⟩ := exists_oddHull h hne
  exact false_of_oddHull h5 h hne hO

theorem twoComp_holds :
    Solomon75TwoComp :=
  twoComp_of_pieces ComponentClassification.GSThmB.aschbacherTheorem5Input_holds

end CFSG.OddStandard.Solomon75
