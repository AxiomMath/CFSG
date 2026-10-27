module

public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes
public import CFSG.RankThree.PartOne.CTP.SeitzSpGeneration

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration CFSG.Open

section B4

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.CatLeafProof

theorem iSup_b4Chain_le_closure_centralizers_of_sp {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1)
    (Ψ : StatedSp 4 K →* adjointGroup .F4 K) (hker : Ψ.ker ≤ Subgroup.center (StatedSp 4 K))
    (hrange : Ψ.range = ⨆ k, b4Chain K k)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEc : Nat.card E = p ^ 2) :
    ⨆ k, b4Chain K k ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : Finite (StatedSp 4 K) := inferInstance
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (StatedSp 4 K)) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      show (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K) =
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 4 K from rfl,
      CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num)]
    intro hd
    have h2 := (Nat.dvd_prime Nat.prime_two).1 (hd.trans (Nat.gcd_dvd_left 2 _))
    omega
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd => hcen (hd.trans (Subgroup.card_dvd_of_le hker))
  have hpℓ : p ≠ ringChar K := by
    intro h
    have hd : p ∣ Nat.card K := by rw [hK, ← h]; exact dvd_pow_self p (n.ne_zero)
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_pow hd (by norm_num : (2 : ℕ) ≠ 0))).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ Ψ.range := hrange ▸ hE
  set Ψ' : StatedSp 4 K →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ := exists_lift_elemAbelian Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 2 := by
    rw [hE1def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv, hEc]
  have hcardE' : Nat.card E' = p ^ 2 := by
    rw [← hcardE1, ← hmapE', card_map_eq_of_disjoint Ψ' hdisE']
  have : CFSG.IsElementaryAbelian p E' :=
    { toIsMulCommutative := hE'ea.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE'ea.2 x x.2) }
  have htop := CFSG.RankThree.PartOne.CTP.closure_centralizers_spPlane
    (⟨hℓ, n.pos, hK, hp, by omega, hpℓ, by norm_num, by omega, this, hcardE'⟩ :
      CFSG.RankThree.PartOne.KCSpFull.SpPlaneSetup (ringChar K) n p 4 K E')
  intro g hg
  rw [← hrange] at hg
  obtain ⟨h, rfl⟩ := hg
  have hh : h ∈ Subgroup.closure {g : StatedSp 4 K | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g} := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmap : (Subgroup.closure {g : StatedSp 4 K | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g}).map Ψ ≤
      Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
    have hxE : Ψ x ∈ E := by
      have h1 : Ψ' x ∈ E1 := hmapE' ▸ ⟨x, hx, rfl⟩
      exact h1
    have hx1' : Ψ x ≠ 1 := by
      intro h1
      apply hx1
      refine Subgroup.disjoint_def.mp hdisE' hx ?_
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    refine Subgroup.subset_closure ⟨Ψ x, hxE, hx1', ?_⟩
    change Ψ k * Ψ x = Ψ x * Ψ k
    rw [← map_mul, ← map_mul, hkx]
  exact hmap ⟨h, hh, rfl⟩

end B4

end CFSG.HardMathSupport.Lang.AnisoF4
