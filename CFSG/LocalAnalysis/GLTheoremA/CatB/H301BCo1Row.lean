module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1Nat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Bridge.Co1Surj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Co1Patterson

section Centre


theorem co1_central_eq_one (t : NativeSporadic.Co1) (ht : ∀ u : NativeSporadic.Co1, u * t = t * u) :
    t = 1 := by
  haveI : IsSimpleGroup NativeSporadic.Co1 := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  have hnc : ¬ IsMulCommutative NativeSporadic.Co1 := by
    intro hcomm
    haveI : IsMulCommutative NativeSporadic.Co1 := hcomm
    have hp : (Nat.card NativeSporadic.Co1).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [CFSG.Sporadic.Co1.card_Co1] at hp
    exact (by norm_num : ¬ Nat.Prime 4157776806543360000) hp
  have hZ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
    (G := NativeSporadic.Co1) hnc
  exact Subgroup.mem_bot.1 (hZ ▸ Subgroup.mem_center_iff.2 ht)

end Centre

section Row


theorem rowCo1_holds (hU : UCo1) : I301BRow .co1 := by
  intro S _ _ hS B I K R0 R1 y _ hBe hBc hyB hy1 _ _ _ hR0y hR0 hR0c _ _ hKB hR1 hKB1 h01
  obtain ⟨i, hi, ⟨e₁⟩⟩ := hS
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have eS : S ≃* NativeSporadic.Co1 := e₁.trans (by exact b.symm)
  have hAut : ∀ α : MulAut NativeSporadic.Co1, ∃ g : NativeSporadic.Co1, α = MulAut.conj g :=
    Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
        Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner
  have hZ : ∀ t : NativeSporadic.Co1, (∀ u : NativeSporadic.Co1, u * t = t * u) → t = 1 :=
    co1_central_eq_one
  have hAutS : ∀ α : MulAut S, ∃ g : S, α = MulAut.conj g :=
    @CFSG.Sporadic.Co2Schreier.forall_inner_of_mulEquiv S NativeSporadic.Co1 _ inferInstance eS hAut
  obtain ⟨Φ⟩ := @nonempty_mulAut_equiv_of_inner S NativeSporadic.Co1 _ inferInstance eS hZ hAutS
  haveI : Finite (MulAut S) := Finite.of_equiv _ Φ.symm.toEquiv
  have hR0c' : Nat.card R0 = 2 ^ 7 := hR0c
  have hBe' : IsElemAbelian 3 B := hBe
  have hBc' : Nat.card B = 3 ^ 4 := hBc
  have hR0e : timmesfeldIsExtraspecial ↥R0 := hR0.resolve_right (by rw [hR0c']; norm_num)
  obtain ⟨c, hc1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥R0)).mp hR0e.2.2.2
  set z : MulAut S := ((c : ↥R0) : MulAut S) with hz
  have hzR0 : z ∈ R0 := (c : ↥R0).2
  have hzc : ∀ r ∈ R0, r * z = z * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨r, hr⟩)
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hz2 : orderOf z = 2 := by
    have h1 : orderOf c ∣ 2 := hR0e.2.2.2 ▸ orderOf_dvd_natCard c
    have h2 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
    have h3 : orderOf c = 2 := ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left h2
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, h3]
  have hBA : B ≤ K ⊔ B := le_sup_right
  have hBz : B ≤ Subgroup.centralizer ({z} : Set (MulAut S)) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_mem_normalizer hR0e hzR0 hzc hz1 (hKB (hBA ha)))
  have h81 : 3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({Φ z} : Set NativeSporadic.Co1)) := by
    rw [← CFSG.Sporadic.Co1Block.card_centralizer_equiv Φ z, ← hBc']
    exact Subgroup.card_dvd_of_le hBz
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_aNC_of_dvd (by rw [MulEquiv.orderOf_eq, hz2]) h81)
  let e : MulAut S ≃* NativeSporadic.Co1 := Φ.trans (MulAut.conj g)
  have hez : e z = aNC := by
    show g * Φ z * g⁻¹ = aNC
    exact hg
  have D : TwoCentralData 4 (e z) co1R := by
    rw [hez]
    exact twoCentralData_co1 hU
  have D' := @TwoCentralData.comap (MulAut S) NativeSporadic.Co1 _ inferInstance e 4 z co1R D
  exact index_four_core D' (by norm_num) hBe' hBc' hyB hy1 hR0e hR0c' hzR0 hzc
    (fun r hr => (Subgroup.mem_centralizer_singleton_iff.1 (hR0y hr)).symm) hKB hR1 hKB1 h01

end Row

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
