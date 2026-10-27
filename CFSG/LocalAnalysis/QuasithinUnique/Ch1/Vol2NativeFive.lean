module

public import CFSG.Quasithin.Vol2.Ch1Five
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch1Chief

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_1_four
  lemma_1_2_1_four_strong lemma_1_2_1_five lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_1_five_of_core (hl2 : L2MultiplierFact) {H L : Subgroup G}
    (hL : L ∈ cComp H) (hcore : A36CoreCat (modO2Image H L))
    (hZ : pCoreOf 2 L ≤ centerOf L) (hm : 1 < CFSG.Open.pRank 2 L) : CFSG.IsQuasisimple ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection hL
  have hperf : Group.IsPerfect ↥L := A36A.isPerfect_of_mem_cComp hL
  have hKc : ψ.ker ≤ Subgroup.center ↥L := by
    rw [hker]
    intro x hx
    have hxG : (x : G) ∈ pCoreOf 2 L := by
      exact ⟨x, hx, rfl⟩
    have hxc := (hZ hxG).2
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp hxc (g : G) g.2))
  have hqs : CFSG.IsQuasisimple ↥(modO2Image H L) → CFSG.IsQuasisimple ↥L := fun h =>
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf ψ hψ hKc).mpr h
  have hcase : A36Case3 ↥(modO2Image H L) ∨ A36Case4 ↥(modO2Image H L) → False := by
    intro h34
    obtain ⟨r, hr, h5, χ₀, hχ₀, hχ₀ker⟩ := exists_sl2_surjection_of_case34 h34
    have hr2 : r ≠ 2 := by omega
    have hFO := hcore.2.1.1
    have hFodd : Odd (Nat.card ↥χ₀.ker) := by
      rw [hχ₀ker, hFO]
      exact A312.odd_card_oddCore _
    have hodd : ∀ x ∈ χ₀.ker, Odd (orderOf x) := fun x hx =>
      Odd.of_dvd_nat hFodd (Subgroup.orderOf_dvd_natCard _ hx)
    have hK₀ : ψ.ker = ⊥ := by
      let χ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r) := χ₀.comp ψ
      have hχ : Function.Surjective χ := hχ₀.comp hψ
      have hKF : ψ.ker ≤ χ.ker := fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        simp [χ, hx]
      have hK2 : IsPGroup 2 ψ.ker := by
        rw [hker]
        exact CFSG.pCore_isPGroup
      have hrel : Odd (ψ.ker.relIndex χ.ker) := by
        rw [Subgroup.relIndex_ker, ← MonoidHom.comap_ker χ₀ ψ,
          Subgroup.map_comap_eq_self_of_surjective hψ]
        exact hFodd
      obtain ⟨W, hWn, -, hKW, hsup⟩ :=
        exists_normal_complement_of_central_two_part (F₁ := χ.ker) hKF hKc hK2 hrel
      exact eq_bot_of_central_two_part hl2 hr h5 hperf χ hχ hKc hKW hsup.symm
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hK₀
    obtain ⟨E, hEL, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two L
    have hle := card_le_two_of_elemAbelian hr hr2 ψ hinj χ₀ hodd hEL hE
    rw [hEcard] at hle
    have h4 : 2 ^ 2 ≤ 2 ^ CFSG.Open.pRank 2 L := Nat.pow_le_pow_right (by norm_num) hm
    omega
  rcases hcore.1 with hc | h3 | h4
  · exact hqs hc.1
  · exact (hcase (Or.inl h3)).elim
  · exact (hcase (Or.inr h4)).elim

theorem lemma_1_2_1_five_core (hK : LocalSQTK G) (h36 : A36CoreForSQTKCat)
    (hl2 : L2MultiplierFact) {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H)
    (hZ : pCoreOf 2 L ≤ centerOf L) (hm : 1 < CFSG.Open.pRank 2 L) : CFSG.IsQuasisimple ↥L :=
  lemma_1_2_1_five_of_core hl2 hL (lemma_1_2_1_four_core hK h36 hH hL) hZ hm

theorem lemma_1_2_1_five (hK : LocalSQTK G) (h36 : A36ForSQTKCat) (hl2 : L2MultiplierFact)
    {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H)
    (hZ : pCoreOf 2 L ≤ centerOf L) (hm : 1 < CFSG.Open.pRank 2 L) : CFSG.IsQuasisimple ↥L :=
  lemma_1_2_1_five_core hK h36.core hl2 hH hL hZ hm

end Ambient

end CFSG.QuasithinUnique.Vol2Native
