module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7Mod
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Diag
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6L

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G}

section Gen



theorem Data.Hyp.L_le_of_S_K₃_u {K₀ : Subgroup G} (h : d.Hyp) (hKU : d.KUnitary)
    (hf : d.IsUnitaryFactor K₀) {Γ : Subgroup G} (hS : d.S ≤ Γ) (hK₃ : d.K₃ ≤ Γ)
    (hu : d.u ∈ Γ) : d.L ≤ Γ := by
  haveI : IsSimpleGroup ↥d.L := h.isSimpleGroup_L
  haveI : IsSimpleGroup SU52 := d.η.symm.isSimpleGroup
  have hpull : ∀ {M : Subgroup SU52}, d.pull M ≤ Γ → M ≤ Γ.comap d.ι :=
    fun hM g hg => hM (d.ι_mem_pull_iff.2 hg)
  have hSΓ : Ssub ≤ Γ.comap d.ι := hpull hS
  have hK₃Γ : K₃sub ≤ Γ.comap d.ι := hpull hK₃
  have huΓ : uSU ∈ Γ.comap d.ι := hu
  have hK₃card : Nat.card K₃sub = 25920 := by
    have h1 : Nat.card ↥K₀ = Nat.card ↥(Data.theta h hf).range :=
      Nat.card_congr (MonoidHom.ofInjective (Data.theta_injective h hf)).toEquiv
    rw [Data.range_theta h hKU hf, Data.K₃, d.card_pull, hf.card_eq] at h1
    exact h1.symm
  obtain ⟨x, hx, hx11⟩ := exists_orderOf_eleven
  have hxΓ : x ∈ Γ.comap d.ι :=
    (sup_le (sup_le (A₂sub_le_Ssub.trans hSΓ) (K₂sub_le_K₃sub.trans hK₃Γ))
      (zpowers_le.2 huΓ)) hx
  have h11 : 11 ∣ Nat.card (Γ.comap d.ι) := by
    have := Subgroup.orderOf_dvd_natCard (Γ.comap d.ι) hxΓ
    rwa [hx11] at this
  have h2 : 2 ^ 10 ∣ Nat.card (Γ.comap d.ι) := by
    have := Subgroup.card_dvd_of_le hSΓ
    rwa [card_Ssub] at this
  have h3 : 25920 ∣ Nat.card (Γ.comap d.ι) := by
    have := Subgroup.card_dvd_of_le hK₃Γ
    rwa [hK₃card] at this
  have h4 : 4561920 ∣ Nat.card (Γ.comap d.ι) := by
    have e : Nat.lcm (Nat.lcm (2 ^ 10) 25920) 11 = 4561920 := by norm_num
    have := Nat.lcm_dvd (Nat.lcm_dvd h2 h3) h11
    rwa [e] at this
  have hpos : 0 < Nat.card (Γ.comap d.ι) := Nat.card_pos
  have hge : 4561920 ≤ Nat.card (Γ.comap d.ι) := Nat.le_of_dvd hpos h4
  have hmul := Subgroup.card_mul_index (Γ.comap d.ι)
  rw [card_SU52.1] at hmul
  have hidx : (Γ.comap d.ι).index ≤ 3 := by
    have h5 : 4561920 * (Γ.comap d.ι).index ≤ 4561920 * 3 :=
      calc 4561920 * (Γ.comap d.ι).index ≤ Nat.card (Γ.comap d.ι) * (Γ.comap d.ι).index :=
            Nat.mul_le_mul_right _ hge
        _ = 13685760 := hmul
        _ = 4561920 * 3 := by norm_num
    exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
  have htop : Γ.comap d.ι = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Γ.comap d.ι).normalCore with
      hb | ht
    · exfalso
      have hd := Subgroup.index_normalCore_dvd_factorial_index (Γ.comap d.ι)
      rw [hb, Subgroup.index_bot, card_SU52.1] at hd
      have hle := Nat.le_of_dvd (Nat.factorial_pos _) hd
      have hf3 : Nat.factorial (Γ.comap d.ι).index ≤ Nat.factorial 3 := Nat.factorial_le hidx
      have h6 : Nat.factorial 3 = 6 := by decide
      omega
    · exact top_le_iff.1 (ht ▸ Subgroup.normalCore_le (Γ.comap d.ι))
  intro l hl
  rw [← d.range_ι] at hl
  obtain ⟨s, rfl⟩ := hl
  have : s ∈ Γ.comap d.ι := htop ▸ Subgroup.mem_top s
  exact this

end Gen

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
