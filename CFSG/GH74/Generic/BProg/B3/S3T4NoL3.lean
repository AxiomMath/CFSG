module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29A2
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement MatrixGroups

theorem noL3PumpupOfA7Step_of_mem {G : Type} [Group G] [Finite G] :
    ∀ (b u : G) (J M : Subgroup G), PumpUpLT 2 b J u M → IsA7Bar J → b ∈ M →
      ¬ QShape3 (↥M ⧸ pPrimeCore 2 ↥M) := by
  classical
  intro b u J M hlt hA7 hbM h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : orderOf b = 2 := hlt.1.1
  have hu : orderOf u = 2 := hlt.2.1.1
  have hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J := hlt.1.2.2
  have hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have hbY : b ∈ centralizer ({u} : Set G) := TwoThin.mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ⟩ := C3.Layer1.PumpCalc.exists_isLam hu hJ hlt.2.2.2.1
  have hΛM : C3.Layer1.PumpCalc.bar u Λ ≤ C3.Layer1.PumpCalc.bar u M :=
    C3.Layer1.PumpCalc.bar_le_of_stable hlt hΛ (Subgroup.le_normalizer hbM)
  obtain ⟨eM⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hMc
  have hq3 : QShape3 ↥(C3.Layer1.PumpCalc.bar u M) := isL3OddGt3_of_mulEquiv eM h3
  have hZt := B1.PilotS3.center_trivial_of_shape3 hMc h3
  have hZ : ∀ z : ↥(C3.Layer1.PumpCalc.bar u M), (∀ g, g * z = z * g) → z = 1 := by
    intro z hz
    have h1 : eM.symm z = 1 := hZt _ fun g => by
      apply eM.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (eM g)
    simpa using congrArg eM h1
  set sb := C3.Layer1.PumpCalc.sbar b hbY with hsb
  have hsb2 : orderOf sb = 2 := C3.Layer1.PumpCalc.orderOf_sbar hb hbY
  have hsbM : sb ∈ C3.Layer1.PumpCalc.bar u M :=
    ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.2 hbM, rfl⟩
  set t : ↥(C3.Layer1.PumpCalc.bar u M) := ⟨sb, hsbM⟩ with ht
  have ht2 : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_mk]
    exact hsb2
  obtain ⟨F, _, _, S, hodd, -, ⟨eS⟩, htS, -, hcomm, -, -⟩ :=
    S3L3KGroup.exists_sl2_component hq3 hZ ht2
  have hSL := S3Sec29D1.SL2Data.of_equiv eS (S3Sec29D1.sl2Data_sl2 hodd)
  have hcen : ∀ w ∈ C3.Layer1.PumpCalc.bar u Λ, w * sb = sb * w := by
    intro w hw
    have h1 := C3.Layer1.PumpCalc.bar_lam_le_centralizer hbY hΛ w hw
    rw [← hsb] at h1
    calc w * sb = sb * w * sb⁻¹ * sb := by rw [h1]
      _ = sb * w := by group
  set Λ' : Subgroup ↥(C3.Layer1.PumpCalc.bar u M) :=
    (C3.Layer1.PumpCalc.bar u Λ).subgroupOf (C3.Layer1.PumpCalc.bar u M) with hΛ'
  have hΛ'C : Λ' ≤ centralizer ({t} : Set ↥(C3.Layer1.PumpCalc.bar u M)) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hcen w (Subgroup.mem_subgroupOf.1 hw)))
  have hΛ'perf : ⁅Λ', Λ'⁆ = Λ' := by
    apply Subgroup.map_injective (C3.Layer1.PumpCalc.bar u M).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hΛM,
      C3.Layer1.PumpCalc.bar_lam_perfect hΛ]
  have hΛ'S : Λ' ≤ S := by
    rw [← hΛ'perf, Subgroup.commutator_le]
    intro a ha c hc
    exact hcomm a (hΛ'C ha) c (hΛ'C hc)
  have hΛ'ne : Λ' ≠ ⊥ := by
    intro h
    apply C3.Layer1.PumpCalc.bar_lam_ne_bot hΛ
    have := congrArg (Subgroup.map (C3.Layer1.PumpCalc.bar u M).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hΛM, Subgroup.map_bot] at this
  have heven : 2 ∣ Nat.card ↥Λ' := by
    by_contra hodd'
    have hodd'' : Odd (Nat.card ↥Λ') := Nat.odd_iff.2 (by omega)
    have hsol : Group.IsSolvable ↥Λ' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd''
    have : Nontrivial ↥Λ' := (Subgroup.nontrivial_iff_ne_bot _).2 hΛ'ne
    have : Group.IsPerfect ↥Λ' := Subgroup.isPerfect_iff.2 hΛ'perf
    exact Group.IsPerfect.not_isSolvable ↥Λ' hsol
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hτ2 : (τ : ↥(C3.Layer1.PumpCalc.bar u M)) * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rw [hτ, pow_two] at this
    exact congrArg Subtype.val this
  have hτ1 : (τ : ↥(C3.Layer1.PumpCalc.bar u M)) ≠ 1 := by
    intro h1
    have : τ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have ht2' : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hinv : ∀ s : ↥(C3.Layer1.PumpCalc.bar u M), ∀ hs : s ∈ S, s * s = 1 → s ≠ 1 →
      (⟨s, hs⟩ : ↥S) = eS.symm (-1) := by
    intro s hs hss hs1
    rcases hSL.invol_eq ⟨s, hs⟩ (Subtype.ext hss) with h1 | h1
    · exact absurd (congrArg Subtype.val h1) hs1
    · exact h1
  have hτt : (τ : ↥(C3.Layer1.PumpCalc.bar u M)) = t := by
    have h1 := hinv _ (hΛ'S τ.2) hτ2 hτ1
    have h2 := hinv t htS ht2' ht1
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hsbΛ : sb ∈ C3.Layer1.PumpCalc.bar u Λ := by
    have htΛ' : t ∈ Λ' := hτt ▸ τ.2
    exact Subgroup.mem_subgroupOf.1 htΛ'
  obtain ⟨φ, hφs, hφo, -⟩ :=
    TwoThin.exists_phi (hΛ.le.trans inf_le_left) (hΛ.le.trans inf_le_right) hΛ.cover
  set β : ↥(C3.Layer1.PumpCalc.bar u Λ) := ⟨sb, hsbΛ⟩ with hβ
  have hφβ : φ β = 1 := by
    apply centerlessBar_of_A7 hA7
    intro c
    obtain ⟨w, rfl⟩ := hφs c
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcen w w.2).symm
  have hβ2 : orderOf β = 2 := by
    rw [hβ, Subgroup.orderOf_mk]
    exact hsb2
  have hβk : β ∈ φ.ker := hφβ
  have hord : orderOf (⟨β, hβk⟩ : ↥φ.ker) = 2 := (Subgroup.orderOf_mk β hβk).trans hβ2
  have hdvd := orderOf_dvd_natCard (⟨β, hβk⟩ : ↥φ.ker)
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.2 hφo) (even_iff_two_dvd.2 hdvd)

theorem noL3PumpupOfA7Step_proved {G : Type} [Group G] [Finite G] : NoL3PumpupOfA7Step G :=
  noL3PumpupOfA7Step_of_mem

end CFSG.GH74.Generic.BProg.B3
