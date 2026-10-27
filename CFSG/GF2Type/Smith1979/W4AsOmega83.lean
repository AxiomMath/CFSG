module

public import CFSG.GF2Type.Smith1979.W4AsStab
public import CFSG.GF2Type.Smith1979.W4AsTorus
public import CFSG.GF2Type.Smith1979.W4O83Main
public import CFSG.GF2Type.Smith1979.W4Rank3
public import CFSG.LargeExtraspecial.S5Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup CFSG.LargeExtraspecial CFSG.GF2Type.Smith1979.W4O83 CFSG.Open
open CFSG.Yardstones.M3aba7dc4b8a8

section Config

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_omega83Config (hw : S.width = 4) (hno : S11.NoA2All S)
    (hTI : WeaklyClosedTITransitive.{0}) (hirr : ¬ S.IsReducible)
    (hex : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) {E : Subgroup S.O}
    (hEM : E ≤ S.Mbar) (hel : IsElemAbelian 3 E) (hE : Nat.card E = 3 ^ 4) :
    Nonempty (Omega83Config S) := by
  obtain ⟨C, hCE⟩ := exists_omega83Pre hw hEM hel hE
  have hbase := hyp4_cons311_of_w4 hTI hw hno hirr
  have hE81 : Nat.card E ∣ 3 ^ 4 := hE ▸ dvd_rfl
  have hfull : ∀ {x : S.O}, x ∈ S.Mbar → ∀ v, (∀ k, C.prL k v ≠ 0) →
      ∀ k, C.prL k ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ≠ 0 := fun hx v hv =>
    full_apply_of_mem_Mbar C hEM hel.2 hE81 hCE hw hbase hex hx hv
  let F : Subgroup S.O := closure (Set.range C.theta)
  have hθF : ∀ i, C.theta i ∈ F := fun i => subset_closure ⟨i, rfl⟩
  have hFE : F ≤ E := (closure_le E).mpr (by rintro _ ⟨i, rfl⟩; exact hCE i)
  have hFM : F ≤ S.Mbar := hFE.trans hEM
  have hnorm : ∀ x ∈ S.Mbar, ∀ y ∈ F, x * y * x⁻¹ ∈ F := by
    intro x hx y hy
    induction hy using closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, hj | hj⟩ := conj_theta_mem C (hfull hx) (hfull (inv_mem hx)) i
      · rw [hj]
        exact hθF j
      · rw [hj]
        exact pow_mem (hθF j) 2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  have hN : (F.subgroupOf S.Mbar).Normal :=
    ⟨fun n hn m => mem_subgroupOf.mpr (by
      have := hnorm (m : S.O) m.2 (n : S.O) (mem_subgroupOf.mp hn)
      simpa using this)⟩
  have hodd : Odd (Nat.card (F.subgroupOf S.Mbar)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFM).toEquiv]
    refine Odd.of_dvd_nat (n := 3 ^ 4) (Odd.pow (by decide)) ?_
    exact (card_dvd_of_le hFE).trans hE81
  have hle := CFSG.LargeExtraspecial.S5.le_timmesfeldOddCore hN hodd
  refine ⟨{ toOmega83Pre := C, theta_mem_oddCore := fun i => ?_ }⟩
  exact mem_map.mpr ⟨⟨C.theta i, hFM (hθF i)⟩, hle (mem_subgroupOf.mpr (hθF i)), rfl⟩

end Config

section Certificates

variable {G : Type} [Group G] [Finite G] {z : G}

theorem false_of_gen4 (hset : GF2RankFourSetting G z) (S : Setting G) (hSz : S.z = z)
    (hSQ : S.QG = coreQ z) (hw : S.width = 4) (hno : S11.NoA2All S)
    (hTI : WeaklyClosedTITransitive.{0}) (hirr : ¬ S.IsReducible)
    (hnwc : ¬ ZWeaklyClosedInCore z) (hS4 : CFSG.GH74.SectionalTwoRankLE S.Mbar 4) : False := by
  obtain ⟨E, hEM, hEel, r, hr, hEcard⟩ :=
    exists_elemAbelian_three_of_sectional hset S hSz hw hS4
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; positivity)
  have hdvd : 3 ^ 4 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 3 hr
  obtain ⟨E', hE'card, -, hE'E⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (H := ⊥) (L := E) (by simp) hdvd bot_le
  have hE'el : IsElemAbelian 3 E' :=
    ⟨⟨⟨fun a b => Subtype.ext (by
      have := hEel.1.is_comm.comm (⟨a, hE'E a.2⟩ : E) ⟨b, hE'E b.2⟩
      simpa using congrArg Subtype.val this)⟩⟩, fun x hx => hEel.2 x (hE'E hx)⟩
  have hex : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
    by_contra hcon
    refine hnwc fun g hg => ?_
    by_contra hne
    refine hcon ⟨g⁻¹, ?_, ?_⟩
    · rw [hSQ, hSz, inv_inv]
      exact hg
    · rw [hSz, inv_inv]
      exact hne
  obtain ⟨C⟩ := exists_omega83Config hw hno hTI hirr hex (hE'E.trans hEM) hE'el hE'card
  exact false_of_omega83_of_not_weaklyClosed hset S hSz hSQ hw hno hTI hirr hnwc C

end Certificates

end CFSG.GF2Type.Smith1979.W4As
