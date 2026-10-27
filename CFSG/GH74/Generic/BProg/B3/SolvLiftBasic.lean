module

public import CFSG.GH74.GLS.Balance.Lift
public import CFSG.GH74.GLS.Balance.Reduce
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.Generic.BProg.Stage2QSProofAbs
public import CFSG.GH74.Generic.BProg.Vocab

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup
open scoped MatrixGroups

namespace SolvLiftBasic

theorem isSolv2CompIn_le {X : Type} [Group X] {H L : Subgroup X} (h : IsSolv2CompIn H L) : L ≤ H := by
  obtain ⟨Lb, -, -, rfl⟩ := h
  exact Subgroup.map_subtype_le _

theorem extLayer2_le {X : Type} [Group X] (H : Subgroup X) : extLayer2 H ≤ H := by
  refine sup_le (B1.pLayerOf_le 2 H) ?_
  exact iSup₂_le fun L hL => isSolv2CompIn_le hL

theorem exists_sl23_of_isSolv2CompIn {X : Type} [Group X] [Finite X] {H Ib : Subgroup X}
    (h : IsSolv2CompIn H Ib) :
    ∃ π : ↥Ib →* SL(2, ZMod 3), Function.Surjective π ∧ Odd (Nat.card π.ker) := by
  have hle : Ib ≤ H := isSolv2CompIn_le h
  obtain ⟨Ibb, -, ⟨e⟩, hIb⟩ := h
  set mkH : ↥H →* ↥H ⧸ pPrimeCore 2 ↥H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hmk
  have hmem : ∀ b : ↥Ib, mkH (Subgroup.inclusion hle b) ∈ Ibb := by
    intro b
    have hb : (b : X) ∈ (Ibb.comap mkH).map H.subtype := by
      rw [← hIb]
      exact b.2
    obtain ⟨z, hz, hzb⟩ := hb
    have hzb' : Subgroup.inclusion hle b = z := Subtype.ext hzb.symm
    rw [hzb']
    exact hz
  let ρ : ↥Ib →* ↥Ibb := (mkH.comp (Subgroup.inclusion hle)).codRestrict Ibb hmem
  refine ⟨e.toMonoidHom.comp ρ, ?_, ?_⟩
  · intro u
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) ((e.symm u : ↥Ibb) : ↥H ⧸ pPrimeCore 2 ↥H)
    have hzc : z ∈ Ibb.comap mkH := by
      show mkH z ∈ Ibb
      rw [show mkH z = ((e.symm u : ↥Ibb) : ↥H ⧸ pPrimeCore 2 ↥H) from hz]
      exact (e.symm u).2
    have hzIb : (z : X) ∈ Ib := by
      rw [hIb]
      exact ⟨z, hzc, rfl⟩
    refine ⟨⟨(z : X), hzIb⟩, ?_⟩
    have hρ : ρ ⟨(z : X), hzIb⟩ = e.symm u := Subtype.ext hz
    show e (ρ ⟨(z : X), hzIb⟩) = u
    rw [hρ]
    exact e.apply_symm_apply u
  · refine Balance.odd_card_of_forall_odd_orderOf _ fun g hg => ?_
    have hg1 : e (ρ g) = 1 := MonoidHom.mem_ker.1 hg
    have hg2 : ρ g = 1 := e.map_eq_one_iff.1 hg1
    have hg3 : mkH (Subgroup.inclusion hle g) = 1 := congrArg Subtype.val hg2
    have hg4 : Subgroup.inclusion hle g ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).1 hg3
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥H) hg4
    rw [orderOf_injective _ (Subgroup.inclusion_injective hle) g] at hdvd
    exact Odd.of_dvd_nat (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hdvd

section Preimage

variable {G : Type} [Group G] [Finite G] {Q : Type*} [Group Q]

theorem exists_preimageHom {Y : Subgroup G} (φ : ↥Y →* Q) (hφ : ¬ 2 ∣ Nat.card φ.ker)
    {Ib : Subgroup Q} (hIb : Ib ≤ φ.range) {I1 : Subgroup G} (hI1 : I1 = (Ib.comap φ).map Y.subtype) :
    ∃ θ : ↥I1 →* ↥Ib, Function.Surjective θ ∧ Odd (Nat.card θ.ker) ∧
      ∀ (z : ↥I1) (hz : (z : G) ∈ Y), ((θ z : ↥Ib) : Q) = φ ⟨(z : G), hz⟩ := by
  subst hI1
  have hI1Y : (Ib.comap φ).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
  have hmem : ∀ z : ↥((Ib.comap φ).map Y.subtype), φ (Subgroup.inclusion hI1Y z) ∈ Ib := by
    rintro ⟨z, y, hy, rfl⟩
    exact hy
  let θ : ↥((Ib.comap φ).map Y.subtype) →* ↥Ib :=
    (φ.comp (Subgroup.inclusion hI1Y)).codRestrict Ib hmem
  refine ⟨θ, ?_, ?_, fun z hz => rfl⟩
  · rintro ⟨b, hb⟩
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 (hIb hb)
    exact ⟨⟨(y : G), ⟨y, hb, rfl⟩⟩, Subtype.ext rfl⟩
  · refine Balance.odd_card_of_forall_odd_orderOf _ fun z hz => ?_
    have hz1 : φ (Subgroup.inclusion hI1Y z) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hz)
    have hz2 : Subgroup.inclusion hI1Y z ∈ φ.ker := hz1
    have hdvd := Subgroup.orderOf_dvd_natCard φ.ker hz2
    rw [orderOf_injective _ (Subgroup.inclusion_injective hI1Y) z] at hdvd
    exact Odd.of_dvd_nat (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hφ)) hdvd

theorem exists_sl23_preimage {Y : Subgroup G} (φ : ↥Y →* Q) (hφ : ¬ 2 ∣ Nat.card φ.ker)
    {Ib : Subgroup Q} (hIb : Ib ≤ φ.range) {I1 : Subgroup G} (hI1 : I1 = (Ib.comap φ).map Y.subtype)
    (hsl : ∃ π : ↥Ib →* SL(2, ZMod 3), Function.Surjective π ∧ Odd (Nat.card π.ker)) :
    ∃ π : ↥I1 →* SL(2, ZMod 3), Function.Surjective π ∧ Odd (Nat.card π.ker) := by
  obtain ⟨θ, hθs, hθo, -⟩ := exists_preimageHom φ hφ hIb hI1
  obtain ⟨π, hπs, hπo⟩ := hsl
  exact ⟨π.comp θ, hπs.comp hθs, Balance.odd_card_ker_comp θ π hθs hθo hπo⟩

theorem exists_two_element_preimage {Y : Subgroup G} (φ : ↥Y →* Q) (hφ : ¬ 2 ∣ Nat.card φ.ker)
    {Ib : Subgroup Q} (hIb : Ib ≤ φ.range) {I1 : Subgroup G} (hI1 : I1 = (Ib.comap φ).map Y.subtype)
    {a : Q} (ha : a ∈ Ib) {k : ℕ} (hk : a ^ (2 ^ k) = 1) :
    ∃ (g : G) (hg : g ∈ Y), g ∈ I1 ∧ (∃ m : ℕ, g ^ (2 ^ m) = 1) ∧ φ ⟨g, hg⟩ = a := by
  obtain ⟨θ, hθs, -, hθ⟩ := exists_preimageHom φ hφ hIb hI1
  obtain ⟨z, hz⟩ := hθs ⟨a, ha⟩
  have hk' : (θ z) ^ (2 ^ k) = 1 := by
    rw [hz]
    exact Subtype.ext (by simpa using hk)
  obtain ⟨n, m, hnm, hθn⟩ := exists_pow_two_power_lift θ z hk'
  have hI1Y : I1 ≤ Y := by
    rw [hI1]
    exact Subgroup.map_subtype_le _
  have hzI : ((z ^ n : ↥I1) : G) ∈ I1 := (z ^ n).2
  have hzY : ((z ^ n : ↥I1) : G) ∈ Y := hI1Y hzI
  refine ⟨((z ^ n : ↥I1) : G), hzY, hzI, ⟨m, ?_⟩, ?_⟩
  · have := congrArg Subtype.val hnm
    simpa using this
  · have h1 := hθ (z ^ n) hzY
    rw [← h1, hθn, hz]

end Preimage

end SolvLiftBasic

end CFSG.GH74.Generic.BProg.B3
