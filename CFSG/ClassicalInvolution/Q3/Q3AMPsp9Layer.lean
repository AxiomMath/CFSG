module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayer
public import CFSG.ClassicalInvolution.SmallCases.Exclusion.PerfectCore

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidual perfectResidualOf
  finite_perfectResidual_isPerfect perfectResidual_characteristic)
open scoped MatrixGroups

section Quotient

theorem oddCore_eq_ker_of_odd_ker_gen {L S H : Type} [Group L] [Finite L] [Group S] [Group H]
    (φ : L →* S) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (e : S ≃* H) (hH : classicalInvolutionOddCore H = ⊥) :
    classicalInvolutionOddCore L = φ.ker := by
  have : Finite S := Finite.of_surjective φ hφ
  have hOS : classicalInvolutionOddCore S = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e
    have hH' : componentClassificationOddCore H = ⊥ := hH
    rw [hH'] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hle : φ.ker ≤ classicalInvolutionOddCore L :=
    CFSG.ComponentClassification.OddCore.maximal L φ.ker φ.normal_ker hodd
  have hge : classicalInvolutionOddCore L ≤ φ.ker := by
    have hN : ((classicalInvolutionOddCore L).map φ).Normal :=
      Subgroup.Normal.map inferInstance φ hφ
    have hNodd : Odd (Nat.card ((classicalInvolutionOddCore L).map φ)) :=
      (CFSG.ComponentClassification.OddCore.odd_card L).of_dvd_nat
        (Subgroup.card_map_dvd (classicalInvolutionOddCore L) φ)
    have h1 : (classicalInvolutionOddCore L).map φ ≤ classicalInvolutionOddCore S :=
      CFSG.ComponentClassification.OddCore.maximal S _ hN hNodd
    rw [hOS, le_bot_iff] at h1
    intro x hx
    have h2 : φ x ∈ (classicalInvolutionOddCore L).map φ := ⟨x, hx, rfl⟩
    rw [h1] at h2
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp h2)
  exact le_antisymm hge hle

theorem nonempty_equiv_quotient_of_odd_ker_gen {L S H : Type} [Group L] [Finite L] [Group S]
    [Group H] (φ : L →* S) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (e : S ≃* H) (hH : classicalInvolutionOddCore H = ⊥) :
    Nonempty (L ⧸ classicalInvolutionOddCore L ≃* H) := by
  have heq := oddCore_eq_ker_of_odd_ker_gen φ hφ hodd e hH
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e)⟩

theorem oddCore_sl2_eq_bot {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) : classicalInvolutionOddCore SL(2, F) = ⊥ :=
  sl2_normal_odd hodd h3 _ inferInstance (CFSG.ComponentClassification.OddCore.odd_card _)

end Quotient

section Layer

variable {G : Type} [Group G] [Finite G]

theorem exists_layerGen_of_action {H : Type} [Group H] (hH : classicalInvolutionOddCore H = ⊥)
    {Y : Subgroup G} {z s w : G}
    (hYC : Y ≤ Subgroup.centralizer ({z} : Set G))
    (hN : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hzY : z ∈ Y) (hwY : w ∈ Y) (hw : w * w = z) (hsz : s * z = z * s) (hs2 : s * s = 1)
    (hact : ∀ y ∈ Y, s * y * s⁻¹ * (w * y * w⁻¹)⁻¹ ∈ oddCoreOf Y)
    {Lb : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)}
    (hLc : Lb ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)))
    (hLn : ∀ x ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩} :
        Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb)
    (hub : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩ ∈ Lb)
    (hLiso : Nonempty (↥Lb ≃* H)) :
    ∃ L : Subgroup G, L ≤ Y ∧ L ≤ Subgroup.centralizer ({s} : Set G) ∧ z ∈ L ∧
      IsSubnormal L (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* H) ∧
      (∀ (y : G) (hy : y ∈ Y), y ∈ L ↔ y ∈ Subgroup.centralizer ({s} : Set G) ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ ∈ Lb) ∧
      (∀ b ∈ Lb, ∃ (y : G) (hy : y ∈ Y), y ∈ L ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ = b) ∧
      (∀ (y : G) (hy : y ∈ Y), y ∈ Subgroup.centralizer ({s} : Set G) →
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ ∈ Subgroup.centralizer
          ({QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩} :
            Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))) ∧
      (∀ (y : G) (hy : y ∈ Y), y ∈ oddCoreOf L →
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ = 1) := by
  classical
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  set ub := π ⟨w, hwY⟩ with hub'
  have hsC : s ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hsz
  have hNs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := hN s hsC
  have hNs' : ∀ y ∈ Y, s⁻¹ * y * s ∈ Y := fun y hy => by
    simpa using hN s⁻¹ (Subgroup.inv_mem _ hsC) y hy
  have hsO : ∀ o ∈ oddCoreOf Y, s * o * s⁻¹ ∈ oddCoreOf Y := fun o ho =>
    conj_mem_oddCoreOf_of_mem_normalizer hNs hNs' ho
  have hπs : ∀ (y : G) (hy : y ∈ Y) (hy' : s * y * s⁻¹ ∈ Y), π ⟨s * y * s⁻¹, hy'⟩ =
      ub * π ⟨y, hy⟩ * ub⁻¹ := by
    intro y hy hy'
    have hwy : w * y * w⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hwY hy) (Y.inv_mem hwY)
    have h1 := mk'_eq_of_mul_inv_mem hy' hwy (hact y hy)
    rw [h1]
    have : (⟨w * y * w⁻¹, hwy⟩ : ↥Y) = ⟨w, hwY⟩ * ⟨y, hy⟩ * ⟨w, hwY⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  have hlift : ∀ b ∈ Lb, ∃ x : ↥Y, (x : G) ∈ Subgroup.centralizer ({s} : Set G) ∧ π x = b := by
    intro b hb
    obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) b
    have hsy : s * (y₀ : G) * s⁻¹ ∈ Y := hNs _ y₀.2
    have hbc : b * ub = ub * b := Subgroup.mem_centralizer_singleton_iff.mp (hLc hb)
    have h1 : π ⟨s * (y₀ : G) * s⁻¹, hsy⟩ = π y₀ := by
      rw [hπs _ y₀.2 hsy]
      have h0 : π ⟨(y₀ : G), y₀.2⟩ = b := hy₀
      rw [h0, ← hbc]
      group
    have h2 : (y₀ : G)⁻¹ * (s * (y₀ : G) * s⁻¹) ∈ oddCoreOf Y :=
      inv_mul_mem_of_mk'_eq y₀.2 hsy h1.symm
    obtain ⟨o, ho, hfix⟩ := exists_mul_centralizes_of_odd hs2 (oddCoreOf_odd_natCard Y) hsO h2
    have hoY : o ∈ Y := oddCoreOf_le_self Y ho
    obtain ⟨hoY', ho'⟩ := mem_oddCoreOf_iff.mp ho
    refine ⟨⟨(y₀ : G) * o, Y.mul_mem y₀.2 hoY⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show (y₀ : G) * o * s = s * ((y₀ : G) * o)
      have := hfix
      calc (y₀ : G) * o * s = (s * ((y₀ : G) * o) * s⁻¹) * s := by rw [this]
        _ = s * ((y₀ : G) * o) := by group
    · have hπo : π ⟨o, hoY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ho'
      have : (⟨(y₀ : G) * o, Y.mul_mem y₀.2 hoY⟩ : ↥Y) = y₀ * ⟨o, hoY⟩ := rfl
      rw [this, map_mul, hπo, mul_one, hy₀]
  let Lx : Subgroup ↥Y :=
    (Subgroup.centralizer ({s} : Set G)).subgroupOf Y ⊓ Lb.comap π
  have hmemLx : ∀ x : ↥Y, x ∈ Lx ↔ (x : G) ∈ Subgroup.centralizer ({s} : Set G) ∧ π x ∈ Lb :=
    fun x => Iff.rfl
  set L : Subgroup G := Lx.map Y.subtype with hL
  have hLY : ∀ y ∈ L, y ∈ Y ∧ y ∈ Subgroup.centralizer ({s} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, ((hmemLx x).mp hx).1⟩
  set R : Subgroup G := Y ⊓ Subgroup.centralizer ({s} : Set G) with hR
  have hLR : L ≤ R := fun y hy => hLY y hy
  have hRT : R ≤ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) :=
    fun y hy => ⟨hYC hy.1, hy.2⟩
  have hcent : ∀ k : ↥Y, (k : G) ∈ Subgroup.centralizer ({s} : Set G) →
      π k ∈ Subgroup.centralizer ({ub} : Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)) := by
    intro k hk
    have hks : s * (k : G) * s⁻¹ = k := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hk
      rw [← this]
      group
    have hsy : s * (k : G) * s⁻¹ ∈ Y := hNs _ k.2
    have h1 := hπs (k : G) k.2 hsy
    have h2 : π ⟨s * (k : G) * s⁻¹, hsy⟩ = π k := by
      congr 1
      exact Subtype.ext hks
    rw [h2] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc π k * ub = (ub * π k * ub⁻¹) * ub := by rw [← h1]
      _ = ub * π k := by group
  obtain ⟨e⟩ := hLiso
  let φ0 : ↥Lx →* (↥Y ⧸ classicalInvolutionOddCore ↥Y) := π.comp Lx.subtype
  let φ : ↥Lx →* Lb := φ0.codRestrict Lb (fun x => ((hmemLx x.1).mp x.2).2)
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hxc, hxb⟩ := hlift b hb
    exact ⟨⟨x, (hmemLx x).mpr ⟨hxc, by rw [hxb]; exact hb⟩⟩, Subtype.ext hxb⟩
  have hodd : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map Lx.subtype ≤ classicalInvolutionOddCore ↥Y := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : π (x : ↥Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.ker_mk' _).le (MonoidHom.mem_ker.mpr h1)
    have hc : Nat.card (φ.ker.map Lx.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← hc]
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥Y).of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  have heq : classicalInvolutionOddCore ↥Lx = φ.ker :=
    oddCore_eq_ker_of_odd_ker_gen φ hφ hodd e hH
  let iL : ↥Lx ≃* ↥L :=
    Subgroup.equivMapOfInjective Lx Y.subtype (Subgroup.subtype_injective Y)
  have hOL : (classicalInvolutionOddCore ↥Lx).map iL.toMonoidHom =
      classicalInvolutionOddCore ↥L :=
    CFSG.ComponentClassification.OddCore.equiv_invariant iL
  refine ⟨L, fun y hy => (hLY y hy).1, fun y hy => (hLY y hy).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨z, hzY⟩, (hmemLx _).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm, ?_⟩,
      rfl⟩
    have : (⟨z, hzY⟩ : ↥Y) = ⟨w, hwY⟩ * ⟨w, hwY⟩ := Subtype.ext hw.symm
    rw [this, map_mul]
    exact hub
  · refine IsSubnormal.step hLR ?_ (IsSubnormal.step hRT ?_ (IsSubnormal.refl _))
    · rw [Subgroup.normal_subgroupOf_iff hLR]
      rintro _ k ⟨x, hx, rfl⟩ hk
      have hkY : k ∈ Y := hk.1
      have hkx : (⟨k, hkY⟩ * x * ⟨k, hkY⟩⁻¹ : ↥Y) ∈ Lx := by
        refine (hmemLx _).mpr ⟨?_, ?_⟩
        · have hxc : (x : G) ∈ Subgroup.centralizer ({s} : Set G) := ((hmemLx x).mp hx).1
          exact (Subgroup.centralizer ({s} : Set G)).mul_mem
            ((Subgroup.centralizer ({s} : Set G)).mul_mem hk.2 hxc)
            ((Subgroup.centralizer ({s} : Set G)).inv_mem hk.2)
        · rw [map_mul, map_mul, map_inv]
          exact hLn _ (hcent ⟨k, hkY⟩ hk.2) _ ((hmemLx x).mp hx).2
      exact ⟨_, hkx, rfl⟩
    · rw [Subgroup.normal_subgroupOf_iff hRT]
      intro h k hh hk
      exact ⟨hN k hk.1 h hh.1, (Subgroup.centralizer ({s} : Set G)).mul_mem
        ((Subgroup.centralizer ({s} : Set G)).mul_mem hk.2 hh.2)
        ((Subgroup.centralizer ({s} : Set G)).inv_mem hk.2)⟩
  · obtain ⟨e'⟩ := nonempty_equiv_quotient_of_odd_ker_gen φ hφ hodd e hH
    exact ⟨((QuotientGroup.congr _ _ iL hOL).symm).trans e'⟩
  · intro y hy
    constructor
    · intro hyL
      obtain ⟨hy', hyc⟩ := hLY y hyL
      obtain ⟨x, hx, hxy⟩ := hyL
      have hxy' : x = ⟨y, hy⟩ := Subtype.ext hxy
      subst hxy'
      exact ⟨hyc, ((hmemLx _).mp hx).2⟩
    · rintro ⟨hyc, hyb⟩
      exact ⟨⟨y, hy⟩, (hmemLx _).mpr ⟨hyc, hyb⟩, rfl⟩
  · intro b hb
    obtain ⟨x, hxc, hxb⟩ := hlift b hb
    exact ⟨(x : G), x.2, ⟨x, (hmemLx x).mpr ⟨hxc, by rw [hxb]; exact hb⟩, rfl⟩, hxb⟩
  · intro y hy hyc
    exact hcent ⟨y, hy⟩ hyc
  · intro y hy hyO
    obtain ⟨xO, hxO, hxy⟩ := hyO
    have hmem : xO ∈ (classicalInvolutionOddCore ↥Lx).map iL.toMonoidHom := by
      rw [hOL]
      exact hxO
    obtain ⟨x, hx, hxe⟩ := hmem
    have hx1 : φ x = 1 := by
      rw [← MonoidHom.mem_ker, ← heq]
      exact hx
    have hyx : y = ((x : ↥Y) : G) := by
      rw [← hxy, ← hxe]
      rfl
    have h1 : π (x : ↥Y) = 1 := congrArg Subtype.val hx1
    have e2 : (⟨y, hy⟩ : ↥Y) = (x : ↥Y) := Subtype.ext hyx
    rw [e2]
    exact h1

theorem isSectionMember_perfectResidualOf_layer {p f : ℕ} [Fact p.Prime] (h4 : 4 ≤ p ^ f)
    (hf : 0 < f) {Y L : Subgroup G} {z : G} (hLY : L ≤ Y) (hz : orderOf z = 2) (hzL : z ∈ L)
    (hsub : IsSubnormal L (Subgroup.centralizer ({z} : Set G) ⊓ Y))
    (hiso : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, GaloisField p f))) :
    IsSectionMember p f Y (perfectResidualOf L) z ∧
      ∀ x ∈ L, ∃ q ∈ perfectResidualOf L, ∃ o ∈ oddCoreOf L, x = q * o := by
  classical
  obtain ⟨e⟩ := hiso
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  have hSLperf : Group.IsPerfect SL(2, GaloisField p f) :=
    sl2_isPerfect (by rw [hcard]; exact h4)
  have := hSLperf
  have hQperf : Group.IsPerfect (↥L ⧸ classicalInvolutionOddCore ↥L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hq : commutator (↥L ⧸ classicalInvolutionOddCore ↥L) = ⊤ := Group.isPerfect_def.mp hQperf
  set Pr : Subgroup ↥L := perfectResidual ↥L with hPr
  have hPc : Pr.Characteristic := perfectResidual_characteristic (G := ↥L)
  have hPn : Pr.Normal := inferInstance
  have hPperf : ⁅Pr, Pr⁆ = Pr :=
    Subgroup.isPerfect_iff.mp (finite_perfectResidual_isPerfect (G := ↥L))
  have hPperf' : Group.IsPerfect ↥Pr := finite_perfectResidual_isPerfect (G := ↥L)
  obtain ⟨P₀, hP₀n, hP₀perf, hP₀sup⟩ := exists_perfect_normal_sup_oddCore_eq_top hq
  have hP₀Pr : P₀ ≤ Pr := by
    have hP₀perf' : Group.IsPerfect ↥(P₀.map L.subtype) := by
      have := Subgroup.isPerfect_iff.mpr hP₀perf
      exact Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hP₀perf])
    have h1 := le_perfectResidualOf_of_perfect (H := L) (Subgroup.map_subtype_le P₀) hP₀perf'
    exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp h1
  have hPsup : Pr ⊔ classicalInvolutionOddCore ↥L = ⊤ :=
    top_le_iff.mp (hP₀sup ▸ sup_le_sup_right hP₀Pr _)
  have : Pr.Normal := hPn
  have hzz : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hzP : (⟨z, hzL⟩ : ↥L) ∈ Pr := mem_of_mul_self_eq_one_of_sup_oddCore_eq_top Pr hPsup hzz
  obtain ⟨q⟩ := nonempty_oddCoreQuotientEquiv_of_sup_eq_top Pr hPsup
  have hKL : Pr.map L.subtype ≤ L := Subgroup.map_subtype_le Pr
  have eP : ↥Pr ≃* ↥(Pr.map L.subtype) := Pr.equivMapOfInjective L.subtype L.subtype_injective
  refine ⟨?_, ?_⟩
  · refine
      { le := hKL.trans hLY
        orderOf_eq_two := hz
        mem := ⟨⟨z, hzL⟩, hzP, rfl⟩
        perfect := Group.IsPerfect.ofSurjective (f := eP.toMonoidHom) eP.surjective
        subnormal := by
          have h3 : (Pr.map L.subtype).subgroupOf L = Pr :=
            Subgroup.comap_map_eq_self_of_injective L.subtype_injective Pr
          have h2 : ((Pr.map L.subtype).subgroupOf L).Normal := by
            rw [h3]
            exact hPn
          exact isSubnormal_trans (isSubnormal_of_normal_subgroupOf hKL h2) hsub
        nonempty_equiv := by
          have e1 : ↥Pr ⧸ classicalInvolutionOddCore ↥Pr ≃* SL(2, GaloisField p f) := q.trans e
          have hO : (classicalInvolutionOddCore ↥Pr).map eP.toMonoidHom =
              classicalInvolutionOddCore ↥(Pr.map L.subtype) :=
            CFSG.ComponentClassification.OddCore.equiv_invariant eP
          exact ⟨((QuotientGroup.congr _ _ eP hO).symm).trans e1⟩ }
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥L) ∈ (↑(Pr ⊔ classicalInvolutionOddCore ↥L) : Set ↥L) := by
      rw [hPsup]
      exact Subgroup.mem_top _
    rw [Subgroup.mul_normal Pr (classicalInvolutionOddCore ↥L)] at hmem
    obtain ⟨q', hq', o, ho, hqo⟩ := hmem
    exact ⟨(q' : G), ⟨q', hq', rfl⟩, (o : G), ⟨o, ho, rfl⟩, (congrArg Subtype.val hqo).symm⟩

end Layer

end CFSG.ClassicalInvolution.Q3.Q3AM
