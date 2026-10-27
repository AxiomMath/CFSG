module

public import CFSG.ClassicalInvolution.Q3.TA3SOLDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQ8
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.Walter.JRFacts
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentSplitting
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.LiteratureLocal
open scoped MatrixGroups

theorem datum_isSolvable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}
    (hD : TightDatum R S t) : Group.IsSolvable R := by
  have hO : Group.IsSolvable (CFSG.Open.classicalInvolutionOddCore R) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card R)
  have hq : Group.IsSolvable (R ⧸ CFSG.Open.classicalInvolutionOddCore R) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hD.twoGroup.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (CFSG.Open.classicalInvolutionOddCore R)

theorem noDatumRee : NoDatumRee := by
  intro X _ _ f hree ⟨R, S, t, hD⟩
  obtain ⟨-, -, -, -, -, h3⟩ := hree.1
  obtain ⟨a, hea, -⟩ := hree.2
  subst hea
  have ha : 1 ≤ a := by omega
  obtain ⟨-, -, hcen, -⟩ := ward_kleidman_small_Ree_involution_centralizer_maximal a ha X hree
  obtain ⟨L, hLC, -, hsup, ⟨eL⟩, hZ⟩ := hcen t hD.order
  have hE4 : 4 ≤ Nat.card (GaloisField 3 (2 * a + 1)) := by
    rw [GaloisField.card 3 (2 * a + 1) (by omega)]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup PSL(2, GaloisField 3 (2 * a + 1)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ u v : ↥L, u * v ≠ v * u := CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2 hE4 eL
  set C := Subgroup.centralizer ({t} : Set X) with hCdef
  have hRC : R ≤ C := hD.cent
  have hCR : C ≤ Subgroup.normalizer (R : Set X) := hD.le_normalizer
  have hcomm : ∀ x ∈ Subgroup.zpowers t, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute t l from
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)).symm).zpow_left n).eq
  have hdec : ∀ c ∈ C, ∃ x ∈ Subgroup.zpowers t, ∃ l ∈ L, c = x * l := by
    intro c hc
    rw [← hsup] at hc
    obtain ⟨x, hx, l, hl, rfl⟩ :=
      (CFSG.QuasithinUnique.ComponentSplitting.mem_sup_iff_of_commute hcomm).mp hc
    exact ⟨x, hx, l, hl, rfl⟩
  have hCL : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
    intro c hc l hl
    obtain ⟨x, hx, l', hl', rfl⟩ := hdec c hc
    have e : x * l' * l * (x * l')⁻¹ = l' * l * l'⁻¹ := by
      have h1 := hcomm x hx (l' * l * l'⁻¹) (L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl'))
      calc x * l' * l * (x * l')⁻¹ = x * (l' * l * l'⁻¹) * x⁻¹ := by group
        _ = l' * l * l'⁻¹ := by rw [h1, mul_inv_cancel_right]
    rw [e]
    exact L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')
  have hconjR : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := fun c hc r hr =>
    (Subgroup.mem_normalizer_iff.mp (hCR hc) r).mp hr
  have hRL : ∀ x ∈ R, x ∈ L → x = 1 := by
    have hn : ((R ⊓ L).subgroupOf L).Normal := ⟨fun k hk l => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact ⟨hconjR l (hLC l.2) k hk.1, L.mul_mem (L.mul_mem l.2 hk.2) (L.inv_mem l.2)⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ L).subgroupOf L) with h | h
    · intro x hxR hxL
      have : (⟨x, hxL⟩ : L) ∈ (R ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr ⟨hxR, hxL⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hLR : L ≤ R := fun l hl => by
        have : (⟨l, hl⟩ : L) ∈ (R ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      have := datum_isSolvable hD
      have hL : Group.IsSolvable ↥L :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLR)
          (Subgroup.inclusion_injective hLR)
      obtain ⟨u, v, huv⟩ := hLnab
      exact huv ((IsSimpleGroup.comm_iff_isSolvable.mpr hL) u v)
  have hRLc : ∀ r ∈ R, ∀ l ∈ L, r * l = l * r := by
    intro r hr l hl
    have h1 : r * l * r⁻¹ * l⁻¹ ∈ L := L.mul_mem (hCL r (hRC hr) l hl) (L.inv_mem hl)
    have h2 : r * l * r⁻¹ * l⁻¹ ∈ R := by
      have := R.mul_mem hr (hconjR l (hLC hl) r⁻¹ (R.inv_mem hr))
      simpa [mul_assoc] using this
    have := hRL _ h2 h1
    calc r * l = r * l * r⁻¹ * l⁻¹ * (l * r) := by group
      _ = l * r := by rw [this, one_mul]
  have hRt : ∀ r ∈ R, r ∈ Subgroup.zpowers t := by
    intro r hr
    have hcen : (⟨r, hRC hr⟩ : C) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      obtain ⟨x, hx, l, hl, hcx⟩ := hdec c c.2
      have hxr : x * r = r * x := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ((show Commute t r from
          (Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)).symm).zpow_left n).eq
      show (c : X) * r = r * c
      rw [hcx, mul_assoc, ← hRLc r hr l hl, ← mul_assoc, hxr, mul_assoc]
    have : r ∈ (Subgroup.center C).map C.subtype := ⟨_, hcen, rfl⟩
    rwa [hZ] at this
  obtain ⟨φ₀, hi₀, hr₀, -⟩ := datum_exists_q8 hD
  have hinj : Function.Injective (φ₀.codRestrict (Subgroup.zpowers t) fun x => hRt _ (hr₀ x)) :=
    fun x y h => hi₀ (congrArg Subtype.val h)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_zpowers, hD.order, Nat.card_eq_fintype_card, QuaternionGroup.card] at hle
  omega

end CFSG.ClassicalInvolution.Q3.TA3
