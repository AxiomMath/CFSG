module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteLit
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit.Aut5L2

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y] (e : Y ≃* PSL2 F)

@[expose] noncomputable def linL2 : Subgroup (MulAut Y) :=
  (SemidirectProduct.rightHom.comp (autEquiv e).toMonoidHom).ker

theorem mem_linL2 (α : MulAut Y) : α ∈ linL2 e ↔ (autEquiv e α).right = 1 := Iff.rfl

omit [Finite F] in
theorem eq_inl_of_right_eq_one {x : PGammaL2 F} (hx : x.right = 1) :
    x = SemidirectProduct.inl x.left := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hx, map_one, mul_one]

theorem mem_innAut5_iff (α : MulAut Y) :
    α ∈ innAut5 Y ↔ autEquiv e α ∈ pGammaL2PSLRange F := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [autEquiv_conj]
    exact ⟨e y, rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, (autEquiv e).injective ?_⟩
    rw [autEquiv_conj, MulEquiv.apply_symm_apply]
    exact hz

theorem inn_le_linL2 : innAut5 Y ≤ linL2 e := by
  rintro _ ⟨y, rfl⟩
  rw [mem_linL2, autEquiv_conj, incl_apply]
  rfl

theorem linL2_normal : (linL2 e).Normal := MonoidHom.normal_ker _

theorem sq_mem_of_linL2 (α : MulAut Y) (hα : α ∈ linL2 e) : α * α ∈ innAut5 Y := by
  rw [mem_innAut5_iff e, map_mul, eq_inl_of_right_eq_one ((mem_linL2 e α).mp hα), ← map_mul]
  obtain ⟨y, hy⟩ := sq_mem_psl2Range (autEquiv e α).left
  exact ⟨y, by rw [← sq, ← hy]; rfl⟩

theorem commutator_mem_l2 [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hL : Blueprint.LieModel Y .PSL 2 p f) (α β : MulAut Y) :
    α * β * α⁻¹ * β⁻¹ ∈ innAut5 Y := by
  obtain ⟨s, hs⟩ := cfFooteL2OutAbelian Y p f hp hp2 hf hL α β
  exact ⟨s, hs.symm⟩

include e in
theorem conj_involution_l2 (hodd : IsOddPrimePower (Nat.card F)) (x y : Y) (hx : orderOf x = 2)
    (hy : orderOf y = 2) : ∃ g : Y, g⁻¹ * x * g = y := by
  have hinv : ∀ z : Y, orderOf z = 2 → BenderSuzuki.PFAppendixIII.IsInvolution (e z) :=
    fun z hz => by
      refine ⟨fun h => ?_, ?_⟩
      · have : z = 1 := e.injective (by rw [h, map_one])
        rw [this, orderOf_one] at hz
        exact absurd hz (by norm_num)
      · have h1 := pow_orderOf_eq_one z
        rw [hz] at h1
        rw [← map_pow, h1, map_one]
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (e x) (e y) (hinv x hx)
    (hinv y hy)
  refine ⟨e.symm g⁻¹, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
  exact hg

theorem centralizer_sylow_lin_l2
    [Finite Y] (hodd : IsOddPrimePower (Nat.card F)) (R : Sylow 2 Y)
    (hna : ∃ a ∈ (R : Subgroup Y), ∃ b ∈ (R : Subgroup Y), a * b ≠ b * a) (α : MulAut Y)
    (hα : α ∈ linL2 e) (h2k : ∃ k : ℕ, α ^ 2 ^ k = 1) (hfix : ∀ r ∈ (R : Subgroup Y), α r = r) :
    ∃ c ∈ (R : Subgroup Y), (∀ r ∈ (R : Subgroup Y), c * r = r * c) ∧ α = MulAut.conj c := by
  set D := sylowMap e R with hD
  have hDcoe : (D : Subgroup (PSL2 F)) = (R : Subgroup Y).map e.toMonoidHom := coe_sylowMap e R
  have hD8 : 8 ≤ Nat.card D := by
    obtain ⟨m, hm, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv e hodd R
    have hcard : Nat.card D = 2 ^ (m + 1) := by
      rw [show Nat.card D = Nat.card (R : Subgroup Y) from card_sylowMap e R,
        Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
    rw [hcard]
    by_contra hlt
    have hm1 : m = 1 := by
      by_contra hne
      have : 2 ^ 3 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hm1
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    apply hab
    have hD2 : ∀ x y : DihedralGroup (2 ^ 1), x * y = y * x := by decide
    have h1 := hD2 (ρ ⟨a, ha⟩) (ρ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (ρ.injective h1)
  obtain ⟨k, hk⟩ := h2k
  have hxD : ∀ d ∈ (D : Subgroup (PSL2 F)),
      autEquiv e α * incl F d = incl F d * autEquiv e α := by
    intro d hd
    rw [hDcoe] at hd
    obtain ⟨r, hr, rfl⟩ := hd
    exact (apply_eq_iff_commute e α r).mp (hfix r hr)
  obtain ⟨d, ⟨hdD, hdC⟩, hd⟩ := mem_center_of_right_eq_one hodd D hD8 (autEquiv e α)
    ((mem_linL2 e α).mp hα) (k := k) (by rw [← map_pow, hk, map_one]) hxD
  have hdR : e.symm d ∈ (R : Subgroup Y) := by
    rw [hDcoe] at hdD
    obtain ⟨r, hr, rfl⟩ := hdD
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨e.symm d, hdR, fun r hr => e.injective ?_, (autEquiv e).injective ?_⟩
  · have hr' : e r ∈ (D : Subgroup (PSL2 F)) := by rw [hDcoe]; exact ⟨r, hr, rfl⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (mem_centralizer_iff.mp hdC _ hr').symm
  · rw [autEquiv_conj, MulEquiv.apply_symm_apply, hd]

theorem not_commute_l2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (α β : MulAut Y) (hα : α ∈ linL2 e) (hαI : α ∉ innAut5 Y) (hβ : β ∉ linL2 e)
    (hβ2 : β * β = 1) : α * β ≠ β * α := by
  intro hcomm
  apply hαI
  rw [mem_innAut5_iff e, eq_inl_of_right_eq_one ((mem_linL2 e α).mp hα)]
  refine mem_pslRange_of_commute_fieldInv hp hp2 hF (autEquiv e β)
    (by rw [← map_mul, hβ2, map_one]) hβ _ ?_
  rw [← eq_inl_of_right_eq_one ((mem_linL2 e α).mp hα), ← map_mul, ← map_mul, hcomm]

end CFSG.ComponentClassification.FooteLit.Aut5L2
