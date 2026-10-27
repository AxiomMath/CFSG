module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S6Pkg
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def Ut (X : Subgroup S.O) : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2) {v | ∃ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = v}

theorem cl_mem_Ut (X : Subgroup S.O) : S.cl (g * S.z * g⁻¹) ∈ Ut S g X :=
  Submodule.subset_span ⟨1, one_mem X, rfl⟩

theorem apply_mem_Ut {X : Subgroup S.O} {x : S.O} (hx : x ∈ X) {u : S.Qt}
    (hu : u ∈ Ut S g X) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Ut S g X := by
  have hle : (Ut S g X).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap ≤ Ut S g X := by
    rw [Ut, Submodule.map_span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨x * y, mul_mem hx hy, rfl⟩
  exact hle ⟨u, hu, rfl⟩

theorem cl_mem_of_invariant (H : Hyp4 S g) {X : Subgroup S.O} (hLX : S.Lbar g ≤ X)
    {W : Submodule (ZMod 2) S.Qt} (hW : ∀ x ∈ X, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hW0 : W ≠ ⊥) : S.cl (g * S.z * g⁻¹) ∈ W := by
  obtain ⟨w, hw, hw0, hfix⟩ := exists_fixed_ne_zero (isPGroup_Lbar S H.conj_mem)
    (S.O.subtype.comp (S.Lbar g).subtype) (fun x u hu => hW _ (hLX x.2) u hu) hW0
  have hwF : w ∈ fixSub S (S.Lbar g) := (mem_fixSub S).mpr fun l hl => hfix ⟨l, hl⟩
  rw [H.fixSub_eq] at hwF
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwF
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exact absurd (zero_smul _ _) hw0
  · rwa [one_smul] at hw

theorem Ut_le_of_invariant (H : Hyp4 S g) {X : Subgroup S.O} (hLX : S.Lbar g ≤ X)
    {W : Submodule (ZMod 2) S.Qt} (hW : ∀ x ∈ X, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hW0 : W ≠ ⊥) : Ut S g X ≤ W := by
  rw [Ut, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hW x hx _ (cl_mem_of_invariant H hLX hW hW0)

theorem fix_Ut_of_normal (H : Hyp4 S g) {X : Subgroup S.O} (hLX : S.Lbar g ≤ X)
    {P : Subgroup S.O} (hPX : P ≤ X) (hPn : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) {p : S.O} (hp : p ∈ P) {u : S.Qt} (hu : u ∈ Ut S g X) :
    (p : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  have hinv : ∀ x ∈ X, ∀ w ∈ Ut S g X ⊓ fixSub S P,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Ut S g X ⊓ fixSub S P := by
    intro x hx w hw
    obtain ⟨hwU, hwF⟩ := Submodule.mem_inf.mp hw
    refine Submodule.mem_inf.mpr ⟨apply_mem_Ut hx hwU, (mem_fixSub S).mpr fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x⁻¹⁻¹ ∈ P := hPn _ (inv_mem hx) q hq
    rw [inv_inv] at hq'
    have h1 := (mem_fixSub S).mp hwF _ hq'
    have e : ((x⁻¹ * q * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
        ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((q : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := rfl
    rw [e] at h1
    have h2 := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2
  have hne : Ut S g X ⊓ fixSub S P ≠ ⊥ := by
    have hU0 : Ut S g X ≠ ⊥ := fun h0 => cl_conj_z_ne_zero S H.conj_mem H.conj_ne
      ((Submodule.mem_bot _).mp (h0 ▸ cl_mem_Ut X))
    obtain ⟨w, hw, hw0, hfix⟩ := exists_fixed_ne_zero hP2 (S.O.subtype.comp P.subtype)
      (fun x u hu => apply_mem_Ut (hPX x.2) hu) hU0
    intro h0
    apply hw0
    have hmem : w ∈ Ut S g X ⊓ fixSub S P :=
      Submodule.mem_inf.mpr ⟨hw, (mem_fixSub S).mpr fun q hq => hfix ⟨q, hq⟩⟩
    rwa [h0, Submodule.mem_bot] at hmem
  have hle := Ut_le_of_invariant H hLX hinv hne
  exact (mem_fixSub S).mp (Submodule.mem_inf.mp (hle hu)).2 p hp

theorem cl_mem_commSpace_of_mem_Lbar (H : Hyp4 S g) (C : Cons311 S g) {κ : S.O}
    (hκL : κ ∈ S.Lbar g) (hκ1 : κ ≠ 1) :
    S.cl (g * S.z * g⁻¹) ∈ commSpace (κ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  by_contra hna
  have hfix : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g), (κ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
    intro p hp
    rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' H.conj_mem hp hκL) with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd (h0 ▸ sub_mem_commSpace _ p) hna
  have hK : zpowers κ ≤ S.Lbar g := (zpowers_le).mpr hκL
  have h1 := card_mul_two_pow_finrank_fix H C hK
  have hle : S.clSub (S.QG ⊓ S.Qa g) ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (zpowers κ) := by
    intro p hp
    refine Submodule.mem_inf.mpr ⟨hp, (mem_fixSub S).mpr fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    have hκp : (κ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := hfix p hp
    have hpow : ∀ j : ℤ, ((κ ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
      intro j
      induction j using Int.induction_on with
      | zero => rfl
      | succ j ih =>
        rw [zpow_add_one, Subgroup.coe_mul, LinearEquiv.mul_apply, hκp, ih]
      | pred j ih =>
        rw [zpow_sub_one, Subgroup.coe_mul, LinearEquiv.mul_apply]
        have hκi : ((κ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
          conv_lhs => rw [← hκp]
          exact inv_apply_apply_O κ p
        rw [hκi, ih]
    exact hpow i
  have h2 := Submodule.finrank_mono hle
  have h3 := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  have h4 := Submodule.finrank_mono
    (inf_le_left : S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (zpowers κ) ≤ S.clSub (S.QG ⊓ S.Qa g))
  have h5 : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (zpowers κ)) = S.width := by
    omega
  rw [h5] at h1
  have h6 : Nat.card (zpowers κ) = 1 := by
    have hpos : 0 < 2 ^ S.width := pow_pos (by norm_num) _
    nlinarith
  apply hκ1
  rw [Nat.card_zpowers, orderOf_eq_one_iff] at h6
  exact h6

theorem polar_eq_zero_of_mem_Ut (H : Hyp4 S g) (C : Cons311 S g) {X : Subgroup S.O}
    (hLX : S.Lbar g ≤ X) {P : Subgroup S.O} (hPX : P ≤ X)
    (hPn : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hP2 : IsPGroup 2 P) (hLP : S.Lbar g ⊓ P ≠ ⊥)
    {u v : S.Qt} (hu : u ∈ Ut S g X) (hv : v ∈ Ut S g X) : polar S.q u v = 0 := by
  obtain ⟨⟨κ, hκ⟩, hκ1'⟩ := ne_bot_iff_exists_ne_one.mp hLP
  obtain ⟨hκL, hκP⟩ := mem_inf.mp hκ
  have hκ1 : κ ≠ 1 := fun h => hκ1' (Subtype.ext h)
  have haC := cl_mem_commSpace_of_mem_Lbar H C hκL hκ1
  have hperp : ∀ w ∈ Ut S g X, polar S.q (S.cl (g * S.z * g⁻¹)) w = 0 := by
    intro w hw
    obtain ⟨y, hy⟩ := mem_commSpace.mp haC
    have hκw := fix_Ut_of_normal H hLX hPX hPn hP2 hκP hw
    rw [← hy, polar_sub_left, ← hκw,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup κ.2, hκw, sub_self]
  set R := Ut S g X ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin (Ut S g X) with hR
  have hRinv : ∀ x ∈ X, ∀ w ∈ R, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ R := by
    intro x hx w hw
    obtain ⟨hwU, hwO⟩ := Submodule.mem_inf.mp hw
    refine Submodule.mem_inf.mpr ⟨apply_mem_Ut hx hwU, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hwO ⊢
    intro y hy
    have h1 := hwO _ (apply_mem_Ut (inv_mem hx) hy)
    change S.q.polarBilin (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) w = 0 at h1
    change S.q.polarBilin y ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = 0
    rw [polarBilin_apply_apply] at h1 ⊢
    rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2, apply_inv_apply_O] at h1
    exact h1
  have hR0 : R ≠ ⊥ := by
    intro h0
    have hmem : S.cl (g * S.z * g⁻¹) ∈ R := by
      refine Submodule.mem_inf.mpr ⟨cl_mem_Ut X, ?_⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      change S.q.polarBilin y (S.cl (g * S.z * g⁻¹)) = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact hperp y hy
    rw [h0, Submodule.mem_bot] at hmem
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne hmem
  have hle := Ut_le_of_invariant H hLX hRinv hR0
  have hvR := Submodule.mem_inf.mp (hle hv)
  have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvR.2) u hu
  change S.q.polarBilin u v = 0 at this
  rwa [polarBilin_apply_apply] at this

theorem apply_sub_mem_Ut_inf_clSub (H : Hyp4 S g) (C : Cons311 S g) {X : Subgroup S.O}
    (hLX : S.Lbar g ≤ X) (hiso : ∀ u ∈ Ut S g X, ∀ v ∈ Ut S g X, polar S.q u v = 0) {l : S.O}
    (hl : l ∈ S.Lbar g) {u : S.Qt} (hu : u ∈ Ut S g X) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g) := by
  refine Submodule.mem_inf.mpr ⟨sub_mem (apply_mem_Ut (hLX hl) hu) hu, ?_⟩
  obtain ⟨w', hw'Q, rfl⟩ := S.exists_cl u
  have hpol : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl w') = 0 := hiso _ (cl_mem_Ut X) _ hu
  have hc := (S.polar_cl_eq_zero_iff H.conj_mem hw'Q).mp hpol
  exact C.comm_le w' ⟨hw'Q, mem_centralizer_singleton_iff.mpr hc.symm⟩ l hl

theorem card_inf_mul_two_pow_le (H : Hyp4 S g) (C : Cons311 S g) {X : Subgroup S.O}
    (hLX : S.Lbar g ≤ X) {P : Subgroup S.O} (hPX : P ≤ X)
    (hPn : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hP2 : IsPGroup 2 P) :
    Nat.card (S.Lbar g ⊓ P : Subgroup S.O) *
      2 ^ finrank (ZMod 2) ↥(Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g)) ≤ 2 ^ S.width := by
  have h1 := card_mul_two_pow_finrank_fix H C (inf_le_left : S.Lbar g ⊓ P ≤ S.Lbar g)
  have hle : Ut S g X ⊓ S.clSub (S.QG ⊓ S.Qa g) ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ P) := by
    intro w hw
    obtain ⟨hwU, hwP⟩ := Submodule.mem_inf.mp hw
    exact Submodule.mem_inf.mpr ⟨hwP, (mem_fixSub S).mpr fun y hy =>
      fix_Ut_of_normal H hLX hPX hPn hP2 (mem_inf.mp hy).2 hwU⟩
  have h2 := Submodule.finrank_mono hle
  rw [← h1]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h2)

end CFSG.LargeExtraspecial.S9
