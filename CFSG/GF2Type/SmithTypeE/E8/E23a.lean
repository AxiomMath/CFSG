module

public import CFSG.GF2Type.SmithTypeE.E8.E23aStd
public import CFSG.GF2Type.SmithTypeE.E8.IdentLift
public import CFSG.LargeExtraspecial.S14SMHLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt perpLevi perpRoots pinnedElt_mem_perpLevi)


variable {G : Type} [Group G] [Finite G]

@[expose] def E23aConcl (S : Setting G) (t u : G) : Prop :=
  IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) ∧
  Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ 33 ∧
  S.QG ⊓ cent2 t u ≤ closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} ∧
  (∀ c ∈ cent2 t u, c ∈ S.M → (∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) → c ∈ S.QG) ∧
  (∀ P : Subgroup G, P ≤ cent2 t u ⊓ S.M →
    (∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) → IsPGroup 2 P → P ≤ S.QG)

theorem commute_conj_iff_E8 (g a b : G) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := by
  constructor
  · intro h
    simp only [Commute, SemiconjBy] at h ⊢
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
      _ = b * a := by group
  · intro h
    simp only [Commute, SemiconjBy] at h ⊢
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem conj_mem_cent2_iff_E8 (g : G) {t u x : G} :
    g * x * g⁻¹ ∈ cent2 (g * t * g⁻¹) (g * u * g⁻¹) ↔ x ∈ cent2 t u := by
  rw [mem_cent2, mem_cent2, commute_conj_iff_E8, commute_conj_iff_E8]

theorem conj_mem_QG_iff_E8 (S : Setting G) {g : G} (hg : g ∈ S.M) {x : G} :
    g * x * g⁻¹ ∈ S.QG ↔ x ∈ S.QG := by
  refine ⟨fun h => ?_, S.conj_mem_QG hg⟩
  have := S.conj_mem_QG (S.M.inv_mem hg) h
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem conj_mem_M_iff_E8 (S : Setting G) {g : G} (hg : g ∈ S.M) {x : G} :
    g * x * g⁻¹ ∈ S.M ↔ x ∈ S.M := by
  refine ⟨fun h => ?_, fun h => S.M.mul_mem (S.M.mul_mem hg h) (S.M.inv_mem hg)⟩
  have := S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hg) h) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem E23aConcl.of_conj (S : Setting G) {t u g : G} (hg : g ∈ S.M)
    (h : E23aConcl S (g * t * g⁻¹) (g * u * g⁻¹)) : E23aConcl S t u := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  set f : G ≃* G := MulAut.conj g with hf
  have hfapp : ∀ x, f x = g * x * g⁻¹ := fun x => by simp [hf, MulAut.conj_apply]
  have hfsymm : ∀ x, f.symm x = g⁻¹ * x * g := fun x => by
    rw [MulEquiv.symm_apply_eq, hfapp]; group
  have hE : (S.QG ⊓ cent2 t u).map f.toMonoidHom = S.QG ⊓ cent2 (g * t * g⁻¹) (g * u * g⁻¹) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyQ, hyH⟩ := mem_inf.mp hy
      exact mem_inf.mpr ⟨by rw [MulEquiv.coe_toMonoidHom, hfapp]; exact S.conj_mem_QG hg hyQ,
        by rw [MulEquiv.coe_toMonoidHom, hfapp]; exact (conj_mem_cent2_iff_E8 g).mpr hyH⟩
    · intro hx
      obtain ⟨hxQ, hxH⟩ := mem_inf.mp hx
      refine ⟨f.symm x, ?_, by simp⟩
      have e : g * f.symm x * g⁻¹ = x := by rw [hfsymm]; group
      have hxQ' : g * f.symm x * g⁻¹ ∈ S.QG := by rw [e]; exact hxQ
      have hxH' : g * f.symm x * g⁻¹ ∈ cent2 (g * t * g⁻¹) (g * u * g⁻¹) := by rw [e]; exact hxH
      exact mem_inf.mpr ⟨(conj_mem_QG_iff_E8 S hg).mp hxQ', (conj_mem_cent2_iff_E8 g).mp hxH'⟩
  let e : ↥(S.QG ⊓ cent2 t u) ≃* ↥(S.QG ⊓ cent2 (g * t * g⁻¹) (g * u * g⁻¹)) :=
    (Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hE)
  refine ⟨CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e.symm h1,
    (Nat.card_congr e.toEquiv).trans h2, fun q hq => ?_, fun c hcH hcM hcq => ?_,
    fun P hPH hPn hP2 => ?_⟩
  ·
    have hq' : g * q * g⁻¹ ∈ S.QG ⊓ cent2 (g * t * g⁻¹) (g * u * g⁻¹) := by
      rw [← hE]; exact ⟨q, hq, by rw [MulEquiv.coe_toMonoidHom, hfapp]⟩
    have hc := h3 hq'
    have hmap : closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 (g * t * g⁻¹) (g * u * g⁻¹)}
        ≤ (closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u}).map f.toMonoidHom := by
      rw [closure_le]
      rintro c ⟨hcz, hcQ, hcH'⟩
      refine ⟨f.symm c, subset_closure ⟨?_, ?_, ?_⟩, by simp⟩
      · rw [hfsymm]; exact hcz.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
      · rw [hfsymm]
        exact (conj_mem_QG_iff_E8 S hg).mp (by rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group])
      · rw [hfsymm]
        exact (conj_mem_cent2_iff_E8 g).mp (by rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group])
    obtain ⟨q', hq', hq'e⟩ := hmap hc
    rw [MulEquiv.coe_toMonoidHom, hfapp] at hq'e
    have : q' = q := by
      have := congrArg (fun x => g⁻¹ * x * g) hq'e
      rwa [show g⁻¹ * (g * q' * g⁻¹) * g = q' by group,
        show g⁻¹ * (g * q * g⁻¹) * g = q by group] at this
    rwa [this] at hq'
  ·
    refine (conj_mem_QG_iff_E8 S hg).mp (h4 _ ((conj_mem_cent2_iff_E8 g).mpr hcH)
      ((conj_mem_M_iff_E8 S hg).mpr hcM) fun q hq => ?_)
    rw [← hE] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    rw [MulEquiv.coe_toMonoidHom, hfapp]
    have := hcq q₀ hq₀
    calc g * c * g⁻¹ * (g * q₀ * g⁻¹) = g * (c * q₀) * g⁻¹ := by group
      _ = g * (q₀ * c) * g⁻¹ := by rw [this]
      _ = g * q₀ * g⁻¹ * (g * c * g⁻¹) := by group
  ·
    set P' := P.map f.toMonoidHom with hP'
    have hmem : ∀ {x : G}, x ∈ P' ↔ g⁻¹ * x * g ∈ P := fun {x} => by
      rw [hP', Subgroup.mem_map]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hfapp]
        rwa [show g⁻¹ * (g * p * g⁻¹) * g = p by group]
      · intro hx
        exact ⟨_, hx, by rw [MulEquiv.coe_toMonoidHom, hfapp]; group⟩
    have hle := h5 P' (fun x hx => by
        have hp := hPH (hmem.mp hx)
        obtain ⟨hpH, hpM⟩ := mem_inf.mp hp
        have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        refine mem_inf.mpr ⟨?_, ?_⟩
        · rw [← e]; exact (conj_mem_cent2_iff_E8 g).mpr hpH
        · rw [← e]; exact (conj_mem_M_iff_E8 S hg).mpr hpM)
      (fun c hc x hx => by
        apply hmem.mpr
        obtain ⟨hcH, hcM⟩ := mem_inf.mp hc
        have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
        have hc' : g⁻¹ * c * g ∈ cent2 t u ⊓ S.M := by
          refine mem_inf.mpr ⟨(conj_mem_cent2_iff_E8 g).mp (by rwa [e]),
            (conj_mem_M_iff_E8 S hg).mp (by rwa [e])⟩
        have := hPn _ hc' _ (hmem.mp hx)
        rwa [show g⁻¹ * c * g * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g by
          group] at this)
      (hP2.map _)
    intro p hp
    apply (conj_mem_QG_iff_E8 S hg).mp
    exact hle (hmem.mpr (by rwa [show g⁻¹ * (g * p * g⁻¹) * g = p by group]))

noncomputable abbrev mbarPt (S : Setting G) {x : G} (hx : x ∈ S.M) : S.Mbar :=
  ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩

theorem mbarPt_mul (S : Setting G) {x y : G} (hx : x ∈ S.M) (hy : y ∈ S.M) :
    mbarPt S (S.M.mul_mem hx hy) = mbarPt S hx * mbarPt S hy :=
  (SMH.toMbarM S).map_mul ⟨x, hx⟩ ⟨y, hy⟩

theorem mbarPt_eq_iff (S : Setting G) {x y : G} (hx : x ∈ S.M) (hy : y ∈ S.M) :
    mbarPt S hx = mbarPt S hy ↔ x⁻¹ * y ∈ S.QG := by
  constructor
  · intro h
    have hρ : S.ρ ⟨x, hx⟩ = S.ρ ⟨y, hy⟩ := congrArg Subtype.val h
    have h1 : S.ρ ((⟨x, hx⟩ : S.M)⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, hρ, inv_mul_cancel]
    exact (S.ρ_eq_one_iff _).mp h1
  · intro h
    have h1 := (S.ρ_eq_one_iff ((⟨x, hx⟩ : S.M)⁻¹ * ⟨y, hy⟩)).mpr h
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact Subtype.ext h1

theorem mbarPt_eq_one_iff (S : Setting G) {x : G} (hx : x ∈ S.M) :
    mbarPt S hx = 1 ↔ x ∈ S.QG := by
  constructor
  · intro h
    exact (S.ρ_eq_one_iff ⟨x, hx⟩).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((S.ρ_eq_one_iff ⟨x, hx⟩).mpr h)

theorem mbarPt_conj (S : Setting G) {c x : G} (hc : c ∈ S.M) (hx : x ∈ S.M) :
    mbarPt S (S.M.mul_mem (S.M.mul_mem hc hx) (S.M.inv_mem hc)) =
      mbarPt S hc * mbarPt S hx * (mbarPt S hc)⁻¹ := by
  apply Subtype.ext
  show S.ρ ⟨c * x * c⁻¹, _⟩ = S.ρ ⟨c, hc⟩ * S.ρ ⟨x, hx⟩ * (S.ρ ⟨c, hc⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_mbarPt_eq (S : Setting G) (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2)))
    (g : ↥(adjointGroup .E7 (ZMod 2))) : ∃ (m : G) (hm : m ∈ S.M), ψ (mbarPt S hm) = g := by
  obtain ⟨⟨m, hmM⟩, hm'⟩ := (ψ.symm g : S.Mbar).2
  refine ⟨m, hmM, ?_⟩
  have : mbarPt S hmM = ψ.symm g := Subtype.ext hm'
  rw [this, MulEquiv.apply_symm_apply]

section Psi

variable {S : Setting G} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}

theorem psi_comm_of_commute {c d : G} (hc : c ∈ S.M) (hd : d ∈ S.M) (h : Commute c d) :
    ψ (mbarPt S hc) * ψ (mbarPt S hd) = ψ (mbarPt S hd) * ψ (mbarPt S hc) := by
  rw [← map_mul, ← map_mul, ← mbarPt_mul, ← mbarPt_mul]
  exact congrArg ψ (Subtype.ext (congrArg S.ρ (Subtype.ext h.eq)))

theorem mul_inv_mul_mem_QG_of_psi_comm {c d : G} (hc : c ∈ S.M) (hd : d ∈ S.M)
    (h : ψ (mbarPt S hc) * ψ (mbarPt S hd) = ψ (mbarPt S hd) * ψ (mbarPt S hc)) :
    (c * d)⁻¹ * (d * c) ∈ S.QG := by
  rw [← map_mul, ← map_mul, ← mbarPt_mul, ← mbarPt_mul] at h
  exact (mbarPt_eq_iff S _ _).mp (ψ.injective h)

theorem orderOf_psi_mul {t u : G} (htM : t ∈ S.M) (huM : u ∈ S.M) (htu : orderOf (t * u) = 3) :
    orderOf (ψ (mbarPt S htM) * ψ (mbarPt S huM)) = 3 := by
  have hθM : t * u ∈ S.M := S.M.mul_mem htM huM
  have e : ψ (mbarPt S htM) * ψ (mbarPt S huM) = ψ (SMH.toMbarM S ⟨t * u, hθM⟩) := by
    rw [← map_mul]
    exact congrArg ψ (mbarPt_mul S htM huM).symm
  rw [e, MulEquiv.orderOf_eq]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have h1 : (⟨t * u, hθM⟩ : S.M) ^ 3 = 1 := by
      refine Subtype.ext ?_
      show (t * u) ^ 3 = 1
      rw [← htu]
      exact pow_orderOf_eq_one _
    rw [h1, map_one]
  · intro h
    exact SMJ.mul_not_mem_QG S htu ((mbarPt_eq_one_iff S hθM).mp h)

end Psi

section Lift

variable {S : Setting G} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}

theorem exists_lift (h34a : SmithE8E34a) (h34b : SmithE8E34b) (hLoc : SmithE8LocalInput)
    [IsSimpleGroup G] (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    (h5 : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r →
      ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧ ψ (mbarPt S hx) = r)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3) {rt ru : ↥(adjointGroup .E7 (ZMod 2))}
    (hψt : ψ (mbarPt S htM) = rt) (hψu : ψ (mbarPt S huM) = ru)
    {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r) (hrt : r * rt = rt * r)
    (hru : r * ru = ru * r) :
    ∃ (y : G) (hyM : y ∈ S.M), IsConj S.z y ∧ y ∉ S.QG ∧ Commute y t ∧ Commute y u ∧
      ψ (mbarPt S hyM) = r := by
  have hti : t⁻¹ = t := SME.inv_eq_of_isConj S ht
  have hui : u⁻¹ = u := SME.inv_eq_of_isConj S hu
  obtain ⟨x, hxM, hx, hxQ, hψx⟩ := h5 r hr
  have hxi : x⁻¹ = x := SME.inv_eq_of_isConj S hx
  have hxt := mul_inv_mul_mem_QG_of_psi_comm hxM htM
    (by rw [hψx, hψt]; exact hrt)
  have hxu := mul_inv_mul_mem_QG_of_psi_comm hxM huM
    (by rw [hψx, hψu]; exact hru)
  have hty : t * x * t⁻¹ * x⁻¹ ∈ S.QG := by
    have e1 : (x * t)⁻¹ * (t * x) = t * x * t * x := by rw [mul_inv_rev, hti, hxi]; group
    rw [hti, hxi]
    rwa [e1] at hxt
  have huy : u * x * u⁻¹ * x⁻¹ ∈ S.QG := by
    have e1 : (x * u)⁻¹ * (u * x) = u * x * u * x := by rw [mul_inv_rev, hui, hxi]; group
    rw [hui, hxi]
    rwa [e1] at hxu
  obtain ⟨y, hyD, hxy, hyt, hyu⟩ := exists_lift_commute h34a h34b hLoc S hw hU ht hu htM huM
    htQ htu hx hxM hxQ hty huy
  have hyM : y ∈ S.M := by
    have := S.M.mul_mem hxM (S.QG_le_M hxy)
    rwa [mul_inv_cancel_left] at this
  have hyQ : y ∉ S.QG := fun hyQ => hxQ (by
    have := S.QG.mul_mem hyQ (S.QG.inv_mem hxy)
    rwa [show y * (x⁻¹ * y)⁻¹ = x by group] at this)
  have hρy : mbarPt S hxM = mbarPt S hyM := (mbarPt_eq_iff S hxM hyM).mpr hxy
  exact ⟨y, hyM, hyD, hyQ, hyt, hyu, by rw [← hρy]; exact hψx⟩

end Lift

section Std

variable {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
  {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}

theorem mem_QG_of_centralizes_std (h34a : SmithE8E34a) [IsSimpleGroup G] (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) (hE : SmithE8Equiv S φ ψ) {t u : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (huQ : u ∉ S.QG) (hψt : ψ (mbarPt S htM) = xT) (hψu : ψ (mbarPt S huM) = xTn)
    {c : G} (hcH : c ∈ cent2 t u) (hcM : c ∈ S.M)
    (hcq : ∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) : c ∈ S.QG := by
  obtain ⟨hct, hcu⟩ := mem_cent2.mp hcH
  have hAt : Acts S φ t xT := by
    have := acts_of_equiv hE htM
    rwa [hψt] at this
  have hAu : Acts S φ u xTn := by
    have := acts_of_equiv hE huM
    rwa [hψu] at this
  have hAc := acts_of_equiv hE hcM
  have hg : ψ (mbarPt S hcM) ∈ perpLevi .E7 (ZMod 2) := by
    refine (commute_xT_xTn_iff _).mp ⟨?_, ?_⟩
    · have := psi_comm_of_commute (ψ := ψ) hcM htM hct
      rw [hψt] at this
      exact this
    · have := psi_comm_of_commute (ψ := ψ) hcM huM hcu
      rw [hψu] at this
      exact this
  have hfix : ∀ v ∈ V0, e7Rep56 (ZMod 2) (ψ (mbarPt S hcM)) v = v := by
    intro v hv
    obtain ⟨q, hqQ, hqt, hqu, rfl⟩ := exists_cent2_of_mem_V0 htM huM hAt hAu h34a hw hU ht hu
      htQ huQ hv
    have hcq' := hcq q (mem_inf.mpr ⟨hqQ, mem_cent2.mpr ⟨hqt, hqu⟩⟩)
    have e : c * q * c⁻¹ = q := by rw [hcq', mul_inv_cancel_right]
    have := hAc q hqQ
    rw [e] at this
    exact this.symm
  have h1 := eq_one_of_fix_V0 hg hfix
  exact mem_QG_of_acts hcM hAc fun v => by rw [h1, rep_one_apply]

theorem le_QG_of_normal_std (h34a : SmithE8E34a) (h34b : SmithE8E34b) (hLoc : SmithE8LocalInput)
    [IsSimpleGroup G] (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    (h5 : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r →
      ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧ ψ (mbarPt S hx) = r)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3) (hψt : ψ (mbarPt S htM) = xT)
    (hψu : ψ (mbarPt S huM) = xTn) {P : Subgroup G} (hPH : P ≤ cent2 t u ⊓ S.M)
    (hPn : ∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P) :
    P ≤ S.QG := by
  obtain ⟨ΦM, hΦM⟩ : ∃ ΦM : ↥S.M →* ↥(adjointGroup .E7 (ZMod 2)),
      ∀ (p : G) (hp : p ∈ S.M), ΦM ⟨p, hp⟩ = ψ (mbarPt S hp) :=
    ⟨ψ.toMonoidHom.comp (SMH.toMbarM S), fun p hp => rfl⟩
  set N : Subgroup ↥(adjointGroup .E7 (ZMod 2)) := (P.comap S.M.subtype).map ΦM with hN
  have hNp : IsPGroup 2 N :=
    (hP2.comap_of_injective S.M.subtype Subtype.val_injective).map ΦM
  have hmemN : ∀ {p : G} (hpM : p ∈ S.M), p ∈ P → ψ (mbarPt S hpM) ∈ N := fun {p} hpM hp =>
    ⟨⟨p, hpM⟩, hp, hΦM p hpM⟩
  have hND : N ≤ perpLevi .E7 (ZMod 2) := by
    rintro _ ⟨⟨p, hpM⟩, hpP, rfl⟩
    obtain ⟨hpH, -⟩ := mem_inf.mp (hPH hpP)
    obtain ⟨hpt, hpu⟩ := mem_cent2.mp hpH
    rw [hΦM p hpM]
    refine (commute_xT_xTn_iff _).mp ⟨?_, ?_⟩
    · have := psi_comm_of_commute (ψ := ψ) hpM htM hpt
      rw [hψt] at this
      exact this
    · have := psi_comm_of_commute (ψ := ψ) hpM huM hpu
      rw [hψu] at this
      exact this
  have hnorm : ∀ γ ∈ perpRoots .E7, ∀ n ∈ N,
      pinnedElt .E7 γ (1 : ZMod 2) * n * (pinnedElt .E7 γ (1 : ZMod 2))⁻¹ ∈ N := by
    intro γ hγ n hn
    obtain ⟨⟨p, hpM⟩, hpP, rfl⟩ := hn
    have hrD : pinnedElt .E7 γ (1 : ZMod 2) ∈ perpLevi .E7 (ZMod 2) := pinnedElt_mem_perpLevi hγ 1
    obtain ⟨hrt, hru⟩ := (commute_xT_xTn_iff _).mpr hrD
    obtain ⟨y, hyM, -, -, hyt, hyu, hψy⟩ := exists_lift h34a h34b hLoc hw hU h5 ht hu htM huM htQ
      htu hψt hψu (isRootInvol_pinnedElt hγ.1) hrt hru
    have hyH : y ∈ cent2 t u ⊓ S.M := mem_inf.mpr ⟨mem_cent2.mpr ⟨hyt, hyu⟩, hyM⟩
    have hypy : y * p * y⁻¹ ∈ P := hPn y hyH p hpP
    have hypyM : y * p * y⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hyM hpM) (S.M.inv_mem hyM)
    have := hmemN hypyM hypy
    rw [mbarPt_conj S hyM hpM, map_mul, map_mul, map_inv, hψy] at this
    rw [hΦM p hpM]
    exact this
  have hbot := eq_bot_of_normalized_pgroup N hND hnorm hNp
  intro p hp
  have hpM : p ∈ S.M := (mem_inf.mp (hPH hp)).2
  have h1 : ψ (mbarPt S hpM) ∈ N := hmemN hpM hp
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : mbarPt S hpM = 1 := by
    have := congrArg ψ.symm h1
    rwa [MulEquiv.symm_apply_apply, map_one] at this
  exact (mbarPt_eq_one_iff S hpM).mp h2

theorem e23aConcl_std (h25 : SmithE8E25) (h34a : SmithE8E34a) (h34b : SmithE8E34b)
    (hLoc : SmithE8LocalInput) [IsSimpleGroup G] (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) (hE : SmithE8Equiv S φ ψ)
    (h2b : ∀ w ∈ weightVec, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = w)
    (h5 : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r →
      ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧ ψ (mbarPt S hx) = r)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ (mbarPt S htM) = xT) (hψu : ψ (mbarPt S huM) = xTn) :
    E23aConcl S t u := by
  have hAt : Acts S φ t xT := by
    have := acts_of_equiv hE htM
    rwa [hψt] at this
  have hAu : Acts S φ u xTn := by
    have := acts_of_equiv hE huM
    rwa [hψu] at this
  have hcard := card_cent2_std htM huM hAt hAu h34a hw hU ht hu htQ huQ
  exact ⟨isExtraspecialPGroup_cent2_E8 h25 h34a S hw hU ht hu htM huM htQ huQ htu hcard.ge,
    hcard, cent2_le_closure_std htM huM hAt hAu h34a hw hU ht hu htQ huQ h2b,
    fun c hcH hcM hcq => mem_QG_of_centralizes_std h34a hw hU hE ht hu htM huM htQ huQ hψt hψu
      hcH hcM hcq,
    fun P hPH hPn hP2 => le_QG_of_normal_std h34a h34b hLoc hw hU h5 ht hu htM huM htQ htu hψt hψu
      hPH hPn hP2⟩

end Std

theorem smithE8E23a_of (h25 : SmithE8E25) (h34a : SmithE8E34a) (h34b : SmithE8E34b)
    (hLoc : SmithE8LocalInput) (hC : SmithE8Compat) : SmithE8E23a := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ htu
  obtain ⟨φ, ψ, ⟨hE, -, h2b, -⟩, h4, h5⟩ := hC G S hw hU
  have hrt := h4 t htM ht htQ
  have hru := h4 u huM hu huQ
  have hord := orderOf_psi_mul (ψ := ψ) htM huM htu
  obtain ⟨g, hg1, hg2⟩ := exists_conj_opposite hrt hru hord
  obtain ⟨m, hmM, hm⟩ := exists_mbarPt_eq S ψ g
  have htM' : m * t * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)
  have huM' : m * u * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hmM huM) (S.M.inv_mem hmM)
  have hψt' : ψ (mbarPt S htM') = xT := by
    rw [mbarPt_conj S hmM htM, map_mul, map_mul, map_inv, hm]
    exact hg1
  have hψu' : ψ (mbarPt S huM') = xTn := by
    rw [mbarPt_conj S hmM huM, map_mul, map_mul, map_inv, hm]
    exact hg2
  have hconjQ : ∀ {x : G}, x ∉ S.QG → m * x * m⁻¹ ∉ S.QG := fun hx h =>
    hx ((conj_mem_QG_iff_E8 S hmM).mp h)
  have h3m : orderOf (m * t * m⁻¹ * (m * u * m⁻¹)) = 3 := by
    rw [show m * t * m⁻¹ * (m * u * m⁻¹) = MulAut.conj m (t * u) by
      rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact htu
  exact E23aConcl.of_conj S hmM (e23aConcl_std h25 h34a h34b hLoc hw hU hE h2b h5
    (ht.trans (isConj_iff.mpr ⟨m, rfl⟩)) (hu.trans (isConj_iff.mpr ⟨m, rfl⟩)) htM' huM'
    (hconjQ htQ) (hconjQ huQ) h3m hψt' hψu')

end CFSG.GF2Type.SmithTypeE.E8
