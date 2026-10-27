module

public import CFSG.GF2Type.Smith1979.CaseI25A1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_conj)

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section PermDelta

@[expose] noncomputable def permDelta (S : Setting G) (g : G) (t : S.O) :
    NLbar S g →* Equiv.Perm (Delta S g t) where
  toFun n :=
    { toFun := fun x => ⟨(n : S.O) * x * (n : S.O)⁻¹, conj_mem_Delta n.2 x.2⟩
      invFun := fun x => ⟨(n : S.O)⁻¹ * x * (n : S.O)⁻¹⁻¹, conj_mem_Delta (inv_mem n.2) x.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun x => Subtype.ext (by group) }
  map_one' := Equiv.ext fun x => Subtype.ext (by
    change (1 : S.O) * x * (1 : S.O)⁻¹ = x
    group)
  map_mul' n m := Equiv.ext fun x => Subtype.ext (by
    change ((n : S.O) * (m : S.O)) * x * ((n : S.O) * (m : S.O))⁻¹ =
      (n : S.O) * ((m : S.O) * x * (m : S.O)⁻¹) * (n : S.O)⁻¹
    group)

noncomputable instance instFintypeDelta (S : Setting G) (g : G) (t : S.O) :
    Fintype (Delta S g t) := Fintype.ofFinite _

theorem permDelta_eq_one_iff {t : S.O} (hcl : Subgroup.closure (Delta S g t) = S.Lbar g)
    (ht : t ∈ S.Lbar g) (n : NLbar S g) :
    permDelta S g t n = 1 ↔ ∀ l ∈ S.Lbar g, (n : S.O) * l = l * (n : S.O) := by
  constructor
  · intro h l hl
    have hΔ : Delta S g t ⊆ (centralizer ({(n : S.O)} : Set S.O) : Set S.O) := by
      intro x hx
      have := congrArg (fun p : Equiv.Perm (Delta S g t) => ((p ⟨x, hx⟩ : Delta S g t) : S.O)) h
      change (n : S.O) * x * (n : S.O)⁻¹ = x at this
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc x * (n : S.O) = ((n : S.O) * x * (n : S.O)⁻¹) * (n : S.O) := by rw [this]
        _ = (n : S.O) * x := by group
    have hle : S.Lbar g ≤ centralizer ({(n : S.O)} : Set S.O) := by
      rw [← hcl]
      exact (closure_le _).mpr hΔ
    exact (mem_centralizer_singleton_iff.mp (hle hl)).symm
  · intro h
    refine Equiv.ext fun x => Subtype.ext ?_
    change (n : S.O) * x * (n : S.O)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact h x (delta_subset_Lbar ht x.2)

end PermDelta

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
  {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
  (hpol : Q.polarBilin = beta H C ht ht1 hVQ) (hX : RmodN S g t = omegaGroup Q hQ)
  (hE : LmodN S g t = pointRadical Q (aV ht))
  (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
include hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing

@[expose] noncomputable def RbarFix (S : Setting G) (g : G) (t : S.O) : Subgroup S.O :=
  Rbar S g t ⊓ NLbar S g

@[expose] noncomputable def thetaRbarFix (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    RbarFix S g t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  (resV haQ t).comp (Subgroup.inclusion (inf_le_left : RbarFix S g t ≤ Rbar S g t))

@[expose] noncomputable def psiRbarFix (S : Setting G) (g : G) (t : S.O) :
    RbarFix S g t →* Equiv.Perm (Delta S g t) :=
  (permDelta S g t).comp (Subgroup.inclusion (inf_le_right : RbarFix S g t ≤ NLbar S g))

theorem range_thetaRbarFix : (thetaRbarFix H.conj_mem t).range = omegaStab Q hQ (aV ht) := by
  ext w
  constructor
  · rintro ⟨r, rfl⟩
    refine mem_omegaStab.mpr ⟨?_, ?_⟩
    · rw [← hX, ← range_resV H.conj_mem t]
      exact ⟨_, rfl⟩
    · exact Subtype.ext (fix_of_mem_normalizer H r.2.2.2)
  · intro hw
    obtain ⟨hwΩ, hwa⟩ := mem_omegaStab.mp hw
    have hwR : w ∈ RmodN S g t := hX ▸ hwΩ
    obtain ⟨r, hr, hrw⟩ := hwR
    have hra : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
      have := hrw (aV ht)
      rw [hwa] at this
      exact this.symm
    have hrN : r ∈ normalizer (S.Lbar g : Set S.O) := by
      have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne
        (Rbar_le_Mbar hr) (by simpa using hra)
      simpa using this
    exact ⟨⟨r, hr, Rbar_le_Mbar hr, hrN⟩, LinearEquiv.ext fun v => Subtype.ext (hrw v).symm⟩

theorem ker_psiRbarFix_le (hcl : Subgroup.closure (Delta S g t) = S.Lbar g) :
    (psiRbarFix S g t).ker ≤ (pointRadical Q (aV ht)).comap (thetaRbarFix H.conj_mem t) := by
  intro r hr
  rw [MonoidHom.mem_ker] at hr
  rw [Subgroup.mem_comap]
  have hcomm : ∀ l ∈ S.Lbar g, (r : S.O) * l = l * (r : S.O) :=
    (permDelta_eq_one_iff hcl ht ⟨r, r.2.2⟩).mp hr
  have ha0 := aV_ne_zero H ht
  have ha := CaseIClosure.Q_aV_eq_zero H ht hsing
  have hθmem : thetaRbarFix H.conj_mem t r ∈ omegaStab Q hQ (aV ht) := by
    rw [← range_thetaRbarFix hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing]
    exact ⟨r, rfl⟩
  obtain ⟨hθΩ, hθa⟩ := mem_omegaStab.mp hθmem
  refine mem_pointRadical_of_commute hQ ha0 ha (omegaGroup_le Q hQ hθΩ) hθa ?_
  intro u hu
  rw [← hE, ← range_resL H.conj_mem ht] at hu
  obtain ⟨⟨l, hl⟩, rfl⟩ := hu
  rw [CaseIClosure.resL_eq_resV H ht hl]
  have hlR : l ∈ Rbar S g t := Lbar_le_Rbar ht hl
  have hrR : (r : S.O) ∈ Rbar S g t := r.2.1
  have e : (⟨r, hrR⟩ : Rbar S g t) * ⟨l, hlR⟩ * (⟨r, hrR⟩ : Rbar S g t)⁻¹ = ⟨l, hlR⟩ :=
    Subtype.ext (by
      change (r : S.O) * l * (r : S.O)⁻¹ = l
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm l hl)
  calc thetaRbarFix H.conj_mem t r * resV H.conj_mem t ⟨l, hlR⟩ * (thetaRbarFix H.conj_mem t r)⁻¹
      = resV H.conj_mem t (⟨r, hrR⟩ * ⟨l, hlR⟩ * (⟨r, hrR⟩ : Rbar S g t)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
        rfl
    _ = resV H.conj_mem t ⟨l, hlR⟩ := by rw [e]

open scoped Classical in
theorem alt_le_image_of_form (hΔ : (Delta S g t).ncard = 6) :
    alternatingGroup (Delta S g t) ≤ (permDelta S g t).range := by
  have hcl := closure_Delta_of_form hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  have h27 := ncard_singular_of_delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  have ha0 := aV_ne_zero H ht
  have ha := CaseIClosure.Q_aV_eq_zero H ht hsing
  set Y := (permDelta S g t).range with hY
  set x₀ : Delta S g t := ⟨t, mem_Delta_self S g t⟩ with hx₀
  have h60 : 60 ∣ Nat.card (psiRbarFix S g t).range := by
    have hdvd := Subgroup.index_dvd_of_le
      (ker_psiRbarFix_le hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hcl)
    rw [Subgroup.index_ker, Subgroup.index_comap,
      range_thetaRbarFix hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing] at hdvd
    have h := Subgroup.relIndex_mul_card (H := pointRadical Q (aV ht))
      (K := omegaStab Q hQ (aV ht))
    rw [inf_of_le_left (pointRadical_le_omegaStab hQ ha0 ha), card_pointRadical hQ ha0 ha, h6,
      card_omegaStab h6 hQ ha0 ha h27] at h
    have : (pointRadical Q (aV ht)).relIndex (omegaStab Q hQ (aV ht)) = 60 := by
      norm_num at h
      omega
    rwa [this] at hdvd
  have hΔcard : Nat.card (Delta S g t) = 6 := (Nat.card_coe_set_eq _).trans hΔ
  have horb : MulAction.orbit Y x₀ = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn, hxn⟩ := x.2
    exact ⟨⟨permDelta S g t ⟨n, hn⟩, ⟨_, rfl⟩⟩, Subtype.ext hxn.symm⟩
  have hkey : Nat.card (MulAction.orbit Y x₀) * Nat.card (MulAction.stabilizer Y x₀) =
      Nat.card Y := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Y x₀)
  have horbcard : Nat.card (MulAction.orbit Y x₀) = 6 := by
    rw [horb, Nat.card_univ]
    exact hΔcard
  set Ystab : Subgroup (Equiv.Perm (Delta S g t)) :=
    (MulAction.stabilizer Y x₀).map Y.subtype with hYstab
  have hcardYstab : Nat.card Ystab = Nat.card (MulAction.stabilizer Y x₀) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hψY : (psiRbarFix S g t).range ≤ Ystab := by
    rintro _ ⟨r, rfl⟩
    refine ⟨⟨(psiRbarFix S g t) r, ⟨_, rfl⟩⟩, MulAction.mem_stabilizer_iff.mpr ?_, rfl⟩
    refine Subtype.ext ?_
    change (r : S.O) * t * (r : S.O)⁻¹ = t
    rw [mul_inv_eq_iff_eq_mul]
    exact commute_of_mem_Rbar H.conj_mem r.2.1
  have h60' : 60 ∣ Nat.card Ystab := h60.trans (Subgroup.card_dvd_of_le hψY)
  have hYcard : Nat.card Y = 6 * Nat.card Ystab := by rw [← hkey, horbcard, hcardYstab]
  have hpermcard : Nat.card (Equiv.Perm (Delta S g t)) = 720 := by
    rw [Nat.card_perm, hΔcard]
    rfl
  have hidx : Y.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index Y
    rw [hpermcard, hYcard] at h1
    have h3 : 60 ≤ Nat.card Ystab := Nat.le_of_dvd Nat.card_pos h60'
    by_contra hcon
    have hcon' : 2 < Y.index := not_le.mp hcon
    nlinarith [Nat.mul_le_mul h3 hcon']
  exact Equiv.Perm.alternatingGroup_le_of_index_le_two hidx

end Context

section NoForm

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

open scoped Classical in
theorem alt_le_image (hΔ : (Delta S g t).ncard = 6) :
    alternatingGroup (Delta S g t) ≤ (permDelta S g t).range := by
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  exact alt_le_image_of_form hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ

open scoped Classical in
theorem range_permDelta_eq (hΔ : (Delta S g t).ncard = 6) :
    (permDelta S g t).range = alternatingGroup (Delta S g t) ∨ (permDelta S g t).range = ⊤ := by
  have halt := alt_le_image hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have hΔcard : Nat.card (Delta S g t) = 6 := (Nat.card_coe_set_eq _).trans hΔ
  have hdvd : (permDelta S g t).range.index ∣ (alternatingGroup (Delta S g t)).index :=
    Subgroup.index_dvd_of_le halt
  have hnt : Nontrivial (Delta S g t) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have h2 : (alternatingGroup (Delta S g t)).index = 2 := alternatingGroup.index_eq_two
  rw [h2] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · right
    exact Subgroup.index_eq_one.mp h
  · left
    exact (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h)

end NoForm

end Case25

end CFSG.GF2Type.Smith1979
