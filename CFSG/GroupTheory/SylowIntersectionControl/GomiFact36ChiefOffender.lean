module

import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private theorem card_fixV_inf_le_autSec_subgroupOf [Finite W] {A : Subgroup (MulAut W)}
    {I Z : Subgroup W} :
    Nat.card ↥(fixV A ⊓ I) ≤
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(Z.subgroupOf I) := by
  set U : Subgroup ↥I := Z.subgroupOf I with hU
  set K : Subgroup ↥I := (fixV A).subgroupOf I with hK
  have himage : K.map (QuotientGroup.mk' U) ≤ fixV (autSec A I Z) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvA : (v : W) ∈ fixV A := hv
    rw [show autSec A I Z = autQuot (autSub A I) U from rfl]
    change (QuotientGroup.mk v : ↥I ⧸ U) ∈ fixV (autQuot (autSub A I) U)
    rw [mk_mem_fixV_autQuot]
    intro g hg _
    obtain ⟨g₀, hg₀A, rfl⟩ := mem_autSub.mp hg
    have hgv : (g₀ : MulAut W) (v : W) = v := (mem_fixV.mp hvA) (g₀ : MulAut W) hg₀A
    rw [Subgroup.mem_subgroupOf]
    change ((resHom I g₀) v : W) * (v : W)⁻¹ ∈ Z
    rw [show (((resHom I g₀) v : ↥I) : W) = (g₀ : MulAut W) (v : W) from rfl, hgv,
      mul_inv_cancel]
    exact Z.one_mem
  have hker : K ⊓ (QuotientGroup.mk' U).ker ≤ U := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact hx.2
  have hcardK : Nat.card ↥K = Nat.card ↥(fixV A ⊓ I) := by
    have hK' : ((fixV A) ⊓ I).subgroupOf I = K := by
      rw [hK]
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
    rw [← hK']
    exact CFSG.natCard_subgroupOf_eq (fixV A ⊓ I) I inf_le_right
  have hmap := B1More.card_map_mul_card_inf_ker K (QuotientGroup.mk' U)
  calc
    Nat.card ↥(fixV A ⊓ I) = Nat.card ↥K := hcardK.symm
    _ = Nat.card ↥(K.map (QuotientGroup.mk' U)) *
          Nat.card ↥(K ⊓ (QuotientGroup.mk' U).ker) := hmap.symm
    _ ≤ Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥U :=
      Nat.mul_le_mul (Subgroup.card_le_of_le himage) (Subgroup.card_le_of_le hker)
    _ = Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(Z.subgroupOf I) := by rw [hU]

private theorem card_le_autSec_mul_fixV [Finite W] {A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hcost : Nat.card I * Nat.card ↥(A ⊓ centSec I ⊥) ≤
      Nat.card A * Nat.card ↥(fixV A ⊓ I))
    (hker : A ⊓ centSec I Z ≤ centSec I ⊥) :
    Nat.card I ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV A ⊓ I) := by
  have hAK := card_autSec_mul (A := A) (W := I) (U := Z) hAI hAZ
  have hKC : A ⊓ centSec I Z ≤ A ⊓ centSec I ⊥ := le_inf inf_le_left hker
  have h1 : Nat.card I * Nat.card ↥(A ⊓ centSec I Z) ≤
      (Nat.card ↥(autSec A I Z) * Nat.card ↥(A ⊓ centSec I Z)) *
        Nat.card ↥(fixV A ⊓ I) := by
    calc
      Nat.card I * Nat.card ↥(A ⊓ centSec I Z)
          ≤ Nat.card I * Nat.card ↥(A ⊓ centSec I ⊥) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hKC)
      _ ≤ Nat.card A * Nat.card ↥(fixV A ⊓ I) := hcost
      _ = (Nat.card ↥(autSec A I Z) * Nat.card ↥(A ⊓ centSec I Z)) *
            Nat.card ↥(fixV A ⊓ I) := by rw [hAK]
  have h2 : Nat.card I * Nat.card ↥(A ⊓ centSec I Z) ≤
      (Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV A ⊓ I)) *
        Nat.card ↥(A ⊓ centSec I Z) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1
  exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos

private theorem card_sec_mul_fixV_le [Finite W] {A : Subgroup (MulAut W)} {I Z : Subgroup W} :
    Nat.card (Sec I Z) * Nat.card ↥(fixV A ⊓ I) ≤
      Nat.card I * Nat.card ↥(fixV (autSec A I Z)) := by
  have hsec : Nat.card (Sec I Z) * Nat.card ↥(Z.subgroupOf I) = Nat.card I := by
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf I)).symm
  have hfix := card_fixV_inf_le_autSec_subgroupOf (A := A) (I := I) (Z := Z)
  calc
    Nat.card (Sec I Z) * Nat.card ↥(fixV A ⊓ I)
        ≤ Nat.card (Sec I Z) *
            (Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(Z.subgroupOf I)) :=
      Nat.mul_le_mul_left _ hfix
    _ = (Nat.card (Sec I Z) * Nat.card ↥(Z.subgroupOf I)) *
          Nat.card ↥(fixV (autSec A I Z)) := by ring
    _ = Nat.card I * Nat.card ↥(fixV (autSec A I Z)) := by rw [hsec]

private theorem arith_card_sec_le {s i ra rf f : ℕ}
    (h1 : s * f ≤ i * rf) (h2 : i ≤ ra * f) (hf : 0 < f) : s ≤ ra * rf := by
  have h3 : s * f ≤ (ra * rf) * f := by
    calc
      s * f ≤ i * rf := h1
      _ ≤ (ra * f) * rf := Nat.mul_le_mul_right rf h2
      _ = (ra * rf) * f := by ring
  exact Nat.le_of_mul_le_mul_right h3 hf

private theorem arith_card_sec_mul_card_sec {s s' i z f f' g ra' rf rf' : ℕ}
    (h1 : s * f ≤ i * rf) (h2 : i * g ≤ z * f)
    (h3 : s' * z ≤ ra' * f') (h4 : f' ≤ rf' * g)
    (hf : 0 < f) (hz : 0 < z) :
    s * s' ≤ ra' * rf * rf' := by
  have h5 : (s * s') * (z * f) ≤ (ra' * rf * rf') * (z * f) := by
    calc
      (s * s') * (z * f) = (s * f) * (s' * z) := by ring
      _ ≤ (i * rf) * (ra' * f') := Nat.mul_le_mul h1 h3
      _ = (i * rf * ra') * f' := by ring
      _ ≤ (i * rf * ra') * (rf' * g) := Nat.mul_le_mul_left _ h4
      _ = (i * g) * (rf * ra' * rf') := by ring
      _ ≤ (z * f) * (rf * ra' * rf') := Nat.mul_le_mul_right _ h2
      _ = (ra' * rf * rf') * (z * f) := by ring
  exact Nat.le_of_mul_le_mul_right h5 (Nat.mul_pos hz hf)

private theorem centSec_subgroupOf_le_center {L : Subgroup (MulAut W)}
    (hL : CFSG.IsQuasisimple ↥L) {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hnc : ¬ XMod.commOf ↥L I ≤ Z) :
    (centSec I Z).subgroupOf L ≤ Subgroup.center ↥L := by
  have hLconj : ∀ l ∈ L, ∀ g ∈ centSec I Z, l * g * l⁻¹ ∈ centSec I Z := by
    intro l hl g hg
    exact CFSG.Quasithin.StabLat.conj_mem_centSec (hLI hl) (hLZ hl) hg
  have hLnorm : L ≤ Subgroup.normalizer (centSec I Z : Set (MulAut W)) :=
    Subgroup.le_normalizer_iff.mpr hLconj
  have hN : ((centSec I Z).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  have hNne : (centSec I Z).subgroupOf L ≠ ⊤ := by
    intro htop
    apply hnc
    have hLle : L ≤ centSec I Z := Subgroup.subgroupOf_eq_top.mp htop
    rw [XMod.commOf_le_iff]
    intro l w hw
    have h := (hLle l.2).2 w hw
    simpa [Subgroup.smul_def, MulAut.smul_def] using h
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hN with h | h
  · exact absurd h hNne
  · exact h

theorem mem_centralizer_of_mem_centSec {L : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    {I Z : Subgroup W} (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hnc : ¬ XMod.commOf ↥L I ≤ Z) {a : MulAut W}
    (haL : a ∈ Subgroup.normalizer (L : Set (MulAut W))) (ha : a ∈ centSec I Z) :
    a ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
  have hLconj : ∀ l ∈ L, ∀ g ∈ centSec I Z, l * g * l⁻¹ ∈ centSec I Z := by
    intro l hl g hg
    exact CFSG.Quasithin.StabLat.conj_mem_centSec (hLI hl) (hLZ hl) hg
  have hNc := centSec_subgroupOf_le_center hL hLI hLZ hnc
  let φ : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨a, haL⟩
  have hcentral : ∀ x : ↥L, x⁻¹ * φ x ∈ Subgroup.center ↥L := by
    intro x
    have hxinv : (((x⁻¹ : ↥L) : MulAut W)) ∈ L := (x⁻¹).2
    have hconj : (((x⁻¹ : ↥L) : MulAut W) * a * (((x⁻¹ : ↥L) : MulAut W))⁻¹) ∈
        centSec I Z := hLconj _ hxinv _ ha
    have hcent : (((x⁻¹ * φ x : ↥L) : MulAut W)) ∈ centSec I Z := by
      have h1 : ((x⁻¹ * φ x : ↥L) : MulAut W) =
          (((x⁻¹ : ↥L) : MulAut W) * a * (((x⁻¹ : ↥L) : MulAut W))⁻¹) * a⁻¹ := by
        change (((x⁻¹ : ↥L) : MulAut W) * (a * (x : ↥L) * a⁻¹)) =
          (((x⁻¹ : ↥L) : MulAut W) * a * (((x⁻¹ : ↥L) : MulAut W))⁻¹) * a⁻¹
        simp only [Subgroup.coe_inv]
        group
      rw [h1]
      exact (centSec I Z).mul_mem hconj ((centSec I Z).inv_mem ha)
    have hmem : (x⁻¹ * φ x) ∈ (centSec I Z).subgroupOf L :=
      (Subgroup.mem_subgroupOf (H := centSec I Z) (K := L)).mpr hcent
    exact hNc hmem
  have hperf : Group.IsPerfect ↥L := hL.1
  have hφhom :=
    @CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      ↥L _ hperf (φ.toMonoidHom) hcentral
  have hφ : ∀ x : ↥L, φ x = x := by
    intro x
    exact DFunLike.congr_fun hφhom x
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hx := congrArg (fun z : ↥L => (z : MulAut W)) (hφ ⟨l, hl⟩)
  have hconj : a * l * a⁻¹ = l := by simpa [φ] using hx
  calc
    l * a = (a * l * a⁻¹) * a := by rw [hconj]
    _ = a * l := by group

theorem inf_centSec_eq_inf_centralizer {L A : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hnc : ¬ XMod.commOf ↥L I ≤ Z)
    (hI : I ≤ fixV (A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) :
    A ⊓ centSec I Z = A ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
  refine le_antisymm ?_ ?_
  · rintro a ⟨haA, haC⟩
    exact ⟨haA, mem_centralizer_of_mem_centSec hL hLI hLZ hnc (hAL haA) haC⟩
  · rintro a ⟨haA, haC⟩
    have hfix : ∀ w ∈ I, a w = w := by
      intro w hw
      exact (mem_fixV.mp (hI hw)) a ⟨haA, haC⟩
    refine ⟨haA, (mem_centSec (W := I) (U := Z)).mpr ⟨?_, ?_⟩⟩
    · intro u
      constructor
      · intro hu
        have h1 : a (a u) = a u := hfix (a u) hu
        have h2 : a u = u := a.injective h1
        exact h2 ▸ hu
      · intro hu
        rw [hfix u hu]
        exact hu
    · intro w hw
      rw [hfix w hw]
      simp

theorem card_sec_le_card_autSec_mul [Finite W] {A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hcost : Nat.card I * Nat.card ↥(A ⊓ centSec I ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ I))
    (hker : A ⊓ centSec I Z ≤ centSec I ⊥) :
    Nat.card (Sec I Z) ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) := by
  have h1 := card_sec_mul_fixV_le (A := A) (I := I) (Z := Z)
  have h2 := card_le_autSec_mul_fixV (A := A) (I := I) (Z := Z) hAI hAZ hcost hker
  exact arith_card_sec_le h1 h2 Nat.card_pos

theorem card_sec_mul_card_sec_le [Finite W] {A : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W}
    (hZI : Z ≤ I) (hIZ' : I ≤ Z') (hZ'I' : Z' ≤ I')
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z')
    (hcost : Nat.card I' * Nat.card ↥(A ⊓ centSec I' ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ I'))
    (hker : A ⊓ centSec I' Z' ≤ centSec I' ⊥) :
    Nat.card (Sec I Z) * Nat.card (Sec I' Z') ≤
      Nat.card ↥(autSec A I' Z') * Nat.card ↥(fixV (autSec A I Z)) *
        Nat.card ↥(fixV (autSec A I' Z')) := by
  have _ := hZI
  have _ := hAZ
  have _ := hAI
  have h1 : Nat.card (Sec I Z) * Nat.card ↥(fixV A ⊓ I) ≤
      Nat.card I * Nat.card ↥(fixV (autSec A I Z)) :=
    card_sec_mul_fixV_le
  have h2 : Nat.card I * Nat.card ↥(fixV A ⊓ Z') ≤
      Nat.card Z' * Nat.card ↥(fixV A ⊓ I) := by
    have hIF : I ⊓ fixV A ≤ Z' := inf_le_left.trans hIZ'
    have hcorr := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (H := W) I
      (fixV A ⊓ Z') (fun x _ y _ => mul_comm x y)).1
    have hsupcard : Nat.card ↥(I ⊔ (fixV A ⊓ Z')) ≤ Nat.card Z' :=
      Subgroup.card_le_of_le (sup_le hIZ' inf_le_right)
    have hinf : I ⊓ (fixV A ⊓ Z') = fixV A ⊓ I := by
      rw [← inf_assoc, inf_eq_left.mpr hIF, inf_comm]
    calc
      Nat.card I * Nat.card ↥(fixV A ⊓ Z')
          = Nat.card ↥(I ⊔ (fixV A ⊓ Z')) * Nat.card ↥(I ⊓ (fixV A ⊓ Z')) := hcorr.symm
      _ = Nat.card ↥(I ⊔ (fixV A ⊓ Z')) * Nat.card ↥(fixV A ⊓ I) := by rw [hinf]
      _ ≤ Nat.card Z' * Nat.card ↥(fixV A ⊓ I) := Nat.mul_le_mul_right _ hsupcard
  have h3 : Nat.card (Sec I' Z') * Nat.card Z' ≤
      Nat.card ↥(autSec A I' Z') * Nat.card ↥(fixV A ⊓ I') := by
    have hsec : Nat.card (Sec I' Z') * Nat.card Z' = Nat.card I' := by
      have hZ : Nat.card ↥(Z'.subgroupOf I') = Nat.card Z' :=
        CFSG.natCard_subgroupOf_eq Z' I' hZ'I'
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z'.subgroupOf I')
      rw [hZ] at h
      exact h.symm
    rw [hsec]
    exact card_le_autSec_mul_fixV hAI' hAZ' hcost hker
  have h4 : Nat.card ↥(fixV A ⊓ I') ≤
      Nat.card ↥(fixV (autSec A I' Z')) * Nat.card ↥(fixV A ⊓ Z') := by
    have h := card_inf_fixV_le_autSec (A := A) (W := I') (U := Z') hZ'I' hAI'
    have hF : Nat.card ↥(I' ⊓ fixV A) = Nat.card ↥(fixV A ⊓ I') := by rw [inf_comm]
    have hG : Nat.card ↥(Z' ⊓ fixV A) = Nat.card ↥(fixV A ⊓ Z') := by rw [inf_comm]
    rw [hF, hG] at h
    exact h
  exact arith_card_sec_mul_card_sec h1 h2 h3 h4 Nat.card_pos Nat.card_pos

theorem le_centSec_bot_of_le_fixV {K : Subgroup (MulAut W)} {U : Subgroup W}
    (h : U ≤ fixV K) : K ≤ centSec U ⊥ := by
  have hfix : ∀ k ∈ K, ∀ u ∈ U, k u = u := fun k hk u hu => mem_fixV.1 (h hu) k hk
  have hstab : K ≤ stabSub U :=
    B1.le_stabSub_of_invariant fun k hk u hu => by rw [hfix k hk u hu]; exact hu
  intro k hk
  exact mem_centSec.2 ⟨hstab hk, fun u hu => by
    rw [hfix k hk u hu, mul_inv_cancel]
    exact Subgroup.one_mem ⊥⟩

theorem autSec_offender_facts [Finite W] {L A : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (hL : CFSG.IsQuasisimple ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hcost : ∀ U : Subgroup W,
      Nat.card U * Nat.card ↥(A ⊓ centSec U ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U))
    (hV₀fix : V₀ ≤ fixV (A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hIV : I ≤ V₀) (hnc : ¬ XMod.commOf ↥L I ≤ Z) :
    ¬ A ≤ centSec I Z ∧ IsElemAbelian2 (autSec A I Z) ∧ IsQuadratic (autSec A I Z) ∧
      Nat.card (Sec I Z) ≤
        Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) := by
  have heq := inf_centSec_eq_inf_centralizer hL hAL hLI hLZ hnc (hIV.trans hV₀fix)
  have hker : A ⊓ centSec I Z ≤ centSec I ⊥ := by
    rw [heq]
    exact le_centSec_bot_of_le_fixV (hIV.trans hV₀fix)
  refine ⟨?_, B69.isElemAbelian2_autSec hAe hAI hAZ, B69.isQuadratic_autSec hAI hAZ hAq,
    card_sec_le_card_autSec_mul hAI hAZ (hcost I) hker⟩
  intro hA
  have h1 : A ≤ A ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [← heq, inf_eq_left.2 hA]
  exact hAnc (h1.trans inf_le_right)

end CFSG.GroupTheory
