module

import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.SubgroupCardInf
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefOffender
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefSetup
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulBasic
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulCoprime
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulPlus
import CFSG.Quasithin.Background.B51SumOffenders
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
public import CFSG.Quasithin.Background.B1Restrict
import CFSG.Quasithin.Background.SmithB51LnSub

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private theorem le_stabSub_commSub_fac {V₀ : Subgroup W} {C X : Subgroup (MulAut W)}
    (hXV₀ : X ≤ stabSub V₀) (hXC : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C) :
    X ≤ stabSub (commSub V₀ C) := by
  refine B1.le_stabSub_of_invariant fun x hx w hw => ?_
  exact B1.commSub_smul_mem (Y := C) x (hXC x hx)
    (fun m hm => (mem_stabSub.mp (hXV₀ hx) m).2 hm) w hw

private theorem le_stabSub_inf_fixV_fac [Finite W] {V₀ : Subgroup W} {C X : Subgroup (MulAut W)}
    (hXV₀ : X ≤ stabSub V₀) (hXC : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C) :
    X ≤ stabSub (V₀ ⊓ fixV C) := by
  refine B1.le_stabSub_of_invariant fun x hx w hw => ⟨?_, ?_⟩
  · exact (mem_stabSub.mp (hXV₀ hx) w).2 hw.1
  · exact B1Red.fixV_inv_of_normalizes (B := X) (L := C) hXC x hx w hw.2

private theorem le_stabSub_commSub_inf_fac [Finite W] {V₀ : Subgroup W}
    {C A : Subgroup (MulAut W)} (hAV₀ : A ≤ stabSub V₀)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C) :
    A ≤ stabSub (commSub V₀ C) ∧ A ≤ stabSub (V₀ ⊓ fixV C) :=
  ⟨le_stabSub_commSub_fac hAV₀ hAC, le_stabSub_inf_fixV_fac hAV₀ hAC⟩

private theorem inf_centSec_sup_le_fac {C : Subgroup (MulAut W)} {V₀ Vp Vz : Subgroup W}
    (hsup : Vp ⊔ Vz = V₀) (hfix : Vz ≤ fixV C) :
    C ⊓ centSec Vp ⊥ ≤ C ⊓ centSec V₀ ⊥ := by
  rintro c ⟨hcC, hc⟩
  have hcVp : ∀ u ∈ Vp, c u = u := fun u hu => by
    have h := (mem_centSec.mp hc).2 u hu
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hcVz : ∀ v ∈ Vz, c v = v := fun v hv => mem_fixV.mp (hfix hv) c hcC
  have hcV₀ : ∀ v ∈ V₀, c v = v := by
    intro v hv
    rw [← hsup] at hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hcVp u hu, hcVz w hw]
  refine ⟨hcC, ?_⟩
  change c ∈ centSec V₀ ⊥
  rw [mem_centSec]
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => by rw [hcV₀ x hx]; exact hx⟩, fun w hw => ?_⟩
  · have h2 : c (c x) = c x := hcV₀ (c x) hx
    have h3 : c x = x := c.injective h2
    rwa [h3] at hx
  · rw [hcV₀ w hw, mul_inv_cancel]
    exact Subgroup.one_mem ⊥

private theorem le_centralizer_of_le_fixV_fac {L A : Subgroup (MulAut W)} {U : Subgroup W}
    (hL : CFSG.IsQuasisimple ↥L) (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLU : L ≤ stabSub U) (hnc : ¬ XMod.commOf ↥L U ≤ ⊥) (hU : U ≤ fixV A) :
    A ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  intro a ha
  exact mem_centralizer_of_mem_centSec hL hLU (B5.Ln.stabSub_bot_le L) hnc (hAL ha)
    (le_centSec_bot_of_le_fixV hU ha)

private theorem card_fixV_inf_le_autSec_fac [Finite W] {A : Subgroup (MulAut W)}
    {I Z I' : Subgroup W} (hI'I : I' ≤ I) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) :
    Nat.card ↥(fixV A ⊓ I') ≤
      Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(Z ⊓ I') := by
  let f : ↥(fixV A ⊓ I') →* Sec I Z :=
    (QuotientGroup.mk' (Z.subgroupOf I)).comp (Subgroup.inclusion (inf_le_right.trans hI'I))
  have hf_apply : ∀ x : ↥(fixV A ⊓ I'),
      f x = QuotientGroup.mk (Subgroup.inclusion (inf_le_right.trans hI'I) x) := fun _ => rfl
  have himage : f.range ≤ fixV (autSec A I Z) := by
    rintro _ ⟨x, rfl⟩
    intro φ hφ
    rw [← B5.range_secHom A hAI hAZ] at hφ
    obtain ⟨a, rfl⟩ := hφ
    rw [hf_apply, B5.secHom_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    exact mem_fixV.mp x.2.1 a a.2
  have hker : Nat.card ↥f.ker ≤ Nat.card ↥(Z ⊓ I') := by
    have hZ : ∀ x : ↥(fixV A ⊓ I'), x ∈ f.ker → (x : W) ∈ Z := by
      intro x hx
      have hmem : Subgroup.inclusion (inf_le_right.trans hI'I) x ∈ Z.subgroupOf I :=
        (QuotientGroup.eq_one_iff (N := Z.subgroupOf I) _).mp hx
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    refine Nat.card_le_card_of_injective
      (fun x : ↥f.ker => (⟨(x.1 : W), ?_⟩ : ↥(Z ⊓ I'))) ?_
    · exact ⟨hZ x.1 x.2, x.1.2.2⟩
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(Z ⊓ I') => (z : W)) hxy
  calc
    Nat.card ↥(fixV A ⊓ I') = Nat.card ↥f.ker * Nat.card ↥f.range :=
      (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ Nat.card ↥(Z ⊓ I') * Nat.card ↥(fixV (autSec A I Z)) :=
      Nat.mul_le_mul hker (Subgroup.card_le_of_le himage)
    _ = Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(Z ⊓ I') := mul_comm _ _

private theorem card_sec_mul_inf_eq_fac [Finite W] {I Z I' : Subgroup W}
    (hZI : Z ≤ I) (hsup : Z ⊔ I' = I) :
    Nat.card (Sec I Z) * Nat.card ↥(Z ⊓ I') = Nat.card I' := by
  have h1 : Nat.card (Sec I Z) * Nat.card Z = Nat.card I := card_sec_mul hZI
  have h2 : Nat.card I * Nat.card ↥(Z ⊓ I') = Nat.card Z * Nat.card I' := by
    rw [← hsup]
    exact (card_sup_mul_card_inf_of_commute Z I' (fun _ _ _ _ => mul_comm _ _)).1
  have h3 : (Nat.card (Sec I Z) * Nat.card ↥(Z ⊓ I')) * Nat.card Z =
      Nat.card I' * Nat.card Z := by
    calc
      (Nat.card (Sec I Z) * Nat.card ↥(Z ⊓ I')) * Nat.card Z
          = (Nat.card (Sec I Z) * Nat.card Z) * Nat.card ↥(Z ⊓ I') := by ring
      _ = Nat.card I * Nat.card ↥(Z ⊓ I') := by rw [h1]
      _ = Nat.card Z * Nat.card I' := h2
      _ = Nat.card I' * Nat.card Z := by ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3

private theorem card_sec_mul_fixV_le_fac [Finite W] {A : Subgroup (MulAut W)}
    {I Z I' : Subgroup W} (hZI : Z ≤ I) (hI'I : I' ≤ I) (hsup : Z ⊔ I' = I)
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) :
    Nat.card (Sec I Z) * Nat.card ↥(fixV A ⊓ I') ≤
      Nat.card I' * Nat.card ↥(fixV (autSec A I Z)) := by
  have h1 := card_fixV_inf_le_autSec_fac (A := A) hI'I hAI hAZ
  have h2 := card_sec_mul_inf_eq_fac (I := I) (Z := Z) (I' := I') hZI hsup
  calc
    Nat.card (Sec I Z) * Nat.card ↥(fixV A ⊓ I')
        ≤ Nat.card (Sec I Z) *
            (Nat.card ↥(fixV (autSec A I Z)) * Nat.card ↥(Z ⊓ I')) :=
      Nat.mul_le_mul_left _ h1
    _ = (Nat.card (Sec I Z) * Nat.card ↥(Z ⊓ I')) *
          Nat.card ↥(fixV (autSec A I Z)) := by ring
    _ = Nat.card I' * Nat.card ↥(fixV (autSec A I Z)) := by rw [h2]

private theorem card_mul_card_inf_le_fac [Finite W] {H K C : Subgroup W} (hH : H ≤ C) :
    Nat.card H * Nat.card ↥(K ⊓ C) ≤ Nat.card C * Nat.card ↥(K ⊓ H) := by
  have h := CFSG.card_mul_card_le_card_inf_mul_card_of_le (H := H) (K := K ⊓ C) (C := C)
    hH inf_le_right
  have hinf : H ⊓ (K ⊓ C) = K ⊓ H := by
    calc H ⊓ (K ⊓ C) = H ⊓ (C ⊓ K) := by rw [inf_comm K C]
      _ = (H ⊓ C) ⊓ K := (inf_assoc H C K).symm
      _ = H ⊓ K := by rw [inf_of_le_left hH]
      _ = K ⊓ H := inf_comm H K
  rw [hinf] at h
  calc
    Nat.card H * Nat.card ↥(K ⊓ C) ≤ Nat.card ↥(K ⊓ H) * Nat.card C := h
    _ = Nat.card C * Nat.card ↥(K ⊓ H) := mul_comm _ _

private theorem card_fixV_inf_sup_le_fac [Finite W] {A : Subgroup (MulAut W)}
    {Vp Vz : Subgroup W} (hinf : Vp ⊓ Vz = ⊥)
    (hp : ∀ a ∈ A, ∀ x ∈ Vp, a x ∈ Vp) (hz : ∀ a ∈ A, ∀ x ∈ Vz, a x ∈ Vz) :
    Nat.card ↥(fixV A ⊓ (Vp ⊔ Vz)) ≤
      Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz) := by
  have hle : fixV A ⊓ (Vp ⊔ Vz) ≤ (fixV A ⊓ Vp) ⊔ (fixV A ⊓ Vz) :=
    B51Sum.fixV_inf_sup_le hinf hp hz
  have hcard : Nat.card ↥((fixV A ⊓ Vp) ⊔ (fixV A ⊓ Vz)) ≤
      Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz) := by
    have h := (card_sup_mul_card_inf_of_commute (fixV A ⊓ Vp) (fixV A ⊓ Vz)
      (fun _ _ _ _ => mul_comm _ _)).1
    calc
      Nat.card ↥((fixV A ⊓ Vp) ⊔ (fixV A ⊓ Vz))
          = Nat.card ↥((fixV A ⊓ Vp) ⊔ (fixV A ⊓ Vz)) * 1 := by rw [mul_one]
      _ ≤ Nat.card ↥((fixV A ⊓ Vp) ⊔ (fixV A ⊓ Vz)) *
            Nat.card ↥((fixV A ⊓ Vp) ⊓ (fixV A ⊓ Vz)) :=
        Nat.mul_le_mul_left _ Nat.card_pos
      _ = Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz) := h
  exact (Subgroup.card_le_of_le hle).trans hcard

private theorem four_mul_card_le_of_sup_fac [Finite W] {A : Subgroup (MulAut W)}
    {V₀ Vp Vz : Subgroup W} {K : Subgroup (MulAut W)} (ra : ℕ)
    (hsup : Vp ⊔ Vz = V₀) (hinf : Vp ⊓ Vz = ⊥)
    (hp : ∀ a ∈ A, ∀ x ∈ Vp, a x ∈ Vp) (hz : ∀ a ∈ A, ∀ x ∈ Vz, a x ∈ Vz)
    (h4 : 4 * Nat.card ↥(Vp ⊓ fixV A) ≤ Nat.card Vp)
    (hKle : K ≤ A ⊓ centSec V₀ ⊥)
    (hcost : Nat.card V₀ * Nat.card ↥(A ⊓ centSec V₀ ⊥) ≤
      Nat.card A * Nat.card ↥(fixV A ⊓ V₀))
    (hk : ra * Nat.card K = Nat.card A) :
    4 * Nat.card Vz ≤ ra * Nat.card ↥(fixV A ⊓ Vz) := by
  have h4' : 4 * Nat.card ↥(fixV A ⊓ Vp) ≤ Nat.card Vp := by
    rwa [inf_comm (fixV A) Vp]
  have hcardV₀ : Nat.card V₀ = Nat.card Vp * Nat.card Vz := by
    have h := (card_sup_mul_card_inf_of_commute Vp Vz (fun _ _ _ _ => mul_comm _ _)).1
    rw [hsup, hinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hfixV₀ : Nat.card ↥(fixV A ⊓ V₀) ≤
      Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz) := by
    rw [← hsup]
    exact card_fixV_inf_sup_le_fac hinf hp hz
  have hcostV₀ : Nat.card V₀ * Nat.card K ≤
      Nat.card A * Nat.card ↥(fixV A ⊓ V₀) :=
    (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hKle)).trans hcost
  have hV₀le : Nat.card V₀ ≤ ra * Nat.card ↥(fixV A ⊓ V₀) := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card K) ?_ Nat.card_pos
    calc
      Nat.card V₀ * Nat.card K
          ≤ Nat.card A * Nat.card ↥(fixV A ⊓ V₀) := hcostV₀
      _ = (ra * Nat.card K) * Nat.card ↥(fixV A ⊓ V₀) := by rw [hk]
      _ = (ra * Nat.card ↥(fixV A ⊓ V₀)) * Nat.card K := by ring
  have hVpVz : Nat.card Vp * Nat.card Vz ≤
      ra * (Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz)) := by
    calc
      Nat.card Vp * Nat.card Vz = Nat.card V₀ := hcardV₀.symm
      _ ≤ ra * Nat.card ↥(fixV A ⊓ V₀) := hV₀le
      _ ≤ ra * (Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz)) :=
        Nat.mul_le_mul_left _ hfixV₀
  refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(fixV A ⊓ Vp)) ?_ Nat.card_pos
  calc
    4 * Nat.card Vz * Nat.card ↥(fixV A ⊓ Vp)
        = 4 * Nat.card ↥(fixV A ⊓ Vp) * Nat.card Vz := by ring
    _ ≤ Nat.card Vp * Nat.card Vz := Nat.mul_le_mul_right _ h4'
    _ ≤ ra * (Nat.card ↥(fixV A ⊓ Vp) * Nat.card ↥(fixV A ⊓ Vz)) := hVpVz
    _ = (ra * Nat.card ↥(fixV A ⊓ Vz)) * Nat.card ↥(fixV A ⊓ Vp) := by ring

private theorem arith_four_mul_le_fac {s f i rf g v ra : ℕ}
    (h1 : s * f ≤ i * rf) (h2 : i * g ≤ v * f) (h3 : 4 * v ≤ ra * g)
    (hf : 0 < f) (hg : 0 < g) : 4 * s ≤ ra * rf := by
  have h4 : 4 * s * (f * g) ≤ ra * rf * (f * g) := by
    calc
      4 * s * (f * g) = (s * f) * (4 * g) := by ring
      _ ≤ (i * rf) * (4 * g) := Nat.mul_le_mul_right _ h1
      _ = (i * g) * (4 * rf) := by ring
      _ ≤ (v * f) * (4 * rf) := Nat.mul_le_mul_right _ h2
      _ = (4 * v) * (f * rf) := by ring
      _ ≤ (ra * g) * (f * rf) := Nat.mul_le_mul_right _ h3
      _ = ra * rf * (f * g) := by ring
  exact Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos hf hg)

private theorem inf_centSec_submoduleClosure_eq_bot_fac [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L)
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) :
    (L ⊓ centSec I Z) ⊓ centSec (G6.submoduleClosure L (fixV S)) ⊥ = ⊥ := by
  let C : Subgroup (MulAut W) := L ⊓ centSec I Z
  let V₀ : Subgroup W := G6.submoduleClosure L (fixV S)
  have hChev : IsGomiChevTwo ↥L := h.2.2.2.2.2.1
  have hV₀stab : L ⊔ (S ⊓ Subgroup.normalizer (L : Set (MulAut W))) ≤ stabSub V₀ :=
    sup_le_stabSub_submoduleClosure_fixV S L
  have hLV₀ : L ≤ stabSub V₀ := le_sup_left.trans hV₀stab
  have hSV₀ : fixV S ≤ V₀ := by
    intro x hx
    refine (le_iSup₂_of_le (f := fun g (_ : g ∈ L) =>
      (fixV S).map (g : MulAut W).toMonoidHom) 1 L.one_mem le_rfl :
      (fixV S).map ((1 : MulAut W) : MulAut W).toMonoidHom ≤ V₀) ⟨x, hx, rfl⟩
  have hC₀L : C ⊓ centSec V₀ ⊥ ≤ L := inf_le_left.trans inf_le_left
  have hC₀Z : C ⊓ centSec V₀ ⊥ ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    inf_le_left.trans (inf_centSec_le_centralizer hChev.1 hIZ)
  have hC₀odd : Odd (Nat.card ↥(C ⊓ centSec V₀ ⊥)) :=
    Odd.of_dvd_nat (odd_card_inf_centSec hChev hIZ) (Subgroup.card_dvd_of_le inf_le_left)
  have hV₀fix : V₀ ≤ fixV (C ⊓ centSec V₀ ⊥) := by
    intro v hv c hc
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp
      ((mem_centSec.mp (Subgroup.mem_inf.mp hc).2).2 v hv))
  exact GomiFact36Hyp.eq_bot_of_fixV_le hW h hC₀L hC₀Z hC₀odd (hSV₀.trans hV₀fix)

private theorem le_stabSub_closure_fac {S L A : Subgroup (MulAut W)} (hAS : A ≤ S)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    L ≤ stabSub (G6.submoduleClosure L (fixV S)) ∧
      A ≤ stabSub (G6.submoduleClosure L (fixV S)) := by
  have h := sup_le_stabSub_submoduleClosure_fixV S L
  exact ⟨le_sup_left.trans h, (le_inf hAS hAL).trans (le_sup_right.trans h)⟩

private theorem conj_mem_inf_centSec_fac {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hCZ : L ⊓ centSec I Z ≤ Subgroup.centralizer (L : Set (MulAut W))) :
    ∀ l ∈ L, ∀ c ∈ L ⊓ centSec I Z, l * c * l⁻¹ ∈ L ⊓ centSec I Z := by
  intro l hl c hc
  refine ⟨L.mul_mem (L.mul_mem hl hc.1) (L.inv_mem hl), ?_⟩
  rw [Subgroup.mem_centralizer_iff.mp (hCZ hc) l hl, mul_assoc, mul_inv_cancel, mul_one]
  exact hc.2

private theorem inf_commSub_fixV_eq_bot_fac {C : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (hCV₀ : ∀ c ∈ C, ∀ w ∈ V₀, c w ∈ V₀)
    (hdecomp : commSub V₀ C ⊔ (V₀ ⊓ fixV C) = V₀ ∧
      commSub V₀ C ⊓ (V₀ ⊓ fixV C) = ⊥) :
    commSub V₀ C ⊓ fixV C = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  have hx' : x ∈ commSub V₀ C ⊓ (V₀ ⊓ fixV C) :=
    ⟨hx.1, (commSub_le_of_invariant hCV₀) hx.1, hx.2⟩
  rw [hdecomp.2] at hx'
  exact hx'

private theorem inf_centSec_commSub_eq_bot_fac {C : Subgroup (MulAut W)} {V₀ Vz : Subgroup W}
    (hdecomp : commSub V₀ C ⊔ Vz = V₀) (hVz : Vz = V₀ ⊓ fixV C)
    (hC₀ : C ⊓ centSec V₀ ⊥ = ⊥) :
    C ⊓ centSec (commSub V₀ C) ⊥ = ⊥ := by
  have hfix : Vz ≤ fixV C := by rw [hVz]; exact inf_le_right
  have hle := inf_centSec_sup_le_fac (C := C) (V₀ := V₀) (Vp := commSub V₀ C) (Vz := Vz)
    hdecomp hfix
  exact le_bot_iff.mp (hle.trans (le_of_eq hC₀))

private theorem sup_Z_inf_fixV_eq_fac [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {I Z : Subgroup W} (hLI : L ≤ stabSub I)
    (hIZ : IsGomiNoncentralFactor L I Z) (hCodd : Odd (Nat.card ↥(L ⊓ centSec I Z))) :
    Z ⊔ (I ⊓ fixV (L ⊓ centSec I Z)) = I := by
  let C : Subgroup (MulAut W) := L ⊓ centSec I Z
  have hCL : C ≤ L := inf_le_left
  have hCinv : XMod.IsInv ↥C I := fun c w hw => (mem_stabSub.mp (hLI (hCL c.2)) w).2 hw
  have hsupI : commSub I C ⊔ (I ⊓ fixV C) = I :=
    (CFSG.Quasithin.coprime_decomp hCodd hW (fun c hc w hw => hCinv ⟨c, hc⟩ w hw)).1
  have hcommIZ : commSub I C ≤ Z := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨c, hc, w, hw, rfl⟩
    exact (mem_centSec.mp (Subgroup.mem_inf.mp hc).2).2 w hw
  refine le_antisymm (sup_le hIZ.2.2.1.1.le inf_le_left) ?_
  calc I = commSub I C ⊔ (I ⊓ fixV C) := hsupI.symm
    _ ≤ Z ⊔ (I ⊓ fixV C) := sup_le_sup_right hcommIZ _

private theorem card_autSec_mul_inf_fac [Finite W] {L A : Subgroup (MulAut W)}
    {I Z : Subgroup W} (hQuasi : CFSG.IsQuasisimple ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hLI : L ≤ stabSub I)
    (hLZ : L ≤ stabSub Z) (hnc : ¬ XMod.commOf ↥L I ≤ Z)
    (hI : I ≤ fixV (A ⊓ Subgroup.centralizer (L : Set (MulAut W))))
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) :
    Nat.card ↥(autSec A I Z) *
      Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) = Nat.card A := by
  have hcent : A ⊓ centSec I Z = A ⊓ Subgroup.centralizer (L : Set (MulAut W)) :=
    inf_centSec_eq_inf_centralizer hQuasi hAL hLI hLZ hnc hI
  rw [← hcent]
  exact card_autSec_mul hAI hAZ

private theorem K_le_centSec_fac [Finite W] {S L A : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (hV₀ : V₀ = G6.submoduleClosure L (fixV S)) (hAS : A ≤ S) :
    A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤ A ⊓ centSec V₀ ⊥ := by
  refine le_inf inf_le_left (le_centSec_bot_of_le_fixV ?_)
  rw [hV₀]
  exact submoduleClosure_fixV_le_fixV (S := S) (L := L)
    (inf_le_left.trans hAS) inf_le_right

private theorem faithful_data_fac [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) {I Z : Subgroup W}
    (hIZ : IsGomiNoncentralFactor L I Z) {V₀ : Subgroup W} {C : Subgroup (MulAut W)}
    (hV₀ : V₀ = G6.submoduleClosure L (fixV S))
    (hCV₀ : ∀ c ∈ C, ∀ w ∈ V₀, c w ∈ V₀)
    (hdecomp : commSub V₀ C ⊔ (V₀ ⊓ fixV C) = V₀ ∧
      commSub V₀ C ⊓ (V₀ ⊓ fixV C) = ⊥)
    (hCdef : C = L ⊓ centSec I Z) :
    commSub V₀ C ⊓ fixV C = ⊥ ∧ C ⊓ centSec (commSub V₀ C) ⊥ = ⊥ := by
  have hC₀ : C ⊓ centSec V₀ ⊥ = ⊥ := by
    rw [hCdef, hV₀]
    exact inf_centSec_submoduleClosure_eq_bot_fac hW h hIZ
  exact ⟨inf_commSub_fixV_eq_bot_fac hCV₀ hdecomp,
    inf_centSec_commSub_eq_bot_fac hdecomp.1 rfl hC₀⟩

private theorem not_le_fixV_commSub_fac [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L A : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) (hAS : A ≤ S)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) (hC : L ⊓ centSec I Z ≠ ⊥) :
    ¬ commSub (G6.submoduleClosure L (fixV S)) (L ⊓ centSec I Z) ≤ fixV A := by
  let C : Subgroup (MulAut W) := L ⊓ centSec I Z
  let V₀ : Subgroup W := G6.submoduleClosure L (fixV S)
  let Vp : Subgroup W := commSub V₀ C
  let Vz : Subgroup W := V₀ ⊓ fixV C
  have hChev : IsGomiChevTwo ↥L := h.2.2.2.2.2.1
  have hCL : C ≤ L := inf_le_left
  have hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    inf_centSec_le_centralizer hChev.1 hIZ
  have hLCnorm := conj_mem_inf_centSec_fac (L := L) (I := I) (Z := Z) hCZ
  have hLV₀ : L ≤ stabSub V₀ := (le_stabSub_closure_fac (A := A) hAS hAL).1
  have hCV₀ : ∀ c ∈ C, ∀ w ∈ V₀, c w ∈ V₀ := fun c hc w hw =>
    (mem_stabSub.mp (hLV₀ (hCL hc)) w).2 hw
  have hdecomp : Vp ⊔ Vz = V₀ ∧ Vp ⊓ Vz = ⊥ :=
    CFSG.Quasithin.coprime_decomp (odd_card_inf_centSec hChev hIZ) hW hCV₀
  have hC₀bot : C ⊓ centSec V₀ ⊥ = ⊥ :=
    inf_centSec_submoduleClosure_eq_bot_fac hW h hIZ
  have hCVp : C ⊓ centSec Vp ⊥ = ⊥ := inf_centSec_commSub_eq_bot_fac hdecomp.1 rfl hC₀bot
  have hLVp : L ≤ stabSub Vp := le_stabSub_commSub_fac hLV₀ hLCnorm
  intro hVpfix
  by_cases hnc : XMod.commOf ↥L Vp ≤ ⊥
  · have hVpfixC : Vp ≤ fixV C := by
      intro w hw c hc
      have h := (XMod.commOf_le_iff.mp hnc) ⟨c, hCL hc⟩ w hw
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h
      simpa [MulAut.smul_def] using h
    have hle : C ≤ centSec Vp ⊥ := le_centSec_bot_of_le_fixV hVpfixC
    have hCbot : C = ⊥ := by
      rw [← inf_eq_left.mpr hle, hCVp]
    exact hC hCbot
  · exact hAnc (le_centralizer_of_le_fixV_fac hChev.1 hAL hLVp hnc hVpfix)

private theorem four_mul_card_commSub_le_fac [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L A : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) (hAS : A ≤ S)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {I Z : Subgroup W} (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hIZ : IsGomiNoncentralFactor L I Z) (hC : L ⊓ centSec I Z ≠ ⊥)
    {V₀ : Subgroup W} (hV₀ : V₀ = G6.submoduleClosure L (fixV S))
    {C : Subgroup (MulAut W)} (hCdef : C = L ⊓ centSec I Z)
    (hdecomp : commSub V₀ C ⊔ (V₀ ⊓ fixV C) = V₀ ∧
      commSub V₀ C ⊓ (V₀ ⊓ fixV C) = ⊥)
    (hCV₀ : ∀ c ∈ C, ∀ w ∈ V₀, c w ∈ V₀)
    (hLVp : L ≤ stabSub (commSub V₀ C)) (hAVp : A ≤ stabSub (commSub V₀ C)) :
    4 * Nat.card ↥(commSub V₀ C ⊓ fixV A) ≤ Nat.card (commSub V₀ C) := by
  have hChev : IsGomiChevTwo ↥L := h.2.2.2.2.2.1
  have hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hCdef]
    exact inf_centSec_le_centralizer hChev.1 hIZ
  have hCodd : Odd (Nat.card C) := by
    rw [hCdef]
    exact odd_card_inf_centSec hChev hIZ
  have hAC : A ≤ Subgroup.normalizer (C : Set (MulAut W)) := by
    rw [hCdef]
    exact le_normalizer_inf_centSec hAL hAI hAZ
  obtain ⟨hVpC, hCVp⟩ := faithful_data_fac hW h hIZ hV₀ hCV₀ hdecomp hCdef
  have hntVp : ¬ commSub V₀ C ≤ fixV A := by
    rw [hV₀, hCdef]
    exact not_le_fixV_commSub_fac hW h hAS hAL hAnc hIZ hC
  exact four_mul_card_inf_fixV_le hW hChev.1.1 (hCdef ▸ inf_le_left) hCZ hCodd hAC hAe
    hLVp hAVp hVpC hCVp hntVp

theorem GomiFact36Hyp.four_mul_card_sec_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L A : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) (hAS : A ≤ S)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hcost : ∀ U : Subgroup W,
      Nat.card U * Nat.card ↥(A ⊓ centSec U ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U))
    {I Z : Subgroup W} (hIV : I ≤ G6.submoduleClosure L (fixV S)) (hAI : A ≤ stabSub I)
    (hAZ : A ≤ stabSub Z) (hIZ : IsGomiNoncentralFactor L I Z) (hC : L ⊓ centSec I Z ≠ ⊥) :
    4 * Nat.card (Sec I Z) ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z)) := by
  let C : Subgroup (MulAut W) := L ⊓ centSec I Z
  let V₀ : Subgroup W := G6.submoduleClosure L (fixV S)
  let Vp : Subgroup W := commSub V₀ C
  let Vz : Subgroup W := V₀ ⊓ fixV C
  let I' : Subgroup W := I ⊓ fixV C
  let K : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (L : Set (MulAut W))
  obtain ⟨hLV₀, hAV₀⟩ := le_stabSub_closure_fac (S := S) (L := L) (A := A) hAS hAL
  have hLCnorm := conj_mem_inf_centSec_fac (L := L) (I := I) (Z := Z)
    (inf_centSec_le_centralizer (h.2.2.2.2.2.1).1 hIZ)
  have hACnorm : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C :=
    Subgroup.le_normalizer_iff.mp (le_normalizer_inf_centSec hAL hAI hAZ)
  have hCV₀ : ∀ c ∈ C, ∀ w ∈ V₀, c w ∈ V₀ := fun c hc w hw =>
    (mem_stabSub.mp (hLV₀ ((inf_le_left : C ≤ L) hc)) w).2 hw
  have hdecomp : Vp ⊔ Vz = V₀ ∧ Vp ⊓ Vz = ⊥ :=
    CFSG.Quasithin.coprime_decomp (odd_card_inf_centSec h.2.2.2.2.2.1 hIZ) hW hCV₀
  have hK₀ := K_le_centSec_fac (S := S) (L := L) (A := A) (V₀ := V₀) rfl hAS
  have hLVp : L ≤ stabSub Vp := le_stabSub_commSub_fac hLV₀ hLCnorm
  obtain ⟨hAVp, hAVz⟩ := le_stabSub_commSub_inf_fac hAV₀ hACnorm
  have h4 : 4 * Nat.card ↥(Vp ⊓ fixV A) ≤ Nat.card Vp :=
    four_mul_card_commSub_le_fac hW h hAS hAL hAe hAnc hAI hAZ hIZ hC rfl rfl hdecomp hCV₀
      hLVp hAVp
  have hI'Vz : I' ≤ Vz := fun x hx => ⟨hIV hx.1, hx.2⟩
  have hZI' : Z ⊔ I' = I := sup_Z_inf_fixV_eq_fac hW hIZ.le_stabSub_left hIZ
    (odd_card_inf_centSec h.2.2.2.2.2.1 hIZ)
  have h6 := card_sec_mul_fixV_le_fac (A := A) hIZ.2.2.1.1.le
    (inf_le_left : I' ≤ I) hZI' hAI hAZ
  have h7 := card_mul_card_inf_le_fac (H := I') (K := fixV A) (C := Vz) hI'Vz
  have hV₀K : V₀ ≤ fixV K := submoduleClosure_fixV_le_fixV (S := S) (L := L)
    (inf_le_left.trans hAS) inf_le_right
  have hAK := card_autSec_mul_inf_fac (h.2.2.2.2.2.1).1 hAL hIZ.le_stabSub_left
    hIZ.le_stabSub_right
    hIZ.2.2.2 (hIV.trans hV₀K) hAI hAZ
  have hγ : 4 * Nat.card Vz ≤
      Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV A ⊓ Vz) :=
    four_mul_card_le_of_sup_fac (A := A) (V₀ := V₀) (Vp := Vp) (Vz := Vz) (K := K)
      (Nat.card ↥(autSec A I Z)) hdecomp.1 hdecomp.2
      (fun a ha x hx => (mem_stabSub.mp (hAVp ha) x).2 hx)
      (fun a ha x hx => (mem_stabSub.mp (hAVz ha) x).2 hx)
      h4 hK₀ (hcost V₀) hAK
  exact arith_four_mul_le_fac h6 h7 hγ Nat.card_pos Nat.card_pos

end CFSG.GroupTheory
