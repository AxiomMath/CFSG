
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHom
public import CFSG.Quasithin.Background.A1cModuleUnits
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

namespace L2Block

structure SecHypS {V : Type} [CommGroup V] (L A : Subgroup (MulAut V)) (U Z : Subgroup V) :
    Prop where
  simple : IsSimpleGroup ↥L
  nonab : ∃ a b : ↥L, a * b ≠ b * a
  normA : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L
  noncomm : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a
  stabLU : L ≤ stabSub U
  stabAU : A ≤ stabSub U
  stabAZ : A ≤ stabSub Z
  fixZ : Z = U ⊓ fixV L
  ltZU : Z < U
  irr : ∀ J : Subgroup V, Z ≤ J → J ≤ U → (∀ l ∈ L, ∀ w ∈ J, l w ∈ J) → J = Z ∨ J = U
  comm : U ≤ commSub U L

namespace SecHypS

variable {V : Type} [CommGroup V] [Finite V] {L A : Subgroup (MulAut V)} {U Z : Subgroup V}
  (H : SecHypS L A U Z)

include H

omit [Finite V] in
theorem isSimple : IsSimpleGroup ↥L := H.simple

omit [Finite V] in
theorem exists_noncomm_L : ∃ a b : ↥L, a * b ≠ b * a := H.nonab

omit [Finite V] in
theorem fix_le : Z ≤ fixV L := by
  rw [H.fixZ]
  exact inf_le_right

omit [Finite V] in
theorem stabLZ : L ≤ stabSub Z := by
  have : L ≤ centSub Z := fun l hl z hz => H.fix_le hz l hl
  exact this.trans (centSub_le_stabSub Z)

omit [Finite V] in
theorem stabX : L ⊔ A ≤ stabSub U ⊓ stabSub Z :=
  sup_le (le_inf H.stabLU H.stabLZ) (le_inf H.stabAU H.stabAZ)

omit [Finite V] in
theorem stabL : L ≤ stabSub U ⊓ stabSub Z := le_inf H.stabLU H.stabLZ

omit [Finite V] in
theorem stabA : A ≤ stabSub U ⊓ stabSub Z := le_inf H.stabAU H.stabAZ

omit [Finite V] in
theorem le_normalizer : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => H.normA a ha l hl, fun hl => ?_⟩
  have h := H.normA a⁻¹ (A.inv_mem ha) _ hl
  simpa [mul_assoc] using h

omit [Finite V] in
theorem normX : ∀ g ∈ L ⊔ A, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  intro x hx l hl
  obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer H.le_normalizer).1 hx
  have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
  rw [e]
  exact L.mul_mem (L.mul_mem hl' (H.normA a ha l hl)) (L.inv_mem hl')

omit [Finite V] H in
theorem conj_mem_centSec {g k : MulAut V} (hg : g ∈ stabSub U ⊓ stabSub Z) (hk : k ∈ centSec U Z) :
    g * k * g⁻¹ ∈ centSec U Z := by
  obtain ⟨hgU, hgZ⟩ := hg
  have hgU' : g⁻¹ ∈ stabSub U := (stabSub U).inv_mem hgU
  refine ⟨(stabSub U).mul_mem ((stabSub U).mul_mem hgU hk.1) hgU', fun w hw => ?_⟩
  have hw' : g⁻¹ w ∈ U := (hgU' w).2 hw
  have h1 : k (g⁻¹ w) * (g⁻¹ w)⁻¹ ∈ Z := hk.2 _ hw'
  have h2 : g (k (g⁻¹ w) * (g⁻¹ w)⁻¹) ∈ Z := (hgZ _).2 h1
  have e : (g * k * g⁻¹) w * w⁻¹ = g (k (g⁻¹ w) * (g⁻¹ w)⁻¹) := by
    rw [map_mul, map_inv]
    simp
  rw [e]
  exact h2

omit [Finite V] in
theorem not_le_centSec : ¬ L ≤ centSec U Z := by
  intro h
  have h1 : commSub U L ≤ Z := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact (h hx).2 w hw
  exact absurd (H.comm.trans h1) (not_le_of_gt H.ltZU)

omit [Finite V] in
theorem inf_centSec_eq_bot : L ⊓ centSec U Z = ⊥ := by
  have := H.isSimple
  set K : Subgroup (MulAut V) := L ⊓ centSec U Z with hK
  have hnorm : (K.subgroupOf L).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hk.1) (L.inv_mem g.2), ?_⟩
    exact conj_mem_centSec (H.stabL g.2) hk.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf L) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥L) ∈ K.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    apply H.not_le_centSec
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ K.subgroupOf L := by rw [h]; trivial
    exact (Subgroup.mem_subgroupOf.1 this).2

omit [Finite V] in
theorem commute_of_mem_centSec {x : MulAut V} (hx : x ∈ A) (hxs : x ∈ centSec U Z) :
    ∀ l ∈ L, x * l = l * x := by
  intro l hl
  have hxst : x ∈ stabSub U ⊓ stabSub Z := H.stabA hx
  have hlst : l ∈ stabSub U ⊓ stabSub Z := H.stabL hl
  have hc : x * l * x⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem (H.normA x hx l hl) (L.inv_mem hl)
  have hcs : x * l * x⁻¹ * l⁻¹ ∈ centSec U Z := by
    have hcst : x * l * x⁻¹ * l⁻¹ ∈ stabSub U ⊓ stabSub Z :=
      ((stabSub U ⊓ stabSub Z).mul_mem
        ((stabSub U ⊓ stabSub Z).mul_mem ((stabSub U ⊓ stabSub Z).mul_mem hxst hlst)
          ((stabSub U ⊓ stabSub Z).inv_mem hxst)) ((stabSub U ⊓ stabSub Z).inv_mem hlst))
    rw [← secHom_eq_one_iff (⟨_, hcst⟩ : ↥(stabSub U ⊓ stabSub Z))]
    have hx1 : secHom U Z ⟨x, hxst⟩ = 1 := (secHom_eq_one_iff ⟨x, hxst⟩).2 hxs
    have e : (⟨x * l * x⁻¹ * l⁻¹, hcst⟩ : ↥(stabSub U ⊓ stabSub Z)) =
        ⟨x, hxst⟩ * ⟨l, hlst⟩ * ⟨x, hxst⟩⁻¹ * ⟨l, hlst⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hx1]
    simp
  have h1 : x * l * x⁻¹ * l⁻¹ ∈ L ⊓ centSec U Z := ⟨hc, hcs⟩
  rw [H.inf_centSec_eq_bot, Subgroup.mem_bot] at h1
  calc x * l = (x * l * x⁻¹ * l⁻¹) * (l * x) := by group
    _ = l * x := by rw [h1, one_mul]

omit [Finite V] in
theorem inf_centSec_le_centSub : A ⊓ centSec U Z ≤ centSub U := by
  rintro x ⟨hxA, hxs⟩
  have hcomm := H.commute_of_mem_centSec hxA hxs
  let D : Subgroup V :=
    { carrier := {v | x v = v}
      one_mem' := map_one x
      mul_mem' := fun {a b} ha hb => by
        show x (a * b) = a * b
        rw [map_mul, show x a = a from ha, show x b = b from hb]
      inv_mem' := fun {a} ha => by
        show x a⁻¹ = a⁻¹
        rw [map_inv, show x a = a from ha] }
  have hD : ∀ v, v ∈ D ↔ x v = v := fun v => Iff.rfl
  have hgen : ∀ l ∈ L, ∀ u ∈ U, l u * u⁻¹ ∈ D := by
    intro l hl u hu
    rw [hD]
    obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ Z, x u = z * u := ⟨x u * u⁻¹, hxs.2 u hu, by simp⟩
    have hlz : l z = z := H.fix_le hzZ l hl
    have hxl : x (l u) = l (x u) := by
      have := congrArg (fun φ : MulAut V => φ u) (hcomm l hl)
      simpa [MulAut.mul_apply] using this
    rw [map_mul, map_inv, hxl, hz, map_mul, hlz, ← div_eq_mul_inv, ← div_eq_mul_inv,
      mul_div_mul_left_eq_div]
  have hUD : U ≤ D := H.comm.trans (by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    exact hgen l hl u hu)
  intro u hu
  exact (hD u).1 (hUD hu)

omit [Finite V] in
theorem not_le_centSec_A : ¬ A ≤ centSec U Z := by
  intro h
  obtain ⟨a, ha, l, hl, hne⟩ := H.noncomm
  exact hne (H.commute_of_mem_centSec ha (h ha) l hl)

end SecHypS

end L2Block

end Bridge

end CFSG.QuasithinUnique

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

namespace L2Block

namespace SecHypS

variable {V : Type} [CommGroup V] [Finite V] {L A : Subgroup (MulAut V)} {U Z : Subgroup V}
  (H : SecHypS L A U Z)

include H

variable {G : Subgroup (MulAut V)}

theorem card_le_autSec (hA : IsFFStarOffender G A) :
    Nat.card (Sec U Z) ≤ Nat.card ↥(autSec A U Z) * Nat.card ↥(fixV (autSec A U Z)) := by
  have hZU : Z ≤ U := H.ltZU.le
  set N : Subgroup (MulAut V) := A ⊓ centSub U with hN
  have hNA : N ≤ A := inf_le_left
  have h1 := B1.card_inf_fixV_le hA hNA U
  have hUN : U ⊓ fixV N = U := inf_eq_left.2 (fun u hu n hn => hn.2 u hu)
  rw [hUN] at h1
  have h2 := card_autSec_mul (A := A) (W := U) (U := Z) H.stabAU H.stabAZ
  have hNeq : A ⊓ centSec U Z = N :=
    le_antisymm (le_inf inf_le_left H.inf_centSec_le_centSub)
      (inf_le_inf_left A (centSub_le_centSec U Z))
  rw [hNeq] at h2
  have h3 := card_sec_mul (V := V) hZU
  have h4 := card_inf_fixV_le_autSec (A := A) hZU H.stabAU
  have h5 : Nat.card ↥(Z ⊓ fixV A) ≤ Nat.card Z := Subgroup.card_le_of_le inf_le_left
  have hn : 0 < Nat.card N := Nat.card_pos
  have hz : 0 < Nat.card Z := Nat.card_pos
  have h6 : Nat.card U ≤ Nat.card ↥(autSec A U Z) * Nat.card ↥(U ⊓ fixV A) := by
    have h7 : Nat.card N * Nat.card U ≤
        (Nat.card ↥(autSec A U Z) * Nat.card N) * Nat.card ↥(U ⊓ fixV A) := by
      rw [h2]; exact h1
    have h8 : Nat.card N * Nat.card U ≤
        Nat.card N * (Nat.card ↥(autSec A U Z) * Nat.card ↥(U ⊓ fixV A)) := by
      calc Nat.card N * Nat.card U
            ≤ (Nat.card ↥(autSec A U Z) * Nat.card N) * Nat.card ↥(U ⊓ fixV A) := h7
        _ = Nat.card N * (Nat.card ↥(autSec A U Z) * Nat.card ↥(U ⊓ fixV A)) := by ring
    exact Nat.le_of_mul_le_mul_left h8 hn
  have h9 : Nat.card (Sec U Z) * Nat.card Z ≤
      (Nat.card ↥(autSec A U Z) * Nat.card ↥(fixV (autSec A U Z))) * Nat.card Z := by
    calc Nat.card (Sec U Z) * Nat.card Z = Nat.card U := h3
      _ ≤ Nat.card ↥(autSec A U Z) * Nat.card ↥(U ⊓ fixV A) := h6
      _ ≤ Nat.card ↥(autSec A U Z) * (Nat.card ↥(fixV (autSec A U Z)) * Nat.card ↥(Z ⊓ fixV A)) :=
          Nat.mul_le_mul_left _ h4
      _ ≤ Nat.card ↥(autSec A U Z) * (Nat.card ↥(fixV (autSec A U Z)) * Nat.card Z) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h5)
      _ = (Nat.card ↥(autSec A U Z) * Nat.card ↥(fixV (autSec A U Z))) * Nat.card Z := by ring
  exact Nat.le_of_mul_le_mul_right h9 hz

theorem isFFModule (hA : IsFFStarOffender G A) : IsFFModule (autSec (L ⊔ A) U Z) := by
  have hFFA : IsFFModule (autSec A U Z) :=
    ⟨autSec A U Z, le_rfl, autSec_ne_bot H.stabA H.not_le_centSec_A,
      isElemAbelian2_autSec hA.2.2.1 H.stabA, H.card_le_autSec hA⟩
  exact B1Red.isFFModule_mono (autSec_mono le_sup_right U Z) hFFA

omit [Finite V] in
theorem secRestrict_injective : Function.Injective (secRestrict H.stabL (U' := Z)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : secHom U Z (Subgroup.inclusion H.stabL x) = 1 := by
    have := congrArg Subtype.val hx
    simpa [secRestrict_apply] using this
  have h2 := (secHom_eq_one_iff _).1 h1
  have h3 : (x : MulAut V) ∈ L ⊓ centSec U Z := ⟨x.2, h2⟩
  rw [H.inf_centSec_eq_bot, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

omit [Finite V] in
theorem exists_equiv_autSec : Nonempty (↥L ≃* ↥(autSec L U Z)) :=
  ⟨MulEquiv.ofBijective (secRestrict H.stabL)
      ⟨H.secRestrict_injective, secRestrict_surjective H.stabL⟩⟩

omit [Finite V] in
theorem isSimple_autSec : IsSimpleGroup ↥(autSec L U Z) := by
  obtain ⟨e₁⟩ := H.exists_equiv_autSec
  have := H.isSimple
  exact e₁.symm.isSimpleGroup

omit [Finite V] in
theorem quasisimple_autSec : CFSG.Open.IsQuasisimple ↥(autSec L U Z) := by
  have := H.isSimple_autSec
  obtain ⟨e₁⟩ := H.exists_equiv_autSec
  obtain ⟨a, b, hab⟩ := H.exists_noncomm_L
  have hnc : ∃ a b : ↥(autSec L U Z), a * b ≠ b * a :=
    ⟨e₁ a, e₁ b, fun h => hab (e₁.injective (by rw [map_mul, map_mul]; exact h))⟩
  exact B1Red.isQuasisimple_to_open (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

omit [Finite V] in
theorem normG : ∀ y ∈ autSec (L ⊔ A) U Z, ∀ l ∈ autSec L U Z, y * l * y⁻¹ ∈ autSec L U Z := by
  intro y hy l hl
  obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom H.stabX).1 hy
  obtain ⟨k, hkL, rfl⟩ := (mem_autSec_iff_secHom H.stabL).1 hl
  have hgk : (g : MulAut V) * (k : MulAut V) * (g : MulAut V)⁻¹ ∈ L := H.normX _ hgX _ hkL
  rw [← map_inv, ← map_mul, ← map_mul]
  exact secHom_mem_autSec H.stabL (g := g * k * g⁻¹) hgk

omit [Finite V] in
theorem sqG (hA2 : ∀ a ∈ A, a ^ 2 = 1) : ∀ y ∈ autSec (L ⊔ A) U Z, y ^ 2 ∈ autSec L U Z := by
  intro y hy
  obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom H.stabX).1 hy
  have hg2 : (g : MulAut V) ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup H.le_normalizer hA2 _ hgX
  rw [← map_pow]
  exact secHom_mem_autSec H.stabL (g := g ^ 2) hg2

omit [Finite V] H in
theorem le_autSec : autSec L U Z ≤ autSec (L ⊔ A) U Z := autSec_mono le_sup_left U Z

omit [Finite V] in
theorem exists_noncomm_autSec : ∃ a b : ↥(autSec L U Z), a * b ≠ b * a := by
  obtain ⟨e₁⟩ := H.exists_equiv_autSec
  obtain ⟨a, b, hab⟩ := H.exists_noncomm_L
  exact ⟨e₁ a, e₁ b, fun h => hab (e₁.injective (by rw [map_mul, map_mul]; exact h))⟩

omit [Finite V] in
theorem isIrrSec : XMod.IsIrrSec ↥(autSec L U Z) (⊥ : Subgroup (Sec U Z)) ⊤ := by
  have hZU : Z ≤ U := H.ltZU.le
  obtain ⟨u₀, hu₀U, hu₀Z⟩ := IsConcreteLE.not_le_iff_exists.1 (not_le_of_gt H.ltZU)
  have hmk : ∀ u : ↥U, (QuotientGroup.mk u : Sec U Z) = 1 ↔ (u : V) ∈ Z := by
    intro u
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨?_, fun J hJ _ _ => ?_⟩
  · refine lt_of_le_of_ne bot_le fun h => ?_
    have : (QuotientGroup.mk (⟨u₀, hu₀U⟩ : ↥U) : Sec U Z) ∈ (⊥ : Subgroup (Sec U Z)) := by
      rw [h]; trivial
    exact hu₀Z ((hmk _).1 (Subgroup.mem_bot.1 this))
  · set J' : Subgroup V := (J.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype with hJ'
    have hmemJ' : ∀ v : V, v ∈ J' ↔ ∃ u : ↥U, (QuotientGroup.mk u : Sec U Z) ∈ J ∧ (u : V) = v := by
      intro v
      simp [hJ', Subgroup.mem_map, Subgroup.mem_comap]
    have h1 : Z ≤ J' := by
      intro z hz
      rw [hmemJ']
      refine ⟨⟨z, hZU hz⟩, ?_, rfl⟩
      rw [(hmk ⟨z, hZU hz⟩).2 hz]
      exact J.one_mem
    have h2 : J' ≤ U := by
      intro v hv
      obtain ⟨u, -, rfl⟩ := (hmemJ' v).1 hv
      exact u.2
    have h3 : ∀ l ∈ L, ∀ w ∈ J', l w ∈ J' := by
      intro l hl w hw
      obtain ⟨u, huJ, rfl⟩ := (hmemJ' w).1 hw
      rw [hmemJ']
      have hlU : (l : MulAut V) (u : V) ∈ U := (H.stabLU hl (u : V)).2 u.2
      refine ⟨⟨l (u : V), hlU⟩, ?_, rfl⟩
      have hls : l ∈ stabSub U ⊓ stabSub Z := H.stabL hl
      have hmem : secHom U Z ⟨l, hls⟩ ∈ autSec L U Z := secHom_mem_autSec H.stabL (g := ⟨l, hls⟩) hl
      have := hJ ⟨secHom U Z ⟨l, hls⟩, hmem⟩ _ huJ
      exact this
    rcases H.irr J' h1 h2 h3 with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
      have : (u : V) ∈ J' := (hmemJ' _).2 ⟨u, hs, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.2 ((hmk u).2 this)
    · right
      rw [eq_top_iff]
      intro s _
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
      have : (u : V) ∈ J' := by rw [h]; exact u.2
      obtain ⟨u', hu'J, hu'⟩ := (hmemJ' _).1 this
      have : u' = u := Subtype.ext hu'
      rw [← this]
      exact hu'J

end SecHypS

end L2Block

end Bridge

end CFSG.QuasithinUnique

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

namespace L2Block

namespace SecHypS

variable {V : Type} [CommGroup V] [Finite V] {L A : Subgroup (MulAut V)} {U Z : Subgroup V}
  (H : SecHypS L A U Z)

include H

variable {G : Subgroup (MulAut V)}

omit [Finite V] H in
theorem eq_one_of_commOf_eq_bot
    (h : XMod.commOf ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) = ⊥) (a : ↥(autSec L U Z)) :
    a = 1 := by
  apply Subtype.ext
  ext s
  have hs : (a • s) * s⁻¹ ∈ XMod.commOf ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) :=
    Subgroup.subset_closure ⟨a, s, trivial, rfl⟩
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hs
  exact hs

omit [Finite V] in
theorem commOf_top : XMod.commOf ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) = ⊤ := by
  rcases H.isIrrSec.2 _ (XMod.isInv_commOf (A := ↥(autSec L U Z)) (⊤ : Subgroup (Sec U Z)))
    bot_le le_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := H.exists_noncomm_autSec
    exact hab (by rw [eq_one_of_commOf_eq_bot h a, eq_one_of_commOf_eq_bot h b])
  · exact h

omit [Finite V] in
theorem isIrrSec_fixed :
    XMod.IsIrrSec ↥(autSec L U Z) (XMod.fixed ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z))) ⊤ := by
  refine ⟨?_, fun J hJ hfJ _ => ?_⟩
  · refine lt_of_le_of_ne le_top fun h => ?_
    obtain ⟨a, b, hab⟩ := H.exists_noncomm_autSec
    have htriv : ∀ c : ↥(autSec L U Z), c = 1 := by
      intro c
      apply Subtype.ext
      ext s
      have hs : s ∈ XMod.fixed ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) := by rw [h]; trivial
      exact hs.2 c
    exact hab (by rw [htriv a, htriv b])
  · rcases H.isIrrSec.2 J hJ bot_le le_top with h | h
    · left
      rw [h] at hfJ ⊢
      exact (le_bot_iff.1 hfJ).symm
    · right
      exact h

theorem isTwoReduced : XMod.IsTwoReduced ↥(autSec L U Z) (⊤ : Subgroup (Sec U Z)) := by
  intro D hD hdk d hd l _
  have := H.isSimple_autSec
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
  · have hd1 : d = 1 := by rw [h] at hd; exact Subgroup.mem_bot.1 hd
    simp [hd1]
  · exfalso
    have h2 : IsPGroup 2 ↥(autSec L U Z) := by
      intro g
      obtain ⟨k, hk⟩ := hdk g (h ▸ Subgroup.mem_top g)
      refine ⟨k, ?_⟩
      apply Subtype.ext
      ext s
      exact hk s trivial
    have hnil := h2.isNilpotent
    have hq := H.quasisimple_autSec
    have : Group.IsPerfect ↥(autSec L U Z) := ⟨hq.1⟩
    have : Nontrivial ↥(autSec L U Z) := (H.isSimple_autSec).toNontrivial
    exact Group.IsPerfect.not_isNilpotent ↥(autSec L U Z) hnil

theorem pCoreOf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) : pCoreOf 2 (autSec (L ⊔ A) U Z) = ⊥ := by
  have hq := H.quasisimple_autSec
  have := H.isSimple_autSec
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (autSec (L ⊔ A) U Z)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (autSec (L ⊔ A) U Z)
  have hQle : pCoreOf 2 (autSec (L ⊔ A) U Z) ≤ autSec (L ⊔ A) U Z :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hnot : ¬ autSec L U Z ≤ pCoreOf 2 (autSec (L ⊔ A) U Z) := by
    intro hle
    have hnil := (hQ2.to_le hle).isNilpotent
    have : Group.IsPerfect ↥(autSec L U Z) := ⟨hq.1⟩
    have : Nontrivial ↥(autSec L U Z) := (H.isSimple_autSec).toNontrivial
    exact Group.IsPerfect.not_isNilpotent ↥(autSec L U Z) hnil
  have hcomm := B1Red.commute_of_normal_not_le hq
    (fun n hn l hl => H.normG n (hQle hn) l hl)
    (fun l hl n hn => B1Red.conj_mem_pCoreOf (le_autSec (A := A) hl) hn) hnot
  have hodd : Odd (Nat.card ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z))) :=
    XMod.odd_card_eqvAut (sec_sq_eq_one hV U Z) H.commOf_top H.isIrrSec_fixed H.isTwoReduced
  rw [eq_bot_iff]
  intro q hq'
  have hqe : q ∈ XMod.eqvAut ↥(autSec L U Z) (Sec U Z) := by
    intro a p
    exact congrArg (fun f : MulAut (Sec U Z) => f p) (hcomm q hq' a a.2)
  obtain ⟨k, hk⟩ := hQ2 ⟨q, hq'⟩
  have hk' : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z))) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hd1 : orderOf (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z))) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z))) ∣
      Nat.card ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z)) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hord := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have h1 : (⟨q, hqe⟩ : ↥(XMod.eqvAut ↥(autSec L U Z) (Sec U Z))) = 1 := orderOf_eq_one_iff.1 hord
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem genFitting_eq (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hV : ∀ v : V, v ^ 2 = 1) :
    quasithinGenFitting (autSec (L ⊔ A) U Z) = autSec L U Z :=
  B1Red.quasithinGenFitting_eq_of_two_quot (le_autSec (A := A)) H.normG H.quasisimple_autSec
      (H.sqG hA2)
    (H.pCoreOf_eq_bot hV)

end SecHypS

end L2Block

end Bridge

end CFSG.QuasithinUnique
