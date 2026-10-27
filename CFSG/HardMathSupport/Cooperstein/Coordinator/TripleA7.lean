module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Main

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

namespace TripleA7

variable {V : Type} [CommGroup V]

theorem eq_one_of_mem_commV_of_apply_eq (hV : ∀ v : V, v ^ 2 = 1) {z : MulAut V}
    (hz3 : z ^ 3 = 1) {u : V} (hu : u ∈ commV (Subgroup.zpowers z)) (hfix : z u = u) : u = 1 := by
  let N : V →* V :=
    { toFun := fun v => v * z v * z (z v)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        ac_rfl }
  have hz3v : ∀ v, z (z (z v)) = v := fun v => by
    have := congrArg (fun f : MulAut V => f v) hz3
    simpa [pow_succ, MulAut.mul_apply] using this
  let S : Subgroup (MulAut V) :=
    { carrier := {x | ∀ v, N (x v) = N v}
      one_mem' := fun v => rfl
      mul_mem' := fun {a b} ha hb v => by
        rw [MulAut.mul_apply, ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (a⁻¹ v)
        rw [MulAut.apply_inv_self] at this
        exact this.symm }
  have hzS : z ∈ S := fun v => by
    show z v * z (z v) * z (z (z v)) = v * z v * z (z v)
    rw [hz3v, mul_comm (z v * z (z v)) v, mul_assoc]
  have hle : commV (Subgroup.zpowers z) ≤ N.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    have hxS : x ∈ S := (Subgroup.zpowers_le.2 hzS) hx
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hxS v, mul_inv_cancel]
  have h1 : N u = 1 := hle hu
  have h2 : N u = u := by
    show u * z u * z (z u) = u
    rw [hfix, hfix, ← pow_two, hV, one_mul]
  rw [← h2, h1]

theorem exists_ne_one_mem_commV {z : MulAut V} (hz : z ≠ 1) :
    ∃ u ∈ commV (Subgroup.zpowers z), u ≠ 1 := by
  obtain ⟨v, hv⟩ : ∃ v, z v ≠ v := by
    by_contra h
    push Not at h
    exact hz (MulEquiv.ext fun v => by rw [h v]; rfl)
  exact ⟨z v * v⁻¹, Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, v, rfl⟩,
    fun h => hv (mul_inv_eq_one.1 h)⟩

theorem apply_mem_commV_zpowers {z h : MulAut V} (hk : h * z * h⁻¹ ∈ Subgroup.zpowers z)
    {u : V} (hu : u ∈ commV (Subgroup.zpowers z)) : h u ∈ commV (Subgroup.zpowers z) := by
  have hle : commV (Subgroup.zpowers z) ≤
      (commV (Subgroup.zpowers z)).comap h.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hx' : h * z ^ j * h⁻¹ ∈ Subgroup.zpowers z := by
      rw [← conj_zpow, ← hk, ← zpow_mul]
      exact Subgroup.zpow_mem_zpowers z _
    show h ((z ^ j) v * v⁻¹) ∈ commV (Subgroup.zpowers z)
    have e : h ((z ^ j) v * v⁻¹) = (h * z ^ j * h⁻¹) (h v) * (h v)⁻¹ := by
      rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e]
    exact Subgroup.subset_closure ⟨_, hx', h v, rfl⟩
  exact hle hu

theorem card_le_card_mul_card_subgroupOf [Finite V] {A : Subgroup (MulAut V)} (U : Subgroup V)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    Nat.card U ≤ Nat.card A * Nat.card ((fixV A).subgroupOf U) := by
  have hD := Subgroup.card_mul_index ((fixV A).subgroupOf U)
  have hC := Subgroup.card_mul_index (fixV A)
  have hidx : ((fixV A).subgroupOf U).index ≤ (fixV A).index := by
    have := Subgroup.relIndex_le_of_le_right (H := fixV A) (le_top : U ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rw [Subgroup.relIndex_top_right] at this
    exact this
  have hCpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have key : Nat.card U * Nat.card (fixV A) ≤
      Nat.card A * Nat.card ((fixV A).subgroupOf U) * Nat.card (fixV A) := by
    calc Nat.card U * Nat.card (fixV A)
        = Nat.card ((fixV A).subgroupOf U) * ((fixV A).subgroupOf U).index *
            Nat.card (fixV A) := by rw [hD]
      _ ≤ Nat.card ((fixV A).subgroupOf U) * (fixV A).index * Nat.card (fixV A) := by gcongr
      _ = Nat.card ((fixV A).subgroupOf U) * Nat.card V := by rw [← hC]; ring
      _ ≤ Nat.card ((fixV A).subgroupOf U) * (Nat.card A * Nat.card (fixV A)) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right key hCpos

end TripleA7

open TripleA7 in
theorem gf2NoFFTripleA7 : GF2NoFFTripleA7 := by
  intro V _ _ hV H L hLF hLq hZ3 ⟨e⟩ A hA
  classical
  obtain ⟨hAH, hAne, hAel, hAmax⟩ := hA
  have hAoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have h := hAmax ⊥ bot_le
    have hfix : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      ext v
      simp only [Subgroup.mem_top, iff_true]
      intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    rwa [Subgroup.card_bot, hfix, Subgroup.card_top, one_mul] at h
  have hLH : L ≤ H := hLF ▸ quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hCL : H ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L := by
    have h1 := centralizer_quasithinGenFitting_le H
    rwa [← hLF] at h1
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [hZ3]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set zL : ↥L := (zc : ↥L) with hzL
  have hzLo : orderOf zL = 3 := by rw [hzL, Subgroup.orderOf_coe, hzc]
  have hcen : Subgroup.center ↥L = Subgroup.zpowers zL := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.2 zc.2
    · rw [hZ3, Nat.card_zpowers, hzLo]
  set z : MulAut V := (zL : MulAut V) with hz
  have hzo : orderOf z = 3 := by rw [hz, Subgroup.orderOf_coe, hzLo]
  have hz3 : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzo; omega
  have hconj : ∀ h ∈ H, h * z * h⁻¹ ∈ Subgroup.zpowers z := by
    intro h hh
    have hmemL : h * z * h⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hHN hh) z).1 zL.2
    have hc : (⟨h * z * h⁻¹, hmemL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg' : h⁻¹ * g * h ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hHN (H.inv_mem hh)) g).1 g.2
        rwa [inv_inv] at this
      have hcomm' : (h⁻¹ * g * h) * z = z * (h⁻¹ * g * h) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.1 zc.2 ⟨h⁻¹ * g * h, hg'⟩)
      show (g : MulAut V) * (h * z * h⁻¹) = h * z * h⁻¹ * g
      calc (g : MulAut V) * (h * z * h⁻¹) = h * ((h⁻¹ * g * h) * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * g * h)) * h⁻¹ := by rw [hcomm']
        _ = h * z * h⁻¹ * g := by group
    rw [hcen] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      have := congrArg Subtype.val hk
      simpa [hz] using this⟩
  set U : Subgroup V := commV (Subgroup.zpowers z)
  have hUinv : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U := fun h hh u hu =>
    apply_mem_commV_zpowers (hconj h hh) hu
  have hfp : ∀ u ∈ U, z u = u → u = 1 := fun u hu hfix =>
    eq_one_of_mem_commV_of_apply_eq hV hz3 hu hfix
  obtain ⟨u₀, hu₀U, hu₀⟩ := exists_ne_one_mem_commV hz1
  have hCLU : ∀ x ∈ L, (∀ u ∈ U, x u = u) → x = 1 := by
    let N : Subgroup ↥L :=
      { carrier := {x | ∀ u ∈ U, (x : MulAut V) u = u}
        one_mem' := fun u _ => rfl
        mul_mem' := fun {a b} ha hb u hu => by
          show (a : MulAut V) ((b : MulAut V) u) = u
          rw [hb u hu, ha u hu]
        inv_mem' := fun {a} ha u hu => by
          show (a : MulAut V)⁻¹ u = u
          conv_lhs => rw [← ha u hu]
          exact MulAut.inv_apply_self _ _ _ }
    have hNn : N.Normal := ⟨fun n hn g u hu => by
      show ((g : MulAut V) * n * (g : MulAut V)⁻¹) u = u
      have hgu : (g : MulAut V)⁻¹ u ∈ U := hUinv _ (hLH (L.inv_mem g.2)) u hu
      rw [MulAut.mul_apply, MulAut.mul_apply, hn _ hgu, MulAut.apply_inv_self]⟩
    have hzN : zL ∉ N := fun h => hu₀ (hfp u₀ hu₀U (h u₀ hu₀U))
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hLq N with hle | htop
    · intro x hxL hx
      by_contra hx1
      have hxN : (⟨x, hxL⟩ : ↥L) ∈ N := hx
      have hxc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := hle hxN
      have hx1' : (⟨⟨x, hxL⟩, hxc⟩ : ↥(Subgroup.center ↥L)) ≠ 1 := fun h =>
        hx1 (congrArg (fun y : ↥(Subgroup.center ↥L) => ((y : ↥L) : MulAut V)) h)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_prime_card hZ3 hx1' (g' := zc))
      have hk' : (⟨x, hxL⟩ : ↥L) ^ k = zL := congrArg Subtype.val hk
      exact hzN (hk' ▸ N.zpow_mem hxN k)
    · exact absurd (htop ▸ Subgroup.mem_top zL) hzN
  let r : ↥H →* MulAut ↥U :=
    (CFSG.Quasithin.resHom U).comp (Subgroup.inclusion (B1.le_stabSub_of_invariant hUinv))
  have hr_apply : ∀ (h : ↥H) (u : ↥U), ((r h u : ↥U) : V) = (h : MulAut V) u := fun _ _ => rfl
  have hrinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro h hh1
    have hfixU : ∀ u ∈ U, (h : MulAut V) u = u := fun u hu => by
      have := congrArg (fun f : MulAut ↥U => ((f ⟨u, hu⟩ : ↥U) : V)) hh1
      simpa [hr_apply] using this
    have hcomm : ∀ l ∈ L, l * (h : MulAut V) = (h : MulAut V) * l := by
      intro l hl
      have hc : (h : MulAut V) * l * (h : MulAut V)⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hHN h.2) l).1 hl) (L.inv_mem hl)
      have hcfix : ∀ u ∈ U, ((h : MulAut V) * l * (h : MulAut V)⁻¹ * l⁻¹) u = u := by
        intro u hu
        have h1 : l⁻¹ u ∈ U := hUinv _ (hLH (L.inv_mem hl)) u hu
        have h2 : (h : MulAut V)⁻¹ (l⁻¹ u) = l⁻¹ u := by
          conv_lhs => rw [← hfixU _ h1]
          exact MulAut.inv_apply_self _ _ _
        simp only [MulAut.mul_apply]
        rw [h2, MulAut.apply_inv_self, hfixU u hu]
      have h1 := hCLU _ hc hcfix
      calc l * (h : MulAut V)
          = ((h : MulAut V) * l * (h : MulAut V)⁻¹ * l⁻¹)⁻¹ * ((h : MulAut V) * l) := by group
        _ = (h : MulAut V) * l := by rw [h1, inv_one, one_mul]
    have hhL : (h : MulAut V) ∈ L :=
      hCL ⟨h.2, Subgroup.mem_centralizer_iff.2 fun l hl => hcomm l hl⟩
    exact Subtype.ext (hCLU _ hhL hfixU)
  set HU : Subgroup (MulAut ↥U) := r.range
  set fL : ↥L →* MulAut ↥U := r.comp (Subgroup.inclusion hLH) with hfL
  set LU : Subgroup (MulAut ↥U) := fL.range
  set fA : ↥A →* MulAut ↥U := r.comp (Subgroup.inclusion hAH)
  set AU : Subgroup (MulAut ↥U) := fA.range
  have hfLinj : Function.Injective fL := hrinj.comp (Subgroup.inclusion_injective hLH)
  have hfAinj : Function.Injective fA := hrinj.comp (Subgroup.inclusion_injective hAH)
  have hAUH : AU ≤ HU := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hLUHU : LU ≤ HU := by
    rintro _ ⟨l, rfl⟩
    exact ⟨_, rfl⟩
  have hAUne : AU ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨fA a, a, rfl⟩, fun h => ha ?_⟩
    exact hfAinj (by rw [map_one]; exact congrArg Subtype.val h)
  have hAUel : IsElemAbelian2 AU := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg fA (Subtype.ext (hAel.1 _ a.2 _ b.2))
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have ha2 : a ^ 2 = 1 := Subtype.ext (hAel.2 _ a.2)
      rw [ha2, map_one]
  have hAUoff : Nat.card ↥U ≤ Nat.card AU * Nat.card (fixV AU) := by
    have hcardA : Nat.card ↥A = Nat.card AU :=
      Nat.card_congr (MonoidHom.ofInjective hfAinj).toEquiv
    have hfixle : (fixV A).subgroupOf U ≤ fixV AU := by
      intro u hu
      rintro _ ⟨a, rfl⟩
      apply Subtype.ext
      exact (Subgroup.mem_subgroupOf.1 hu) a a.2
    calc Nat.card ↥U ≤ Nat.card A * Nat.card ((fixV A).subgroupOf U) :=
          card_le_card_mul_card_subgroupOf U hAoff
      _ ≤ Nat.card AU * Nat.card (fixV AU) := by
          rw [hcardA]
          exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hfixle)
  obtain ⟨BU, hBUA, hB⟩ := exists_isBestOffender_le hAUH hAUne hAUel hAUoff
  have hzU : fL zL ≠ 1 := fun h => by
    have := hfLinj (h.trans (map_one fL).symm)
    exact hz1 (congrArg Subtype.val this)
  have hLUq : CFSG.IsQuasisimple ↥LU :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hLq fL.rangeRestrict_surjective
      ⟨zL, fun h => hzU (congrArg Subtype.val h)⟩
  have hkey : ∀ g ∈ HU, ∀ y ∈ LU, g * y * g⁻¹ ∈ LU := by
    rintro _ ⟨h, rfl⟩ _ ⟨l, rfl⟩
    refine ⟨⟨(h : MulAut V) * l * (h : MulAut V)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (hHN h.2) l).1 l.2⟩, ?_⟩
    have e1 : Subgroup.inclusion hLH ⟨(h : MulAut V) * l * (h : MulAut V)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (hHN h.2) l).1 l.2⟩ =
        h * Subgroup.inclusion hLH l * h⁻¹ := Subtype.ext rfl
    simp only [hfL, MonoidHom.comp_apply]
    rw [e1, map_mul, map_mul, map_inv]
  have hHUN : HU ≤ Subgroup.normalizer (LU : Set (MulAut ↥U)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hkey g hg y, fun hy => ?_⟩
    have := hkey g⁻¹ (HU.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hLcomp : Family.IsComp LU HU :=
    ⟨hLUHU, IsSubnormal.step hLUHU ((Subgroup.normal_subgroupOf_iff_le_normalizer hLUHU).2 hHUN)
      (IsSubnormal.refl HU), ⟨hLUq.1.commutator_eq_top, hLUq.2.1⟩⟩
  have hLB : ⁅LU, BU⁆ ≠ ⊥ := by
    intro hc
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB.2.1
    obtain ⟨a, rfl⟩ := hBUA hb
    have hacomm : ∀ l ∈ L, l * (a : MulAut V) = (a : MulAut V) * l := by
      intro l hl
      have hmem := Subgroup.commutator_mem_commutator
        (show fL ⟨l, hl⟩ ∈ LU from ⟨⟨l, hl⟩, rfl⟩) hb
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      have h2 : r (Subgroup.inclusion hLH ⟨l, hl⟩ * Subgroup.inclusion hAH a) =
          r (Subgroup.inclusion hAH a * Subgroup.inclusion hLH ⟨l, hl⟩) := by
        rw [map_mul, map_mul]
        exact hmem
      exact congrArg Subtype.val (hrinj h2)
    have haL : (a : MulAut V) ∈ L :=
      hCL ⟨hAH a.2, Subgroup.mem_centralizer_iff.2 hacomm⟩
    have hac : (⟨a, haL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hacomm g g.2)
    have ha3 : (a : MulAut V) ^ 3 = 1 := by
      have h1 := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨⟨a, haL⟩, hac⟩)
      rw [hZ3] at h1
      simpa using congrArg (fun x : ↥(Subgroup.center ↥L) => ((x : ↥L) : MulAut V)) h1
    have ha2 : (a : MulAut V) ^ 2 = 1 := hAel.2 _ a.2
    have ha1 : a = 1 := Subtype.ext (by
      calc (a : MulAut V) = (a : MulAut V) ^ 3 * ((a : MulAut V) ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, ha2, inv_one, mul_one])
    have hfa : fA a = 1 := by rw [ha1, map_one]
    exact hb1 (Subtype.ext hfa)
  have hU' : ∀ u : ↥U, u * u = 1 := fun u =>
    Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, hV]; rfl)
  obtain ⟨hBN, -, ⟨sec⟩⟩ := Layer.Actor.irreducibleSectionProp (↥U) hU' HU LU BU hLcomp hB hLB
  have := sec.nontrivial
  set ψ : ↥L →* ↥(sec.τW.comp (Subgroup.inclusion le_sup_left)).range :=
    (sec.τW.comp (Subgroup.inclusion le_sup_left)).rangeRestrict.comp fL.rangeRestrict
  have hψs : Function.Surjective ψ :=
    (MonoidHom.rangeRestrict_surjective _).comp fL.rangeRestrict_surjective
  have hψz : ψ zL ≠ 1 := by
    intro h1
    have hτ : sec.τW (Subgroup.inclusion le_sup_left (fL.rangeRestrict zL)) = 1 :=
      congrArg Subtype.val h1
    have hI := sec.injective_image _ (fun w => by rw [hτ]; rfl)
    obtain ⟨w, hw⟩ := exists_ne (1 : sec.W)
    obtain ⟨v, rfl⟩ := sec.π_surjective w
    have hv1 : v ≠ 1 := fun h => hw (by rw [h, map_one])
    have hvfix := congrArg (fun x : ↥sec.I => ((x : ↥U) : V)) (hI v)
    simp only [sec.τI_apply] at hvfix
    have hzv : z ((v : ↥U) : V) = ((v : ↥U) : V) := hvfix
    exact hv1 (Subtype.ext (Subtype.ext (hfp _ (v : ↥U).2 hzv)))
  have hZb : Subgroup.center ↥(sec.τW.comp (Subgroup.inclusion le_sup_left)).range ≠ ⊥ := by
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hall
    apply hψz
    apply hall
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := hψs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 zc.2 l]
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq ⟨zL, hψz⟩
  let eL := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hψs hker
  have hlt := CFSG.QuasithinUnique.Bridge.ThreeA7Excl.threeA7_core sec.W
    (Meierfrankenfeld.GeneralFF.irrSection_sq hU' sec) _ _ sec.lbar_quasisimple
    (Meierfrankenfeld.GeneralFF.irrSection_isIrrOn sec) ⟨eL.symm.trans e⟩ hZb
    (Meierfrankenfeld.GeneralFF.irrSection_range_le_normalizer sec hBN) sec.abar_ne_bot
    sec.abar_elem sec.abar_quadratic
  exact absurd sec.abar_offender (not_le.2 hlt)

end CFSG.HardMathSupport.Cooperstein.Coordinator
