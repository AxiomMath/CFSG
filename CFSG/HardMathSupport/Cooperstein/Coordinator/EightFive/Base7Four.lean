module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleChief
import CFSG.Quasithin.SteinbergCBI16A7
public import CFSG.Quasithin.Background.B1MoreQuot
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V]

theorem inf_fixV_eq_bot_of_transfer {G : Type*} [Group G] [Finite G] {L : Subgroup (MulAut V)}
    (ρ : G →* ↥L) (hρ : Function.Surjective ρ) (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
    (hU : L ≤ stabSub U) (hUL : commSub U L = U) {K : Subgroup G} (hK : Odd K.index)
    (p : V →* V) (hpZ : ∀ z ∈ U ⊓ fixV L, p z = z)
    (hpK : ∀ k ∈ K, ∀ u ∈ U, p ((ρ k : MulAut V) u) = p u) : U ⊓ fixV L = ⊥ := by
  classical
  have : Fintype (G ⧸ K) := Fintype.ofFinite _
  have hmemU : ∀ g : G, ∀ u ∈ U, (ρ g : MulAut V) u ∈ U := fun g u hu => (hU (ρ g).2 u).2 hu
  let F : (G ⧸ K) → V →* V := fun c => p.comp ((ρ (c.out)⁻¹ : MulAut V) : V ≃* V).toMonoidHom
  let P : V →* V := ∏ c : G ⧸ K, F c
  have hP : ∀ v, P v = ∏ c : G ⧸ K, p ((ρ (c.out)⁻¹ : MulAut V) v) := fun v => by
    simp only [P, MonoidHom.finsetProd_apply, F, MonoidHom.comp_apply]
    rfl
  have hPg : ∀ g : G, ∀ u ∈ U, P ((ρ g : MulAut V) u) = P u := by
    intro g u hu
    rw [hP, hP]
    have hc : ∀ c : G ⧸ K, p ((ρ (c.out)⁻¹ : MulAut V) ((ρ g : MulAut V) u)) =
        p ((ρ ((g⁻¹ • c).out)⁻¹ : MulAut V) u) := by
      intro c
      have hk : ((g⁻¹ • c).out)⁻¹ * (g⁻¹ * c.out) ∈ K := by
        apply QuotientGroup.eq.1
        rw [QuotientGroup.out_eq']
        calc g⁻¹ • c = g⁻¹ • ((c.out : G) : G ⧸ K) := by rw [QuotientGroup.out_eq']
          _ = ((g⁻¹ * c.out : G) : G ⧸ K) := rfl
      have hkk : (c.out)⁻¹ * g =
          (((g⁻¹ • c).out)⁻¹ * (g⁻¹ * c.out))⁻¹ * ((g⁻¹ • c).out)⁻¹ := by
        simp only [mul_inv_rev, inv_inv]
        group
      have h1 : (ρ (c.out)⁻¹ : MulAut V) ((ρ g : MulAut V) u) =
          (ρ ((c.out)⁻¹ * g) : MulAut V) u := by
        rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
      have h2 : (ρ ((c.out)⁻¹ * g) : MulAut V) u =
          (ρ (((g⁻¹ • c).out)⁻¹ * (g⁻¹ * c.out))⁻¹ : MulAut V)
            ((ρ ((g⁻¹ • c).out)⁻¹ : MulAut V) u) := by
        rw [hkk, map_mul, Subgroup.coe_mul, MulAut.mul_apply]
      rw [h1, h2]
      exact hpK _ (K.inv_mem hk) _ (hmemU _ u hu)
    rw [Finset.prod_congr rfl (fun c _ => hc c)]
    exact Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ (fun c => rfl)
  have hPz : ∀ z ∈ U ⊓ fixV L, P z = z := by
    intro z hz
    rw [hP]
    have h1 : ∀ c : G ⧸ K, p ((ρ (c.out)⁻¹ : MulAut V) z) = z := fun c => by
      rw [hz.2 _ (ρ _).2, hpZ z hz]
    rw [Finset.prod_congr rfl (fun c _ => h1 c), Finset.prod_const, Finset.card_univ]
    have hcard : Fintype.card (G ⧸ K) = K.index := by
      rw [Subgroup.index, Nat.card_eq_fintype_card]
    rw [hcard]
    obtain ⟨m, hm⟩ := hK
    rw [hm, pow_succ, pow_mul, hV, one_pow, one_mul]
  have hker : U ≤ P.ker := by
    rw [← hUL, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨g, hg⟩ := hρ ⟨x, hx⟩
    have hxg : x = (ρ g : MulAut V) := by rw [hg]
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hxg, hPg g w hw, mul_inv_cancel]
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← hPz z hz]
  exact hker hz.1

open SteinbergCB.I16 Matrix in
private theorem mem_fixV_of_tA [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (ι : alternatingGroup (Fin 7) ≃* ↥L) {U : Subgroup V} (hU : L ≤ stabSub U)
    (hUL : commSub U L = U) (hidx : (fixV L).relIndex U = 2 ^ 4) {u : V} (hu : u ∈ U)
    (htu : (ι tA : MulAut V) u * u⁻¹ ∈ fixV L) : u ∈ fixV L := by
  classical
  have hstab : ∀ l : ↥L, (resHom U).comp (Subgroup.inclusion hU) l ∈
      stabSub ((fixV L).subgroupOf U) := by
    intro l w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact le_stabSub_fixV (Subgroup.le_normalizer) l.2 w
  let act : ↥L →* MulAut (Sec U (fixV L)) := (quotHom ((fixV L).subgroupOf U)).comp
    (((resHom U).comp (Subgroup.inclusion hU)).codRestrict _ hstab)
  have hact : ∀ (l : ↥L) (w : ↥U), act l (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨(l : MulAut V) w, (hU l.2 w).2 w.2⟩ := fun _ _ => rfl
  have hmk : ∀ a b : ↥U, (QuotientGroup.mk a : Sec U (fixV L)) = QuotientGroup.mk b ↔
      (a : V) * (b : V)⁻¹ ∈ fixV L := fun a b => by
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv, Subgroup.mem_subgroupOf]
    rfl
  have hXcard : Nat.card (Sec U (fixV L)) = 2 ^ 4 := hidx
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := Sec U (fixV L)) (fun a b => mul_comm a b) (fun a => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
      rw [← QuotientGroup.mk_pow]
      have hw : w ^ 2 = 1 := Subtype.ext (hV w)
      rw [hw, QuotientGroup.mk_one]) hXcard
  let M : alternatingGroup (Fin 7) →* GL (Fin 4) (ZMod 2) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (act.comp ι.toMonoidHom)
  have hM : ∀ (σ : alternatingGroup (Fin 7)) (x : Sec U (fixV L)),
      ((M σ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ Multiplicative.toAdd (e x) =
        Multiplicative.toAdd (e (act (ι σ) x)) := fun σ x =>
    CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e _ x
  have hMinj : Function.Injective M := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    rcases (MonoidHom.normal_ker M).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff M).1 h
    · exfalso
      have htriv : ∀ l ∈ L, ∀ w ∈ U, l w * w⁻¹ ∈ fixV L := by
        intro l hl w hw
        obtain ⟨σ, hσ⟩ := ι.surjective ⟨l, hl⟩
        have h1 : M σ = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top σ)
        have h2 : act (ι σ) = 1 :=
          (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective (by rw [map_one]; exact h1)
        have h3 := congrArg (fun φ : MulAut (Sec U (fixV L)) => φ (QuotientGroup.mk ⟨w, hw⟩)) h2
        simp only [hact, MulAut.one_apply] at h3
        rw [hσ] at h3
        exact (hmk _ _).1 h3
      have hle : U ≤ fixV L := by
        rw [← hUL, commSub, Subgroup.closure_le]
        rintro _ ⟨x, hx, w, hw, rfl⟩
        exact htriv x hx w hw
      have h1 := (Subgroup.relIndex_eq_one).2 hle
      rw [hidx] at h1
      norm_num at h1
  obtain ⟨ht3, ht1, hv1, hv2, htv1, htv2, hvv, hv1n, hv2n, hv12⟩ := relations_A7
  have hmat : ∀ a b : alternatingGroup (Fin 7), a * b = b * a →
      (M a : Mat4) * (M b : Mat4) = (M b : Mat4) * (M a : Mat4) := by
    intro a b hab
    rw [← Units.val_mul, ← map_mul, hab, map_mul, Units.val_mul]
  have hne : ∀ a b : alternatingGroup (Fin 7), a ≠ b → (M a : Mat4) ≠ (M b : Mat4) :=
    fun a b hab h => hab (hMinj (Units.ext h))
  have hsq : ∀ a : alternatingGroup (Fin 7), a * a = 1 → (M a : Mat4) * (M a : Mat4) = 1 :=
    fun a ha => by rw [← Units.val_mul, ← map_mul, ha, map_one, Units.val_one]
  have hne1 : ∀ a : alternatingGroup (Fin 7), a ≠ 1 → (M a : Mat4) ≠ 1 := fun a ha h =>
    hne a 1 ha (by rw [h, map_one, Units.val_one])
  have hx3 : (M tA : Mat4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ht3, map_one, Units.val_one]
  have hfp : ∀ v, (M tA : Mat4) *ᵥ v = v → v = 0 := fun v hv =>
    fixed_eq_zero_of_fourGroup hx3 (hne1 _ ht1) (hsq _ hv1) (hsq _ hv2) (hmat _ _ htv1)
      (hmat _ _ htv2) (hmat _ _ hvv) (hne1 _ hv1n) (hne1 _ hv2n) (hne _ _ hv12) hv
  have hfixX : act (ι tA) (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩ := by
    rw [hact]
    exact (hmk _ _).2 htu
  have h1 := hM tA (QuotientGroup.mk ⟨u, hu⟩)
  rw [hfixX] at h1
  have h2 : e (QuotientGroup.mk ⟨u, hu⟩) = 1 :=
    Multiplicative.toAdd.injective ((hfp _ h1).trans toAdd_one.symm)
  have h3 : (QuotientGroup.mk ⟨u, hu⟩ : Sec U (fixV L)) = 1 :=
    e.injective (h2.trans (map_one e).symm)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

open SteinbergCB.I16 in
theorem inf_fixV_eq_bot_of_relIndex [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hL : Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    {U : Subgroup V} (hU : L ≤ stabSub U) (hUL : commSub U L = U)
    (hidx : (fixV L).relIndex U = 2 ^ 4) : U ⊓ fixV L = ⊥ := by
  obtain ⟨ι'⟩ := hL
  set ι : alternatingGroup (Fin 7) ≃* ↥L := ι'.symm with hι
  set t : MulAut V := (ι tA : MulAut V) with ht
  have ht3 : ∀ v, t (t (t v)) = v := by
    intro v
    have h1 : (ι tA) ^ 3 = 1 := by rw [← map_pow, relations_A7.1, map_one]
    have h2 : t ^ 3 = 1 := by rw [ht, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have h3 := congrArg (fun φ : MulAut V => φ v) h2
    simpa [pow_succ, MulAut.mul_apply] using h3
  have hUt : ∀ w ∈ U, t w ∈ U := fun w hw => (hU (ι tA).2 w).2 hw
  let p : V →* V :=
    { toFun := fun v => v * t v * t (t v)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        simp only [mul_comm, mul_left_comm, mul_assoc] }
  have hp : ∀ v, p v = v * t v * t (t v) := fun _ => rfl
  have hpfix : ∀ u ∈ U, p u ∈ fixV L := by
    intro u hu
    have hpu : p u ∈ U := by
      rw [hp]
      exact U.mul_mem (U.mul_mem hu (hUt u hu)) (hUt _ (hUt u hu))
    refine mem_fixV_of_tA hV ι hU hUL hidx hpu ?_
    have htp : t (p u) = p u := by
      rw [hp, map_mul, map_mul, ht3]
      simp only [mul_comm, mul_left_comm]
    rw [← ht, htp, mul_inv_cancel]
    exact one_mem _
  refine inf_fixV_eq_bot_of_transfer ι.toMonoidHom ι.surjective hV hU hUL (K := L7)
    (by rw [index_L7]; decide) p (fun z hz => ?_) (fun k hk u hu => ?_)
  · rw [hp, hz.2 t (ι tA).2, hz.2 t (ι tA).2, ← pow_two, hV, one_mul]
  ·
    have hk' : (ι k : MulAut V) (p u) = p u := hpfix u hu _ (ι k).2
    change p ((ι k : MulAut V) u) = p u
    rw [← hk']
    have hA : k * tA * k⁻¹ = tA ∨ k * tA * k⁻¹ = tA⁻¹ := by
      rcases conj_tP hk with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have hmulι : ∀ a b : alternatingGroup (Fin 7), ∀ v,
        (ι (a * b) : MulAut V) v = (ι a : MulAut V) ((ι b : MulAut V) v) := fun a b v => by
      rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
    rcases hA with h | h
    ·
      have hc : ∀ v, (ι k : MulAut V) (t v) = t ((ι k : MulAut V) v) := by
        intro v
        have hkt : k * tA = tA * k := by
          calc k * tA = k * tA * k⁻¹ * k := by group
            _ = tA * k := by rw [h]
        rw [ht, ← hmulι, hkt, hmulι]
      rw [hp, hp, map_mul, map_mul, ← hc u, ← hc (t u)]
    ·
      have hc : ∀ v, (ι k : MulAut V) (t v) = t (t ((ι k : MulAut V) v)) := by
        intro v
        have hkt : k * tA = tA⁻¹ * k := by
          calc k * tA = k * tA * k⁻¹ * k := by group
            _ = tA⁻¹ * k := by rw [h]
        have hinv : ∀ w, (ι tA⁻¹ : MulAut V) w = t (t w) := fun w => by
          have h1 : (ι tA⁻¹ : MulAut V) = t⁻¹ := by
            rw [ht, map_inv, Subgroup.coe_inv]
          rw [h1]
          conv_lhs => rw [← ht3 (t⁻¹ w)]
          rw [MulAut.apply_inv_self]
        rw [ht, ← hmulι, hkt, hmulι, hinv]
      have hc2 : ∀ v, (ι k : MulAut V) (t (t v)) = t ((ι k : MulAut V) v) := by
        intro v
        rw [hc, hc, ht3]
      rw [hp, hp, map_mul, map_mul, hc u, hc2 u]
      exact mul_right_comm _ _ _

theorem card_commV_of_relIndex [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hL : Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    (hidx : (fixV L).relIndex (commV L) = 2 ^ 4) : Nat.card (commV L) = 2 ^ 4 := by
  have hperf : commutator ↥L = ⊤ := by
    obtain ⟨ι⟩ := hL
    have : Group.IsPerfect (alternatingGroup (Fin 7)) :=
      ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)⟩
    exact (Group.IsPerfect.ofSurjective (f := ι.symm.toMonoidHom) ι.symm.surjective).commutator_eq_top
  have hbot := inf_fixV_eq_bot_of_relIndex hV hL (le_stabSub_commV Subgroup.le_normalizer)
    (commSub_commV_of_perfect hperf) hidx
  have h := Subgroup.relIndex_mul_card (H := fixV L) (K := commV L)
  rw [inf_comm, hbot, Subgroup.card_bot, mul_one, hidx] at h
  exact h.symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
