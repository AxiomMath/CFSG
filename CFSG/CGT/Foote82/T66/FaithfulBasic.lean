module

public import CFSG.CGT.Foote82.T66.CitedL13
import CFSG.CGT.Foote82.Lemma61
import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.Basic

public section

namespace CFSG.CGT.Foote82.L13Aux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero' (x : V) : x + x = 0 := by
  have h2 : (2 : ZMod 2) • x = 0 := by
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_smul]
  rwa [two_smul] at h2

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem perfect_of_isQuasisimple {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hq.1)

theorem invariant_commSpace_top (L : Subgroup (GLV V)) : Invariant L (commSpace L ⊤) :=
  invariant_commSpace (fun _ hk' _ hk => L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk'))
    (invariant_top L)

@[expose] def kT (L : Subgroup (GLV V)) : Subgroup ↥L where
  carrier := {ℓ | ∀ w ∈ commSpace L ⊤, (ℓ : GLV V) w - w ∈ fixedSpace L}
  mul_mem' := fun {a b} ha hb w hw => by
    show (a : GLV V) ((b : GLV V) w) - w ∈ fixedSpace L
    have h1 : (a : GLV V) ((b : GLV V) w - w) = (b : GLV V) w - w := hb w hw a a.2
    have e : (a : GLV V) ((b : GLV V) w) - w = ((b : GLV V) w - w) + ((a : GLV V) w - w) := by
      rw [← h1, map_sub]
      abel
    rw [e]
    exact (fixedSpace L).add_mem (hb w hw) (ha w hw)
  one_mem' := fun w _ => by
    show (1 : GLV V) w - w ∈ fixedSpace L
    simp
  inv_mem' := fun {a} ha w hw => by
    show (a : GLV V).symm w - w ∈ fixedSpace L
    have hw' : (a : GLV V).symm w ∈ commSpace L ⊤ :=
      invariant_commSpace_top L _ (L.inv_mem a.2) w hw
    have h := ha _ hw'
    have e : (a : GLV V) ((a : GLV V).symm w) = w := LinearEquiv.apply_symm_apply _ w
    rw [e] at h
    have h' := (fixedSpace L).neg_mem h
    rwa [neg_sub] at h'

theorem kT_normal (L : Subgroup (GLV V)) : (kT L).Normal := by
  constructor
  intro n hn g w hw
  have hw' : (g : GLV V).symm w ∈ commSpace L ⊤ :=
    invariant_commSpace_top L _ (L.inv_mem g.2) w hw
  have h := hn _ hw'
  have e : ((g * n * g⁻¹ : ↥L) : GLV V) w - w =
      (g : GLV V) ((n : GLV V) ((g : GLV V).symm w) - (g : GLV V).symm w) := by
    show (g : GLV V) ((n : GLV V) ((g : GLV V).symm w)) - w = _
    rw [map_sub, LinearEquiv.apply_symm_apply]
  rw [e, h g g.2]
  exact h

theorem kT_ne_top {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L) (hirr : HasIrrTildeV L) :
    kT L ≠ ⊤ := by
  intro h
  obtain ⟨hlt, -⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  have hle : commSpace L (commSpace L ⊤) ≤ fixedSpace L := commSpace_le_iff.2 fun l hl u hu => by
    have hmem : (⟨l, hl⟩ : ↥L) ∈ kT L := h ▸ Subgroup.mem_top _
    exact hmem u hu
  rw [commSpace_commSpace_top_of_perfect hperf] at hle
  exact hlt.not_ge fun w hw => ⟨hle hw, hw⟩

theorem kT_le_center {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : HasIrrTildeV L) : kT L ≤ Subgroup.center ↥L :=
  (normal_eq_top_or_le_center hq (kT_normal L)).resolve_left
    (kT_ne_top (perfect_of_isQuasisimple hq) hirr)

section Kernel

variable {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L) (hcen : kT L ≤ Subgroup.center ↥L)
include hperf hcen

theorem kT_comm {z : ↥L} (hz : z ∈ kT L) (l : ↥L) (v : V) :
    (z : GLV V) ((l : GLV V) v) = (l : GLV V) ((z : GLV V) v) := by
  have h := Subgroup.mem_center_iff.1 (hcen hz) l
  have h' : (l : GLV V) * (z : GLV V) = (z : GLV V) * (l : GLV V) := congrArg Subtype.val h
  exact (congrArg (fun f : GLV V => f v) h').symm

theorem kT_fix {z : ↥L} (hz : z ∈ kT L) : ∀ u ∈ commSpace L ⊤, (z : GLV V) u = u := by
  have hle : commSpace L (commSpace L ⊤) ≤
      LinearMap.eqLocus ((z : GLV V) : V →ₗ[ZMod 2] V) LinearMap.id := by
    refine commSpace_le_iff.2 fun l hl u hu => ?_
    rw [LinearMap.mem_eqLocus]
    have e2 : l ((z : GLV V) u - u) = (z : GLV V) u - u := hz u hu l hl
    have e1 := kT_comm hperf hcen hz ⟨l, hl⟩ u
    show (z : GLV V) (l u - u) = l u - u
    rw [map_sub, e1]
    rw [map_sub] at e2
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact e2
  intro u hu
  rw [← commSpace_commSpace_top_of_perfect hperf] at hu
  exact hle hu

theorem kT_sub_mem {z : ↥L} (hz : z ∈ kT L) (v : V) : (z : GLV V) v - v ∈ fixedSpace L := by
  intro l hl
  have hlv : (z : GLV V) (l v - v) = l v - v :=
    kT_fix hperf hcen hz _ (sub_mem_commSpace hl Submodule.mem_top)
  have hc := kT_comm hperf hcen hz ⟨l, hl⟩ v
  show l ((z : GLV V) v - v) = (z : GLV V) v - v
  rw [map_sub, ← hc]
  rw [map_sub] at hlv
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact hlv

theorem kT_sq {z : ↥L} (hz : z ∈ kT L) : z ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hc : (z : GLV V) ((z : GLV V) v - v) = (z : GLV V) v - v :=
    kT_fix hperf hcen hz _ (sub_mem_commSpace z.2 Submodule.mem_top)
  show (z : GLV V) ((z : GLV V) v) = v
  rw [map_sub] at hc
  have e : (z : GLV V) ((z : GLV V) v) = ((z : GLV V) v - v) + (z : GLV V) v := by
    rw [← hc]
    abel
  rw [e]
  have h2 := add_self_eq_zero' ((z : GLV V) v - v)
  calc (z : GLV V) v - v + (z : GLV V) v
      = ((z : GLV V) v - v + ((z : GLV V) v - v)) + v := by abel
    _ = v := by rw [h2, zero_add]

theorem kT_isPGroup : IsPGroup 2 ↥(kT L) := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact kT_sq hperf hcen g.2)⟩

theorem faithfulTildeV_of_forall
    (h : ∀ v : V, ∃ u ∈ commSpace L ⊤, v - u ∈ fixedSpace L) : FaithfulTildeV L := by
  intro ℓ hℓ hw
  have hz : (⟨ℓ, hℓ⟩ : ↥L) ∈ kT L := hw
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, hvu⟩ := h v
  have h1 : ℓ u = u := kT_fix hperf hcen hz u hu
  have h2 : ℓ (v - u) = v - u := hvu ℓ hℓ
  rw [map_sub, h1, sub_left_inj] at h2
  exact h2

end Kernel

theorem fix_of_mem_commutator {L Y : Subgroup (GLV V)} (hY : Y ≤ L) {v : V}
    (hv : ∀ y ∈ Y, y v - v ∈ fixedSpace L) : ∀ x ∈ ⁅Y, Y⁆, x v = v := by
  have hle : ⁅Y, Y⁆ ≤ MulAction.stabilizer (GLV V) v := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [MulAction.mem_stabilizer_iff]
    have hga : g (g v - v) = g v - v := hv g hg g (hY hg)
    have hgb : g (h v - v) = h v - v := hv h hh g (hY hg)
    have hha : h (g v - v) = g v - v := hv g hg h (hY hh)
    have hginv : g.symm v = v - (g v - v) := by
      rw [LinearEquiv.symm_apply_eq, map_sub, hga]
      abel
    have hhinv : h.symm v = v - (h v - v) := by
      have hhb : h (h v - v) = h v - v := hv h hh h (hY hh)
      rw [LinearEquiv.symm_apply_eq, map_sub, hhb]
      abel
    have hgb' : g.symm (h v - v) = h v - v := by
      rw [LinearEquiv.symm_apply_eq, hgb]
    have hhb : h (h v - v) = h v - v := hv h hh h (hY hh)
    show g (h (g.symm (h.symm v))) = v
    have e1 : g.symm (h.symm v) = v - (g v - v) - (h v - v) := by
      rw [hhinv, map_sub g.symm v (h v - v), hginv, hgb']
    have e2 : h (v - (g v - v) - (h v - v)) = v - (g v - v) := by
      calc h (v - (g v - v) - (h v - v)) = h (v - (g v - v)) - h (h v - v) :=
            map_sub h _ _
        _ = (h v - h (g v - v)) - h (h v - v) := by rw [map_sub h v (g v - v)]
        _ = (h v - (g v - v)) - (h v - v) := by rw [hha, hhb]
        _ = v - (g v - v) := by abel
    have e3 : g (v - (g v - v)) = v := by
      rw [map_sub g v (g v - v), hga]
      abel
    rw [e1, e2, e3]
  exact fun x hx => MulAction.mem_stabilizer_iff.1 (hle hx)

section Witness

variable {X M : Type} [Group X] [AddCommGroup M] {L : Subgroup (GLV V)}

def cocy (β : ↥(commSpace L ⊤) →+ M) (v : V) (ℓ : ↥L) : M :=
  β ⟨(ℓ : GLV V) v - v, sub_mem_commSpace ℓ.2 Submodule.mem_top⟩

variable (α : ↥L →* X) (β : ↥(commSpace L ⊤) →+ M) (act : X → M → M)
  (hact : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
    β w' = act (α ℓ) (β w))
  (hker : ∀ w : ↥(commSpace L ⊤), β w = 0 ↔ (w : V) ∈ fixedSpace L)

include hact in
theorem cocy_mul (v : V) (ℓ m : ↥L) :
    cocy β v (ℓ * m) = cocy β v ℓ + act (α ℓ) (cocy β v m) := by
  have hw : (ℓ : GLV V) ((m : GLV V) v - v) ∈ commSpace L ⊤ :=
    invariant_commSpace_top L _ ℓ.2 _ (sub_mem_commSpace m.2 Submodule.mem_top)
  have h1 := hact ℓ ⟨(m : GLV V) v - v, sub_mem_commSpace m.2 Submodule.mem_top⟩
    ⟨(ℓ : GLV V) ((m : GLV V) v - v), hw⟩ rfl
  have e : (⟨((ℓ * m : ↥L) : GLV V) v - v, sub_mem_commSpace (ℓ * m).2 Submodule.mem_top⟩ :
      ↥(commSpace L ⊤)) = ⟨(ℓ : GLV V) ((m : GLV V) v - v), hw⟩ +
        ⟨(ℓ : GLV V) v - v, sub_mem_commSpace ℓ.2 Submodule.mem_top⟩ := by
    apply Subtype.ext
    show (ℓ : GLV V) ((m : GLV V) v) - v = (ℓ : GLV V) ((m : GLV V) v - v) + ((ℓ : GLV V) v - v)
    rw [map_sub]
    abel
  unfold cocy
  rw [e, map_add, h1, add_comm]

include hker in
theorem cocy_eq_zero_of_mem_kT (hperf : ⁅L, L⁆ = L) (hcen : kT L ≤ Subgroup.center ↥L) (v : V)
    {k : ↥L} (hk : k ∈ kT L) : cocy β v k = 0 :=
  (hker _).2 (kT_sub_mem hperf hcen hk v)

include hact hker in
theorem ker_le_kT (hact1 : ∀ a, act 1 a = a) : α.ker ≤ kT L := by
  intro k hk w hw
  have hw' : (k : GLV V) w ∈ commSpace L ⊤ := invariant_commSpace_top L _ k.2 w hw
  have h := hact k ⟨w, hw⟩ ⟨(k : GLV V) w, hw'⟩ rfl
  rw [MonoidHom.mem_ker.1 hk, hact1] at h
  have h0 : β (⟨(k : GLV V) w, hw'⟩ - ⟨w, hw⟩) = 0 := by rw [map_sub, h, sub_self]
  exact (hker _).1 h0

include hact hker in
theorem cocy_eq_of_map_eq (hperf : ⁅L, L⁆ = L) (hcen : kT L ≤ Subgroup.center ↥L)
    (hact1 : ∀ a, act 1 a = a) (hact0 : ∀ x, act x 0 = 0) (v : V) {ℓ ℓ' : ↥L}
    (h : α ℓ = α ℓ') : cocy β v ℓ = cocy β v ℓ' := by
  have hk : ℓ⁻¹ * ℓ' ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h0 := cocy_eq_zero_of_mem_kT β hker hperf hcen v
    (ker_le_kT α β act hact hker hact1 hk)
  have e := cocy_mul α β act hact v ℓ (ℓ⁻¹ * ℓ')
  rw [mul_inv_cancel_left, h0, hact0, add_zero] at e
  exact e.symm

include hact hker in
theorem exists_sub_mem_of_cobound (hβ : Function.Surjective β) (v : V) (Y : Subgroup ↥L)
    (m : M) (hm : ∀ ℓ ∈ Y, cocy β v ℓ = act (α ℓ) m - m) :
    ∃ u ∈ commSpace L ⊤, ∀ ℓ ∈ Y, (ℓ : GLV V) (v - u) - (v - u) ∈ fixedSpace L := by
  obtain ⟨u₀, rfl⟩ := hβ m
  refine ⟨u₀, u₀.2, fun ℓ hℓ => ?_⟩
  have hw' : (ℓ : GLV V) u₀ ∈ commSpace L ⊤ := invariant_commSpace_top L _ ℓ.2 _ u₀.2
  have h1 := hact ℓ u₀ ⟨(ℓ : GLV V) u₀, hw'⟩ rfl
  have h0 : β (⟨(ℓ : GLV V) v - v, sub_mem_commSpace ℓ.2 Submodule.mem_top⟩ -
      (⟨(ℓ : GLV V) u₀, hw'⟩ - u₀)) = 0 := by
    rw [map_sub, map_sub, h1]
    have := hm ℓ hℓ
    unfold cocy at this
    rw [this, sub_self]
  have h2 := (hker _).1 h0
  have e : (((⟨(ℓ : GLV V) v - v, sub_mem_commSpace ℓ.2 Submodule.mem_top⟩ -
      (⟨(ℓ : GLV V) u₀, hw'⟩ - u₀) : ↥(commSpace L ⊤))) : V) =
      (ℓ : GLV V) (v - u₀) - (v - u₀) := by
    show (ℓ : GLV V) v - v - ((ℓ : GLV V) u₀ - u₀) = _
    rw [map_sub]
    abel
  rw [e] at h2
  exact h2

include hact hker in
theorem forall_exists_of_h1 (hperf : ⁅L, L⁆ = L) (hcen : kT L ≤ Subgroup.center ↥L)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) (hact1 : ∀ a, act 1 a = a)
    (hact0 : ∀ x, act x 0 = 0) (h1 : H1Zero X M act) :
    ∀ v : V, ∃ u ∈ commSpace L ⊤, v - u ∈ fixedSpace L := by
  intro v
  set s := Function.surjInv hα
  have hs : ∀ x, α (s x) = x := Function.surjInv_eq hα
  have hcoc : ∀ {ℓ ℓ' : ↥L}, α ℓ = α ℓ' → cocy β v ℓ = cocy β v ℓ' := fun h =>
    cocy_eq_of_map_eq α β act hact hker hperf hcen hact1 hact0 v h
  obtain ⟨a, ha⟩ := h1 (fun x => cocy β v (s x)) fun x y => by
    have e : α (s (x * y)) = α (s x * s y) := by rw [hs, map_mul, hs, hs]
    show cocy β v (s (x * y)) = cocy β v (s x) + act x (cocy β v (s y))
    rw [hcoc e, cocy_mul α β act hact v, hs]
  obtain ⟨u, hu, hY⟩ := exists_sub_mem_of_cobound α β act hact hker hβ v ⊤ a
    fun ℓ _ => by
      have e : α (s (α ℓ)) = α ℓ := hs _
      rw [← hcoc e]
      exact ha (α ℓ)
  refine ⟨u, hu, ?_⟩
  have hfix := fix_of_mem_commutator (L := L) (Y := L) le_rfl
    (v := v - u) fun y hy => hY ⟨y, hy⟩ (Subgroup.mem_top _)
  rw [hperf] at hfix
  exact hfix

include hact hker in
theorem faithfulTildeV_of_h1 (hq : CFSG.Open.IsQuasisimple ↥L) (hirr : HasIrrTildeV L)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) (hact1 : ∀ a, act 1 a = a)
    (hact0 : ∀ x, act x 0 = 0) (h1 : H1Zero X M act) : FaithfulTildeV L :=
  faithfulTildeV_of_forall (perfect_of_isQuasisimple hq) (kT_le_center hq hirr)
    (forall_exists_of_h1 α β act hact hker (perfect_of_isQuasisimple hq)
      (kT_le_center hq hirr) hα hβ hact1 hact0 h1)

end Witness

theorem ker_iff_of_eq {M : Type} [AddCommGroup M] {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ M}
    (hβk : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (w : ↥(commSpace L ⊤)) : β w = 0 ↔ (w : V) ∈ fixedSpace L := by
  rw [← AddMonoidHom.mem_ker, hβk]
  rfl

theorem faithfulTildeV_of_omegaMinus {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : HasIrrTildeV L) {m : ℕ} (hO : IsOmegaMinusModule L m)
    (h1 : H1Zero ↥(omegaMinusTwo m) (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) fun g a =>
      ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a) :
    FaithfulTildeV L := by
  obtain ⟨α, hα, β, hβ, hβk, hR⟩ := hO
  exact faithfulTildeV_of_h1 α β _ (fun ℓ w w' h => hR ℓ w w' h) (ker_iff_of_eq hβk) hq hirr
    hα hβ (fun a => by simp) (fun x => Matrix.mulVec_zero _) h1

end CFSG.CGT.Foote82.L13Aux
