module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24Sufficient
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerNative

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open CFSG.Blueprint.Fischer CFSG.Fischer Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def tClass (t : G) : Set G := {g | IsConj t g}

theorem self_mem_tClass (t : G) : t ∈ tClass t := IsConj.refl t

theorem conj_mem_tClass {t x : G} (g : G) (hx : x ∈ tClass t) : g * x * g⁻¹ ∈ tClass t :=
  IsConj.trans hx (isConj_iff.2 ⟨g, rfl⟩)

theorem tClass_inv (t : G) : ∀ g : G, ∀ x ∈ tClass t, g * x * g⁻¹ ∈ tClass t :=
  fun g _ hx => conj_mem_tClass g hx

theorem orderOf_of_mem_tClass {t x : G} (ht : orderOf t = 2) (hx : x ∈ tClass t) :
    orderOf x = 2 := by
  obtain ⟨c, hc⟩ := hx
  rw [← SemiconjBy.orderOf_eq _ hc, ht]

theorem mul_self_of_mem_tClass {t x : G} (ht : orderOf t = 2) (hx : x ∈ tClass t) :
    x * x = 1 :=
  ThreeTransposition.mul_self_of_orderOf (orderOf_of_mem_tClass ht hx)

open CFSG.EvenSmallLie.UnitarySix.ToddOrbit in
structure FischerHyp
    (t : G)
    (L E : Subgroup G) (p : L →* Equiv.Perm (Fin 693)) : Prop where
  todd : ToddOrbit.Hyp t L E p
  centralizer_eq : centralizer {t} = L
  tv : ∀ s (hs : s ∈ L), IsConj t s → s ≠ t → ∃ m, p ⟨s, hs⟩ = tvP m
  inj : ∀ s s' (hs : s ∈ L) (hs' : s' ∈ L), IsConj t s → IsConj t s' → s ≠ t → s' ≠ t →
    p ⟨s, hs⟩ = p ⟨s', hs'⟩ → s = s'
  m22 : ∃ f : ToddOrbit.orb E t ≃ Fin 22, ∀ σ : Equiv.Perm (Fin 22),
    σ ∈ CFSG.Blueprint.NativeSporadic.M22 ↔ ∃ n ∈ normalizer (E : Set G),
      ∀ s : ToddOrbit.orb E t, (f.symm (σ (f s)) : G) = n * s * n⁻¹
  ker : ∀ n ∈ normalizer (E : Set G), (∀ s ∈ ToddOrbit.orb E t, n * s * n⁻¹ = s) → n ∈ E
  card_sylow : ∀ P : Sylow 2 G, Nat.card P = 2 ^ 17
  card_sylowN : ∀ P : Sylow 2 (normalizer (E : Set G)), Nat.card P = 2 ^ 17

namespace FischerHyp

variable {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

theorem orderOf_t
    (h : FischerHyp t L E p) : orderOf t = 2 := h.todd.orderOf_t

theorem mem_L
    (h : FischerHyp t L E p) {s : G} (hs : s ∈ LocalClass (tClass t) t) : s ∈ L := by
  rw [← h.centralizer_eq]
  exact mem_centralizer_singleton_iff.2 hs.2.2

theorem commute_t
    (h : FischerHyp t L E p) {y : G} (hy : y ∈ L) : y * t = t * y := by
  rw [← h.centralizer_eq] at hy
  exact mem_centralizer_singleton_iff.1 hy

theorem E_comm
    (h : FischerHyp t L E p) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  have hx2 : x * x = 1 := by rw [← sq]; exact h.todd.E_sq x hx
  have hy2 : y * y = 1 := by rw [← sq]; exact h.todd.E_sq y hy
  have hxy : x * y * (x * y) = 1 := by rw [← sq]; exact h.todd.E_sq _ (mul_mem hx hy)
  calc x * y = x * y * (x * y) * (y * x) := by
        rw [show x * y * (x * y) * (y * x) = x * y * x * (y * y) * x by group, hy2, mul_one,
          mul_assoc, hx2, mul_one]
    _ = y * x := by rw [hxy, one_mul]

theorem conj_mem_localClass_t
    (h : FischerHyp t L E p) {s y : G}
    (hs : s ∈ LocalClass (tClass t) t) (hy : y ∈ L) : y * s * y⁻¹ ∈ LocalClass (tClass t) t := by
  have hyt : y * t * y⁻¹ = t := by rw [h.commute_t hy, mul_inv_cancel_right]
  have := ThreeTransposition.conj_mem_localClass (tClass_inv t) y hs
  rwa [hyt] at this

@[expose] noncomputable def pt
    (h : FischerHyp t L E p) (s : LocalClass (tClass t) t) :
    Fin 693 :=
  Classical.choose (h.tv s (h.mem_L s.2) s.2.1 s.2.2.1)

theorem p_pt
    (h : FischerHyp t L E p) (s : LocalClass (tClass t) t) :
    p ⟨s, h.mem_L s.2⟩ = tvP (h.pt s) :=
  Classical.choose_spec (h.tv s (h.mem_L s.2) s.2.1 s.2.2.1)

theorem p_eq_tvP_iff
    (h : FischerHyp t L E p) (s : LocalClass (tClass t) t) (m : Fin 693) :
    p ⟨s, h.mem_L s.2⟩ = tvP m ↔ h.pt s = m := by
  rw [h.p_pt]
  exact tvP_injective.eq_iff

theorem pt_injective
    (h : FischerHyp t L E p) : Function.Injective h.pt := by
  intro s s' hss'
  have he : p ⟨s, h.mem_L s.2⟩ = p ⟨s', h.mem_L s'.2⟩ := by rw [h.p_pt, h.p_pt, hss']
  exact Subtype.ext (h.inj s s' _ _ s.2.1 s'.2.1 s.2.2.1 s'.2.2.1 he)

theorem exists_mem_localClass
    (h : FischerHyp t L E p) : ∃ s, s ∈ LocalClass (tClass t) t := by
  obtain ⟨n, hn, hne⟩ := h.todd.move
  have hsE : n⁻¹ * t * n ∈ E := ToddOrbit.orb_subset h.todd.t_mem_E ⟨n, hn, rfl⟩
  exact ⟨n⁻¹ * t * n, isConj_iff.2 ⟨n⁻¹, by group⟩, hne, h.E_comm _ hsE t h.todd.t_mem_E⟩

theorem pt_surjective
    (h : FischerHyp t L E p) : Function.Surjective h.pt := by
  intro m
  obtain ⟨s₀, hs₀⟩ := h.exists_mem_localClass
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T46 (h.pt ⟨s₀, hs₀⟩) m
  obtain ⟨y, hy⟩ := h.todd.surj g g.2
  have hmem := h.conj_mem_localClass_t hs₀ y.2
  refine ⟨⟨_, hmem⟩, (h.p_eq_tvP_iff ⟨_, hmem⟩ m).1 ?_⟩
  have e : (⟨(y : G) * s₀ * (y : G)⁻¹, h.mem_L hmem⟩ : L) = y * ⟨s₀, h.mem_L hs₀⟩ * y⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hy, h.p_pt ⟨s₀, hs₀⟩,
    (isPolarAut_of_mem g.2).mul_tvP_mul_inv, ← hg]
  rfl

theorem comm_iff
    (h : FischerHyp t L E p) (f g : LocalClass (tClass t) t) :
    (f : G) * g = g * f ↔ perp (h.pt f) (h.pt g) := by
  rw [← tvP_comm_iff_perp, ← h.p_pt f, ← h.p_pt g, ← map_mul, ← map_mul]
  constructor
  · intro hfg
    exact congrArg p (Subtype.ext hfg)
  · intro hp
    have hmem := h.conj_mem_localClass_t g.2 (h.mem_L f.2)
    have e : (⟨(f : G) * g * (f : G)⁻¹, h.mem_L hmem⟩ : L) =
        ⟨f, h.mem_L f.2⟩ * ⟨g, h.mem_L g.2⟩ * ⟨f, h.mem_L f.2⟩⁻¹ := rfl
    have hpe : p ⟨(f : G) * g * (f : G)⁻¹, h.mem_L hmem⟩ = p ⟨g, h.mem_L g.2⟩ := by
      rw [e, map_mul, hp, map_mul, map_inv, mul_inv_cancel_right]
    have := h.inj _ g _ (h.mem_L g.2) hmem.1 g.2.1 hmem.2.1 g.2.2.1 hpe
    calc (f : G) * g = (f : G) * g * (f : G)⁻¹ * f := by group
      _ = g * f := by rw [this]

theorem pt_tau
    (h : FischerHyp t L E p) (f g : LocalClass (tClass t) t)
    (hfg : (f : G) * g * f ∈ LocalClass (tClass t) t) :
    h.pt ⟨_, hfg⟩ = tvP (h.pt f) (h.pt g) := by
  rw [← h.p_eq_tvP_iff ⟨_, hfg⟩]
  have e : (⟨(f : G) * g * f, h.mem_L hfg⟩ : L) =
      ⟨f, h.mem_L f.2⟩ * ⟨g, h.mem_L g.2⟩ * ⟨f, h.mem_L f.2⟩ := rfl
  rw [e, map_mul, map_mul, h.p_pt f, h.p_pt g, tvP_conj]

@[expose] noncomputable def localPoints
    (h : FischerHyp t L E p) :
    LocalPoints polarModel (tClass t) t where
  χ := Equiv.ofBijective h.pt ⟨h.pt_injective, h.pt_surjective⟩
  comm f g := h.comm_iff f g
  tau f g hfg := h.pt_tau f g hfg

end FischerHyp

section Conj

variable {D : Set G} (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D)
include hDinv

theorem conj_mem_localClass_iff (g : G) {d f : G} :
    g * f * g⁻¹ ∈ LocalClass D (g * d * g⁻¹) ↔ f ∈ LocalClass D d := by
  refine ⟨fun hf => ?_, ThreeTransposition.conj_mem_localClass hDinv g⟩
  have := ThreeTransposition.conj_mem_localClass hDinv g⁻¹ hf
  rwa [show g⁻¹ * (g * f * g⁻¹) * g⁻¹⁻¹ = f by group,
    show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group] at this

@[expose] def conjStarInv (g d : G) : LocalClass D d ≃ LocalClass D (g * d * g⁻¹) where
  toFun f := ⟨g * f * g⁻¹, (conj_mem_localClass_iff hDinv g).2 f.2⟩
  invFun f := ⟨g⁻¹ * f * g, by
    have := (conj_mem_localClass_iff hDinv g⁻¹ (d := g * d * g⁻¹) (f := (f : G))).2 f.2
    rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group, inv_inv] at this⟩
  left_inv f := Subtype.ext (by show g⁻¹ * (g * (f : G) * g⁻¹) * g = f; group)
  right_inv f := Subtype.ext (by show g * (g⁻¹ * (f : G) * g) * g⁻¹ = f; group)

theorem conjStarInv_symm_val (g d : G) (f : LocalClass D (g * d * g⁻¹)) :
    ((conjStarInv hDinv g d).symm f : G) = g⁻¹ * f * g := rfl

@[expose] noncomputable def localPointsConj {P : Type} {M : LocalModel P} {d : G}
    (L : LocalPoints M D d) (g : G) : LocalPoints M D (g * d * g⁻¹) where
  χ := (conjStarInv hDinv g d).symm.trans L.χ
  comm f f' := by
    rw [Equiv.trans_apply, Equiv.trans_apply, ← L.comm, conjStarInv_symm_val,
      conjStarInv_symm_val,
      show g⁻¹ * (f : G) * g * (g⁻¹ * f' * g) = g⁻¹ * (f * f') * g by group,
      show g⁻¹ * (f' : G) * g * (g⁻¹ * f * g) = g⁻¹ * (f' * f) * g by group]
    exact ⟨fun h => by rw [h], fun h => mul_left_cancel (mul_right_cancel h)⟩
  tau f f' hff := by
    have h' : ((conjStarInv hDinv g d).symm f : G) * (conjStarInv hDinv g d).symm f' *
        (conjStarInv hDinv g d).symm f ∈ LocalClass D d := by
      rw [conjStarInv_symm_val, conjStarInv_symm_val,
        show g⁻¹ * (f : G) * g * (g⁻¹ * f' * g) * (g⁻¹ * f * g) = g⁻¹ * (f * f' * f) * g⁻¹⁻¹
          by group]
      have := (conj_mem_localClass_iff hDinv g⁻¹ (d := g * d * g⁻¹)).2 hff
      rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group] at this
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, ← L.tau _ _ h']
    congr 1
    apply Subtype.ext
    show g⁻¹ * ((f : G) * f' * f) * g = g⁻¹ * f * g * (g⁻¹ * f' * g) * (g⁻¹ * f * g)
    group

end Conj

theorem FischerHyp.nonempty_localPoints
    {t : G} {L E : Subgroup G}
    {p : L →* Equiv.Perm (Fin 693)} (h : FischerHyp t L E p) :
    ∀ x ∈ tClass t, Nonempty (LocalPoints polarModel (tClass t) x) := by
  intro x hx
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  exact ⟨localPointsConj (tClass_inv t) h.localPoints g⟩

section LocalGroup

variable {D : Set G} (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, x * x = 1)
include hDinv hD2

theorem mul_mul_mem_localClass {d e x : G} (he : e ∈ LocalClass D d) (hx : x ∈ LocalClass D d) :
    e * x * e ∈ LocalClass D d := by
  have hee : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hD2 e he.1)
  have h := ThreeTransposition.conj_mem_localClass hDinv e hx
  rwa [hee, show e * d * e = d by rw [he.2.2, mul_assoc, hD2 e he.1, mul_one]] at h

theorem exists_conj_eq_of_localPoints
    {d : G} (Lp : LocalPoints polarModel D d)
    (f f' : LocalClass D d) : ∃ g ∈ LocalGroup D d, g * f * g⁻¹ = f' := by
  set S : Set (Fin 693) := {m | ∃ g ∈ LocalGroup D d, g * f * g⁻¹ = Lp.χ.symm m} with hS
  have hstep : ∀ q m, m ∈ S → tvP q m ∈ S := by
    rintro q m ⟨g, hg, hgm⟩
    set e := Lp.χ.symm q
    have hmem := mul_mul_mem_localClass hDinv hD2 e.2 (Lp.χ.symm m).2
    have htau := Lp.tau e (Lp.χ.symm m) hmem
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at htau
    change Lp.χ _ = tvP q m at htau
    refine ⟨e * g, mul_mem (subset_closure e.2) hg, ?_⟩
    rw [← htau, Equiv.symm_apply_apply]
    have hee : (e : G)⁻¹ = e := inv_eq_of_mul_eq_one_right (hD2 e e.2.1)
    show (e : G) * g * f * (e * g)⁻¹ = e * (Lp.χ.symm m : G) * e
    rw [← hgm, mul_inv_rev, hee]
    group
  have hstab : T46 ≤ MulAction.stabilizer (Equiv.Perm (Fin 693)) S := by
    rw [T46_eq_closure, closure_le]
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    refine Set.Subset.antisymm ?_ fun m hm => ⟨tvP q m, hstep q m hm, tvP_tvP q m⟩
    rintro _ ⟨m, hm, rfl⟩
    exact hstep q m hm
  have hf : Lp.χ f ∈ S := ⟨1, one_mem _, by rw [Equiv.symm_apply_apply]; group⟩
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq T46 (Lp.χ f) (Lp.χ f')
  have hw' : (w : Equiv.Perm (Fin 693)) • S = S := hstab w.2
  have hmem : Lp.χ f' ∈ S := by
    rw [← hw', ← hw]
    exact Set.smul_mem_smul_set hf
  obtain ⟨g, hg, hgf⟩ := hmem
  exact ⟨g, hg, by rw [hgf, Equiv.symm_apply_apply]⟩

theorem orderOf_mul_mem_of_localPoints
    {d : G} (Lp : LocalPoints polarModel D d)
    (f g : LocalClass D d) : orderOf ((f : G) * g) ∈ ({1, 2, 3} : Set ℕ) := by
  have hf2 := hD2 f f.2.1
  have hg2 := hD2 g g.2.1
  by_cases hfg : (f : G) * g = g * f
  · rcases (ThreeTransposition.commute_iff_orderOf_mul hf2 hg2).1 hfg with h | h <;> simp [h]
  · have hp : ¬ perp (Lp.χ f) (Lp.χ g) := fun hp => hfg ((Lp.comm f g).2 hp)
    have h1 := mul_mul_mem_localClass hDinv hD2 f.2 g.2
    have h2 := mul_mul_mem_localClass hDinv hD2 g.2 f.2
    have he : (f : G) * g * f = g * f * g := by
      have e1 := Lp.tau f g h1
      have e2 := Lp.tau g f h2
      have e3 : polarModel.tv (Lp.χ f) (Lp.χ g) = polarModel.tv (Lp.χ g) (Lp.χ f) :=
        tvP_swap hp
      rw [← e1, ← e2] at e3
      exact congrArg Subtype.val (Lp.χ.injective e3)
    have h3 : ((f : G) * g) ^ 3 = 1 := by
      calc ((f : G) * g) ^ 3 = (f * g * f) * (g * f * g) := by
            rw [pow_succ, pow_two]; simp only [mul_assoc]
        _ = (g * f * g) * (g * f * g) := by rw [he]
        _ = g * f * (g * g) * f * g := by simp only [mul_assoc]
        _ = g * (f * f) * g := by rw [hg2, mul_one]; simp only [mul_assoc]
        _ = 1 := by rw [hf2, mul_one, hg2]
    have hne : (f : G) * g ≠ 1 := by
      intro h1'
      apply hfg
      have hgf : (g : G) = f := by
        calc (g : G) = f * f * g := by rw [hf2, one_mul]
          _ = f * (f * g) := by rw [mul_assoc]
          _ = f := by rw [h1', mul_one]
      rw [hgf]
    have := orderOf_eq_prime h3 hne
    simp [this]

end LocalGroup

theorem localGroup_le_centralizer {D : Set G} (d : G) :
    LocalGroup D d ≤ centralizer {d} := by
  rw [LocalGroup, closure_le]
  intro f hf
  exact mem_centralizer_singleton_iff.2 hf.2.2

theorem pair_localGroup_of_localPoints
    [Finite G] {D : Set G}
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, orderOf x = 2) {d : G}
    (Lp : LocalPoints polarModel D d) :
    Pair (LocalGroup D d) {x | (x : G) ∈ LocalClass D d} ∧ 1 < (LocalClass D d).ncard := by
  have hD2' : ∀ x ∈ D, x * x = 1 := fun x hx => ThreeTransposition.mul_self_of_orderOf (hD2 x hx)
  have hcard : (LocalClass D d).ncard = 693 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr Lp.χ, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨⟨inferInstance, ?_, fun x hx => ?_, fun x hx y hy => ?_, closure_closure_coe_preimage⟩,
    by rw [hcard]; norm_num⟩
  · set e₀ : LocalClass D d := Lp.χ.symm 0
    refine ⟨⟨e₀, subset_closure e₀.2⟩, Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨g, hg, hgx⟩ := exists_conj_eq_of_localPoints hDinv hD2' Lp e₀ ⟨x, hx⟩
      exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgx⟩
    · obtain ⟨c, hc⟩ := isConj_iff.1 hx
      have hcx : (c : G) * e₀ * (c : G)⁻¹ = x := congrArg Subtype.val hc
      have hcd : (c : G) * d * (c : G)⁻¹ = d := by
        rw [mem_centralizer_singleton_iff.1 (localGroup_le_centralizer d c.2), mul_inv_cancel_right]
      have := ThreeTransposition.conj_mem_localClass hDinv c e₀.2
      rw [hcd, hcx] at this
      exact this
  · rw [← Subgroup.orderOf_coe]
    exact hD2 x hx.1
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact orderOf_mul_mem_of_localPoints hDinv hD2' Lp ⟨x, hx⟩ ⟨y, hy⟩

theorem FischerHyp.pair_localGroup
    [Finite G] {t : G} {L E : Subgroup G}
    {p : L →* Equiv.Perm (Fin 693)} (h : FischerHyp t L E p) :
    Pair (LocalGroup (tClass t) t) {x | (x : G) ∈ LocalClass (tClass t) t} ∧
      1 < (LocalClass (tClass t) t).ncard :=
  pair_localGroup_of_localPoints (tClass_inv t) (fun _ hx => orderOf_of_mem_tClass h.orderOf_t hx)
    h.localPoints

end CFSG.EvenSmallLie.UnitarySix.Fischer
