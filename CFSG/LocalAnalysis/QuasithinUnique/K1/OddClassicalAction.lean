module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalCore
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

section Transport

variable {N : Type} [Group N] {X : Type} [Group X]

theorem isSylowTwoOf_top_map {Lb Q : Subgroup N} (e : Lb ≃* X) (hQ : IsSylowTwoOf Q Lb) :
    IsSylowTwoOf ((Q.subgroupOf Lb).map e.toMonoidHom) ⊤ := by
  have hQ2 : IsPGroup 2 (Q.subgroupOf Lb) :=
    hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
  refine ⟨le_top, hQ2.map e.toMonoidHom, ?_⟩
  have h1 : ((Q.subgroupOf Lb).map e.toMonoidHom).relIndex ⊤ =
      ((Q.subgroupOf Lb).map e.toMonoidHom).index := Subgroup.relIndex_top_right _
  have h2 : ((Q.subgroupOf Lb).map e.toMonoidHom).index = (Q.subgroupOf Lb).index :=
    Subgroup.index_map_equiv _ e
  change ¬ 2 ∣ ((Q.subgroupOf Lb).map e.toMonoidHom).relIndex ⊤
  rw [h1, h2]
  exact hQ.2.2

theorem noStrongAb_of_mulEquiv (Lb : Subgroup N) (e : Lb ≃* X)
    (hX : NoStrongAb (⊤ : Subgroup X)) : NoStrongAb Lb := by
  intro Q B hQ hBQ hcomm hcl
  have hBL : B ≤ Lb := hBQ.trans hQ.1
  have hQX := isSylowTwoOf_top_map e hQ
  have hBX : (B.subgroupOf Lb).map e.toMonoidHom ≤ (Q.subgroupOf Lb).map e.toMonoidHom :=
    Subgroup.map_mono (fun x hx => hBQ hx)
  have hcommX : IsMulCommutative ((B.subgroupOf Lb).map e.toMonoidHom) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← ha, ← hb]
    show e a' * e b' = e b' * e a'
    rw [← map_mul, ← map_mul]
    congr 1
    have := hcomm.is_comm.comm ⟨(a' : N), ha'⟩ ⟨(b' : N), hb'⟩
    have h : (a' : N) * b' = b' * a' := congrArg Subtype.val this
    exact Subtype.ext h
  have hclX : ∀ a ∈ (B.subgroupOf Lb).map e.toMonoidHom, ∀ g ∈ (⊤ : Subgroup X),
      g⁻¹ * a * g ∈ (Q.subgroupOf Lb).map e.toMonoidHom →
        g⁻¹ * a * g ∈ (B.subgroupOf Lb).map e.toMonoidHom := by
    intro a ha g _ hg
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨g', rfl⟩ := e.surjective g
    obtain ⟨q', hq', hq⟩ := hg
    have hq'' : (g'⁻¹ * a' * g') = q' := by
      apply e.injective
      show e (g'⁻¹ * a' * g') = e q'
      rw [map_mul, map_mul, map_inv]
      exact hq.symm
    refine ⟨g'⁻¹ * a' * g', ?_, by simp⟩
    have := hcl (a' : N) ha' (g' : N) g'.2 (by
      have h := hq'
      rw [← hq''] at h
      exact h)
    exact this
  have hbot := hX _ _ hQX hBX hcommX hclX
  rw [eq_bot_iff]
  intro b hb
  have hb' : (⟨b, hBL hb⟩ : Lb) ∈ B.subgroupOf Lb := hb
  have : e ⟨b, hBL hb⟩ ∈ (B.subgroupOf Lb).map e.toMonoidHom := ⟨_, hb', rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  have h1 : (⟨b, hBL hb⟩ : Lb) = 1 := e.injective (by simpa using this)
  have h2 : b = 1 := congrArg Subtype.val h1
  rw [h2]; exact Subgroup.one_mem _

theorem card_sylow_of_mulEquiv (Lb : Subgroup N) (e : Lb ≃* X)
    (hX : ∀ Q : Subgroup X, IsSylowTwoOf Q ⊤ → Nat.card Q = 4) :
    ∀ Q : Subgroup N, IsSylowTwoOf Q Lb → Nat.card Q = 4 := by
  intro Q hQ
  have h := hX _ (isSylowTwoOf_top_map e hQ)
  rw [Subgroup.card_map_of_injective e.injective] at h
  rw [← h]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.1).toEquiv).symm

end Transport

section Action

variable {G : Type} [Group G] [Finite G]

theorem action_core {H S U L : Subgroup G} (hSC : StrongClosureComponent H S U L)
    (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L))
    (hev : 2 ∣ Nat.card (L ⧸ Subgroup.center L))
    (hnonab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x) :
    (NoStrongAb (⊤ : Subgroup (L ⧸ Subgroup.center L)) →
      ∀ u ∈ U, ∀ y ∈ L, u⁻¹ * y * u = y) ∧
    ((∀ Q : Subgroup (L ⧸ Subgroup.center L), IsSylowTwoOf Q ⊤ → Nat.card Q = 4) →
      ∀ u ∈ U, ∃ x ∈ L, ∀ y ∈ L, u⁻¹ * y * u = x⁻¹ * y * x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hSC.perfect
  let N : Subgroup G := H ⊓ Subgroup.normalizer (L : Set G)
  have hNH : N ≤ H := inf_le_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLN : L ≤ N := le_inf hSC.le_H Subgroup.le_normalizer
  have hUN : U ≤ N := le_inf (hSC.le_S.trans hSC.sylow.1) hSC.normalizes
  have hU2 : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hSC.elem.2 x x.2)⟩
  obtain ⟨R, hR, hUR⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUN hU2
  obtain ⟨S₁, hS₁, hRS₁⟩ := EscapingLocal.exists_isSylowTwoOf_ge (hR.1.trans hNH) hR.2.1
  have hcl₁ := stronglyClosed_of_le_pGroup hSC.sylow hS₁.1 hS₁.2.1 (hUR.trans hRS₁) hSC.closed
  have hclR : ∀ a ∈ U, ∀ g ∈ N, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ U := fun a ha g hg hgR =>
    hcl₁ a ha g (hNH hg) (hRS₁ hgR)
  let C : Subgroup N := (Subgroup.centralizer (L : Set G)).subgroupOf N
  have hCmem : ∀ n : N, n ∈ C ↔ ∀ y ∈ L, y * (n : G) = (n : G) * y := fun n => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hCn : C.Normal := by
    refine ⟨fun c hc n => ?_⟩
    rw [hCmem] at hc ⊢
    intro y hy
    have hn : (n : G) ∈ Subgroup.normalizer (L : Set G) := hNL n.2
    have hy' : (n : G)⁻¹ * y * (n : G) ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem hn)
        y).mp hy
      simpa using this
    have h1 := hc _ hy'
    change y * ((n : G) * (c : G) * (n : G)⁻¹) = ((n : G) * (c : G) * (n : G)⁻¹) * y
    calc y * ((n : G) * (c : G) * (n : G)⁻¹)
        = (n : G) * (((n : G)⁻¹ * y * (n : G)) * (c : G)) * (n : G)⁻¹ := by group
      _ = (n : G) * ((c : G) * ((n : G)⁻¹ * y * (n : G))) * (n : G)⁻¹ := by rw [h1]
      _ = ((n : G) * (c : G) * (n : G)⁻¹) * y := by group
  let π : N →* N ⧸ C := QuotientGroup.mk' C
  obtain ⟨R', hR'⟩ := isSylowTwoOf_iff_exists.mp hR
  have hU'R' : U.subgroupOf N ≤ (R' : Subgroup N) := subgroupOf_le_of_map_eq hR' hUR
  obtain ⟨Rbar, hRbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed R'
    (U.subgroupOf N) C hU'R' (stronglyClosed_subgroupOf hR' hclR)
  let φ : L →* N ⧸ C := π.comp (Subgroup.inclusion hLN)
  have hφker : φ.ker = Subgroup.center L := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    change π (Subgroup.inclusion hLN y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hCmem]
    constructor
    · intro h z
      exact Subtype.ext (h (z : G) z.2)
    · intro h z hz
      exact congrArg Subtype.val (h ⟨z, hz⟩)
  let Lbar : Subgroup (N ⧸ C) := φ.range
  have hLbarN : Lbar.Normal := by
    refine ⟨fun x hx n => ?_⟩
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective n
    obtain ⟨x', rfl⟩ := hx
    have hn : (n' : G) ∈ Subgroup.normalizer (L : Set G) := hNL n'.2
    have hnx : (n' : G) * (x' : G) * (n' : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hn x').mp x'.2
    refine ⟨⟨_, hnx⟩, ?_⟩
    have e : Subgroup.inclusion hLN ⟨(n' : G) * (x' : G) * (n' : G)⁻¹, hnx⟩ =
        n' * Subgroup.inclusion hLN x' * n'⁻¹ := Subtype.ext rfl
    show π (Subgroup.inclusion hLN ⟨_, hnx⟩) = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  let Ubar : Subgroup (N ⧸ C) := (U.subgroupOf N).map π
  have hRbar' : (Rbar : Subgroup (N ⧸ C)) = (R' : Subgroup N).map π := hRbar
  have hUbar_le : Ubar ≤ (Rbar : Subgroup (N ⧸ C)) := by
    rw [hRbar']
    exact Subgroup.map_mono hU'R'
  have hSbar : IsSylowTwoOf (Rbar : Subgroup (N ⧸ C)) ⊤ :=
    ⟨le_top, Rbar.isPGroup', by
      have h : ((Rbar : Subgroup (N ⧸ C)).subgroupOf ⊤).index =
          (Rbar : Subgroup (N ⧸ C)).index := Subgroup.relIndex_top_right _
      rw [h]
      exact Rbar.not_dvd_index⟩
  have hUbarE : IsElemAbelian 2 Ubar :=
    isElemAbelian_map (isElemAbelian_subgroupOf hSC.elem) π
  have hclbar' : ∀ a ∈ Ubar, ∀ g : N ⧸ C, g⁻¹ * a * g ∈ (Rbar : Subgroup (N ⧸ C)) →
      g⁻¹ * a * g ∈ Ubar := fun a ha g hg => hclbar a ha g hg
  let e₀ : L ⧸ Subgroup.center L ≃* Lbar :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hLbs : IsSimpleGroup Lbar := by
    have := hsimple
    exact e₀.symm.isSimpleGroup
  have hLbev : 2 ∣ Nat.card Lbar := by
    rw [← Nat.card_congr e₀.toEquiv]
    exact hev
  have hLbnonab : ∃ x y : Lbar, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnonab
    exact ⟨e₀ x, e₀ y, fun h => hxy (e₀.injective (by simpa using h))⟩
  have := hLbarN
  have key : ∀ (u : G) (hu : u ∈ U) (x : L),
      φ (conjAutOfNormalizer L (hSC.normalizes hu) x) =
        (π ⟨u, hUN hu⟩)⁻¹ * φ x * π ⟨u, hUN hu⟩ := by
    intro u hu x
    have e : Subgroup.inclusion hLN (conjAutOfNormalizer L (hSC.normalizes hu) x) =
        (⟨u, hUN hu⟩ : N)⁻¹ * Subgroup.inclusion hLN x * ⟨u, hUN hu⟩ := Subtype.ext rfl
    show π (Subgroup.inclusion hLN (conjAutOfNormalizer L (hSC.normalizes hu) x)) = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hub : ∀ (u : G) (hu : u ∈ U), π ⟨u, hUN hu⟩ ∈ Ubar := fun u hu =>
    Subgroup.mem_map_of_mem π (show (⟨u, hUN hu⟩ : N) ∈ U.subgroupOf N from hu)
  refine ⟨fun hN u hu y hy => ?_, fun h4 u hu => ?_⟩
  · have hN' : NoStrongAb Lbar := noStrongAb_of_mulEquiv Lbar e₀.symm hN
    have hcen := core_nasc hLbs hLbev hN' hSbar hUbar_le hUbarE hclbar'
    have hc := Subgroup.mem_centralizer_iff.mp (hcen (hub u hu))
    let c : L ≃* L := conjAutOfNormalizer L (hSC.normalizes hu)
    have hdisp : ∀ x : L, ((1 : L)⁻¹ * x * 1)⁻¹ * c x ∈ Subgroup.center L := by
      intro x
      rw [← hφker, MonoidHom.mem_ker, map_mul, map_inv, key u hu x]
      have hx := hc (φ x) ⟨x, rfl⟩
      have h1 : (π ⟨u, hUN hu⟩)⁻¹ * φ x * π ⟨u, hUN hu⟩ = φ x := by
        rw [mul_assoc, hx, ← mul_assoc, inv_mul_cancel, one_mul]
      simp only [inv_one, one_mul, mul_one, h1, inv_mul_cancel]
    have hid := eq_conj_of_central_displacement c 1 hdisp
    have h := congrArg Subtype.val (hid ⟨y, hy⟩)
    calc u⁻¹ * y * u = ((c ⟨y, hy⟩ : L) : G) := rfl
      _ = y := by simpa using h
  · have h4' := card_sylow_of_mulEquiv Lbar e₀.symm h4
    obtain ⟨l, hl, hc⟩ := core_four hLbs hLbnonab hLbev h4' hSbar hUbar_le hUbarE hclbar'
      (π ⟨u, hUN hu⟩) (hub u hu)
    obtain ⟨x₀, rfl⟩ := hl
    have hcom := Subgroup.mem_centralizer_iff.mp hc
    let c : L ≃* L := conjAutOfNormalizer L (hSC.normalizes hu)
    have hdisp : ∀ x : L, (((x₀⁻¹ : L))⁻¹ * x * (x₀⁻¹ : L))⁻¹ * c x ∈ Subgroup.center L := by
      intro x
      rw [← hφker, MonoidHom.mem_ker, map_mul, map_inv, key u hu x]
      have hz := hcom (φ x) ⟨x, rfl⟩
      have h1 : (π ⟨u, hUN hu⟩ * φ x₀)⁻¹ * φ x * (π ⟨u, hUN hu⟩ * φ x₀) = φ x := by
        rw [mul_assoc, hz, ← mul_assoc, inv_mul_cancel, one_mul]
      have h2 : (π ⟨u, hUN hu⟩)⁻¹ * φ x * π ⟨u, hUN hu⟩ = φ x₀ * φ x * (φ x₀)⁻¹ := by
        calc (π ⟨u, hUN hu⟩)⁻¹ * φ x * π ⟨u, hUN hu⟩
            = φ x₀ * ((π ⟨u, hUN hu⟩ * φ x₀)⁻¹ * φ x * (π ⟨u, hUN hu⟩ * φ x₀)) * (φ x₀)⁻¹ := by
              group
          _ = φ x₀ * φ x * (φ x₀)⁻¹ := by rw [h1]
      rw [h2]
      simp only [inv_inv, map_mul, map_inv]
      group
    have hid := eq_conj_of_central_displacement c (x₀⁻¹) hdisp
    refine ⟨((x₀⁻¹ : L) : G), (x₀⁻¹).2, fun y hy => ?_⟩
    have h := congrArg Subtype.val (hid ⟨y, hy⟩)
    calc u⁻¹ * y * u = ((c ⟨y, hy⟩ : L) : G) := rfl
      _ = ((((x₀⁻¹ : L))⁻¹ * ⟨y, hy⟩ * (x₀⁻¹ : L) : L) : G) := h
      _ = ((x₀⁻¹ : L) : G)⁻¹ * y * ((x₀⁻¹ : L) : G) := rfl

end Action

end CFSG.QuasithinUnique.K1
