module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalInner
public import CFSG.Adapters.Involutions

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

@[expose] def OddCoreFree (X : Type*) [Group X] : Prop :=
  ∀ M : Subgroup X, M.Normal → Odd (Nat.card M) → M = ⊥

section OddCoreFree

variable {X Y : Type*} [Group X] [Group Y]

theorem OddCoreFree.of_mulEquiv (e : X ≃* Y) (h : OddCoreFree Y) : OddCoreFree X := by
  intro M hM hodd
  have hM' : (M.map e.toMonoidHom).Normal := Subgroup.Normal.map hM e.toMonoidHom e.surjective
  have hcard : Nat.card (M.map e.toMonoidHom) = Nat.card M :=
    Subgroup.card_map_of_injective e.injective
  have := h _ hM' (hcard ▸ hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp this

theorem oddCoreFree_of_simple_even [IsSimpleGroup X] [Finite X] (heven : Even (Nat.card X)) :
    OddCoreFree X := by
  intro M hM hodd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exact h
  · exfalso
    have : Nat.card M = Nat.card X := by rw [h]; exact Subgroup.card_top
    rw [this] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven

end OddCoreFree

theorem eq_bot_of_stronglyClosed_complement {K : Type} [Group K] [Finite K]
    (J R B : Subgroup K) [J.Normal] (hR : IsSylowTwoOf R ⊤) (hBR : B ≤ R)
    (hB : IsElemAbelian 2 B)
    (hcl : ∀ a ∈ B, ∀ g : K, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ B)
    (hX : NoStronglyClosedElemAbelian J) (hodd : OddCoreFree J)
    (hC : ∀ k : K, (∀ j ∈ J, k * j = j * k) → k = 1) : B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hB1
  have hBJ : B ⊓ J = ⊥ := by
    by_contra hne
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hu1' : (u : K) ≠ 1 := fun h => hu1 (Subtype.ext h)
    obtain ⟨P, A, hW, hA⟩ := exists_witness_of_normal J R B hR hBR hB hcl u.2.1 u.2.2 hu1'
    exact hA (hX P A hW)
  have hRp : IsPGroup 2 R := hR.2.1
  have : Group.IsNilpotent R := hRp.isNilpotent
  have hBn : (B.subgroupOf R).Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hx' : (x : K) ∈ B := hx
    have := hcl (x : K) hx' ((y : K)⁻¹)
      (by simpa using R.mul_mem (R.mul_mem y.2 x.2) (R.inv_mem y.2))
    show (y : K) * (x : K) * (y : K)⁻¹ ∈ B
    simpa using this
  have hBne : B.subgroupOf R ≠ ⊥ := by
    intro h
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have : (⟨b, hBR hb⟩ : R) ∈ B.subgroupOf R := hb
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hBne)
  set z : K := ((c : R) : K) with hz
  have hzB : z ∈ B := c.2.1
  have hzR : z ∈ R := (c : R).2
  have hz1 : z ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hzc : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    have := Subgroup.mem_center_iff.mp c.2.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hz2 : z * z = 1 := by rw [← sq]; exact hB.2 z hzB
  have hwc : ∀ g ∈ J ⊔ R, g⁻¹ * z * g ∈ R → g⁻¹ * z * g = z := by
    intro g hg hgz
    obtain ⟨j, hj, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have h1 : j⁻¹ * z * j ∈ R := by
      have : j⁻¹ * z * j = r * ((j * r)⁻¹ * z * (j * r)) * r⁻¹ := by group
      rw [this]
      exact R.mul_mem (R.mul_mem hr hgz) (R.inv_mem hr)
    have h2 : j⁻¹ * z * j ∈ B := hcl z hzB j h1
    have h3 : (j⁻¹ * z * j) * z⁻¹ ∈ B := B.mul_mem h2 (B.inv_mem hzB)
    have h4 : (j⁻¹ * z * j) * z⁻¹ ∈ J := by
      have : (j⁻¹ * z * j) * z⁻¹ = j⁻¹ * (z * j * z⁻¹) := by group
      rw [this]
      exact J.mul_mem (J.inv_mem hj) (Subgroup.Normal.conj_mem inferInstance j hj z)
    have h5 : (j⁻¹ * z * j) * z⁻¹ ∈ B ⊓ J := ⟨h3, h4⟩
    rw [hBJ, Subgroup.mem_bot, mul_inv_eq_one] at h5
    have h6 : (j * r)⁻¹ * z * (j * r) = r⁻¹ * (j⁻¹ * z * j) * r := by group
    rw [h6, h5]
    calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
      _ = r⁻¹ * (r * z) := by rw [hzc r hr]
      _ = z := by group
  let Y : Subgroup K := J ⊔ R
  have hJY : J ≤ Y := le_sup_left
  have hRY : R ≤ Y := le_sup_right
  let RY : Subgroup Y := R.subgroupOf Y
  have hRYp : IsPGroup 2 RY := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  have hRYi : ¬ 2 ∣ RY.index := by
    have h := Subgroup.relIndex_mul_index hRY
    have hKR : ¬ 2 ∣ R.index := by
      have := hR.2.2
      rwa [show (R.subgroupOf ⊤).index = R.index from Subgroup.relIndex_top_right R] at this
    intro hd
    apply hKR
    rw [← h]
    exact Dvd.dvd.mul_right hd _
  let SY : Sylow 2 Y := hRYp.toSylow hRYi
  have hSY : (SY : Subgroup Y) = RY := rfl
  let zY : Y := ⟨z, hRY hzR⟩
  have hzY1 : zY ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzY2 : zY * zY = 1 := Subtype.ext hz2
  have hzYc : zY ∈ Subgroup.centralizer (SY : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : (s : K) ∈ R := hs
    exact Subtype.ext (hzc _ hs')
  have hwcY : ∀ g : Y, g⁻¹ * zY * g ∈ (SY : Subgroup Y) → g⁻¹ * zY * g = zY := by
    intro g hg
    have hg' : ((g⁻¹ * zY * g : Y) : K) ∈ R := hg
    exact Subtype.ext (hwc (g : K) g.2 (by simpa using hg'))
  have : Fintype Y := Fintype.ofFinite Y
  have hiso : ∀ g : Y, (g * zY * g⁻¹) * zY = zY * (g * zY * g⁻¹) → g * zY * g⁻¹ = zY :=
    fun g hcomm => CFSG.Adapters.isolated_of_weakClosure SY hzYc hzY2 hwcY g hcomm
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar Y zY hzY1 hzY2 hiso
  have hodd' : ∀ M : Subgroup K, M ≤ J → (∀ j ∈ J, ∀ m ∈ M, j * m * j⁻¹ ∈ M) →
      Odd (Nat.card M) → M = ⊥ := by
    intro M hMJ hMn hMo
    have hMn' : (M.subgroupOf J).Normal := by
      refine ⟨fun x hx y => ?_⟩
      have hx' : (x : K) ∈ M := hx
      show ((y : K) * (x : K) * (y : K)⁻¹) ∈ M
      exact hMn y y.2 x hx'
    have hcard : Nat.card (M.subgroupOf J) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMJ).toEquiv
    have hbot := hodd _ hMn' (hcard ▸ hMo)
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hMJ hx⟩ : J) ∈ M.subgroupOf J := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
  let NK : Subgroup K := N.map Y.subtype
  have hNKcard : Nat.card NK = Nat.card N := Subgroup.card_map_of_injective Y.subtype_injective
  have hMbot : NK ⊓ J = ⊥ := by
    refine hodd' _ inf_le_right ?_ ?_
    · rintro j hj m ⟨hmN, hmJ⟩
      refine ⟨?_, J.mul_mem (J.mul_mem hj hmJ) (J.inv_mem hj)⟩
      obtain ⟨n, hn, rfl⟩ := hmN
      exact ⟨⟨j, hJY hj⟩ * n * ⟨j, hJY hj⟩⁻¹, hNn.conj_mem n hn _, rfl⟩
    · have hd : Nat.card ↥(NK ⊓ J) ∣ Nat.card N := hNKcard ▸ Subgroup.card_dvd_of_le inf_le_left
      exact Odd.of_dvd_nat hNodd hd
  have hcomm : ∀ j ∈ J, z * j = j * z := by
    intro j hj
    let jY : Y := ⟨j, hJY hj⟩
    have h1 : j * z * j⁻¹ * z⁻¹ ∈ NK := ⟨jY * zY * jY⁻¹ * zY⁻¹, hN jY, rfl⟩
    have h2 : j * z * j⁻¹ * z⁻¹ ∈ J := by
      have : j * z * j⁻¹ * z⁻¹ = j * (z * j⁻¹ * z⁻¹) := by group
      rw [this]
      exact J.mul_mem hj (Subgroup.Normal.conj_mem inferInstance j⁻¹ (J.inv_mem hj) z)
    have h3 : j * z * j⁻¹ * z⁻¹ ∈ NK ⊓ J := ⟨h1, h2⟩
    rw [hMbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  exact hz1 (hC z fun j hj => hcomm j hj)

theorem centralizes_of_noStronglyClosed {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (hS : IsSylowTwoOf S H) (hUS : U ≤ S) (hU : IsElemAbelian 2 U)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) (hLH : L ≤ H)
    (hperf : Group.IsPerfect L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hX : NoStronglyClosedElemAbelian (L ⧸ Subgroup.center L))
    (hodd : OddCoreFree (L ⧸ Subgroup.center L)) :
    ∀ u ∈ U, ∀ y ∈ L, y * u = u * y := by
  have := hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := H ⊓ Subgroup.normalizer (L : Set G)
  have hNH : N ≤ H := inf_le_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLN : L ≤ N := le_inf hLH Subgroup.le_normalizer
  have hUN : U ≤ N := le_inf (hUS.trans hS.1) hUL
  have hU2 : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hU.2 x x.2)⟩
  obtain ⟨R, hR, hUR⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUN hU2
  obtain ⟨S₁, hS₁, hRS₁⟩ := EscapingLocal.exists_isSylowTwoOf_ge (hR.1.trans hNH) hR.2.1
  have hcl₁ := stronglyClosed_of_le_pGroup hS hS₁.1 hS₁.2.1 (hUR.trans hRS₁) hcl
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
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem hn) y).mp hy
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
    isSylowTwoOf_top_iff.mpr ⟨Rbar.isPGroup', Rbar.not_dvd_index⟩
  let e₀ : L ⧸ Subgroup.center L ≃* Lbar :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hX' : NoStronglyClosedElemAbelian Lbar := NoStronglyClosedElemAbelian.of_mulEquiv e₀.symm hX
  have hodd' : OddCoreFree Lbar := OddCoreFree.of_mulEquiv e₀.symm hodd
  have hC' : ∀ k : N ⧸ C, (∀ j ∈ Lbar, k * j = j * k) → k = 1 := by
    intro k hk
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective k
    have hnN : (n : G) ∈ Subgroup.normalizer (L : Set G) := hNL n.2
    let c : L ≃* L := conjAutOfNormalizer L hnN
    have hcen : ∀ x : L, ((1 : L)⁻¹ * x * 1)⁻¹ * c x ∈ Subgroup.center L := by
      intro x
      have h1 : (QuotientGroup.mk (n * Subgroup.inclusion hLN x) : N ⧸ C) =
          QuotientGroup.mk (Subgroup.inclusion hLN x * n) := by
        have := hk (φ x) ⟨x, rfl⟩
        simpa [φ, π] using this
      have h2 : (n * Subgroup.inclusion hLN x)⁻¹ * (Subgroup.inclusion hLN x * n) ∈ C :=
        QuotientGroup.eq.mp h1
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 := (hCmem _).mp h2 y y.2
      apply Subtype.ext
      have hv : (((1 : L)⁻¹ * x * 1)⁻¹ * c x : L).val = (x : G)⁻¹ * ((n : G)⁻¹ * x * (n : G)) := by
        simp [c, coe_conjAutOfNormalizer]
      have hv2 : (((n * Subgroup.inclusion hLN x)⁻¹ * (Subgroup.inclusion hLN x * n) : N) : G) =
          (x : G)⁻¹ * ((n : G)⁻¹ * x * (n : G)) := by
        simp [Subgroup.inclusion]
        group
      show (y : G) * ((((1 : L)⁻¹ * x * 1)⁻¹ * c x : L) : G) =
        ((((1 : L)⁻¹ * x * 1)⁻¹ * c x : L) : G) * (y : G)
      rw [hv, ← hv2]
      exact h3
    have hc := eq_conj_of_central_displacement c 1 hcen
    have hnC : n ∈ C := by
      rw [hCmem]
      intro y hy
      have h := congrArg Subtype.val (hc ⟨y, hy⟩)
      simp [c, coe_conjAutOfNormalizer] at h
      calc y * (n : G) = (n : G) * ((n : G)⁻¹ * y * (n : G)) := by group
        _ = (n : G) * y := by rw [h]
    exact (QuotientGroup.eq_one_iff n).mpr hnC
  have hUbar := eq_bot_of_stronglyClosed_complement Lbar (Rbar : Subgroup (N ⧸ C)) Ubar hSbar
    hUbar_le (isElemAbelian_map (isElemAbelian_subgroupOf hU) π)
    (fun a ha g hg => hclbar a ha g hg) hX' hodd' hC'
  intro u hu
  let u' : N := ⟨u, hUN hu⟩
  have hu' : π u' ∈ Ubar := Subgroup.mem_map_of_mem π (show u' ∈ U.subgroupOf N from hu)
  rw [hUbar, Subgroup.mem_bot] at hu'
  have hu'C : u' ∈ C := (QuotientGroup.eq_one_iff u').mp hu'
  exact (hCmem u').mp hu'C

end CFSG.QuasithinUnique.K1
