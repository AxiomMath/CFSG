module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

variable {G : Type*} [Group G] {L : Subgroup G} {z : G}

theorem map_conj_eq_of_mem_normalizer {R : Subgroup G} {n : G} (hn : n ∈ normalizer (R : Set G)) :
    R.map (MulAut.conj n).toMonoidHom = R := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_normalizer_iff.1 hn r).1 hr
  · intro hx
    refine ⟨n⁻¹ * x * n, (mem_normalizer_iff.1 hn _).2 ?_, ?_⟩
    · simpa [mul_assoc] using hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

@[expose] def conjNormalizer (R : Subgroup G) : normalizer (R : Set G) →* MulAut R where
  toFun n := conjRestrict R n (map_conj_eq_of_mem_normalizer n.2)
  map_one' := MulEquiv.ext fun r => Subtype.ext (by simp [coe_conjRestrict])
  map_mul' n n' := MulEquiv.ext fun r => Subtype.ext (by
    simp only [coe_conjRestrict, Subgroup.coe_mul, MulAut.mul_apply, _root_.mul_inv_rev]
    group)

theorem coe_conjNormalizer (R : Subgroup G) (n : normalizer (R : Set G)) (r : R) :
    (conjNormalizer R n r : G) = n * r * (n : G)⁻¹ :=
  rfl

theorem ker_conjNormalizer {R : Subgroup G} (hR : centralizer (R : Set G) = R) :
    (conjNormalizer R).ker = R.subgroupOf (normalizer (R : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    have hmem : (n : G) ∈ centralizer (R : Set G) := by
      refine mem_centralizer_iff.2 fun r hr => ?_
      have := congrArg (fun α : MulAut R => (α ⟨r, hr⟩ : G)) h
      simp only [coe_conjNormalizer, MulAut.one_apply] at this
      calc r * n = n * r * (n : G)⁻¹ * n := by rw [this]
        _ = n * r := by group
    rw [hR] at hmem
    exact hmem
  · intro h
    have h' : (n : G) ∈ centralizer (R : Set G) := by
      rw [hR]
      exact h
    refine MulEquiv.ext fun r => Subtype.ext ?_
    rw [coe_conjNormalizer, MulAut.one_apply, ← mem_centralizer_iff.1 h' r r.2]
    group

section Setting

variable (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)

include hzC in
theorem zpowers_le_centralizer : zpowers z ≤ centralizer (L : Set G) :=
  zpowers_le.2 hzC

include hz in
theorem sq_eq_one_of_orderOf : z ^ 2 = 1 := by
  have h := pow_orderOf_eq_one z
  rwa [hz] at h

include hzC hinf hz in
theorem sup_facts {A : Subgroup G} (hAL : A ≤ L) (hAe : IsElementaryAbelian 2 A)
    (hAc : Nat.card A = 64) :
    A ⊓ zpowers z = ⊥ ∧ IsElementaryAbelian 2 (A ⊔ zpowers z : Subgroup G) ∧
      Nat.card (A ⊔ zpowers z : Subgroup G) = 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzA : zpowers z ≤ centralizer (A : Set G) := fun t ht =>
    mem_centralizer_iff.2 fun a ha =>
      mem_centralizer_iff.1 (zpowers_le_centralizer hzC ht) a (hAL ha)
  have hAz : A ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf hAL le_rfl
  have : IsElementaryAbelian 2 A := hAe
  have : IsElementaryAbelian 2 (zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (sq_eq_one_of_orderOf hz)
  refine ⟨hAz, IsElementaryAbelian.sup_of_le_centralizer hzA, ?_⟩
  rw [card_sup_eq_mul hzA hAz, hAc, Nat.card_zpowers, hz]

include hzC hsup in
theorem centralizer_inf_le {A : Subgroup G} (hAC : centralizer (A : Set G) ⊓ L = A) :
    centralizer (A : Set G) ⊓ centralizer ({z} : Set G) ≤ A ⊔ zpowers z := by
  intro x hx
  obtain ⟨hxA, hxz⟩ := Subgroup.mem_inf.1 hx
  have hAL : A ≤ L := hAC ▸ inf_le_right
  obtain ⟨l, hl, s, hs, rfl⟩ :=
    (mem_sup_of_le_centralizer (zpowers_le_centralizer hzC)).1 (hsup ▸ hxz)
  have hsA : s ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun a ha =>
    mem_centralizer_iff.1 (zpowers_le_centralizer hzC hs) a (hAL ha)
  have hlA : l ∈ centralizer (A : Set G) := by
    have := (centralizer (A : Set G)).mul_mem hxA ((centralizer (A : Set G)).inv_mem hsA)
    simpa using this
  have hlA' : l ∈ A := hAC ▸ Subgroup.mem_inf.2 ⟨hlA, hl⟩
  exact mul_mem_sup hlA' hs

include hzC hsup hinf hz hb hnd hV in
theorem exists_conj_eq_of_card_eq [Finite G] {W : Submodule (ZMod 2) V}
    (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) {E : Subgroup G} (hEH : E ≤ centralizer ({z} : Set G))
    (hEe : IsElementaryAbelian 2 E) (hEc : Nat.card E = 128) :
    ∃ l : L, E = (pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z).map
      (MulAut.conj (l : G)).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLH : L ≤ centralizer ({z} : Set G) := hsup ▸ le_sup_left
  have hHc : Nat.card (centralizer ({z} : Set G)) = Nat.card L * 2 := by
    rw [← hsup, card_sup_eq_mul (zpowers_le_centralizer hzC) hinf, Nat.card_zpowers, hz]
  have hrelH : L.relIndex (centralizer ({z} : Set G)) = 2 := by
    have h1 := (L.subgroupOf (centralizer ({z} : Set G))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv, hHc, mul_comm (Nat.card L)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrelE : L.relIndex E ≤ 2 :=
    hrelH ▸ relIndex_le_of_le_right hEH (by rw [hrelH]; norm_num)
  have hLEcard : Nat.card (L.subgroupOf E) = Nat.card (L ⊓ E : Subgroup G) := by
    rw [← inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hLE64 : 64 ≤ Nat.card (L ⊓ E : Subgroup G) := by
    have h1 := (L.subgroupOf E).index_mul_card
    rw [hLEcard, hEc] at h1
    have h2 : (L.subgroupOf E).index * Nat.card (L ⊓ E : Subgroup G) ≤
        2 * Nat.card (L ⊓ E : Subgroup G) := Nat.mul_le_mul_right _ hrelE
    omega
  have hLEe : IsElementaryAbelian 2 (L ⊓ E : Subgroup G) :=
    isElementaryAbelian_of_forall
      (fun x hx y hy => mul_comm_of_isElementaryAbelian hEe (Subgroup.mem_inf.1 hx).2
        (Subgroup.mem_inf.1 hy).2)
      (fun x hx => mul_self_of_isElementaryAbelian hEe (Subgroup.mem_inf.1 hx).2)
  obtain ⟨h64, hW₁⟩ := elementary_le_of_model hb hnd hV φ inf_le_left hLEe
  obtain ⟨W₁, hW₁i, hd₁, hA₁⟩ := hW₁ (le_antisymm h64 hLE64)
  obtain ⟨hA₁e, hA₁c, hA₁C, -⟩ := pullSub_radical hb hnd hV φ hW₁i hd₁
  have hEC : E ≤ centralizer (pullSub φ (pointwiseStabilizer b W₁) : Set G) ⊓
      centralizer ({z} : Set G) := by
    refine fun x hx => Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, hEH hx⟩
    rw [← hA₁] at ha
    exact mul_comm_of_isElementaryAbelian hEe (Subgroup.mem_inf.1 ha).2 hx
  have hEle := hEC.trans (centralizer_inf_le hzC hsup hA₁C)
  obtain ⟨-, -, h128⟩ := sup_facts hzC hinf hz (pullSub_le φ _) hA₁e hA₁c
  have hEeq : E = pullSub φ (pointwiseStabilizer b W₁) ⊔ zpowers z :=
    eq_of_le_of_card_ge hEle (by rw [h128, hEc])
  obtain ⟨l, hl⟩ := exists_conj_radical_of_model hb hnd hV φ hW hd hW₁i hd₁
  refine ⟨l, ?_⟩
  rw [hEeq, Subgroup.map_sup, hl, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply,
    show (l : G) * z * (l : G)⁻¹ = z by
      rw [mem_centralizer_iff.1 hzC l l.2, mul_inv_cancel_right]]

include hzC hinf in
theorem sup_inf_eq {A : Subgroup G} (hAL : A ≤ L) : (A ⊔ zpowers z) ⊓ L = A := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hAL)
  obtain ⟨hxR, hxL⟩ := Subgroup.mem_inf.1 hx
  have hzA : zpowers z ≤ centralizer (A : Set G) := fun t ht =>
    mem_centralizer_iff.2 fun a ha =>
      mem_centralizer_iff.1 (zpowers_le_centralizer hzC ht) a (hAL ha)
  obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_of_le_centralizer hzA).1 hxR
  have hsL : s ∈ L := by
    have := L.mul_mem (L.inv_mem (hAL ha)) hxL
    simpa using this
  have hs1 : s = 1 := by
    have : s ∈ L ⊓ zpowers z := Subgroup.mem_inf.2 ⟨hsL, hs⟩
    rwa [hinf, mem_bot] at this
  rw [hs1, mul_one]
  exact ha

include hzC hsup hinf hz in
theorem centralizer_sup_eq {A : Subgroup G} (hAL : A ≤ L) (hAe : IsElementaryAbelian 2 A)
    (hAc : Nat.card A = 64) (hAC : centralizer (A : Set G) ⊓ L = A) :
    centralizer ((A ⊔ zpowers z : Subgroup G) : Set G) = A ⊔ zpowers z := by
  obtain ⟨-, hRe, -⟩ := sup_facts hzC hinf hz hAL hAe hAc
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_centralizer_iff.2 fun r hr =>
    mul_comm_of_isElementaryAbelian hRe hr hx)
  have hxz : x ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hx z (mem_sup_right (mem_zpowers z))).symm
  have hxA : x ∈ centralizer (A : Set G) := mem_centralizer_iff.2 fun a ha =>
    mem_centralizer_iff.1 hx a (mem_sup_left ha)
  exact centralizer_inf_le hzC hsup hAC (Subgroup.mem_inf.2 ⟨hxA, hxz⟩)

include hzC hsup hinf hz hb hnd hV in
theorem conj_set_eq [Finite G] {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) :
    {x | ∃ n ∈ normalizer ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) :
        Set G), n * z * n⁻¹ = x} =
      {x | ∃ g : G, g * z * g⁻¹ = x} ∩
        ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := pullSub φ (pointwiseStabilizer b W) with hA
  set R := A ⊔ zpowers z with hR
  obtain ⟨hAe, hAc, hAC, -⟩ := pullSub_radical hb hnd hV φ hW hd
  have hAL : A ≤ L := pullSub_le φ _
  obtain ⟨-, hRe, hRc⟩ := sup_facts hzC hinf hz hAL hAe hAc
  have hzR : z ∈ R := mem_sup_right (mem_zpowers z)
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, (mem_normalizer_iff.1 hn z).1 hzR⟩
  · rintro ⟨⟨g, rfl⟩, hxR⟩
    set E := R.map (MulAut.conj g⁻¹).toMonoidHom with hE
    have hEH : E ≤ centralizer ({z} : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hc := mul_comm_of_isElementaryAbelian hRe hr hxR
      calc g⁻¹ * r * g * z = g⁻¹ * (r * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * r) * g := by rw [hc]
        _ = z * (g⁻¹ * r * g) := by group
    have : IsElementaryAbelian 2 R := hRe
    have hEe : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
    have hEc : Nat.card E = 128 := by
      rw [hE, card_map_of_injective (MulAut.conj g⁻¹).injective, hRc]
    obtain ⟨l, hl⟩ := exists_conj_eq_of_card_eq hzC hsup hinf hz hb hnd hV φ hW hd hEH hEe hEc
    have hlz : (l : G) * z = z * l := mem_centralizer_iff.1 hzC l l.2
    refine ⟨g * l, mem_normalizer_iff.2 fun h => ?_, ?_⟩
    · constructor
      · intro hh
        have h1 : (l : G) * h * (l : G)⁻¹ ∈ E := by
          rw [hl]
          exact ⟨h, hh, rfl⟩
        obtain ⟨r, hr, hrh⟩ := h1
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hrh
        have : g * l * h * (g * l)⁻¹ = r := by
          calc g * l * h * (g * l)⁻¹ = g * ((l : G) * h * (l : G)⁻¹) * g⁻¹ := by group
            _ = g * (g⁻¹ * r * g) * g⁻¹ := by rw [hrh]
            _ = r := by group
        rw [this]
        exact hr
      · intro hh
        have h1 : g⁻¹ * (g * l * h * (g * l)⁻¹) * g ∈ E := ⟨_, hh, by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
        rw [hl] at h1
        obtain ⟨r, hr, hrh⟩ := h1
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hrh
        have h2 : (l : G) * r * (l : G)⁻¹ = (l : G) * h * (l : G)⁻¹ := by
          rw [hrh]
          group
        have : r = h := by simpa using h2
        rw [← this]
        exact hr
    · show g * l * z * (g * l)⁻¹ = g * z * g⁻¹
      calc g * l * z * (g * l)⁻¹ = g * ((l : G) * z) * (l : G)⁻¹ * g⁻¹ := by group
        _ = g * (z * l) * (l : G)⁻¹ * g⁻¹ := by rw [hlz]
        _ = g * z * g⁻¹ := by group

include hzC hsup hz hb hnd hV in
theorem conj_set_ne [Finite G]
    (hfus : ∃ g : G, g⁻¹ * z * g ∈ centralizer ({z} : Set G) ∧ g⁻¹ * z * g ≠ z)
    {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W) (hd : finrank (ZMod 2) W = 3) :
    {x | ∃ g : G, g * z * g⁻¹ = x} ∩
      ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) ≠ {z} := by
  obtain ⟨g, hgH, hgne⟩ := hfus
  set y := g⁻¹ * z * g with hy
  have hzz : zpowers z ≤ centralizer (L : Set G) := zpowers_le_centralizer hzC
  obtain ⟨u, huL, s, hs, hus⟩ := (mem_sup_of_le_centralizer hzz).1 (hsup ▸ hgH)
  have hz2 := sq_eq_one_of_orderOf hz
  have : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hs2 : s ^ 2 = 1 := by
    rw [pow_two]
    exact mul_self_of_isElementaryAbelian this hs
  have hcomm : u * s = s * u := mem_centralizer_iff.1 (hzz hs) u huL
  have hy2 : y ^ 2 = 1 := by
    rw [hy, pow_two]
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [← pow_two, hz2]; group
  have hu2 : u ^ 2 = 1 := by
    have h1 : y ^ 2 = u ^ 2 * s ^ 2 := by
      rw [← hus, pow_two, pow_two, pow_two]
      calc u * s * (u * s) = u * (s * u) * s := by group
        _ = u * (u * s) * s := by rw [hcomm]
        _ = u * u * (s * s) := by group
    rw [hy2, hs2, mul_one] at h1
    exact h1.symm
  obtain ⟨W₁, hW₁, hd₁, huA⟩ := exists_radical_mem_of_model hb hnd hV φ huL hu2
  obtain ⟨l, hl⟩ := exists_conj_radical_of_model hb hnd hV φ hW₁ hd₁ hW hd
  have hls : (l : G) * s * (l : G)⁻¹ = s := by
    rw [mem_centralizer_iff.1 (hzz hs) l l.2, mul_inv_cancel_right]
  have hlz : (l : G) * z * (l : G)⁻¹ = z := by
    rw [mem_centralizer_iff.1 hzC l l.2, mul_inv_cancel_right]
  intro hset
  have hmem : (l : G) * y * (l : G)⁻¹ ∈ {x | ∃ g : G, g * z * g⁻¹ = x} ∩
      ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) := by
    refine ⟨⟨l * g⁻¹, ?_⟩, ?_⟩
    · show (l : G) * g⁻¹ * z * ((l : G) * g⁻¹)⁻¹ = (l : G) * y * (l : G)⁻¹
      rw [hy]
      group
    have h1 : (l : G) * y * (l : G)⁻¹ = ((l : G) * u * (l : G)⁻¹) * s := by
      calc (l : G) * y * (l : G)⁻¹ = l * (u * s) * (l : G)⁻¹ := by rw [hus]
        _ = ((l : G) * u * (l : G)⁻¹) * ((l : G) * s * (l : G)⁻¹) := by group
        _ = ((l : G) * u * (l : G)⁻¹) * s := by rw [hls]
    rw [SetLike.mem_coe, h1]
    refine mul_mem_sup ?_ hs
    rw [← hl]
    exact ⟨u, huA, rfl⟩
  rw [hset, Set.mem_singleton_iff] at hmem
  apply hgne
  have : y = (l : G)⁻¹ * z * l := by
    rw [← hmem]
    group
  rw [this]
  calc (l : G)⁻¹ * z * l = (l : G)⁻¹ * ((l : G) * z * (l : G)⁻¹) * l := by rw [hlz]
    _ = z := by group

include hzC hsup hinf in
theorem normalizer_inf_eq {A : Subgroup G} (hAL : A ≤ L) :
    normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
        (normalizer (A : Set G) ⊓ L) ⊔ zpowers z ∧
      (normalizer (A : Set G) ⊓ L) ⊓ zpowers z = ⊥ := by
  have hzz : zpowers z ≤ centralizer (L : Set G) := zpowers_le_centralizer hzC
  have hLH : L ≤ centralizer ({z} : Set G) := hsup ▸ le_sup_left
  have hzH : zpowers z ≤ centralizer ({z} : Set G) := hsup ▸ le_sup_right
  have hRN : zpowers z ≤ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) :=
    le_sup_right.trans le_normalizer
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (fun l hl => ?_) (le_inf hRN hzH)),
    by rw [eq_bot_iff, ← hinf]; exact inf_le_inf inf_le_right le_rfl⟩
  · obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨l, hl, s, hs, rfl⟩ := (mem_sup_of_le_centralizer hzz).1 (hsup ▸ hxH)
    have hlN : l ∈ normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) := by
      have := mul_mem hxN (inv_mem (hRN hs))
      simpa using this
    have hlA : l ∈ normalizer (A : Set G) := by
      refine mem_normalizer_iff.2 fun h => ?_
      rw [← sup_inf_eq hzC hinf hAL, Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(mem_normalizer_iff.1 hlN h).1 h1, mul_mem (mul_mem hl h2) (inv_mem hl)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨(mem_normalizer_iff.1 hlN h).2 h1, ?_⟩
        have := mul_mem (mul_mem (inv_mem hl) h2) hl
        simpa [mul_assoc] using this
    exact mul_mem_sup (Subgroup.mem_inf.2 ⟨hlA, hl⟩) hs
  · obtain ⟨hlA, hlL⟩ := Subgroup.mem_inf.1 hl
    have hlz : l ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.2 fun t ht =>
        (mem_centralizer_iff.1 (hzz ht) l hlL).symm)
    exact Subgroup.mem_inf.2 ⟨inf_normalizer_le_normalizer_sup A (zpowers z)
      (Subgroup.mem_inf.2 ⟨hlA, hlz⟩), hLH hlL⟩

abbrev linOf (g : bilinIsometryGroup b) : V →ₗ[ZMod 2] V :=
  ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)

include hb hnd hV in
theorem exists_restrict_hom {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) :
    ∃ ρ : (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L : Subgroup G) →*
        LinearMap.GeneralLinearGroup (ZMod 2) W,
      Function.Surjective ρ ∧
      ρ.ker = (pullSub φ (pointwiseStabilizer b W)).subgroupOf
        (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L) ∧
      ∀ (n : (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L : Subgroup G))
        (w : W), (((ρ n : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w : V) =
          linOf (φ ⟨n, (Subgroup.mem_inf.1 n.2).2⟩) w := by
  obtain ⟨-, -, -, -, hsurj, hker⟩ := pointwiseStabilizer_lagrangian hb hnd hV hW hd
  obtain ⟨-, -, -, hNL⟩ := pullSub_radical hb hnd hV φ hW hd
  set A := pullSub φ (pointwiseStabilizer b W) with hA
  set N := normalizer (A : Set G) ⊓ L with hN
  have hmem : ∀ n : N, (φ.toMonoidHom.comp (inclusion (inf_le_right : N ≤ L))) n ∈
      subspaceStabilizer b W := fun n => by
    have h : (n : G) ∈ pullSub φ (subspaceStabilizer b W) := by
      rw [← hNL]
      exact n.2
    obtain ⟨_, hφ⟩ := mem_pullSub.1 h
    exact hφ
  set σ : N →* subspaceStabilizer b W :=
    MonoidHom.codRestrict (φ.toMonoidHom.comp (inclusion inf_le_right)) _ hmem with hσ
  refine ⟨(restrictSubspace b W).comp σ, fun A' => ?_, ?_, fun n w => rfl⟩
  · obtain ⟨g, hg⟩ := hsurj A'
    have hgN : ((φ.symm g : L) : G) ∈ N := by
      rw [hNL, mem_pullSub]
      exact ⟨(φ.symm g).2, by simp⟩
    refine ⟨⟨_, hgN⟩, ?_⟩
    rw [MonoidHom.comp_apply, ← hg]
    congr 1
    apply Subtype.ext
    show φ ((inclusion (inf_le_right : N ≤ L)) ⟨_, hgN⟩) = g
    have : (inclusion (inf_le_right : N ≤ L)) ⟨_, hgN⟩ = φ.symm g := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  · ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_restrictSubspace,
      mem_subgroupOf, mem_subgroupOf, mem_pullSub]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩

include hb hnd hV in
theorem coordinates {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) :
    (∀ (a : G) (ha : a ∈ L), a ∈ pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ↔
      ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Bᵀ = B ∧
        LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1) ∧
    ∀ (n : G)
      (hn : n ∈ normalizer (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G) ⊓ L),
      IsUnit (LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ ∧
      (∀ j : Fin 3, linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩) (e (Sum.inl j)) =
        ∑ i, (LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ i j •
          e (Sum.inl i)) ∧
      ∀ (a : G) (ha : a ∈ L) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
        LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
        LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩ * φ ⟨a, ha⟩ *
          (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩)⁻¹)) =
          fromBlocks 1 ((LinearMap.toMatrix e e
              (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ * B *
            ((LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁)ᵀ)
            0 1 := by
  have hW := isTotallyIsotropic_lagrangianOf he
  have hd : finrank (ZMod 2) (lagrangianOf e) = 3 := finrank_lagrangianOf
  obtain ⟨-, -, -, hNL⟩ := pullSub_radical hb hnd hV φ hW hd
  refine ⟨fun a ha => ?_, fun n hn => ?_⟩
  · rw [mem_pullSub]
    exact ⟨fun ⟨_, h⟩ => (mem_pointwiseStabilizer_iff_toMatrix he _).1 h,
      fun h => ⟨ha, (mem_pointwiseStabilizer_iff_toMatrix he _).2 h⟩⟩
  have hgmem : φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩ ∈ subspaceStabilizer b (lagrangianOf e) := by
    have h : n ∈ pullSub φ (subspaceStabilizer b (lagrangianOf e)) := by
      rw [← hNL]
      exact hn
    obtain ⟨_, hφ⟩ := mem_pullSub.1 h
    exact hφ
  set g : subspaceStabilizer b (lagrangianOf e) := ⟨_, hgmem⟩ with hg
  have hD : (LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ =
      LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
        ((restrictSubspace b (lagrangianOf e) g :
          LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
            lagrangianOf e →ₗ[ZMod 2] lagrangianOf e) := by
    rw [toMatrix_restrictSubspace he g, spMatrixOf_spCoord]
  refine ⟨?_, fun j => ?_, fun a ha B hB hr => ?_⟩
  · rw [hD, ← coe_basisGL]
    exact Units.isUnit _
  · rw [hD]
    have h1 := (lagrangianBasis e).sum_repr
      (((restrictSubspace b (lagrangianOf e) g :
        LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
          lagrangianOf e →ₗ[ZMod 2] lagrangianOf e) (lagrangianBasis e j))
    have h2 := congrArg (fun w : lagrangianOf e => (w : V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_lagrangianBasis,
      restrictSubspace_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.toMatrix_apply]
  · have := spMatrixOf_spCoord_conj he g (r := φ ⟨a, ha⟩) (by rw [spMatrixOf_spCoord]; exact hr) hB
    rw [spMatrixOf_spCoord, ← hD] at this
    exact this

end Setting

universe u

theorem standard_binary_symplectic_six_cyclic_kernel_and_first_fusion {G : Type} [Group G]
    [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
    z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
    L ⊓ zpowers z = ⊥ ∧
    {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (centralizer ({z} : Set G) : Set G) ≠ {z} ∧
    ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      {b : BilinForm (ZMod 2) V}, b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
      ∀ (φ : L ≃* bilinIsometryGroup b) {W : Submodule (ZMod 2) V},
        IsTotallyIsotropic b W → finrank (ZMod 2) W = 3 →
        pullSub φ (pointwiseStabilizer b W) ⊓ zpowers z = ⊥ ∧
        IsElementaryAbelian 2 (pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) ∧
        Nat.card (pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) = 128 ∧
        centralizer ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) =
          pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z ∧
        {x | ∃ n ∈ normalizer ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) :
            Set G), n * z * n⁻¹ = x} =
          {x | ∃ g : G, g * z * g⁻¹ = x} ∩
            ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) ∧
        {x | ∃ g : G, g * z * g⁻¹ = x} ∩
            ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) ≠ {z} ∧
        (∃ ψ : normalizer ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) :
            Set G) →* MulAut (pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G),
          (∀ n r, (ψ n r : G) = n * r * (n : G)⁻¹) ∧
          ψ.ker = (pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z).subgroupOf
            (normalizer ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) :
              Set G))) ∧
        normalizer ((pullSub φ (pointwiseStabilizer b W) ⊔ zpowers z : Subgroup G) : Set G) ⊓
            centralizer ({z} : Set G) =
          (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L) ⊔ zpowers z ∧
        (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L) ⊓ zpowers z = ⊥ ∧
        (∃ ρ : (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L : Subgroup G) →*
            LinearMap.GeneralLinearGroup (ZMod 2) W,
          Function.Surjective ρ ∧
          ρ.ker = (pullSub φ (pointwiseStabilizer b W)).subgroupOf
            (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L) ∧
          ∀ (n : (normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L : Subgroup G))
            (w : W), (((ρ n : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w : V) =
              linOf (φ ⟨n, (Subgroup.mem_inf.1 n.2).2⟩) w) ∧
        ∀ e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V, IsSymplecticBasis b e → W = lagrangianOf e →
          (∀ (a : G) (ha : a ∈ L), a ∈ pullSub φ (pointwiseStabilizer b W) ↔
            ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Bᵀ = B ∧
              LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1) ∧
          ∀ (n : G) (hn : n ∈ normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L),
            IsUnit (LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ ∧
            (∀ j : Fin 3, linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩) (e (Sum.inl j)) =
              ∑ i, (LinearMap.toMatrix e e
                (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ i j • e (Sum.inl i)) ∧
            ∀ (a : G) (ha : a ∈ L) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
              LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
              LinearMap.toMatrix e e (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩ * φ ⟨a, ha⟩ *
                (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩)⁻¹)) =
                fromBlocks 1 ((LinearMap.toMatrix e e
                    (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁ * B *
                  ((LinearMap.toMatrix e e
                    (linOf (φ ⟨n, (Subgroup.mem_inf.1 hn).2⟩))).toBlocks₁₁)ᵀ) 0 1 := by
  obtain ⟨hTC, hsup, hinf, -, -, hfus⟩ :=
    standard_binary_symplectic_six_initial hG hL hLn hZ hmodel T hT hzT hz hH
  have hTz := standard_binary_symplectic_six_sylow_eq hG hL hLn hZ hmodel T hT hzT hz hH
  rw [hTz] at hsup hinf hTC
  have hzC : z ∈ centralizer (L : Set G) := hTC (mem_zpowers z)
  refine ⟨hTz, hzC, hsup, hinf, ?_, fun {V} _ _ _ b hb hnd hV φ W hW hd => ?_⟩
  · intro hset
    obtain ⟨g, hgH, hgne⟩ := hfus
    have hmem : g⁻¹ * z * g ∈ {x | ∃ g : G, g * z * g⁻¹ = x} ∩
        (centralizer ({z} : Set G) : Set G) := ⟨⟨g⁻¹, by group⟩, hgH⟩
    rw [hset, Set.mem_singleton_iff] at hmem
    exact hgne hmem
  obtain ⟨hAe, hAc, hAC, -⟩ := pullSub_radical hb hnd hV φ hW hd
  have hAL := pullSub_le φ (pointwiseStabilizer b W)
  obtain ⟨hAz, hRe, hRc⟩ := sup_facts hzC hinf hz hAL hAe hAc
  have hRC := centralizer_sup_eq hzC hsup hinf hz hAL hAe hAc hAC
  obtain ⟨hNH, hNz⟩ := normalizer_inf_eq hzC hsup hinf hAL
  refine ⟨hAz, hRe, hRc, hRC, conj_set_eq hzC hsup hinf hz hb hnd hV φ hW hd,
    conj_set_ne hzC hsup hz hb hnd hV φ hfus hW hd,
    ⟨conjNormalizer _, coe_conjNormalizer _, ker_conjNormalizer hRC⟩, hNH, hNz,
    exists_restrict_hom hb hnd hV φ hW hd, fun e he hWe => ?_⟩
  subst hWe
  exact coordinates hb hnd hV φ he

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
