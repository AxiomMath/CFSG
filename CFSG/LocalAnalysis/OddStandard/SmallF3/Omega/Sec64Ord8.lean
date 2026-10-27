module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64TwoA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63ArrowAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63TwoGroup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Suzuki

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
variable {G : Type} [Group G]
private lemma sec64_card_m2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
private lemma sec64_card_m4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
private lemma sec64_E4_exp (z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    z ^ 2 = 1 := by
  revert z; decide
private lemma sec64_Z4_exp (z : Multiplicative (ZMod 4)) : z ^ 4 = 1 := by
  revert z; decide
private lemma sec64_sq_mem {G : Type} [Group G] {R K : Subgroup G} {F : Type} [Group F]
    (φ : ↥R →* F) (hker : φ.ker = K.subgroupOf R) (hexp : ∀ z : F, z ^ 2 = 1)
    {s : G} (hs : s ∈ R) : s ^ 2 ∈ K := by
  have hmem : (⟨s, hs⟩ : ↥R) ^ 2 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hexp (φ ⟨s, hs⟩)
  rw [hker] at hmem
  simpa using (Subgroup.mem_subgroupOf.mp hmem)
private lemma sec64_mem_U_eq {G : Type} [Group G] [Finite G] (U : Subgroup G)
    (hcard : Nat.card U = 2) (hcyc : IsCyclic ↥U) {y : G} (hy : orderOf y = 2)
    (hyU : y ∈ U) {u : G} (hu : u ∈ U) : u = 1 ∨ u = y := by
  have hdvd : orderOf u ∣ 2 := by
    have h := Subgroup.orderOf_dvd_natCard U hu
    rwa [hcard] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · exact Or.inr (sec64_unique_inv hcyc hu hyU h2 hy)
private lemma sec64_relIndex_eq_card {G : Type} [Group G] [Finite G] {R H : Subgroup G}
    {F : Type} [Group F] [Finite F] (hQ : QuotEquivTo R (R ⊓ H) F) :
    H.relIndex R = Nat.card F := by
  obtain ⟨φ, hφsurj, hφker⟩ := hQ
  have hker : H.subgroupOf R = φ.ker :=
    (hφker.trans (Subgroup.inf_subgroupOf_left H R)).symm
  calc H.relIndex R = (H.subgroupOf R).index := rfl
    _ = φ.ker.index := by rw [hker]
    _ = Nat.card φ.range := Subgroup.index_ker φ
    _ = Nat.card F := by
        rw [MonoidHom.range_eq_top_of_surjective φ hφsurj, Subgroup.card_top]
private def sec64_prodHom {M N P : Type} [Monoid M] [Monoid N] [Group P]
    (f : M →* P) (g : N →* P) (hcomm : ∀ m n, f m * g n = g n * f m) : M × N →* P where
  toFun := fun p => f p.1 * g p.2
  map_one' := by
    show f 1 * g 1 = 1
    rw [map_one f, map_one g, one_mul]
  map_mul' := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩
    simp only [Prod.mk_mul_mk, map_mul]
    calc f p1 * f q1 * (g p2 * g q2)
        = f p1 * (f q1 * g p2) * g q2 := by group
      _ = f p1 * (g p2 * f q1) * g q2 := by rw [hcomm q1 p2]
      _ = (f p1 * g p2) * (f q1 * g q2) := by group
theorem sec64_E8 [Finite G] {T H : Subgroup G} {x y : G} (c : Sec64Cfg T H x y)
    (hU2 : Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) = 2)
    (hTR : T ⊓ centralizer ({y} : Set G) ≠ T)
    (hQ : QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G)) ∧
      Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8 := by
  classical
  let R : Subgroup G := T ⊓ centralizer ({y} : Set G)
  let U : Subgroup G := R ⊓ H
  have hQ0 : QuotEquivTo (T ⊓ centralizer ({y} : Set G))
      (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := hQ
  obtain ⟨φ, _hφsurj, hφker⟩ := hQ
  have hyR : y ∈ R := ⟨c.hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyU : y ∈ U := c.mem_U
  have hyne : y ≠ 1 := by
    intro h
    have : orderOf y = 1 := orderOf_eq_one_iff.mpr h
    rw [c.hy] at this
    norm_num at this
  have hUmem : ∀ u ∈ U, u = 1 ∨ u = y := fun u hu =>
    sec64_mem_U_eq U hU2 c.hU c.hy hyU hu
  have hcent : ∀ r ∈ T, r * y = y * r → r ∈ R := fun r hrT hry =>
    ⟨hrT, Subgroup.mem_centralizer_singleton_iff.mpr hry⟩
  have hR2 : ∀ r ∈ R, r ^ 2 = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hrR, hr2ne⟩ := hcon
    have hr2U : r ^ 2 ∈ U := sec64_sq_mem φ hφker sec64_E4_exp hrR
    have hr2y : r ^ 2 = y := by
      rcases hUmem (r ^ 2) hr2U with h | h
      · exact absurd h hr2ne
      · exact h
    have hchar : ∀ a ∈ normalizer (R : Set G), ∀ q ∈ U, a * q * a⁻¹ ∈ U := by
      intro a ha q hq
      rcases hUmem q hq with hq1 | hqy
      · subst hq1; simp
      · subst hqy
        have harR : a * r * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp ha r).mp hrR
        have hsq : (a * r * a⁻¹) ^ 2 ∈ U := sec64_sq_mem φ hφker sec64_E4_exp harR
        have heq : (a * r * a⁻¹) ^ 2 = a * r ^ 2 * a⁻¹ := by
          rw [pow_two, pow_two]; group
        rw [heq, hr2y] at hsq
        exact hsq
    exact hTR (sec63_eq_of_char_cyclic c.isPGroup inf_le_left c.hy c.mem_U c.hU hcent hchar)
  refine ⟨?_, ?_⟩
  · constructor
    · refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
      have ha2 : (a : G) * a = 1 := by simpa [pow_two] using hR2 (a : G) a.2
      have hb2 : (b : G) * b = 1 := by simpa [pow_two] using hR2 (b : G) b.2
      have hab : (a : G) * b * (a * b) = 1 := by
        simpa [pow_two] using hR2 ((a : G) * b) (mul_mem a.2 b.2)
      calc (a : G) * b = ((a : G) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
        _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
        _ = (b : G) * (a : G) := by
            rw [inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_left ha2]
    · intro x hx; exact hR2 x hx
  · have hrel : H.relIndex R = 4 := by
      rw [sec64_relIndex_eq_card hQ0, Nat.card_prod, sec64_card_m2]
    have hU2' : Nat.card ↥(R ⊓ H) = 2 := hU2
    rw [sec64_card_eq R H, hU2', hrel]
theorem sec64_Z2Z4 [Finite G] {T H : Subgroup G} {x y : G} (c : Sec64Cfg T H x y)
    (hU2 : Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) = 2)
    (hTR : T ⊓ centralizer ({y} : Set G) ≠ T)
    (hQ : QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 4))) :
    Nonempty (↥(T ⊓ centralizer ({y} : Set G)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) := by
  classical
  let R : Subgroup G := T ⊓ centralizer ({y} : Set G)
  let U : Subgroup G := R ⊓ H
  have hQ0 : QuotEquivTo (T ⊓ centralizer ({y} : Set G))
      (T ⊓ centralizer ({y} : Set G) ⊓ H) (Multiplicative (ZMod 4)) := hQ
  obtain ⟨φ, hφsurj, hφker⟩ := hQ
  have hyR : y ∈ R := ⟨c.hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyU : y ∈ U := c.mem_U
  have hyne : y ≠ 1 := by
    intro h
    have : orderOf y = 1 := orderOf_eq_one_iff.mpr h
    rw [c.hy] at this
    norm_num at this
  have hUmem : ∀ u ∈ U, u = 1 ∨ u = y := fun u hu =>
    sec64_mem_U_eq U hU2 c.hU c.hy hyU hu
  have hcent : ∀ r ∈ T, r * y = y * r → r ∈ R := fun r hrT hry =>
    ⟨hrT, Subgroup.mem_centralizer_singleton_iff.mpr hry⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ↥R, φ c0 = Multiplicative.ofAdd (1 : ZMod 4) := by
    obtain ⟨c0, hc0⟩ := hφsurj (Multiplicative.ofAdd (1 : ZMod 4))
    exact ⟨c0, hc0⟩
  have hφc0pow : ∀ k : ZMod 4, φ (c0 ^ k.val) = Multiplicative.ofAdd k := by
    intro k
    rw [map_pow, hc0, ← ofAdd_nsmul]
    congr 1
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  have hc04U : (c0 : G) ^ 4 ∈ U := by
    have hmem : c0 ^ 4 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hc0]
      exact sec64_Z4_exp _
    rw [hφker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hc04 : (c0 : G) ^ 4 = 1 := by
    rcases hUmem ((c0 : G) ^ 4) hc04U with h | h
    · exact h
    · exfalso
      have hRz : R = Subgroup.zpowers (c0 : G) := by
        apply le_antisymm
        · intro s hs
          obtain ⟨k, hk⟩ : ∃ k : ZMod 4, φ ⟨s, hs⟩ = Multiplicative.ofAdd k :=
            ⟨(φ ⟨s, hs⟩).toAdd, (ofAdd_toAdd _).symm⟩
          have hmem : (⟨s, hs⟩ : ↥R) * (c0 ^ k.val)⁻¹ ∈ φ.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hφc0pow k, hk, mul_inv_cancel]
          rw [hφker] at hmem
          have hu : s * ((c0 : G) ^ k.val)⁻¹ ∈ U := Subgroup.mem_subgroupOf.mp hmem
          rcases hUmem _ hu with h1 | hy'
          · have hs' : s = (c0 : G) ^ k.val := by
              have hc := congrArg (fun x : G => x * (c0 : G) ^ k.val) h1
              simpa using hc
            rw [hs']
            exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (c0 : G)) k.val
          · have hs' : s = y * (c0 : G) ^ k.val := by
              have hc := congrArg (fun x : G => x * (c0 : G) ^ k.val) hy'
              simpa using hc
            rw [hs', ← h]
            exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers (c0 : G)) 4)
              (Subgroup.pow_mem _ (Subgroup.mem_zpowers (c0 : G)) k.val)
        · exact Subgroup.zpowers_le.mpr c0.2
      have hRcyc : IsCyclic ↥R := by
        rw [hRz]
        exact Subgroup.isCyclic_zpowers (c0 : G)
      have hRT : R = T :=
        sec63_eq_of_char_cyclic c.isPGroup inf_le_left c.hy hyR hRcyc hcent
          (fun a ha q hq => (Subgroup.mem_normalizer_iff.mp ha q).mp hq)
      exact hTR hRT
  have hycentral : ∀ r ∈ R, y * r = r * y := by
    intro r hr
    have hconj : r * y * r⁻¹ ∈ U := c.norm_U (r := r) (u := y) hr hyU
    rcases hUmem _ hconj with h | h
    · exfalso
      have : y = 1 := by
        calc y = r⁻¹ * (r * y * r⁻¹) * r := by group
          _ = 1 := by rw [h]; group
      exact hyne this
    · calc y * r = (r * y * r⁻¹) * r := by rw [h]
        _ = r * y := by group
  have hyc0 : Commute (⟨y, hyR⟩ : ↥R) c0 := Subtype.ext (hycentral (c0 : G) c0.2)
  have hy2 : y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [c.hy] at h
  let Fy : ℤ →+ Additive ↥R := zmultiplesHom (Additive ↥R) (Additive.ofMul (⟨y, hyR⟩ : ↥R))
  have hFy : Fy 2 = 0 := by
    change (zmultiplesHom (Additive ↥R) (Additive.ofMul (⟨y, hyR⟩ : ↥R))) 2 = 0
    rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_ofNat]
    have hyR2 : (⟨y, hyR⟩ : ↥R) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hy2
    rw [hyR2]
    rfl
  let Fc : ℤ →+ Additive ↥R := zmultiplesHom (Additive ↥R) (Additive.ofMul c0)
  have hFc : Fc 4 = 0 := by
    change (zmultiplesHom (Additive ↥R) (Additive.ofMul c0)) 4 = 0
    rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_ofNat]
    have hcR4 : c0 ^ 4 = 1 := by
      apply Subtype.ext
      simpa using hc04
    rw [hcR4]
    rfl
  let fy : Multiplicative (ZMod 2) →* ↥R :=
    AddMonoidHom.toMultiplicativeLeft (ZMod.lift 2 ⟨Fy, hFy⟩)
  let fc : Multiplicative (ZMod 4) →* ↥R :=
    AddMonoidHom.toMultiplicativeLeft (ZMod.lift 4 ⟨Fc, hFc⟩)
  have fy_apply : ∀ a : ZMod 2, fy (Multiplicative.ofAdd a) = (⟨y, hyR⟩ : ↥R) ^ a.val := by
    intro a
    simp only [fy, Fy, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
      toAdd_ofAdd]
    conv_lhs => rw [show a = ((a.val : ℤ) : ZMod 2) by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]]
    rw [ZMod.lift_coe, zmultiplesHom_apply, ← ofMul_zpow, toMul_ofMul, zpow_natCast]
  have fc_apply : ∀ k : ZMod 4, fc (Multiplicative.ofAdd k) = c0 ^ k.val := by
    intro k
    simp only [fc, Fc, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
      toAdd_ofAdd]
    conv_lhs => rw [show k = ((k.val : ℤ) : ZMod 4) by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]]
    rw [ZMod.lift_coe, zmultiplesHom_apply, ← ofMul_zpow, toMul_ofMul, zpow_natCast]
  have hcomm : ∀ m n, fy m * fc n = fc n * fy m := by
    intro m n
    rw [show m = Multiplicative.ofAdd m.toAdd from (ofAdd_toAdd m).symm,
      show n = Multiplicative.ofAdd n.toAdd from (ofAdd_toAdd n).symm,
      fy_apply m.toAdd, fc_apply n.toAdd]
    exact (hyc0.pow_pow m.toAdd.val n.toAdd.val).eq
  let e : Multiplicative (ZMod 2) × Multiplicative (ZMod 4) →* ↥R := sec64_prodHom fy fc hcomm
  have hUmemR : ∀ u : ↥R, u ∈ U.subgroupOf R → u = 1 ∨ u = ⟨y, hyR⟩ := by
    intro u hu
    have huG : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    rcases hUmem (u : G) huG with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hsurj : Function.Surjective e := by
    intro r
    set k : ZMod 4 := (φ r).toAdd with hk
    have hφr : φ r = Multiplicative.ofAdd k := by
      rw [hk]
      exact (ofAdd_toAdd (φ r)).symm
    have hφfcb : φ (fc (Multiplicative.ofAdd k)) = Multiplicative.ofAdd k := by
      rw [fc_apply k]
      exact hφc0pow k
    have hkeru : r * (fc (Multiplicative.ofAdd k))⁻¹ ∈ U.subgroupOf R := by
      rw [← hφker, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hφfcb, hφr, mul_inv_cancel]
    rcases hUmemR _ hkeru with hu | hu
    · refine ⟨(1, Multiplicative.ofAdd k), ?_⟩
      have hr : r = fc (Multiplicative.ofAdd k) := by
        have hc := congrArg (fun x : ↥R => x * fc (Multiplicative.ofAdd k)) hu
        simpa using hc
      show fy 1 * fc (Multiplicative.ofAdd k) = r
      simp [hr]
    · refine ⟨(Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd k), ?_⟩
      have hr : r = (⟨y, hyR⟩ : ↥R) * fc (Multiplicative.ofAdd k) := by
        have hc := congrArg (fun x : ↥R => x * fc (Multiplicative.ofAdd k)) hu
        simpa using hc
      show fy (Multiplicative.ofAdd (1 : ZMod 2)) * fc (Multiplicative.ofAdd k) = r
      rw [fy_apply, hr]
      have hv : (1 : ZMod 2).val = 1 := by decide
      rw [hv, pow_one]
  have hcardR : Nat.card ↥R = 8 := by
    have hrel : H.relIndex R = 4 := by
      rw [sec64_relIndex_eq_card hQ0, sec64_card_m4]
    rw [sec64_card_eq R H, (show Nat.card ↥(R ⊓ H) = 2 from hU2), hrel]
  have hdom : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) = 8 := by
    rw [Nat.card_prod, sec64_card_m2, sec64_card_m4]
  have hbij : Function.Bijective e := by
    haveI : Fintype (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) := Fintype.ofFinite _
    haveI : Fintype ↥R := Fintype.ofFinite _
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨hsurj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hdom, hcardR]
  exact ⟨(MulEquiv.ofBijective e hbij).symm⟩
theorem sec64_case_two [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (halt : Sec64Tri T H y)
    (hU2 : Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) = 2)
    (hTR : ¬ T ≤ centralizer ({y} : Set G)) : Sec64Out T H y := by
  have hTR' : T ⊓ centralizer ({y} : Set G) ≠ T := fun h => hTR (inf_eq_left.mp h)
  have hxy_ne : x ≠ y := fun h => c.hxH (h ▸ c.hyH)
  unfold Sec64Out Sec64Tri at *
  rcases halt with hrel | hrest
  · left
    have hcardR : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 4 :=
      sec63_card_four hrel hU2 c.mem_R c.hxH
    have hle : CFSG.Open.pRank 2 T ≤ 2 := sec6_suzuki_four c.isPGroup c.hyT c.hy hcardR
    have hge : 2 ≤ CFSG.Open.pRank 2 T :=
      sec64_two_le_pRank c.hx c.hy c.hxy hxy_ne c.hxT c.hyT
    omega
  · rcases hrest with ⟨hE8, hQ⟩ | hQ
    · right
      have hF4 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
        rw [Nat.card_prod, sec64_card_m2]
      have hres := sec64_E8 c hU2 hTR' hQ
      exact ⟨sec64_not_relIndex_le_two hQ hF4, hE8 hres.1 hres.2 hU2 hTR'⟩
    · right
      exact ⟨sec64_not_relIndex_le_two hQ (by rw [sec64_card_m4]),
        hout.lemma12 G T c.isPGroup y c.hyT c.hy (sec64_Z2Z4 c hU2 hTR' hQ)⟩
end CFSG.OddStandard.SmallF3.Omega
