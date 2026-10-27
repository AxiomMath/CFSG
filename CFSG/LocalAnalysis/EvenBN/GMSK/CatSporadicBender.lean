module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootGeneric
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicSmall
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section FixedRootDatumOf

variable {T : StdType} {D : Type} [Group D] {n : ℕ} {α : MulAut D} {S : Subgroup D}

theorem FixedRootDatumOf.isComponent (d : FixedRootDatumOf T D n α S) (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.IsComponent (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) := by
  have e := Subgroup.subgroupOfEquivOfLe d.le_fixed
  have : IsSimpleGroup (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) :=
    e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnab
  have hnab' : ∃ x y : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), x * y ≠ y * x := by
    refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h'
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').1, d.normal.isSubnormal⟩

theorem FixedRootDatumOf.false_of_comps (d : FixedRootDatumOf T D n α S) (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q)
    (hQS : ¬ Q S) (hC : CompsSatisfy (α.toMonoidHom.eqLocus (MonoidHom.id D)) Q) : False :=
  hQS (hQ _ _ (Subgroup.subgroupOfEquivOfLe d.le_fixed).symm (hC _ (d.isComponent hs hnab)))

theorem SporadicBender.center_eq_bot_of_subgroup_nonabelian (hD : IsSimpleGroup D)
    (hnab : ∃ a b : S, a * b ≠ b * a) : center D = ⊥ := by
  obtain ⟨a, b, hab⟩ := hnab
  have hnab' : ∃ x y : D, x * y ≠ y * x :=
    ⟨a, b, fun h' => hab (Subtype.ext (by simpa only [coe_mul] using h'))⟩
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab').2

theorem FixedRootDatumOf.false_of_inner_comps (hD : IsSimpleGroup D)
    (d : FixedRootDatumOf T D n α S) (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hin : α ∈ inner D) {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q) (hQS : ¬ Q S)
    (hC : ∀ t : D, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set D)) Q) : False := by
  obtain ⟨t, ht, rfl⟩ := Sporadic.exists_involution_of_mem_inner
    (SporadicBender.center_eq_bot_of_subgroup_nonabelian hD hnab) d.orderOf_eq hin
  exact d.false_of_comps hs hnab hQ hQS
    (CompsSatisfy.of_mulEquiv hQ (MulEquiv.subgroupCongr (Sporadic.eqLocus_conj t)) (hC t ht))

theorem FixedRootDatumOf.false_of_outer_comps (d : FixedRootDatumOf T D n α S)
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hout : α ∉ inner D)
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q) (hQS : ¬ Q S)
    (hC : ∀ β : MulAut D, orderOf β = 2 → β ∉ inner D →
      CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Q) : False :=
  d.false_of_comps hs hnab hQ hQS (CompsSatisfy.of_mulEquiv hQ
    (MulEquiv.subgroupCongr (Sporadic.eqLocus_eq_fixSub α)) (hC α d.orderOf_eq hout))

theorem FixedRootDatumOf.card_dvd_card_fixed (d : FixedRootDatumOf T D n α S) :
    Nat.card S ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.le_fixed).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem SporadicBender.card_inner_eq_of_center_eq_bot {N : Type*} [Group N] (hZ : center N = ⊥) :
    Nat.card (inner N) = Nat.card N := by
  have hinj : Function.Injective (MulAut.conj : N →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [mem_center_iff]
    intro x
    have h := congrArg (fun φ : MulAut N => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  exact Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv

theorem SporadicBender.card_dvd_of_normal_of_odd_outer {C : Type*} [Group C] [Finite C]
    (N : Subgroup C) [N.Normal] (hZ : center N = ⊥)
    (hout : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer N)))
    (P : Subgroup C) (hP : IsPGroup 2 P) :
    Nat.card P ∣ Nat.card ↥(P ⊓ centralizer (N : Set C)) * Nat.card N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : P →* MulAut N := (MulAut.conjNormal : C →* MulAut N).comp P.subtype with hf
  have hker : f.ker.map P.subtype = P ⊓ centralizer (N : Set C) := by
    ext x
    simp only [mem_map, MonoidHom.mem_ker, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun m hm => ?_⟩
      have h1 := congrArg (fun φ : MulAut N => ((φ ⟨m, hm⟩ : N) : C)) hy
      simp only [hf, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply] at h1
      calc m * (y : C) = (y : C) * m * (y : C)⁻¹ * y := by rw [h1]
        _ = y * m := by group
    · rintro ⟨hxP, hx⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      refine MulEquiv.ext fun m => Subtype.ext ?_
      simp only [hf, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply]
      rw [← hx m m.2, mul_inv_cancel_right]
  have hkercard : Nat.card f.ker = Nat.card ↥(P ⊓ centralizer (N : Set C)) := by
    rw [← hker, card_map_of_injective P.subtype_injective]
  have hcard : Nat.card P = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hp : IsPGroup 2 f.range := hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Finite (MulAut N) :=
    Finite.of_injective (fun φ : MulAut N => (φ : N → N)) DFunLike.coe_injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card f.range ∣
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer N) * Nat.card N := by
    rw [← SporadicBender.card_inner_eq_of_center_eq_bot hZ,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (2 ^ k)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer N)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hout)
  have hrange : Nat.card f.range ∣ Nat.card N := by
    rw [hk] at hdvd ⊢
    exact hcop.dvd_of_dvd_mul_left hdvd
  rw [hcard, hkercard]
  exact Nat.mul_dvd_mul_left _ hrange

theorem FixedRootDatumOf.two_pow_dvd_of_odd_outer [Finite D] (d : FixedRootDatumOf T D n α S)
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hout : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))) {a : ℕ}
    (ha : 2 ^ a ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D))) :
    2 ^ a ∣ 2 * Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D) with hCdef
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 ha
  have hPp : IsPGroup 2 P := IsPGroup.of_card hP
  set N := S.subgroupOf C
  have : N.Normal := d.normal
  let eN : N ≃* S := Subgroup.subgroupOfEquivOfLe d.le_fixed
  have := hs
  have : IsSimpleGroup N := eN.isSimpleGroup
  have hNnab : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    refine ⟨eN.symm x, eN.symm y, fun h' => hxy ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eN h'
  have hZN : center N = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hNnab).2
  have houtN : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer N)) := by
    rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eN).toEquiv]
  have hdvd := SporadicBender.card_dvd_of_normal_of_odd_outer N hZN houtN P hPp
  set Q := (P ⊓ centralizer (N : Set C)).map C.subtype with hQdef
  have hQle : Q ≤ C ⊓ centralizer (S : Set D) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨x.2, ?_⟩
    rw [mem_centralizer_iff]
    intro s hs
    have h1 := (mem_centralizer_iff.1 (mem_inf.1 hx).2) ⟨s, d.le_fixed hs⟩
      (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hs)
    exact congrArg Subtype.val h1
  have hQp : IsPGroup 2 Q := (hPp.to_le inf_le_left).map C.subtype
  have hQcard : Nat.card Q = Nat.card ↥(P ⊓ centralizer (N : Set C)) :=
    card_map_of_injective C.subtype_injective
  have hle := (d.rankOne Q hQle hQp).1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hQ2 : Nat.card Q ∣ 2 := by
    rw [hk] at hle ⊢
    rcases k with _ | _ | k
    · exact one_dvd _
    · exact dvd_rfl
    · exfalso
      have : 4 ≤ 2 ^ (k + 1 + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [hP, ← hQcard, Nat.card_congr eN.toEquiv] at hdvd
  exact hdvd.trans (Nat.mul_dvd_mul_right hQ2 _)

theorem FixedRootDatumOf.mem_of_prime_of_outer [Finite D] (d : FixedRootDatumOf T D n α S)
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hout : α ∉ inner D) {t : D}
    (htS : t ∈ S)
    (hcore : CFSG.oddCore ↥(α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D)) =
      ⊥)
    {x : D} (hx : x ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓ centralizer ({t} : Set D))
    {r : ℕ} (hr : r.Prime) (hxr : orderOf x = r)
    (hrO : ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) : x ∈ S := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D) with hCdef
  set N := S.subgroupOf C
  have : N.Normal := d.normal
  have hSC : S ≤ C := d.le_fixed
  have hnorm : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    intro c hc s hs
    have := d.normal.conj_mem ⟨s, hSC hs⟩ (by rw [mem_subgroupOf]; exact hs) ⟨c, hc⟩
    rwa [mem_subgroupOf] at this
  set Z := C ⊓ centralizer (S : Set D) with hZdef
  have hZodd : Odd (Nat.card Z) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 hev
    have hP : zpowers (z : D) ≤ C ⊓ centralizer (S : Set D) := zpowers_le.2 z.2
    have hPp : IsPGroup 2 (zpowers (z : D)) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hbot := (d.rankOne _ hP hPp).2 hout
    have hz1 : (z : D) = 1 := by
      have : (z : D) ∈ zpowers (z : D) := mem_zpowers _
      rwa [hbot, mem_bot] at this
    rw [show z = 1 from Subtype.ext hz1, orderOf_one] at hz
    omega
  have hZle : Z ≤ C ⊓ centralizer ({t} : Set D) := by
    intro z hz
    refine mem_inf.2 ⟨(mem_inf.1 hz).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.1 (mem_inf.1 hz).2) t htS).symm
  have hZn : (Z.subgroupOf (C ⊓ centralizer ({t} : Set D))).Normal := by
    refine ⟨fun z hz c => ?_⟩
    rw [mem_subgroupOf] at hz ⊢
    obtain ⟨hzC, hzS⟩ := mem_inf.1 hz
    have hcC : (c : D) ∈ C := (mem_inf.1 c.2).1
    refine mem_inf.2 ⟨?_, ?_⟩
    · simp only [coe_mul, coe_inv]
      exact C.mul_mem (C.mul_mem hcC hzC) (C.inv_mem hcC)
    · rw [mem_centralizer_iff]
      intro s hs
      have hs' : (c : D)⁻¹ * s * (c : D) ∈ S := by
        have := hnorm _ (C.inv_mem hcC) s hs
        rwa [inv_inv] at this
      have h1 := (mem_centralizer_iff.1 hzS) _ hs'
      simp only [coe_mul, coe_inv]
      calc s * ((c : D) * z * (c : D)⁻¹)
          = (c : D) * ((c : D)⁻¹ * s * (c : D) * z) * (c : D)⁻¹ := by group
        _ = (c : D) * (z * ((c : D)⁻¹ * s * (c : D))) * (c : D)⁻¹ := by rw [h1]
        _ = (c : D) * z * (c : D)⁻¹ * s := by group
  have hZbot : Z = ⊥ := by
    have hle : Z.subgroupOf (C ⊓ centralizer ({t} : Set D)) ≤
        CFSG.oddCore ↥(C ⊓ centralizer ({t} : Set D)) :=
      le_sSup ⟨hZn, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]; exact hZodd⟩
    rw [hcore, le_bot_iff, subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hZle] at hle
    exact hle
  set f : C →* MulAut N := MulAut.conjNormal
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcZ : (c : D) ∈ Z := by
      refine mem_inf.2 ⟨c.2, mem_centralizer_iff.2 fun s hs => ?_⟩
      have h1 := congrArg (fun φ : MulAut N => ((φ ⟨⟨s, hSC hs⟩, by
        rw [mem_subgroupOf]; exact hs⟩ : N) : C)) hc
      simp only [f, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      have h2 := congrArg Subtype.val h1
      simp only [coe_mul, coe_inv] at h2
      calc s * (c : D) = (c : D) * s * (c : D)⁻¹ * c := by rw [h2]
        _ = c * s := by group
    rw [hZbot, mem_bot] at hcZ
    exact (mem_bot).2 (Subtype.ext hcZ)
  let eN : N ≃* S := Subgroup.subgroupOfEquivOfLe hSC
  have := hs
  have : IsSimpleGroup N := eN.isSimpleGroup
  have hNnab : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eN.symm a, eN.symm b, fun h' => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eN h'
  have hZN : center N = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hNnab).2
  have : Finite (MulAut N) :=
    Finite.of_injective (fun φ : MulAut N => (φ : N → N)) DFunLike.coe_injective
  have hCdvd : Nat.card C ∣
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer N) * Nat.card N := by
    rw [← SporadicBender.card_inner_eq_of_center_eq_bot hZN,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    exact Subgroup.card_dvd_of_injective f hfinj
  have hQdvd : Nat.card (C ⧸ N) ∣
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eN).toEquiv]
      at hCdvd
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hCdvd
  by_contra hxS
  set xC : C := ⟨x, (mem_inf.1 hx).1⟩
  have hxCr : orderOf xC = r := by rw [Subgroup.orderOf_mk, hxr]
  have hne : (xC : C ⧸ N) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact hxS h1
  have hpow : (xC : C ⧸ N) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow, ← hxCr, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hord := orderOf_eq_prime hpow hne
  exact hrO ((hord ▸ orderOf_dvd_natCard (xC : C ⧸ N)).trans hQdvd)

end FixedRootDatumOf

namespace SporadicBender

@[expose] def SporadicFixedRootFreeOf (T : StdType) (s : TauCeti.SporadicName) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → NativeSporadic.IsSporadic D s →
    ∀ (n : ℕ) (α : MulAut D) (S : Subgroup D), ¬ FixedRootDatumOf T D n α S

@[expose] def BenderFixedRootFree (s : TauCeti.SporadicName) : Prop :=
  SporadicFixedRootFreeOf T_U3 s ∧ SporadicFixedRootFreeOf T_Sz s

theorem sporadicFixedRootFreeOf_of_comps {T : StdType} {s : TauCeti.SporadicName}
    {Qi Qo : (Y : Type) → [Group Y] → Prop} (hQi : IsoInvariant Qi) (hQo : IsoInvariant Qo)
    (hT : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], T n X →
      IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ ¬ Qi X ∧ ¬ Qo X)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set G)) Qi)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ β : MulAut G, orderOf β = 2 → β ∉ inner G →
        CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Qo) :
    SporadicFixedRootFreeOf T s := by
  intro D _ _ hD hs n α S d
  obtain ⟨hSs, hnab, hi, ho⟩ := hT n S d.type
  by_cases hα : α ∈ inner D
  · exact d.false_of_inner_comps hD hSs hnab hα hQi hi (hin D hD hs)
  · exact d.false_of_outer_comps hSs hnab hα hQo ho (hout D hD hs)

theorem sporadicFixedRootFreeOf_of_card {T : StdType} {s : TauCeti.SporadicName} {N : ℕ}
    (hN : Nat.card (NativeSporadic.Carrier s) = N)
    (hT : ∀ (n : ℕ) (X : Type) [Group X], T n X → ¬ Nat.card X ∣ N) :
    SporadicFixedRootFreeOf T s := by
  intro D _ _ _ ⟨e⟩ n α S d
  refine hT n S d.type ?_
  rw [← hN, ← Nat.card_congr e.toEquiv]
  exact Subgroup.card_subgroup_dvd_card S

@[expose] def u3Order (n : ℕ) : ℕ :=
  (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1)

@[expose] def szOrder (n : ℕ) : ℕ := (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)

theorem le_of_two_pow_dvd {a e h : ℕ} (hh : Odd h) (hd : 2 ^ a ∣ 2 ^ e * h) : a ≤ e := by
  have hcop : Nat.Coprime (2 ^ a) h := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hh)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right hd)

section Unitary

variable {X : Type} [Group X] {n : ℕ}

theorem simple_of_T_U3 (h : T_U3 n X) : IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a :=
  ⟨isSimpleGroup_of_lieModel_PSU3 h.2, exists_mul_ne_of_lieModel_PSU3 h.2⟩

theorem card_eq_u3Order (h : T_U3 n X) : Nat.card X = u3Order n :=
  card_of_lieModel_PSU3 h.2

theorem two_pow_dvd_card_of_T_U3 (h : T_U3 n X) : 2 ^ (3 * n) ∣ Nat.card X := by
  have hd := Nat.ordProj_dvd (Nat.card X) 2
  rwa [factorization_two_card_of_lieModel_PSU3 h.2] at hd

theorem not_dvd_of_check_U3 (hX : T_U3 n X) {N e h : ℕ} (hN : N = 2 ^ e * h) (hh : Odd h)
    (hcheck : ∀ m ≤ e / 3, 2 ≤ m → ¬ u3Order m ∣ N) : ¬ Nat.card X ∣ N := by
  intro hd
  have hle : 3 * n ≤ e := le_of_two_pow_dvd hh (hN ▸ (two_pow_dvd_card_of_T_U3 hX).trans hd)
  exact hcheck n (by omega) hX.1 (card_eq_u3Order hX ▸ hd)

theorem ne_of_check_U3 (hX : T_U3 n X) {N e h : ℕ} (hN : N = 2 ^ e * h) (hh : Odd h)
    (hcheck : ∀ m ≤ e / 3, 2 ≤ m → u3Order m ≠ N) : Nat.card X ≠ N := by
  intro hd
  have hle : 3 * n ≤ e :=
    le_of_two_pow_dvd hh (hN ▸ hd ▸ two_pow_dvd_card_of_T_U3 hX)
  exact hcheck n (by omega) hX.1 (card_eq_u3Order hX ▸ hd)

end Unitary

section Suzuki

variable {X : Type} [Group X] {n : ℕ}

theorem simple_of_T_Sz (h : T_Sz n X) : IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a :=
  ⟨isSimpleGroup_of_lieModel_twistedB2 h, exists_mul_ne_of_lieModel_twistedB2 h⟩

theorem card_eq_szOrder (h : T_Sz n X) :
    Nat.card X = szOrder n := by
  rw [card_of_lieModel_twistedB2 h, szOrder]

theorem two_pow_dvd_card_of_T_Sz (h : T_Sz n X) : 2 ^ (2 * n) ∣ Nat.card X := by
  have hd := Nat.ordProj_dvd (Nat.card X) 2
  rwa [factorization_two_card_of_lieModel_twistedB2 h] at hd

theorem not_dvd_of_check_Sz (hX : T_Sz n X) {N e h : ℕ}
    (hN : N = 2 ^ e * h) (hh : Odd h) (hcheck : ∀ m ≤ e / 2, 3 ≤ m → ¬ szOrder m ∣ N) :
    ¬ Nat.card X ∣ N := by
  intro hd
  have hle : 2 * n ≤ e := le_of_two_pow_dvd hh (hN ▸ (two_pow_dvd_card_of_T_Sz hX).trans hd)
  exact hcheck n (by omega) (three_le_of_lieModel_twistedB2 hX) (card_eq_szOrder hX ▸ hd)

theorem ne_of_check_Sz (hX : T_Sz n X) {N e h : ℕ}
    (hN : N = 2 ^ e * h) (hh : Odd h) (hcheck : ∀ m ≤ e / 2, 3 ≤ m → szOrder m ≠ N) :
    Nat.card X ≠ N := by
  intro hd
  have hle : 2 * n ≤ e := le_of_two_pow_dvd hh (hN ▸ hd ▸ two_pow_dvd_card_of_T_Sz hX)
  exact hcheck n (by omega) (three_le_of_lieModel_twistedB2 hX) (card_eq_szOrder hX ▸ hd)

end Suzuki

theorem benderFixedRootFree_of_card {s : TauCeti.SporadicName}
    {N e h : ℕ} (hs : Nat.card (NativeSporadic.Carrier s) = N) (hN : N = 2 ^ e * h)
    (hh : Odd h) (hU : ∀ m ≤ e / 3, 2 ≤ m → ¬ u3Order m ∣ N)
    (hS : ∀ m ≤ e / 2, 3 ≤ m → ¬ szOrder m ∣ N) : BenderFixedRootFree s :=
  ⟨sporadicFixedRootFreeOf_of_card hs fun _ _ _ hX => not_dvd_of_check_U3 hX hN hh hU,
    sporadicFixedRootFreeOf_of_card hs fun _ _ _ hX => not_dvd_of_check_Sz hX hN hh hS⟩

theorem m11_benderFree :
    BenderFixedRootFree .M11 :=
  benderFixedRootFree_of_card CFSG.Sporadic.Mathieu.card_M11 (e := 4) (h := 495) (by norm_num)
    (by decide) (by decide) (by decide)

theorem m12_benderFree :
    BenderFixedRootFree .M12 :=
  benderFixedRootFree_of_card CFSG.Sporadic.Mathieu.card_M12 (e := 6) (h := 1485) (by norm_num)
    (by decide) (by decide) (by decide)

theorem j4_benderFree :
    BenderFixedRootFree .J4 :=
  benderFixedRootFree_of_card CFSG.Sporadic.J4.card_J4 (e := 21) (h := 41377816699065)
    (by norm_num) (by decide) (by decide) (by decide)

theorem m22_benderFree :
    BenderFixedRootFree .M22 :=
  benderFixedRootFree_of_card CFSG.Sporadic.Mathieu.card_M22 (e := 7) (h := 3465) (by norm_num)
    (by decide) (by decide) (by decide)

theorem m23_benderFree :
    BenderFixedRootFree .M23 :=
  benderFixedRootFree_of_card CFSG.EvenSmallLie.CatalogOrders.card_M23 (e := 7) (h := 79695)
    (by norm_num) (by decide) (by decide) (by decide)

theorem m24_benderFree :
    BenderFixedRootFree .M24 :=
  benderFixedRootFree_of_card CFSG.Sporadic.Mathieu.card_M24 (e := 10) (h := 239085)
    (by norm_num) (by decide) (by decide) (by decide)

theorem j1_benderFree :
    BenderFixedRootFree .J1 :=
  benderFixedRootFree_of_card CFSG.Sporadic.J1.card_J1 (e := 3) (h := 21945) (by norm_num)
    (by decide) (by decide) (by decide)

theorem j2_benderFree :
    BenderFixedRootFree .J2 :=
  benderFixedRootFree_of_card CFSG.Sporadic.J2.card_J2 (e := 7) (h := 4725) (by norm_num)
    (by decide) (by decide) (by decide)

theorem j3_benderFree :
    BenderFixedRootFree .J3 :=
  benderFixedRootFree_of_card CFSG.Sporadic.J3.card_J3 (e := 7) (h := 392445) (by norm_num)
    (by decide) (by decide) (by decide)

theorem hs_benderFree :
    BenderFixedRootFree .HS :=
  benderFixedRootFree_of_card CFSG.Sporadic.HS.card_HS (e := 9) (h := 86625) (by norm_num)
    (by decide) (by decide) (by decide)

theorem mcl_benderFree :
    BenderFixedRootFree .McL :=
  benderFixedRootFree_of_card CFSG.Sporadic.McL.card_McL (e := 7) (h := 7016625) (by norm_num)
    (by decide) (by decide) (by decide)

theorem he_benderFree :
    BenderFixedRootFree .He :=
  benderFixedRootFree_of_card CFSG.Sporadic.He.fam_he_order.1 (e := 10) (h := 3935925)
    (by norm_num) (by decide) (by decide) (by decide)

theorem co2_benderFree :
    BenderFixedRootFree .Co2 :=
  benderFixedRootFree_of_card CFSG.Sporadic.Co2.card_Co2 (e := 18) (h := 161382375)
    (by norm_num) (by decide) (by decide) (by decide)

theorem co3_benderFree :
    BenderFixedRootFree .Co3 :=
  benderFixedRootFree_of_card CFSG.Sporadic.Co3.card_Co3 (e := 10) (h := 484147125)
    (by norm_num) (by decide) (by decide) (by decide)

theorem ly_benderFree :
    BenderFixedRootFree .Ly :=
  benderFixedRootFree_of_card CFSG.Sporadic.Ly.card_Ly (e := 8) (h := 202207730484375)
    (by norm_num) (by decide) (by decide) (by decide)

theorem card_quotient_center_eq {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : Nat.card (X ⧸ center X) = Nat.card X :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2).trans
      QuotientGroup.quotientBot).toEquiv

open CFSG.ComponentClassification.RestrictedStd.Spor (isoInvariant_card_quotient_center) in
theorem suz_fixedRootFreeOf
    {T : StdType}
    (hT : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], T n X → IsSimpleGroup X ∧
      (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X ≠ 20160 ∧ ¬ Nat.card X ∣ 190080 ∧
        ¬ Nat.card X ∣ 1209600) :
    SporadicFixedRootFreeOf T .Suz := by
  intro D _ _ hD hs n α S d
  obtain ⟨e⟩ := hs
  obtain ⟨hSs, hnab, h1, h2, h3⟩ := hT n S d.type
  by_cases hα : α ∈ inner D
  · refine d.false_of_inner_comps hD hSs hnab hα (isoInvariant_card_quotient_center {20160}) ?_
      fun t ht B hB =>
        CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t
          ht B hB
    rw [Set.mem_singleton_iff, card_quotient_center_eq hSs hnab]
    exact h1
  · rcases Sporadic.suz_outer_card e α d.orderOf_eq hα with hc | hc
    · exact h2 (hc ▸ d.card_dvd_card_fixed)
    · exact h3 (hc ▸ d.card_dvd_card_fixed)

theorem suz_benderFree :
    BenderFixedRootFree .Suz :=
  ⟨suz_fixedRootFreeOf fun _ _ _ _ hX => ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2,
      ne_of_check_U3 hX (e := 6) (h := 315) (by norm_num) (by decide) (by decide),
      not_dvd_of_check_U3 hX (e := 7) (h := 1485) (by norm_num) (by decide) (by decide),
      not_dvd_of_check_U3 hX (e := 8) (h := 4725) (by norm_num) (by decide) (by decide)⟩,
    suz_fixedRootFreeOf fun _ _ _ _ hX => ⟨(simple_of_T_Sz hX).1, (simple_of_T_Sz hX).2,
      ne_of_check_Sz hX (e := 6) (h := 315) (by norm_num) (by decide) (by decide),
      not_dvd_of_check_Sz hX (e := 7) (h := 1485) (by norm_num) (by decide) (by decide),
      not_dvd_of_check_Sz hX (e := 8) (h := 4725) (by norm_num) (by decide) (by decide)⟩⟩

open CFSG.Sporadic.RuSchreier in
open CFSG.ComponentClassification.RestrictedStd.Spor (centralizerEquiv
  centralizerSubtypeEquiv) in
theorem ru_card_centralizer
    {G : Type} [Group G]
    (e : G ≃* NativeSporadic.Carrier .Ru) (t : G) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set G)) = 245760 ∨
      Nat.card (centralizer ({t} : Set G)) = 116480 := by
  set θ : G ≃* ruP := e.trans ruEquivP
  have hu : orderOf ((θ t : ruP) : Equiv.Perm (Fin 4060)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  rw [Nat.card_congr ((centralizerEquiv θ t).trans (centralizerSubtypeEquiv ruP (θ t))).toEquiv]
  have hmem : ((θ t : ruP) : Equiv.Perm (Fin 4060)) ∈
      {x | x ∈ ruP ∧ orderOf x = 2} := ⟨(θ t).2, hu⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with ⟨g, hg, hgu⟩ | ⟨g, hg, hgu⟩
  · left
    change Nat.card (CFSG.Sporadic.Schreier.centralizerIn ruP _) = _
    rw [← hgu, CFSG.Sporadic.Schreier.centralizerIn_conj ruP hg,
      card_map_of_injective (MulAut.conj g).injective, CFSG.Sporadic.Schreier.centralizerIn,
      ← ruC_eq_centralizer, card_ruC]
  · right
    change Nat.card (CFSG.Sporadic.Schreier.centralizerIn ruP _) = _
    rw [← hgu, CFSG.Sporadic.Schreier.centralizerIn_conj ruP hg,
      card_map_of_injective (MulAut.conj g).injective, CFSG.Sporadic.Schreier.centralizerIn,
      ruCentralizer_a, card_ruL]

open CFSG.Sporadic.RuSchreier in
open CFSG.ComponentClassification.RestrictedStd.Spor (isoInvariant_not_three_dvd
  compsSatisfy_centralizer_of_mulEquiv ru_centralizerIn_comps mem_inner_of_mulEquiv) in
theorem ru_benderFree :
    BenderFixedRootFree .Ru := by
  have hinner : ∀ (D : Type) [Group D], Nonempty (D ≃* NativeSporadic.Carrier .Ru) →
      ∀ α : MulAut D, α ∈ inner D :=
    fun D _ ⟨e⟩ α => mem_inner_of_mulEquiv (e.trans ruEquivP) mulAut_inner α
  refine ⟨sporadicFixedRootFreeOf_of_comps isoInvariant_not_three_dvd isoInvariant_not_three_dvd
    (fun _ _ _ _ hX => ⟨(simple_of_T_U3 hX).1, (simple_of_T_U3 hX).2,
      not_not_intro (three_dvd_card_of_lieModel_PSU3 hX.2),
      not_not_intro (three_dvd_card_of_lieModel_PSU3 hX.2)⟩)
    (fun _ _ _ _ ⟨e⟩ t ht => compsSatisfy_centralizer_of_mulEquiv _ isoInvariant_not_three_dvd
      ru_centralizerIn_comps (e.trans ruEquivP) t ht)
    (fun G _ _ _ hG β _ hβ => absurd (hinner G hG β) hβ), ?_⟩
  intro D _ _ hD hs n α S d
  obtain ⟨e⟩ := hs
  have hS : LieModel S .twistedB2 0 2 n := d.type
  obtain ⟨hSs, hnab⟩ := simple_of_T_Sz hS
  obtain ⟨t, ht, rfl⟩ := Sporadic.exists_involution_of_mem_inner
    (center_eq_bot_of_subgroup_nonabelian hD hnab) d.orderOf_eq (hinner D ⟨e⟩ _)
  have hC : Nat.card ((MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D)) =
      Nat.card (centralizer ({t} : Set D)) := by
    rw [Sporadic.eqLocus_conj]
  have hdvd := d.card_dvd_card_fixed
  rw [hC] at hdvd
  rcases ru_card_centralizer e t ht with hc | hc
  · rw [hc] at hdvd
    exact not_dvd_of_check_Sz hS (e := 14) (h := 15) (by norm_num) (by decide) (by decide) hdvd
  · have h8 := d.two_pow_dvd_of_odd_outer hSs hnab (odd_card_outer_of_lieModel_twistedB2 hS)
      (a := 8) (by rw [hC, hc]; norm_num)
    have h7 : 2 ^ 7 ∣ Nat.card S :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by rw [← pow_succ']; exact h8)
    have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have hlo := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hS0).1 h7
    rw [factorization_two_card_of_lieModel_twistedB2 hS] at hlo
    rw [hc] at hdvd
    have hhi : 2 * n ≤ 8 := le_of_two_pow_dvd (h := 455) (by decide)
      ((two_pow_dvd_card_of_T_Sz hS).trans (hdvd.trans (by norm_num)))
    obtain ⟨k, rfl⟩ := odd_of_lieModel_twistedB2 hS
    omega

end SporadicBender

end CFSG.LocalAnalysis.EvenBN.GMSK
