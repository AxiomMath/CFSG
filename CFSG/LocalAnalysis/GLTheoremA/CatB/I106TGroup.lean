module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I106TGroup

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem mem_glaPPrimeCoreOf_iff' {p : ℕ} {J : Subgroup G} (c : ↥J) :
    (c : G) ∈ GLAPPrimeCoreOf p J ↔ c ∈ GLAPPrimeCore p ↥J := by
  unfold GLAPPrimeCoreOf
  constructor
  · intro h
    obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.1 h
    have hzc' : z = c := Subtype.ext hzc
    exact hzc' ▸ hz
  · intro h
    exact Subgroup.mem_map_of_mem _ h

theorem isPGroup_three_center_quotient (X : Type) [Group X] [Finite X] :
    IsPGroup 3 (Subgroup.center (X ⧸ CFSG.pPrimeCore 3 X)) := by
  have : (CFSG.pPrimeCore 3 X).Normal := CFSG.pPrimeCore_normal
  exact CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)

theorem exists_pow_eq_one_of_mem_center {X : Type} [Group X] [Finite X]
    (hX : IsPGroup 3 ↥(Subgroup.center X)) :
    ∀ z ∈ Subgroup.center X, ∃ n : ℕ, z ^ 3 ^ n = 1 := by
  intro z hz
  obtain ⟨n, hn⟩ := hX ⟨z, hz⟩
  exact ⟨n, congrArg Subtype.val hn⟩

theorem center_pQuot_three_pow (J : Subgroup G) [Finite G] :
    ∀ z ∈ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J), ∃ n : ℕ, z ^ 3 ^ n = 1 :=
  exists_pow_eq_one_of_mem_center
    (by
      have := isPGroup_three_center_quotient ↥J
      exact this)

theorem isElemAbelian_map_of_hom {K G' : Type} [Group K] [Group G'] {F : Subgroup K}
    {f : K →* G'} (hF : IsElemAbelian 3 F) : IsElemAbelian 3 (F.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
    show (a : G') * (b : G') = (b : G') * (a : G')
    rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hF ha' hb']
  · intro x hx
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.1 hx
    rw [← hxx, ← map_pow, hF.2 x' hx', map_one]

end Basic

section Lift

theorem exists_lift_elemAb {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (M : Subgroup K) (E : Subgroup (K ⧸ N))
    (hME : M.map (QuotientGroup.mk' N) = E) (hE : IsElemAbelian 3 E) :
    ∃ F : Subgroup K, F ≤ M ∧ F ⊓ N = ⊥ ∧ F.map (QuotientGroup.mk' N) = E ∧
      IsElemAbelian 3 F ∧ Nat.card F = Nat.card E := by
  classical
  let f : M →* K ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  have hker : f.ker = N.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hrange : f.range = E := by
    rw [← hME]
    ext q
    constructor
    · rintro ⟨m, rfl⟩
      exact Subgroup.mem_map.2 ⟨m, m.2, rfl⟩
    · intro hq
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hq
      exact ⟨⟨m, hm⟩, rfl⟩
  have hidx : (N.subgroupOf M).index = Nat.card E := by
    rw [← hker, Subgroup.index_ker, hrange]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hE)
  have hNMdvd : Nat.card (N.subgroupOf M) ∣ Nat.card N := by
    have h1 : Nat.card ((N.subgroupOf M).map M.subtype) = Nat.card (N.subgroupOf M) :=
      Subgroup.card_map_of_injective Subtype.val_injective
    have h2 : (N.subgroupOf M).map M.subtype ≤ N := by
      rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hm
    rw [← h1]
    exact Subgroup.card_dvd_of_le h2
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf M)) (N.subgroupOf M).index := by
    rw [hidx, hk]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left hNMdvd hN.symm)
  obtain ⟨F', hF'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hFM : F'.map M.subtype ≤ M := Subgroup.map_subtype_le F'
  have hdisj : F'.map M.subtype ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxN⟩
    obtain ⟨f', hf', hfx⟩ := Subgroup.mem_map.1 hxF
    have hfx' : (f' : K) = x := hfx
    have hf'N : f' ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.2 (by rw [hfx']; exact hxN)
    have hf1 : f' = 1 := Subgroup.disjoint_def.1 hF'.disjoint hf'N hf'
    rw [Subgroup.mem_bot, ← hfx, hf1, map_one]
  have hFmap : (F'.map M.subtype).map (QuotientGroup.mk' N) = E := by
    apply le_antisymm
    · calc (F'.map M.subtype).map (QuotientGroup.mk' N)
          ≤ M.map (QuotientGroup.mk' N) := Subgroup.map_mono hFM
        _ = E := hME
    · intro q hq
      rw [← hME] at hq
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hq
      obtain ⟨⟨a, b⟩, hab⟩ := hF'.2 ⟨m, hm⟩
      have hab' : (a : K) * (b : K) = m := congrArg Subtype.val hab
      have ha1 : QuotientGroup.mk' N (a : K) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.1 a.2)
      have hbF : (b : K) ∈ F'.map M.subtype := Subgroup.mem_map_of_mem _ b.2
      refine Subgroup.mem_map.2 ⟨(b : K), hbF, ?_⟩
      rw [← hab', map_mul, ha1, one_mul]
  refine ⟨F'.map M.subtype, hFM, hdisj, hFmap, ?_, ?_⟩
  ·
    have hcomm : ∀ x ∈ F'.map M.subtype, ∀ y ∈ F'.map M.subtype, x * y = y * x := by
      intro x hx y hy
      have hxE : QuotientGroup.mk' N x ∈ E := hFmap ▸ Subgroup.mem_map_of_mem _ hx
      have hyE : QuotientGroup.mk' N y ∈ E := hFmap ▸ Subgroup.mem_map_of_mem _ hy
      have hq : QuotientGroup.mk' N (x * y) = QuotientGroup.mk' N (y * x) := by
        rw [map_mul, map_mul]
        exact isElemAbelian_commute hE hxE hyE
      have hmem : (x * y)⁻¹ * (y * x) ∈ F'.map M.subtype ⊓ N := by
        refine ⟨?_, (QuotientGroup.eq).1 hq⟩
        exact (F'.map M.subtype).mul_mem ((F'.map M.subtype).inv_mem
          ((F'.map M.subtype).mul_mem hx hy)) ((F'.map M.subtype).mul_mem hy hx)
      rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      exact hmem
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
    intro x hx
    have hxE : QuotientGroup.mk' N x ∈ E := hFmap ▸ Subgroup.mem_map_of_mem _ hx
    have h3 : QuotientGroup.mk' N (x ^ 3) = 1 := by
      rw [map_pow]
      exact hE.2 _ hxE
    have hmem : x ^ 3 ∈ F'.map M.subtype ⊓ N :=
      ⟨(F'.map M.subtype).pow_mem hx 3, (QuotientGroup.eq_one_iff _).1 h3⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact hmem
  ·
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp (F'.map M.subtype).subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have haN : (a : K) ∈ N := (QuotientGroup.eq_one_iff _).1 ha
      have hmem : (a : K) ∈ F'.map M.subtype ⊓ N := ⟨a.2, haN⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have h1 := Subgroup.card_map_of_injective (K := (⊤ : Subgroup (F'.map M.subtype))) hinj
    have hmap : (⊤ : Subgroup (F'.map M.subtype)).map
        ((QuotientGroup.mk' N).comp (F'.map M.subtype).subtype) =
          (F'.map M.subtype).map (QuotientGroup.mk' N) := by
      ext q
      constructor
      · rintro ⟨a, _, rfl⟩
        exact Subgroup.mem_map.2 ⟨a, a.2, rfl⟩
      · intro hq
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hq
        exact ⟨⟨a, ha⟩, trivial, rfl⟩
    rw [hmap, hFmap, Subgroup.card_top] at h1
    exact h1.symm

end Lift

section Coprime

theorem exists_fixed_lift {K : Type} [Group K] [Finite K] {N : Subgroup K} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (φ : K ≃* K) (hφN : N.map φ.toMonoidHom = N)
    (hφ3 : ∀ z, φ (φ (φ z)) = z) (x0 : K)
    (hx0 : QuotientGroup.mk' N (φ x0) = QuotientGroup.mk' N x0) :
    ∃ c : K, QuotientGroup.mk' N c = QuotientGroup.mk' N x0 ∧ φ c = c := by
  classical
  have hφmem : ∀ n ∈ N, φ n ∈ N := by
    intro n hn
    have h : φ n ∈ N.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hn
    rwa [hφN] at h
  have hpres : ∀ z : K, QuotientGroup.mk' N z = QuotientGroup.mk' N x0 →
      QuotientGroup.mk' N (φ z) = QuotientGroup.mk' N x0 := by
    intro z hz
    have hz' : z⁻¹ * x0 ∈ N := QuotientGroup.eq.1 hz
    have hx0' : (φ x0)⁻¹ * x0 ∈ N := QuotientGroup.eq.1 hx0
    apply QuotientGroup.eq.2
    have h1 : (φ z)⁻¹ * x0 = φ (z⁻¹ * x0) * ((φ x0)⁻¹ * x0) := by
      rw [map_mul, map_inv]
      group
    rw [h1]
    exact N.mul_mem (hφmem _ hz') hx0'
  let T := {z : K // QuotientGroup.mk' N z = QuotientGroup.mk' N x0}
  let ψ : T → T := fun t => ⟨φ t.1, hpres t.1 t.2⟩
  have hψinj : Function.Injective ψ := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  let p : Equiv.Perm T := Equiv.ofBijective ψ (Finite.injective_iff_bijective.1 hψinj)
  have hpψ : ∀ t : T, p t = ψ t := fun t => rfl
  have hp3' : ∀ t : T, p (p (p t)) = t := fun t => by
    rw [hpψ, hpψ, hpψ]
    exact Subtype.ext (hφ3 t.1)
  have hp3 : p ^ 3 = 1 := by
    ext t
    simp only [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hp3' t]
  have hP : IsPGroup 3 (Subgroup.zpowers p) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hp3
  have hTcard : ¬ 3 ∣ Nat.card T := by
    have e : T ≃ N :=
      { toFun := fun t => ⟨x0⁻¹ * t.1, QuotientGroup.eq.1 t.2.symm⟩
        invFun := fun n => ⟨x0 * n.1, QuotientGroup.eq.2 (by simpa using N.inv_mem n.2)⟩
        left_inv := fun t => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
    rw [Nat.card_congr e]
    exact hN
  obtain ⟨t, ht⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card T hTcard
  have htfix : p t = t := MulAction.mem_fixedPoints.1 ht ⟨p, Subgroup.mem_zpowers p⟩
  refine ⟨t.1, t.2, ?_⟩
  have h2 : ψ t = t := (hpψ t).symm.trans htfix
  exact congrArg Subtype.val h2

end Coprime

section Conj

variable {G : Type} [Group G]

theorem conj_inv_mem_of_mem_normalizer {J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) {h : G} (hh : h ∈ J) : y⁻¹ * h * y ∈ J := by
  apply (Subgroup.mem_normalizer_iff.1 hy (y⁻¹ * h * y)).2
  rwa [show y * (y⁻¹ * h * y) * y⁻¹ = h by group]

theorem conj_mem_of_mem_normalizer {J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) {h : G} (hh : h ∈ J) : y * h * y⁻¹ ∈ J :=
  (Subgroup.mem_normalizer_iff.1 hy h).1 hh

@[expose] def conjJ (J : Subgroup G) (y : G) (hy : y ∈ Subgroup.normalizer (J : Set G)) :
    ↥J ≃* ↥J where
  toFun x := ⟨y⁻¹ * x * y, conj_inv_mem_of_mem_normalizer hy x.2⟩
  invFun x := ⟨y * x * y⁻¹, conj_mem_of_mem_normalizer hy x.2⟩
  left_inv x := Subtype.ext (by group)
  right_inv x := Subtype.ext (by group)
  map_mul' x z := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjJ_val {J : Subgroup G} (y : G) (hy : y ∈ Subgroup.normalizer (J : Set G)) (x : ↥J) :
    ((conjJ J y hy x : ↥J) : G) = y⁻¹ * x * y := rfl

end Conj

section CentModPart

variable {G : Type} [Group G]

theorem mk_mem_center_of_centModSubgroup {J : Subgroup G} (x : ↥J)
    (hx : (x : G) ∈ centModSubgroup 3 J) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x ∈ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) g
  rw [← map_mul, ← map_mul]
  apply QuotientGroup.eq.2
  have hc : (l⁻¹ * x * l * x⁻¹ : ↥J) ∈ GLAPPrimeCore 3 ↥J := by
    rw [← mem_glaPPrimeCoreOf_iff']
    have h := (mem_centModSubgroup.1 hx).2 ((l⁻¹ : ↥J) : G) (l⁻¹ : ↥J).2
    have e : (((l⁻¹ * x * l * x⁻¹ : ↥J)) : G) = ⁅((l⁻¹ : ↥J) : G), (x : G)⁆ := by
      simp [commutatorElement_def]
    rw [e]
    exact h
  have key : (l * x)⁻¹ * (x * l) = x⁻¹ * (l⁻¹ * x * l * x⁻¹) * x⁻¹⁻¹ := by group
  rw [key]
  exact Subgroup.Normal.conj_mem inferInstance _ hc _

theorem eq_one_of_centMod {J : Subgroup G} (F : Subgroup ↥J)
    (E : Subgroup (↥J ⧸ GLAPPrimeCore 3 ↥J))
    (hFN : F ⊓ GLAPPrimeCore 3 ↥J = ⊥) (hFE : F.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) = E)
    (hcap : E ⊓ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) = ⊥) :
    ∀ f ∈ F.map J.subtype, CentMod 3 J f → f = 1 := by
  intro f hf hc
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hf
  have hxc : (x : G) ∈ centModSubgroup 3 J := centMod_iff.1 hc
  have hcen := mk_mem_center_of_centModSubgroup x hxc
  have hE : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x ∈ E := hFE ▸ Subgroup.mem_map_of_mem _ hx
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x ∈ E ⊓ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    ⟨hE, hcen⟩
  rw [hcap, Subgroup.mem_bot] at h1
  have h2 : x ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : x ∈ F ⊓ GLAPPrimeCore 3 ↥J := ⟨hx, h2⟩
  rw [hFN, Subgroup.mem_bot] at h3
  rw [h3, map_one]

end CentModPart

end CFSG.LocalAnalysis.GLTheoremA.I106TGroup
