module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input185
public import CFSG.LocalAnalysis.GL83PartI.I710.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185 (fixerAut mem_fixerAut)

section NormalComplement

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem eq_one_of_pow_of_coprime {H : Subgroup G} (hcop : Nat.Coprime p (Nat.card H)) {y : G}
    (hy : y ∈ H) {k : ℕ} (hk : y ^ p ^ k = 1) : y = 1 := by
  have hk' : (⟨y, hy⟩ : ↥H) ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
  have h1 : orderOf (⟨y, hy⟩ : ↥H) ∣ Nat.card H := orderOf_dvd_natCard _
  have h2 : orderOf (⟨y, hy⟩ : ↥H) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : Nat.Coprime (orderOf (⟨y, hy⟩ : ↥H)) (p ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h1 hcop.symm)
  have h4 : orderOf (⟨y, hy⟩ : ↥H) = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h4)

theorem hasNormalPComplement_of_pElements_central [Fact p.Prime]
    (h : ∀ g : G, (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ Subgroup.center G) :
    CFSG.HasNormalPComplement p G := by
  obtain ⟨S⟩ : Nonempty (Sylow p G) := inferInstance
  refine CFSG.hasNormalPComplement_of_sylow_le_center_normalizer p S ?_
  intro x hx
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxc : x ∈ Subgroup.center G := h x ⟨k, hxk⟩
  unfold CFSG.centerIn
  exact Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hx,
    Subgroup.mem_centralizer_iff.2 fun y _ => Subgroup.mem_center_iff.1 hxc y⟩

theorem mem_map_iff_coprime {N : Subgroup G} {M : Subgroup ↥N} [M.Normal]
    (hMc : Nat.Coprime p (Nat.card M)) (hMq : IsPGroup p (↥N ⧸ M)) (x : G) :
    x ∈ M.map N.subtype ↔ x ∈ N ∧ Nat.Coprime p (orderOf x) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m.2, ?_⟩
    have h1 : orderOf ((N.subtype m : G)) = orderOf (⟨m, hm⟩ : ↥M) := by
      have e1 : orderOf (N.subtype m) = orderOf m := orderOf_injective N.subtype N.subtype_injective m
      have e2 : orderOf (M.subtype ⟨m, hm⟩) = orderOf (⟨m, hm⟩ : ↥M) :=
        orderOf_injective M.subtype M.subtype_injective _
      rw [e1, ← e2]
      rfl
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hMc
  · rintro ⟨hxN, hxc⟩
    obtain ⟨j, hj⟩ := hMq (QuotientGroup.mk (⟨x, hxN⟩ : ↥N))
    have hq : (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : ↥N ⧸ M) ^ orderOf x = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxN⟩ : ↥N) ^ orderOf x = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (p ^ j) (orderOf x) := Nat.Coprime.pow_left j hxc
    have h1 : (QuotientGroup.mk (⟨x, hxN⟩ : ↥N) : ↥N ⧸ M) = 1 := by
      have h3 := pow_gcd_eq_one.2 ⟨hj, hq⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
    exact ⟨⟨x, hxN⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem hasNormalPComplement_of_normal [Fact p.Prime] {N : Subgroup G} [hN : N.Normal]
    (hq : IsPGroup p (G ⧸ N)) (hc : CFSG.HasNormalPComplement p ↥N) :
    CFSG.HasNormalPComplement p G := by
  obtain ⟨M, hMn, hMc, hMq⟩ := hc
  haveI := hMn
  have key := mem_map_iff_coprime hMc hMq
  have hnorm : (M.map N.subtype).Normal := by
    constructor
    intro x hx g
    obtain ⟨hxN, hxc⟩ := (key x).1 hx
    refine (key _).2 ⟨hN.conj_mem x hxN g, ?_⟩
    have : orderOf (g * x * g⁻¹) = orderOf x := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [this]
    exact hxc
  refine ⟨M.map N.subtype, hnorm, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hMc
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := hq (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      obtain ⟨j, hj⟩ := hMq (QuotientGroup.mk (⟨g ^ p ^ k, hk⟩ : ↥N))
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hj
      refine ⟨k + j, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_add, pow_mul]
      exact ⟨_, hj, rfl⟩

theorem hasNormalPComplement_of_injective {H : Type*} [Group H] [Finite H] (f : H →* G)
    (hf : Function.Injective f) (h : CFSG.HasNormalPComplement p G) :
    CFSG.HasNormalPComplement p H := by
  obtain ⟨N, hN, hc, hq⟩ := h
  haveI := hN
  refine ⟨N.comap f, inferInstance, ?_, ?_⟩
  · have h1 : Nat.card (N.comap f) = Nat.card ((N.comap f).map f) :=
      (Subgroup.card_map_of_injective hf).symm
    have h2 : Nat.card ((N.comap f).map f) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le (Subgroup.map_comap_le f N)
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right h2 hc
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hq (QuotientGroup.mk (f x))
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show f (x ^ p ^ k) ∈ N
      rw [map_pow]
      exact hk

end NormalComplement

section Fixer

variable {K : Type} [Group K]

theorem commute_conj_of_mem_fixerAut {P : Subgroup K} {α : MulAut K} (hα : α ∈ fixerAut P)
    {g : K} (hg : g ∈ P) : α * MulAut.conj g = MulAut.conj g * α := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, (mem_fixerAut.1 hα) g hg]

theorem conj_injective_of_center (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hc : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => by
    have h := congrArg (fun φ : MulAut K => φ g) hk
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    have h2 : k * g = g * k := by
      calc k * g = k * g * k⁻¹ * k := by group
        _ = g * k := by rw [h]
    exact h2.symm
  rw [hZ] at hc
  exact hc

theorem center_eq_bot_of_simple (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    Subgroup.center K = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem mem_center_fixerAut_of_inner {p : ℕ} [Fact p.Prime] (hZ : Subgroup.center K = ⊥)
    (P : Sylow p K) (c : ↥(fixerAut (P : Subgroup K))) (hcp : ∃ k : ℕ, c ^ p ^ k = 1)
    (hci : (c : MulAut K) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    c ∈ Subgroup.center ↥(fixerAut (P : Subgroup K)) := by
  obtain ⟨g, hg⟩ := hci
  have hgP : ∀ x ∈ (P : Subgroup K), g * x = x * g := by
    intro x hx
    have h1 : (c : MulAut K) x = x := (mem_fixerAut.1 c.2) x hx
    rw [← hg, MulAut.conj_apply] at h1
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h1]
  obtain ⟨k, hk⟩ := hcp
  have hgk : g ^ p ^ k = 1 := by
    apply conj_injective_of_center hZ
    rw [map_pow, map_one, hg]
    simpa using congrArg Subtype.val hk
  have hgmem : g ∈ (P : Subgroup K) := GL83.I710.mem_sylow_of_commute P ⟨k, hgk⟩ hgP
  rw [Subgroup.mem_center_iff]
  intro d
  apply Subtype.ext
  show (d : MulAut K) * c = c * d
  rw [← hg]
  exact commute_conj_of_mem_fixerAut d.2 hgmem

theorem fusionIsSylowIn_map_of_surjective [Finite K] {K' : Type} [Group K'] {p : ℕ} [Fact p.Prime]
    {f : K →* K'} (hf : Function.Surjective f) {P : Subgroup K}
    (hP : CFSG.Open.fusionIsSylowIn p P ⊤) : CFSG.Open.fusionIsSylowIn p (P.map f) ⊤ := by
  let S : Sylow p K := ⟨P, hP.2.1, fun {Q} hQ hle => hP.2.2 Q le_top hQ hle⟩
  let S' : Sylow p K' := S.mapSurjective hf
  have hS' : (S' : Subgroup K') = P.map f := rfl
  rw [← hS']
  exact ⟨le_top, S'.isPGroup', fun Q _ hQ hle => S'.is_maximal' hQ hle⟩

theorem hasNormalPComplement_fixerAut_of_outer [Finite K] {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center K = ⊥) (P : Sylow p K) (hO : CFSG.HasNormalPComplement p (Outer K)) :
    CFSG.HasNormalPComplement p ↥(fixerAut (P : Subgroup K)) := by
  obtain ⟨MO, hMOn, hMOc, hMOq⟩ := hO
  haveI := hMOn
  set C : Subgroup (MulAut K) := fixerAut (P : Subgroup K) with hC
  let π : ↥C →* Outer K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)).comp C.subtype
  let N : Subgroup ↥C := MO.comap π
  haveI hNn : N.Normal := Subgroup.Normal.comap hMOn π
  refine hasNormalPComplement_of_normal (N := N) ?_ ?_
  · intro q
    induction q using QuotientGroup.induction_on with
    | H c =>
      obtain ⟨k, hk⟩ := hMOq (QuotientGroup.mk (π c))
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show π (c ^ p ^ k) ∈ MO
      rw [map_pow]
      exact hk
  · refine hasNormalPComplement_of_pElements_central fun n hn => ?_
    obtain ⟨k, hk⟩ := hn
    have hck : (n : ↥C) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hπ1 : π n = 1 := by
      refine eq_one_of_pow_of_coprime (k := k) hMOc n.2 ?_
      rw [← map_pow, hck, map_one]
    have hinner : ((n : ↥C) : MulAut K) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
      (QuotientGroup.eq_one_iff _).1 hπ1
    have hcen := mem_center_fixerAut_of_inner hZ P (n : ↥C) ⟨k, hck⟩ hinner
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hcen (m : ↥C)

theorem hasNormalPComplement_fixerAut_of_abelian
    (hIA : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) [Finite K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K) (P : Sylow p K) (hP1 : (P : Subgroup K) ≠ ⊥)
    (hPab : IsMulCommutative (P : Subgroup K)) :
    CFSG.HasNormalPComplement p ↥(fixerAut (P : Subgroup K)) := by
  have hZ := center_eq_bot_of_simple hs hnab
  refine hasNormalPComplement_of_pElements_central fun c hc => ?_
  obtain ⟨k, hk⟩ := hc
  have hck : (c : MulAut K) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨g, -, hcg⟩ := hIA p hp.out hp2 K hs hnab hcat P hP1 hPab (c : MulAut K) ⟨k, hck⟩
    (fun g hg => commute_conj_of_mem_fixerAut c.2 hg)
  exact mem_center_fixerAut_of_inner hZ P c ⟨k, hk⟩ ⟨g, hcg.symm⟩

theorem hasNormalPComplement_fixerAut_of_quotient [Finite K] {p : ℕ} (hperf : commutator K = ⊤)
    (P : Subgroup K)
    (h : CFSG.HasNormalPComplement p ↥(fixerAut (P.map (QuotientGroup.mk' (Subgroup.center K))))) :
    CFSG.HasNormalPComplement p ↥(fixerAut P) := by
  have hmaps : ∀ α : ↥(fixerAut P), quotientCenterAut' K α ∈
      fixerAut (P.map (QuotientGroup.mk' (Subgroup.center K))) := by
    intro α
    refine mem_fixerAut.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (quotientCenterAut' K α) (QuotientGroup.mk x) = QuotientGroup.mk x
    simp only [quotientCenterAut', MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.congr_mk]
    rw [(mem_fixerAut.1 α.2) x hx]
  let f : ↥(fixerAut P) →* ↥(fixerAut (P.map (QuotientGroup.mk' (Subgroup.center K)))) :=
    ((quotientCenterAut' K).comp (fixerAut P).subtype).codRestrict _ hmaps
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply quotientCenterAut'_injective hperf
    exact congrArg Subtype.val hab
  exact hasNormalPComplement_of_injective f hf h

end Fixer

section Residual

@[expose] def Input7_10_1ResTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ¬ CFSG.HasNormalPComplement 2 (Outer K) →
    ∀ S : Subgroup K, CFSG.Open.fusionIsSylowIn 2 S ⊤ → CFSG.HasNormalPComplement 2 ↥(fixerAut S)

@[expose] def Input7_10_1ResOdd : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ¬ CFSG.HasNormalPComplement p (Outer K) →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn p P ⊤ → (P = ⊥ ∨ ¬ IsMulCommutative ↥P) →
      CFSG.HasNormalPComplement p ↥(fixerAut P)

@[expose] def Input7_10_1ResOddNonab : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ¬ CFSG.HasNormalPComplement p (Outer K) →
    ∀ P : Subgroup K, CFSG.Open.fusionIsSylowIn p P ⊤ → ¬ IsMulCommutative ↥P →
      CFSG.HasNormalPComplement p ↥(fixerAut P)

variable {K : Type} [Group K] [Finite K]

theorem hasNormalPComplement_fixerAut_simple
    (hIA : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction) {p : ℕ} [hp : Fact p.Prime]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    {P : Subgroup K} (hP : CFSG.Open.fusionIsSylowIn p P ⊤)
    (hres : ¬ CFSG.HasNormalPComplement p (Outer K) → (p = 2 ∨ P = ⊥ ∨ ¬ IsMulCommutative ↥P) →
      CFSG.HasNormalPComplement p ↥(fixerAut P)) :
    CFSG.HasNormalPComplement p ↥(fixerAut P) := by
  have hZ := center_eq_bot_of_simple hs hnab
  let S : Sylow p K := ⟨P, hP.2.1, fun {Q} hQ hle => hP.2.2 Q le_top hQ hle⟩
  by_cases hO : CFSG.HasNormalPComplement p (Outer K)
  · exact hasNormalPComplement_fixerAut_of_outer hZ S hO
  · by_cases hc : p = 2 ∨ P = ⊥ ∨ ¬ IsMulCommutative ↥P
    · exact hres hO hc
    · obtain ⟨hp2, hc'⟩ := not_or.1 hc
      obtain ⟨hP1, hPab⟩ := not_or.1 hc'
      exact hasNormalPComplement_fixerAut_of_abelian hIA hp2 hs hnab hcat S hP1 (not_not.1 hPab)

theorem hasNormalPComplement_fixerAut_quasisimple
    (hIA : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction) {p : ℕ} [hp : Fact p.Prime]
    (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K) {P : Subgroup K}
    (hP : CFSG.Open.fusionIsSylowIn p P ⊤)
    (hres : ¬ CFSG.HasNormalPComplement p (Outer (K ⧸ Subgroup.center K)) →
      (p = 2 ∨ P.map (QuotientGroup.mk' (Subgroup.center K)) = ⊥ ∨
        ¬ IsMulCommutative ↥(P.map (QuotientGroup.mk' (Subgroup.center K)))) →
      CFSG.HasNormalPComplement p ↥(fixerAut (P.map (QuotientGroup.mk' (Subgroup.center K))))) :
    CFSG.HasNormalPComplement p ↥(fixerAut P) := by
  refine hasNormalPComplement_fixerAut_of_quotient hq.1 P ?_
  exact hasNormalPComplement_fixerAut_simple hIA hq.2
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq)
    (CFSG.HardMathSupport.Solomon.LocalBalance.isCatalogGroup_center_quotient_of_isKGroup hK hq)
    (fusionIsSylowIn_map_of_surjective (QuotientGroup.mk'_surjective _) hP) hres

theorem input7_10_1_of_res (hIA : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (h2 : Input7_10_1ResTwo) (hodd : Input7_10_1ResOdd) : Input185.Input7_10_1 := by
  intro p hp K _ _ hq hK P hP
  haveI : Fact p.Prime := ⟨hp⟩
  refine hasNormalPComplement_fixerAut_quasisimple hIA hq hK hP fun hO hc => ?_
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hcat := CFSG.HardMathSupport.Solomon.LocalBalance.isCatalogGroup_center_quotient_of_isKGroup hK hq
  have hPb := fusionIsSylowIn_map_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center K)) hP
  by_cases hp2 : p = 2
  · subst hp2
    exact h2 _ hs hnab hcat hO _ hPb
  · exact hodd p hp hp2 _ hs hnab hcat hO _ hPb (hc.resolve_left hp2)

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5
