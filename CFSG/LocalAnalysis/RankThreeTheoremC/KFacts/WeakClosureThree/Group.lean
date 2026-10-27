module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open scoped Pointwise

section Outer

variable {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]

theorem mem_of_conjNormal_mem_inner (hKc : centralizer (K : Set X) = ⊥) {u : X}
    (hu : (MulAut.conjNormal u : MulAut ↥K) ∈ inner ↥K) : u ∈ K := by
  obtain ⟨k, hk⟩ := hu
  have hmem : (k : X)⁻¹ * u ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun α : MulAut ↥K => (α ⟨y, hy⟩ : X)) hk
    simp only [MulAut.conjNormal_apply] at h
    have h' : (k : X) * y * (k : X)⁻¹ = u * y * u⁻¹ := h
    calc y * ((k : X)⁻¹ * u) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * u := by group
      _ = (k : X)⁻¹ * (u * y * u⁻¹) * u := by rw [h']
      _ = (k : X)⁻¹ * u * y := by group
  rw [hKc] at hmem
  have h0 : (k : X)⁻¹ * u = 1 := Subgroup.mem_bot.mp hmem
  have hu' : u = k := by
    calc u = (k : X) * ((k : X)⁻¹ * u) := by group
      _ = k := by rw [h0, mul_one]
  rw [hu']
  exact k.2

theorem mem_of_pow_three_pow_eq_one (hKc : centralizer (K : Set X) = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer ↥K)) {u : X} {n : ℕ} (hu : u ^ 3 ^ n = 1) : u ∈ K := by
  apply mem_of_conjNormal_mem_inner K hKc
  have hαn : (MulAut.conjNormal u : MulAut ↥K) ^ 3 ^ n = 1 := by
    rw [← map_pow, hu, map_one]
  have h1 : (QuotientGroup.mk' (inner ↥K) (MulAut.conjNormal u : MulAut ↥K)) ^ 3 ^ n = 1 := by
    rw [← map_pow, hαn, map_one]
  have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard
    (QuotientGroup.mk' (inner ↥K) (MulAut.conjNormal u : MulAut ↥K)))
  have hcop : Nat.Coprime (3 ^ n) (Nat.card (Outer ↥K)) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hout)
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h2
  exact (QuotientGroup.eq_one_iff _).mp h2

end Outer

theorem exists_map_conj_le {X : Type} [Group X] [Finite X] (Q : Sylow 3 X) {U : Subgroup X}
    (hU : IsPGroup 3 U) : ∃ g : X, U.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q', hUQ'⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q' Q
  refine ⟨g, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : (MulAut.conj g) u ∈ MulAut.conj g • (Q' : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) _ (hUQ' hu)
  have h2 : ((g • Q' : Sylow 3 X) : Subgroup X) = (Q : Subgroup X) := congrArg _ hg
  rw [← h2, Sylow.coe_subgroup_smul]
  exact h1

theorem exists_elemAbelian_of_le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {H : Subgroup G} {k : ℕ} (h : k ≤ CFSG.Open.pRank p H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ ∃ j, k ≤ j ∧ Nat.card E = p ^ j := by
  have hne : {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by rw [(Subgroup.mem_bot).1 hx, one_pow]⟩,
      by simp⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k' ⟨E', -, -, hk'⟩
    have h1 : p ^ k' ≤ Nat.card G := hk' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hp).le.trans h1
  obtain ⟨E, hEH, hE, hk⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEH, hE, _, h, hk⟩

theorem false_of_centralFusion {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hKc : centralizer (K : Set X) = ⊥) (hF : CentralFusionAt ↥K) (Q : Sylow 3 X)
    {A : Subgroup X} (hAQ : A ≤ (Q : Subgroup X)) (hA : Nat.card A = 3)
    (hAc : ∀ a ∈ A, ∀ q ∈ (Q : Subgroup X), q * a = a * q)
    (hwc : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) →
      A.map (MulAut.conj g).toMonoidHom = A) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQK : (Q : Subgroup X) ≤ K := fun x hx => by
    obtain ⟨n, hn⟩ := Q.isPGroup' ⟨x, hx⟩
    exact mem_of_pow_three_pow_eq_one K hKc hF.1 (n := n) (congrArg Subtype.val hn)
  have hpg : IsPGroup 3 ((Q : Subgroup X).subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact Q.isPGroup'.comap_subtype
  have hidx : ¬ 3 ∣ ((Q : Subgroup X).subgroupOf K).index := by
    intro h
    apply Q.not_dvd_index
    rw [← Subgroup.relIndex_mul_index hQK]
    exact Dvd.dvd.mul_right h _
  set T : Sylow 3 ↥K := hpg.toSylow hidx with hTdef
  have hT : (T : Subgroup ↥K) = (Q : Subgroup X).subgroupOf K := IsPGroup.toSylow_coe _ _
  have hAK : A ≤ K := hAQ.trans hQK
  have hA'T : A.subgroupOf K ≤ (T : Subgroup ↥K) := by
    rw [hT]
    intro a ha
    exact Subgroup.mem_subgroupOf.2 (hAQ (Subgroup.mem_subgroupOf.1 ha))
  have hA'c : ∀ a ∈ A.subgroupOf K, ∀ t ∈ (T : Subgroup ↥K), a * t = t * a := by
    intro a ha t ht
    rw [hT] at ht
    apply Subtype.ext
    exact (hAc a (Subgroup.mem_subgroupOf.1 ha) t (Subgroup.mem_subgroupOf.1 ht)).symm
  have hA'card : Nat.card (A.subgroupOf K) = 3 := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  obtain ⟨g, hgN, hgA⟩ := hF.2 T (A.subgroupOf K) hA'T hA'c hA'card
  have hle : A.map (MulAut.conj (g : X)).toMonoidHom ≤ (Q : Subgroup X) := by
    rintro _ ⟨a, ha, rfl⟩
    have haT : (⟨a, hAK ha⟩ : ↥K) ∈ (T : Subgroup ↥K) := hA'T (Subgroup.mem_subgroupOf.2 ha)
    have hgaT := (Subgroup.mem_normalizer_iff.1 hgN _).1 haT
    rw [hT, Subgroup.mem_subgroupOf] at hgaT
    exact hgaT
  apply hgA
  rw [map_conj_subgroupOf K A hAK g, hwc (g : X) hle]

theorem mem_of_fixes_abelian_sylow (hIA : KFactInnerAction) {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hKcat : IsCatalogGroup K) (hKc : centralizer (K : Set X) = ⊥) (hKdvd : 3 ∣ Nat.card K)
    (S : Sylow 3 ↥K) (hab : IsMulCommutative (S : Subgroup ↥K)) {u : X} (hu : u ^ 3 = 1)
    (hfix : ∀ s ∈ (S : Subgroup ↥K), u * (s : X) = (s : X) * u) : u ∈ K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSne : (S : Subgroup ↥K) ≠ ⊥ := S.ne_bot_of_dvd_card hKdvd
  have hφ3 : (MulAut.conjNormal u : MulAut ↥K) ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hu, map_one]
  have hcomm : ∀ g ∈ (S : Subgroup ↥K),
      (MulAut.conjNormal u : MulAut ↥K) * MulAut.conj g =
        MulAut.conj g * (MulAut.conjNormal u : MulAut ↥K) := by
    intro g hg
    have hug : u * (g : X) = (g : X) * u := hfix g hg
    have hug' : u⁻¹ * (g : X)⁻¹ = (g : X)⁻¹ * u⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hug]
    refine MulEquiv.ext fun k => Subtype.ext ?_
    show u * ((g : X) * (k : X) * (g : X)⁻¹) * u⁻¹ = (g : X) * (u * (k : X) * u⁻¹) * (g : X)⁻¹
    calc u * ((g : X) * (k : X) * (g : X)⁻¹) * u⁻¹
        = (u * (g : X)) * (k : X) * ((g : X)⁻¹ * u⁻¹) := by group
      _ = ((g : X) * u) * (k : X) * (u⁻¹ * (g : X)⁻¹) := by rw [hug, hug']
      _ = (g : X) * (u * (k : X) * u⁻¹) * (g : X)⁻¹ := by group
  obtain ⟨g, -, hφg⟩ :=
    hIA 3 Nat.prime_three (by norm_num) ↥K hKs hKnab hKcat S hSne hab _ ⟨1, hφ3⟩ hcomm
  exact mem_of_conjNormal_mem_inner K hKc ⟨g, hφg.symm⟩

theorem false_of_abelian_sylow (hWC : KFactWeakClosure) (hIA : KFactInnerAction) {X : Type}
    [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKcat : IsCatalogGroup K)
    (hKc : centralizer (K : Set X) = ⊥) (hKdvd : 3 ∣ Nat.card K) (Q : Sylow 3 X) (S : Sylow 3 ↥K)
    (hSmem : ∀ s : ↥K, s ∈ (S : Subgroup ↥K) ↔ (s : X) ∈ (Q : Subgroup X))
    (hab : IsMulCommutative (S : Subgroup ↥K)) (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K))
    {A : Subgroup X} (hAQ : A ≤ (Q : Subgroup X)) (hA : Nat.card A = 3)
    (hAc : ∀ a ∈ A, ∀ q ∈ (Q : Subgroup X), q * a = a * q)
    (hwc : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) →
      A.map (MulAut.conj g).toMonoidHom = A) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := pow_eq_one_of_card_prime hA
  have hAK : A ≤ K := fun a ha =>
    mem_of_fixes_abelian_sylow hIA K hKs hKnab hKcat hKc hKdvd S hab (hApow a ha)
      (fun s hs => (hAc a ha s ((hSmem s).1 hs)).symm)
  have hSrk : 2 ≤ CFSG.Open.pRank 3 (S : Subgroup ↥K) := (pRank_top_eq_of_sylow S) ▸ h2
  have hA'S : A.subgroupOf K ≤ (S : Subgroup ↥K) := fun s hs =>
    (hSmem s).2 (hAQ (Subgroup.mem_subgroupOf.1 hs))
  have hA'card : Nat.card (A.subgroupOf K) = 3 := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  obtain ⟨g, hg1, hg2⟩ := wcOn_of_kFactWeakClosure hWC Nat.prime_three (by norm_num) hKs hKnab
    hKcat S hab hSrk (A.subgroupOf K) hA'S hA'card
  rw [map_conj_subgroupOf K A hAK g] at hg1 hg2
  have hAgK : A.map (MulAut.conj (g : X)).toMonoidHom ≤ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact K.mul_mem (K.mul_mem g.2 (hAK ha)) (K.inv_mem g.2)
  have hle : A.map (MulAut.conj (g : X)).toMonoidHom ≤ (Q : Subgroup X) := by
    intro y hy
    exact (hSmem ⟨y, hAgK hy⟩).1 (hg1 (Subgroup.mem_subgroupOf.2 hy))
  exact hg2 (by rw [hwc (g : X) hle])

theorem mem_of_fixes_small_sylow (hO : OuterThreeInner) {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hKcat : IsCatalogGroup K) (hKc : centralizer (K : Set X) = ⊥) (S : Sylow 3 ↥K)
    (hSn : ¬ IsMulCommutative (S : Subgroup ↥K)) (hfac : (Nat.card K).factorization 3 ≤ 3)
    {u : X} (hu : u ^ 3 = 1) (hfix : ∀ s ∈ (S : Subgroup ↥K), u * (s : X) * u⁻¹ = (s : X)) :
    u ∈ K := by
  apply mem_of_conjNormal_mem_inner K hKc
  refine hO ↥K hKs hKnab hKcat S hSn hfac _ (by rw [← map_pow, hu, map_one]) ?_
  intro s hs
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  exact hfix s hs

section Omega

variable {X : Type} [Group X] [Finite X] (Q : Sylow 3 X) {E : Subgroup X}

theorem omega_false_of_pair (hE : IsElemAbelian 3 E)
    (hall : ∀ y ∈ (Q : Subgroup X), y ^ 3 = 1 → y ∈ E) (h : HasNoncommPair 3 X) : False := by
  obtain ⟨x, y, hx, hy, hxy, hP⟩ := h
  obtain ⟨g, hg⟩ := exists_map_conj_le Q hP
  have hmem : ∀ z ∈ ({x, y} : Set X), g * z * g⁻¹ ∈ (Q : Subgroup X) := fun z hz =>
    hg ⟨z, Subgroup.subset_closure hz, rfl⟩
  have hxE : g * x * g⁻¹ ∈ E :=
    hall _ (hmem x (by simp)) (by rw [conj_pow, hx, mul_one, mul_inv_cancel])
  have hyE : g * y * g⁻¹ ∈ E :=
    hall _ (hmem y (by simp)) (by rw [conj_pow, hy, mul_one, mul_inv_cancel])
  have hc : (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩)
  apply hxy
  have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := hc
      _ = g * (y * x) * g⁻¹ := by group
  simpa using h1

theorem omega_false_of_elemAbelian (hEcard : Nat.card E = 27)
    (hall : ∀ y ∈ (Q : Subgroup X), y ^ 3 = 1 → y ∈ E) {F : Subgroup X}
    (hF : IsElemAbelian 3 F) (hFcard : 27 < Nat.card F) : False := by
  have hFp : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨g, hg⟩ := exists_map_conj_le Q hFp
  have hle : F.map (MulAut.conj g).toMonoidHom ≤ E := by
    rintro _ ⟨f, hf, rfl⟩
    refine hall _ (hg ⟨f, hf, rfl⟩) ?_
    show (g * f * g⁻¹) ^ 3 = 1
    rw [conj_pow, hF.2 f hf, mul_one, mul_inv_cancel]
  have h := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard] at h
  omega

end Omega

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
