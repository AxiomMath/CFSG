module

public import CFSG.CGT.PushingUpLit.CGT6.EmbTight
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

section TwoQuotient

variable {X : Type} [Group X] [Finite X]

theorem le_of_perfect_of_isPGroup_quotient {N P : Subgroup X} [N.Normal]
    (hN : IsPGroup 2 (X ⧸ N)) (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have h : N.subgroupOf P = ⊤ := by
    refine eq_top_of_perfect_two_quotient (E := ↥P) (N.subgroupOf P) fun e => ?_
    obtain ⟨n, hn⟩ := hN ((e : X) : X ⧸ N)
    refine ⟨n, ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, ← QuotientGroup.eq_one_iff,
      QuotientGroup.mk_pow]
    exact hn
  intro x hx
  have : (⟨x, hx⟩ : ↥P) ∈ N.subgroupOf P := by rw [h]; trivial
  exact this

omit [Finite X] in
theorem pCore_le_of_isPGroup_quotient {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 (X ⧸ N))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : pCore p X ≤ N := by
  intro x hx
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := p) (G := X)) ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hN (x : X ⧸ N)
  have h1 : (x : X ⧸ N) ^ p ^ a = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : x ^ p ^ a = 1 := congrArg Subtype.val ha
    rw [this]
    rfl
  have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp)
  have h2 := pow_gcd_eq_one.mpr ⟨h1, hb⟩
  rw [hcop.gcd_eq_one, pow_one] at h2
  exact (QuotientGroup.eq_one_iff x).mp h2

theorem fitting_le_of_isPGroup_quotient {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 (X ⧸ N))
    (hO : pCore 2 X = ⊥) : fittingSubgroup X ≤ N := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  by_cases h2 : p.1.1 = 2
  · rw [h2, hO]
    exact bot_le
  · exact pCore_le_of_isPGroup_quotient hN h2

theorem odd_card_center_of_pCore_eq_bot {Lx : Subgroup X} [Lx.Normal] (hO : pCore 2 X = ⊥) :
    Odd (Nat.card ↥(Subgroup.center ↥Lx)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have hev : 2 ∣ Nat.card ↥(Subgroup.center ↥Lx) := by
    have := Nat.not_odd_iff_even.mp hodd
    exact even_iff_two_dvd.mp this
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Lx)) 2 hev
  let Z : Subgroup X := (Subgroup.center ↥Lx).map Lx.subtype
  have hZn : Z.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hn
    have hgc : g * (c : X) * g⁻¹ ∈ Lx := (inferInstance : Lx.Normal).conj_mem _ c.2 g
    refine ⟨⟨g * (c : X) * g⁻¹, hgc⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center ↥Lx
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hl : g⁻¹ * (l : X) * g ∈ Lx := by
      simpa using (inferInstance : Lx.Normal).conj_mem _ l.2 g⁻¹
    have h1 := Subgroup.mem_center_iff.mp hc ⟨g⁻¹ * (l : X) * g, hl⟩
    have h2 : (g⁻¹ * (l : X) * g) * (c : X) = (c : X) * (g⁻¹ * (l : X) * g) :=
      congrArg Subtype.val h1
    calc (l : X) * (g * (c : X) * g⁻¹) = g * ((g⁻¹ * (l : X) * g) * (c : X)) * g⁻¹ := by group
      _ = g * ((c : X) * (g⁻¹ * (l : X) * g)) * g⁻¹ := by rw [h2]
      _ = g * (c : X) * g⁻¹ * (l : X) := by group
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hb a)
  let z' : X := ((z : ↥Lx) : X)
  have hz'Z : z' ∈ Z := ⟨z, z.2, rfl⟩
  have hz'2 : z' ^ 2 = 1 := by
    have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h3 := congrArg (fun w : ↥(Subgroup.center ↥Lx) => ((w : ↥Lx) : X)) this
    simpa using h3
  have hz'1 : z' ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hz
    omega
  let M : Subgroup X := Subgroup.normalClosure {z'}
  have hMZ : M ≤ Z := Subgroup.normalClosure_le_normal (by simpa using hz'Z)
  have hM2 : IsPGroup 2 ↥M := by
    intro m
    refine ⟨1, Subtype.ext ?_⟩
    have key : ∀ x ∈ M, x ^ 2 = 1 := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => x ^ 2 = 1) ?_ ?_ ?_ ?_ hx
      · intro x hx'
        obtain ⟨y, hy, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx'
        obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
        have hy' : y = z' := by simpa using hy
        rw [hy']
        rw [conj_pow, hz'2]
        group
      · simp
      · intro x y hx hy hpx hpy
        have hxZ : x ∈ Z := hMZ hx
        have hyZ : y ∈ Z := hMZ hy
        have hc : Commute x y := hZc x hxZ y hyZ
        rw [hc.mul_pow, hpx, hpy, one_mul]
      · intro x hx hpx
        rw [inv_pow, hpx, inv_one]
    simpa using key m m.2
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hMle : M ≤ pCore 2 X := le_sSup ⟨hMn, hM2⟩
  rw [hO] at hMle
  have : z' ∈ M := Subgroup.subset_normalClosure rfl
  exact hz'1 (by simpa using hMle this)

theorem layer_le_of_isPGroup_quotient {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 (X ⧸ N)) :
    layer X ≤ N := by
  refine sSup_le fun K hK => ?_
  have : Group.IsPerfect ↥K := hK.1.1
  exact le_of_perfect_of_isPGroup_quotient hN (Subgroup.isPerfect_iff.mp this)

theorem layer_eq_of_minimal {Ax : Subgroup X} {Lx : Subgroup X} [Lx.Normal]
    (hN : IsPGroup 2 (X ⧸ Lx)) (hmin : ∀ N : Subgroup X, N.Normal → Ax ≤ N → Lx ≤ N)
    (hA : Ax ≤ layer X) : layer X = Lx := by
  refine le_antisymm (layer_le_of_isPGroup_quotient hN) ?_
  have : (layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  exact hmin _ inferInstance hA

theorem pLayer_le_layer_of_centralizes {Lx : Subgroup X} [Lx.Normal] (hN : IsPGroup 2 (X ⧸ Lx))
    (hLQ : ⁅Lx, pPrimeCore 2 X⁆ = ⊥) : pLayer X 2 ≤ layer X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine sSup_le fun J hJ => ?_
  have hperf : Group.IsPerfect ↥J :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 J hJ
  have hJL : J ≤ Lx := le_of_perfect_of_isPGroup_quotient hN (Subgroup.isPerfect_iff.mp hperf)
  obtain ⟨K, hK, hJsub, hmap, -⟩ := hJ
  have hJC : J ≤ Subgroup.centralizer (pPrimeCore 2 X : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp (hLQ ▸ Subgroup.commutator_mono hJL le_rfl))
  let f : ↥J →* ↥K := ((QuotientGroup.mk' (pPrimeCore 2 X)).comp J.subtype).codRestrict K
    (fun j => hmap ▸ ⟨j, j.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj, hjk⟩ := (hmap ▸ hk : k ∈ J.map (QuotientGroup.mk' (pPrimeCore 2 X)))
    exact ⟨⟨j, hj⟩, Subtype.ext hjk⟩
  have hker : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 X)) (j : X) = 1 := congrArg Subtype.val hj
    have h2 : (j : X) ∈ pPrimeCore 2 X := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro j'
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hJC j'.2) _ h2).symm
  have hq : CFSG.IsQuasisimple ↥J :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf f hf hker).mpr hK.1
  exact CFSG.LocalCores.component_le_layer ⟨hq, hJsub⟩

theorem le_pLayer_of_component_centralizer
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections X) {P A : Subgroup X}
    (hP : IsPGroup 2 P) (hq : CFSG.IsQuasisimple ↥A) (hAC : A ≤ Subgroup.centralizer (P : Set X))
    (hs : (A.subgroupOf (Subgroup.centralizer (P : Set X))).IsSubnormal) : A ≤ pLayer X 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.ComponentClassification.Sol76.le_pLayer_of_isQuasisimple hAC hq hs
  have h2 := CFSG.ComponentClassification.LBalance.lBalancePLayer_centralizer_le (p := 2) hSch P hP
  rw [← CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map,
    CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_top] at *
  exact h1.trans h2

theorem component_normal_of_centralizes {K Lx Tx Ax : Subgroup X} (hK : CFSG.IsComponent K)
    (hAK : Ax ≤ K) (hAperf : ⁅Ax, Ax⁆ = Ax) (hA1 : Ax ≠ ⊥) (hL : Lx ≤ layer X)
    (hT : Tx ≤ Subgroup.centralizer (Ax : Set X)) (hLT : Lx ⊔ Tx = ⊤) : K.Normal := by
  have hLn : Lx ≤ Subgroup.normalizer (K : Set X) :=
    hL.trans (CFSG.LocalCores.layer_le_normalizer hK)
  have hTn : Tx ≤ Subgroup.normalizer (K : Set X) := by
    intro t ht
    have hKt : CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
    have hAt : Ax ≤ K.map (MulAut.conj t).toMonoidHom := by
      intro a ha
      refine ⟨a, hAK ha, ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp (hT ht) a ha
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← h1]
      group
    rcases CFSG.LocalCores.distinct_components_commute hK hKt with h | h
    · rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
          ⟨k, hk, by simp [MulAut.conj_apply]⟩
        rwa [← h] at this
      · intro hk
        rw [h] at hk
        obtain ⟨k', hk', hkk⟩ := hk
        have : k' = k := by
          simpa [MulAut.conj_apply] using hkk
        rwa [this] at hk'
    · exfalso
      have h2 : ⁅Ax, Ax⁆ ≤ ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ :=
        Subgroup.commutator_mono hAK hAt
      rw [h, le_bot_iff, hAperf] at h2
      exact hA1 h2
  have hnorm : Subgroup.normalizer (K : Set X) = ⊤ :=
    top_le_iff.mp (hLT ▸ sup_le hLn hTn)
  exact Subgroup.normalizer_eq_top_iff.mp hnorm

end TwoQuotient

section Cfg

variable {V : Type} [CommGroup V] [Finite V]

open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def FourSeven : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y →
      ∀ X : Subgroup (MulAut V), X ≤ G → ¬ 2 ∣ Nat.card X →
        Y ≤ Subgroup.normalizer (X : Set (MulAut V)) →
          X ≤ Subgroup.centralizer (Y : Set (MulAut V))

omit [CommGroup V] [Finite V] in
theorem openIsKGroup_of_isKGroup {X : Type} [Group X] (h : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup X := fun K L _ _ hsimple _ => h K (L.subgroupOf K) hsimple

omit [CommGroup V] [Finite V] in
theorem schreierSections_of_isKGroup (hS : SchreierFor Assembly.InCatalog) {X : Type} [Group X]
    [Finite X] (h : CFSG.IsKGroup X) : LBalance.SchreierSections X :=
  LBalance.SchreierSections.of_isKGroup (fun S _ _ _ hnc hcat => hS S hnc hcat)
    (openIsKGroup_of_isKGroup h)

omit [CommGroup V] [Finite V] in
theorem isPGroup_quotient_of_sup_eq_top {X : Type} [Group X] {Lx Tx : Subgroup X} [Lx.Normal]
    (hT : IsPGroup 2 Tx) (hLT : Lx ⊔ Tx = ⊤) : IsPGroup 2 (X ⧸ Lx) := by
  intro xb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hx : x ∈ Lx ⊔ Tx := hLT ▸ Subgroup.mem_top x
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine ⟨k, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul, ← QuotientGroup.mk_pow]
  have : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [this]
  rfl

omit [Finite V] in
theorem centralizer_subgroupOf_eq {G T : Subgroup (MulAut V)} (hTG : T ≤ G) :
    Subgroup.centralizer ((T.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      (G ⊓ Subgroup.centralizer (T : Set (MulAut V))).subgroupOf G := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, fun t ht => ?_⟩
    have := h ⟨t, hTG ht⟩ (Subgroup.mem_subgroupOf.mpr ht)
    exact congrArg Subtype.val this
  · rintro ⟨-, h⟩ t ht
    apply Subtype.ext
    exact h _ (Subgroup.mem_subgroupOf.mp ht)

omit [Finite V] in
theorem isPGroup_subgroupOf {G T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT : IsPGroup 2 ↥T) :
    IsPGroup 2 ↥(T.subgroupOf G) :=
  IsPGroup.of_surjective hT (Subgroup.subgroupOfEquivOfLe hTG).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTG).symm.surjective

omit [Finite V] in
theorem le_normalizer_map_subtype {G : Subgroup (MulAut V)} (N : Subgroup ↥G) [N.Normal] :
    G ≤ Subgroup.normalizer ((N.map G.subtype : Subgroup (MulAut V)) : Set (MulAut V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ (g : ↥G) (h : MulAut V), h ∈ N.map G.subtype →
      (g : MulAut V) * h * (g : MulAut V)⁻¹ ∈ N.map G.subtype := by
    rintro g _ ⟨n, hn, rfl⟩
    exact ⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n hn g, by simp⟩
  intro h
  constructor
  · exact key ⟨g, hg⟩ h
  · intro h2
    have h3 := key ⟨g, hg⟩⁻¹ _ h2
    have e : ((⟨g, hg⟩⁻¹ : ↥G) : MulAut V) * (g * h * g⁻¹) *
        ((⟨g, hg⟩⁻¹ : ↥G) : MulAut V)⁻¹ = h := by
      simp [mul_assoc]
    rwa [e] at h3

structure LayerOut (G Y : Subgroup (MulAut V)) : Prop where
  y_le : Y.subgroupOf G ≤ CFSG.layer ↥G
  layer_eq : CFSG.layer ↥G = (conjClosure Y G).subgroupOf G
  fstar : generalizedFitting ↥G = (conjClosure Y G).subgroupOf G
  oddZ : Odd (Nat.card ↥(Subgroup.center ↥(conjClosure Y G)))
  quasi_of_comp : (∃ K : Subgroup ↥G, CFSG.IsComponent K ∧ Y.subgroupOf G ≤ K) →
    CFSG.Open.IsQuasisimple ↥(conjClosure Y G)

theorem layerOut_of_cfg (hS : SchreierFor Assembly.InCatalog) (h47 : FourSeven)
    (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)} (cfg : Emb4Cfg G T Y)
    (h9 : Out49 G Y) : LayerOut G Y := by
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hTG : T ≤ G := cfg.adm.hTG
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hLn : ((conjClosure Y G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr le_normalizer_conjClosure
  have hSch := schreierSections_of_isKGroup hS cfg.kgroup
  have hQS : Nine7.QS (Y.subgroupOf G) := qs_subgroupOf hV hYG cfg.adm.hperf h9.hcls2
  have hq : CFSG.IsQuasisimple ↥(Y.subgroupOf G) :=
    ⟨⟨hQS.1⟩, hQS.2, Nine7.exists_noncomm_center_quotient hQS⟩
  have hT2 : IsPGroup 2 ↥(T.subgroupOf G) := isPGroup_subgroupOf hTG cfg.adm.hT2
  have hcent := centralizer_subgroupOf_eq hTG
  have hAC : Y.subgroupOf G ≤ Subgroup.centralizer ((T.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    rw [hcent]
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr (cfg.adm.hYC (Subgroup.mem_subgroupOf.mp ha))
  have hs : ((Y.subgroupOf G).subgroupOf
      (Subgroup.centralizer ((T.subgroupOf G : Subgroup ↥G) : Set ↥G))).IsSubnormal := by
    rw [hcent]
    exact (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff (B := Y)
      (L := G ⊓ Subgroup.centralizer (T : Set (MulAut V))) (K := G) inf_le_left).mpr cfg.adm.hsub
  have hA2 : Y.subgroupOf G ≤ pLayer ↥G 2 :=
    le_pLayer_of_component_centralizer hSch hT2 hq hAC hs
  have hLT : (conjClosure Y G).subgroupOf G ⊔ T.subgroupOf G = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLG,
      Subgroup.map_subgroupOf_eq_of_le hTG, cfg.gen, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hN : IsPGroup 2 (↥G ⧸ (conjClosure Y G).subgroupOf G) :=
    isPGroup_quotient_of_sup_eq_top hT2 hLT
  have hmin : ∀ N : Subgroup ↥G, N.Normal → Y.subgroupOf G ≤ N →
      (conjClosure Y G).subgroupOf G ≤ N := by
    intro N hNn hAN
    have h1 : conjClosure Y G ≤ N.map G.subtype := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      exact ⟨⟨g, hg⟩ * ⟨y, hYG hy⟩ * ⟨g, hg⟩⁻¹,
        hNn.conj_mem _ (hAN (Subgroup.mem_subgroupOf.mpr hy)) ⟨g, hg⟩, by simp⟩
    have h2 := Subgroup.comap_mono (f := G.subtype) h1
    rwa [Subgroup.comap_map_eq_self_of_injective G.subtype_injective] at h2
  have hLQ : ⁅(conjClosure Y G).subgroupOf G, pPrimeCore 2 ↥G⁆ = ⊥ := by
    have hQn : (pPrimeCore 2 ↥G).Normal := CFSG.pPrimeCore_normal
    let Q' : Subgroup (MulAut V) := (pPrimeCore 2 ↥G).map G.subtype
    have hodd : ¬ 2 ∣ Nat.card Q' := by
      have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥G)
      have h2 : Nat.card Q' = Nat.card (pPrimeCore 2 ↥G) :=
        Subgroup.card_map_of_injective G.subtype_injective
      rw [h2]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hc
    have hnorm : Y ≤ Subgroup.normalizer (Q' : Set (MulAut V)) :=
      hYG.trans (le_normalizer_map_subtype (pPrimeCore 2 ↥G))
    have hQY : Q' ≤ Subgroup.centralizer (Y : Set (MulAut V)) :=
      h47 V hV G T Y cfg Q' (Subgroup.map_subtype_le _) hodd hnorm
    have hLc : conjClosure Y G ≤ Subgroup.centralizer (Q' : Set (MulAut V)) := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : g⁻¹ * q * g ∈ Q' := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_map_subtype (pPrimeCore 2 ↥G)
          (G.inv_mem hg)) q).mp hq
        rwa [inv_inv] at this
      have hcomm := Subgroup.mem_centralizer_iff.mp (hQY hq') y hy
      calc q * (g * y * g⁻¹) = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcomm]
        _ = g * y * g⁻¹ * q := by group
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl q hq
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hLc hl) (q : MulAut V) ⟨q, hq, rfl⟩
  have hAlayer : Y.subgroupOf G ≤ layer ↥G := hA2.trans (pLayer_le_layer_of_centralizes hN hLQ)
  have hlayer : layer ↥G = (conjClosure Y G).subgroupOf G := layer_eq_of_minimal hN hmin hAlayer
  refine ⟨hAlayer, hlayer, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le (fitting_le_of_isPGroup_quotient hN cfg.o2) hlayer.le) ?_
    exact hlayer.symm.le.trans le_sup_right
  · have hodd := odd_card_center_of_pCore_eq_bot (Lx := (conjClosure Y G).subgroupOf G) cfg.o2
    let e : ↥(conjClosure Y G) ≃* ↥((conjClosure Y G).subgroupOf G) :=
      (Subgroup.subgroupOfEquivOfLe hLG).symm
    rwa [← Nat.card_congr (Subgroup.centerCongr e).toEquiv] at hodd
  · rintro ⟨K, hK, hAK⟩
    have hA1 : Y.subgroupOf G ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hq)
    have hperf : ⁅Y.subgroupOf G, Y.subgroupOf G⁆ = Y.subgroupOf G :=
      Subgroup.isPerfect_iff.mp hq.1
    have hKn : K.Normal := component_normal_of_centralizes hK hAK hperf hA1 hlayer.symm.le
      (Subgroup.le_centralizer_iff.mp hAC) hLT
    have hLK : (conjClosure Y G).subgroupOf G ≤ K := hmin K hKn hAK
    have hKL : K ≤ (conjClosure Y G).subgroupOf G :=
      hlayer ▸ CFSG.LocalCores.component_le_layer hK
    have heq : (conjClosure Y G).subgroupOf G = K := le_antisymm hLK hKL
    have hQK : CFSG.Open.IsQuasisimple ↥K := ⟨hK.1.1.commutator_eq_top, hK.1.2.1⟩
    have hQL : CFSG.Open.IsQuasisimple ↥((conjClosure Y G).subgroupOf G) := by
      rw [heq]
      exact hQK
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hLG).symm hQL

end Cfg

section DiagFree

@[expose] def DiagFree : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → Out49 G Y → LayerOut G Y →
      (∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤) →
      (¬ ∃ K : Subgroup ↥G, CFSG.IsComponent K ∧ Y.subgroupOf G ≤ K) → False

end DiagFree

section Assembly

@[expose] def IrrStep : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → Out49 G Y →
      ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem step410_of_parts (hS : SchreierFor Assembly.InCatalog) (h47 : FourSeven)
    (hD : DiagFree) (hI : IrrStep) : Step410 := by
  intro V _ _ hV G T Y cfg h9
  have hL := layerOut_of_cfg hS h47 hV cfg h9
  have hirr := hI V hV G T Y cfg h9
  have hcomp : ∃ K : Subgroup ↥G, CFSG.IsComponent K ∧ Y.subgroupOf G ≤ K := by
    by_contra h
    exact hD V hV G T Y cfg h9 hL hirr h
  exact ⟨hL.quasi_of_comp hcomp, hL.fstar, hL.oddZ, hirr⟩

end Assembly

end CFSG.CGT.PushingUpLit.CGT6
