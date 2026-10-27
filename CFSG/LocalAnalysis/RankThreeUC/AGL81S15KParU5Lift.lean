module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCore
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.KParU5Proof

@[expose] noncomputable def pairHom {G' : Type*} [Group G'] {x y : G'} (hxy : x * y = y * x) :
    ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y) →* G' :=
  (Subgroup.zpowers x).subtype.noncommCoprod (Subgroup.zpowers y).subtype (by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow (show Commute x y from hxy) i j))

theorem pairHom_apply {G' : Type*} [Group G'] {x y : G'} (hxy : x * y = y * x)
    (p : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y)) :
    pairHom hxy p = (p.1 : G') * (p.2 : G') := rfl

theorem exists_pow_of_mem_zpowers {G' : Type*} [Group G'] {q : ℕ} {x u : G'} (hq : 0 < q)
    (hxq : x ^ q = 1) (hu : u ∈ Subgroup.zpowers x) : ∃ i : ℕ, x ^ i = u := by
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨q, hq, hxq⟩
  exact (Submonoid.mem_powers_iff u x).1 (hfin.mem_powers_iff_mem_zpowers.2 hu)

theorem pairHom_injective {G' : Type*} [Group G'] {q : ℕ} {x y : G'} (hxy : x * y = y * x)
    (hq : 0 < q) (hxq : x ^ q = 1) (hyq : y ^ q = 1)
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → q ∣ i ∧ q ∣ j) : Function.Injective (pairHom hxy) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ h
  obtain ⟨i, rfl⟩ := exists_pow_of_mem_zpowers hq hxq hu
  obtain ⟨j, rfl⟩ := exists_pow_of_mem_zpowers hq hyq hv
  rw [MonoidHom.mem_ker, pairHom_apply] at h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hind i j h
  subst ha
  subst hb
  rw [Subgroup.mem_bot]
  ext
  · simp [pow_mul, hxq]
  · simp [pow_mul, hyq]

theorem prod_pow_eq_one {G' : Type*} [Group G'] {q : ℕ} {x y : G'} (hq : 0 < q) (hxq : x ^ q = 1)
    (hyq : y ^ q = 1) (p : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y)) : p ^ q = 1 := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
  obtain ⟨i, rfl⟩ := exists_pow_of_mem_zpowers hq hxq hu
  obtain ⟨j, rfl⟩ := exists_pow_of_mem_zpowers hq hyq hv
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp only [Prod.pow_fst, SubgroupClass.coe_pow, Prod.fst_one, OneMemClass.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hxq, one_pow]
  · simp only [Prod.pow_snd, SubgroupClass.coe_pow, Prod.snd_one, OneMemClass.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hyq, one_pow]

theorem range_pow_eq_one {G' : Type*} [Group G'] {q : ℕ} {x y : G'} (hxy : x * y = y * x)
    (hq : 0 < q) (hxq : x ^ q = 1) (hyq : y ^ q = 1) (e : ↥(pairHom hxy).range) : e ^ q = 1 := by
  obtain ⟨e, p, rfl⟩ := e
  apply Subtype.ext
  change (pairHom hxy p) ^ q = 1
  rw [← map_pow, prod_pow_eq_one hq hxq hyq, map_one]

theorem not_isCyclic_range {G' : Type*} [Group G'] {q : ℕ} (hq : q.Prime) {x y : G'}
    (hxy : x * y = y * x) (hxq : x ^ q = 1) (hyq : y ^ q = 1)
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → q ∣ i ∧ q ∣ j) : ¬ IsCyclic ↥(pairHom hxy).range := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hcyc
  have hinj := pairHom_injective hxy hq.pos hxq hyq hind
  have hx1 : x ≠ 1 := fun h => by
    have := (hind 1 0 (by simp [h])).1
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hy1 : y ≠ 1 := fun h => by
    have := (hind 0 1 (by simp [h])).2
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hox : orderOf x = q := orderOf_eq_prime hxq hx1
  have hoy : orderOf y = q := orderOf_eq_prime hyq hy1
  have hcard : Nat.card ↥(pairHom hxy).range = q * q := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hox, hoy]
  have hexp : Monoid.exponent ↥(pairHom hxy).range ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (range_pow_eq_one hxy hq.pos hxq hyq)
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have := Nat.le_of_dvd hq.pos hexp
  nlinarith [hq.one_lt]

theorem two_le_pRank_of_lift {G G' : Type*} [Group G] [Finite G] [Group G'] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (g : G →* G') {𝒢 : Subgroup G} {x y : G'}
    (hx : x ∈ 𝒢.map g) (hy : y ∈ 𝒢.map g) (hxq : x ^ q = 1) (hyq : y ^ q = 1)
    (hxy : x * y = y * x) (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → q ∣ i ∧ q ∣ j) :
    2 ≤ CFSG.Open.pRank q 𝒢 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  by_contra hlt
  have hr : CFSG.Open.pRank q 𝒢 ≤ 1 := by omega
  set E : Subgroup G' := (pairHom hxy).range with hE
  have hEle : E ≤ 𝒢.map g := by
    rintro _ ⟨⟨u, v⟩, rfl⟩
    rw [pairHom_apply]
    exact mul_mem ((Subgroup.zpowers_le.2 hx) u.2) ((Subgroup.zpowers_le.2 hy) v.2)
  have hEnc : ¬ IsCyclic ↥E := not_isCyclic_range hq hxy hxq hyq hind
  have hEpow : ∀ e : ↥E, e ^ q = 1 := range_pow_eq_one hxy hq.pos hxq hyq
  set N : Subgroup G := 𝒢 ⊓ E.comap g with hN
  set gN : ↥N →* ↥E := (g.comp N.subtype).codRestrict E (fun n => n.2.2) with hgN
  have hgNsurj : Function.Surjective gN := by
    rintro ⟨e, he⟩
    obtain ⟨a, ha, hae⟩ := hEle he
    refine ⟨⟨a, ha, show g a ∈ E by rw [hae]; exact he⟩, ?_⟩
    apply Subtype.ext
    exact hae
  obtain ⟨S₁⟩ : Nonempty (Sylow q ↥N) := inferInstance
  have hP : IsPGroup q (⊤ : Subgroup ↥E) := fun e =>
    ⟨1, Subtype.ext (by simpa using hEpow e.1)⟩
  have hS₂ : (S₁.mapSurjective hgNsurj : Subgroup ↥E) = ⊤ :=
    ((S₁.mapSurjective hgNsurj).is_maximal' hP le_top).symm
  have hS₁img : (S₁ : Subgroup ↥N).map gN = ⊤ := by
    rw [← Sylow.coe_mapSurjective hgNsurj S₁]
    exact hS₂
  set S : Subgroup G := (S₁ : Subgroup ↥N).map N.subtype with hS
  have hSp : IsPGroup q S := S₁.isPGroup'.map N.subtype
  have hSle : S ≤ 𝒢 := (Subgroup.map_subtype_le _).trans inf_le_left
  have hr' : CFSG.pRank q ↥𝒢 ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hr
  have hcyc : IsCyclic ↥S := CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hq hq2 hSle hSp hr'
  have hSE : ∀ s : ↥S, g (s : G) ∈ E := by
    rintro ⟨_, n, -, rfl⟩
    exact n.2.2
  set gS : ↥S →* ↥E := (g.comp S.subtype).codRestrict E hSE with hgS
  have hgSsurj : Function.Surjective gS := by
    intro e
    have he : e ∈ (S₁ : Subgroup ↥N).map gN := by rw [hS₁img]; trivial
    obtain ⟨s₁, hs₁, hse⟩ := he
    exact ⟨⟨(s₁ : G), s₁, hs₁, rfl⟩, Subtype.ext (congrArg Subtype.val hse)⟩
  exact hEnc (isCyclic_of_surjective gS hgSsurj)

section Node

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

variable {W : Type} [Group W] [Finite W] {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}

theorem exists_node_lift {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      ∃ P : Subgroup W, IsMinOverBorel L S₀ P ∧
        ∀ x ∈ rankOne D.rootGroup i, ∃ a : ↥L,
          QuotientGroup.mk' (Subgroup.center ↥L) a = π' x ∧ (a : W) ∈ pElementSubgroup 2 P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS h
  obtain ⟨Pk, hBP, hLP, hmin⟩ := node_parabolic hS hπ' hT i
  refine ⟨π', hπ', _, hmin, ?_⟩
  set Z := Subgroup.center ↥L with hZ
  set q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hqdef
  set PL : Subgroup ↥L := (Pk.map π').comap q with hPL
  have hlift : ∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Pk →
      ∃ a : ↥L, q a = π' x ∧ (a : W) ∈ pElementSubgroup 2 (PL.map L.subtype) := by
    intro x hx hxP
    obtain ⟨a, haq, haP, k, hk⟩ := exists_two_lift (π := π') Pk hx hxP
    exact ⟨a, haq, Subgroup.subset_closure ⟨⟨a, haP, rfl⟩, k, by
      rw [Subgroup.orderOf_coe]; exact hk⟩⟩
  have hroot2 : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → ∀ x ∈ D.rootGroup γ, ∃ k : ℕ, x ^ 2 ^ k = 1 :=
    fun γ hγ x hx => by
      obtain ⟨k, hk⟩ := hπ'.pGroup γ hγ ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hαroot : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)⟩
  set G : Subgroup ↥L := (pElementSubgroup 2 (PL.map L.subtype)).subgroupOf L with hG
  set T : Subgroup K := (G.map q).comap π' with hTdef
  have hrankT : rankOne D.rootGroup i ≤ T := by
    have hroot : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → D.rootGroup γ ≤ rankOne D.rootGroup i →
        D.rootGroup γ ≤ T := by
      intro γ hγ hγL x hx
      obtain ⟨a, haq, haW⟩ := hlift x (hroot2 γ hγ x hx) (hLP (hγL hx))
      exact ⟨a, Subgroup.mem_subgroupOf.2 haW, haq⟩
    show D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ T
    exact sup_le (hroot _ hαroot.1 le_sup_left) (hroot _ hαroot.2 le_sup_right)
  intro x hx
  obtain ⟨a, haG, haq⟩ := hrankT hx
  exact ⟨a, haq, Subgroup.mem_subgroupOf.1 haG⟩

theorem exists_minOver_two_le_pRank {L S₀ : Subgroup W} (hS : IsSylowTwoOf S₀ L)
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) (i : Fin D.rank) {N : ℕ}
    (hinj : ∀ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M →
      ∀ z ∈ rankOne D.rootGroup i, π' z = 1 → z = 1)
    (hell : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ N → ∃ a ∈ rankOne D.rootGroup i,
      ∃ b ∈ rankOne D.rootGroup i, a ^ q = 1 ∧ b ^ q = 1 ∧ a * b = b * a ∧
        ∀ s t : ℕ, a ^ s * b ^ t = 1 → q ∣ s ∧ q ∣ t) :
    ∃ P : Subgroup W, IsMinOverBorel L S₀ P ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ N → 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P) := by
  classical
  obtain ⟨π', hπ', P, hmin, hlift⟩ := exists_node_lift hS h i
  refine ⟨P, hmin, fun q hq hq2 hqN => ?_⟩
  obtain ⟨a, ha, b, hb, haq, hbq, hab, hind⟩ := hell q hq hq2 hqN
  set 𝒢 : Subgroup ↥L := (pElementSubgroup 2 P).subgroupOf L with h𝒢
  have hmem : ∀ x ∈ rankOne D.rootGroup i,
      π' x ∈ 𝒢.map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    intro x hx
    obtain ⟨c, hcx, hc⟩ := hlift x hx
    exact ⟨c, Subgroup.mem_subgroupOf.2 hc, hcx⟩
  have key := two_le_pRank_of_lift hq hq2 (QuotientGroup.mk' (Subgroup.center ↥L)) (hmem a ha)
    (hmem b hb) (by rw [← map_pow, haq, map_one]) (by rw [← map_pow, hbq, map_one])
    (by rw [← map_mul, ← map_mul, hab]) (fun s t hst => hind s t (hinj π' hπ' _
      (mul_mem (pow_mem ha s) (pow_mem hb t)) (by rw [map_mul, map_pow, map_pow]; exact hst)))
  have hP : pElementSubgroup 2 P ≤ L := (pElementSubgroup_le P).trans hmin.1
  have hmap : 𝒢.map L.subtype = pElementSubgroup 2 P := Subgroup.map_subgroupOf_eq_of_le hP
  rw [← hmap]
  exact key.trans (CFSG.SectionRank.pRank_le_map hq.one_lt L.subtype L.subtype_injective 𝒢)

end Node

end CFSG.LocalAnalysis.RankThreeUC.S15.KParU5Proof
