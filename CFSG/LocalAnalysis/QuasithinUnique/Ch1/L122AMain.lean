module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AOut
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ATwoConj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Background.A3Structure36ABasic

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_1_three lemma_1_2_2_b
  Lemma122A lemma_1_2_4_exists lemma_1_2_4_unique lemma_1_2_4_existsUnique lemma_1_2_4_normal
  lemma_1_2_4_list normal_conjClosure_of_pCoreOf_ne_bot

namespace L122A

variable {G : Type} [Group G] [Finite G]

structure TwoFactor (H L : Subgroup G) (t : ↥H ⧸ CFSG.pCore 2 ↥H) : Prop where
  not_normalizes : t ∉ Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H))
  comm : ⁅modO2Image H L, conjSub t (modO2Image H L)⁆ = ⊥
  types : A38Types ↥(modO2Image H L)
  conj : ∀ g : ↥H ⧸ CFSG.pCore 2 ↥H, conjSub g (modO2Image H L) = modO2Image H L ∨
    conjSub g (modO2Image H L) = conjSub t (modO2Image H L)

theorem exists_twoFactor (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (hK : LocalSQTK G)
    {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H)
    (hcard : Set.ncard (conjSubgroupsBy H L) = 2) : ∃ t, TwoFactor H L t := by
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
  have hLb := modO2Image_mem_cComp hL
  obtain ⟨hL1, -⟩ := h38 _ hQ _ hLb
  rcases hL1 with hnorm | ⟨htypes, t, htn, hcomm, -, hcl⟩
  · exfalso
    have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
    have hn : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hnorm
    have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hL)).mp hn
    have hset : conjSubgroupsBy H L = {L} := by
      ext K'
      constructor
      · rintro ⟨h, hhH, rfl⟩
        exact A38.map_conj_eq_iff.mpr (hHN hhH)
      · rintro rfl
        exact ⟨1, H.one_mem, by ext x; simp⟩
    rw [hset, Set.ncard_singleton] at hcard
    omega
  · refine ⟨t, ⟨htn, hcomm, htypes, fun g => ?_⟩⟩
    have hLg := A38.cComp_conj (t := g) hLb
    have hLt' := A38.cComp_conj (t := t) hLb
    have hle : conjSub g (modO2Image H L) ≤ modO2Image H L ⊔ conjSub t (modO2Image H L) := by
      unfold conjSub
      rw [← hcl]
      intro x hx
      rw [A38.mem_map_conj] at hx
      have := mem_conjClosure (Subgroup.mem_top g) hx
      simpa [mul_assoc] using this
    exact A38.eq_or_eq_of_le_sup (h37 _ hQ) hLg hLb hLt' hle

theorem eq_one_of_forall_commute_of_simple {K : Type*} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (a : K) (ha : ∀ b : K, a * b = b * a) : a = 1 := by
  by_contra h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · have : a ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun b => (ha b).symm
    rw [h, Subgroup.mem_bot] at this
    exact h1 this
  · obtain ⟨c, d, hcd⟩ := hnab
    apply hcd
    have : c ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top c
    exact (Subgroup.mem_center_iff.mp this d).symm

theorem pElement_mem_conjClosure
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (hK : LocalSQTK G)
    {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Set.ncard (conjSubgroupsBy H L) = 2)
    (hdvd : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) (x : G) (hxH : x ∈ H)
    (hx : ∃ k : ℕ, orderOf x = p ^ k) : x ∈ conjClosure L H := by
  obtain ⟨k, hk⟩ := hx
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
  obtain ⟨t, htf⟩ := exists_twoFactor h37 h38 hK hH hL hcard
  have hLb : modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_mem_cComp hL
  have hns : ¬ Group.IsSolvable ↥(modO2Image H L) := not_isSolvable_of_mem_cComp hLb
  have hsimple : IsSimpleGroup ↥(modO2Image H L) := isSimpleGroup_of_a38Types htf.types
  have hnab : ∃ a b : ↥(modO2Image H L), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hns (Group.isSolvable_of_comm hcon)
  have hne : modO2Image H L ≠ conjSub t (modO2Image H L) := fun h =>
    htf.not_normalizes (conjSub_eq_iff.mp h.symm)
  have h₂ : ∀ g : ↥H ⧸ CFSG.pCore 2 ↥H, conjSub g (conjSub t (modO2Image H L)) = modO2Image H L ∨
      conjSub g (conjSub t (modO2Image H L)) = conjSub t (modO2Image H L) := fun g => by
    rw [conjSub_conjSub]
    exact htf.conj (g * t)
  set xH : ↥H := ⟨x, hxH⟩ with hxH_def
  have hxord : xH ^ (p ^ k) = 1 := by
    apply Subtype.ext
    change x ^ (p ^ k) = 1
    rw [← hk]
    exact pow_orderOf_eq_one x
  have hxb : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) xH) ^ (p ^ k) = 1 := by
    rw [← map_pow, hxord, map_one]
  obtain ⟨hn₁, hn₂⟩ := normalizes_of_pElement hne htf.conj h₂ hp hp2 hxb
  have hc : ∀ a ∈ modO2Image H L, ∀ b ∈ conjSub t (modO2Image H L), a * b = b * a := by
    intro a ha b hb
    have h := Subgroup.commutator_mem_commutator ha hb
    rw [htf.comm, Subgroup.mem_bot, commutatorElement_def] at h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  have hz₁ : ∀ a ∈ modO2Image H L, (∀ b ∈ modO2Image H L, a * b = b * a) → a = 1 := by
    intro a ha hab
    have := eq_one_of_forall_commute_of_simple (K := ↥(modO2Image H L)) hnab ⟨a, ha⟩
      (fun b => Subtype.ext (hab b b.2))
    exact congrArg Subtype.val this
  have hz₂ : ∀ a ∈ conjSub t (modO2Image H L),
      (∀ b ∈ conjSub t (modO2Image H L), a * b = b * a) → a = 1 := by
    intro a ha hab
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hb1 : b = 1 := hz₁ b hb fun c hc' => by
      have h := hab ((MulAut.conj t).toMonoidHom c) (Subgroup.mem_map_of_mem _ hc')
      apply (MulAut.conj t).injective
      rw [map_mul, map_mul]
      exact h
    rw [hb1, map_one]
  have hp₁ : p ∣ Nat.card ↥(modO2Image H L) := by
    obtain ⟨e⟩ := modO2_mulEquiv hL
    rw [← Nat.card_congr e.toEquiv]
    exact hdvd
  have hp₂ : p ∣ Nat.card ↥(conjSub t (modO2Image H L)) := by
    have hcc : Nat.card ↥(modO2Image H L) = Nat.card ↥(conjSub t (modO2Image H L)) :=
      Nat.card_congr (A38.conjEquiv t (modO2Image H L)).toEquiv
    rw [← hcc]
    exact hp₁
  have hout₁ : OutPLifts p ↥(modO2Image H L) := outPLifts_of_a38Types htf.types hp hp2
  have hout₂ : OutPLifts p ↥(conjSub t (modO2Image H L)) :=
    hout₁.of_mulEquiv (A38.conjEquiv t (modO2Image H L))
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp hQ.sqt) p hp hp2
  obtain ⟨a, ha, b, hb, hxab⟩ := mem_prodSub_of_pElement (hc := hc) hp hz₁ hz₂ hp₁ hp₂ hout₁
    hout₂ hrank hxb hn₁ hn₂
  have hle : conjClosure L H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (le_of_mem_cComp hL hz)) (H.inv_mem hh)
  have hΛn : ((conjClosure L H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (le_normalizer_conjClosure L H)
  set Λ : Subgroup ↥H := (conjClosure L H).subgroupOf H with hΛ
  have hLbΛ : modO2Image H L ≤ Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    apply Subgroup.map_mono
    intro y hy
    exact le_conjClosure L H hy
  have hN₂Λ : conjSub t (modO2Image H L) ≤ Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    obtain ⟨th, hth⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) t
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a', ha', rfl⟩ := hy
    refine ⟨th * a' * th⁻¹, ?_, ?_⟩
    · change ((th * a' * th⁻¹ : ↥H) : G) ∈ conjClosure L H
      have := mem_conjClosure th.2 ha'
      simpa using this
    · simp [← hth]
  have hxbΛ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) xH ∈
      Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    rw [hxab]
    exact (Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).mul_mem (hLbΛ ha) (hN₂Λ hb)
  obtain ⟨y, hyΛ, hyx⟩ := hxbΛ
  have ho : y⁻¹ * xH ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq (s := CFSG.pCore 2 ↥H)).mp hyx
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥H) ⟨y⁻¹ * xH, ho⟩
  have hj' : (y⁻¹ * xH) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hπ : QuotientGroup.mk' Λ xH = QuotientGroup.mk' Λ (y⁻¹ * xH) := by
    rw [map_mul]
    have : QuotientGroup.mk' Λ y⁻¹ = 1 := (QuotientGroup.eq_one_iff _).mpr (Λ.inv_mem hyΛ)
    rw [this, one_mul]
  have h1 : orderOf (QuotientGroup.mk' Λ xH) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxord, map_one])
  have h2 : orderOf (QuotientGroup.mk' Λ xH) ∣ 2 ^ j :=
    orderOf_dvd_of_pow_eq_one (by rw [hπ, ← map_pow, hj', map_one])
  have hcop : Nat.Coprime (p ^ k) (2 ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hord : orderOf (QuotientGroup.mk' Λ xH) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hone : QuotientGroup.mk' Λ xH = 1 := orderOf_eq_one_iff.mp hord
  have hxΛ : xH ∈ Λ := (QuotientGroup.eq_one_iff xH).mp hone
  exact hxΛ

theorem conjClosure_le_closure
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (hK : LocalSQTK G)
    {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) {p : ℕ} (hp : p.Prime)
    (hcard : Set.ncard (conjSubgroupsBy H L) = 2)
    (hdvd : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    conjClosure L H ≤ Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
  set O := Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} with hO
  have hinv : ∀ h ∈ H, ∀ z ∈ O, h * z * h⁻¹ ∈ O := by
    intro h hh z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      refine ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), ?_⟩
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
      rw [this]
      exact O.mul_mem ihx ihy
    | inv x _ ih =>
      have : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
      rw [this]
      exact O.inv_mem ih
  have hLO : L ≤ O := by
    have hperf : Group.IsPerfect ↥L := A36A.isPerfect_of_mem_cComp hL
    have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH
    obtain ⟨t, htf⟩ := exists_twoFactor h37 h38 hK hH hL hcard
    have hLb : modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      modO2Image_mem_cComp hL
    obtain ⟨e⟩ := modO2_mulEquiv hL
    have htypes : A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := A38Types.of_mulEquiv e.symm htf.types
    have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_a38Types htypes
    have hNn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
    have htop : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p ↥L = ⊤ :=
      primeResidual_eq_top_of_perfect hp (CFSG.pCore 2 ↥L) CFSG.pCore_isPGroup hdvd
    have : Fact p.Prime := ⟨hp⟩
    intro z hz
    have hz' : (⟨z, hz⟩ : ↥L) ∈ Subgroup.closure {a : ↥L | ∃ k : ℕ, orderOf a = p ^ k} := by
      rw [← CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure, htop]
      exact Subgroup.mem_top _
    have key : ∀ a : ↥L, a ∈ Subgroup.closure {a : ↥L | ∃ k : ℕ, orderOf a = p ^ k} →
        (a : G) ∈ O := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        apply Subgroup.subset_closure
        refine ⟨le_of_mem_cComp hL a.2, ?_⟩
        obtain ⟨k, hk⟩ := ha
        exact ⟨k, by rw [Subgroup.orderOf_coe, hk]⟩
      | one => exact O.one_mem
      | mul a b _ _ iha ihb => exact O.mul_mem iha ihb
      | inv a _ iha => exact O.inv_mem iha
    exact key _ hz'
  exact conjClosure_le fun h hh z hz => hinv h hh z (hLO hz)

end L122A

theorem lemma122A_of_localSQTK
    {G : Type} [Group G] [Finite G] (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hK : LocalSQTK G) {H L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hL : L ∈ cComp H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Set.ncard (conjSubgroupsBy H L) = 2) (hdvd : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = p ^ k} = conjClosure L H := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxH, hx⟩
    exact L122A.pElement_mem_conjClosure h37 h38 hK hH hL hp hp2 hcard hdvd x hxH hx
  · exact L122A.conjClosure_le_closure h37 h38 hK hH hL hp hcard hdvd

theorem lemma122A_of_inputs
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) : Lemma122A := by
  unfold Lemma122A
  intro G _ _ _ _ hq H L hH hL p hp hp2 hcard hdvd
  exact lemma122A_of_localSQTK h37 h38 hq.1 hH hL hp hp2 hcard hdvd

end CFSG.QuasithinUnique.Vol2Native
