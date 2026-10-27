module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.GH74.GLS.Stage1.Main.BrPairSwap

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup

namespace InnerQ.KFC1

variable {X : Type} [Group X] [Finite X]

theorem mem_centralizer_of_isCyclic {A : Subgroup X} (hA : IsCyclic A) (hAp : IsPGroup 3 A)
    {x g : X} (hxA : x ∈ A) (hxo : orderOf x = 3) (hgA : g ∈ normalizer (A : Set X))
    (hgx : g * x = x * g) (hg : Nat.Coprime 3 (orderOf g)) :
    g ∈ centralizer (A : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.commutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconjA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.mp hgA a).mp ha
  rw [mem_centralizer_iff]
  intro a ha
  by_contra hne
  set c := g * a * g⁻¹ * a⁻¹ with hc
  have hcA : c ∈ A := mul_mem (hconjA a ha) (inv_mem ha)
  have hc1 : c ≠ 1 := by
    intro h
    apply hne
    rw [hc, mul_inv_eq_one] at h
    calc a * g = g * a * g⁻¹ * g := by rw [h]
      _ = g * a := by group
  have hga : g * a * g⁻¹ = c * a := by rw [hc]; group
  have hpow : ∀ m : ℕ, g * a ^ m * g⁻¹ = c ^ m * a ^ m := by
    intro m
    rw [← conj_pow, hga, (Commute.mul_pow (hcomm c hcA a ha) m)]
  obtain ⟨n, hn⟩ := hAp ⟨c, hcA⟩
  have hcn : c ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨j, hj, hoc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hcn)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := by
    rcases j with _ | k
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hoc)) hc1
    · exact ⟨k, rfl⟩
  set c' := c ^ 3 ^ k with hc'
  have hc'o : orderOf c' = 3 := by
    rw [hc', orderOf_pow' c (pow_ne_zero _ (by norm_num)), hoc, pow_succ,
      Nat.gcd_mul_right_left]
    simp
  have hc'A : c' ∈ A := pow_mem hcA _
  have hc'x : c' ∈ zpowers x := by
    have heq : zpowers (⟨c', hc'A⟩ : A) = zpowers (⟨x, hxA⟩ : A) :=
      (IsCyclic.subgroup_eq_iff_card_eq).mpr (by
        rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc'o,
          hxo])
    have h1 : (⟨c', hc'A⟩ : A) ∈ zpowers (⟨x, hxA⟩ : A) := heq ▸ mem_zpowers _
    obtain ⟨i, hi⟩ := h1
    exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  have hgc' : g * c' = c' * g := by
    obtain ⟨i, hi⟩ := hc'x
    rw [← hi]
    exact (Commute.zpow_right hgx i).eq
  set b := a ^ 3 ^ k with hb
  have hgb : g * b * g⁻¹ = c' * b := by rw [hb, hpow, hc']
  have hiter : ∀ m : ℕ, g ^ m * b * (g ^ m)⁻¹ = c' ^ m * b := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc g ^ (m + 1) * b * (g ^ (m + 1))⁻¹ = g * (g ^ m * b * (g ^ m)⁻¹) * g⁻¹ := by group
        _ = g * c' ^ m * g⁻¹ * (g * b * g⁻¹) := by rw [ih]; group
        _ = c' ^ (m + 1) * b := by
          rw [hgb, show g * c' ^ m * g⁻¹ = c' ^ m by
            rw [← conj_pow, show g * c' * g⁻¹ = c' by rw [hgc']; group], pow_succ, mul_assoc]
  have h1 := hiter (orderOf g)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
  have h3 : 3 ∣ orderOf g := hc'o ▸ orderOf_dvd_of_pow_eq_one h1
  exact absurd (Nat.Coprime.eq_one_of_dvd hg h3) (by norm_num)

theorem centralizer_isPGroup_isCyclic {T : Sylow 3 X} {X₀ : Subgroup X} {x : X}
    (hred : ReducedNongeneration 3 X T X₀) (hxZ : x ∈ center X) (hxo : orderOf x = 3)
    {K : Subgroup X} [K.Normal] (hK : IsComponentOf K ⊤) (hKX₀ : ¬ K ≤ X₀) :
    IsPGroup 3 (centralizer (K : Set X)) ∧ IsCyclic (centralizer (K : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer (K : Set X) with hCdef
  have hCcore : primeComplementCore (G := C) 3 = ⊥ :=
    cfsg_subnormal_primeComplementCore_eq_bot 3 C
      (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)) hred.core_eq_bot
  have hKC : ¬ K ≤ C := by
    intro hKC
    have hctop : center K = ⊤ := eq_top_iff.mpr fun k _ =>
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp (hKC k.2) g g.2)
    haveI := hK.2.2.2
    obtain ⟨q, hq⟩ := exists_ne (1 : K ⧸ center K)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq ((QuotientGroup.eq_one_iff k).mpr (hctop ▸ mem_top k))
  have hClayer : CFSG.layer C = ⊥ := by
    rw [CFSG.layer.eq_sSup, sSup_eq_bot]
    intro L hL
    exfalso
    have hL' := (CFSG.isComponent_iff_open _).mp
      (CFSG.GH74.GLS.Stage1.Main.isComponent_map_subtype_of_normal inferInstance hL)
    have := hred.eq_of_isComponentOf_of_center hxZ hxo hL' hK
    exact hKC (this ▸ map_subtype_le L)
  have hchar : IsCharacteristicP 3 C :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot C 3 hCcore hClayer
  set Q := (CFSG.pCore 3 C).map C.subtype with hQ
  have hQcyc : IsCyclic Q :=
    hred.isCyclic_of_le_centralizer hK hKX₀ (CFSG.pCore_isPGroup.map _) (map_subtype_le _)
  have hxC : x ∈ C := center_le_centralizer _ hxZ
  have hxQ : x ∈ Q := by
    refine ⟨⟨x, hxC⟩, mem_pCore_of_mem_center ?_ (by rw [Subgroup.orderOf_mk, hxo]), rfl⟩
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hxZ g)
  have hp : IsPGroup 3 C := by
    refine IsPGroup.of_card (n := (Nat.card C).primeFactorsList.length) ?_
    refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => ?_
    haveI : Fact q.Prime := ⟨hq⟩
    by_contra hq3
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqd
    have hcop : Nat.Coprime 3 (orderOf (g : X)) := by
      rw [Subgroup.orderOf_coe, hg]
      exact (Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm hq3)
    have hgN : (g : X) ∈ normalizer (Q : Set X) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨g * w * g⁻¹, (CFSG.pCore_normal (p := 3) (G := C)).conj_mem w hw g, rfl⟩
      · rintro ⟨w, hw, hwy⟩
        refine ⟨g⁻¹ * w * g, ?_, ?_⟩
        · have := (CFSG.pCore_normal (p := 3) (G := C)).conj_mem w hw g⁻¹
          simpa using this
        · simp only [coe_subtype, coe_mul, coe_inv] at hwy ⊢
          rw [hwy]
          group
    have hgx : (g : X) * x = x * g := (mem_center_iff.mp hxZ g)
    have hgc := mem_centralizer_of_isCyclic hQcyc (CFSG.pCore_isPGroup.map _) hxQ hxo hgN hgx hcop
    have hgP : g ∈ CFSG.pCore 3 C := hchar (by
      rw [mem_centralizer_iff]
      intro w hw
      exact Subtype.ext (mem_centralizer_iff.mp hgc _ ⟨w, hw, rfl⟩))
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 3) (G := C) ⟨g, hgP⟩
    have hdvd : q ∣ 3 ^ m := hg ▸ orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow hdvd))
  exact ⟨hp, hred.isCyclic_of_le_centralizer hK hKX₀ hp le_rfl⟩

theorem conjNormal_apply_coe {K : Subgroup X} [K.Normal] (y : X) (k : K) :
    ((MulAut.conjNormal y k : K) : X) = y * k * y⁻¹ :=
  MulAut.conjNormal_apply y k

theorem mul_inv_mem_centralizer {K : Subgroup X} [K.Normal] {y : X} {t : K}
    (h : (MulAut.conjNormal y : MulAut K) = MulAut.conj t) :
    y * (t : X)⁻¹ ∈ centralizer (K : Set X) := by
  have hconj : ∀ k ∈ K, y * k * y⁻¹ = t * k * (t : X)⁻¹ := fun k hk => by
    have := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : X)) h
    simpa [conjNormal_apply_coe, MulAut.conj_apply] using this
  rw [mem_centralizer_iff]
  intro k hk
  have hk' : (t : X)⁻¹ * k * t ∈ K := mul_mem (mul_mem (inv_mem t.2) hk) t.2
  have h1 := hconj _ hk'
  rw [show (t : X) * ((t : X)⁻¹ * k * t) * (t : X)⁻¹ = k by group] at h1
  calc k * (y * (t : X)⁻¹) = y * ((t : X)⁻¹ * k * t) * y⁻¹ * (y * (t : X)⁻¹) := by rw [h1]
    _ = y * (t : X)⁻¹ * k := by group

theorem exists_sq {K B : Subgroup X} [K.Normal] (hBK : B ≤ K)
    (hsq : ∀ f : MulAut K, (∀ b : K, (b : X) ∈ B → f b = b) →
      ∃ t : K, (t : X) ∈ B ∧ f ^ 2 = MulAut.conj t)
    {y : X} (hy : y ∈ centralizer (B : Set X)) :
    ∃ t : K, (t : X) ∈ B ∧ (t : X) ∈ centralizer (B : Set X) ∧
      (MulAut.conjNormal (y ^ 2) : MulAut K) = MulAut.conj t := by
  obtain ⟨t, htB, ht⟩ := hsq (MulAut.conjNormal y) fun b hb => Subtype.ext (by
    rw [conjNormal_apply_coe, (mem_centralizer_iff.mp hy b hb).symm]
    simp)
  have ht' : (MulAut.conjNormal (y ^ 2) : MulAut K) = MulAut.conj t := by rw [map_pow, ht]
  refine ⟨t, htB, ?_, ht'⟩
  rw [mem_centralizer_iff]
  intro b hb
  have h1 := congrArg (fun f : MulAut K => ((f ⟨b, hBK hb⟩ : K) : X)) ht'
  simp only [conjNormal_apply_coe, MulAut.conj_apply, coe_mul, coe_inv] at h1
  have hyb : y ^ 2 * b * (y ^ 2)⁻¹ = b := by
    rw [(Commute.pow_left (mem_centralizer_iff.mp hy b hb).symm 2).eq]
    group
  rw [hyb] at h1
  calc b * t = (t * b * (t : X)⁻¹) * t := by rw [← h1]
    _ = t * b := by group

theorem centralizer_facts {K B : Subgroup X} [K.Normal] (hBK : B ≤ K) (hBp : IsPGroup 3 B)
    {x : X} (hxZ : x ∈ center X) (hxo : orderOf x = 3)
    (hC : IsPGroup 3 (centralizer (K : Set X)) ∧ IsCyclic (centralizer (K : Set X)))
    (hsq : ∀ f : MulAut K, (∀ b : K, (b : X) ∈ B → f b = b) →
      ∃ t : K, (t : X) ∈ B ∧ f ^ 2 = MulAut.conj t) :
    (∃ Q : Subgroup X, Q ≤ centralizer (B : Set X) ∧
        centralizer (B : Set X) ≤ normalizer (Q : Set X) ∧ Nat.Coprime 3 (Nat.card Q) ∧
        ∀ g ∈ centralizer (B : Set X), ∃ n : ℕ, g ^ 3 ^ n ∈ Q) ∧
      (∀ y ∈ centralizer (B : Set X), IsPGroup 3 (zpowers y) →
        ∃ k ∈ K ⊓ centralizer (B : Set X), y * k⁻¹ ∈ centralizer (K : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CB := centralizer (B : Set X)
  set CK := centralizer (K : Set X)
  have hxCK : x ∈ CK := center_le_centralizer _ hxZ
  have hdec : ∀ g ∈ CB, ∃ c ∈ CK, ∃ t ∈ B, t ∈ CB ∧ g ^ 2 = c * t := by
    intro g hg
    obtain ⟨t, htB, htC, ht⟩ := exists_sq hBK hsq hg
    exact ⟨g ^ 2 * (t : X)⁻¹, mul_inv_mem_centralizer ht, t, htB, htC, by group⟩
  have h3 : ∀ c ∈ CK, ∀ t ∈ B, ∃ n : ℕ, (c * t) ^ 3 ^ n = 1 := by
    intro c hc t ht
    obtain ⟨a, ha⟩ := hC.1 ⟨c, hc⟩
    obtain ⟨b, hb⟩ := hBp ⟨t, ht⟩
    have hct : Commute c t := (mem_centralizer_iff.mp hc t (hBK ht)).symm
    refine ⟨a + b, ?_⟩
    rw [hct.mul_pow, pow_add]
    have ha' : c ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hb' : t ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
    rw [pow_mul, ha', one_pow, one_mul, mul_comm (3 ^ a), pow_mul, hb', one_pow]
  have hinvCK : ∀ s : X, s ^ 2 = 1 → ∀ c ∈ CK, s * c = c * s := by
    intro s hs2 c hc
    have hsN : s ∈ normalizer (CK : Set X) := by
      rw [mem_normalizer_iff]
      intro w
      exact ⟨fun hw => (inferInstance : CK.Normal).conj_mem w hw s, fun hw => by
        have := (inferInstance : CK.Normal).conj_mem _ hw s⁻¹
        simpa [mul_assoc] using this⟩
    have hcop : Nat.Coprime 3 (orderOf s) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hs2) (by norm_num)
    have hsc := mem_centralizer_of_isCyclic hC.2 hC.1 hxCK hxo hsN
      (mem_center_iff.mp hxZ s) hcop
    exact (mem_centralizer_iff.mp hsc c hc).symm
  have h23 : ∀ g : X, g ^ 2 = 1 → ∀ n : ℕ, g ^ 3 ^ n = 1 → g = 1 := by
    intro g h2 n h3
    have h : orderOf g ∣ Nat.gcd 2 (3 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [(Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h
    exact h
  have hmul : ∀ s s' : X, s ∈ CB → s ^ 2 = 1 → s' ∈ CB → s' ^ 2 = 1 → (s * s') ^ 2 = 1 := by
    intro s s' hs hs2 hs' hs'2
    obtain ⟨c, hc, t, htB, -, hu⟩ := hdec _ (mul_mem hs hs')
    have hsi : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hs2]
    have hs'i : s'⁻¹ = s' := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hs'2]
    have hinv : s * (s * s') ^ 2 * s⁻¹ = ((s * s') ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv_rev, hsi, hs'i]
      calc s * (s * s' * (s * s')) * s = (s * s) * s' * s * (s' * s) := by group
        _ = s' * s * (s' * s) := by rw [← pow_two, hs2, one_mul]
    have hfix : s * (s * s') ^ 2 * s⁻¹ = (s * s') ^ 2 := by
      rw [hu, show s * (c * t) * s⁻¹ = (s * c) * (t * s⁻¹) by group, hinvCK s hs2 c hc,
        show t * s⁻¹ = s⁻¹ * t by
          rw [hsi]; exact (mem_centralizer_iff.mp hs t htB)]
      group
    rw [hfix] at hinv
    have h4 : ((s * s') ^ 2) ^ 2 = 1 := by
      rw [pow_two ((s * s') ^ 2)]
      nth_rewrite 1 [hinv]
      exact inv_mul_cancel _
    obtain ⟨n, hn⟩ := h3 c hc t htB
    exact h23 _ h4 n (hu ▸ hn)
  let Q : Subgroup X :=
    { carrier := {g | g ∈ CB ∧ g ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, hmul a b ha.1 ha.2 hb.1 hb.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmemQ : ∀ g, g ∈ Q ↔ g ∈ CB ∧ g ^ 2 = 1 := fun g => Iff.rfl
  refine ⟨⟨Q, fun g hg => ((hmemQ g).mp hg).1, ?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    rw [mem_normalizer_iff]
    intro w
    rw [hmemQ, hmemQ]
    constructor
    · rintro ⟨hw, hw2⟩
      refine ⟨mul_mem (mul_mem hg hw) (inv_mem hg), ?_⟩
      rw [conj_pow, hw2]
      group
    · rintro ⟨hw, hw2⟩
      refine ⟨?_, ?_⟩
      · have := mul_mem (mul_mem (inv_mem hg) hw) hg
        simpa [mul_assoc] using this
      · rw [conj_pow] at hw2
        have := congrArg (fun z => g⁻¹ * z * g) hw2
        simpa [mul_assoc] using this
  · have hQp : IsPGroup 2 Q := fun g => ⟨1, Subtype.ext (by simpa using ((hmemQ g).mp g.2).2)⟩
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  · intro g hg
    obtain ⟨c, hc, t, htB, -, hgt⟩ := hdec g hg
    obtain ⟨n, hn⟩ := h3 c hc t htB
    refine ⟨n, (hmemQ _).mpr ⟨pow_mem hg _, ?_⟩⟩
    rw [← pow_mul, mul_comm, pow_mul, hgt, hn]
  · intro y hy hyp
    obtain ⟨n, hn⟩ := hyp ⟨y, mem_zpowers y⟩
    have hyn : y ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨t, -, htC, ht⟩ := exists_sq hBK hsq hy
    obtain ⟨m, hm⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ n)).add_one
    have hyeq : y = (y ^ 2) ^ m := by
      rw [← pow_mul, show 2 * m = 3 ^ n + 1 by omega, pow_succ, hyn, one_mul]
    have hconj : (MulAut.conjNormal y : MulAut K) = MulAut.conj (t ^ m) := by
      rw [hyeq, map_pow, ht, map_pow]
    refine ⟨((t ^ m : K) : X), Subgroup.mem_inf.mpr ⟨(t ^ m).2, ?_⟩,
      mul_inv_mem_centralizer hconj⟩
    rw [Subgroup.coe_pow]
    exact pow_mem htC m

end InnerQ.KFC1

end CFSG.LocalAnalysis.RankThreeTheoremC
