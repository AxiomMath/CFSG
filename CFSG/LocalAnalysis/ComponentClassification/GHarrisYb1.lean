module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL36c

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem exists_oddPart_pow {N Q : Type*} [Group N] [Finite N] [Group Q] {c : N}
    (hc : ∀ n : N, n * c = c * n) {k : ℕ} (hck : orderOf c = 2 ^ k) (f : N →* Q)
    (hf : Function.Surjective f) (hker : f.ker = zpowers c) (hQ : Odd (Nat.card Q)) :
    ∃ K : Subgroup N, (∀ n : N, n ∈ K ↔ Odd (orderOf n)) ∧
      ∀ n : N, ∃ s ∈ zpowers c, ∃ m ∈ K, n = s * m := by
  have hZn : (zpowers c).Normal := by
    rw [← hker]
    infer_instance
  have hcard : Nat.card (zpowers c) = 2 ^ k := by rw [Nat.card_zpowers, hck]
  have hidx : (zpowers c).index = Nat.card Q := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, card_top]
  have hcop : Nat.Coprime (Nat.card (zpowers c)) (zpowers c).index := by
    rw [hcard, hidx]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hQ)
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = Nat.card Q := by
    have h := hK.card_mul_card
    have h2 := (zpowers c).index_mul_card
    rw [hcard] at h h2
    rw [hidx] at h2
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    nlinarith
  have hdecomp : ∀ n : N, ∃ s ∈ zpowers c, ∃ m ∈ K, s * m = n := by
    intro n
    obtain ⟨⟨s, m⟩, hsm, -⟩ := (isComplement'_def.mp hK).existsUnique n
    exact ⟨s, s.2, m, m.2, hsm⟩
  have hodd : ∀ m ∈ K, Odd (orderOf m) := by
    intro m hm
    have hdvd : orderOf m ∣ Nat.card K := by
      rw [← Subgroup.orderOf_mk m hm]
      exact orderOf_dvd_natCard _
    rw [hKcard] at hdvd
    exact hQ.of_dvd_nat hdvd
  have hs2 : ∀ s ∈ zpowers c, orderOf s ∣ 2 ^ k := by
    intro s hs
    rw [← hck]
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs
    exact orderOf_dvd_of_pow_eq_one (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow])
  refine ⟨K, fun n => ⟨fun hn => hodd n hn, fun hn => ?_⟩, fun n => ?_⟩
  · obtain ⟨s, hs, m, hm, rfl⟩ := hdecomp n
    have hcomm : Commute s m := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs
      exact (Commute.zpow_left (show Commute c m from (hc m).symm) i)
    have hcop' : Nat.Coprime (orderOf s) (orderOf m) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hs2 s hs)
      rw [hj]
      exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr (hodd m hm))
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop'] at hn
    have hs1 : orderOf s = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hs2 s hs)
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [hj] at hn
        exact (Nat.not_odd_iff_even.mpr ((Nat.even_pow.mpr ⟨even_two, j.succ_ne_zero⟩).mul_right
          _)) hn
    rw [orderOf_eq_one_iff.mp hs1, one_mul]
    exact hm
  · obtain ⟨s, hs, m, hm, rfl⟩ := hdecomp n
    exact ⟨s, hs, m, hm, rfl⟩

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

omit [Finite Y] in
theorem M_eq_top (hz : ∀ y : Y, y * D.z = D.z * y) : D.M = ⊤ :=
  eq_top_iff.mpr fun y _ => mem_centralizer_singleton_iff.mpr (hz y)

theorem OM_eq_bot (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) : D.OM = ⊥ := by
  have hn : D.OM.Normal := ⟨fun o ho g => D.conj_mem_OM (by rw [D.M_eq_top hz]; exact mem_top g) ho⟩
  have := (pPrimeCore_eq_bot_iff.mp hO) D.OM hn (Nat.coprime_two_left.mpr D.odd_card_OM)
  exact this

theorem M1_eq (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.M1 = centralizer ({D.l} : Set Y) := by
  ext g
  rw [D.mem_M1, D.OM_eq_bot hO hz, mem_bot, D.M_eq_top hz, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    calc g * D.l = g * D.l * g⁻¹ * D.l⁻¹ * (D.l * g) := by group
      _ = D.l * g := by rw [h, one_mul]
  · intro h
    refine ⟨mem_top g, ?_⟩
    rw [h, mul_inv_cancel_right, mul_inv_cancel]

theorem index_centralizer_l (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) : (centralizer ({D.l} : Set Y)).index = 2 := by
  have h := D.M1_index
  rw [D.M1_eq hO hz, D.M_eq_top hz] at h
  have h' : (centralizer ({D.l} : Set Y)).relIndex ⊤ = 2 := h
  rwa [Subgroup.relIndex_top_right] at h'

abbrev Y1 : Subgroup Y := centralizer ({D.l} : Set Y)

abbrev lY : D.Y1 := ⟨D.l, mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite Y] in
theorem lY_comm (y : D.Y1) : y * D.lY = D.lY * y :=
  Subtype.ext (mem_centralizer_singleton_iff.mp y.2)

omit [Finite Y] in
instance zpowers_lY_normal : (zpowers D.lY).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
  rw [((Commute.zpow_right (D.lY_comm g) k)).eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers _) k

abbrev Xt : Type := D.Y1 ⧸ zpowers D.lY

abbrev piX : D.Y1 →* D.Xt := QuotientGroup.mk' (zpowers D.lY)

omit [Finite Y] in
theorem orderOf_lY : orderOf D.lY = 2 ^ 2 := by
  rw [Subgroup.orderOf_mk]
  have h4 : D.l ^ 4 = 1 := D.l_pow_four
  obtain ⟨b, hb, hob⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one (show D.l ^ (2 ^ 2) = 1 from h4))
  interval_cases b
  · rw [pow_zero, orderOf_eq_one_iff] at hob
    exact absurd (D.toG_injective (hob.trans (map_one D.toG).symm)) SE.gen1_ne_one
  · rw [pow_one] at hob
    exfalso
    have h2 : D.l ^ 2 = 1 := by rw [← hob, pow_orderOf_eq_one]
    rw [pow_two, D.l_mul_l] at h2
    exact D.z_ne_one h2
  · exact hob

theorem pPrimeCore_Xt (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) : pPrimeCore 2 D.Xt = ⊥ := by
  rw [pPrimeCore_eq_bot_iff]
  intro Nt hNt hcop
  have hY1n : D.Y1.Normal := normal_of_index_eq_two (D.index_centralizer_l hO hz)
  set N' := Nt.comap D.piX with hN'
  have hN'n : N'.Normal := hNt.comap _
  set f := D.piX.subgroupComap Nt with hf
  have hfs : Function.Surjective f :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _)
  have hlN' : D.lY ∈ N' := by
    rw [hN', mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)]
    exact one_mem _
  set lN : N' := ⟨D.lY, hlN'⟩ with hlN
  have hlNc : ∀ n : N', n * lN = lN * n := fun n => Subtype.ext (D.lY_comm n)
  have hlN4 : orderOf lN = 2 ^ 2 := by rw [Subgroup.orderOf_mk]; exact D.orderOf_lY
  have hker : f.ker = zpowers lN := by
    ext n
    rw [MonoidHom.mem_ker]
    have hiff : n ∈ zpowers lN ↔ (n : D.Y1) ∈ zpowers D.lY := by
      rw [mem_zpowers_iff, mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
    rw [hiff, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  obtain ⟨K, hK, hKd⟩ := exists_oddPart_pow hlNc hlN4 f hfs hker (Nat.coprime_two_left.mp hcop)
  set KG : Subgroup Y := (K.map N'.subtype).map D.Y1.subtype with hKG
  have hKodd : Odd (Nat.card K) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp hev)
    have := (hK m).mp m.2
    rw [Subgroup.orderOf_coe, hm] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  have hKG : KG ≤ (pPrimeCore 2 D.Y1).map D.Y1.subtype := by
    refine GrSLit.le_map_pPrimeCore (map_subtype_le _) (fun g hg k hk => ?_) (by
      rw [hKG, card_map_of_injective D.Y1.subtype_injective,
        card_map_of_injective N'.subtype_injective]
      exact hKodd)
    obtain ⟨_, ⟨k₀, hk₀, rfl⟩, rfl⟩ := hk
    have hmem : (⟨g, hg⟩ : D.Y1) * (k₀ : D.Y1) * (⟨g, hg⟩ : D.Y1)⁻¹ ∈ N' :=
      hN'n.conj_mem _ k₀.2 _
    have hodd : Odd (orderOf (⟨_, hmem⟩ : N')) := by
      have hord : orderOf ((⟨g, hg⟩ : D.Y1) * (k₀ : D.Y1) * (⟨g, hg⟩ : D.Y1)⁻¹) =
          orderOf (k₀ : D.Y1) := (MulAut.conj (⟨g, hg⟩ : D.Y1)).orderOf_eq k₀.1
      rw [Subgroup.orderOf_mk, hord, Subgroup.orderOf_coe]
      exact (hK k₀).mp hk₀
    exact ⟨_, ⟨_, (hK _).mpr hodd, rfl⟩, rfl⟩
  have hKbot : KG = ⊥ := by
    have := hKG.trans (GrSLit.map_pPrimeCore_le_of_normal (N := D.Y1))
    rwa [hO, le_bot_iff] at this
  rw [eq_bot_iff]
  intro nt hnt
  obtain ⟨n, hn⟩ := hfs ⟨nt, hnt⟩
  obtain ⟨s, hs, m, hm, hnsm⟩ := hKd n
  have hm1 : m = 1 := by
    have h1 : (((m : N') : D.Y1) : Y) ∈ KG := ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    rw [hKbot, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  rw [hm1, mul_one] at hnsm
  have hfn : f n = 1 := by rw [hnsm, ← MonoidHom.mem_ker, hker]; exact hs
  rw [mem_bot]
  calc nt = ((⟨nt, hnt⟩ : Nt) : D.Xt) := rfl
    _ = ((f n : Nt) : D.Xt) := by rw [hn]
    _ = 1 := by rw [hfn]; rfl

end GHSylow

end CFSG.ComponentClassification.GHarris
