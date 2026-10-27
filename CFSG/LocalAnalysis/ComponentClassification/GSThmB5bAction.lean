module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bConj
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

section Action

variable {G : Type*} [Group G]

@[expose] noncomputable def oddBarMulAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ pPrimeCore 2 Y) where
  toFun φ := QuotientGroup.congr (pPrimeCore 2 Y) (pPrimeCore 2 Y) φ (pPrimeCore_map_iso 2 φ)
  map_one' := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  map_mul' φ ψ := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl

@[expose] noncomputable def oddBarConj (L : Subgroup G) :
    ↥(normalizer (L : Set G)) →* MulAut (L ⧸ pPrimeCore 2 L) :=
  (oddBarMulAut L).comp L.normalizerMonoidHom

theorem oddBarConj_apply_mk (L : Subgroup G) (g : ↥(normalizer (L : Set G))) (l : L) :
    oddBarConj L g (l : L ⧸ pPrimeCore 2 L) =
      ((⟨(g : G) * l * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 l).mp l.2⟩ : L) :
        L ⧸ pPrimeCore 2 L) := rfl

theorem mem_coreActionKernel_of_oddBarConj_eq_one {L : Subgroup G}
    {g : ↥(normalizer (L : Set G))} (hg : oddBarConj L g = 1) : (g : G) ∈ coreActionKernel L := by
  have hON : (g : G) ∈ normalizer ((pPrimeCore 2 L).map L.subtype : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L) g.2
  rw [mem_coreActionKernel]
  refine ⟨g.2, fun j hj => ?_⟩
  have h1 := congrArg (fun φ : MulAut (L ⧸ pPrimeCore 2 L) =>
    φ ((⟨j, hj⟩ : L) : L ⧸ pPrimeCore 2 L)) hg
  simp only [oddBarConj_apply_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have h2 := mem_map_of_mem L.subtype h1
  simp only [map_mul, map_inv, subtype_apply] at h2
  have h3 := (mem_normalizer_iff.mp (inv_mem hON) _).mp h2
  convert h3 using 1
  group

variable [Finite G]

theorem exists_fixed_lift {L : Subgroup G} {t : ↥(normalizer (L : Set G))}
    (ht : (t : G) * t = 1) {y : L}
    (hy : oddBarConj L t (y : L ⧸ pPrimeCore 2 L) = y) :
    ∃ y' : L, (y' : L ⧸ pPrimeCore 2 L) = y ∧ (t : G) * y' = y' * t := by
  have hON : (t : G) ∈ normalizer ((pPrimeCore 2 L).map L.subtype : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L) t.2
  rw [oddBarConj_apply_mk, QuotientGroup.eq] at hy
  have ho := mem_map_of_mem L.subtype hy
  simp only [map_mul, map_inv, subtype_apply] at ho
  set o : G := ((t : G) * y * (t : G)⁻¹)⁻¹ * y with hodef
  set t' : G := (y : G)⁻¹ * t * y with ht'
  have ht'eq : t' = o⁻¹ * t := by rw [ht', hodef]; group
  have htt' : (t : G)⁻¹ * t' ∈ (pPrimeCore 2 L).map L.subtype := by
    rw [ht'eq]
    have := (mem_normalizer_iff.mp (inv_mem hON) _).mp (inv_mem ho)
    convert this using 1
    rw [hodef]
    group
  have ht'2 : t' * t' = 1 := by
    rw [ht']
    calc (y : G)⁻¹ * t * y * ((y : G)⁻¹ * t * y) = (y : G)⁻¹ * ((t : G) * t) * y := by group
      _ = 1 := by rw [ht]; group
  have hodd : Odd (orderOf ((t : G)⁻¹ * t')) := by
    obtain ⟨w, hw, hwe⟩ := mem_map.mp htt'
    rw [← hwe, subtype_apply, Subgroup.orderOf_coe]
    have hdvd : orderOf (⟨w, hw⟩ : pPrimeCore 2 L) ∣ Nat.card (pPrimeCore 2 L) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    have h2 := Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2))
    rwa [Nat.coprime_two_left] at h2
  obtain ⟨w, hw, hwt⟩ := exists_conj_of_inv_mul ht ht'2 hodd
  have hwO : w ∈ (pPrimeCore 2 L).map L.subtype := (zpowers_le.mpr htt') hw
  obtain ⟨w₀, hw₀, hw₀e⟩ := mem_map.mp hwO
  refine ⟨y * w₀⁻¹, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff w₀).mpr hw₀,
      inv_one, mul_one]
  · have hw' : (w₀ : G) = w := hw₀e
    simp only [coe_mul, coe_inv, hw']
    calc (t : G) * ((y : G) * w⁻¹) = (y : G) * (((y : G)⁻¹ * t * y) * w⁻¹) := by group
      _ = (y : G) * ((w⁻¹ * t * w) * w⁻¹) := by rw [hwt]
      _ = (y : G) * w⁻¹ * t := by group

theorem exists_elementary_lift {L : Subgroup G} {t : ↥(normalizer (L : Set G))}
    (ht : (t : G) * t = 1) {E : Subgroup (L ⧸ pPrimeCore 2 L)} (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hEfix : ∀ e ∈ E, oddBarConj L t e = e) :
    ∃ E₁ : Subgroup G, E₁ ≤ L ∧ E₁ ≤ centralizer ({(t : G)} : Set G) ∧
      (∀ e ∈ E₁, e ^ 2 = 1) ∧ Nat.card E₁ = Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 L) with hπ
  set M : Subgroup L := E.comap π ⊓ (centralizer ({(t : G)} : Set G)).comap L.subtype with hM
  set f : M →* L ⧸ pPrimeCore 2 L := π.comp M.subtype with hf
  have hrange : f.range = E := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact (mem_inf.mp m.2).1
    · intro e he
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective e
      obtain ⟨y', hy', hyt⟩ := exists_fixed_lift ht (hEfix _ he)
      have hy'M : y' ∈ M := by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · show π y' ∈ E
          rw [hπ, QuotientGroup.mk'_apply, hy']
          exact he
        · show (y' : G) ∈ centralizer ({(t : G)} : Set G)
          rw [mem_centralizer_singleton_iff]
          exact hyt.symm
      refine ⟨⟨y', hy'M⟩, ?_⟩
      show π y' = _
      rw [hπ, QuotientGroup.mk'_apply, hy']
  have hkerO : ∀ k : M, k ∈ f.ker → (k : L) ∈ pPrimeCore 2 L := by
    intro k hk
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, subtype_apply, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact hk
  have hkerodd : Nat.Coprime 2 (Nat.card f.ker) := by
    set g₀ : f.ker →* L := M.subtype.comp f.ker.subtype with hg₀
    have hg₀inj : Function.Injective g₀ :=
      M.subtype_injective.comp f.ker.subtype_injective
    have hle : g₀.range ≤ pPrimeCore 2 L := by
      rintro _ ⟨k, rfl⟩
      exact hkerO k k.2
    have h1 : Nat.card f.ker = Nat.card g₀.range :=
      Nat.card_congr (MonoidHom.ofInjective hg₀inj).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (CFSG.pPrimeCore_coprime_card (p := 2))
  have hE2grp : IsPGroup 2 E := fun e => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hE2 _ e.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2grp
  have hcardM : Nat.card M = Nat.card E * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange]
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 M))
  have hRcard : Nat.card R = Nat.card E := by
    rw [Sylow.card_eq_multiplicity, hcardM, hk]
    have hk0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
    have hodd : ¬ 2 ∣ Nat.card f.ker := fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_right h2 hkerodd) (by norm_num)
    rw [Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  have hRker : ∀ r : M, r ∈ (R : Subgroup M) → r ∈ f.ker → r = 1 := by
    intro r hr hrk
    have h1 : (R : Subgroup M) ⊓ f.ker = ⊥ := by
      apply eq_bot_of_isPGroup_two_of_coprime (R.isPGroup'.to_le inf_le_left)
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hkerodd
    have : r ∈ (R : Subgroup M) ⊓ f.ker := mem_inf.mpr ⟨hr, hrk⟩
    rw [h1] at this
    exact mem_bot.mp this
  refine ⟨((R : Subgroup M).map M.subtype).map L.subtype, ?_, ?_, ?_, ?_⟩
  · exact map_subtype_le _
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact (mem_inf.mp r.2).2
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have hr2 : r ^ 2 = 1 := by
      apply hRker _ (pow_mem hr 2)
      rw [MonoidHom.mem_ker, map_pow]
      have hfr : f r ∈ E := hrange ▸ ⟨r, rfl⟩
      exact hE2 _ hfr
    simp only [subtype_apply]
    rw [← SubgroupClass.coe_pow, ← SubgroupClass.coe_pow, hr2]
    rfl
  · rw [← hRcard, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective M.subtype_injective]

end Action

end CFSG.ComponentClassification.GSThmB
