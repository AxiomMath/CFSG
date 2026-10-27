module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514V
public import CFSG.HardMathSupport.Solomon.Coordinator.L514T

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

@[expose] def Y0Level : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → ∀ r : ℕ, IsL3Eps r Y → r ≠ 8 →
    ∀ α : MulAut Y, α ^ 3 = 1 → α ≠ 1 → IsFieldAutThree α →
      ∃ y : Y, y ^ 3 = 1 ∧ y ≠ 1 ∧ α y = y ∧ ∃ r0 : ℕ, r = r0 ^ 3 ∧ ∃ L : Subgroup Y,
        (∀ J : Subgroup Y, GLAPComponent 3 (fixedSub α ⊓ Cen y) J ↔ J = L) ∧
          IsTypeL2 r0 (barOf 3 L)

section Pair

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem l514y0_mem_cs_iff_commute {a b : G} : b ∈ Cs a ↔ Commute a b := by
  rw [Subgroup.mem_centralizer_singleton_iff]; exact eq_comm

omit [Finite G] in
theorem l514y0_commute_conj_of_commute {g w m : G} (hw : Commute g w) (hm : Commute g m) :
    Commute g (w * m * w⁻¹) := (hw.mul_right hm).mul_right hw.inv_right

theorem l514y0_barX_inf_cs_cs {K : Subgroup G} {g y : G} (hgN : g ∈ Subgroup.normalizer (K : Set G))
    (hg3 : g ^ 3 = 1) (hyK : y ∈ K) (hy3 : y ^ 3 = 1) (hcomm : g * y = y * g) :
    barX 3 K (K ⊓ Cs g ⊓ Cs y) =
      fixedSub (barAut 3 K ⟨g, hgN⟩) ⊓ Cen (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨y, hyK⟩) := by
  have hF := fixedSub_barAut_eq hg3 hgN
  have hgyC : Commute g y := hcomm
  ext z
  constructor
  · rintro ⟨⟨x, hxK⟩, hx, rfl⟩
    have hx' : x ∈ K ⊓ Cs g ⊓ Cs y := Subgroup.mem_subgroupOf.1 hx
    refine ⟨?_, ?_⟩
    · have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨x, hxK⟩ ∈ barX 3 K (K ⊓ Cen g) :=
        ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 ⟨hxK, hx'.1.2⟩, rfl⟩
      rw [← hF] at this
      exact this
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((l514y0_mem_cs_iff_commute.1 hx'.2).eq.symm)
  · rintro ⟨hz1, hz2⟩
    rw [hF] at hz1
    obtain ⟨⟨x, hxK⟩, hx, rfl⟩ := hz1
    have hx' : x ∈ K ⊓ Cen g := Subgroup.mem_subgroupOf.1 hx
    have hxgC : Commute g x := l514y0_mem_cs_iff_commute.1 hx'.2
    have hfixO : y * x * y⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hz2
      rw [← map_mul, ← map_mul] at h1
      have h1' := QuotientGroup.eq.1 h1
      rw [mem_gLAPPrimeCoreOf_iff]
      refine ⟨K.mul_mem (K.mul_mem (K.mul_mem hyK hxK) (K.inv_mem hyK)) (K.inv_mem hxK), ?_⟩
      have := (GLAPPrimeCore.normal 3 ↥K).conj_mem _ h1' (⟨y, hyK⟩ * ⟨x, hxK⟩)
      convert this using 1
      apply Subtype.ext
      simp [mul_assoc]
    have hfix : y * x * y⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 K ⊓ Cs g :=
      ⟨hfixO, l514y0_mem_cs_iff_commute.2 (((hgyC.mul_right hxgC).mul_right hgyC.inv_right).mul_right
        hxgC.inv_right)⟩
    have hM : GLAPPrimeCoreOf 3 K ⊓ Cs g ≤ GLAPPrimeCoreOf 3 K := inf_le_left
    have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 K ⊓ Cs g)) :=
      (card_gLAPPrimeCoreOf_coprime 3 K).coprime_dvd_right (Subgroup.card_dvd_of_le hM)
    have hnorm : ∀ w ∈ K, Commute g w →
        w ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K ⊓ Cs g : Subgroup G) : Set G) := by
      intro w hwK hwg
      rw [Subgroup.mem_normalizer_iff]
      intro m
      constructor
      · rintro ⟨hm1, hm2⟩
        exact ⟨conj_mem_gLAPPrimeCoreOf 3 K hwK hm1,
          l514y0_mem_cs_iff_commute.2 (l514y0_commute_conj_of_commute hwg (l514y0_mem_cs_iff_commute.1 hm2))⟩
      · rintro ⟨hm1, hm2⟩
        refine ⟨?_, ?_⟩
        · have := conj_mem_gLAPPrimeCoreOf 3 K (K.inv_mem hwK) hm1
          simpa [mul_assoc] using this
        · have := l514y0_commute_conj_of_commute hwg.inv_right (l514y0_mem_cs_iff_commute.1 hm2)
          exact l514y0_mem_cs_iff_commute.2 (by simpa [mul_assoc] using this)
    obtain ⟨m, hm, hcm⟩ := exists_commute_mul hy3 (hnorm y hyK hgyC) hcop (hnorm x hxK hxgC) hfix
    have hmK : m ∈ K := gLAPPrimeCoreOf_le 3 K hm.1
    have hmgC : Commute g m := l514y0_mem_cs_iff_commute.1 hm.2
    refine ⟨⟨x * m, K.mul_mem hxK hmK⟩, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ⟨⟨K.mul_mem hxK hmK, l514y0_mem_cs_iff_commute.2 (hxgC.mul_right hmgC)⟩,
        l514y0_mem_cs_iff_commute.2 ?_⟩
      exact (show y * (x * m) = x * m * y from hcm)
    · have hm' : (⟨m, hmK⟩ : ↥K) ∈ GLAPPrimeCore 3 ↥K := ((mem_gLAPPrimeCoreOf_iff 3 K m).1 hm.1).2
      have h2 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) ⟨m, hmK⟩ = 1 :=
        (QuotientGroup.eq_one_iff _).2 hm'
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (⟨x, hxK⟩ * ⟨m, hmK⟩) = _
      rw [map_mul, h2, mul_one]

end Pair

section Assembly

theorem l514y0_isTypeL2_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {r : ℕ}
    (h : IsTypeL2 r A) : IsTypeL2 r B :=
  p6_isTypeL2_of_equiv e h

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem l514y0_barAut_of_mem {K : Subgroup G} {y : G} (hy : y ∈ K) :
    barAut 3 K ⟨y, Subgroup.le_normalizer hy⟩ =
      MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨y, hy⟩) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) z
  refine (barAut_mk 3 K _ x).trans ?_
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem l514y0_exists_lift_pow_three {K : Subgroup G} {k : G} (hk : k ∈ K)
    (hk3 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, hk⟩) ^ 3 = 1) :
    ∃ n : ℕ, (k ^ n) ^ 3 = 1 ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k ^ n, pow_mem hk n⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, hk⟩ := by
  have hO : k ^ 3 ∈ GLAPPrimeCoreOf 3 K := by
    rw [mem_gLAPPrimeCoreOf_iff]
    refine ⟨pow_mem hk 3, ?_⟩
    rw [← map_pow] at hk3
    exact (QuotientGroup.eq_one_iff _).1 hk3
  have hcop : Nat.Coprime (orderOf (k ^ 3)) 3 := by
    have h1 : orderOf (k ^ 3) ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
      have := orderOf_dvd_natCard (⟨k ^ 3, hO⟩ : ↥(GLAPPrimeCoreOf 3 K))
      rwa [← Subgroup.orderOf_coe] at this
    exact ((card_gLAPPrimeCoreOf_coprime 3 K).symm).coprime_dvd_left h1
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 3)
  refine ⟨orderOf (k ^ 3) * u, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_mul, pow_orderOf_eq_one, one_pow]
  · have h3 : orderOf (k ^ 3) * u = 3 * (orderOf (k ^ 3) * u / 3) + 1 := by
      have := Nat.div_add_mod (orderOf (k ^ 3) * u) 3
      rw [hu] at this
      omega
    have e : (⟨k ^ (orderOf (k ^ 3) * u), pow_mem hk _⟩ : ↥K) =
        ⟨k, hk⟩ ^ (orderOf (k ^ 3) * u) := rfl
    rw [e, map_pow, h3, pow_succ, pow_mul, hk3, one_pow, one_mul]

theorem inputL3y0_of_ylevel (h : Y0Level) : InputL3y0 innAutDerivedVocab := by
  intro G _ _ K g r hq hE hr8 hg3 hfld hnt
  obtain ⟨hgN, hfa⟩ := hfld
  set α := barAut 3 K ⟨g, hgN⟩ with hα
  have hα3 : α ^ 3 = 1 := Lemma510Ns.barAut_pow_three hgN hg3
  have hα1 : α ≠ 1 := fun h1 => hnt ⟨hgN, h1⟩
  obtain ⟨y, hy3, hy1, hαy, r0, hr, L, hL, hLtype⟩ := h _ hq r hE hr8 α hα3 hα1 hfa
  have hF := fixedSub_barAut_eq hg3 hgN
  have hyF : y ∈ barX 3 K (K ⊓ Cen g) := by rw [← hF]; exact hαy
  obtain ⟨⟨k, hkK⟩, hk, hky⟩ := hyF
  have hk' : k ∈ K ⊓ Cen g := Subgroup.mem_subgroupOf.1 hk
  have hkc : Commute g k := l514y0_mem_cs_iff_commute.1 hk'.2
  have hk3 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, hkK⟩) ^ 3 = 1 := by rw [hky]; exact hy3
  obtain ⟨n, hn3, hnmk⟩ := l514y0_exists_lift_pow_three hkK hk3
  set y₀ := k ^ n with hy₀
  have hy₀K : y₀ ∈ K := pow_mem hkK n
  have hy₀g : y₀ ∈ Cs g := l514y0_mem_cs_iff_commute.2 (hkc.pow_right n)
  have hy₀y : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨y₀, hy₀K⟩ = y := hnmk.trans hky
  have hcomm : g * y₀ = y₀ * g := (l514y0_mem_cs_iff_commute.1 hy₀g).eq
  have hcen : Subgroup.center (barOf 3 K) = ⊥ := by
    rcases l3_std hq (by rcases hE with ⟨-, h⟩ | ⟨-, h⟩ <;> [exact Or.inl h; exact Or.inr h]) with
      ⟨F, _, _, e, hZ⟩ | ⟨p, f, F, _, hF, hq, e, hZ⟩ <;> exact hZ
  refine ⟨y₀, ⟨hy₀K, hy₀g⟩, hn3, ⟨Subgroup.le_normalizer hy₀K, ?_⟩, ?_, ?_⟩
  · rw [l514y0_barAut_of_mem hy₀K]
    exact le_sup_left (a := innerAut (barOf 3 K)) ⟨_, rfl⟩
  · rintro ⟨hN, hb⟩
    rw [l514y0_barAut_of_mem hy₀K] at hb
    apply hy1
    rw [← hy₀y]
    have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨y₀, hy₀K⟩ ∈ Subgroup.center (barOf 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun a : MulAut (barOf 3 K) => a z) hb
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen, Subgroup.mem_bot] at this
    exact this
  · set X : Subgroup G := K ⊓ Cs g ⊓ Cs y₀ with hX
    have hXK : X ≤ K := inf_le_left.trans inf_le_left
    have hpair := l514y0_barX_inf_cs_cs hgN hg3 hy₀K hn3 hcomm
    rw [hy₀y] at hpair
    have hS : GLAPComponent 3 (barX 3 K X) L := by
      rw [hpair]; exact (hL L).2 rfl
    have hu : ∀ S' : Subgroup (barOf 3 K), GLAPComponent 3 (barX 3 K X) S' → S' = L := by
      intro S' hS'
      rw [hpair] at hS'
      exact (hL S').1 hS'
    obtain ⟨J₀, hJ₀, hJu, ⟨eJ⟩⟩ := l514t_comp_unique_transfer hXK hS hu
    have hlay : GLAPLayer 3 X = J₀ :=
      le_antisymm (sSup_le fun J hJ => (hJu J hJ).le) (le_sSup hJ₀)
    refine ⟨r0, hr, ?_, ?_⟩
    · rw [hlay]; exact hJ₀
    · have key : ∀ M : Subgroup G, M = J₀ → IsTypeL2 r0 (barOf 3 M) := by
        rintro M rfl
        exact l514y0_isTypeL2_of_mulEquiv eJ.symm hLtype
      exact key _ hlay

end Assembly


end CFSG.HardMathSupport.Solomon.Coordinator
