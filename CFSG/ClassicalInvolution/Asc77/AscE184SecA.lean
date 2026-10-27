module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.ClassicalInvolution.Asc77.AscL62Pair
public import CFSG.ClassicalInvolution.Asc77.AscSix66Aux

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE184Sect

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] [Finite G] in
theorem exists_fixed_mem_coset {A N : Subgroup G} (hA : IsPGroup 2 ↥A) (hN : Odd (Nat.card ↥N))
    (hAN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) {x : G}
    (hx : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ a ∈ A, a * (x * n) * a⁻¹ = x * n := by
  classical
  set 𝒞 : Set G := {c | x⁻¹ * c ∈ N} with h𝒞
  have hmem : ∀ a ∈ A, ∀ c ∈ 𝒞, a * c * a⁻¹ ∈ 𝒞 := by
    intro a ha c hc
    show x⁻¹ * (a * c * a⁻¹) ∈ N
    have h1 : x⁻¹ * (a * c * a⁻¹) = (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * c) * a⁻¹) := by group
    rw [h1]
    exact N.mul_mem (hx a ha) (hAN a ha _ hc)
  let inst : MulAction ↥A ↥𝒞 :=
    { smul := fun a c => ⟨(a : G) * c * (a : G)⁻¹, hmem a a.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by
        change (1 : G) * (c : G) * (1 : G)⁻¹ = c
        group)
      mul_smul := fun a b c => Subtype.ext (by
        change ((a * b : ↥A) : G) * (c : G) * ((a * b : ↥A) : G)⁻¹ =
          (a : G) * ((b : G) * (c : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card ↥𝒞 = Nat.card ↥N := by
    refine Nat.card_congr ⟨fun c => ⟨x⁻¹ * c, c.2⟩, fun n => ⟨x * n, ?_⟩, ?_, ?_⟩
    · show x⁻¹ * (x * (n : G)) ∈ N
      simp
    · intro c
      apply Subtype.ext
      simp
    · intro n
      apply Subtype.ext
      simp
  have hodd : ¬ 2 ∣ Nat.card ↥𝒞 := by
    rw [hcard]
    exact fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  obtain ⟨⟨c, hc⟩, hfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (↥𝒞) hodd
  refine ⟨x⁻¹ * c, hc, fun a ha => ?_⟩
  have h1 : (a : G) * c * (a : G)⁻¹ = c := congrArg Subtype.val (hfix ⟨a, ha⟩)
  have h2 : x * (x⁻¹ * c) = c := by group
  rw [h2]
  exact h1

omit [Fact p.Prime] in
theorem le_centralizer_of_normalized {A J T : Subgroup G} (hAJ : ⁅A, J⁆ ≤ oddCoreOf J)
    (hTJ : T ≤ J) (hT2 : IsPGroup 2 ↥T) (hT : ∀ a ∈ A, conjSub a T = T) :
    T ≤ Subgroup.centralizer (A : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : ⁅a, t⁆ ∈ oddCoreOf J := hAJ (Subgroup.commutator_mem_commutator ha (hTJ ht))
  have h2 : ⁅a, t⁆ ∈ T := by
    have e : ⁅a, t⁆ = (a * t * a⁻¹) * t⁻¹ := by rw [commutatorElement_def]
    rw [e]
    have : a * t * a⁻¹ ∈ conjSub a T := conj_mem_conjSub ht
    rw [hT a ha] at this
    exact T.mul_mem this (T.inv_mem ht)
  have h3 : ⁅a, t⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) h1
    (hT2.to_le (Subgroup.zpowers_le.mpr h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

omit [Fact p.Prime] in
theorem exists_isSylow2In_centralizer {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) :
    ∃ T : Subgroup G, IsSylow2In T J ∧ T ≤ Subgroup.centralizer (A : Set G) := by
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_commutator_le_oddCoreOf hAJ
  obtain ⟨T, hT, hTinv⟩ := AscL62.exists_sylow_normalized hA hAN
  exact ⟨T, hT, le_centralizer_of_normalized hAJ hT.1 hT.2.1 hTinv⟩

omit [Fact p.Prime] in
theorem exists_mul_of_mem {A J : Subgroup G} (hA : IsPGroup 2 ↥A) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J)
    {x : G} (hx : x ∈ J) :
    ∃ c ∈ J ⊓ Subgroup.centralizer (A : Set G), ∃ n ∈ oddCoreOf J, x = c * n := by
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_commutator_le_oddCoreOf hAJ
  have hN : ∀ a ∈ A, ∀ n ∈ oddCoreOf J, a * n * a⁻¹ ∈ oddCoreOf J := fun a ha n hn =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hAN ha) hn
  have hx' : ∀ a ∈ A, x⁻¹ * (a * x * a⁻¹) ∈ oddCoreOf J := by
    intro a ha
    have h1 : ⁅a, x⁻¹⁆ ∈ oddCoreOf J :=
      hAJ (Subgroup.commutator_mem_commutator ha (J.inv_mem hx))
    have h2 : x⁻¹ * (a * x * a⁻¹) = ⁅a, x⁻¹⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact (oddCoreOf J).inv_mem h1
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset hA (oddCoreOf_odd_natCard J) hN hx'
  have hc : x * n ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hfix a ha
    calc a * (x * n) = (a * (x * n) * a⁻¹) * a := by group
      _ = (x * n) * a := by rw [this]
  exact ⟨x * n, Subgroup.mem_inf.mpr ⟨J.mul_mem hx (oddCoreOf_le_self J hn), hc⟩, n⁻¹,
    (oddCoreOf J).inv_mem hn, by group⟩


@[expose] def fixedSylows (A J : Subgroup G) : Set (Subgroup G) :=
  {T | IsSylow2In T J ∧ T ≤ Subgroup.centralizer (A : Set G)}

@[expose] def secMember (A J : Subgroup G) : Subgroup G := ⨆ T ∈ fixedSylows A J, T

omit [Finite G] [Fact p.Prime] in
theorem le_secMember {A J T : Subgroup G} (hT : T ∈ fixedSylows A J) : T ≤ secMember A J :=
  le_iSup₂_of_le T hT le_rfl

omit [Finite G] [Fact p.Prime] in
theorem secMember_le (A J : Subgroup G) :
    secMember A J ≤ J ⊓ Subgroup.centralizer (A : Set G) :=
  iSup₂_le fun _ hT => le_inf hT.1.1 hT.2

omit [Finite G] [Fact p.Prime] in
theorem secMember_le_left (A J : Subgroup G) : secMember A J ≤ J :=
  (secMember_le A J).trans inf_le_left

omit [Finite G] [Fact p.Prime] in
theorem secMember_le_centralizer (A J : Subgroup G) :
    secMember A J ≤ Subgroup.centralizer (A : Set G) :=
  (secMember_le A J).trans inf_le_right

omit [Finite G] [Fact p.Prime] in
theorem conjSub_secMember_le {A J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (A : Set G)) :
    conjSub g (secMember A J) ≤ secMember A (conjSub g J) := by
  unfold secMember
  rw [conjSub_iSup]
  refine iSup_le fun T => ?_
  rw [conjSub_iSup]
  refine iSup_le fun hT => ?_
  refine le_iSup₂_of_le (conjSub g T) ⟨hT.1.conj g, ?_⟩ le_rfl
  intro y hy
  rw [mem_conjSub_iff] at hy
  have ht : g⁻¹ * y * g ∈ Subgroup.centralizer (A : Set G) := hT.2 hy
  have := (Subgroup.centralizer (A : Set G)).mul_mem
    ((Subgroup.centralizer (A : Set G)).mul_mem hg ht)
    ((Subgroup.centralizer (A : Set G)).inv_mem hg)
  simpa [mul_assoc] using this

omit [Finite G] [Fact p.Prime] in
theorem conjSub_secMember {A J : Subgroup G} {g : G} (hg : g ∈ Subgroup.centralizer (A : Set G)) :
    conjSub g (secMember A J) = secMember A (conjSub g J) := by
  refine le_antisymm (conjSub_secMember_le hg) ?_
  have h1 := conjSub_secMember_le (A := A) (J := conjSub g J)
    ((Subgroup.centralizer (A : Set G)).inv_mem hg)
  rw [conjSub_inv_conjSub] at h1
  have h2 := conjSub_mono (n := g) h1
  rwa [conjSub_conjSub_inv] at h2

omit [Finite G] [Fact p.Prime] in
theorem conjSub_secMember_of_mem {A J : Subgroup G} {g : G} (hgJ : g ∈ J)
    (hg : g ∈ Subgroup.centralizer (A : Set G)) : conjSub g (secMember A J) = secMember A J := by
  rw [conjSub_secMember hg, conjSub_eq_self_of_mem hgJ]

omit [Fact p.Prime] in
theorem exists_mem_fixedSylows {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) : ∃ T, T ∈ fixedSylows A J :=
  exists_isSylow2In_centralizer hA hAJ

omit [Finite G] [Fact p.Prime] in
def mulSub (M N : Subgroup G) (h : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) : Subgroup G where
  carrier := {x | ∃ m ∈ M, ∃ n ∈ N, x = m * n}
  mul_mem' := by
    rintro _ _ ⟨m, hm, n, hn, rfl⟩ ⟨m', hm', n', hn', rfl⟩
    refine ⟨m * m', M.mul_mem hm hm', (m'⁻¹ * n * m') * n', N.mul_mem ?_ hn', by group⟩
    have := h m'⁻¹ (M.inv_mem hm') n hn
    simpa using this
  one_mem' := ⟨1, M.one_mem, 1, N.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨m, hm, n, hn, rfl⟩
    refine ⟨m⁻¹, M.inv_mem hm, m * n⁻¹ * m⁻¹, h m hm n⁻¹ (N.inv_mem hn), by group⟩


theorem exists_mul_secMember (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hJ : J ∈ Ω) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) {x : G} (hx : x ∈ J) :
    ∃ m ∈ secMember A J, ∃ n ∈ oddCoreOf J, x = m * n := by
  have hnorm : ∀ j ∈ J, ∀ n ∈ oddCoreOf J, j * n * j⁻¹ ∈ oddCoreOf J := fun j hj n hn =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hj) hn
  have hnormM : ∀ m ∈ secMember A J, ∀ n ∈ oddCoreOf J, m * n * m⁻¹ ∈ oddCoreOf J :=
    fun m hm n hn => hnorm m (secMember_le_left A J hm) n hn
  have hle : J ≤ mulSub (secMember A J) (oddCoreOf J) hnormM := by
    refine hΩ.le_of_forall_isSylow2In hJ fun V hV => ?_
    obtain ⟨T₀, hT₀⟩ := exists_mem_fixedSylows hA hAJ
    obtain ⟨x', hx'J, hx'⟩ := exists_conjSub_eq_of_isSylow2In hT₀.1 hV
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_mul_of_mem hA hAJ hx'J
    intro v hv
    rw [← hx', mem_conjSub_iff] at hv
    set t : G := (c * n)⁻¹ * v * (c * n) with htdef
    have htT : t ∈ T₀ := hv
    have htJ : t ∈ J := hT₀.1.1 htT
    have hcJ : c ∈ J := (Subgroup.mem_inf.mp hc).1
    have hcC : c ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp hc).2
    have hm' : c * t * c⁻¹ ∈ secMember A J := by
      have h1 : c * t * c⁻¹ ∈ conjSub c (secMember A J) := conj_mem_conjSub (le_secMember hT₀ htT)
      rwa [conjSub_secMember_of_mem hcJ hcC] at h1
    have ho₁ : n * t * n⁻¹ * t⁻¹ ∈ oddCoreOf J := by
      have h1 := hnorm t htJ n⁻¹ ((oddCoreOf J).inv_mem hn)
      have h2 := (oddCoreOf J).mul_mem hn h1
      simpa [mul_assoc] using h2
    have ho₂ : c * (n * t * n⁻¹ * t⁻¹) * c⁻¹ ∈ oddCoreOf J := hnorm c hcJ _ ho₁
    refine ⟨c * t * c⁻¹, hm', (c * t * c⁻¹)⁻¹ * (c * (n * t * n⁻¹ * t⁻¹) * c⁻¹) * (c * t * c⁻¹),
      ?_, ?_⟩
    · have := hnormM _ ((secMember A J).inv_mem hm') _ ho₂
      simpa using this
    · have hv' : v = c * n * t * (c * n)⁻¹ := by rw [htdef]; group
      rw [hv']
      group
  obtain ⟨m, hm, n, hn, h⟩ := hle hx
  exact ⟨m, hm, n, hn, h⟩

omit [Fact p.Prime] in
theorem isSylow2In_secMember_iff {A J V : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) : IsSylow2In V (secMember A J) ↔ V ∈ fixedSylows A J := by
  have hback : ∀ {W : Subgroup G}, W ∈ fixedSylows A J → IsSylow2In W (secMember A J) :=
    fun {W} hW => ⟨le_secMember hW, hW.1.2.1, fun V' hV'M hV'2 hle =>
      hW.1.2.2 V' (hV'M.trans (secMember_le_left A J)) hV'2 hle⟩
  refine ⟨fun hV => ?_, hback⟩
  obtain ⟨T₀, hT₀⟩ := exists_mem_fixedSylows hA hAJ
  have hcard : Nat.card T₀ = Nat.card V := (hback hT₀).natCard_eq hV
  have hVJ : V ≤ J := hV.1.trans (secMember_le_left A J)
  exact ⟨hT₀.1.of_natCard_le hV.2.1 hVJ hcard.le, hV.1.trans (secMember_le_centralizer A J)⟩

theorem isUniqueInvolution_secMember (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G}
    (hA : IsPGroup 2 ↥A) (hJ : J ∈ Ω) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) {z : G}
    (hz : IsUniqueInvolution J z) : IsUniqueInvolution (secMember A J) z := by
  obtain ⟨T₀, hT₀⟩ := exists_mem_fixedSylows hA hAJ
  have h8 : 8 ≤ Nat.card T₀ := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJ hT₀.1)
  have hzT : z ∈ T₀ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup hz hT₀.1.1 hT₀.1.2.1 (by omega)
  exact AscL62.isUniqueInvolution_of_le hz (secMember_le_left A J) (le_secMember hT₀ hzT)


omit [Finite G] [Fact p.Prime] in
@[expose] def secQuotMap (A J : Subgroup G) :
    ↥(secMember A J) →* ↥J ⧸ classicalInvolutionOddCore ↥J :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥J)).comp
    (Subgroup.inclusion (secMember_le_left A J))

omit [Finite G] [Fact p.Prime] in
theorem mem_ker_secQuotMap {A J : Subgroup G} {x : ↥(secMember A J)} :
    x ∈ (secQuotMap A J).ker ↔ (x : G) ∈ oddCoreOf J := by
  rw [MonoidHom.mem_ker, secQuotMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_oddCoreOf_iff]
  exact ⟨fun h => ⟨secMember_le_left A J x.2, h⟩, fun ⟨_, h⟩ => h⟩

theorem secQuotMap_surjective (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hJ : J ∈ Ω) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) : Function.Surjective (secQuotMap A J) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥J) q
  obtain ⟨m, hm, n, hn, hxmn⟩ := exists_mul_secMember hΩ hA hJ hAJ x.2
  refine ⟨⟨m, hm⟩, ?_⟩
  change QuotientGroup.mk' (classicalInvolutionOddCore ↥J) ⟨m, secMember_le_left A J hm⟩ =
    QuotientGroup.mk' (classicalInvolutionOddCore ↥J) x
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h1 : (⟨m, secMember_le_left A J hm⟩ : ↥J)⁻¹ * x = ⟨n, oddCoreOf_le_self J hn⟩ :=
    Subtype.ext (by simp [hxmn])
  rw [h1]
  exact (mem_oddCoreOf_iff.mp hn).2

omit [Finite G] [Fact p.Prime] in
theorem ker_secQuotMap_eq (A J : Subgroup G) :
    (secQuotMap A J).ker = (oddCoreOf J).subgroupOf (secMember A J) := by
  ext x
  rw [mem_ker_secQuotMap, Subgroup.mem_subgroupOf]

omit [Fact p.Prime] in
theorem odd_natCard_ker_secQuotMap (A J : Subgroup G) :
    Odd (Nat.card ↥(secQuotMap A J).ker) := by
  rw [ker_secQuotMap_eq]
  have hcard : Nat.card ↥((oddCoreOf J).subgroupOf (secMember A J)) =
      Nat.card ↥(oddCoreOf J ⊓ secMember A J) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [hcard]
  exact (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem oddCoreOf_secMember (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hJ : J ∈ Ω) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) :
    oddCoreOf (secMember A J) = secMember A J ⊓ oddCoreOf J := by
  have hψ := secQuotMap_surjective hΩ hA hJ hAJ
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxO⟩ := mem_oddCoreOf_iff.mp hx
    refine ⟨hxM, ?_⟩
    have hnorm : ((classicalInvolutionOddCore ↥(secMember A J)).map (secQuotMap A J)).Normal :=
      (classicalInvolutionOddCore_normal _).map _ hψ
    have hodd : Odd (Nat.card ↥((classicalInvolutionOddCore ↥(secMember A J)).map
        (secQuotMap A J))) :=
      (CFSG.ComponentClassification.OddCore.odd_card ↥(secMember A J)).of_dvd_nat
        (Subgroup.card_map_dvd (H := classicalInvolutionOddCore ↥(secMember A J))
          (secQuotMap A J))
    have hle : (classicalInvolutionOddCore ↥(secMember A J)).map (secQuotMap A J) ≤
        classicalInvolutionOddCore (↥J ⧸ classicalInvolutionOddCore ↥J) := le_sSup ⟨hnorm, hodd⟩
    have hcf : classicalInvolutionOddCore (↥J ⧸ classicalInvolutionOddCore ↥J) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree ↥J
    rw [hcf] at hle
    have h1 : secQuotMap A J ⟨x, hxM⟩ ∈ (⊥ : Subgroup (↥J ⧸ classicalInvolutionOddCore ↥J)) :=
      hle (Subgroup.mem_map_of_mem _ hxO)
    have h2 : (⟨x, hxM⟩ : ↥(secMember A J)) ∈ (secQuotMap A J).ker := by
      rw [MonoidHom.mem_ker]
      exact Subgroup.mem_bot.mp h1
    exact mem_ker_secQuotMap.mp h2
  · rintro x ⟨hxM, hxO⟩
    have hker : (⟨x, hxM⟩ : ↥(secMember A J)) ∈ (secQuotMap A J).ker :=
      mem_ker_secQuotMap.mpr hxO
    have hle : (secQuotMap A J).ker ≤ classicalInvolutionOddCore ↥(secMember A J) :=
      le_sSup ⟨(secQuotMap A J).normal_ker, odd_natCard_ker_secQuotMap A J⟩
    exact mem_oddCoreOf_iff.mpr ⟨hxM, hle hker⟩

theorem nonempty_equiv_secMember (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hJ : J ∈ Ω) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) :
    Nonempty (↥(secMember A J) ⧸ classicalInvolutionOddCore ↥(secMember A J) ≃*
      SL(2, GaloisField p f)) := by
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hJ
  have hker : (secQuotMap A J).ker = classicalInvolutionOddCore ↥(secMember A J) := by
    ext x
    rw [mem_ker_secQuotMap]
    have h1 : x ∈ classicalInvolutionOddCore ↥(secMember A J) ↔
        (x : G) ∈ oddCoreOf (secMember A J) :=
      ⟨fun h => mem_oddCoreOf_iff.mpr ⟨x.2, h⟩, fun h => (mem_oddCoreOf_iff.mp h).2⟩
    rw [h1, oddCoreOf_secMember hΩ hA hJ hAJ]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivOfSurjective (secQuotMap A J)
      (secQuotMap_surjective hΩ hA hJ hAJ)).trans e)⟩


omit [Finite G] [Fact p.Prime] in
theorem exists_orderOf_eq_pow_two {T : Subgroup G} (hT : IsPGroup 2 ↥T) {t : G} (ht : t ∈ T) :
    ∃ a : ℕ, orderOf t = 2 ^ a := by
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have h1 : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨i, hi⟩

theorem secMember_perfect (hΩ : HypOmegaMod p f Ω) {A J : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hJ : J ∈ Ω) (hAJ : ⁅A, J⁆ ≤ oddCoreOf J) : Group.IsPerfect ↥(secMember A J) := by
  set M := secMember A J with hM
  have hψ := secQuotMap_surjective hΩ hA hJ hAJ
  have hJperf : Group.IsPerfect ↥J := hΩ.isPerfect hJ
  have hbar : Group.IsPerfect (↥J ⧸ classicalInvolutionOddCore ↥J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (classicalInvolutionOddCore ↥J))
      (QuotientGroup.mk'_surjective _)
  set C : Subgroup ↥M := commutator ↥M with hC
  have hCtop : C.map (secQuotMap A J) = ⊤ := by
    rw [hC, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective _ hψ, ← commutator_def, hbar.commutator_eq_top]
  have h2el : ∀ y : ↥M, (∃ a : ℕ, orderOf (y : G) = 2 ^ a) → y ∈ C := by
    rintro y ⟨a, ha⟩
    have hyψ : secQuotMap A J y ∈ C.map (secQuotMap A J) := by
      rw [hCtop]
      exact Subgroup.mem_top _
    obtain ⟨c, hcC, hcy⟩ := hyψ
    have hk : c⁻¹ * y ∈ (secQuotMap A J).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel]
    have hordk : orderOf (c⁻¹ * y) ∣ Nat.card ↥(secQuotMap A J).ker :=
      Subgroup.orderOf_dvd_natCard _ hk
    have hodd := odd_natCard_ker_secQuotMap A J
    have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).mpr hcC
    have hπ : QuotientGroup.mk' C y = QuotientGroup.mk' C (c⁻¹ * y) := by
      rw [map_mul, map_inv, hc1, inv_one, one_mul]
    have hy2 : orderOf y = 2 ^ a := by
      rw [← Subgroup.orderOf_coe]
      exact ha
    have h1 : orderOf (QuotientGroup.mk' C y) ∣ 2 ^ a := hy2 ▸ orderOf_map_dvd _ y
    have h2 : orderOf (QuotientGroup.mk' C y) ∣ Nat.card ↥(secQuotMap A J).ker := by
      rw [hπ]
      exact (orderOf_map_dvd _ _).trans hordk
    have hcop2 : Nat.Coprime 2 (Nat.card ↥(secQuotMap A J).ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h =>
        (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    have h3 : orderOf (QuotientGroup.mk' C y) = 1 :=
      (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left a hcop2)).eq_one_of_dvd h2
    exact (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp h3)
  have hgen : ∀ T ∈ fixedSylows A J, T ≤ C.map M.subtype := by
    intro T hT t ht
    have hy : (⟨t, le_secMember hT ht⟩ : ↥M) ∈ C :=
      h2el _ (exists_orderOf_eq_pow_two hT.1.2.1 ht)
    exact ⟨_, hy, rfl⟩
  have hMle : M ≤ C.map M.subtype := iSup₂_le fun T hT => hgen T hT
  refine Group.isPerfect_def.mpr (eq_top_iff.mpr fun y _ => ?_)
  obtain ⟨c, hc, hcy⟩ := hMle y.2
  have : c = y := Subtype.ext hcy
  exact this ▸ hc

end CFSG.ClassicalInvolution.Asc77.AscE184Sect
