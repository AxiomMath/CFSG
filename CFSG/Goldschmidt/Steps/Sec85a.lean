module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterGeneric
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem exists_zpow_of_mem_normalizer {C : Subgroup G} [IsCyclic C] {k : G}
    (hk : k ∈ Subgroup.normalizer (C : Set G)) : ∃ m : ℤ, ∀ c ∈ C, k * c * k⁻¹ = c ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (C.normalizerMonoidHom ⟨k, hk⟩).toMonoidHom
  exact ⟨m, fun c hc => by simpa using congrArg Subtype.val (hm ⟨c, hc⟩)⟩

omit [Finite G] in
theorem commutator_le_centralizer_of_isCyclic {C K : Subgroup G} [IsCyclic C]
    (hK : K ≤ Subgroup.normalizer (C : Set G)) : ⁅K, K⁆ ≤ Subgroup.centralizer (C : Set G) := by
  rw [Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨m₁, h₁⟩ := exists_zpow_of_mem_normalizer (hK hk₁)
  obtain ⟨m₂, h₂⟩ := exists_zpow_of_mem_normalizer (hK hk₂)
  obtain ⟨n₁, h₁'⟩ := exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ (hK hk₁))
  obtain ⟨n₂, h₂'⟩ := exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ (hK hk₂))
  have e₁ : ∀ c ∈ C, (c ^ n₁) ^ m₁ = c := fun c hc => by
    rw [← h₁ _ (C.zpow_mem hc n₁), ← h₁' c hc]
    group
  have e₂ : ∀ c ∈ C, (c ^ n₂) ^ m₂ = c := fun c hc => by
    rw [← h₂ _ (C.zpow_mem hc n₂), ← h₂' c hc]
    group
  refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
  have hc₂ := C.zpow_mem hc n₂
  have hc₂₁ := C.zpow_mem hc₂ n₁
  have hc₂₁₂ := C.zpow_mem hc₂₁ m₂
  have key : ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹ = c := by
    calc ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹
        = k₁ * (k₂ * (k₁⁻¹ * (k₂⁻¹ * c * k₂⁻¹⁻¹) * k₁⁻¹⁻¹) * k₂⁻¹) * k₁⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (((c ^ n₂) ^ n₁) ^ m₂) ^ m₁ := by rw [h₂' c hc, h₁' _ hc₂, h₂ _ hc₂₁, h₁ _ hc₂₁₂]
      _ = c := by
          rw [← zpow_mul (c ^ n₂) n₁ m₂, mul_comm n₁ m₂, zpow_mul (c ^ n₂) m₂ n₁, e₂ c hc,
            e₁ c hc]
  calc c * ⁅k₁, k₂⁆ = ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹ * ⁅k₁, k₂⁆ := by rw [key]
    _ = ⁅k₁, k₂⁆ * c := by group

omit [Finite G] in
theorem commutator_self_le (K : Subgroup G) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)

theorem commutator_eq_bot_of_le_centralizer_fitting {L X : Subgroup G}
    (hX : Group.IsSolvable X) (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLL : ⁅L, L⁆ = L)
    (hLF : L ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G)) : ⁅L, X⁆ = ⊥ := by
  set F := CFSG.fittingSubgroupOf X with hF
  have hFn := GorensteinWalter.fittingSubgroupOf_isNormalIn X
  have hLF' : ⁅F, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hLF
  have h1 : ⁅⁅X, F⁆, L⁆ = ⊥ := by
    refine le_bot_iff.mp (hLF' ▸ Subgroup.commutator_mono ?_ le_rfl)
    rw [Subgroup.commutator_le]
    intro x hx f hf
    rw [commutatorElement_def]
    exact F.mul_mem (hFn.2 x hx f hf) (F.inv_mem hf)
  have h2 : ⁅⁅F, L⁆, X⁆ = ⊥ := by rw [hLF', Subgroup.commutator_bot_left]
  have h3 : ⁅⁅L, X⁆, F⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hLXX : ⁅L, X⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    rw [commutatorElement_def]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLX hl) x).mp hx) (X.inv_mem hx)
  have hLXF : ⁅L, X⁆ ≤ F := by
    intro y hy
    have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3 hy
    have hy' : (⟨y, hLXX hy⟩ : X) ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.mp hyC z ⟨z, hz, rfl⟩
    exact ⟨_, CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hX hy', rfl⟩
  have h4 : ⁅⁅L, X⁆, L⁆ = ⊥ := le_bot_iff.mp (hLF' ▸ Subgroup.commutator_mono hLXF le_rfl)
  have h5 : ⁅⁅X, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm X L]; exact h4
  have h6 : ⁅⁅L, L⁆, X⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h4 h5
  rwa [hLL] at h6

omit [Finite G] in
theorem isCyclic_map_conj {K : Subgroup G} [IsCyclic K] (g : G) :
    IsCyclic (K.map (MulAut.conj g).toMonoidHom) :=
  (MulEquiv.isCyclic (K.equivMapOfInjective _ (MulAut.conj g).injective)).mp inferInstance

theorem mem_qCoreOf_two_of_eq {H : Subgroup G} {a : G} (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (hHa : H = Subgroup.centralizer ({a} : Set G)) : a ∈ qCoreOf H 2 := by
  have hle : Subgroup.zpowers a ≤ H :=
    Subgroup.zpowers_le.mpr (hHa ▸ Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hN : IsNormalIn (Subgroup.zpowers a) H := ⟨hle, fun h hh y hy => by
    have hc := mem_centralizer_zpowers (hHa ▸ hh : h ∈ Subgroup.centralizer ({a} : Set G))
    rw [← Subgroup.mem_centralizer_iff.mp hc y hy, mul_inv_cancel_right]
    exact hy⟩
  have hp : IsPGroup 2 (Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1, pow_one])
  exact le_qCoreOf_of_isNormalIn_pGroup H _ 2 Nat.prime_two hle hN hp (Subgroup.mem_zpowers a)

theorem exists_involution {K : Subgroup G} (hK : IsPGroup 2 K) (hK1 : K ≠ ⊥) :
    ∃ t ∈ K, t ≠ 1 ∧ t ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hK1 (Subgroup.card_eq_one.mp (by simpa using hk))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  refine ⟨x, x.2, fun h => ?_, ?_⟩
  · have h1 : x = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this

omit [Finite G] in
theorem eq_of_mem_omega1 [Finite G] {P : Subgroup G} {a t : G} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hΩ : Subgroup.zpowers a = Omega1 P) (htP : t ∈ P) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    t = a := by
  have htz : t ∈ Subgroup.zpowers a := by
    rw [hΩ]
    exact Subgroup.subset_closure ⟨htP, ht2⟩
  have h2 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  exact (mem_two h2 (Subgroup.mem_zpowers a) ha1 htz).resolve_left ht1

theorem qCoreOf_two_le_centralizer (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {H : Subgroup G} (hAH : A ≤ H) : qCoreOf H 2 ≤ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : IsPGroup 2 (A ⊔ qCoreOf H 2 : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (S.isPGroup'.to_le hset.le) (qCoreOf_isPGroup H 2)
      (hAH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H 2)))
  exact le_sup_right.trans (pGroup_le_centralizer hset h4 hR le_sup_left)

theorem false_of_four (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a)
    (hHa : H = Subgroup.centralizer ({a} : Set G)) {t : G}
    (htA : t ∈ Subgroup.centralizer (A : Set G)) (ht2 : t ^ 2 = 1) (hta : t ∉ Subgroup.zpowers a)
    (hC : ∀ v ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers t, v ≠ 1 → v ^ 2 = 1 →
      Subgroup.centralizer ({v} : Set G) ≤ H) : False := by
  have ha2 : a ^ 2 = 1 := hset.elem.2 a ha
  have ht1 : t ≠ 1 := fun h => hta (h ▸ Subgroup.one_mem _)
  have hat : a ≠ t := fun h => hta (h ▸ Subgroup.mem_zpowers a)
  have hcomm : a * t = t * a := Subgroup.mem_centralizer_iff.mp htA a ha
  set V := Subgroup.zpowers a ⊔ Subgroup.zpowers t with hV
  have hV4 : IsKleinFour V := Semidihedral.FixedCoreNontrivial.isKleinFour_sup_zpowers
    (orderOf_eq_prime ha2 ha1) (orderOf_eq_prime ht2 ht1) hat hcomm
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by
    have := Monoid.pow_exponent_eq_one v
    rwa [IsKleinFour.exponent_two] at this
  have hCAH : Subgroup.centralizer (A : Set G) ≤ H :=
    hHa ▸ Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
  refine false_of_centralizer_le hset (Walter.ne_top_of_mem_benderM hH) fun b hb hb1 => ?_
  have hHb := centralizer_mem_benderM hset h4 ha ha1 hb hb1 hH hHa
  rw [(eq_oddCoreOf_sup hset h4 hb hb1 hHb).2]
  refine sup_le ?_ hCAH
  have hVb : V ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm hset.elem ha hb)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp htA b hb).symm
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two V (oddCoreOf (Subgroup.centralizer ({b} : Set G))) hV2
    (by rw [IsKleinFour.card_four]; norm_num) (odd_card_oddCoreOf _).not_two_dvd_nat
    (hVb.trans (le_normalizer_oddCoreOf _))
  rw [hgen]
  refine iSup₂_le fun v hv => inf_le_right.trans (hC v v.2 (fun h => hv (Subtype.ext h)) ?_)
  simpa using congrArg Subtype.val (hV2 v)

theorem zpowers_eq_omega1 (h81 : S_G81) (h84 : S_G84) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) : Subgroup.zpowers a = Omega1 (qCoreOf H 2) := by
  have hHa := (h81 G S A hset h4 a ha ha1 H hH).1
  have ha2 : a ^ 2 = 1 := hset.elem.2 a ha
  have haP := mem_qCoreOf_two_of_eq ha2 ha1 hHa
  refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨haP, ha2⟩)) ?_
  refine (Subgroup.closure_le _).mpr fun t ht => ?_
  obtain ⟨htP, ht2⟩ := ht
  by_contra hta
  have hAH : A ≤ H := hset.le.trans (le_of_mem_benderM hset h4 ha hH)
  refine false_of_four hset h4 ha ha1 hH hHa (qCoreOf_two_le_centralizer hset h4 hAH htP) ht2
    hta fun v hv hv1 hv2 => ?_
  have hvP : v ∈ qCoreOf H 2 :=
    sup_le (Subgroup.zpowers_le.mpr haP) (Subgroup.zpowers_le.mpr htP) hv
  have hvF : Subgroup.zpowers v ≤ CFSG.fittingSubgroupOf H :=
    Subgroup.zpowers_le.mpr (qCoreOf_le_fittingSubgroupOf H 2 Nat.prime_two hvP)
  have hcard : (Nat.card (Subgroup.zpowers v)).Prime := by
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1]
    exact Nat.prime_two
  refine le_trans (fun y hy => ?_) (h84 G S A hset h4 a ha ha1 H hH _ hvF hcard)
  exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hy)

end CFSG.Goldschmidt.Sec8
