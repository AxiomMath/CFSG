module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

section Burnside

variable {H : Type*} [Group H] [Finite H]

theorem exists_normal_threeComplement (W : Sylow 3 H)
    (hW : Subgroup.normalizer (W : Set H) ≤ Subgroup.centralizer (W : Set H)) :
    ∃ M : Subgroup H, M.Normal ∧ Subgroup.IsComplement' M (W : Subgroup H) ∧ ¬ 3 ∣ Nat.card M ∧
      ∀ h : H, h ∈ M ↔ ¬ 3 ∣ orderOf h := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := MonoidHom.ker_transferSylow_isComplement' W hW
  set M := (MonoidHom.transferSylow W hW).ker with hM
  have hMcop : ¬ 3 ∣ Nat.card M := by
    have h1 : (W : Subgroup H).index = Nat.card M := hc.index_eq_card
    rw [← h1]
    exact W.not_dvd_index
  refine ⟨M, inferInstance, hc, hMcop, fun h => ⟨fun hh => ?_, fun hh => ?_⟩⟩
  · intro hd
    exact hMcop (hd.trans (Subgroup.orderOf_dvd_natCard M hh))
  · obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp W.isPGroup' (MonoidHom.transferSylow W hW h)
    have hdvd : orderOf (MonoidHom.transferSylow W hW h) ∣ orderOf h := orderOf_map_dvd _ h
    have hk0 : k = 0 := by
      by_contra hne
      exact hh ((dvd_pow_self 3 hne).trans (hk ▸ hdvd))
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact MonoidHom.mem_ker.mpr hk

end Burnside

variable {G : Type} [Group G] [Finite G]

theorem exists_two_lift {S : Type*} [Group S] (P B : Subgroup G)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hB3 : IsPGroup 3 ↥B) (θ : ↥P →* S)
    (hθ2 : IsPGroup 2 ↥θ.range)
    (hcen : ∀ y ∈ P, IsPGroup 3 ↥(Subgroup.zpowers y) → ∀ q ∈ P, y * q = q * y) :
    ∃ T : Subgroup G, T ≤ P ∧ IsPGroup 2 ↥T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (T.subgroupOf P).map θ = θ.range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W⟩ : Nonempty (Sylow 3 ↥P) := inferInstance
  have hWc : ∀ w : ↥P, w ∈ (W : Subgroup ↥P) → ∀ q : ↥P, w * q = q * w := by
    intro w hw q
    apply Subtype.ext
    refine hcen (w : G) w.2 ?_ q q.2
    have h1 : IsPGroup 3 ↥(Subgroup.zpowers w) :=
      W.isPGroup'.to_le (Subgroup.zpowers_le.2 hw)
    have h2 := h1.map P.subtype
    rwa [MonoidHom.map_zpowers] at h2
  have hN : Subgroup.normalizer (W : Set ↥P) ≤ Subgroup.centralizer (W : Set ↥P) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hWc w hw g
  obtain ⟨M, hMn, hMc, hMcop, hMmem⟩ := exists_normal_threeComplement W hN
  have hθW : ∀ w : ↥P, w ∈ (W : Subgroup ↥P) → θ w = 1 := by
    intro w hw
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp W.isPGroup' ⟨w, hw⟩
    have hk' : orderOf w = 3 ^ k := by simpa using hk
    have h1 : orderOf (⟨θ w, (MonoidHom.mem_range.2 ⟨w, rfl⟩)⟩ : ↥θ.range) ∣ orderOf w :=
      orderOf_map_dvd (θ.rangeRestrict) w
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hθ2 ⟨θ w, (MonoidHom.mem_range.2 ⟨w, rfl⟩)⟩
    have hj0 : j = 0 := by
      by_contra hne
      have h2 : 2 ∣ 3 ^ k := (dvd_pow_self 2 hne).trans (hj ▸ h1) |>.trans (hk' ▸ dvd_refl _)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact congrArg Subtype.val hj
  set M' : Subgroup G := M.map P.subtype with hM'
  have hM'P : M' ≤ P := Subgroup.map_subtype_le M
  have hM'cop : ¬ 3 ∣ Nat.card M' := by
    rw [hM', Subgroup.card_map_of_injective P.subtype_injective]
    exact hMcop
  have hBM' : ∀ a ∈ B, ∀ m ∈ M', a * m * a⁻¹ ∈ M' := by
    intro a ha m hm
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    have hmP : a * (m₀ : G) * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hBP ha) _).1 m₀.2
    have hord : orderOf (a * (m₀ : G) * a⁻¹) = orderOf m₀ := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    have hmem : (⟨a * (m₀ : G) * a⁻¹, hmP⟩ : ↥P) ∈ M := by
      refine (hMmem _).2 ?_
      rw [Subgroup.orderOf_mk, hord]
      intro hdvd
      exact hMcop (hdvd.trans (Subgroup.orderOf_dvd_natCard M hm₀))
    exact ⟨_, hmem, rfl⟩
  obtain ⟨T₂, hT₂⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_normalizing_sylow (p := 2) (q := 3)
    B M' hB3 Nat.prime_three hBM' hM'cop
  refine ⟨T₂.map M'.subtype, (Subgroup.map_subtype_le _).trans hM'P, T₂.isPGroup'.map _, hT₂, ?_⟩
  have hθM : ∀ q : ↥P, ∃ m : ↥M', θ q = θ ⟨m, hM'P m.2⟩ := by
    intro q
    obtain ⟨m, hm, w, hw, hq⟩ := Set.mem_mul.1
      ((Subgroup.isComplement'_def.1 hMc).mul_eq ▸ Set.mem_univ q)
    refine ⟨⟨(m : G), ⟨m, hm, rfl⟩⟩, ?_⟩
    rw [← hq, map_mul, hθW w hw, mul_one]
  let θM : ↥M' →* ↥θ.range := (θ.comp (Subgroup.inclusion hM'P)).codRestrict θ.range
    (fun m => MonoidHom.mem_range.2 ⟨_, rfl⟩)
  have hθMs : Function.Surjective θM := by
    rintro ⟨r, q, rfl⟩
    obtain ⟨m, hm⟩ := hθM q
    exact ⟨m, Subtype.ext hm.symm⟩
  have htop : IsPGroup 2 (⊤ : Subgroup ↥θ.range) := hθ2.of_equiv Subgroup.topEquiv.symm
  have hQ : (T₂.mapSurjective hθMs : Subgroup ↥θ.range) = ⊤ :=
    ((T₂.mapSurjective hθMs).3 htop le_top).symm
  rw [Sylow.coe_mapSurjective] at hQ
  refine le_antisymm (Subgroup.map_le_range _ _) ?_
  rintro r hr
  have hr' : (⟨r, hr⟩ : ↥θ.range) ∈ (T₂ : Subgroup ↥M').map θM := by
    rw [hQ]
    exact Subgroup.mem_top _
  obtain ⟨t₂, ht₂, hθt⟩ := hr'
  refine ⟨⟨(t₂ : G), hM'P t₂.2⟩, ?_, congrArg Subtype.val hθt⟩
  show _ ∈ (Subgroup.map M'.subtype ↑T₂).subgroupOf P
  rw [Subgroup.mem_subgroupOf]
  exact ⟨t₂, ht₂, rfl⟩

section KTransfer

variable {L B K : Subgroup G}

theorem mem_chevTransfer_iff {s : PSimple 3 L} :
    s ∈ chevTransfer 3 L K ↔ ∃ k : ↥L, (k : G) ∈ K ∧ chevQuotHom 3 L k = s := by
  unfold chevTransfer
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem chevQuotHom_normalizerMonoidHom (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {ρ : ↥B →* PSimple 3 L}
    (hρ : ∀ b : ↥B, chevAut 3 L ⟨b, hBN b.2⟩ = MulAut.conj (ρ b)) (b : ↥B) (l : ↥L) :
    chevQuotHom 3 L (L.normalizerMonoidHom ⟨b, hBN b.2⟩ l) =
      ρ b * chevQuotHom 3 L l * (ρ b)⁻¹ := by
  rw [← chevAut_chevQuotHom, hρ b]
  rfl

theorem chevTransfer_le_centralizer (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {ρ : ↥B →* PSimple 3 L}
    (hρ : ∀ b : ↥B, chevAut 3 L ⟨b, hBN b.2⟩ = MulAut.conj (ρ b)) {d : ↥B}
    (hKd : K ≤ Subgroup.centralizer ({(d : G)} : Set G)) :
    chevTransfer 3 L K ≤ Subgroup.centralizer ({ρ d} : Set (PSimple 3 L)) := by
  intro s hs
  obtain ⟨k, hkK, rfl⟩ := mem_chevTransfer_iff.1 hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := chevQuotHom_normalizerMonoidHom hBN hρ d k
  have h2 : L.normalizerMonoidHom ⟨d, hBN d.2⟩ k = k := by
    apply Subtype.ext
    rw [chev_coe_normalizerMonoidHom]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKd hkK)
    show (d : G) * (k : G) * (d : G)⁻¹ = k
    rw [← this]
    group
  rw [h2] at h1
  have h3 : ρ d * chevQuotHom 3 L k = chevQuotHom 3 L k * ρ d :=
    calc ρ d * chevQuotHom 3 L k = (ρ d * chevQuotHom 3 L k * (ρ d)⁻¹) * ρ d := by group
      _ = chevQuotHom 3 L k * ρ d := by rw [← h1]
  exact h3.symm

theorem isPerfect_chevTransfer (hKL : K ≤ L) (hKq : CFSG.Open.IsQuasisimple ↥K) :
    Group.IsPerfect ↥(chevTransfer 3 L K) := by
  haveI : Group.IsPerfect ↥K := ⟨hKq.1⟩
  haveI : Group.IsPerfect ↥(K.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  exact Group.IsPerfect.map (f := chevQuotHom 3 L)

theorem chevQuotHom_eq_one_of_central (K : Subgroup G) {k : ↥K}
    (hk : ∀ k' : ↥K, k * k' = k' * k) : chevQuotHom 3 K k = 1 := by
  show (QuotientGroup.mk' (Subgroup.center (PQuot 3 K))) (pQuotHom 3 K k) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro y
  obtain ⟨k', rfl⟩ := pQuotHom_surjective 3 K y
  rw [← map_mul, ← map_mul, hk k']

theorem chevQuotHom_eq_one_of_coprime (K : Subgroup G) (hcop : Nat.Coprime 3 (Nat.card K))
    (k : ↥K) : chevQuotHom 3 K k = 1 := by
  have htop : (⊤ : Subgroup ↥K) ≤ GLAPPrimeCore 3 ↥K :=
    le_sSup ⟨Subgroup.normal_top, by rwa [Subgroup.card_top]⟩
  show (QuotientGroup.mk' (Subgroup.center (PQuot 3 K))) (pQuotHom 3 K k) = 1
  have h1 : pQuotHom 3 K k = 1 := by
    show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) k = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact htop (Subgroup.mem_top k)
  rw [h1, map_one]

theorem ker_dichotomy (hKL : K ≤ L) (hKq : CFSG.Open.IsQuasisimple ↥K) :
    (∀ k : ↥K, chevQuotHom 3 L (Subgroup.inclusion hKL k) = 1 → ∀ k' : ↥K, k * k' = k' * k) ∨
      Nat.Coprime 3 (Nat.card K) := by
  set φ : ↥K →* PSimple 3 L := (chevQuotHom 3 L).comp (Subgroup.inclusion hKL) with hφ
  by_cases hN : φ.ker = ⊤
  · right
    have hcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ GLAPPrimeCoreOf 3 L := by
      intro k hk k' hk'
      have hκ : ∀ κ : ↥L, chevQuotHom 3 L κ = 1 → pQuotHom 3 L κ ∈ Subgroup.center (PQuot 3 L) := by
        intro κ hκ
        have : (QuotientGroup.mk' (Subgroup.center (PQuot 3 L))) (pQuotHom 3 L κ) = 1 := hκ
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      have h1 : chevQuotHom 3 L ⟨k, hKL hk⟩ = 1 := by
        have : (⟨k, hk⟩ : ↥K) ∈ φ.ker := hN ▸ Subgroup.mem_top _
        exact this
      have hc := Subgroup.mem_center_iff.1 (hκ _ h1) (pQuotHom 3 L ⟨k', hKL hk'⟩)
      have hzL : ⁅k, k'⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem (hKL hk) (hKL hk')) (L.inv_mem (hKL hk)))
          (L.inv_mem (hKL hk'))
      refine (chev_mem_glaPPrimeCoreOf_iff hzL).2 ?_
      have e : (⟨⁅k, k'⁆, hzL⟩ : ↥L) = ⟨k, hKL hk⟩ * ⟨k', hKL hk'⟩ * ⟨k, hKL hk⟩⁻¹ * ⟨k', hKL hk'⟩⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [e, ← ker_pQuotHom, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      generalize pQuotHom 3 L ⟨k, hKL hk⟩ = a at hc ⊢
      generalize pQuotHom 3 L ⟨k', hKL hk'⟩ = b at hc ⊢
      rw [← hc]
      group
    have hle : ⁅K, K⁆ ≤ GLAPPrimeCoreOf 3 L := Subgroup.commutator_le.2 hcomm
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hKq.1⟩
    rw [hperf] at hle
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three L)
  · left
    have hne : φ.ker ≠ ⊤ := hN
    have hle := le_center_of_normal_of_isQuasisimple hKq (MonoidHom.normal_ker φ) hne
    intro k hk k'
    exact (Subgroup.mem_center_iff.1 (hle hk) k').symm

theorem exists_surj_chevTransfer (hKL : K ≤ L) (hKq : CFSG.Open.IsQuasisimple ↥K) :
    ∃ f : ↥(chevTransfer 3 L K) →* PSimple 3 K, Function.Surjective f := by
  let θ : ↥K →* ↥(chevTransfer 3 L K) :=
    ((chevQuotHom 3 L).comp (Subgroup.inclusion hKL)).codRestrict _
      (fun k => mem_chevTransfer_iff.2 ⟨Subgroup.inclusion hKL k, k.2, rfl⟩)
  have hθ : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    obtain ⟨k, hkK, rfl⟩ := mem_chevTransfer_iff.1 hs
    exact ⟨⟨k, hkK⟩, rfl⟩
  have hker : θ.ker ≤ (chevQuotHom 3 K).ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hk1 : chevQuotHom 3 L (Subgroup.inclusion hKL k) = 1 := congrArg Subtype.val hk
    rcases ker_dichotomy hKL hKq with h | h
    · exact chevQuotHom_eq_one_of_central K (h k hk1)
    · exact chevQuotHom_eq_one_of_coprime K h k
  have hlift : Function.Surjective (QuotientGroup.lift θ.ker (chevQuotHom 3 K) hker) := by
    intro y
    obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 K y
    exact ⟨QuotientGroup.mk k, rfl⟩
  exact ⟨(QuotientGroup.lift θ.ker (chevQuotHom 3 K) hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.toMonoidHom,
    hlift.comp (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.surjective⟩

noncomputable def preimageK (L K : Subgroup G) (T' : Subgroup (PSimple 3 L)) : Subgroup G :=
  ((T'.comap (chevQuotHom 3 L)) ⊓ K.subgroupOf L).map L.subtype

theorem mem_preimageK {T' : Subgroup (PSimple 3 L)} {g : G} :
    g ∈ preimageK L K T' ↔ ∃ hg : g ∈ L, g ∈ K ∧ chevQuotHom 3 L ⟨g, hg⟩ ∈ T' := by
  unfold preimageK
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, Subgroup.mem_subgroupOf.1 hl.2, hl.1⟩
  · rintro ⟨hg, hgK, hπ⟩
    exact ⟨⟨g, hg⟩, ⟨hπ, Subgroup.mem_subgroupOf.2 hgK⟩, rfl⟩

end KTransfer

section Final

variable {L B K : Subgroup G}

theorem exists_T_of_T' (hBN : B ≤ Subgroup.normalizer (L : Set G)) {ρ : ↥B →* PSimple 3 L}
    (hρ : ∀ b : ↥B, chevAut 3 L ⟨b, hBN b.2⟩ = MulAut.conj (ρ b)) (hB3 : IsPGroup 3 ↥B)
    (hKL : K ≤ L) (hKq : CFSG.Open.IsQuasisimple ↥K) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hKs : Nontrivial (PSimple 3 K)) {T' : Subgroup (PSimple 3 L)}
    (hT'K : T' ≤ chevTransfer 3 L K) (hT'2 : IsPGroup 2 ↥T')
    (hT'N : ∀ b : ↥B, ρ b ∈ Subgroup.normalizer (T' : Set (PSimple 3 L)))
    (hT'a : ∃ (b : ↥B) (t : PSimple 3 L), t ∈ T' ∧ ρ b * t * (ρ b)⁻¹ ≠ t)
    (hT'z : ∃ t ∈ T', ∃ k ∈ chevTransfer 3 L K, t * k ≠ k * t) :
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 ↥T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ Nat.card ↥T' ≤ Nat.card ↥T ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := chevQuotHom 3 L with hπ
  set P := preimageK L K T' with hP
  have hPK : P ≤ K := fun g hg => ((mem_preimageK).1 hg).2.1
  have hPL : P ≤ L := hPK.trans hKL
  have hfwd : ∀ b ∈ B, ∀ g ∈ P, b * g * b⁻¹ ∈ P := by
    intro b hb g hg
    obtain ⟨hgL, hgK, hπg⟩ := mem_preimageK.1 hg
    set bb : ↥B := ⟨b, hb⟩ with hbb
    have h1 := chevQuotHom_normalizerMonoidHom hBN hρ bb ⟨g, hgL⟩
    have hmem : ρ bb * π ⟨g, hgL⟩ * (ρ bb)⁻¹ ∈ T' :=
      (Subgroup.mem_normalizer_iff.1 (hT'N bb) _).1 hπg
    refine mem_preimageK.2 ⟨(L.normalizerMonoidHom ⟨b, hBN hb⟩ ⟨g, hgL⟩).2,
      (Subgroup.mem_normalizer_iff.1 (hBK hb) g).1 hgK, ?_⟩
    rw [← h1] at hmem
    exact hmem
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hfwd b hb g hg, fun hg => ?_⟩
    have := hfwd b⁻¹ (B.inv_mem hb) _ hg
    simpa [mul_assoc] using this
  let θ : ↥P →* PSimple 3 L := π.comp (Subgroup.inclusion hPL)
  have hrange : θ.range = T' := by
    ext s
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨_, _, hπ'⟩ := mem_preimageK.1 q.2
      exact hπ'
    · intro hs
      obtain ⟨l, hlK, rfl⟩ := mem_chevTransfer_iff.1 (hT'K hs)
      exact ⟨⟨(l : G), mem_preimageK.2 ⟨l.2, hlK, hs⟩⟩, rfl⟩
  have hθ2 : IsPGroup 2 ↥θ.range := by
    rw [hrange]
    exact hT'2
  have hcen : ∀ y ∈ P, IsPGroup 3 ↥(Subgroup.zpowers y) → ∀ q ∈ P, y * q = q * y := by
    intro y hy hy3 q hq
    obtain ⟨hyL, hyK, hπy⟩ := mem_preimageK.1 hy
    obtain ⟨hqL, hqK, -⟩ := mem_preimageK.1 hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hy3 ⟨y, Subgroup.mem_zpowers y⟩
    have hk' : orderOf y = 3 ^ k := by simpa using hk
    have hπ1 : π ⟨y, hyL⟩ = 1 := by
      obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hT'2 ⟨π ⟨y, hyL⟩, hπy⟩
      have hj' : orderOf (π ⟨y, hyL⟩) = 2 ^ j := by simpa using hj
      have hdvd : orderOf (π ⟨y, hyL⟩) ∣ orderOf y := by
        have := orderOf_map_dvd π (⟨y, hyL⟩ : ↥L)
        rwa [Subgroup.orderOf_mk] at this
      have hj0 : j = 0 := by
        by_contra hne
        have h2 : 2 ∣ 3 ^ k := (dvd_pow_self 2 hne).trans (hj' ▸ hdvd) |>.trans (hk' ▸ dvd_refl _)
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
      rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
      exact hj'
    rcases ker_dichotomy hKL hKq with h | h
    · exact congrArg Subtype.val (h ⟨y, hyK⟩ hπ1 ⟨q, hqK⟩)
    · have hyo : orderOf y ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hyK
      have hk0 : k = 0 := by
        by_contra hne
        have h3 : 3 ∣ Nat.card K := (dvd_pow_self 3 hne).trans (hk' ▸ hyo)
        exact absurd h3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 h)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
      rw [hk', one_mul, mul_one]
  obtain ⟨T, hTP, hT2, hTB, hθT⟩ := exists_two_lift P B hBP hB3 θ hθ2 hcen
  have hTK : T ≤ K := hTP.trans hPK
  have hT'T : ∀ t' ∈ T', ∃ t ∈ T, ∃ ht : t ∈ L, π ⟨t, ht⟩ = t' := by
    intro t' ht'
    have : t' ∈ (T.subgroupOf P).map θ := by rw [hθT, hrange]; exact ht'
    obtain ⟨q, hq, rfl⟩ := this
    exact ⟨q, Subgroup.mem_subgroupOf.1 hq, hPL q.2, rfl⟩
  refine ⟨T, hTK, hT2, hTB, ?_, ?_, ?_⟩
  ·
    intro hcomm
    obtain ⟨b, t', ht', hne⟩ := hT'a
    obtain ⟨t, htT, htL, rfl⟩ := hT'T t' ht'
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm htT
    have hbt : (b : G) * t = t * (b : G) := Subgroup.mem_centralizer_iff.1 hc b b.2
    have h1 := chevQuotHom_normalizerMonoidHom hBN hρ b ⟨t, htL⟩
    apply hne
    rw [← h1]
    congr 1
    apply Subtype.ext
    show (b : G) * t * (b : G)⁻¹ = t
    rw [hbt]
    group
  ·
    have h1 : Nat.card ↥T' = Nat.card ↥((T.subgroupOf P).map θ) := by
      rw [hθT, hrange]
    have h2 := Subgroup.card_map_dvd (H := T.subgroupOf P) θ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv] at h2
    rw [h1]
    exact Nat.le_of_dvd Nat.card_pos h2
  ·
    intro hle
    have hne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
      intro htop
      have h1 : ∀ k : ↥K, chevQuotHom 3 K k = 1 := by
        intro k
        show (QuotientGroup.mk' (Subgroup.center (PQuot 3 K))) (pQuotHom 3 K k) = 1
        have : pQuotHom 3 K k = 1 := by
          show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) k = 1
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, htop]
          exact Subgroup.mem_top k
        rw [this, map_one]
      have hsub : Subsingleton (PSimple 3 K) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨a', rfl⟩ := chevQuotHom_surjective 3 K a
        obtain ⟨b', rfl⟩ := chevQuotHom_surjective 3 K b
        rw [h1 a', h1 b']
      exact (not_nontrivial_iff_subsingleton.2 hsub) hKs
    have hZ := le_center_of_normal_of_isQuasisimple hKq (GLAPPrimeCore.normal 3 ↥K) hne
    obtain ⟨t', ht', k'', hk'', hne'⟩ := hT'z
    obtain ⟨t, htT, htL, rfl⟩ := hT'T t' ht'
    obtain ⟨k, hkK, rfl⟩ := mem_chevTransfer_iff.1 hk''
    have htO : (⟨t, hTK htT⟩ : ↥K) ∈ GLAPPrimeCore 3 ↥K :=
      (chev_mem_glaPPrimeCoreOf_iff (hTK htT)).1 (hle htT)
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 (hZ htO) ⟨k, hkK⟩)
    apply hne'
    have hc' : (⟨t, htL⟩ : ↥L) * k = k * ⟨t, htL⟩ := Subtype.ext hc.symm
    rw [← map_mul, ← map_mul, hc']

end Final

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
