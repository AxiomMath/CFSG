module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique
import CFSG.Quasithin.Background.C2Basic
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_pCoreOf_two (X : Subgroup G) : X ≤ normalizer (pCoreOf 2 X : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨x, hx⟩ * w * (⟨x, hx⟩ : ↥X)⁻¹,
      (CFSG.pCore_normal (G := ↥X) (p := 2)).conj_mem w hw _, rfl⟩
  · intro hy
    obtain ⟨w, hw, hwy⟩ := hy
    have hwy' : (w : G) = x * y * x⁻¹ := hwy
    have hyX : y ∈ X := by
      have h2 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [← h2, ← hwy']
      exact X.mul_mem (X.mul_mem (X.inv_mem hx) w.2) hx
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    have h3 := (CFSG.pCore_normal (G := ↥X) (p := 2)).conj_mem w hw (⟨x, hx⟩ : ↥X)⁻¹
    have h4 : (⟨x, hx⟩ : ↥X)⁻¹ * w * ((⟨x, hx⟩ : ↥X)⁻¹)⁻¹ = ⟨y, hyX⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [hwy']
      group
    rwa [h4] at h3

theorem pCoreOf_le_of_isTwoRadicalIn {X S : Subgroup G} (hS : CFSG.Quasithin.IsTwoRadicalIn X S) :
    pCoreOf 2 X ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.Quasithin.le_of_isSignalizer_of_isTwoRadicalIn hS ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype
  · exact inf_le_left.trans (le_normalizer_pCoreOf_two X)

theorem barM_inf_normalizer_ne {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) : barM X (normalizer (S : Set G) ⊓ L) ≠ barM X L := by
  intro he
  apply hL.not_le_normalizer
  have hO := pCoreOf_le_of_isTwoRadicalIn hA.twoRadical
  intro l hl
  have hlX : l ∈ X := hL.le hl
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨l, hlX⟩ ∈ barM X L :=
    ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [← he] at hmem
  obtain ⟨n, hn, hnl⟩ := hmem
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
  have hw : ((n⁻¹ * ⟨l, hlX⟩ : ↥X) : G) ∈ S := hO ⟨_, hnl, rfl⟩
  have hwN : ((n⁻¹ * ⟨l, hlX⟩ : ↥X) : G) ∈ normalizer (S : Set G) := Subgroup.le_normalizer hw
  have : l = (n : G) * ((n⁻¹ * ⟨l, hlX⟩ : ↥X) : G) := by simp
  rw [this]
  exact (normalizer (S : Set G)).mul_mem hn.1 hwN

theorem isQuasisimple_of_surjective_of_isPGroup_ker {I C : Type} [Group I] [Finite I] [Group C]
    (hQ : Open.IsQuasisimple (I ⧸ CFSG.pCore 2 I)) (φ : I →* C) (hφ : Function.Surjective φ)
    (hk : IsPGroup 2 φ.ker) (hC : CFSG.pCore 2 C = ⊥) : Open.IsQuasisimple C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : φ.ker ≤ CFSG.pCore 2 I := le_sSup ⟨MonoidHom.normal_ker φ, hk⟩
  have hge : CFSG.pCore 2 I ≤ φ.ker := by
    intro x hx
    have h1 : (CFSG.pCore 2 I).map φ ≤ CFSG.pCore 2 C :=
      le_sSup ⟨(CFSG.pCore_normal (G := I) (p := 2)).map φ hφ,
        (CFSG.pCore_isPGroup (G := I) (p := 2)).map φ⟩
    have h2 := h1 ⟨x, hx, rfl⟩
    rw [hC, Subgroup.mem_bot] at h2
    exact h2
  have hker : φ.ker = CFSG.pCore 2 I := le_antisymm hle hge
  exact Open.IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)) hQ

theorem eq_of_map_eq_of_isPGroup_ker {N : Subgroup G} {Q : Type*} [Group Q] (ψ : ↥N →* Q)
    (hψ : IsPGroup 2 ψ.ker) {K₁ K₂ : Subgroup G} (h₁N : K₁ ≤ N) (h₂N : K₂ ≤ N)
    (h₁ : IsSubnormal K₁ N) (h₂ : IsSubnormal K₂ N) (hp₁ : ⁅K₁, K₁⁆ = K₁) (hp₂ : ⁅K₂, K₂⁆ = K₂)
    (he : (K₁.subgroupOf N).map ψ = (K₂.subgroupOf N).map ψ) : K₁ = K₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := ψ.ker.map N.subtype with hT
  have hT2 : IsPGroup 2 T := hψ.map N.subtype
  have hTN : T ≤ N := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hNT : N ≤ normalizer (T : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨n, hn⟩ * w * (⟨n, hn⟩ : ↥N)⁻¹, (MonoidHom.normal_ker ψ).conj_mem w hw _, rfl⟩
    · intro hy
      obtain ⟨w, hw, hwy⟩ := hy
      have hwy' : (w : G) = n * y * n⁻¹ := hwy
      have hyN : y ∈ N := by
        have h2 : n⁻¹ * (n * y * n⁻¹) * n = y := by group
        rw [← h2, ← hwy']
        exact N.mul_mem (N.mul_mem (N.inv_mem hn) w.2) hn
      refine ⟨⟨y, hyN⟩, ?_, rfl⟩
      have h3 := (MonoidHom.normal_ker ψ).conj_mem w hw (⟨n, hn⟩ : ↥N)⁻¹
      have h4 : (⟨n, hn⟩ : ↥N)⁻¹ * w * ((⟨n, hn⟩ : ↥N)⁻¹)⁻¹ = ⟨y, hyN⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [hwy']
        group
      rwa [h4] at h3
  have hle : ∀ {A B : Subgroup G}, A ≤ N →
      (A.subgroupOf N).map ψ ≤ (B.subgroupOf N).map ψ → A ≤ B ⊔ T := by
    intro A B hAN hAB a ha
    obtain ⟨b, hb, hba⟩ := hAB ⟨⟨a, hAN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hb
    have hk : b⁻¹ * ⟨a, hAN ha⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
    have hw : ((b⁻¹ * ⟨a, hAN ha⟩ : ↥N) : G) ∈ T := ⟨_, hk, rfl⟩
    have : a = (b : G) * ((b⁻¹ * ⟨a, hAN ha⟩ : ↥N) : G) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hb hw
  have h12 := hle h₁N he.le
  have h21 := hle h₂N he.ge
  set R := K₁ ⊔ T with hR
  have hRN : R ≤ N := sup_le h₁N hTN
  have hR₂ : R ≤ K₂ ⊔ T := sup_le h12 le_sup_right
  have hs₁ : IsSubnormal K₁ R := by
    have := h₁.inf_of_le hRN
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hs₂ : IsSubnormal K₂ R := by
    have hK₂R : K₂ ≤ R := h21.trans (sup_le le_sup_left le_sup_right)
    have := h₂.inf_of_le hRN
    rwa [inf_eq_left.mpr hK₂R] at this
  exact eq_of_perfect_of_isSubnormal hT2 (hRN.trans hNT) hs₁ hs₂ hp₁ hp₂ le_rfl hR₂

theorem eq_one_of_mem_zpowers_of_not_mem {Y : Type*} [Group Y] {Z : Subgroup Y} {a c : Y}
    (ha : orderOf a = 3) (haZ : a ∉ Z) (hc : c ∈ Subgroup.zpowers a) (hcZ : c ∈ Z) : c = 1 := by
  obtain ⟨k, rfl⟩ := hc
  change a ^ k ∈ Z at hcZ
  change a ^ k = 1
  have ha3 : a ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← ha, pow_orderOf_eq_one]
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h | h | h
  · obtain ⟨m, hm⟩ : (3 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero h
    rw [hm, zpow_mul, ha3, one_zpow]
  · exfalso
    apply haZ
    have hk : k = 3 * (k / 3) + 1 := by omega
    have : a ^ k = a := by
      rw [hk, zpow_add, zpow_mul, ha3, one_zpow, one_mul, zpow_one]
    rwa [this] at hcZ
  · exfalso
    apply haZ
    have hk : k = 3 * (k / 3) + 2 := by omega
    have h2 : (a ^ k) ^ (2 : ℤ) = a := by
      rw [← zpow_mul, hk]
      have : (3 * (k / 3) + 2) * 2 = 3 * (2 * (k / 3) + 1) + 1 := by ring
      rw [this, zpow_add, zpow_mul, ha3, one_zpow, one_mul, zpow_one]
    rw [← h2]
    exact Z.zpow_mem hcZ 2

private theorem zpowers_facts {Y : Type*} [Group Y] {a : Y} (ha : orderOf a = 3) :
    (∀ u v : ↥(Subgroup.zpowers a), u * v = v * u) ∧ (∀ u : ↥(Subgroup.zpowers a), u ^ 3 = 1) ∧
      Nat.card ↥(Subgroup.zpowers a) = 3 := by
  refine ⟨fun u v => ?_, fun u => ?_, by rw [Nat.card_zpowers, ha]⟩
  · obtain ⟨_, i, rfl⟩ := u
    obtain ⟨_, j, rfl⟩ := v
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨_, i, rfl⟩ := u
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow]

theorem four_le_pRank_of_three_blocks {Y : Type*} [Group Y] [Finite Y]
    {L₁ L₂ L₃ Z : Subgroup Y}
    (h12 : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (h13 : ∀ x ∈ L₁, ∀ y ∈ L₃, x * y = y * x)
    (h23 : ∀ x ∈ L₂, ∀ y ∈ L₃, x * y = y * x)
    (hZ₁ : ∀ x ∈ Z, ∀ y ∈ L₁, x * y = y * x)
    (hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, x * y = y * x) → x ∈ Z)
    (hZ₃ : ∀ x ∈ L₃, (∀ y ∈ L₃, x * y = y * x) → x ∈ Z)
    {z a₁ a₂ a₃ : Y} (hz : orderOf z = 3) (hzZ : z ∈ Z) (hz₁ : z ∈ L₁) (ha₁ : a₁ ∈ L₁)
    (ha₂ : a₂ ∈ L₂) (ha₃ : a₃ ∈ L₃) (ho₁ : orderOf a₁ = 3) (ho₂ : orderOf a₂ = 3)
    (ho₃ : orderOf a₃ = 3) (hn₁ : a₁ ∉ Subgroup.zpowers z) (hn₂ : a₂ ∉ Z) (hn₃ : a₃ ∉ Z) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  have hzL : Subgroup.zpowers z ≤ L₁ := (Subgroup.zpowers_le).mpr hz₁
  have hZz : Subgroup.zpowers z ≤ Z := (Subgroup.zpowers_le).mpr hzZ
  have hA₁ : Subgroup.zpowers a₁ ≤ L₁ := (Subgroup.zpowers_le).mpr ha₁
  have hA₂ : Subgroup.zpowers a₂ ≤ L₂ := (Subgroup.zpowers_le).mpr ha₂
  have hA₃ : Subgroup.zpowers a₃ ≤ L₃ := (Subgroup.zpowers_le).mpr ha₃
  let φ₁ : ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers a₁) →* Y :=
    MonoidHom.noncommCoprod (Subgroup.zpowers z).subtype (Subgroup.zpowers a₁).subtype
      fun u v => hZ₁ u (hZz u.2) v (hA₁ v.2)
  have hφ₁L : ∀ p, φ₁ p ∈ L₁ := fun p => L₁.mul_mem (hzL p.1.2) (hA₁ p.2.2)
  let φ₂ : (↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers a₁)) × ↥(Subgroup.zpowers a₂) →* Y :=
    MonoidHom.noncommCoprod φ₁ (Subgroup.zpowers a₂).subtype
      fun p v => h12 _ (hφ₁L p) v (hA₂ v.2)
  have hφ₂c : ∀ p, ∀ y ∈ L₃, φ₂ p * y = y * φ₂ p := by
    intro p y hy
    change φ₁ p.1 * (p.2 : Y) * y = y * (φ₁ p.1 * (p.2 : Y))
    rw [mul_assoc, h23 _ (hA₂ p.2.2) y hy, ← mul_assoc, h13 _ (hφ₁L p.1) y hy, mul_assoc]
  let φ₃ : ((↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers a₁)) × ↥(Subgroup.zpowers a₂)) ×
      ↥(Subgroup.zpowers a₃) →* Y :=
    MonoidHom.noncommCoprod φ₂ (Subgroup.zpowers a₃).subtype
      fun p v => hφ₂c p v (hA₃ v.2)
  have hinj : Function.Injective φ₃ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨⟨u, v⟩, w⟩, c⟩ h
    change ((u : Y) * v * w) * c = 1 at h
    have hc : (c : Y) = ((u : Y) * v * w)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hc1 : (c : Y) = 1 := by
      refine eq_one_of_mem_zpowers_of_not_mem ho₃ hn₃ c.2 (hZ₃ _ (hA₃ c.2) fun y hy => ?_)
      rw [hc]
      exact (Commute.inv_left (show Commute ((u : Y) * v * w) y from
        hφ₂c ⟨⟨u, v⟩, w⟩ y hy)).eq
    rw [hc1, mul_one] at h
    have hw : (w : Y) = ((u : Y) * v)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hw1 : (w : Y) = 1 := by
      refine eq_one_of_mem_zpowers_of_not_mem ho₂ hn₂ w.2 (hZ₂ _ (hA₂ w.2) fun y hy => ?_)
      have huv : (u : Y) * v ∈ L₁ := hφ₁L ⟨u, v⟩
      rw [hw]
      exact (Commute.inv_left (show Commute ((u : Y) * v) y from h12 _ huv y hy)).eq
    rw [hw1, mul_one] at h
    have hv : (v : Y) = (u : Y)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hv1 : (v : Y) = 1 :=
      eq_one_of_mem_zpowers_of_not_mem ho₁ hn₁ v.2 (hv ▸ (Subgroup.zpowers z).inv_mem u.2)
    rw [hv1, mul_one] at h
    have hu1 : (u : Y) = 1 := h
    have e1 : u = 1 := Subtype.ext hu1
    have e2 : v = 1 := Subtype.ext hv1
    have e3 : w = 1 := Subtype.ext hw1
    have e4 : c = 1 := Subtype.ext hc1
    rw [e1, e2, e3, e4]
    rfl
  obtain ⟨cz, pz, kz⟩ := zpowers_facts hz
  obtain ⟨c₁, p₁, k₁⟩ := zpowers_facts ho₁
  obtain ⟨c₂, p₂, k₂⟩ := zpowers_facts ho₂
  obtain ⟨c₃, p₃, k₃⟩ := zpowers_facts ho₃
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun x y => ?_) (fun x => ?_) ?_ φ₃
    hinj le_top
  · exact Prod.ext (Prod.ext (Prod.ext (cz _ _) (c₁ _ _)) (c₂ _ _)) (c₃ _ _)
  · exact Prod.ext (Prod.ext (Prod.ext (pz _) (p₁ _)) (p₂ _)) (p₃ _)
  · rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, kz, k₁, k₂, k₃]
    norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
