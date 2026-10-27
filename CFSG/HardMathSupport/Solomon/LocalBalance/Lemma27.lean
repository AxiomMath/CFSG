module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43One
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.HardMathSupport.Solomon.Proving.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Foundations.Catalog

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

@[expose] def IsSL3Eps (X : Type*) [Group X] : Prop :=
  (IsSLThree X ∨ IsSUThree X) ∧ 3 ∣ Nat.card (Subgroup.center X)

@[expose] def AutHasQ8 {K : Type*} [Group K] (F : Subgroup K) : Prop :=
  ∃ f : QuaternionGroup 2 →* autizer (⊤ : Subgroup K) F, Function.Injective f

@[expose] def TotallyFused {K : Type*} [Group K] (F : Subgroup K) : Prop :=
  ∀ f ∈ F, f ≠ 1 → ∀ f' ∈ F, f' ≠ 1 → ∃ k : K, k * f * k⁻¹ = f'

@[expose] def IsThreeNilpotent (H : Type*) [Group H] : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), Nat.Coprime 3 (Nat.card N) ∧ IsPGroup 3 (H ⧸ N)

@[expose] def Input30_2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSL3Eps X →
    (∀ F : Subgroup (X ⧸ Subgroup.center X), IsElemAbelian 3 F → Nat.card F = 3 ^ 2 →
      (AutHasQ8 F ↔ TotallyFused F) ∧
      (TotallyFused F ↔
        (¬ IsMulCommutative (F.comap (QuotientGroup.mk' (Subgroup.center X))) ∧
          ∀ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 = 1))) ∧
    ((Nat.card (X ⧸ Subgroup.center X)).factorization 3 = 2 →
      ∀ F : Sylow 3 (X ⧸ Subgroup.center X),
        IsElemAbelian 3 (F : Subgroup (X ⧸ Subgroup.center X)) ∧
          AutHasQ8 (F : Subgroup (X ⧸ Subgroup.center X))) ∧
    (∀ x : X ⧸ Subgroup.center X, orderOf x = 3 →
      (∃ P : Sylow 3 (X ⧸ Subgroup.center X), x ∈ P ∧ ∀ y ∈ P, x * y = y * x) →
        IsThreeNilpotent ↥(Subgroup.centralizer ({x} : Set (X ⧸ Subgroup.center X))))

@[expose] def Input25_3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K J A : Subgroup Y) (b : Y),
    IsQuasisimple ↥K → IsKGroup ↥K → b ∈ K → orderOf b = 3 →
    IsComponentOf J (K ⊓ Subgroup.centralizer ({b} : Set Y)) →
    ∀ hbJ : b ∈ J, IsSL3Eps (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) =
      Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)) →
    A ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 A → Nat.card A = 9 → b ∈ A →
    (∀ a ∈ A, a ≠ 1 → InducesFieldAut 3 J a) →
    J = K ∨ ∃ a ∈ A, a ≠ 1 ∧ b ∉ oPrimePOf 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))

@[expose] def Input14_5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsKGroup Y → GLAPPrimeCore 3 Y = ⊥ →
    ∀ x : Y, x ^ 3 = 1 →
      ⁅GLAPLayer 3 (Subgroup.centralizer ({x} : Set Y)),
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set Y))⁆ = ⊥

@[expose] def Input11_2Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ (X B L : Subgroup G), IsElemAbelian 3 B → B ≤ X →
      GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → GLAPComponent 3 X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.center ↥(barX 3 X (bClosure B L)) ≠ ⊥ →
      ∀ R : Sylow 3 ↥L,
        Nat.card ↥R = 27 ∧ (¬ ∀ r ∈ (R : Subgroup ↥L), ∀ s ∈ (R : Subgroup ↥L), r * s = s * r) ∧
          (∀ r ∈ (R : Subgroup ↥L), r ^ 3 = 1) ∧
          (Subgroup.center (barOf 3 L) ≤
            (R : Subgroup ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) ∧
          (∀ w ∈ (R : Subgroup ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)),
            (∀ r ∈ (R : Subgroup ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)), w * r = r * w) →
              w ∈ Subgroup.center (barOf 3 L))

@[expose] def Input11_2Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ (X B L : Subgroup G), IsElemAbelian 3 B → B ≤ X →
      GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → GLAPComponent 3 X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      ∀ b₁ ∈ B, b₁ ∉ Subgroup.normalizer (L : Set G) →
        Nonempty (barOf 3 (GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({b₁} : Set G))) ≃*
          (barOf 3 L ⧸ Subgroup.center (barOf 3 L)))

@[expose] def InputB0T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Δ : Subgroup G), IsElemAbelian 3 B →
    B ≤ Subgroup.normalizer (Δ : Set G) → Nat.Coprime 3 (Nat.card Δ) →
    CFSG.Open.IsKGroup ↥Δ → Even (Nat.card (⁅Δ, B⁆ : Subgroup G)) →
      ∃ T : Subgroup G, T ≤ Δ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
        (⁅T, B⁆ : Subgroup G) ≠ ⊥

@[expose] def IsD4Type (X : Type) [Group X] : Prop :=
  ∃ p f : ℕ, p ≠ 3 ∧ StatedClassicalModel (X ⧸ Subgroup.center X) StatedLieTag.POmegaPlus 4 p f

@[expose] def Input14_33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q : Subgroup X) (t : X),
    K ⊔ Q₁ ⊔ Subgroup.zpowers t = ⊤ → K.Normal → IsQuasisimple ↥K → IsKGroup ↥K →
    GLAPPrimeCore 3 X = ⊥ → 1 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (K : Set X)) →
    GLATwoLocalRank 3 X ≤ 4 →
    IsPGroup 3 Q₁ → (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∈ Subgroup.normalizer (Q₁ : Set X) →
    (∀ q ∈ Q₁, t * q * t⁻¹ * q ∈ (frattini ↥Q₁).map Q₁.subtype) →
    Q ≤ Q₁ → (Q.subgroupOf Q₁).Normal →
    Nat.card Q = 27 → (¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) → (∀ a ∈ Q, a ^ 3 = 1) →
    ¬ ((Subgroup.center ↥Q).map Q.subtype ≤ (Subgroup.center ↥K).map K.subtype) →
    (Subgroup.center ↥Q).map Q.subtype ≤ K →
    (∃ J : Subgroup X, IsComponentOf J (GLAPLayer 3 (K ⊓ Subgroup.centralizer
        (((Subgroup.center ↥Q).map Q.subtype : Subgroup X) : Set X))) ∧
      (Subgroup.center ↥Q).map Q.subtype ≤ J ∧
        IsSL3Eps (↥J ⧸ GLAPPrimeCore 3 ↥J) ∧
        (((Subgroup.center ↥Q).map Q.subtype).subgroupOf J).map
            (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) = Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) ∧
        (Nat.card J).factorization 3 = 3) →
    Q ≤ Subgroup.centralizer (GLAPLayer 3 (K ⊓ Subgroup.centralizer
        (((Subgroup.center ↥Q).map Q.subtype : Subgroup X) : Set X)) : Set X) →
    IsD4Type ↥K

@[expose] def InputD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsKGroup X → IsD4Type X →
    (∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ (3 ^ k) = 1 → z = 1) ∧
    ∀ x : X, x ^ 3 = 1 → x ≠ 1 → 4 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X))

variable {G : Type} [Group G] [Finite G]

abbrev Cb (b : G) : Subgroup G := Subgroup.centralizer ({b} : Set G)

abbrev P3 (X : Subgroup G) : Subgroup G := GLAPPrimeCoreOf 3 X

@[expose] def mkX (X : Subgroup G) (g : G) (hg : g ∈ X) : ↥X ⧸ GLAPPrimeCore 3 ↥X :=
  QuotientGroup.mk (⟨g, hg⟩ : ↥X)

structure Tri (B : Subgroup G) (b : G) (L₁ L₂ L₃ : Subgroup G) : Prop where
  elemB : IsElemAbelian 3 B
  mem : b ∈ B
  ne_one : b ≠ 1
  comp₁ : GLAPComponent 3 (Cb b) L₁
  comp₂ : GLAPComponent 3 (Cb b) L₂
  comp₃ : GLAPComponent 3 (Cb b) L₃
  ne₁₂ : L₁ ≠ L₂
  ne₂₃ : L₂ ≠ L₃
  ne₁₃ : L₁ ≠ L₃
  cyc : ∃ β ∈ B, L₂ = GLBConj β L₁ ∧ L₃ = GLBConj β L₂ ∧ L₁ = GLBConj β L₃

structure FusData {H : Type*} [Group H] (Q Z : Subgroup H) : Prop where
  Zle : Z ≤ Q
  Zcard : Nat.card Z = 3
  Zcenter : ∀ w : H, w ∈ Z ↔ (w ∈ Q ∧ ∀ q ∈ Q, w * q = q * w)
  exp3 : ∀ a ∈ Q, (∃ k : ℕ, a ^ (3 ^ k) = 1) → a ^ 3 = 1
  fus : ∀ a ∈ Q, a ^ 3 = 1 → a ∉ Z → ∀ a' ∈ Q, a' ^ 3 = 1 → a' ∉ Z →
    ∃ c ∈ Q, ∃ w ∈ Z, c * a * c⁻¹ = a' * w
  shift : ∀ a ∈ Q, a ^ 3 = 1 → a ∉ Z → ∀ w ∈ Z, ∃ r ∈ Q, r * a * r⁻¹ = a * w
  exists_noncentral : ∃ a ∈ Q, a ^ 3 = 1 ∧ a ∉ Z

@[expose] def ZR (R : Subgroup G) : Subgroup G := (Subgroup.center ↥R).map R.subtype

@[expose] def SylInfo (b : G) (L : Subgroup G) : Prop :=
  ∀ R : Subgroup G, R ≤ L → IsPGroup 3 R → Nat.card R = 3 ^ (Nat.card L).factorization 3 →
    Nat.card R = 27 ∧ (¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) ∧ (∀ a ∈ R, a ^ 3 = 1) ∧
      ZR R = Subgroup.zpowers b

structure RData (B : Subgroup G) (b : G) (L₁ L₂ L₃ : Subgroup G) : Prop where
  tri : Tri B b L₁ L₂ L₃
  fus₁ : FusData (barX 3 (Cb b) L₁) (barX 3 (Cb b) (Subgroup.zpowers b))
  fus₂ : FusData (barX 3 (Cb b) L₂) (barX 3 (Cb b) (Subgroup.zpowers b))
  fus₃ : FusData (barX 3 (Cb b) L₃) (barX 3 (Cb b) (Subgroup.zpowers b))
  eps₁ : IsSL3Eps (barOf 3 L₁)
  eps₂ : IsSL3Eps (barOf 3 L₂)
  eps₃ : IsSL3Eps (barOf 3 L₃)
  syl₁ : SylInfo b L₁
  syl₂ : SylInfo b L₂
  syl₃ : SylInfo b L₃

@[expose] def Y2 (b : G) (Li Lj : Subgroup G) : Prop :=
  ∀ u ∈ Li, ∀ v ∈ Lj, u * v = v * u → u ^ 3 = 1 → v ^ 3 = 1 → u ∉ Subgroup.zpowers b →
    v ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb (u * v))

structure SylData (B : Subgroup G) (b : G) (L₁ L₂ L₃ R R₁ R₂ R₃ : Subgroup G) : Prop where
  hRK : R ≤ L₁ ⊔ L₂ ⊔ L₃
  hRp : IsPGroup 3 R
  hRs : Nat.card R = 3 ^ (Nat.card ↥(L₁ ⊔ L₂ ⊔ L₃)).factorization 3
  hbR : b ∈ R
  hRB : ∀ g ∈ B, ∀ r ∈ R, g * r * g⁻¹ ∈ R
  h1 : R₁ = R ⊓ L₁
  h2 : R₂ = R ⊓ L₂
  h3 : R₃ = R ⊓ L₃
  hprod : R = R₁ ⊔ R₂ ⊔ R₃
  c12 : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a
  c23 : ∀ a ∈ R₂, ∀ c ∈ R₃, a * c = c * a
  c13 : ∀ a ∈ R₁, ∀ c ∈ R₃, a * c = c * a
  s1 : Nat.card R₁ = 3 ^ (Nat.card L₁).factorization 3
  s2 : Nat.card R₂ = 3 ^ (Nat.card L₂).factorization 3
  s3 : Nat.card R₃ = 3 ^ (Nat.card L₃).factorization 3

section Generic1

open scoped Pointwise in
theorem g_conj_of_cong {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (N : Subgroup H)
    [N.Normal] (hcop : Nat.Coprime p (Nat.card N)) {u v : H} (hu : ∃ k : ℕ, u ^ (p ^ k) = 1)
    (hv : ∃ k : ℕ, v ^ (p ^ k) = 1) (h : u * v⁻¹ ∈ N) : ∃ c ∈ N, c * u * c⁻¹ = v := by
  have : Fact p.Prime := ⟨hp⟩
  have hNint : ∀ w : H, (∃ k : ℕ, w ^ (p ^ k) = 1) → w ∈ N → w = 1 := by
    intro w ⟨k, hk⟩ hw
    have h1 : orderOf (⟨w, hw⟩ : ↥N) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
    have h2 : orderOf (⟨w, hw⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h3 : orderOf (⟨w, hw⟩ : ↥N) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2
    have := orderOf_eq_one_iff.1 h3
    simpa using congrArg Subtype.val this
  set M : Subgroup H := Subgroup.zpowers v ⊔ N with hM
  have hNM : N ≤ M := le_sup_right
  have hvM : v ∈ M := Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
  have huM : u ∈ M := by
    have : u = (u * v⁻¹) * v := by group
    rw [this]; exact M.mul_mem (hNM h) hvM
  have hzp : ∀ w ∈ Subgroup.zpowers v, ∃ k : ℕ, w ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hv
    intro w hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ⟨k, by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]⟩
  have hint : N.subgroupOf (Subgroup.zpowers v) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have hw' : (w : H) ∈ N := hw
    have := hNint w (hzp w w.2) hw'
    exact Subtype.ext this
  have hrel : N.relIndex M = Nat.card (Subgroup.zpowers v) := by
    have h1 := Subgroup.relIndex_sup_right (H := Subgroup.zpowers v) (K := N)
    rw [← hM] at h1
    rw [h1]
    show (N.subgroupOf (Subgroup.zpowers v)).index = _
    rw [hint, Subgroup.index_bot]
  have hcardM : Nat.card M = Nat.card N * Nat.card (Subgroup.zpowers v) := by
    rw [← hrel]
    have h1 := Subgroup.card_mul_index (N.subgroupOf M)
    have h2 : Nat.card (N.subgroupOf M) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    rw [h2] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card (Subgroup.zpowers v) = p ^ a := by
    obtain ⟨k, hk⟩ := hv
    have : orderOf v ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 this
    exact ⟨a, by rw [Nat.card_zpowers, ha]⟩
  have hzM : Subgroup.zpowers v ≤ M := le_sup_left
  have huzM : Subgroup.zpowers u ≤ M := (Subgroup.zpowers_le).2 huM
  set P : Subgroup ↥M := (Subgroup.zpowers v).subgroupOf M with hP
  have hPcard : Nat.card P = p ^ a := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzM).toEquiv]; exact ha
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hfact : (Nat.card M).factorization p = a := by
    have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
    rw [hcardM, ha, Nat.factorization_mul hN0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop), zero_add]
  have hScard : Nat.card S = p ^ a := by rw [Sylow.card_eq_multiplicity, hfact]
  have hSP : (S : Subgroup ↥M) = P :=
    (Subgroup.eq_of_le_of_card_ge hPS (by rw [hScard, hPcard])).symm
  set uM : ↥M := ⟨u, huM⟩ with huMdef
  set Q : Subgroup ↥M := Subgroup.zpowers uM with hQ
  have hQp : IsPGroup p Q := by
    obtain ⟨k, hk⟩ := hu
    have hk' : uM ^ (p ^ k) = 1 := Subtype.ext (by simpa [uM] using hk)
    intro g
    refine ⟨k, ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    have : (g : ↥M) = uM ^ j := hj.symm
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨S', hQS'⟩ := hQp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M S' S
  have hmemS' : uM ∈ (S' : Subgroup ↥M) := hQS' (Subgroup.mem_zpowers uM)
  have hconj : g * uM * g⁻¹ ∈ (S : Subgroup ↥M) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨uM, hmemS', by simp [MulAut.conj_apply]⟩
  rw [hSP] at hconj
  have hconj' : (g : H) * u * (g : H)⁻¹ ∈ Subgroup.zpowers v := by
    have := (Subgroup.mem_subgroupOf).1 hconj
    simpa [uM] using this
  have hgM : (g : H) ∈ M := g.2
  have hgmem : (g : H) ∈ ((Subgroup.zpowers v : Subgroup H) : Set H) * (N : Set H) := by
    rw [← Subgroup.mul_normal]; exact hgM
  obtain ⟨w, hw, n, hn, hwn⟩ := hgmem
  have hx : n * u * n⁻¹ ∈ Subgroup.zpowers v := by
    have e : n * u * n⁻¹ = w⁻¹ * ((g : H) * u * (g : H)⁻¹) * w := by
      rw [← hwn]; group
    rw [e]
    exact (Subgroup.zpowers v).mul_mem ((Subgroup.zpowers v).mul_mem
      ((Subgroup.zpowers v).inv_mem hw) hconj') hw
  have hxN : n * u * n⁻¹ * v⁻¹ ∈ N := by
    have e : n * u * n⁻¹ * v⁻¹ = (n * (u * v⁻¹) * n⁻¹) * (n * (v * n⁻¹ * v⁻¹)) := by group
    rw [e]
    refine N.mul_mem (Subgroup.Normal.conj_mem inferInstance _ h n) (N.mul_mem hn ?_)
    have := Subgroup.Normal.conj_mem (inferInstance : N.Normal) n⁻¹ (N.inv_mem hn) v
    simpa [mul_assoc] using this
  have h1 : n * u * n⁻¹ * v⁻¹ = 1 :=
    hNint _ (hzp _ ((Subgroup.zpowers v).mul_mem hx ((Subgroup.zpowers v).inv_mem
      (Subgroup.mem_zpowers v)))) hxN
  refine ⟨n, hn, ?_⟩
  have := mul_inv_eq_one.1 h1
  exact this


theorem g_lift_centralizer {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (N : Subgroup H) [N.Normal] (hcop : Nat.Coprime p (Nat.card N)) {y : H}
    (hy : ∃ k : ℕ, y ^ (p ^ k) = 1) {g : H} (hg : g * y * g⁻¹ * y⁻¹ ∈ N) :
    ∃ n ∈ N, (g * n) * y = y * (g * n) := by
  have hu : ∃ k : ℕ, (g * y * g⁻¹) ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, by rw [conj_pow, hk]; group⟩
  obtain ⟨c, hc, hcy⟩ := g_conj_of_cong hp N hcop hu hy (by simpa [mul_assoc] using hg)
  refine ⟨g⁻¹ * c * g, ?_, ?_⟩
  · have := Subgroup.Normal.conj_mem (inferInstance : N.Normal) c hc g⁻¹
    simpa [mul_assoc] using this
  · have e : g * (g⁻¹ * c * g) = c * g := by group
    rw [e]
    have h2 : c * (g * y * g⁻¹) * c⁻¹ = y := by simpa [mul_assoc] using hcy
    calc c * g * y = (c * (g * y * g⁻¹) * c⁻¹) * (c * g) := by group
      _ = y * (c * g) := by rw [h2]

theorem g_mem_of_pow {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {M L : Subgroup H}
    (hLM : L ≤ M) (hn : (L.subgroupOf M).Normal) (hcop : Nat.Coprime p (L.relIndex M)) {g : H}
    (hg : g ∈ M) {k : ℕ} (hk : g ^ (p ^ k) = 1) : g ∈ L := by
  set q : ↥M ⧸ L.subgroupOf M := QuotientGroup.mk (⟨g, hg⟩ : ↥M) with hq
  have h1 : orderOf q ∣ p ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hq, ← QuotientGroup.mk_pow]
    have : (⟨g, hg⟩ : ↥M) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this]; rfl
  have h2 : orderOf q ∣ Nat.card (↥M ⧸ L.subgroupOf M) := orderOf_dvd_natCard _
  have h3 : Nat.card (↥M ⧸ L.subgroupOf M) = L.relIndex M := by
    rw [← Subgroup.index_eq_card]; rfl
  rw [h3] at h2
  have h4 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2
  have h5 : q = 1 := orderOf_eq_one_iff.1 h4
  have h6 : (⟨g, hg⟩ : ↥M) ∈ L.subgroupOf M := (QuotientGroup.eq_one_iff _).1 h5
  exact h6

end Generic1

section Generic2

theorem g2_crit_group {A : Type*} [Group A] [Finite A] {N : Subgroup A} (hN : N.Normal)
    (h : ∀ g ∈ N, ∃ k : ℕ, g ^ (3 ^ k) ∈ GLAPPrimeCore 3 A) : N ≤ oPrimeP 3 A := by
  have hN' : (N.map (QuotientGroup.mk' (GLAPPrimeCore 3 A))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 3 (N.map (QuotientGroup.mk' (GLAPPrimeCore 3 A))) := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨k, hk⟩ := h g hg
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hle : N.map (QuotientGroup.mk' (GLAPPrimeCore 3 A)) ≤ CFSG.pCore 3 (A ⧸ GLAPPrimeCore 3 A) :=
    le_sSup ⟨hN', hp⟩
  intro g hg
  exact hle ⟨g, hg, rfl⟩

theorem g2_mem_oPrimeP {A : Type*} [Group A] [Finite A] {g : A} (hg : g ∈ oPrimeP 3 A) :
    ∃ k : ℕ, g ^ (3 ^ k) ∈ GLAPPrimeCore 3 A := by
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore 3 A) g) ∈ CFSG.pCore 3 (A ⧸ GLAPPrimeCore 3 A) := hg
  have h2 := CFSG.pCore_isPGroup (p := 3) (G := A ⧸ GLAPPrimeCore 3 A)
  obtain ⟨k, hk⟩ := h2 ⟨_, h1⟩
  refine ⟨k, (QuotientGroup.eq_one_iff _).1 ?_⟩
  have := congrArg Subtype.val hk
  simpa [map_pow] using this

theorem g2_oPrimeP_map_iso {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y) :
    (oPrimeP 3 X).map e.toMonoidHom = oPrimeP 3 Y := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  let Φ : (X ⧸ GLAPPrimeCore 3 X) ≃* (Y ⧸ GLAPPrimeCore 3 Y) :=
    QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso 3 e)
  have hpc := CFSG.pCore_map_iso 3 Φ
  ext y
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 X) x ∈ CFSG.pCore 3 (X ⧸ GLAPPrimeCore 3 X) := hx
    have h2 : Φ (QuotientGroup.mk' (GLAPPrimeCore 3 X) x) ∈ CFSG.pCore 3 (Y ⧸ GLAPPrimeCore 3 Y) := by
      rw [← hpc]; exact ⟨_, h1, rfl⟩
    have h3 : Φ (QuotientGroup.mk' (GLAPPrimeCore 3 X) x) =
        QuotientGroup.mk' (GLAPPrimeCore 3 Y) (e x) :=
      QuotientGroup.congr_mk _ _ e (glaPPrimeCore_map_iso 3 e) x
    show QuotientGroup.mk' (GLAPPrimeCore 3 Y) (e x) ∈ CFSG.pCore 3 (Y ⧸ GLAPPrimeCore 3 Y)
    rw [← h3]; exact h2
  · intro hy
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 Y) y ∈ CFSG.pCore 3 (Y ⧸ GLAPPrimeCore 3 Y) := hy
    rw [← hpc] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 X) z
    have h3 : Φ (QuotientGroup.mk' (GLAPPrimeCore 3 X) x) =
        QuotientGroup.mk' (GLAPPrimeCore 3 Y) (e x) :=
      QuotientGroup.congr_mk _ _ e (glaPPrimeCore_map_iso 3 e) x
    have h4 : QuotientGroup.mk' (GLAPPrimeCore 3 Y) (e x) = QuotientGroup.mk' (GLAPPrimeCore 3 Y) y :=
      h3.symm.trans hzy
    have h5 : (e x)⁻¹ * y ∈ GLAPPrimeCore 3 Y := (QuotientGroup.eq).1 h4
    refine ⟨x * (e.symm ((e x)⁻¹ * y)), ?_, ?_⟩
    ·
      have hw : e.symm ((e x)⁻¹ * y) ∈ GLAPPrimeCore 3 X := by
        have := glaPPrimeCore_map_iso 3 e.symm
        rw [← this]; exact ⟨_, h5, rfl⟩
      have hwO : e.symm ((e x)⁻¹ * y) ∈ oPrimeP 3 X := by
        have h1' : QuotientGroup.mk' (GLAPPrimeCore 3 X) (e.symm ((e x)⁻¹ * y)) = 1 :=
          (QuotientGroup.eq_one_iff _).2 hw
        show QuotientGroup.mk' (GLAPPrimeCore 3 X) _ ∈ CFSG.pCore 3 (X ⧸ GLAPPrimeCore 3 X)
        rw [h1']; exact (CFSG.pCore 3 (X ⧸ GLAPPrimeCore 3 X)).one_mem
      have hx : x ∈ oPrimeP 3 X := hz
      exact (oPrimeP 3 X).mul_mem hx hwO
    · simp

end Generic2

section Generic2

theorem oPrimePOf_gLBConj (g : G) (X : Subgroup G) :
    oPrimePOf 3 (GLBConj g X) = GLBConj g (oPrimePOf 3 X) := by
  have hp := g2_oPrimeP_map_iso (conjEquiv g X)
  have hf : (GLBConj g X).subtype.comp (conjEquiv g X).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp X.subtype := by
    ext t
    simp
  calc oPrimePOf 3 (GLBConj g X)
      = ((oPrimeP 3 ↥X).map (conjEquiv g X).toMonoidHom).map (GLBConj g X).subtype := by
        rw [hp]; rfl
    _ = (oPrimeP 3 ↥X).map ((GLBConj g X).subtype.comp (conjEquiv g X).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (oPrimeP 3 ↥X).map ((MulAut.conj g⁻¹).toMonoidHom.comp X.subtype) := by rw [hf]
    _ = ((oPrimeP 3 ↥X).map X.subtype).map (MulAut.conj g⁻¹).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
    _ = GLBConj g (oPrimePOf 3 X) := rfl

theorem g2_oPrimePOf_le (X : Subgroup G) : oPrimePOf 3 X ≤ X := Subgroup.map_subtype_le _

theorem g2_oPrimePOf_normal (X : Subgroup G) : ((oPrimePOf 3 X).subgroupOf X).Normal := by
  have : (oPrimePOf 3 X).subgroupOf X = oPrimeP 3 ↥X := by
    unfold oPrimePOf
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [this]
  infer_instance

theorem g2_mem_oPrimePOf {X : Subgroup G} {g : G} (hg : g ∈ oPrimePOf 3 X) :
    ∃ k : ℕ, g ^ (3 ^ k) ∈ P3 X := by
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨k, hk⟩ := g2_mem_oPrimeP hg'
  exact ⟨k, ⟨_, hk, by simp⟩⟩

theorem g2_crit {X N : Subgroup G} (hNX : N ≤ X) (hn : (N.subgroupOf X).Normal)
    (h : ∀ g ∈ N, ∃ k : ℕ, g ^ (3 ^ k) ∈ P3 X) : N ≤ oPrimePOf 3 X := by
  have h1 : N.subgroupOf X ≤ oPrimeP 3 ↥X := by
    refine g2_crit_group hn ?_
    intro g hg
    obtain ⟨k, hk⟩ := h (g : G) hg
    obtain ⟨g', hg', hgg⟩ := hk
    refine ⟨k, ?_⟩
    have : g' = g ^ (3 ^ k) := Subtype.ext (by simpa using hgg)
    rw [← this]; exact hg'
  intro x hx
  exact ⟨⟨x, hNX hx⟩, h1 ((Subgroup.mem_subgroupOf).2 hx), rfl⟩

theorem g2_normalizer_oPrimePOf {M H : Subgroup G} (hMH : M ≤ Subgroup.normalizer (H : Set G)) :
    M ≤ Subgroup.normalizer (oPrimePOf 3 H : Set G) := by
  intro m hm
  have h1 := hMH hm
  rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
  rw [← oPrimePOf_gLBConj, h1]

theorem o_le_of_subnormal {A₀ A : Subgroup G} (h : IsSubnormal A₀ A) :
    oPrimePOf 3 A₀ ≤ oPrimePOf 3 A := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hHM hn hsub ih =>
    refine le_trans ?_ ih
    have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
    refine g2_crit ((g2_oPrimePOf_le H).trans hHM) ?_ ?_
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((g2_oPrimePOf_le H).trans hHM)).2 (g2_normalizer_oPrimePOf hMH)
    · intro g hg
      obtain ⟨k, hk⟩ := g2_mem_oPrimePOf hg
      exact ⟨k, glaPPrimeCoreOf_le_of_isSubnormal 3 (IsSubnormal.step hHM hn (IsSubnormal.refl M)) hk⟩

theorem o_inf_le_of_subnormal {A₀ A : Subgroup G} (h : IsSubnormal A₀ A) :
    oPrimePOf 3 A ⊓ A₀ ≤ oPrimePOf 3 A₀ := by
  induction h with
  | refl => exact inf_le_left
  | @step H M K hHM hn hsub ih =>
    intro g hg
    have hg1 : g ∈ oPrimePOf 3 M := ih ⟨hg.1, hHM hg.2⟩
    have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
    have hHMsub : IsSubnormal H M := IsSubnormal.step hHM hn (IsSubnormal.refl M)
    refine (g2_crit (X := H) (N := oPrimePOf 3 M ⊓ H) inf_le_right ?_ ?_) ⟨hg1, hg.2⟩
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro w hw
      have hwM : w ∈ M := hHM hw
      have h1 : w ∈ Subgroup.normalizer (oPrimePOf 3 M : Set G) := by
        have := (Subgroup.normal_subgroupOf_iff_le_normalizer (g2_oPrimePOf_le M)).1
          (g2_oPrimePOf_normal M)
        exact this hwM
      have h2 : w ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hw
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro z
      simp only [Subgroup.mem_inf]
      rw [h1 z, h2 z]
    · intro g' hg'
      obtain ⟨k, hk⟩ := g2_mem_oPrimePOf hg'.1
      refine ⟨k, ?_⟩
      have : g' ^ (3 ^ k) ∈ H := H.pow_mem hg'.2 _
      have h3 := glaPPrimeCoreOf_inf_eq_of_isSubnormal (p := 3) Nat.prime_three hHMsub
      have h4 : g' ^ (3 ^ k) ∈ H ⊓ GLAPPrimeCoreOf 3 M := ⟨this, hk⟩
      rw [h3] at h4
      exact h4

theorem o_inf_centralizer_le {H : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx : ∃ k : ℕ, x ^ (3 ^ k) = 1) :
    oPrimePOf 3 H ⊓ Subgroup.centralizer ({x} : Set G) ≤
      oPrimePOf 3 (H ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have _ := hxH
  have _ := hx
  refine g2_crit (X := H ⊓ Subgroup.centralizer ({x} : Set G))
    (N := oPrimePOf 3 H ⊓ Subgroup.centralizer ({x} : Set G))
    (inf_le_inf_right _ (g2_oPrimePOf_le H)) ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ (g2_oPrimePOf_le H))]
    intro w hw
    have h1 : w ∈ Subgroup.normalizer (oPrimePOf 3 H : Set G) := by
      have := (Subgroup.normal_subgroupOf_iff_le_normalizer (g2_oPrimePOf_le H)).1
        (g2_oPrimePOf_normal H)
      exact this hw.1
    have h2 : w ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
      Subgroup.le_normalizer hw.2
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro z
    simp only [Subgroup.mem_inf]
    rw [h1 z, h2 z]
  · intro g hg
    obtain ⟨k, hk⟩ := g2_mem_oPrimePOf hg.1
    refine ⟨k, gLAPPrimeCoreOf_inf_le Nat.prime_three H _ ⟨hk, ?_⟩⟩
    exact (Subgroup.centralizer ({x} : Set G)).pow_mem hg.2 _

theorem o_map_hom_le {A A' : Type*} [Group A] [Group A'] [Finite A] (f : A →* A')
    (hf : Function.Surjective f) : (oPrimeP 3 A).map f ≤ oPrimeP 3 A' := by
  have : Finite A' := Finite.of_surjective f hf
  have hO : (GLAPPrimeCore 3 A).map f ≤ GLAPPrimeCore 3 A' := by
    refine le_sSup ⟨Subgroup.Normal.map inferInstance f hf, ?_⟩
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f)
      (coprime_card_gLAPPrimeCore_aux 3 A)
  refine g2_crit_group (Subgroup.Normal.map inferInstance f hf) ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨k, hk⟩ := g2_mem_oPrimeP hg
  exact ⟨k, by rw [← map_pow]; exact hO ⟨_, hk, rfl⟩⟩

end Generic2

section Comp

theorem q_p3_trivial {X : Subgroup G} {w : G} (hw : w ∈ P3 X) {k : ℕ} (hk : w ^ (3 ^ k) = 1) :
    w = 1 := by
  have hnd := not_dvd_card_glaPPrimeCoreOf Nat.prime_three X
  have h1 : orderOf (⟨w, hw⟩ : ↥(P3 X)) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  have h2 : orderOf (⟨w, hw⟩ : ↥(P3 X)) ∣ Nat.card (P3 X) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (P3 X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have := orderOf_eq_one_iff.1 h3
  simpa using congrArg Subtype.val this

theorem q_p3_le_normalizer {X L : Subgroup G} (hL : GLAPComponent 3 X L) :
    P3 X ≤ Subgroup.normalizer (L : Set G) := by
  have hn := glaPComponent_normal_preimBarX hL
  have h1 : preimBarX 3 X L ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX 3 hL.1)).1 hn
  refine le_trans ?_ h1
  rintro y ⟨y', hy', rfl⟩
  refine ⟨y', ?_, rfl⟩
  have : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y' = 1 := (QuotientGroup.eq_one_iff y').2 hy'
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) y' ∈ barX 3 X L
  rw [this]; exact (barX 3 X L).one_mem

theorem q_le_normalizer_of_ne {X L L' : Subgroup G} (hL : GLAPComponent 3 X L)
    (hL' : GLAPComponent 3 X L') (hne : L ≠ L') : L ≤ Subgroup.normalizer (L' : Set G) := by
  have hcomm := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hL hL' hne
  intro l hl
  have hlX : l ∈ X := hL.1 hl
  have hl'inv : l⁻¹ ∈ Subgroup.normalizer (L' : Set G) → l ∈ Subgroup.normalizer (L' : Set G) := by
    intro h; simpa using Subgroup.inv_mem _ h
  refine hl'inv ?_
  rw [mem_normalizer_iff_gLBConj_eq]
  have hX : GLBConj l⁻¹ X = X :=
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (X.inv_mem hlX))
  have hL'' : GLAPComponent 3 X (GLBConj l⁻¹ L') := by
    have := glaPComponent_gLBConj l⁻¹ hL'
    rwa [hX] at this
  have hcomm' : ⁅L', L⁆ ≤ GLAPPrimeCoreOf 3 X := by
    rw [Subgroup.commutator_comm]; exact hcomm
  refine glaPComponent_unique hL'' hL' ?_
  apply le_antisymm
  · refine barX_le_of_forall hL'.1 (fun k hk => ?_)
    have hk' : l⁻¹ * k * l ∈ L' := by simpa using mem_gLBConj.1 hk
    refine ⟨l⁻¹ * k * l, hk', hcomm' ?_⟩
    have := Subgroup.commutator_mem_commutator ((L'.inv_mem hk')) hl
    simpa [commutatorElement_def, mul_assoc] using this
  · refine barX_le_of_forall hL''.1 (fun k hk => ?_)
    refine ⟨l * k * l⁻¹, ?_, ?_⟩
    · rw [mem_gLBConj]; simpa [mul_assoc] using hk
    · have := hcomm (Subgroup.commutator_mem_commutator hl (L'.inv_mem hk))
      simpa [commutatorElement_def, mul_assoc] using this

theorem q_mem_of_bar {X L : Subgroup G} (hL : GLAPComponent 3 X L) {g : G} (hgX : g ∈ X) {k : ℕ}
    (hk : g ^ (3 ^ k) = 1) (h : mkX X g hgX ∈ barX 3 X L) : g ∈ L := by
  set M := preimBarX 3 X L with hMdef
  have hg : g ∈ M := ⟨⟨g, hgX⟩, h, rfl⟩
  obtain ⟨l, hl, hn⟩ := exists_mul_of_mem_preimBarX 3 hg
  have hLM : L ≤ M := le_preimBarX 3 hL.1
  have hnorm : (L.subgroupOf M).Normal := glaPComponent_normal_preimBarX hL
  have hlM : l ∈ M := hLM hl
  have hnM : l⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hlM) hg
  set q : ↥M ⧸ L.subgroupOf M := QuotientGroup.mk (⟨g, hg⟩ : ↥M) with hq
  have hq3 : q ^ (3 ^ k) = 1 := by
    rw [hq, ← QuotientGroup.mk_pow]
    have : (⟨g, hg⟩ : ↥M) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this]; rfl
  have hqn : q = QuotientGroup.mk (⟨l⁻¹ * g, hnM⟩ : ↥M) := by
    rw [hq]
    apply (QuotientGroup.eq).2
    show (⟨g, hg⟩ : ↥M)⁻¹ * ⟨l⁻¹ * g, hnM⟩ ∈ L.subgroupOf M
    rw [Subgroup.mem_subgroupOf]
    have h2 : (g⁻¹ * (l⁻¹ * g) : G) = (g⁻¹ * l⁻¹ * g) := by group
    show g⁻¹ * (l⁻¹ * g) ∈ L
    have hgn : g ∈ Subgroup.normalizer (L : Set G) := by
      have : l⁻¹ * g ∈ Subgroup.normalizer (L : Set G) := by
        have hn' : l⁻¹ * g ∈ P3 X := hn
        exact q_p3_le_normalizer hL hn'
      have := Subgroup.mul_mem _ (Subgroup.le_normalizer hl) this
      simpa using this
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgn) l⁻¹).1 (L.inv_mem hl)
    simpa [mul_assoc] using this
  have hnP : l⁻¹ * g ∈ P3 X := hn
  have hnd := not_dvd_card_glaPPrimeCoreOf Nat.prime_three X
  set c := Nat.card (P3 X) with hc
  have hqc : q ^ c = 1 := by
    rw [hqn, ← QuotientGroup.mk_pow]
    have : (⟨l⁻¹ * g, hnM⟩ : ↥M) ^ c = 1 := by
      have h1 : (⟨l⁻¹ * g, hnP⟩ : ↥(P3 X)) ^ c = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      exact Subtype.ext (by simpa using h2)
    rw [this]; rfl
  have hcop : Nat.Coprime (3 ^ k) c :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd)
  have h4 : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_of_pow_eq_one hqc)
  have h5 : q = 1 := orderOf_eq_one_iff.1 h4
  have h6 : (⟨g, hg⟩ : ↥M) ∈ L.subgroupOf M := (QuotientGroup.eq_one_iff _).1 h5
  exact h6

theorem q_mem_zpowers_of_bar {X : Subgroup G} {b g : G} (hbX : b ∈ X) {kb : ℕ}
    (hb : b ^ (3 ^ kb) = 1) (hgX : g ∈ X) {k : ℕ} (hk : g ^ (3 ^ k) = 1) (hc : g * b = b * g)
    (h : mkX X g hgX ∈ barX 3 X (Subgroup.zpowers b)) : g ∈ Subgroup.zpowers b := by
  obtain ⟨s, hs, hsg⟩ := h
  have hs' : (s : G) ∈ Subgroup.zpowers b := (Subgroup.mem_subgroupOf).1 hs
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hs'
  have h1 : (s⁻¹ * ⟨g, hgX⟩ : ↥X) ∈ GLAPPrimeCore 3 ↥X := by
    refine (QuotientGroup.eq).1 ?_
    exact hsg
  have h2 : (s : G)⁻¹ * g ∈ P3 X := ⟨_, h1, rfl⟩
  have hsb : (s : G) = b ^ j := hj.symm
  have hcomm : Commute (s : G)⁻¹ g := by
    rw [hsb]
    exact (Commute.zpow_left (show Commute b g from hc.symm) j).inv_left
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((s : G)⁻¹ * g) ^ (3 ^ m) = 1 := by
    have hs3 : ∃ m, (s : G) ^ (3 ^ m) = 1 := by
      rw [hsb]
      exact ⟨kb, by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]⟩
    obtain ⟨m1, hm1⟩ := hs3
    refine ⟨max m1 k, ?_⟩
    rw [hcomm.mul_pow]
    have e1 : ((s : G)⁻¹) ^ (3 ^ max m1 k) = 1 := by
      have : (s : G) ^ (3 ^ max m1 k) = 1 := by
        have : 3 ^ max m1 k = 3 ^ m1 * 3 ^ (max m1 k - m1) := by
          rw [← pow_add]; congr 1; omega
        rw [this, pow_mul, hm1, one_pow]
      rw [inv_pow, this, inv_one]
    have e2 : g ^ (3 ^ max m1 k) = 1 := by
      have : 3 ^ max m1 k = 3 ^ k * 3 ^ (max m1 k - k) := by
        rw [← pow_add]; congr 1; omega
      rw [this, pow_mul, hk, one_pow]
    rw [e1, e2, one_mul]
  have h3 : (s : G)⁻¹ * g = 1 := q_p3_trivial h2 hm
  have : g = (s : G) := by
    have := congrArg ((s : G) * ·) h3
    simpa using this
  rw [this]; exact hs'

end Comp

section TC

theorem tc_one {H : Type*} [Group H] {Q Z : Subgroup H} (h : FusData Q Z) {a a' : H} (ha : a ∈ Q)
    (ha' : a' ∈ Q) (ha3 : a ^ 3 = 1) (ha'3 : a' ^ 3 = 1) (hna : a ∉ Z) (hna' : a' ∉ Z) :
    ∃ c ∈ Q, c * a * c⁻¹ = a' := by
  obtain ⟨c₁, hc₁, w, hw, hcw⟩ := h.fus a ha ha3 hna a' ha' ha'3 hna'
  have hwQ : w ∈ Q := h.Zle hw
  have hwc : ∀ q ∈ Q, w * q = q * w := ((h.Zcenter w).1 hw).2
  have hw3 : w ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Z) (x := (⟨w, hw⟩ : ↥Z))
    rw [h.Zcard] at this
    exact congrArg Subtype.val this
  have h1 : (a' * w) ^ 3 = 1 := by
    have hcomm : Commute a' w := (hwc a' ha').symm
    rw [hcomm.mul_pow, ha'3, hw3, one_mul]
  have hnot : a' * w ∉ Z := fun hmem => hna' (by
    have := Z.mul_mem hmem (Z.inv_mem hw)
    simpa using this)
  obtain ⟨r, hrQ, hr⟩ := h.shift (a' * w) (Q.mul_mem ha' hwQ) h1 hnot w⁻¹ (Z.inv_mem hw)
  refine ⟨r * c₁, Q.mul_mem hrQ hc₁, ?_⟩
  calc r * c₁ * a * (r * c₁)⁻¹ = r * (c₁ * a * c₁⁻¹) * r⁻¹ := by group
    _ = r * (a' * w) * r⁻¹ := by rw [hcw]
    _ = a' * w * w⁻¹ := hr
    _ = a' := by group

theorem tc_two {H : Type*} [Group H] {Q₁ Q₂ Z : Subgroup H} (h₁ : FusData Q₁ Z)
    (h₂ : FusData Q₂ Z) (hc : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) {u u' v v' : H} (hu : u ∈ Q₁)
    (hu' : u' ∈ Q₁) (hv : v ∈ Q₂) (hv' : v' ∈ Q₂) (hu3 : u ^ 3 = 1) (hu'3 : u' ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (hv'3 : v' ^ 3 = 1) (hnu : u ∉ Z) (hnu' : u' ∉ Z) (hnv : v ∉ Z)
    (hnv' : v' ∉ Z) : ∃ c ∈ Q₁ ⊔ Q₂, c * (u * v) * c⁻¹ = u' * v' := by
  obtain ⟨c₁, hc₁, h₁e⟩ := tc_one h₁ hu hu' hu3 hu'3 hnu hnu'
  obtain ⟨c₂, hc₂, h₂e⟩ := tc_one h₂ hv hv' hv3 hv'3 hnv hnv'
  refine ⟨c₁ * c₂, Subgroup.mul_mem_sup hc₁ hc₂, ?_⟩
  have hc2u : c₂ * u = u * c₂ := (hc u hu c₂ hc₂).symm
  have hc1v' : c₁ * v' = v' * c₁ := hc c₁ hc₁ v' hv'
  calc c₁ * c₂ * (u * v) * (c₁ * c₂)⁻¹
      = c₁ * (c₂ * u) * v * c₂⁻¹ * c₁⁻¹ := by group
    _ = c₁ * (u * c₂) * v * c₂⁻¹ * c₁⁻¹ := by rw [hc2u]
    _ = c₁ * u * (c₂ * v * c₂⁻¹) * c₁⁻¹ := by group
    _ = c₁ * u * v' * c₁⁻¹ := by rw [h₂e]
    _ = (c₁ * u * c₁⁻¹) * (c₁ * v' * c₁⁻¹) := by group
    _ = u' * v' := by
        rw [h₁e]
        congr 1
        rw [hc1v']; group

end TC

section TriSec

theorem exists_tri (i112 : Input11_2Full) {m : ℕ} (hS : GLStanding G m 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent 3 (Cb b) L) (hn : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    ∃ L₂ L₃ : Subgroup G, Tri B b L L₂ L₃ ∧ bClosure B L = L ⊔ L₂ ⊔ L₃ ∧
      ∀ L' : Subgroup G, IsBConjugate B L L' → L' = L ∨ L' = L₂ ∨ L' = L₃ := by
  have := hS.simple
  have hp : Nat.Prime 3 := hS.prime
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBC : B ≤ Cb b := le_centralizer_of_mem hBel hbB
  have hCne : Cb b ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
  have hrk : GLATwoLocalRank 3 ↥(Cb b) ≤ CFSG.Open.pRank 3 B :=
    (glaTwoLocalRank_subgroup_le hp (Cb b)).trans (hS.rank_eq.le.trans (hS.le_pRank' hB))
  have h112 := i112 G m 3 hS (Cb b) B L hBel hBC hrk hL hn
  have h3 : (Subgroup.normalizer (L : Set G)).relIndex B = 3 := h112.2.1
  obtain ⟨L₂, L₃, ⟨g₂, hg₂, hL₂⟩, ⟨g₃, hg₃, hL₃⟩, h12, h13, h23, hall⟩ :=
    exists_three_conjugates hBel.1 h3
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => elemAbelian_comm hBel hx hy
  have hcube : ∀ x ∈ B, x ^ 3 = 1 := hBel.2
  have hcomp : ∀ g ∈ B, GLAPComponent 3 (Cb b) (GLBConj g L) := by
    intro g hg
    have := glaPComponent_gLBConj g hL
    rwa [gLBConj_centralizer_singleton_of_commute (hcomm g hg b hbB)] at this
  set β := g₂ with hβ
  have hβB : β ∈ B := hg₂
  have hLβ : L₂ = GLBConj β L := hL₂
  have hββ : GLBConj β L₂ = L₃ := by
    have hmem : GLBConj β L₂ ∈ {X | ∃ g ∈ B, X = GLBConj g L} := by
      refine ⟨β * β, B.mul_mem hβB hβB, ?_⟩
      rw [hLβ, gLBConj_gLBConj]
    rcases hall _ hmem with h | h | h
    · exfalso
      have h1 : GLBConj (β * β) L = L := by rw [← gLBConj_gLBConj, ← hLβ]; exact h
      have h2 : β * β ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 h1
      have h3' : β = (β * β) * (β * β) := by
        have := hcube β hβB
        calc β = β ^ 3 * β := by rw [this, one_mul]
          _ = (β * β) * (β * β) := by simp [pow_succ, mul_assoc]
      have : β ∈ Subgroup.normalizer (L : Set G) := by
        rw [h3']; exact Subgroup.mul_mem _ h2 h2
      exact h12 (by rw [hLβ, gLBConj_eq_of_mem_normalizer this])
    · exfalso
      have e := congrArg (GLBConj β⁻¹) h
      rw [gLBConj_inv_gLBConj] at e
      have e2 : GLBConj β⁻¹ L₂ = L := by rw [hLβ, gLBConj_inv_gLBConj]
      rw [e2] at e
      exact h12 e.symm
    · exact h
  have hc2 : GLAPComponent 3 (Cb b) L₂ := hL₂ ▸ hcomp g₂ hg₂
  have hc3 : GLAPComponent 3 (Cb b) L₃ := hL₃ ▸ hcomp g₃ hg₃
  refine ⟨L₂, L₃, ⟨hBel, hbB, hb1, hL, hc2, hc3, h12, h23, h13, ⟨β, hβB, hLβ, hββ.symm, ?_⟩⟩,
    ?_, hall⟩
  ·
    rw [← hββ, hLβ, gLBConj_gLBConj, gLBConj_gLBConj]
    have : β * (β * β) = β ^ 3 := by simp [pow_succ, mul_assoc]
    rw [this, hcube β hβB, gLBConj_one]
  · unfold bClosure
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      rcases hall (GLBConj g L) ⟨g, hg, rfl⟩ with h | h | h
      · rw [h]; exact le_sup_of_le_left le_sup_left
      · rw [h]; exact le_sup_of_le_left le_sup_right
      · rw [h]; exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂_of_le 1 B.one_mem (by rw [gLBConj_one])
      · exact le_iSup₂_of_le g₂ hg₂ (le_of_eq hL₂)
      · exact le_iSup₂_of_le g₃ hg₃ (le_of_eq hL₃)

end TriSec

section T1Sec

theorem t1_sylow_conj {K : Type*} [Group K] [Finite K] (P : Sylow 3 K) (a : K)
    (h : ∃ k : ℕ, a ^ (3 ^ k) = 1) : ∃ g : K, g⁻¹ * a * g ∈ (P : Subgroup K) := by
  have hfp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h
  have hpg : IsPGroup 3 (Subgroup.zpowers a) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨j, hj⟩
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  refine ⟨g, ?_⟩
  have haQ : a ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers a)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haQ
  simpa [MulAut.smul_def] using haQ

theorem t1_center_card {R : Type*} [Group R] (h27 : Nat.card R = 27)
    (hna : ¬ ∀ r s : R, r * s = s * r) : Nat.card (Subgroup.center R) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 3) (n := 3) (G := R)
    (by simpa using h27) (by norm_num)
  have hdvd : Nat.card (Subgroup.center R) ∣ 27 := h27 ▸ Subgroup.card_subgroup_dvd_card _
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    rw [← hk] at this
    have := Nat.le_of_dvd (by norm_num) (this.trans hdvd)
    omega
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by omega)
  interval_cases k
  · exact hk
  · exfalso
    have hidx : (Subgroup.center R).index = 3 := by
      have := (Subgroup.center R).card_mul_index
      rw [hk, h27] at this
      omega
    have : IsCyclic (R ⧸ Subgroup.center R) := by
      apply isCyclic_of_prime_card (p := 3)
      rw [← Subgroup.index_eq_card]; exact hidx
    apply hna
    intro r s
    exact (QuotientGroup.mk' (Subgroup.center R)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']) |>.is_comm.comm r s
  · exfalso
    apply hna
    have : Subgroup.center R = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hk, h27]; norm_num
    intro r s
    have hr : r ∈ Subgroup.center R := this ▸ Subgroup.mem_top r
    exact ((Subgroup.mem_center_iff.mp hr) s).symm

theorem t1_comm_mem_center {R : Type*} [Group R] (h27 : Nat.card R = 27)
    (hna : ¬ ∀ r s : R, r * s = s * r) (x y : R) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := t1_center_card h27 hna
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by omega)
  have hq : Nat.card (R ⧸ Subgroup.center R) = 3 ^ 2 := by
    have := (Subgroup.center R).card_mul_index
    rw [hc, h27, Subgroup.index_eq_card] at this
    omega
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : R ⧸ Subgroup.center R) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have := hcomm.is_comm.comm (QuotientGroup.mk x : R ⧸ Subgroup.center R) (QuotientGroup.mk y)
    rw [this]
    group
  exact (QuotientGroup.eq_one_iff _).mp this

theorem t1_pow_conj {R : Type*} [Group R] (s a c : R) (hca : c * a = a * c)
    (hcs : c * s = s * c) (hc : s * a * s⁻¹ = c * a) (k : ℕ) :
    s ^ k * a * (s ^ k)⁻¹ = a * c ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcs' : s ^ k * c * (s ^ k)⁻¹ = c :=
      by rw [mul_inv_eq_iff_eq_mul]; exact ((Commute.pow_right (show Commute c s from hcs) k).eq).symm
    calc s ^ (k + 1) * a * (s ^ (k + 1))⁻¹ = s ^ k * (s * a * s⁻¹) * (s ^ k)⁻¹ := by group
      _ = s ^ k * (c * a) * (s ^ k)⁻¹ := by rw [hc]
      _ = (s ^ k * c * (s ^ k)⁻¹) * (s ^ k * a * (s ^ k)⁻¹) := by group
      _ = c * (a * c ^ k) := by rw [ih, hcs']
      _ = a * c ^ (k + 1) := by rw [← mul_assoc, hca, mul_assoc, pow_succ']

theorem fusData_of_abstract (i302 : Input30_2) {X : Type} [Group X] [Finite X]
    (hε : IsSL3Eps X) (hX3 : (Nat.card X).factorization 3 = 3) (R : Subgroup X)
    (hRp : IsPGroup 3 R) (hR27 : Nat.card R = 27)
    (hRna : ¬ ∀ r ∈ R, ∀ s ∈ R, r * s = s * r) (hR3 : ∀ r ∈ R, r ^ 3 = 1)
    (hZR : Subgroup.center X ≤ R)
    (hZR' : ∀ w ∈ R, (∀ r ∈ R, w * r = r * w) → w ∈ Subgroup.center X) :
    FusData (⊤ : Subgroup X) (Subgroup.center X) := by
  have hfp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRna' : ¬ ∀ r s : R, r * s = s * r := by
    intro h; apply hRna; intro r hr s hs
    exact congrArg Subtype.val (h ⟨r, hr⟩ ⟨s, hs⟩)
  have hRc := t1_center_card hR27 hRna'
  have hZ : (Subgroup.center R).map R.subtype = Subgroup.center X := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hZR' r.1 r.2 (fun s hs => by
        have := Subgroup.mem_center_iff.mp hr ⟨s, hs⟩
        exact congrArg Subtype.val this.symm)
    · intro hx
      refine ⟨⟨x, hZR hx⟩, ?_, rfl⟩
      refine Subgroup.mem_center_iff.mpr (fun s => ?_)
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx s.1)
  have hZcard : Nat.card (Subgroup.center X) = 3 := by
    rw [← hZ, Subgroup.card_map_of_injective R.subtype_injective]; exact hRc
  have hfin : Finite X := inferInstance
  obtain ⟨P, hP⟩ : ∃ P : Sylow 3 X, (P : Subgroup X) = R := by
    obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hRP ?_).symm⟩
    rw [Sylow.card_eq_multiplicity, hX3, hR27]; norm_num
  have hconj : ∀ a : X, (∃ k : ℕ, a ^ (3 ^ k) = 1) → ∃ g : X, g⁻¹ * a * g ∈ R := by
    intro a h
    obtain ⟨g, hg⟩ := t1_sylow_conj P a h
    exact ⟨g, hP ▸ hg⟩
  have hconjpow : ∀ (a g : X) (n : ℕ), (g⁻¹ * a * g) ^ n = g⁻¹ * a ^ n * g := by
    intro a g n
    have := conj_pow (a := g⁻¹) (b := a) (i := n)
    simpa using this
  have hshiftR : ∀ a ∈ R, a ∉ Subgroup.center X → ∀ w ∈ Subgroup.center X,
      ∃ r ∈ R, r * a * r⁻¹ = a * w := by
    intro a haR haZ w hw
    have hnc : ¬ ∀ s ∈ R, a * s = s * a := fun h => haZ (hZR' a haR h)
    push Not at hnc
    obtain ⟨s, hsR, hs⟩ := hnc
    set c : X := s * a * s⁻¹ * a⁻¹ with hc
    have h0 : (⟨s, hsR⟩ * ⟨a, haR⟩ * (⟨s, hsR⟩ : R)⁻¹ * (⟨a, haR⟩ : R)⁻¹ : R) ∈
        Subgroup.center R := t1_comm_mem_center hR27 hRna' _ _
    have hcZ : c ∈ Subgroup.center X := by
      rw [← hZ]
      exact ⟨_, h0, rfl⟩
    have hc1 : c ≠ 1 := by
      intro h1
      apply hs
      have h2 : s * a * s⁻¹ = a := by
        have := congrArg (· * a) h1
        simpa [hc] using this
      calc a * s = (s * a * s⁻¹) * s := by rw [h2]
        _ = s * a := by group
    have hca : c * a = a * c := (Subgroup.mem_center_iff.mp hcZ a).symm
    have hcs : c * s = s * c := (Subgroup.mem_center_iff.mp hcZ s).symm
    have hcc : s * a * s⁻¹ = c * a := by rw [hc]; group
    have hgen : Subgroup.zpowers (⟨c, hcZ⟩ : Subgroup.center X) = ⊤ :=
      zpowers_eq_top_of_prime_card hZcard (fun h => hc1 (congrArg Subtype.val h))
    have hwm : (⟨w, hw⟩ : Subgroup.center X) ∈ Subgroup.zpowers (⟨c, hcZ⟩ : Subgroup.center X) := by
      rw [hgen]; exact Subgroup.mem_top _
    rw [← mem_powers_iff_mem_zpowers] at hwm
    obtain ⟨k, hk⟩ := hwm
    have hk' : c ^ k = w := congrArg Subtype.val hk
    exact ⟨s ^ k, R.pow_mem hsR k, by
      rw [t1_pow_conj s a c hca hcs hcc k, hk']⟩
  refine ⟨?_, hZcard, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_top
  · intro w
    constructor
    · intro hw; exact ⟨Subgroup.mem_top _, fun q _ => (Subgroup.mem_center_iff.mp hw q).symm⟩
    · rintro ⟨-, h⟩; exact Subgroup.mem_center_iff.mpr (fun q => (h q trivial).symm)
  · intro a _ hk
    obtain ⟨g, hg⟩ := hconj a hk
    have := hR3 _ hg
    rw [hconjpow] at this
    have h2 : g * (g⁻¹ * a ^ 3 * g) * g⁻¹ = 1 := by rw [this]; group
    simpa [mul_assoc] using h2
  · intro a _ ha3 haZ a' _ ha'3 ha'Z
    set Z := Subgroup.center X with hZdef
    have hcardK : Nat.card (X ⧸ Z) * 3 = Nat.card X := by
      rw [← hZcard]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
    have hK0 : Nat.card (X ⧸ Z) ≠ 0 := Nat.card_pos.ne'
    have hKfac : (Nat.card (X ⧸ Z)).factorization 3 = 2 := by
      have h1 := hX3
      rw [← hcardK, Nat.factorization_mul hK0 (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_three] at h1
      omega
    obtain ⟨hA, hB, -⟩ := i302 X hε
    obtain ⟨F⟩ : Nonempty (Sylow 3 (X ⧸ Z)) := inferInstance
    obtain ⟨hFab, hq8⟩ := hB hKfac F
    have hFcard : Nat.card (F : Subgroup (X ⧸ Z)) = 3 ^ 2 := by
      rw [Sylow.card_eq_multiplicity, hKfac]
    have hTF : TotallyFused (F : Subgroup (X ⧸ Z)) := ((hA F hFab hFcard).1).1 hq8
    have hmk_pow : ∀ x : X, x ^ 3 = 1 → ((x : X ⧸ Z)) ^ 3 = 1 := fun x hx => by
      rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
    have hmk_ne : ∀ x : X, x ∉ Z → ((x : X ⧸ Z)) ≠ 1 := fun x hx h =>
      hx ((QuotientGroup.eq_one_iff x).1 h)
    obtain ⟨g1, hg1⟩ := t1_sylow_conj F (a : X ⧸ Z) ⟨1, by simpa using hmk_pow a ha3⟩
    obtain ⟨g2, hg2⟩ := t1_sylow_conj F (a' : X ⧸ Z) ⟨1, by simpa using hmk_pow a' ha'3⟩
    have hf1 : g1⁻¹ * (a : X ⧸ Z) * g1 ≠ 1 := fun h => hmk_ne a haZ (by
      have : (a : X ⧸ Z) = g1 * (g1⁻¹ * (a : X ⧸ Z) * g1) * g1⁻¹ := by group
      rw [this, h]; group)
    have hf2 : g2⁻¹ * (a' : X ⧸ Z) * g2 ≠ 1 := fun h => hmk_ne a' ha'Z (by
      have : (a' : X ⧸ Z) = g2 * (g2⁻¹ * (a' : X ⧸ Z) * g2) * g2⁻¹ := by group
      rw [this, h]; group)
    obtain ⟨m, hm⟩ := hTF _ hg1 hf1 _ hg2 hf2
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (g2 * m * g1⁻¹)
    have key : (g2 * m * g1⁻¹) * (a : X ⧸ Z) * (g2 * m * g1⁻¹)⁻¹ = (a' : X ⧸ Z) := by
      calc (g2 * m * g1⁻¹) * (a : X ⧸ Z) * (g2 * m * g1⁻¹)⁻¹
          = g2 * (m * (g1⁻¹ * (a : X ⧸ Z) * g1) * m⁻¹) * g2⁻¹ := by group
        _ = g2 * (g2⁻¹ * (a' : X ⧸ Z) * g2) * g2⁻¹ := by rw [hm]
        _ = a' := by group
    refine ⟨c, trivial, a'⁻¹ * (c * a * c⁻¹), ?_, (mul_inv_cancel_left a' _).symm⟩
    apply (QuotientGroup.eq_one_iff _).1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hc, key, inv_mul_cancel]
  · intro a _ ha3 haZ w hw
    obtain ⟨g, hg⟩ := hconj a ⟨1, by simpa using ha3⟩
    have hga : g⁻¹ * a * g ∉ Subgroup.center X := by
      intro h
      apply haZ
      have h1 := Subgroup.mem_center_iff.mp h g
      have : a = g⁻¹ * a * g := by
        calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
          _ = (g⁻¹ * a * g) * g * g⁻¹ := by rw [h1]
          _ = g⁻¹ * a * g := by group
      rw [this]; exact h
    obtain ⟨r, hr, hra⟩ := hshiftR _ hg hga w hw
    refine ⟨g * r * g⁻¹, trivial, ?_⟩
    have hwg := Subgroup.mem_center_iff.mp hw g
    calc g * r * g⁻¹ * a * (g * r * g⁻¹)⁻¹ = g * (r * (g⁻¹ * a * g) * r⁻¹) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * w) * g⁻¹ := by rw [hra]
      _ = a * (g * w * g⁻¹) := by group
      _ = a * w := by rw [hwg]; group
  · obtain ⟨r, hr, s, hs, hne⟩ : ∃ r ∈ R, ∃ s ∈ R, r * s ≠ s * r := by
      by_contra h; push Not at h; exact hRna h
    refine ⟨r, trivial, hR3 r hr, fun hrz => hne ?_⟩
    exact (Subgroup.mem_center_iff.mp hrz s).symm

theorem fusData_of_equiv {H X : Type*} [Group H] [Group X] {Q : Subgroup H} (e : X ≃* ↥Q)
    {Z : Subgroup X} (h : FusData (⊤ : Subgroup X) Z) :
    FusData Q (Z.map (Q.subtype.comp e.toMonoidHom)) := by
  set φ : X →* H := Q.subtype.comp e.toMonoidHom with hφ
  have hinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφx : ∀ x, φ x = ((e x : ↥Q) : H) := fun x => rfl
  have hsurj : ∀ a ∈ Q, ∃ x, φ x = a := fun a ha => ⟨e.symm ⟨a, ha⟩, by simp [hφx]⟩
  have hmem : ∀ x, φ x ∈ Z.map φ ↔ x ∈ Z := fun x => Subgroup.mem_map_iff_mem hinj
  have hφQ : ∀ x, φ x ∈ Q := fun x => (e x).2
  have hpow : ∀ x (n : ℕ), φ x ^ n = 1 ↔ x ^ n = 1 := fun x n => by
    rw [← map_pow, ← map_one φ]; exact hinj.eq_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩; exact hφQ z
  · rw [Subgroup.card_map_of_injective hinj]; exact h.Zcard
  · intro w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hφQ z, ?_⟩
      intro q hq
      obtain ⟨y, rfl⟩ := hsurj q hq
      rw [← map_mul, ← map_mul, (h.Zcenter z).1 hz |>.2 y trivial]
    · rintro ⟨hw, hc⟩
      obtain ⟨z, rfl⟩ := hsurj w hw
      refine ⟨z, ?_, rfl⟩
      refine (h.Zcenter z).2 ⟨trivial, fun q _ => ?_⟩
      apply hinj
      rw [map_mul, map_mul]; exact hc _ (hφQ q)
  · intro a ha hk
    obtain ⟨x, rfl⟩ := hsurj a ha
    obtain ⟨k, hk⟩ := hk
    rw [hpow] at hk ⊢
    exact h.exp3 x trivial ⟨k, hk⟩
  · intro a ha ha3 haZ a' ha' ha'3 ha'Z
    obtain ⟨x, rfl⟩ := hsurj a ha
    obtain ⟨x', rfl⟩ := hsurj a' ha'
    rw [hpow] at ha3 ha'3
    rw [hmem] at haZ ha'Z
    obtain ⟨c, -, w, hw, hcw⟩ := h.fus x trivial ha3 haZ x' trivial ha'3 ha'Z
    refine ⟨φ c, hφQ c, φ w, ⟨w, hw, rfl⟩, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, hcw]
  · intro a ha ha3 haZ w hw
    obtain ⟨x, rfl⟩ := hsurj a ha
    obtain ⟨w, hw', rfl⟩ := hw
    rw [hpow] at ha3
    rw [hmem] at haZ
    obtain ⟨r, -, hr⟩ := h.shift x trivial ha3 haZ w hw'
    refine ⟨φ r, hφQ r, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, hr]
  · obtain ⟨x, -, hx3, hxZ⟩ := h.exists_noncentral
    refine ⟨φ x, hφQ x, ?_, ?_⟩
    · rw [hpow]; exact hx3
    · rw [hmem]; exact hxZ

end T1Sec

section T2Sec

theorem t2_card_center_three {R : Type*} [Group R] [Finite R] (hcard : Nat.card R = 27)
    (hna : ¬ ∀ r s : R, r * s = s * r) : Nat.card (Subgroup.center R) = 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have : Nontrivial R := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  have := hpg.center_nontrivial
  have hdvd : Nat.card (Subgroup.center R) ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center R)
    rw [hcard] at this
    simpa using this
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hgt : 1 < Nat.card (Subgroup.center R) := Finite.one_lt_card_iff_nontrivial.2 inferInstance
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
  interval_cases k
  · rw [hkc] at hgt; norm_num at hgt
  · simpa using hkc
  · exfalso
    have hq : Nat.card (R ⧸ Subgroup.center R) = 3 := by
      rw [hcard, hkc] at hmul
      omega
    have : Fact (Nat.Prime (Nat.card (R ⧸ Subgroup.center R))) := ⟨by rw [hq]; exact Nat.prime_three⟩
    have : IsCyclic (R ⧸ Subgroup.center R) := isCyclic_of_prime_card rfl
    have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center R)) (by simp [QuotientGroup.ker_mk'])
    exact hna fun r s => hcomm.is_comm.comm r s
  · exfalso
    have htop : Subgroup.center R = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hkc, hcard]; norm_num)
    apply hna
    intro r s
    have : s ∈ Subgroup.center R := htop ▸ Subgroup.mem_top s
    exact Subgroup.mem_center_iff.1 this r

theorem t2_inj_of_coprime {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (R : Subgroup H) (hR : IsPGroup 3 R) {x : H} (hx : x ∈ R)
    (h : QuotientGroup.mk' N x = 1) : x = 1 := by
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  have h3 : Nat.Coprime (3 ^ k) (orderOf x) := (hN.coprime_dvd_right h2).pow_left k
  have := Nat.Coprime.eq_one_of_dvd h3.symm h1
  exact orderOf_eq_one_iff.1 this

theorem t2_map_card {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (R : Subgroup H) (hR : IsPGroup 3 R) :
    Nat.card (R.map (QuotientGroup.mk' N)) = Nat.card R := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).domRestrict R) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := t2_inj_of_coprime N hN R hR x.2 (by simpa using hx)
    exact Subtype.ext this
  rw [← MonoidHom.domRestrict_range]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Finite G] in
theorem t2_barX_mono' {X S T : Subgroup G} (h : S ≤ T) : barX 3 X S ≤ barX 3 X T :=
  Subgroup.map_mono fun _ hx => h hx

theorem t2_comm_of_sup {C L M : Subgroup G} (hL : L ≤ C) (hM : M ≤ C)
    {w : ↥C ⧸ GLAPPrimeCore 3 ↥C} (hwL : ∀ y ∈ barX 3 C L, y * w = w * y)
    (hwM : ∀ y ∈ barX 3 C M, y * w = w * y) : ∀ y ∈ barX 3 C (L ⊔ M), y * w = w * y := by
  let S : Subgroup G := ((Subgroup.centralizer ({w} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))).comap
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C))).map C.subtype
  have hLS : L ≤ S := fun x hx =>
    ⟨⟨x, hL hx⟩, by
      show QuotientGroup.mk' _ _ ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hwL _ ⟨⟨x, hL hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩, rfl⟩
  have hMS : M ≤ S := fun x hx =>
    ⟨⟨x, hM hx⟩, by
      show QuotientGroup.mk' _ _ ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hwM _ ⟨⟨x, hM hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (x : G) ∈ S := sup_le hLS hMS ((Subgroup.mem_subgroupOf).1 hx)
  obtain ⟨c, hc, hcx⟩ := hxS
  have : c = x := Subtype.ext hcx
  subst this
  have hc' : QuotientGroup.mk' _ c ∈ Subgroup.centralizer ({w} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc'
  exact hc'

theorem t2_bClosure_conj {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    bClosure B (GLBConj g L) = bClosure B L := by
  apply le_antisymm
  · refine iSup₂_le fun h hh => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂ (f := fun (x : G) (_ : x ∈ B) => GLBConj x L) (g * h) (B.mul_mem hg hh)
  · refine iSup₂_le fun h hh => ?_
    calc GLBConj h L = GLBConj (g⁻¹ * h) (GLBConj g L) := by rw [gLBConj_gLBConj]; simp
      _ ≤ bClosure B (GLBConj g L) :=
        le_iSup₂ (f := fun (x : G) (_ : x ∈ B) => GLBConj x (GLBConj g L)) (g⁻¹ * h)
          (B.mul_mem (B.inv_mem hg) hh)

theorem t2_not_le_normalizer {B L L' : Subgroup G} {g : G} (hg : g ∈ B) (h : L' = GLBConj g L)
    (hne : L ≠ L') : ¬ B ≤ Subgroup.normalizer (L : Set G) := fun hB =>
  hne (h.trans (gLBConj_eq_of_mem_normalizer (hB hg))).symm

theorem t2_type_transfer {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSLThree X ∨ IsSUThree X) : IsSLThree Y ∨ IsSUThree Y := by
  rcases h with ⟨K, F, fin, ⟨e'⟩⟩ | ⟨K, F, fin, q, hk, ⟨e'⟩⟩
  · exact Or.inl ⟨K, F, fin, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨K, F, fin, q, hk, ⟨e.symm.trans e'⟩⟩

theorem t2_type_conj {L L' : Subgroup G} {g : G} (h : L' = GLBConj g L)
    (ht : IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L)) :
    IsSLThree (barOf 3 L') ∨ IsSUThree (barOf 3 L') := by
  subst h
  exact t2_type_transfer (conjQuotEquiv 3 g L) ht

theorem t2_bbar_ne {b : G} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    barX 3 (Cb b) (Subgroup.zpowers b) ≠ ⊥ := by
  intro h
  have hbC : b ∈ Cb b := by rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b)) ⟨b, hbC⟩ ∈ barX 3 (Cb b) (Subgroup.zpowers b) :=
    ⟨⟨b, hbC⟩, (Subgroup.mem_subgroupOf).2 (Subgroup.mem_zpowers b), rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hd : orderOf (⟨b, hbC⟩ : ↥(Cb b)) ∣ Nat.card (GLAPPrimeCore 3 ↥(Cb b)) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  rw [Subgroup.orderOf_mk, hord] at hd
  have := Nat.Coprime.eq_one_of_dvd (coprime_card_gLAPPrimeCore_aux 3 ↥(Cb b)) hd
  omega

theorem t2_bbar_card_le {b : G} (hb3 : b ^ 3 = 1) :
    Nat.card (barX 3 (Cb b) (Subgroup.zpowers b)) ≤ 3 := by
  have hbC : b ∈ Cb b := by rw [Subgroup.mem_centralizer_singleton_iff]
  set bb : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b) := QuotientGroup.mk' _ ⟨b, hbC⟩ with hbb
  have hle : barX 3 (Cb b) (Subgroup.zpowers b) ≤ Subgroup.zpowers bb := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_subgroupOf).1 hx)
    refine ⟨i, ?_⟩
    have : (⟨b, hbC⟩ : ↥(Cb b)) ^ i = x := Subtype.ext (by simpa using hi)
    show bb ^ i = _
    rw [hbb, ← map_zpow, this]
  refine (Subgroup.card_le_of_le hle).trans ?_
  rw [Nat.card_zpowers]
  have hbb3 : bb ^ 3 = 1 := by
    have h3 : (⟨b, hbC⟩ : ↥(Cb b)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [hbb, ← map_pow, h3, map_one]
  exact orderOf_le_of_pow_eq_one (by norm_num) hbb3


theorem t2_core (i112 : Input11_2Four) (i302 : Input30_2) {m : ℕ}
    (hS : GLStanding G m 3) {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) {L L' L'' K : Subgroup G} (hL : GLAPComponent 3 (Cb b) L)
    (hL' : GLAPComponent 3 (Cb b) L') (hL'' : GLAPComponent 3 (Cb b) L'') (hne' : L ≠ L')
    (hne'' : L ≠ L'') (hnorm : ¬ B ≤ Subgroup.normalizer (L : Set G)) (hK : bClosure B L = K)
    (hKs : K = L ⊔ (L' ⊔ L''))
    (hZ : barX 3 (Cb b) (Subgroup.zpowers b) =
      (Subgroup.center ↥(barX 3 (Cb b) K)).map (barX 3 (Cb b) K).subtype)
    (htype : IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L)) :
    FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b)) ∧ IsSL3Eps (barOf 3 L) ∧
      SylInfo b L := by
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hBC : B ≤ Cb b := le_centralizer_of_mem hBel hbB
  have hrk : GLATwoLocalRank 3 ↥(Cb b) ≤ CFSG.Open.pRank 3 B := by
    have := hS.simple
    exact (glaTwoLocalRank_subgroup_le Nat.prime_three (Cb b)).trans
      (hS.rank_eq.le.trans (hS.le_pRank' hB))
  have hcen : Subgroup.center ↥(barX 3 (Cb b) (bClosure B L)) ≠ ⊥ := by
    intro h
    rw [hK] at h
    apply t2_bbar_ne hb3 hb1
    rw [hZ, h, Subgroup.map_bot]
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥L))
  obtain ⟨hc27, hRna, hR3, hZsub, hZsup⟩ :=
    i112 G m hS (Cb b) B L hBel hBC hrk hL hnorm hcen R
  have hN := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have hRp : IsPGroup 3 (R : Subgroup ↥L) := R.isPGroup'
  have hcardRb : Nat.card ((R : Subgroup ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) = 27 :=
    (t2_map_card (GLAPPrimeCore 3 ↥L) hN _ hRp).trans hc27
  set Rb := (R : Subgroup ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hRb
  have hRbp : IsPGroup 3 Rb := IsPGroup.of_card (n := 3) (by rw [hcardRb]; norm_num)
  have hnaRb : ¬ ∀ r ∈ Rb, ∀ s ∈ Rb, r * s = s * r := by
    intro hall
    apply hRna
    intro r hr s hs
    have h1 := hall _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (r * s * (s * r)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      simp
    have := t2_inj_of_coprime _ hN _ hRp
      ((R : Subgroup ↥L).mul_mem ((R : Subgroup ↥L).mul_mem hr hs)
        ((R : Subgroup ↥L).inv_mem ((R : Subgroup ↥L).mul_mem hs hr))) h2
    exact mul_inv_eq_one.1 this
  have hR3Rb : ∀ r ∈ Rb, r ^ 3 = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hR3 r hr, map_one]
  have hX3 : (Nat.card (barOf 3 L)).factorization 3 = 3 := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)
    have hf : (Nat.card ↥L).factorization 3 = 3 := by
      have h := Sylow.card_eq_multiplicity R
      have h' : (27 : ℕ) = 3 ^ (Nat.card ↥L).factorization 3 := hc27.symm.trans h
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ 3 = 3 ^ _ by simpa using h')).symm
    have hnd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := fun h => by
      have := Nat.Coprime.eq_one_of_dvd hN h
      omega
    have hz1 : Nat.card (↥L ⧸ GLAPPrimeCore 3 ↥L) ≠ 0 := Nat.card_pos.ne'
    have hz2 : Nat.card (GLAPPrimeCore 3 ↥L) ≠ 0 := Nat.card_pos.ne'
    rw [hmul, Nat.factorization_mul hz1 hz2, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero] at hf
    exact hf
  have hcX : Subgroup.center (barOf 3 L) = (Subgroup.center Rb).map Rb.subtype := by
    ext w
    constructor
    · intro hw
      have hwR : w ∈ Rb := hZsub hw
      exact ⟨⟨w, hwR⟩, Subgroup.mem_center_iff.2 fun r =>
        Subtype.ext (Subgroup.mem_center_iff.1 hw r), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact hZsup _ c.2 fun r hr =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨r, hr⟩)).symm
  have hcc : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    rw [hcX, Subgroup.card_map_of_injective Rb.subtype_injective]
    exact t2_card_center_three hcardRb fun h =>
      hnaRb fun r hr s hs => congrArg Subtype.val (h ⟨r, hr⟩ ⟨s, hs⟩)
  have heps : IsSL3Eps (barOf 3 L) := ⟨htype, by rw [hcc]⟩
  have hfus := fusData_of_abstract i302 heps hX3 Rb hRbp hcardRb hnaRb hR3Rb hZsub hZsup
  let e : barOf 3 L ≃* ↥(barX 3 (Cb b) L) := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  have hfus2 : FusData (barX 3 (Cb b) L)
      (Subgroup.map ((barX 3 (Cb b) L).subtype.comp e.toMonoidHom) (Subgroup.center (barOf 3 L))) :=
    fusData_of_equiv e hfus
  have hcomm_of_ne : ∀ {M : Subgroup G}, GLAPComponent 3 (Cb b) M → L ≠ M →
      barX 3 (Cb b) L ≤ Subgroup.centralizer (barX 3 (Cb b) M : Set (↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b))) :=
    fun {M} hM hne => barX_le_centralizer fun s hs t ht _ _ => by
      have hcm := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hL hM hne
      apply hcm
      have := Subgroup.commutator_mem_commutator hs ht
      rwa [commutatorElement_def] at this
  have hLK : L ≤ K := by rw [hKs]; exact le_sup_left
  have hle : Subgroup.map ((barX 3 (Cb b) L).subtype.comp e.toMonoidHom) (Subgroup.center (barOf 3 L)) ≤
      barX 3 (Cb b) (Subgroup.zpowers b) := by
    rintro _ ⟨z, hz, rfl⟩
    have hwL : ((e z : ↥(barX 3 (Cb b) L)) : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) ∈ barX 3 (Cb b) L :=
      (e z).2
    have hyL : ∀ y ∈ barX 3 (Cb b) L,
        y * ((e z : ↥(barX 3 (Cb b) L)) : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) =
          ((e z : ↥(barX 3 (Cb b) L)) : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) * y := fun y hy => by
      have h1 := Subgroup.mem_center_iff.1 hz (e.symm ⟨y, hy⟩)
      have h2 := congrArg e h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact congrArg Subtype.val h2
    have hyL' := fun y hy => Subgroup.mem_centralizer_iff.1 (hcomm_of_ne hL' hne' hwL) y hy
    have hyL'' := fun y hy => Subgroup.mem_centralizer_iff.1 (hcomm_of_ne hL'' hne'' hwL) y hy
    have hyM := t2_comm_of_sup hL'.1 hL''.1 hyL' hyL''
    have hyK := t2_comm_of_sup hL.1 (sup_le hL'.1 hL''.1) hyL hyM
    rw [← hKs] at hyK
    rw [hZ]
    exact ⟨⟨_, t2_barX_mono' hLK hwL⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hyK g.1 g.2), rfl⟩
  have hZim := Subgroup.eq_of_le_of_card_ge hle (by rw [hfus2.Zcard]; exact t2_bbar_card_le hb3)
  refine ⟨hZim ▸ hfus2, heps, ?_⟩
  have hbC : b ∈ Cb b := by rw [Subgroup.mem_centralizer_singleton_iff]
  have hbbar : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b)) ⟨b, hbC⟩ ∈
      barX 3 (Cb b) (Subgroup.zpowers b) :=
    ⟨⟨b, hbC⟩, (Subgroup.mem_subgroupOf).2 (Subgroup.mem_zpowers b), rfl⟩
  have hbL : b ∈ L := by
    refine q_mem_of_bar hL hbC (k := 1) (by simpa using hb3) ?_
    rw [← hZim] at hbbar
    obtain ⟨z, _, hz⟩ := hbbar
    have h2 : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b)) ⟨b, hbC⟩ : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b))
        ∈ barX 3 (Cb b) L := by
      rw [← hz]
      exact (e z).2
    exact h2
  have hcommL : ∀ g : ↥L, g * (⟨b, hbL⟩ : ↥L) = ⟨b, hbL⟩ * g := fun g => Subtype.ext (by
    have := hL.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this)
  have hNn : (Subgroup.zpowers (⟨b, hbL⟩ : ↥L)).Normal := ⟨fun n hn g => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have h := ((show Commute g (⟨b, hbL⟩ : ↥L) from hcommL g).zpow_right i).eq
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩⟩
  have hNp : IsPGroup 3 (Subgroup.zpowers (⟨b, hbL⟩ : ↥L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_eq_prime hb3 hb1]
    simp
  intro R0 hR0L hR0p hR0c
  have hsub : IsPGroup 3 (R0.subgroupOf L) :=
    IsPGroup.of_equiv hR0p (Subgroup.subgroupOfEquivOfLe hR0L).symm
  have hcsub : Nat.card (R0.subgroupOf L) = Nat.card R0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0L).toEquiv
  obtain ⟨Q, hQ⟩ := hsub.exists_le_sylow
  have hQeq : R0.subgroupOf L = (Q : Subgroup ↥L) :=
    Subgroup.eq_of_le_of_card_ge hQ (by
      rw [Sylow.card_eq_multiplicity Q, hcsub, hR0c])
  have hmemQ : ∀ r : ↥L, r ∈ (Q : Subgroup ↥L) ↔ (r : G) ∈ R0 := fun r => by
    rw [← hQeq]; exact Subgroup.mem_subgroupOf
  obtain ⟨hq27, hqna, hq3, -, hqZsup⟩ :=
    i112 G m hS (Cb b) B L hBel hBC hrk hL hnorm hcen Q
  have hcardR : Nat.card R0 = 27 := by
    rw [← hcsub, hQeq]; exact hq27
  refine ⟨hcardR, ?_, ?_, ?_⟩
  · intro hall
    apply hqna
    intro r hr s hs
    exact Subtype.ext (hall r.1 ((hmemQ r).1 hr) s.1 ((hmemQ s).1 hs))
  · intro a ha
    have := hq3 ⟨a, hR0L ha⟩ ((hmemQ _).2 ha)
    exact congrArg Subtype.val this
  · apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hcR : (c : G) ∈ R0 := c.2
      have hcL : (c : G) ∈ L := hR0L hcR
      have hcC : (c : G) ∈ Cb b := hL.1 hcL
      have hcen' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨c, hcL⟩ ∈ Subgroup.center (barOf 3 L) := by
        apply hqZsup
        · exact ⟨⟨c, hcL⟩, (hmemQ _).2 hcR, rfl⟩
        · rintro _ ⟨r, hr, rfl⟩
          have h1 := Subgroup.mem_center_iff.1 hc ⟨r.1, (hmemQ r).1 hr⟩
          have h2 : r * (⟨c, hcL⟩ : ↥L) = ⟨c, hcL⟩ * r := Subtype.ext (by simpa using congrArg Subtype.val h1)
          rw [← map_mul, ← map_mul, h2]
      have hmem : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b)) ⟨c, hcC⟩ :
          ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) ∈ barX 3 (Cb b) (Subgroup.zpowers b) := by
        rw [← hZim]
        exact ⟨_, hcen', rfl⟩
      have hex : (c : G) ^ 3 = 1 := by
        have := hq3 ⟨c, hcL⟩ ((hmemQ _).2 hcR)
        exact congrArg Subtype.val this
      refine q_mem_zpowers_of_bar hbC (kb := 1) (by simpa using hb3) hcC (k := 1)
        (by simpa using hex) ?_ hmem
      have := hcC
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    · have hbR : b ∈ R0 :=
        (hmemQ _).1 (hNp.le_sylow_of_normal Q (Subgroup.mem_zpowers (⟨b, hbL⟩ : ↥L)))
      refine Subgroup.zpowers_le.2 ⟨⟨b, hbR⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      have := hL.1 (hR0L g.2)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this

theorem rData_of_inputs (i112 : Input11_2Four) (i302 : Input30_2) {m : ℕ}
    (hS : GLStanding G m 3) {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G}
    {L₁ L₂ L₃ : Subgroup G} (hT : Tri B b L₁ L₂ L₃) (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃)
    (hbK : b ∈ bClosure B L₁)
    (hZ : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L₁))
    (htype : IsSLThree (barOf 3 L₁) ∨ IsSUThree (barOf 3 L₁)) : RData B b L₁ L₂ L₃ := by
  obtain ⟨β, hβ, h2, h3, h1⟩ := hT.cyc
  have hbB : b ∈ B := hT.mem
  have hb1 : b ≠ 1 := hT.ne_one
  have hZ' : barX 3 (Cb b) (Subgroup.zpowers b) =
      (Subgroup.center ↥(barX 3 (Cb b) (bClosure B L₁))).map (barX 3 (Cb b) (bClosure B L₁)).subtype :=
    hZ
  have hc2 : bClosure B L₂ = bClosure B L₁ := by rw [h2]; exact t2_bClosure_conj hβ
  have hc3 : bClosure B L₃ = bClosure B L₁ := by rw [h3, t2_bClosure_conj hβ, hc2]
  have hn1 := t2_not_le_normalizer hβ h2 hT.ne₁₂
  have hn2 := t2_not_le_normalizer hβ h3 hT.ne₂₃
  have hn3 := t2_not_le_normalizer hβ h1 hT.ne₁₃.symm
  have ht2 := t2_type_conj h2 htype
  have ht3 := t2_type_conj h3 ht2
  have hK2 : bClosure B L₁ = L₂ ⊔ (L₁ ⊔ L₃) := by rw [hK]; ac_rfl
  have hK3 : bClosure B L₁ = L₃ ⊔ (L₁ ⊔ L₂) := by rw [hK]; ac_rfl
  have hK1 : bClosure B L₁ = L₁ ⊔ (L₂ ⊔ L₃) := by rw [hK, sup_assoc]
  obtain ⟨f1, e1, s1⟩ := t2_core i112 i302 hS hB hbB hb1 hT.comp₁ hT.comp₂ hT.comp₃ hT.ne₁₂ hT.ne₁₃ hn1
    rfl hK1 hZ' htype
  obtain ⟨f2, e2, s2⟩ := t2_core i112 i302 hS hB hbB hb1 hT.comp₂ hT.comp₁ hT.comp₃ hT.ne₁₂.symm hT.ne₂₃
    hn2 hc2 hK2 hZ' ht2
  obtain ⟨f3, e3, s3⟩ := t2_core i112 i302 hS hB hbB hb1 hT.comp₃ hT.comp₁ hT.comp₂ hT.ne₁₃.symm hT.ne₂₃.symm
    hn3 hc3 hK3 hZ' ht3
  exact ⟨hT, f1, f2, f3, e1, e2, e3, s1, s2, s3⟩

end T2Sec

section R1Sec

omit [Finite G] in
private theorem r1_cb_conj (c w : G) :
    Cb (c * w * c⁻¹) = GLBConj c⁻¹ (Cb w) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_inv]
  constructor
  · intro h
    calc c⁻¹ * y * c * w = c⁻¹ * (y * (c * w * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * w * c⁻¹) * y) * c := by rw [h]
      _ = w * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * w * c⁻¹) = c * ((c⁻¹ * y * c) * w) * c⁻¹ := by group
      _ = c * (w * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * w * c⁻¹ * y := by group

private theorem r1_transport {b c w : G} (hc : c * b = b * c) (h : b ∈ oPrimePOf 3 (Cb w)) :
    b ∈ oPrimePOf 3 (Cb (c * w * c⁻¹)) := by
  rw [r1_cb_conj, oPrimePOf_gLBConj, mem_gLBConj]
  have : c⁻¹ * b * c⁻¹⁻¹ = b := by
    rw [inv_inv]; calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = b := by rw [← hc]; group
  rwa [this]


omit [Finite G] in
private theorem r1_commute_of_B {B : Subgroup G} (hB : IsElemAbelian 3 B) {x y : G} (hx : x ∈ B)
    (hy : y ∈ B) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hB hx hy

private theorem r1_y2_step {b β : G} {A A' D D' : Subgroup G} (hβ : β * b = b * β)
    (hA : ∀ y, y ∈ A ↔ β * y * β⁻¹ ∈ A') (hD : ∀ y, y ∈ D ↔ β * y * β⁻¹ ∈ D')
    (h : Y2 b A' D') : Y2 b A D := by
  intro u hu v hv hc hu3 hv3 hnu hnv
  have hnz : ∀ x : G, β * x * β⁻¹ ∈ Subgroup.zpowers b → x ∈ Subgroup.zpowers b := by
    rintro x ⟨k, hk⟩
    have hcm : β * b ^ k = b ^ k * β := (Commute.zpow_right (show Commute β b from hβ) k).eq
    refine ⟨k, ?_⟩
    have hk' : β * x * β⁻¹ = b ^ k := hk.symm
    calc b ^ k = β⁻¹ * (β * b ^ k) := by group
      _ = β⁻¹ * (b ^ k * β) := by rw [hcm]
      _ = β⁻¹ * (β * x * β⁻¹) * β := by rw [hk']; group
      _ = x := by group
  have hmain := h (β * u * β⁻¹) ((hA u).1 hu) (β * v * β⁻¹) ((hD v).1 hv)
    (by calc β * u * β⁻¹ * (β * v * β⁻¹) = β * (u * v) * β⁻¹ := by group
          _ = β * (v * u) * β⁻¹ := by rw [hc]
          _ = β * v * β⁻¹ * (β * u * β⁻¹) := by group)
    (by rw [conj_pow, hu3]; group)
    (by rw [conj_pow, hv3]; group)
    (fun h' => hnu (hnz u h')) (fun h' => hnv (hnz v h'))
  have := r1_transport (b := b) (c := β⁻¹) (w := β * u * β⁻¹ * (β * v * β⁻¹))
    (by simpa using (Commute.inv_left (show Commute β b from hβ)).eq) hmain
  have e : β⁻¹ * (β * u * β⁻¹ * (β * v * β⁻¹)) * β⁻¹⁻¹ = u * v := by group
  rwa [e] at this

omit [Finite G] in
private theorem r1_ex_of_cb {b c : G} (hc : c ∈ Cb b) : c * b = b * c := by
  simpa using Subgroup.mem_centralizer_singleton_iff.1 hc


omit [Finite G] in
private theorem r1_mem_barX {C K : Subgroup G} {g : G} (hgC : g ∈ C) (hg : g ∈ K) :
    mkX C g hgC ∈ barX 3 C K :=
  ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩

omit [Finite G] in
private theorem r1_mkX_pow {C : Subgroup G} {g : G} (hgC : g ∈ C) (n : ℕ) :
    mkX C g hgC ^ n = mkX C (g ^ n) (pow_mem hgC n) := by
  unfold mkX
  rw [← QuotientGroup.mk_pow]
  rfl

omit [Finite G] in
private theorem r1_mkX_mul {C : Subgroup G} {g h : G} (hgC : g ∈ C) (hhC : h ∈ C) :
    mkX C g hgC * mkX C h hhC = mkX C (g * h) (mul_mem hgC hhC) := rfl

omit [Finite G] in
private theorem r1_card_sup_mul_card_inf {K : Type*} [Group K] {A B : Subgroup K}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let μ : A × B →* K :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hcomm x x.2 y y.2
  have hμ : ∀ x : A × B, μ x = (x.1 : K) * x.2 := fun _ => rfl
  have hrange : μ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card μ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : K), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : K)⁻¹, B.inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact B.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Subtype.ext (Prod.ext rfl (Subtype.ext h))
  have h := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at h
  rwa [mul_comm]

omit [Finite G] in
private theorem r1_mem_sup_of_comm {K : Type*} [Group K] {A B : Subgroup K}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x : K} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let μ : A × B →* K :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hcomm x x.2 y y.2
  have hrange : μ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, hab⟩ := hx
  exact ⟨a, a.2, b, b.2, hab⟩

omit [Finite G] in
private theorem r1_sylow_inf_normal {K : Type*} [Group K] [Finite K] (S : Sylow 3 K)
    {N : Subgroup K} [N.Normal] :
    ∃ P : Sylow 3 ↥N, (P : Subgroup ↥N) = ((S : Subgroup K) ⊓ N).subgroupOf N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  let P : Subgroup ↥N := ((S : Subgroup K) ⊓ N).subgroupOf N
  have hP1 : IsPGroup 3 P := by
    have hSn : IsPGroup 3 (↥((S : Subgroup K) ⊓ N)) := S.isPGroup'.to_inf_left
    exact hSn.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup K) ⊓ N) (K := N) inf_le_right).symm
  have hrel1 :
      ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) *
          (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) =
        ((S : Subgroup K) ⊓ N).relIndex ((S : Subgroup K) ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H := (S : Subgroup K) ⊓ N)
      (K := (S : Subgroup K)) (L := (S : Subgroup K) ⊔ N) inf_le_left le_sup_left
  have hrel2 :
      ((S : Subgroup K) ⊓ N).relIndex N * N.relIndex ((S : Subgroup K) ⊔ N) =
        ((S : Subgroup K) ⊓ N).relIndex ((S : Subgroup K) ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H := (S : Subgroup K) ⊓ N) (K := N)
      (L := (S : Subgroup K) ⊔ N) inf_le_right le_sup_right
  have h2a : N.relIndex ((S : Subgroup K) ⊔ N) = N.relIndex (S : Subgroup K) :=
    Subgroup.relIndex_sup_right (H := (S : Subgroup K)) (K := N)
  have h2a' : N.relIndex (S : Subgroup K) = ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) :=
    (Subgroup.inf_relIndex_left (H := (S : Subgroup K)) (K := N)).symm
  have hrel2' :
      ((S : Subgroup K) ⊓ N).relIndex N * ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) =
        ((S : Subgroup K) ⊓ N).relIndex ((S : Subgroup K) ⊔ N) := by
    simpa [h2a, h2a'] using hrel2
  have hcanc : ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) ≠ 0 := by
    intro hz
    have hdvd : ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) ∣
        ((S : Subgroup K) ⊓ N).index :=
      Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup K) ⊓ N)
        (K := (S : Subgroup K)) inf_le_left
    have hSne : ((S : Subgroup K) ⊓ N).index ≠ 0 :=
      (Subgroup.finiteIndex_of_finite (H := (S : Subgroup K) ⊓ N)).index_ne_zero
    exact hSne (eq_zero_of_zero_dvd (by simpa [hz] using hdvd))
  have hrel : ((S : Subgroup K) ⊓ N).relIndex N =
      (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) := by
    have h' : ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) *
          (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) =
        ((S : Subgroup K) ⊓ N).relIndex N *
          ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) :=
      hrel1.trans hrel2'.symm
    have h'' : (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) *
          ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) =
        ((S : Subgroup K) ⊓ N).relIndex N *
          ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) := by
      simpa [mul_comm] using h'
    exact (Nat.mul_right_cancel (m := ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K))
      (Nat.pos_of_ne_zero hcanc) h'').symm
  have hP2 : ¬ 3 ∣ P.index := by
    intro hp
    have hp' : 3 ∣ (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) := by
      change 3 ∣ ((S : Subgroup K) ⊓ N).relIndex N at hp
      rwa [hrel] at hp
    have hdvd : (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) ∣
        (S : Subgroup K).index :=
      Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup K))
        (K := (S : Subgroup K) ⊔ N) le_sup_left
    exact S.not_dvd_index (hp'.trans hdvd)
  exact ⟨hP1.toSylow hP2, rfl⟩

omit [Finite G] in
private theorem r1_card_sylow_inf_normal {K : Type*} [Group K] [Finite K] (S : Sylow 3 K)
    (N : Subgroup K) [N.Normal] :
    Nat.card ↥((S : Subgroup K) ⊓ N) = 3 ^ (Nat.card N).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ := r1_sylow_inf_normal S (N := N)
  have e2 : Nat.card ↥((S : Subgroup K) ⊓ N) =
      Nat.card ↥(((S : Subgroup K) ⊓ N).subgroupOf N) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  rw [e2, ← hP']
  exact Sylow.card_eq_multiplicity P'

omit [Finite G] in
private theorem r1_card_normal_mul {K : Type*} [Group K] (U V : Subgroup K) [U.Normal] [V.Normal]
    (hUV : U ⊔ V = ⊤) :
    Nat.card K * Nat.card ↥(U ⊓ V) = Nat.card ↥U * Nat.card ↥V := by
  have h1 : Nat.card ↥V * V.relIndex (U ⊔ V) = Nat.card ↥(U ⊔ V) := by
    have hmul := (V.subgroupOf (U ⊔ V)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : V ≤ U ⊔ V)).toEquiv] at hmul
    exact hmul
  have h2 : Nat.card ↥(U ⊓ V) * (U ⊓ V).relIndex U = Nat.card ↥U := by
    have hmul := ((U ⊓ V).subgroupOf U).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : U ⊓ V ≤ U)).toEquiv] at hmul
    exact hmul
  have h3 : V.relIndex (U ⊔ V) = (U ⊓ V).relIndex U := by
    rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_left]
  have h4 : Nat.card ↥(U ⊔ V) = Nat.card K := by
    rw [hUV]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [← h4, ← h1, ← h2, h3]
  ring

omit [Finite G] in
private theorem r1_abs {K : Type*} [Group K] [Finite K] (U V : Subgroup K) [U.Normal] [V.Normal]
    (hUV : U ⊔ V = ⊤)
    (hcomm : ∀ s ∈ U, ∀ t ∈ V, (∃ k : ℕ, (s * t * s⁻¹ * t⁻¹) ^ (3 ^ k) = 1) → s * t = t * s)
    {x : K} (hx : ∃ k : ℕ, x ^ (3 ^ k) = 1) :
    ∃ a ∈ U, ∃ b ∈ V, a * b = b * a ∧ (∃ k : ℕ, a ^ (3 ^ k) = 1) ∧ (∃ k : ℕ, b ^ (3 ^ k) = 1) ∧
      a * b = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    rintro ⟨g, n, rfl⟩
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, Subtype.ext ?_⟩
    simp only [OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  have hxS : x ∈ (S : Subgroup K) := hS (Subgroup.mem_zpowers x)
  have hpS : ∀ y ∈ (S : Subgroup K), ∃ k : ℕ, y ^ (3 ^ k) = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  set A : Subgroup K := (S : Subgroup K) ⊓ U with hA
  set B : Subgroup K := (S : Subgroup K) ⊓ V with hB
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    refine hcomm a ha.2 b hb.2 (hpS _ ?_)
    exact mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1)
  have hAB' : A ⊓ B = (S : Subgroup K) ⊓ (U ⊓ V) := by
    ext y
    simp only [hA, hB, Subgroup.mem_inf]
    tauto
  have hcA := r1_card_sylow_inf_normal S U
  have hcB := r1_card_sylow_inf_normal S V
  have hcI := r1_card_sylow_inf_normal S (U ⊓ V)
  have hprod := r1_card_sup_mul_card_inf hAB
  have hN := r1_card_normal_mul U V hUV
  have hpos : ∀ N : Subgroup K, Nat.card ↥N ≠ 0 := fun N => Nat.card_pos.ne'
  have hfac := congrArg (fun n => n.factorization 3) hN
  simp only [Nat.factorization_mul (Nat.card_pos.ne') (hpos _), Finsupp.add_apply] at hfac
  have hSc : Nat.card ↥(S : Subgroup K) = 3 ^ (Nat.card K).factorization 3 :=
    S.card_eq_multiplicity
  have hle : A ⊔ B ≤ (S : Subgroup K) := sup_le inf_le_left inf_le_left
  have heq : A ⊔ B = (S : Subgroup K) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hd : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hd
    rw [hprod, hAB', hSc, hcI, hcA, hcB, ← pow_add, ← pow_add, hfac]
  rw [← heq] at hxS
  obtain ⟨a, ha, b, hb, hab⟩ := r1_mem_sup_of_comm hAB hxS
  exact ⟨a, ha.2, b, hb.2, hAB a ha b hb, hpS a ha.1, hpS b hb.1, hab⟩

private theorem r1_p3_trivial {C : Subgroup G} {z : G} (hz : z ∈ P3 C) {k : ℕ}
    (hk : z ^ (3 ^ k) = 1) : z = 1 := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  have h1 : z' ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have h2 : orderOf z' ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf z' ∣ Nat.card (GLAPPrimeCore 3 ↥C) := by
    have := orderOf_dvd_natCard (⟨z', hz'⟩ : GLAPPrimeCore 3 ↥C)
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (GLAPPrimeCore 3 ↥C)) :=
    Nat.Coprime.pow_left k (coprime_card_gLAPPrimeCore_aux 3 ↥C)
  have h4 : orderOf z' = 1 := (hcop.coprime_dvd_left h2).eq_one_of_dvd h3
  have : z' = 1 := orderOf_eq_one_iff.1 h4
  simp [this]

private theorem r1_cube {C L : Subgroup G} {Z : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)}
    (hF : FusData (barX 3 C L) Z) {g : G} (hgL : g ∈ L) (hgC : g ∈ C)
    (hk : ∃ k : ℕ, g ^ (3 ^ k) = 1) : g ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hk
  have hmem := r1_mem_barX hgC hgL
  have h1 : mkX C g hgC ^ (3 ^ k) = 1 := by
    rw [r1_mkX_pow]
    simp only [hk]
    rfl
  have h3 := hF.exp3 _ hmem ⟨k, h1⟩
  rw [r1_mkX_pow] at h3
  have h4 : (⟨g ^ 3, pow_mem hgC 3⟩ : ↥C) ∈ GLAPPrimeCore 3 ↥C :=
    (QuotientGroup.eq_one_iff _).1 h3
  refine r1_p3_trivial (C := C) (k := k) ⟨_, h4, rfl⟩ ?_
  rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]

theorem r_conj {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {u u' v v' : G} (hu : u ∈ L₁) (hu' : u' ∈ L₁) (hv : v ∈ L₂) (hv' : v' ∈ L₂)
    (hc : u * v = v * u) (hc' : u' * v' = v' * u') (hu3 : u ^ 3 = 1) (hu'3 : u' ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (hv'3 : v' ^ 3 = 1) (hnu : u ∉ Subgroup.zpowers b)
    (hnu' : u' ∉ Subgroup.zpowers b) (hnv : v ∉ Subgroup.zpowers b)
    (hnv' : v' ∉ Subgroup.zpowers b) : ∃ c ∈ Cb b, c * (u * v) * c⁻¹ = u' * v' := by
  have hT := hR.tri
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hb3 : b ^ (3 ^ 1) = 1 := by simpa using hT.elemB.2 b hT.mem
  have hu1 : u ∈ Cb b := hT.comp₁.1 hu
  have hu1' : u' ∈ Cb b := hT.comp₁.1 hu'
  have hv1 : v ∈ Cb b := hT.comp₂.1 hv
  have hv1' : v' ∈ Cb b := hT.comp₂.1 hv'
  have hcomm : ∀ x ∈ barX 3 (Cb b) L₁, ∀ y ∈ barX 3 (Cb b) L₂, x * y = y * x := by
    have hle := barX_le_centralizer (p := 3) (C := Cb b) (S := L₁) (T := L₂) (by
      intro s hs t ht _ _
      exact commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₁ hT.comp₂ hT.ne₁₂
        (Subgroup.commutator_mem_commutator hs ht))
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm
  have hnz : ∀ {w : G} (hwC : w ∈ Cb b), w ^ 3 = 1 → w ∉ Subgroup.zpowers b →
      mkX (Cb b) w hwC ∉ barX 3 (Cb b) (Subgroup.zpowers b) := by
    intro w hwC hw3 hnw hmem
    exact hnw (q_mem_zpowers_of_bar hbC hb3 hwC (k := 1) (by simpa using hw3)
      (Subgroup.mem_centralizer_singleton_iff.1 hwC) hmem)
  have hpow : ∀ {w : G} (hwC : w ∈ Cb b), w ^ 3 = 1 →
      mkX (Cb b) w hwC ^ 3 = 1 := by
    intro w hwC hw3
    rw [r1_mkX_pow]
    simp only [hw3]
    rfl
  obtain ⟨cb, hcb, hceq⟩ := tc_two hR.fus₁ hR.fus₂ hcomm
    (r1_mem_barX hu1 hu) (r1_mem_barX hu1' hu') (r1_mem_barX hv1 hv) (r1_mem_barX hv1' hv')
    (hpow hu1 hu3) (hpow hu1' hu'3) (hpow hv1 hv3) (hpow hv1' hv'3)
    (hnz hu1 hu3 hnu) (hnz hu1' hu'3 hnu') (hnz hv1 hv3 hnv) (hnz hv1' hv'3 hnv')
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective cb
  let W : ↥(Cb b) := ⟨u * v, mul_mem hu1 hv1⟩
  let W' : ↥(Cb b) := ⟨u' * v', mul_mem hu1' hv1'⟩
  have hW3 : W ^ 3 = 1 := by
    apply Subtype.ext
    show (u * v) ^ 3 = 1
    rw [(show Commute u v from hc).mul_pow, hu3, hv3, one_mul]
  have hW'3 : W' ^ 3 = 1 := by
    apply Subtype.ext
    show (u' * v') ^ 3 = 1
    rw [(show Commute u' v' from hc').mul_pow, hu'3, hv'3, one_mul]
  have hcong : (c₀ * W * c₀⁻¹) * W'⁻¹ ∈ GLAPPrimeCore 3 ↥(Cb b) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      mul_inv_eq_one]
    exact hceq
  obtain ⟨n, hn, hne⟩ := g_conj_of_cong (p := 3) Nat.prime_three (GLAPPrimeCore 3 ↥(Cb b))
    (coprime_card_gLAPPrimeCore_aux 3 ↥(Cb b)) (u := c₀ * W * c₀⁻¹) (v := W')
    ⟨1, by rw [pow_one, conj_pow, hW3]; group⟩ ⟨1, by rw [pow_one, hW'3]⟩ hcong
  refine ⟨((n * c₀ : ↥(Cb b)) : G), (n * c₀).2, ?_⟩
  have := congrArg Subtype.val hne
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  calc (n : G) * c₀ * (u * v) * ((n : G) * c₀)⁻¹
      = (n : G) * (c₀ * (u * v) * (c₀ : G)⁻¹) * (n : G)⁻¹ := by group
    _ = u' * v' := this


theorem y2_of_exists {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {u₀ v₀ : G} (hu₀ : u₀ ∈ L₁) (hv₀ : v₀ ∈ L₂) (hc : u₀ * v₀ = v₀ * u₀) (hu3 : u₀ ^ 3 = 1)
    (hv3 : v₀ ^ 3 = 1) (hnu : u₀ ∉ Subgroup.zpowers b) (hnv : v₀ ∉ Subgroup.zpowers b)
    (hgood : b ∈ oPrimePOf 3 (Cb (u₀ * v₀))) : Y2 b L₁ L₂ := by
  intro u hu v hv hc' hu3' hv3' hnu' hnv'
  obtain ⟨c, hcC, hce⟩ := r_conj hR hu₀ hu hv₀ hv hc hc' hu3 hu3' hv3 hv3' hnu hnu' hnv hnv'
  rw [← hce]
  exact r1_transport (r1_ex_of_cb hcC) hgood

theorem y2_symm {b : G} {Li Lj : Subgroup G} (h : Y2 b Li Lj) : Y2 b Lj Li := by
  intro u hu v hv hc hu3 hv3 hnu hnv
  rw [hc]
  exact h v hv u hu hc.symm hv3 hu3 hnv hnu

theorem y2_cyc {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hT : Tri B b L₁ L₂ L₃)
    (h : Y2 b L₁ L₂) : Y2 b L₂ L₃ ∧ Y2 b L₃ L₁ := by
  obtain ⟨β, hβB, h21, h32, h13⟩ := hT.cyc
  have hβb : β * b = b * β := r1_commute_of_B hT.elemB hβB hT.mem
  have hm : ∀ {X Y : Subgroup G}, X = GLBConj β Y → ∀ y, y ∈ X ↔ β * y * β⁻¹ ∈ Y := by
    intro X Y hXY y
    rw [hXY, mem_gLBConj]
  have h23 : Y2 b L₂ L₃ := r1_y2_step hβb (hm h21) (hm h32) h
  refine ⟨h23, y2_symm ?_⟩
  exact r1_y2_step hβb (hm h13) (hm h32) (y2_symm h23)

theorem decomp_sylow {b : G} {Li Lj : Subgroup G} (hLi : GLAPComponent 3 (Cb b) Li)
    (hLj : GLAPComponent 3 (Cb b) Lj) (hne : Li ≠ Lj)
    (hfi : FusData (barX 3 (Cb b) Li) (barX 3 (Cb b) (Subgroup.zpowers b)))
    (hfj : FusData (barX 3 (Cb b) Lj) (barX 3 (Cb b) (Subgroup.zpowers b))) {x : G}
    (hx : x ∈ Li ⊔ Lj) (hx3 : x ^ 3 = 1) :
    ∃ c ∈ Li ⊔ Lj, ∃ u ∈ Li, ∃ v ∈ Lj, u * v = v * u ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧
      c * x * c⁻¹ = u * v := by
  set M : Subgroup G := Li ⊔ Lj with hM
  have hLiM : Li ≤ M := le_sup_left
  have hLjM : Lj ≤ M := le_sup_right
  have hLiN : Li ≤ Subgroup.normalizer (Lj : Set G) := q_le_normalizer_of_ne hLi hLj hne
  have hLjN : Lj ≤ Subgroup.normalizer (Li : Set G) := q_le_normalizer_of_ne hLj hLi hne.symm
  have hMi : M ≤ Subgroup.normalizer (Li : Set G) := sup_le Subgroup.le_normalizer hLjN
  have hMj : M ≤ Subgroup.normalizer (Lj : Set G) := sup_le hLiN Subgroup.le_normalizer
  have hU : (Li.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLiM).2 hMi
  have hV : (Lj.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLjM).2 hMj
  have hUV : Li.subgroupOf M ⊔ Lj.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLiM hLjM]
    exact Subgroup.subgroupOf_self M
  have hcomm : ∀ s ∈ Li.subgroupOf M, ∀ t ∈ Lj.subgroupOf M,
      (∃ k : ℕ, (s * t * s⁻¹ * t⁻¹) ^ (3 ^ k) = 1) → s * t = t * s := by
    intro s hs t ht ⟨k, hk⟩
    have hcm := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hLi hLj hne
      (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hs)
        (Subgroup.mem_subgroupOf.1 ht))
    have h1 : ((s : G) * t * (s : G)⁻¹ * (t : G)⁻¹) = 1 :=
      r1_p3_trivial hcm (k := k) (by simpa using congrArg Subtype.val hk)
    have h2 : s * t * s⁻¹ * t⁻¹ = 1 := Subtype.ext (by simpa using h1)
    calc s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
      _ = t * s := by rw [h2, one_mul]
  obtain ⟨a, ha, b', hb, hab, ⟨k1, hk1⟩, ⟨k2, hk2⟩, hx'⟩ :=
    r1_abs (Li.subgroupOf M) (Lj.subgroupOf M) hUV hcomm (x := (⟨x, hx⟩ : ↥M))
      ⟨1, Subtype.ext (by simpa using hx3)⟩
  have haL : (a : G) ∈ Li := Subgroup.mem_subgroupOf.1 ha
  have hbL : (b' : G) ∈ Lj := Subgroup.mem_subgroupOf.1 hb
  have ha3 : (a : G) ^ 3 = 1 :=
    r1_cube hfi haL (hLi.1 haL) ⟨k1, by simpa using congrArg Subtype.val hk1⟩
  have hb3 : (b' : G) ^ 3 = 1 :=
    r1_cube hfj hbL (hLj.1 hbL) ⟨k2, by simpa using congrArg Subtype.val hk2⟩
  refine ⟨1, one_mem _, a, haL, b', hbL, congrArg Subtype.val hab, ha3, hb3, ?_⟩
  have := congrArg Subtype.val hx'
  simpa using this.symm

end R1Sec

section JSec

theorem j_normal_le_center_or_top {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) (M : Subgroup Q)
    [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  have hs := hQ.2
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · left
    intro m hm
    have : QuotientGroup.mk' (Subgroup.center Q) m = 1 := by
      have : QuotientGroup.mk' (Subgroup.center Q) m ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
        h ▸ Subgroup.mem_map_of_mem _ hm
      simpa using this
    exact (QuotientGroup.eq_one_iff m).1 this
  · right
    have hcomm : commutator Q ≤ M := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      have h1 : QuotientGroup.mk' (Subgroup.center Q) g₁ ∈ M.map (QuotientGroup.mk' (Subgroup.center Q)) :=
        h ▸ Subgroup.mem_top _
      have h2 : QuotientGroup.mk' (Subgroup.center Q) g₂ ∈ M.map (QuotientGroup.mk' (Subgroup.center Q)) :=
        h ▸ Subgroup.mem_top _
      obtain ⟨m₁, hm₁, e₁⟩ := h1
      obtain ⟨m₂, hm₂, e₂⟩ := h2
      have c₁ : m₁⁻¹ * g₁ ∈ Subgroup.center Q := QuotientGroup.eq.1 e₁
      have c₂ : m₂⁻¹ * g₂ ∈ Subgroup.center Q := QuotientGroup.eq.1 e₂
      set z₁ := m₁⁻¹ * g₁ with hz₁
      set z₂ := m₂⁻¹ * g₂ with hz₂
      have eg₁ : g₁ = m₁ * z₁ := by simp [hz₁]
      have eg₂ : g₂ = m₂ * z₂ := by simp [hz₂]
      have hz₁c := Subgroup.mem_center_iff.1 c₁
      have hz₂c := Subgroup.mem_center_iff.1 c₂
      have : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
        rw [eg₁, eg₂]
        simp only [mul_inv_rev]
        have a1 : ∀ y : Q, z₁ * y = y * z₁ := fun y => (hz₁c y).symm
        have a2 : ∀ y : Q, z₂ * y = y * z₂ := fun y => (hz₂c y).symm
        calc m₁ * z₁ * (m₂ * z₂) * (z₁⁻¹ * m₁⁻¹) * (z₂⁻¹ * m₂⁻¹)
            = m₁ * (z₁ * (m₂ * z₂)) * (z₁⁻¹ * m₁⁻¹) * (z₂⁻¹ * m₂⁻¹) := by group
          _ = m₁ * ((m₂ * z₂) * z₁) * (z₁⁻¹ * m₁⁻¹) * (z₂⁻¹ * m₂⁻¹) := by rw [a1]
          _ = m₁ * m₂ * (z₂ * z₁ * z₁⁻¹) * m₁⁻¹ * (z₂⁻¹ * m₂⁻¹) := by group
          _ = m₁ * m₂ * z₂ * m₁⁻¹ * (z₂⁻¹ * m₂⁻¹) := by group
          _ = m₁ * m₂ * (z₂ * m₁⁻¹) * (z₂⁻¹ * m₂⁻¹) := by group
          _ = m₁ * m₂ * (m₁⁻¹ * z₂) * (z₂⁻¹ * m₂⁻¹) := by rw [a2]
          _ = m₁ * m₂ * m₁⁻¹ * (z₂ * z₂⁻¹) * m₂⁻¹ := by group
          _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
      rw [commutatorElement_def, this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hm₁ hm₂)
        (Subgroup.inv_mem _ hm₁)) (Subgroup.inv_mem _ hm₂)
    exact top_le_iff.1 (hQ.1 ▸ hcomm)

theorem j_core_bot {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hZ : Nat.card (Subgroup.center Q) = 3) : GLAPPrimeCore 3 Q = ⊥ := by
  refine le_bot_iff.1 (sSup_le ?_)
  rintro N ⟨hN, hcop⟩
  have := hN
  rcases j_normal_le_center_or_top hQ N with h | h
  · have hdvd : Nat.card N ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le h
    have h1 : Nat.card N = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
    exact le_bot_iff.2 (Subgroup.eq_bot_of_card_eq N h1)
  · exfalso
    subst h
    have h3 : 3 ∣ Nat.card Q := hZ ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center Q)
    rw [Subgroup.card_top] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

theorem j_comp_eq_top {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {S : Subgroup Q} (hS : IsComponentOf S ⊤) : S = ⊤ := by
  by_contra hne
  obtain ⟨M, hSM, hMA, hMne, hMn, -⟩ := isSubnormal_exists_normal hS.2.1 hne
  have : M.Normal := ⟨fun n hn g => by
    have := hMn.conj_mem (⟨n, trivial⟩ : (⊤ : Subgroup Q)) (Subgroup.mem_subgroupOf.2 hn)
      ⟨g, trivial⟩
    exact Subgroup.mem_subgroupOf.1 this⟩
  rcases j_normal_le_center_or_top hQ M with h | h
  · have hSc : S ≤ Subgroup.center Q := hSM.trans h
    have hnt : Nontrivial (↥S ⧸ Subgroup.center ↥S) := hS.2.2.2.toNontrivial
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥S ⧸ Subgroup.center ↥S)
    induction q using QuotientGroup.induction_on with
    | H s =>
      refine hq ((QuotientGroup.eq_one_iff s).2 ?_)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hSc s.2) g)
  · exact hMne h

theorem j_comp_A {C A : Subgroup G} (hAC : A ≤ C)
    (hq : CFSG.Open.IsQuasisimple ↥(barX 3 C A)) (hbot : GLAPPrimeCore 3 ↥(barX 3 C A) = ⊥) :
    GLAPPrimeCoreOf 3 A ≤ P3 C ∧ ∃ J : Subgroup G, GLAPComponent 3 A J ∧ barX 3 A J = ⊤ ∧
      ∀ J', GLAPComponent 3 A J' → J' = J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set f := barMap 3 hAC with hf
  have hsurj : Function.Surjective f := barMap_surjective hAC
  have hker : ∀ a : ↥A, f a = 1 ↔ (a : G) ∈ P3 C := by
    intro a
    constructor
    · intro h
      have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (Subgroup.inclusion hAC a) = 1 :=
        congrArg Subtype.val h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    · rintro ⟨c, hc, hca⟩
      have hc' : Subgroup.inclusion hAC a = c := Subtype.ext hca.symm
      refine Subtype.ext ?_
      change QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (Subgroup.inclusion hAC a) = 1
      rw [hc', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
    refine not_dvd_card_glaPPrimeCoreOf hp C (hd.trans ?_)
    have hc : Nat.card (f.ker.map A.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [← hc]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (hker a).1 ha
  have hmap := glaPPrimeCore_map_of_surjective hp f hsurj hcop
  rw [hbot] at hmap
  have hcoreker : GLAPPrimeCore 3 ↥A = f.ker := by
    refine le_antisymm (fun a ha => ?_) (le_sSup ⟨inferInstance, hcop⟩)
    rw [MonoidHom.mem_ker]
    have : f a ∈ (GLAPPrimeCore 3 ↥A).map f := Subgroup.mem_map_of_mem _ ha
    rw [hmap] at this
    simpa using this
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hcoreker] at ha
    exact (hker a).1 ha
  · let e : (↥A ⧸ GLAPPrimeCore 3 ↥A) ≃* ↥(barX 3 C A) :=
      (QuotientGroup.quotientMulEquivOfEq hcoreker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
    have hQA : CFSG.Open.IsQuasisimple (↥A ⧸ GLAPPrimeCore 3 ↥A) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
    have hcompTop : IsComponentOf (⊤ : Subgroup (↥A ⧸ GLAPPrimeCore 3 ↥A)) ⊤ :=
      ⟨le_rfl, IsSubnormal.refl _,
        CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
          (Subgroup.topEquiv (G := ↥A ⧸ GLAPPrimeCore 3 ↥A)).symm hQA⟩
    obtain ⟨J, hJ, hJbar⟩ := exists_glaPComponent_barX_eq (p := 3) A hcompTop
    refine ⟨J, hJ, hJbar, fun J' hJ' => ?_⟩
    have h' : IsComponentOf (barX 3 A J') ⊤ := hJ'.2.2.1
    exact glaPComponent_unique hJ' hJ ((j_comp_eq_top hQA h').trans hJbar.symm)

omit [Finite G] in
theorem j_gLBConj_self {g : G} {X : Subgroup G} (hg : g ∈ X) : GLBConj g X = X := by
  ext y
  rw [mem_gLBConj]
  constructor
  · intro h
    have := X.mul_mem (X.mul_mem (X.inv_mem hg) h) hg
    simpa [mul_assoc] using this
  · intro h
    exact X.mul_mem (X.mul_mem hg h) (X.inv_mem hg)

theorem j_normalizes {X L : Subgroup G} (hL : GLAPComponent 3 X L) {x : G} (hxX : x ∈ X)
    (hxL : ⁅L, Subgroup.zpowers x⁆ ≤ P3 X) : x ∈ Subgroup.normalizer (L : Set G) := by
  have hL' : GLAPComponent 3 X (GLBConj x L) := by
    have := glaPComponent_gLBConj x hL
    rwa [j_gLBConj_self hxX] at this
  have hLX : L ≤ X := hL.1
  have hL'X : GLBConj x L ≤ X := hL'.1
  have hbar : barX 3 X (GLBConj x L) = barX 3 X L := by
    refine le_antisymm ?_ ?_
    · refine barX_le_of_forall hLX (fun k hk => ?_)
      have hl : x * k * x⁻¹ ∈ L := mem_gLBConj.1 hk
      refine ⟨x * k * x⁻¹, hl, ?_⟩
      have hc := Subgroup.commutator_mem_commutator (L.inv_mem hl)
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
      have := hxL hc
      rw [commutatorElement_def] at this
      convert this using 1
      group
    · refine barX_le_of_forall hL'X (fun k hk => ?_)
      refine ⟨x⁻¹ * k * x, ?_, ?_⟩
      · rw [mem_gLBConj]
        have e : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
        rw [e]
        exact hk
      · have hc := Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
            (L.inv_mem hk)
        rw [Subgroup.commutator_comm] at hc
        have := hxL hc
        rw [commutatorElement_def] at this
        convert this using 1
        group
  exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hL' hL hbar)

omit [Finite G] in
theorem j_isPGroup_zpowers {x : G} (hx : x ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers x) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  apply Subtype.ext
  show (g : G) ^ (3 ^ 1) = 1
  rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hx]

theorem j_barX_A {C L : Subgroup G} (hLC : L ≤ C) {x : G} (hxC : x ∈ C) (hx3 : x ^ 3 = 1)
    (hxn : x ∈ Subgroup.normalizer (L : Set G)) (hxL : ⁅L, Subgroup.zpowers x⁆ ≤ P3 C) :
    barX 3 C (L ⊓ Subgroup.centralizer ({x} : Set G)) = barX 3 C L := by
  rw [barX_inf_centralizer Nat.prime_three hxC hLC hxn (j_isPGroup_zpowers hx3)]
  refine inf_eq_left.2 ?_
  have h1 := barX_le_centralizer (p := 3) (C := C) (S := L) (T := Subgroup.zpowers x)
    (fun s hs t ht _ _ => by
      have hc := Subgroup.commutator_mem_commutator hs ht
      rw [commutatorElement_def] at hc
      exact hxL hc)
  refine h1.trans (Subgroup.centralizer_le ?_)
  rintro _ rfl
  exact ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x), rfl⟩

theorem j_comp_up {A W J : Subgroup G} (hJ : GLAPComponent 3 A J) (hAW : IsSubnormal A W) :
    GLAPComponent 3 W J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hJA, hsn, hcomp, hmin⟩ := hJ
  have hAW' : A ≤ W := isSubnormal_le' hAW
  have hJW : J ≤ W := hJA.trans hAW'
  have hsnW : IsSubnormal J W := isSubnormal_trans' hsn hAW
  refine ⟨hJW, hsnW, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := W) 3 hsnW
    rwa [barX_self] at this
  · have e : ↥(barX 3 A J) ≃* ↥(barX 3 W J) :=
      (quotEquivBarX hp hJA hsn).symm.trans (quotEquivBarX hp hJW hsnW)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J' hJ' hJ'sn heq
    have hJ'J : J' ≤ J := hJ'.le
    have hJ'A : IsSubnormal J' A := isSubnormal_of_le_of_le hJ'sn (hJ'J.trans hJA) hAW'
    have hcore : J ⊓ GLAPPrimeCoreOf 3 W ≤ GLAPPrimeCoreOf 3 A := by
      have := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hAW
      rintro y ⟨hyJ, hyP⟩
      rw [← this]
      exact ⟨hJA hyJ, hyP⟩
    refine hmin J' hJ' hJ'A ?_
    show barX 3 A J' = barX 3 A J
    refine le_antisymm (barX_mono 3 hJ'J) ?_
    refine barX_le_of_forall (hJ'J.trans hJA) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := W) (le_of_eq heq.symm) hk (hJW hk)
    exact ⟨j, hj, hcore ⟨J.mul_mem (J.inv_mem (hJ'J hj)) hk, hjk⟩⟩

theorem j_center_card {H : Type*} [Group H] {Q Z : Subgroup H} (h : FusData Q Z) :
    Nat.card (Subgroup.center ↥Q) = 3 := by
  have e : Subgroup.center ↥Q = Z.subgroupOf Q := by
    ext z
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, h.Zcenter]
    constructor
    · intro hz
      refine ⟨z.2, fun q hq => ?_⟩
      have := hz ⟨q, hq⟩
      exact (congrArg Subtype.val this).symm
    · rintro ⟨-, hz⟩ g
      exact Subtype.ext (hz g g.2).symm
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Zle).toEquiv]
  exact h.Zcard

omit [Finite G] in
theorem j_ne_one {C : Subgroup G} {b : G} (h : Nat.card (barX 3 C (Subgroup.zpowers b)) = 3) :
    b ≠ 1 := by
  rintro rfl
  rw [Subgroup.zpowers_one_eq_bot] at h
  have : barX 3 C ⊥ = ⊥ := by simp [barX]
  rw [this] at h
  simp at h

omit [Finite G] in
theorem j_centralizer_zpowers (b : G) :
    Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) = Cb b := by
  ext y
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h b (Subgroup.mem_zpowers b)).symm
  · intro h g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute b y from h.symm) n)).eq

omit [Finite G] in
theorem j_isElemAbelian_zpowers {b : G} (hb : b ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers b) := CFSG.Open.isElemAbelian_zpowers hb

theorem jstar (i183 : Input18_3_4) {m : ℕ} (hS : GLStanding G m 3) {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Cb b) L) (hbL : b ∈ L) (hb3 : b ^ 3 = 1)
    (hfus : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) {x : G}
    (hxC : x ∈ Cb b) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxL : ⁅L, Subgroup.zpowers x⁆ ≤ P3 (Cb b)) :
    GLAPComponent 3 (Cb b ⊓ Cb x) (GLAPLayer 3 (L ⊓ Cb x)) ∧ b ∈ GLAPLayer 3 (L ⊓ Cb x) ∧
      barX 3 (Cb b) (GLAPLayer 3 (L ⊓ Cb x)) = barX 3 (Cb b) L ∧
      GLAPComponent 3 (Cb x) (⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g (GLAPLayer 3 (L ⊓ Cb x))) ∧
      GLAPLayer 3 (L ⊓ Cb x) ≤ ⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g (GLAPLayer 3 (L ⊓ Cb x)) ∧
      GLAPComponent 3
        ((⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g (GLAPLayer 3 (L ⊓ Cb x))) ⊓ Cb b)
        (GLAPLayer 3 (L ⊓ Cb x)) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hLC : L ≤ Cb b := hL.1
  have hxn : x ∈ Subgroup.normalizer (L : Set G) := j_normalizes hL hxC hxL
  have hbarA := j_barX_A hLC hxC hx3 hxn hxL
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cb b) (L ⊓ Cb x)) := by
    rw [hbarA]; exact hL.2.2.1.2.2
  have hbot : GLAPPrimeCore 3 ↥(barX 3 (Cb b) (L ⊓ Cb x)) = ⊥ := by
    rw [hbarA]; exact j_core_bot hL.2.2.1.2.2 (j_center_card hfus)
  have hAC : L ⊓ Cb x ≤ Cb b := inf_le_left.trans hLC
  obtain ⟨hcore, J, hJ, hJtop, hJuniq⟩ := j_comp_A hAC hq hbot
  have hlayer : GLAPLayer 3 (L ⊓ Cb x) = J := by
    unfold GLAPLayer
    have : {L' | GLAPComponent 3 (L ⊓ Cb x) L'} = {J} :=
      Set.ext fun L' => ⟨fun h => hJuniq L' h, fun h => (Set.mem_singleton_iff.1 h) ▸ hJ⟩
    rw [this, sSup_singleton]
  rw [hlayer]
  have hJA : J ≤ L ⊓ Cb x := hJ.1
  have hAW : IsSubnormal (L ⊓ Cb x) (Cb b ⊓ Cb x) := isSubnormal_inf hL.2.1 (Cb x)
  have hJW : GLAPComponent 3 (Cb b ⊓ Cb x) J := j_comp_up hJ hAW
  have hbA : b ∈ L ⊓ Cb x :=
    ⟨hbL, Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm⟩
  have hbJ : b ∈ J := by
    refine q_mem_of_bar hJ hbA (k := 1) (by simpa using hb3) ?_
    rw [hJtop]
    exact Subgroup.mem_top _
  have hbarJ : barX 3 (Cb b) J = barX 3 (Cb b) L := by
    refine le_antisymm (barX_mono 3 (hJA.trans inf_le_left)) ?_
    rw [← hbarA]
    refine barX_le_of_forall (hJA.trans hAC) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := L ⊓ Cb x) (J := J) (K := L ⊓ Cb x)
      (by rw [hJtop, barX_self]) hk hk
    exact ⟨j, hj, hcore hjk⟩
  have hbne : b ≠ 1 := j_ne_one hfus.Zcard
  have hsimple : IsSimpleGroup G := hS.simple
  have hXne : Cb x ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hx1
  have hK := isKGroup_of_isKProper hS.kProper hXne
  have hbX : b ∈ Cb x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm
  have hE : Subgroup.zpowers b ≤ Cb x := Subgroup.zpowers_le.2 hbX
  have hJ1 : GLAPComponent 3 (Cb x ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) J := by
    rw [j_centralizer_zpowers, inf_comm]
    exact hJW
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ :=
    i183 G (Cb x) hK 3 hp3 (Subgroup.zpowers b) hE (j_isElemAbelian_zpowers hb3) J hJ1
  set Js : Subgroup G := ⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g J with hJs
  have hJJs : J ≤ Js := by
    refine le_trans ?_ (le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cb x)) => GLBConj g J) 1
      (Subgroup.one_mem _))
    rw [gLBConj_one]
  have hCne : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    subst h
    have h0 : Js = ⊥ := by rw [← hC2]; simp
    have : b ∈ (⊥ : Subgroup G) := h0 ▸ hJJs hbJ
    exact hbne (Subgroup.mem_bot.1 this)
  obtain ⟨L₀, hL₀⟩ := hCne
  have hnorm : ∀ L' ∈ 𝒞, L' ≤ Subgroup.normalizer (L₀ : Set G) := by
    intro L' hL'
    by_cases h : L' = L₀
    · subst h
      exact Subgroup.le_normalizer
    · exact q_le_normalizer_of_ne (hC1 L' hL') (hC1 L₀ hL₀) h
  have hJsn : Js ≤ Subgroup.normalizer (L₀ : Set G) := by
    rw [← hC2]
    exact iSup₂_le hnorm
  have hEn : Subgroup.zpowers b ≤ Subgroup.normalizer (L₀ : Set G) :=
    Subgroup.zpowers_le.2 (hJsn (hJJs hbJ))
  have heq : ∀ L' ∈ 𝒞, L' = L₀ := by
    intro L' hL'
    obtain ⟨e, he, hee⟩ := hC4 L₀ hL₀ L' hL'
    rw [← hee]
    exact gLBConj_eq_of_mem_normalizer (hEn he)
  have hJsL : Js = L₀ := by
    rw [← hC2]
    exact le_antisymm (iSup₂_le fun L' hL' => (heq L' hL').le)
      (le_iSup₂_of_le L₀ hL₀ le_rfl)
  have h4 : GLAPComponent 3 (Cb x) Js := hJsL ▸ hC1 L₀ hL₀
  refine ⟨hJW, hbJ, hbarJ, h4, hJJs, ?_⟩
  exact glaPComponent_of_le hp3 hJW
    (le_inf hJJs (hJA.trans (inf_le_left.trans hLC)))
    (le_inf inf_le_right (inf_le_left.trans h4.1))

end JSec

section S1TSec

theorem s1t_isKGroup_of_subgroup {X : Type*} [Group X] (hX : CFSG.Open.IsKGroup X)
    (H : Subgroup X) : CFSG.Open.IsKGroup ↥H :=
  hX.subgroup H

theorem s1t_isKGroup_quotient {X : Type*} [Group X] (hX : CFSG.Open.IsKGroup X) (M : Subgroup X)
    [M.Normal] : CFSG.Open.IsKGroup (X ⧸ M) :=
  hX.quotient M


theorem s1t_isComponentOf_top {Y : Type*} [Group Y] {C J : Subgroup Y}
    (hJ : IsComponentOf J C) : IsComponentOf (J.subgroupOf C) (⊤ : Subgroup ↥C) := by
  refine ⟨le_top, ?_, ?_⟩
  · have := isSubnormal_comap' C.subtype hJ.2.1
    rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hJ.1).symm hJ.2.2

theorem s1t_comm_of_ne {Y : Type*} [Group Y] [Finite Y] {C J J' : Subgroup Y}
    (hJ : IsComponentOf J C) (hJ' : IsComponentOf J' C) (hne : J ≠ J') : ⁅J, J'⁆ = ⊥ := by
  have hne' : J.subgroupOf C ≠ J'.subgroupOf C := by
    intro h
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hJ.1, ← Subgroup.map_subgroupOf_eq_of_le hJ'.1, h]
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    (s1t_isComponentOf_top hJ) (s1t_isComponentOf_top hJ') hne'
  rw [← subgroupOf_commutator hJ.1 hJ'.1] at h
  have h2 := congrArg (Subgroup.map C.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le (commutator_le_of_le' hJ.1 hJ'.1)] at h2
  simpa using h2

theorem s1t_isQuasisimple {Y : Type*} [Group Y] [Finite Y] {C J : Subgroup Y}
    (hJ : GLAPComponent 3 C J)
    (hcomm : ⁅GLAPLayer 3 C, GLAPPrimeCoreOf 3 C⁆ = ⊥) : CFSG.Open.IsQuasisimple ↥J := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hPcJ : ⁅J, GLAPPrimeCoreOf 3 J⁆ = ⊥ := by
    refine le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono (le_sSup hJ) ?_)
    exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp hJ.2.1
  set Pc : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hPc
  have hcent : ∀ u ∈ Pc, ∀ g : ↥J, g * u = u * g := by
    intro u hu g
    have hmem := Subgroup.commutator_mem_commutator (g₁ := (g : Y)) (g₂ := (u : Y))
      (H₁ := J) (H₂ := GLAPPrimeCoreOf 3 J) g.2 ⟨u, hu, rfl⟩
    rw [hPcJ, Subgroup.mem_bot, commutatorElement_def] at hmem
    apply Subtype.ext
    have h1 : (g : Y) * u * (g : Y)⁻¹ * (u : Y)⁻¹ = 1 := hmem
    have h2 : (g : Y) * u * (g : Y)⁻¹ = u := by
      have := mul_inv_eq_one.1 h1
      exact this
    calc ((g * u : ↥J) : Y) = (g : Y) * u := rfl
      _ = (u : Y) * g := by
        have := congrArg (· * (g : Y)) h2
        simpa [mul_assoc] using this
      _ = ((u * g : ↥J) : Y) := rfl
  have hPcle : Pc ≤ Subgroup.center ↥J := fun u hu =>
    Subgroup.mem_center_iff.2 fun g => hcent u hu g
  have hperfJ : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = (⊤ : Subgroup ↥J) := by
    have := subgroupOf_commutator (X := J) (A := J) (B := J) le_rfl le_rfl
    rw [hperf, Subgroup.subgroupOf_self] at this
    exact this.symm
  have hcenter : (Subgroup.center ↥J).map (QuotientGroup.mk' Pc) =
      Subgroup.center (↥J ⧸ Pc) := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine Subgroup.mem_center_iff.2 fun q => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      show QuotientGroup.mk' Pc g * QuotientGroup.mk' Pc z =
        QuotientGroup.mk' Pc z * QuotientGroup.mk' Pc g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
    · intro w hw
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
      refine ⟨j, ?_, rfl⟩
      have h1 : ⁅(⊤ : Subgroup ↥J), Subgroup.zpowers j⁆ ≤ Pc := by
        rw [Subgroup.commutator_le]
        intro g _ k hk
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        rw [← QuotientGroup.eq_one_iff (N := Pc), commutatorElement_def]
        have hz : (QuotientGroup.mk j : ↥J ⧸ Pc) ^ n ∈ Subgroup.center (↥J ⧸ Pc) :=
          Subgroup.zpow_mem _ hw n
        have hc := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk g)
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
        rw [hc]
        group
      have h2 : ⁅⁅(⊤ : Subgroup ↥J), Subgroup.zpowers j⁆, (⊤ : Subgroup ↥J)⁆ = ⊥ := by
        refine le_bot_iff.1 ?_
        rw [Subgroup.commutator_le]
        intro x hx g _
        have hx' := h1 hx
        have := hcent x hx' g
        rw [commutatorElement_def]
        simp [this.symm]
      have h3 : ⁅⁅Subgroup.zpowers j, (⊤ : Subgroup ↥J)⁆, (⊤ : Subgroup ↥J)⁆ = ⊥ := by
        rw [Subgroup.commutator_comm (Subgroup.zpowers j) (⊤ : Subgroup ↥J)]
        exact h2
      have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate
        (H₁ := (⊤ : Subgroup ↥J)) (H₂ := ⊤) (H₃ := Subgroup.zpowers j) h2 h3
      rw [hperfJ] at h4
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have hm := Subgroup.commutator_mem_commutator (g₁ := g) (g₂ := j) (H₁ := ⊤)
        (H₂ := Subgroup.zpowers j) (Subgroup.mem_top g) (Subgroup.mem_zpowers j)
      rw [h4, Subgroup.mem_bot, commutatorElement_def] at hm
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hm)
  have hsimple := (isQuasisimple_quotient_of_glaPComponent hJ).2
  have : ((Subgroup.center ↥J).map (QuotientGroup.mk' Pc)).Normal := hcenter ▸ inferInstance
  have hsimple' : IsSimpleGroup ((↥J ⧸ Pc) ⧸ (Subgroup.center ↥J).map (QuotientGroup.mk' Pc)) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).isSimpleGroup_congr.2 hsimple
  exact ⟨by rw [commutator_def]; exact hperfJ,
    ((QuotientGroup.quotientQuotientEquivQuotient Pc (Subgroup.center ↥J) hPcle).isSimpleGroup_congr).1
      hsimple'⟩

theorem s1t_isQuasisimple_of_open {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hp : Group.IsPerfect Q := ⟨hQ.1⟩
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  refine ⟨hp, hQ.2, ?_⟩
  have h := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using h

theorem s1t_isKGroup_of_open {X : Type} [Group X] [Finite X] (h : CFSG.Open.IsKGroup X) :
    CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple h

theorem s1t_map_cent {H : Type*} [Group H] [Finite H] {y : H} (hy : y ^ 3 = 1) :
    (Subgroup.centralizer ({y} : Set H)).map (QuotientGroup.mk' (GLAPPrimeCore 3 H)) =
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 H) y} :
        Set (H ⧸ GLAPPrimeCore 3 H)) := by
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← map_mul, ← map_mul, hg']
  · intro hw
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    have hg : g * y * g⁻¹ * y⁻¹ ∈ GLAPPrimeCore 3 H := by
      rw [← QuotientGroup.eq_one_iff (N := GLAPPrimeCore 3 H)]
      have hw' : (QuotientGroup.mk g : H ⧸ GLAPPrimeCore 3 H) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk g := hw
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hw']
      group
    obtain ⟨n, hn, hc⟩ := g_lift_centralizer Nat.prime_three (GLAPPrimeCore 3 H)
      (coprime_card_gLAPPrimeCore_aux 3 H) ⟨1, by simpa using hy⟩ hg
    refine ⟨g * n, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 hc
    · show QuotientGroup.mk (g * n) = (QuotientGroup.mk g : H ⧸ GLAPPrimeCore 3 H)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, mul_one]

theorem s1t_inducesFieldAut {Y : Type*} [Group Y] (J : Subgroup Y) {a : Y}
    (h : a ∈ Subgroup.centralizer (J : Set Y)) : InducesFieldAut 3 J a := by
  have hn : a ∈ Subgroup.normalizer (J : Set Y) := Subgroup.centralizer_le_normalizer _ h
  refine ⟨hn, Or.inl ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk]
    show QuotientGroup.mk _ = QuotientGroup.mk x
    congr 1
    apply Subtype.ext
    have hx : (x : Y) * a = a * x := by
      exact Subgroup.mem_centralizer_iff.1 h x x.2
    show a * (x : Y) * a⁻¹ = x
    rw [← hx]; group

theorem s1t_isSL3Eps_of_equiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : IsSL3Eps X) : IsSL3Eps X' := by
  obtain ⟨hty, hc⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hty with ⟨K, hf, hfin, ⟨f⟩⟩ | ⟨K, hf, hfin, q, hq, ⟨f⟩⟩
    · exact Or.inl ⟨K, hf, hfin, ⟨e.symm.trans f⟩⟩
    · exact Or.inr ⟨K, hf, hfin, q, hq, ⟨e.symm.trans f⟩⟩
  · rwa [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]

theorem s1t_center_map {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨g', rfl⟩ := e.surjective g
    show e g' * e x = e x * e g'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g']
  · intro hz
    refine ⟨e.symm z, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz (e g)

theorem s1t_ker_pi {H : Type*} [Group H] [Finite H] (S : Subgroup H) :
    Nat.Coprime 3 (Nat.card ↥(S ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 H)).ker)) := by
  have h1 : Nat.card ↥(S ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 H)).ker) ∣
      Nat.card (GLAPPrimeCore 3 H) := by
    have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 H)).ker = GLAPPrimeCore 3 H :=
      QuotientGroup.ker_mk' _
    have h2 : Nat.card ↥(QuotientGroup.mk' (GLAPPrimeCore 3 H)).ker =
        Nat.card (GLAPPrimeCore 3 H) := by rw [hker]
    rw [← h2]
    exact Subgroup.card_dvd_of_le inf_le_right
  exact (coprime_card_gLAPPrimeCore_aux 3 H).coprime_dvd_right h1

theorem s1t_ker_sub {G' : Type*} [Group G'] (Js : Subgroup G') (S : Subgroup ↥Js) :
    Nat.Coprime 3 (Nat.card ↥(S ⊓ (Js.subtype).ker)) := by
  rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right _

theorem s1t_zpow_three {M : Type*} [Group M] {x : M} (hx : x ^ 3 = 1) (i : ℤ) :
    (x ^ i) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem s1t_mem_zpowers_of_prime {M : Type*} [Group M] {x z : M} (hx : orderOf x = 3)
    (hz : z ∈ Subgroup.zpowers x) (hz1 : z ≠ 1) : x ∈ Subgroup.zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hmod : x ^ k = x ^ (k % 3) := by
    have := zpow_mod_orderOf x k
    rw [hx] at this
    simpa using this.symm
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h
  · exact absurd (by rw [hmod, h, zpow_zero]) hz1
  · refine Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩
    rw [hmod, h]; simp
  · refine Subgroup.mem_zpowers_iff.2 ⟨2, ?_⟩
    rw [hmod, h]
    calc ((x ^ (2 : ℤ)) ^ (2 : ℤ)) = x ^ (4 : ℤ) := by rw [← zpow_mul]; norm_num
      _ = x ^ 3 * x := by rw [show (4 : ℤ) = 3 + 1 by norm_num, zpow_add, zpow_one]; simp
      _ = x := by rw [h3, one_mul]

theorem s1_tilde (i145 : Input14_5) (i253 : Input25_3) {m : ℕ} (hS : GLStanding G m 3) {b : G} (hb3 : orderOf b = 3)
    {x : G} (hx1 : x ≠ 1) {Js J₁ J₂ : Subgroup G} (hJs : GLAPComponent 3 (Cb x) Js)
    (h₁ : GLAPComponent 3 (Js ⊓ Cb b) J₁) (h₂ : GLAPComponent 3 (Js ⊓ Cb b) J₂) (hne : J₁ ≠ J₂)
    (hb₁ : b ∈ J₁) (hb₂ : b ∈ J₂) (hε₁ : IsSL3Eps (barOf 3 J₁))
    (hZ₁ : Subgroup.center (barOf 3 J₁) = Subgroup.zpowers (QuotientGroup.mk (⟨b, hb₁⟩ : ↥J₁)))
    (hn₂ : ∃ a ∈ J₂, a ^ 3 = 1 ∧ a ∉ Subgroup.zpowers b) :
    ∃ y ∈ J₂, y ^ 3 = 1 ∧ y ∉ Subgroup.zpowers b ∧ b ∉ oPrimePOf 3 (Js ⊓ Cb y) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hJ₂le : J₂ ≤ Js ⊓ Cb b := h₂.1
  have hbJs : b ∈ Js := (h₁.1 hb₁).1
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hJsne : Js ≠ ⊤ := by
    intro htop
    have hCx : Cb x = ⊤ := top_le_iff.1 (htop ▸ hJs.1)
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cb x := hCx ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact hx1 (Subgroup.mem_bot.1 (h ▸ hxc))
    · obtain ⟨u, v, huv⟩ := hS.nonabelian
      exact huv (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top u) v).symm
  set b' : ↥Js := ⟨b, hbJs⟩ with hb'
  set A_H : Subgroup ↥Js := Subgroup.centralizer ({b'} : Set ↥Js) with hAH
  have hAmap : A_H.map Js.subtype = Js ⊓ Cb b := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    · rintro ⟨hgJ, hgC⟩
      exact ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)), rfl⟩
  obtain ⟨J₁', hJ₁', rfl⟩ := exists_glaPComponent_map_eq hp Js.subtype (s1t_ker_sub Js A_H)
    (K' := J₁) (by rw [hAmap]; exact h₁)
  obtain ⟨J₂', hJ₂', rfl⟩ := exists_glaPComponent_map_eq hp Js.subtype (s1t_ker_sub Js A_H)
    (K' := J₂) (by rw [hAmap]; exact h₂)
  set π : ↥Js →* (↥Js ⧸ GLAPPrimeCore 3 ↥Js) := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Js) with hπ
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3')
  have hbt3 : π b' ^ 3 = 1 := by rw [← map_pow, hb'3, map_one]
  have hbt1 : π b' ≠ 1 := by
    intro h1
    have hmem : b' ∈ GLAPPrimeCore 3 ↥Js := (QuotientGroup.eq_one_iff b').1 h1
    have hord : orderOf b' = 3 := orderOf_eq_prime hb'3 (by
      intro h
      have h' : b = 1 := congrArg Subtype.val h
      rw [h'] at hb3
      simp at hb3)
    have h2 : orderOf (⟨b', hmem⟩ : ↥(GLAPPrimeCore 3 ↥Js)) = 3 := by
      rw [Subgroup.orderOf_mk, hord]
    have h3 : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥Js) :=
      Dvd.dvd.trans (by rw [h2]) (orderOf_dvd_natCard (⟨b', hmem⟩ : ↥(GLAPPrimeCore 3 ↥Js)))
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_gLAPPrimeCore_aux 3 ↥Js) h3
  have hbtord : orderOf (π b') = 3 := orderOf_eq_prime hbt3 hbt1
  set CY : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js) :=
    Subgroup.centralizer ({π b'} : Set (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) with hCY
  have hAπ : A_H.map π = CY := s1t_map_cent hb'3
  have hKJs : CFSG.Open.IsKGroup ↥Js := isKGroup_of_isKProper hS.kProper hJsne
  have hKY : CFSG.Open.IsKGroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js) := s1t_isKGroup_quotient hKJs _
  have hcoreY : GLAPPrimeCore 3 (↥Js ⧸ GLAPPrimeCore 3 ↥Js) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hcommY := i145 (↥Js ⧸ GLAPPrimeCore 3 ↥Js) (s1t_isKGroup_of_open hKY) hcoreY (π b') hbt3
  have hc₁ : GLAPComponent 3 CY (J₁'.map π) :=
    hAπ ▸ glaPComponent_map hp π (s1t_ker_pi A_H) hJ₁'
  have hc₂ : GLAPComponent 3 CY (J₂'.map π) :=
    hAπ ▸ glaPComponent_map hp π (s1t_ker_pi A_H) hJ₂'
  have hq₁ := s1t_isQuasisimple hc₁ hcommY
  have hq₂ := s1t_isQuasisimple hc₂ hcommY
  have hcomp₁ : IsComponentOf (J₁'.map π) CY := ⟨hc₁.1, hc₁.2.1, hq₁⟩
  have hcomp₂ : IsComponentOf (J₂'.map π) CY := ⟨hc₂.1, hc₂.2.1, hq₂⟩
  have hne' : J₁'.map π ≠ J₂'.map π := by
    intro heq
    apply hne
    congr 1
    have hb₁' := lcEquiv_barX hp π A_H (s1t_ker_pi A_H) hJ₁'.1
    have hb₂' := lcEquiv_barX hp π A_H (s1t_ker_pi A_H) hJ₂'.1
    have hbar : barX 3 A_H J₁' = barX 3 A_H J₂' := by
      apply Subgroup.map_injective (lcEquiv hp π A_H (s1t_ker_pi A_H)).injective
      show (barX 3 A_H J₁').map (lcMonoidHom hp π A_H (s1t_ker_pi A_H)) =
        (barX 3 A_H J₂').map (lcMonoidHom hp π A_H (s1t_ker_pi A_H))
      rw [hb₁', hb₂', heq]
    exact glaPComponent_uniqueAux hJ₁' hJ₂' hbar
  have hcomm12 : ⁅J₁'.map π, J₂'.map π⁆ = ⊥ := s1t_comm_of_ne hcomp₁ hcomp₂ hne'
  have hb'₁ : b' ∈ J₁' := by
    obtain ⟨x, hx, hxb⟩ := hb₁
    exact (Subtype.ext hxb : x = b') ▸ hx
  have hb'₂ : b' ∈ J₂' := by
    obtain ⟨x, hx, hxb⟩ := hb₂
    exact (Subtype.ext hxb : x = b') ▸ hx
  obtain ⟨a, ha₂, ha3, hanot⟩ := hn₂
  have haJs : a ∈ Js := (hJ₂le ha₂).1
  have haC : a * b = b * a := Subgroup.mem_centralizer_singleton_iff.1 (hJ₂le ha₂).2
  obtain ⟨a', ha'₂, ha'a⟩ := ha₂
  have ha'eq : a' = ⟨a, haJs⟩ := Subtype.ext ha'a
  have hat3 : π a' ^ 3 = 1 := by
    rw [← map_pow]
    have ha'a' : (a' : G) = a := ha'a
    have : a' ^ 3 = 1 := Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]; rw [ha'a']; exact ha3)
    rw [this, map_one]
  have hat_mem : π a' ∈ J₂'.map π := ⟨a', ha'₂, rfl⟩
  have hbt_mem₁ : π b' ∈ J₁'.map π := ⟨b', hb'₁, rfl⟩
  have hbt_mem₂ : π b' ∈ J₂'.map π := ⟨b', hb'₂, rfl⟩
  have hat_comm : π a' * π b' = π b' * π a' :=
    Subgroup.mem_centralizer_singleton_iff.1 (hc₂.1 hat_mem)
  have hat_not : π a' ∉ Subgroup.zpowers (π b') := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hanot
    refine q_mem_zpowers_of_bar (X := Js) (b := b) (g := a) hbJs (kb := 1)
      (by simpa using hb3') haJs (k := 1) (by simpa using ha3) haC ?_
    refine ⟨b' ^ k, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      have h1 : ((b' ^ k : ↥Js) : G) = b ^ k := Subgroup.coe_zpow _ _ _
      rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
    · show π (b' ^ k) = QuotientGroup.mk (⟨a, haJs⟩ : ↥Js)
      rw [map_zpow, hk, ha'eq]
      rfl
  have hcm : Commute (π b') (π a') := hat_comm.symm
  have hcomm_zp : ∀ h ∈ Subgroup.zpowers (π b'), h * π a' = π a' * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hcm.zpow_left k).eq
  have hzea : IsElemAbelian 3 (Subgroup.zpowers (π b')) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbt3, one_zpow]
  have hA'card : Nat.card ↥(Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a')) = 9 := by
    rw [card_sup_zpowers_of_pow_three_eq_one hat3 hat_not hcomm_zp, Nat.card_zpowers, hbtord]
  have hA'ea : IsElemAbelian 3 (Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a')) :=
    isElemAbelian_sup_zpowers hzea hat3 hcomm_zp
  have hA'norm : Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a') ≤
      Subgroup.normalizer ((⊤ : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) : Set _) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hcent : Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a') ≤
      Subgroup.centralizer ((J₁'.map π : Subgroup _) : Set _) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (hc₁.1 hh)
    · have h21 : ⁅J₂'.map π, J₁'.map π⁆ = ⊥ := (Subgroup.commutator_comm _ _).trans hcomm12
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h21 hat_mem
  have hfield : ∀ a₀ ∈ Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a'), a₀ ≠ 1 →
      InducesFieldAut 3 (J₁'.map π) a₀ := fun a₀ h _ => s1t_inducesFieldAut _ (hcent h)
  have hYq : CFSG.Open.IsQuasisimple (↥Js ⧸ GLAPPrimeCore 3 ↥Js) :=
    isQuasisimple_quotient_of_glaPComponent hJs
  have hKq : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) :=
    s1t_isQuasisimple_of_open
      (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        Subgroup.topEquiv.symm hYq)
  have hKk : CFSG.IsKGroup ↥(⊤ : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) :=
    s1t_isKGroup_of_open (s1t_isKGroup_of_subgroup hKY ⊤)
  have hcomp₁' : IsComponentOf (J₁'.map π) (⊤ ⊓ Subgroup.centralizer ({π b'} :
      Set (↥Js ⧸ GLAPPrimeCore 3 ↥Js))) := by
    rw [top_inf_eq]; exact hcomp₁
  let e : barOf 3 (J₁'.map Js.subtype) ≃* (↥(J₁'.map π) ⧸ GLAPPrimeCore 3 ↥(J₁'.map π)) :=
    (lcEquiv hp Js.subtype J₁' (s1t_ker_sub Js J₁')).symm.trans
      (lcEquiv hp π J₁' (s1t_ker_pi J₁'))
  have he_b : e (QuotientGroup.mk ⟨b, hb₁⟩) = QuotientGroup.mk ⟨π b', hbt_mem₁⟩ := by
    have h1 : (lcEquiv hp Js.subtype J₁' (s1t_ker_sub Js J₁')).symm
        (QuotientGroup.mk ⟨b, hb₁⟩) = QuotientGroup.mk ⟨b', hb'₁⟩ := by
      rw [MulEquiv.symm_apply_eq]; rfl
    have h2 : e (QuotientGroup.mk ⟨b, hb₁⟩) = lcEquiv hp π J₁' (s1t_ker_pi J₁')
        ((lcEquiv hp Js.subtype J₁' (s1t_ker_sub Js J₁')).symm (QuotientGroup.mk ⟨b, hb₁⟩)) := rfl
    rw [h2, h1]; rfl
  have hε : IsSL3Eps (↥(J₁'.map π) ⧸ GLAPPrimeCore 3 ↥(J₁'.map π)) :=
    s1t_isSL3Eps_of_equiv e hε₁
  have hZ : Subgroup.center (↥(J₁'.map π) ⧸ GLAPPrimeCore 3 ↥(J₁'.map π)) =
      Subgroup.zpowers (QuotientGroup.mk (⟨π b', hbt_mem₁⟩ : ↥(J₁'.map π))) := by
    rw [← s1t_center_map e, hZ₁, MonoidHom.map_zpowers]
    congr 1
  have key := i253 (↥Js ⧸ GLAPPrimeCore 3 ↥Js) ⊤ (J₁'.map π)
    (Subgroup.zpowers (π b') ⊔ Subgroup.zpowers (π a')) (π b') hKq hKk (Subgroup.mem_top _)
    hbtord hcomp₁' hbt_mem₁ hε hZ hA'norm hA'ea hA'card
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) hfield
  rcases key with htop | ⟨a₀, ha₀, ha₀1, hnot⟩
  ·
    exfalso
    have h21 : ⁅J₂'.map π, J₁'.map π⁆ = ⊥ := (Subgroup.commutator_comm _ _).trans hcomm12
    have hle : ⁅J₂'.map π, J₂'.map π⁆ ≤ ⁅J₂'.map π, J₁'.map π⁆ :=
      Subgroup.commutator_mono le_rfl (htop ▸ le_top)
    rw [h21, le_bot_iff, glaPComponent_perfect hc₂] at hle
    apply hat_not
    have : π a' ∈ J₂'.map π := hat_mem
    rw [hle] at this
    rw [Subgroup.mem_bot.1 this]
    exact Subgroup.one_mem _
  ·
    have hnorm_zp : Subgroup.zpowers (π b') ≤ Subgroup.normalizer
        ((Subgroup.zpowers (π a') : Subgroup (↥Js ⧸ GLAPPrimeCore 3 ↥Js)) : Set _) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact ((hcm.zpow_zpow k j).symm).eq
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm_zp
    have ha₀' := ha₀
    rw [← SetLike.mem_coe, hmul] at ha₀'
    obtain ⟨u, hu, v, hv, huv⟩ := ha₀'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hba' : Commute b' a' := by
      show b' * a' = a' * b'
      rw [ha'eq]; exact Subtype.ext haC.symm
    set y₀ : ↥Js := b' ^ i * a' ^ j with hy₀
    have hy₀J : y₀ ∈ J₂' :=
      J₂'.mul_mem (Subgroup.zpow_mem _ hb'₂ i) (Subgroup.zpow_mem _ ha'₂ j)
    have hy₀3 : y₀ ^ 3 = 1 := by
      rw [hy₀, (hba'.zpow_zpow i j).mul_pow, s1t_zpow_three hb'3 i, s1t_zpow_three
        (show a' ^ 3 = 1 from Subtype.ext (by
          simp only [Subgroup.coe_pow, Subgroup.coe_one]; rw [show (a' : G) = a from ha'a]; exact ha3)) j,
        one_mul]
    have hπy₀ : π y₀ = a₀ := by
      rw [hy₀, map_mul, map_zpow, map_zpow, hi, hj]; exact huv
    subst hπy₀
    refine ⟨(y₀ : G), ⟨y₀, hy₀J, rfl⟩, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hy₀3
      simpa using this
    · intro hyb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyb
      have hy₀k : y₀ = b' ^ k := Subtype.ext hk.symm
      have hmemz : π y₀ ∈ Subgroup.zpowers (π b') :=
        Subgroup.mem_zpowers_iff.2 ⟨k, by rw [hy₀k, map_zpow]⟩
      apply hnot
      have hbt_in : π b' ∈ Subgroup.zpowers (π y₀) := s1t_mem_zpowers_of_prime hbtord hmemz ha₀1
      refine mem_oPrimePOf_of_forall_comm hp ?_ ?_
      · refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.1 hmemz
        rw [← hk']
        exact (Commute.self_zpow (π b') k').eq
      · intro w hw
        have hwc : Commute w (π y₀) := Subgroup.mem_centralizer_singleton_iff.1 hw.2
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hbt_in
        rw [← hm]
        exact ((hwc.zpow_right m).symm).eq
    · intro hmem
      apply hnot
      let φ : ↥(Js ⊓ Cb (y₀ : G)) →* ↥(⊤ ⊓ Subgroup.centralizer ({π y₀} :
          Set (↥Js ⧸ GLAPPrimeCore 3 ↥Js))) :=
        MonoidHom.codRestrict (π.comp (Subgroup.inclusion inf_le_left)) _ (fun g => by
          refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
          show π (Subgroup.inclusion inf_le_left g) * π y₀ = π y₀ * π (Subgroup.inclusion inf_le_left g)
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2.2))
      have hφ : Function.Surjective φ := by
        intro w
        have hw : w.1 ∈ (Subgroup.centralizer ({y₀} : Set ↥Js)).map π := by
          rw [s1t_map_cent hy₀3]; exact w.2.2
        obtain ⟨g, hg, hgw⟩ := hw
        have hgc : (g : G) * (y₀ : G) = (y₀ : G) * (g : G) :=
          congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
        exact ⟨⟨(g : G), g.2, Subgroup.mem_centralizer_singleton_iff.2 hgc⟩, Subtype.ext hgw⟩
      have hle := o_map_hom_le φ hφ
      obtain ⟨o, ho, hob⟩ := hmem
      refine ⟨φ o, hle (Subgroup.mem_map_of_mem φ ho), ?_⟩
      show π (Subgroup.inclusion inf_le_left o) = π b'
      congr 1
      exact Subtype.ext hob


end S1TSec

section S1Sec

omit [Finite G] in
private theorem s1_eps_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSL3Eps X) : IsSL3Eps Y := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hs with ⟨K, f, fin, ⟨φ⟩⟩ | ⟨K, f, fin, q, hq, ⟨φ⟩⟩
    · exact Or.inl ⟨K, f, fin, ⟨e.symm.trans φ⟩⟩
    · exact Or.inr ⟨K, f, fin, q, hq, ⟨e.symm.trans φ⟩⟩
  · have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
      Subgroup.map_center_eq e
    rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact hc

omit [Finite G] in
private theorem s1_center_zpowers {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X)
    (hZ : Subgroup.center Y = Subgroup.zpowers (e x)) :
    Subgroup.center X = Subgroup.zpowers x := by
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  have hz : Subgroup.zpowers (e x) = (Subgroup.zpowers x).map e.toMonoidHom :=
    (MonoidHom.map_zpowers e.toMonoidHom x).symm
  rw [hZ, hz] at hcen
  exact Subgroup.map_injective e.injective hcen

private theorem s1_E {C A : Subgroup G} (hAC : A ≤ C) :
    ∃ E : (↥A ⧸ GLAPPrimeCore 3 ↥A) ≃*
        (↥(barX 3 C A) ⧸ GLAPPrimeCore 3 ↥(barX 3 C A)),
      ∀ g (hgA : g ∈ A) (hgC : g ∈ C),
        E (QuotientGroup.mk ⟨g, hgA⟩) =
          QuotientGroup.mk ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨g, hgC⟩,
            ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hgA, rfl⟩⟩ := by
  have hker : Nat.Coprime 3 (Nat.card ↥(A.subgroupOf C ⊓
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).ker)) := by
    refine (coprime_card_gLAPPrimeCore_aux 3 ↥C).coprime_dvd_right ?_
    have : A.subgroupOf C ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).ker ≤
        GLAPPrimeCore 3 ↥C := by
      rw [QuotientGroup.ker_mk']
      exact inf_le_right
    exact Subgroup.card_dvd_of_le this
  let e1 := lcEquiv Nat.prime_three (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)) (A.subgroupOf C) hker
  let e0 := Subgroup.subgroupOfEquivOfLe hAC
  let qA := QuotientGroup.congr (GLAPPrimeCore 3 ↥A) (GLAPPrimeCore 3 ↥(A.subgroupOf C)) e0.symm
    (glaPPrimeCore_map_iso 3 e0.symm)
  refine ⟨qA.trans e1, fun g hgA hgC => ?_⟩
  rfl

omit [Finite G] in
private theorem s1_cast {H : Type*} [Group H] (S T : Subgroup H) (h : S = T) :
    ∃ f : (↥S ⧸ GLAPPrimeCore 3 ↥S) ≃* (↥T ⧸ GLAPPrimeCore 3 ↥T),
      ∀ s (hs : s ∈ S) (ht : s ∈ T), f (QuotientGroup.mk ⟨s, hs⟩) = QuotientGroup.mk ⟨s, ht⟩ := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ _ _ => rfl⟩

omit [Finite G] in
private theorem s1_barX_zpowers {C : Subgroup G} {b : G} (hbC : b ∈ C) (v : ↥C ⧸ GLAPPrimeCore 3 ↥C) :
    v ∈ barX 3 C (Subgroup.zpowers b) ↔
      v ∈ Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_subgroupOf.1 hc
    refine ⟨n, ?_⟩
    have : (⟨b, hbC⟩ : ↥C) ^ n = c := Subtype.ext (by simpa using hn)
    simp only
    rw [← map_zpow, this]
  · rintro ⟨n, rfl⟩
    refine ⟨⟨b, hbC⟩ ^ n, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    exact ⟨n, by simp⟩

private theorem s1_center_barOf {C L : Subgroup G} {b : G} (hL : GLAPComponent 3 C L)
    (hbC : b ∈ C) (hbL : b ∈ L)
    (hF : FusData (barX 3 C L) (barX 3 C (Subgroup.zpowers b))) :
    Subgroup.center (↥L ⧸ GLAPPrimeCore 3 ↥L) =
      Subgroup.zpowers (QuotientGroup.mk (⟨b, hbL⟩ : ↥L)) := by
  let φ := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩ ∈ barX 3 C L :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbL, rfl⟩
  have hφ : φ (QuotientGroup.mk ⟨b, hbL⟩) =
      ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩, hmem⟩ := rfl
  refine s1_center_zpowers φ _ ?_
  rw [hφ]
  ext w
  rw [Subgroup.mem_center_iff]
  have h1 := hF.Zcenter (w : ↥C ⧸ GLAPPrimeCore 3 ↥C)
  rw [s1_barX_zpowers hbC] at h1
  have h2 : w ∈ Subgroup.zpowers
      (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩, hmem⟩ : ↥(barX 3 C L)) ↔
      (w : ↥C ⧸ GLAPPrimeCore 3 ↥C) ∈
        Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩) := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [h2, h1]
  constructor
  · intro h
    refine ⟨w.2, fun q hq => ?_⟩
    have := h ⟨q, hq⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨-, h⟩ g
    exact Subtype.ext (h g g.2).symm

private theorem s1_hn2 {C J L : Subgroup G} {b : G}
    (hbar : barX 3 C J = barX 3 C L)
    (hF : FusData (barX 3 C L) (barX 3 C (Subgroup.zpowers b))) :
    ∃ a ∈ J, a ^ 3 = 1 ∧ a ∉ Subgroup.zpowers b := by
  obtain ⟨a0, ha0Q, ha03, ha0Z⟩ := hF.exists_noncentral
  rw [← hbar] at ha0Q
  obtain ⟨c, hc, rfl⟩ := ha0Q
  have hcJ : (c : G) ∈ J := Subgroup.mem_subgroupOf.1 hc
  have hz : c ^ 3 ∈ GLAPPrimeCore 3 ↥C := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using ha03
  set m := orderOf (c ^ 3) with hm
  have hmc : m ∣ Nat.card (GLAPPrimeCore 3 ↥C) := by
    have := orderOf_dvd_natCard (⟨c ^ 3, hz⟩ : GLAPPrimeCore 3 ↥C)
    simpa using this
  have hm3 : m % 3 ≠ 0 := by
    intro h0
    have h3m : 3 ∣ m := Nat.dvd_of_mod_eq_zero h0
    have := (coprime_card_gLAPPrimeCore_aux 3 ↥C).eq_one_of_dvd (h3m.trans hmc)
    omega
  have hmm : m * m % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  obtain ⟨k, hk⟩ : ∃ k, m * m = 3 * k + 1 := ⟨m * m / 3, by omega⟩
  have ha3 : (c ^ (m * m)) ^ 3 = 1 := by
    have h1 : (c ^ 3) ^ m = 1 := pow_orderOf_eq_one _
    calc (c ^ (m * m)) ^ 3 = ((c ^ 3) ^ m) ^ m := by
          simp only [← pow_mul]; congr 1; ring
      _ = 1 := by rw [h1, one_pow]
  have himg : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) (c ^ (m * m)) =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) c := by
    rw [map_pow, hk, pow_succ, pow_mul, ha03, one_pow, one_mul]
  refine ⟨((c ^ (m * m) : ↥C) : G), Subgroup.mem_subgroupOf.1 (pow_mem hc _), ?_, ?_⟩
  · simpa using congrArg Subtype.val ha3
  · intro hz'
    apply ha0Z
    rw [← himg]
    exact ⟨c ^ (m * m), Subgroup.mem_subgroupOf.2 hz', rfl⟩

omit [Finite G] in
private theorem s1_layer_le {L X : Subgroup G} : GLAPLayer 3 (L ⊓ X) ≤ L ⊓ X :=
  sSup_le fun _ hK => hK.1

private theorem s1_b_mem {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L)
    (hF : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) (hb3 : b ^ 3 = 1) :
    b ∈ L := by
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hmem : mkX (Cb b) b hbC ∈ barX 3 (Cb b) (Subgroup.zpowers b) :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers b), rfl⟩
  exact q_mem_of_bar hL hbC (k := 1) (by simpa using hb3) (hF.Zle hmem)

private theorem s1_equiv {C J L : Subgroup G} (hJC : J ≤ C) (hLC : L ≤ C)
    (h : barX 3 C J = barX 3 C L) :
    ∃ e : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* (↥L ⧸ GLAPPrimeCore 3 ↥L),
      ∀ g (hgJ : g ∈ J) (hgL : g ∈ L),
        e (QuotientGroup.mk ⟨g, hgJ⟩) = QuotientGroup.mk ⟨g, hgL⟩ := by
  obtain ⟨EJ, hEJ⟩ := s1_E hJC
  obtain ⟨EL, hEL⟩ := s1_E hLC
  obtain ⟨f, hf⟩ := s1_cast _ _ h
  refine ⟨(EJ.trans f).trans EL.symm, fun g hgJ hgL => ?_⟩
  have hgC : g ∈ C := hJC hgJ
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hEJ g hgJ hgC]
  rw [MulEquiv.symm_apply_eq, hEL g hgL hgC]
  exact hf _ _ _

theorem s1_core (i183 : Input18_3_4) (i145 : Input14_5) (i253 : Input25_3) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    (hY : Y2 b L₂ L₃) {x : G} (hx : x ∈ L₃) (hx3 : x ^ 3 = 1) (hxb : x ∉ Subgroup.zpowers b) :
    b ∈ oPrimePOf 3 (Cb x) := by
  have hT := hR.tri
  have hb3' : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3' hT.ne_one
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hbL1 : b ∈ L₁ := s1_b_mem hT.comp₁ hR.fus₁ hb3'
  have hbL2 : b ∈ L₂ := s1_b_mem hT.comp₂ hR.fus₂ hb3'
  have hxC : x ∈ Cb b := hT.comp₃.1 hx
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ one_mem _)
  have hzx : Subgroup.zpowers x ≤ L₃ := Subgroup.zpowers_le.2 hx
  have hc1 : ⁅L₁, Subgroup.zpowers x⁆ ≤ P3 (Cb b) :=
    (Subgroup.commutator_mono le_rfl hzx).trans
      (commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₁ hT.comp₃ hT.ne₁₃)
  have hc2 : ⁅L₂, Subgroup.zpowers x⁆ ≤ P3 (Cb b) :=
    (Subgroup.commutator_mono le_rfl hzx).trans
      (commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₂ hT.comp₃ hT.ne₂₃)
  obtain ⟨hJ1c, hbJ1, hbar1, hJs1, hJJs1, hJ1c2⟩ :=
    jstar i183 hS hT.comp₁ hbL1 hb3' hR.fus₁ hxC hx3 hx1 hc1
  obtain ⟨hJ2c, hbJ2, hbar2, hJs2, hJJs2, hJ2c2⟩ :=
    jstar i183 hS hT.comp₂ hbL2 hb3' hR.fus₂ hxC hx3 hx1 hc2
  set J₁ := GLAPLayer 3 (L₁ ⊓ Cb x) with hJ₁
  set J₂ := GLAPLayer 3 (L₂ ⊓ Cb x) with hJ₂
  set Js₁ := ⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g J₁ with hJs₁
  set Js₂ := ⨆ g ∈ GLAPLayer 3 (Cb x), GLBConj g J₂ with hJs₂
  by_cases hJs : Js₁ = Js₂
  ·
    have h₂ : GLAPComponent 3 (Js₁ ⊓ Cb b) J₂ := by rw [hJs]; exact hJ2c2
    have hne : J₁ ≠ J₂ := by
      intro h
      apply hT.ne₁₂
      refine glaPComponent_uniqueAux hT.comp₁ hT.comp₂ ?_
      rw [← hbar1, ← hbar2, h]
    have hJ1L : J₁ ≤ L₁ := s1_layer_le.trans inf_le_left
    have hJ2L : J₂ ≤ L₂ := s1_layer_le.trans inf_le_left
    have hJ2x : J₂ ≤ Cb x := s1_layer_le.trans inf_le_right
    obtain ⟨e, he⟩ := s1_equiv (hJ1L.trans hT.comp₁.1) hT.comp₁.1 hbar1
    have hε₁ : IsSL3Eps (barOf 3 J₁) := s1_eps_of_equiv e.symm hR.eps₁
    have hZ₁ : Subgroup.center (barOf 3 J₁) =
        Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ1⟩ : ↥J₁)) := by
      refine s1_center_zpowers e _ ?_
      rw [he b hbJ1 hbL1]
      exact s1_center_barOf hT.comp₁ hbC hbL1 hR.fus₁
    have hn₂ : ∃ a ∈ J₂, a ^ 3 = 1 ∧ a ∉ Subgroup.zpowers b := s1_hn2 hbar2 hR.fus₂
    obtain ⟨y, hyJ2, hy3, hyb, hbny⟩ :=
      s1_tilde i145 i253 hS hbo hx1 hJs1 hJ1c2 h₂ hne hbJ1 hbJ2 hε₁ hZ₁ hn₂
    exfalso
    apply hbny
    have hyL2 : y ∈ L₂ := hJ2L hyJ2
    have hyCx : y ∈ Cb x := hJ2x hyJ2
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyCx
    have hbyx := hY y hyL2 x hx hyx hy3 hx3 hyb hxb
    have hxCyx : x ∈ Cb (y * x) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (y * x) = (x * y) * x := by group
        _ = (y * x) * x := by rw [hyx]
    have hbCx : b ∈ Cb x := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm
    have h1 := o_inf_centralizer_le hxCyx ⟨1, by simpa using hx3⟩ ⟨hbyx, hbCx⟩
    have hW : Cb (y * x) ⊓ Cb x = Cb x ⊓ Cb y := by
      ext z
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        calc z * y = z * (y * x) * x⁻¹ := by group
          _ = (y * x) * z * x⁻¹ := by rw [h1]
          _ = y * (x * z) * x⁻¹ := by group
          _ = y * (z * x) * x⁻¹ := by rw [h2]
          _ = y * z := by group
      · rintro ⟨h2, h1⟩
        refine ⟨?_, h2⟩
        calc z * (y * x) = (z * y) * x := by group
          _ = (y * z) * x := by rw [h1]
          _ = y * (z * x) := by group
          _ = y * (x * z) := by rw [h2]
          _ = (y * x) * z := by group
    rw [hW] at h1
    have hsn := isSubnormal_inf hJs1.2.1 (Cb y)
    have hbyC : b ∈ Cb y := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hT.comp₂.1 hyL2)).symm
    exact o_inf_le_of_subnormal hsn ⟨h1, hJJs1 hbJ1, hbyC⟩
  ·
    have hb12 : b ∈ Js₁ ⊓ Js₂ := ⟨hJJs1 hbJ1, hJJs2 hbJ2⟩
    exact o_le_of_subnormal hJs1.2.1
      (inf_le_oPrimePOf_of_ne Nat.prime_three hJs1 hJs2 hJs hb12)

end S1Sec

section RMSec

omit [Finite G] in
private theorem rm_cb_conj (c w : G) :
    Cb (c * w * c⁻¹) = GLBConj c⁻¹ (Cb w) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_inv]
  constructor
  · intro h
    calc c⁻¹ * y * c * w = c⁻¹ * (y * (c * w * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * w * c⁻¹) * y) * c := by rw [h]
      _ = w * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * w * c⁻¹) = c * ((c⁻¹ * y * c) * w) * c⁻¹ := by group
      _ = c * (w * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * w * c⁻¹ * y := by group

private theorem rm_transport {b c w : G} (hc : c * b = b * c) (h : b ∈ oPrimePOf 3 (Cb w)) :
    b ∈ oPrimePOf 3 (Cb (c * w * c⁻¹)) := by
  rw [rm_cb_conj, oPrimePOf_gLBConj, mem_gLBConj]
  have : c⁻¹ * b * c⁻¹⁻¹ = b := by
    rw [inv_inv]; calc c⁻¹ * b * c = c⁻¹ * (b * c) := by group
      _ = b := by rw [← hc]; group
  rwa [this]

omit [Finite G] in
private theorem rm_commute_of_B {B : Subgroup G} (hB : IsElemAbelian 3 B) {x y : G} (hx : x ∈ B)
    (hy : y ∈ B) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hB hx hy

private theorem rm_step {b β : G} {A A' : Subgroup G} (hβ : β * b = b * β)
    (hA : ∀ y, y ∈ A ↔ β * y * β⁻¹ ∈ A')
    (h : ∀ x ∈ A', x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x)) :
    ∀ x ∈ A, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) := by
  intro x hx hx3 hxn
  have hnz : ∀ x : G, β * x * β⁻¹ ∈ Subgroup.zpowers b → x ∈ Subgroup.zpowers b := by
    rintro x ⟨k, hk⟩
    have hcm : β * b ^ k = b ^ k * β := (Commute.zpow_right (show Commute β b from hβ) k).eq
    refine ⟨k, ?_⟩
    have hk' : β * x * β⁻¹ = b ^ k := hk.symm
    calc b ^ k = β⁻¹ * (β * b ^ k) := by group
      _ = β⁻¹ * (b ^ k * β) := by rw [hcm]
      _ = β⁻¹ * (β * x * β⁻¹) * β := by rw [hk']; group
      _ = x := by group
  have hmain := h (β * x * β⁻¹) ((hA x).1 hx) (by rw [conj_pow, hx3]; group)
    (fun h' => hxn (hnz x h'))
  have := rm_transport (b := b) (c := β⁻¹) (w := β * x * β⁻¹)
    (by simpa using (Commute.inv_left (show Commute β b from hβ)).eq) hmain
  have e : β⁻¹ * (β * x * β⁻¹) * β⁻¹⁻¹ = x := by group
  rwa [e] at this

private theorem rm_zp {b x : G} (hb : orderOf b = 3) (hx : x ∈ Subgroup.zpowers b)
    (hx3 : orderOf x = 3) : b ∈ oPrimePOf 3 (Cb x) := by
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hx
  have hEq : Subgroup.zpowers x = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hb, hx3]
  have hbx : b ∈ Subgroup.zpowers x := by rw [hEq]; exact Subgroup.mem_zpowers b
  have hbc : b ∈ Cb x := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨j, rfl⟩ := hbx
    exact ((Commute.refl x).zpow_left j).eq
  refine mem_oPrimePOf_of_forall_comm Nat.prime_three hbc fun y hy => ?_
  have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
  obtain ⟨j, hj⟩ := hbx
  rw [← hj]
  exact (((show Commute y x from hyx).zpow_right j).eq).symm

private theorem rm_b_mem {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L)
    (hF : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) (hb3 : b ^ 3 = 1) :
    b ∈ L := by
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hmem : mkX (Cb b) b hbC ∈ barX 3 (Cb b) (Subgroup.zpowers b) :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers b), rfl⟩
  exact q_mem_of_bar hL hbC (k := 1) (by simpa using hb3) (hF.Zle hmem)

theorem r_main (i183 : Input18_3_4) (i145 : Input14_5) (i253 : Input25_3) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    (hY : Y2 b L₁ L₂) {Li Lj : Subgroup G} (hi : Li = L₁ ∨ Li = L₂ ∨ Li = L₃)
    (hj : Lj = L₁ ∨ Lj = L₂ ∨ Lj = L₃) {x : G} (hx : x ∈ Li ⊔ Lj) (hx3 : orderOf x = 3) :
    b ∈ oPrimePOf 3 (Cb x) := by
  have hT := hR.tri
  have hb3' : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbo : orderOf b = 3 :=
    orderOf_eq_prime hb3' hT.ne_one
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨β, hβB, h21, h32, h13⟩ := hT.cyc
  have hβb : β * b = b * β := rm_commute_of_B hT.elemB hβB hT.mem
  have hm : ∀ {X Y : Subgroup G}, X = GLBConj β Y → ∀ y, y ∈ X ↔ β * y * β⁻¹ ∈ Y := by
    intro X Y hXY y
    rw [hXY, mem_gLBConj]
  have hY23 := (y2_cyc hT hY).1
  have hY31 := (y2_cyc hT hY).2
  have hY21 := y2_symm hY
  have hY32 := y2_symm hY23
  have hY13 := y2_symm hY31
  have hP3 : ∀ x ∈ L₃, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) :=
    fun x hx hx3 hxb => s1_core i183 i145 i253 hS hR hY23 hx hx3 hxb
  have hP1 : ∀ x ∈ L₁, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) :=
    rm_step hβb (hm h13) hP3
  have hP2 : ∀ x ∈ L₂, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x) :=
    rm_step hβb (hm h21) hP1
  have hF : ∀ {L : Subgroup G}, (L = L₁ ∨ L = L₂ ∨ L = L₃) →
      (∀ x ∈ L, x ^ 3 = 1 → x ∉ Subgroup.zpowers b → b ∈ oPrimePOf 3 (Cb x)) ∧
        GLAPComponent 3 (Cb b) L ∧
        FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b)) := by
    intro L hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨hP1, hT.comp₁, hR.fus₁⟩
    · exact ⟨hP2, hT.comp₂, hR.fus₂⟩
    · exact ⟨hP3, hT.comp₃, hR.fus₃⟩
  have hfull : ∀ {L : Subgroup G}, (L = L₁ ∨ L = L₂ ∨ L = L₃) → ∀ y ∈ L, orderOf y = 3 →
      b ∈ oPrimePOf 3 (Cb y) := by
    intro L hL y hy hy3
    by_cases hz : y ∈ Subgroup.zpowers b
    · exact rm_zp hbo hz hy3
    · exact (hF hL).1 y hy (by rw [← hy3]; exact pow_orderOf_eq_one y) hz
  have hbmem : ∀ {L : Subgroup G}, (L = L₁ ∨ L = L₂ ∨ L = L₃) → b ∈ L := fun hL =>
    rm_b_mem (hF hL).2.1 (hF hL).2.2 hb3'
  by_cases hij : Li = Lj
  · subst hij
    rw [sup_idem] at hx
    exact hfull hi x hx hx3
  have hxc : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hYij : Y2 b Li Lj := by
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first | exact absurd rfl hij | assumption
  obtain ⟨c, hc, u, hu, v, hv, hcm, hu3, hv3, hcx⟩ :=
    decomp_sylow (hF hi).2.1 (hF hj).2.1 hij (hF hi).2.2 (hF hj).2.2 hx hxc
  have hcC : c ∈ Cb b := by
    have : Li ⊔ Lj ≤ Cb b := sup_le (hF hi).2.1.1 (hF hj).2.1.1
    exact this hc
  have hcb : c * b = b * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hord : orderOf (u * v) = 3 := by
    rw [← hcx, ← hx3]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
  suffices h : b ∈ oPrimePOf 3 (Cb (u * v)) by
    have h2 := rm_transport (b := b) (c := c⁻¹) (w := u * v)
      (by simpa using (Commute.inv_left (show Commute c b from hcb)).eq) h
    rw [← hcx] at h2
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h2
  by_cases huz : u ∈ Subgroup.zpowers b
  · have : u * v ∈ Lj := mul_mem
      ((Subgroup.zpowers_le.2 (hbmem hj)) huz) hv
    exact hfull hj _ this hord
  by_cases hvz : v ∈ Subgroup.zpowers b
  · have : u * v ∈ Li := mul_mem hu ((Subgroup.zpowers_le.2 (hbmem hi)) hvz)
    exact hfull hi _ this hord
  exact hYij u hu v hv hcm hu3 hv3 huz hvz

end RMSec

section CaseA

theorem a_normal_inf_center {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (R N : Subgroup P) [R.Normal] (hN : N ≤ Subgroup.center P)
    (hNR : N ≤ R) (hne : N ≠ R) :
    ∃ y ∈ R, y ∉ N ∧ ∀ g : P, g * y * g⁻¹ * y⁻¹ ∈ N := by
  have : N.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hN hn) g
    rw [show g * n * g⁻¹ = n by rw [this]; group]; exact hn⟩
  have : Group.IsNilpotent (P ⧸ N) := (hP.to_quotient N).isNilpotent
  obtain ⟨y, hyR, hyN⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hNR hne)
  have hne' : R.map (QuotientGroup.mk' N) ≠ ⊥ := by
    intro h
    have : QuotientGroup.mk' N y ∈ R.map (QuotientGroup.mk' N) := ⟨y, hyR, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hyN this
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := P ⧸ N) hne'
  obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h2
  have hq' : (q : P ⧸ N) ∈ R.map (QuotientGroup.mk' N) ⊓ Subgroup.center (P ⧸ N) := q.2
  obtain ⟨⟨y₀, hy₀R, hy₀⟩, hqc⟩ := hq'
  refine ⟨y₀, hy₀R, ?_, fun g => ?_⟩
  · intro hy₀N
    apply hq1
    apply Subtype.ext
    rw [← hy₀]
    exact (QuotientGroup.eq_one_iff y₀).2 hy₀N
  · have := Subgroup.mem_center_iff.1 hqc (QuotientGroup.mk g)
    rw [← hy₀] at this
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk'_apply] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this]; group


theorem a_fixed_class {R D N : Subgroup G} (hR : IsPGroup 3 R) (hD : IsPGroup 3 D)
    (hDR : D ≤ Subgroup.normalizer (R : Set G)) (hNR : N ≤ R)
    (hNc : ∀ n ∈ N, ∀ r ∈ R, n * r = r * n) (hNd : ∀ n ∈ N, ∀ d ∈ D, n * d = d * n)
    (hne : N ≠ R) :
    ∃ y ∈ R, y ∉ N ∧ ∀ d ∈ D, d * y * d⁻¹ * y⁻¹ ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 (R ⊔ D : Subgroup G) := hR.to_sup_of_normal_left' hD hDR
  have hle : (R ⊔ D : Subgroup G) ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer hDR
  have hRn : (R.subgroupOf (R ⊔ D)).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    le_sup_left).2 hle
  have hPp' : IsPGroup 3 ↥(R ⊔ D : Subgroup G) := hPp
  have hNP : N.subgroupOf (R ⊔ D) ≤ Subgroup.center ↥(R ⊔ D : Subgroup G) := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : G) ∈ Subgroup.centralizer ({(n : G)} : Set G) := by
      have : (R ⊔ D : Subgroup G) ≤ Subgroup.centralizer ({(n : G)} : Set G) := by
        refine sup_le (fun r hr => ?_) (fun d hd => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hNc n hn r hr).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hNd n hn d hd).symm
      exact this g.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact Subtype.ext (by simpa using hg)
  have hRle : R ≤ R ⊔ D := le_sup_left
  have hDle : D ≤ R ⊔ D := le_sup_right
  have hNR' : N.subgroupOf (R ⊔ D) ≤ R.subgroupOf (R ⊔ D) := fun x hx => hNR hx
  have hne' : N.subgroupOf (R ⊔ D) ≠ R.subgroupOf (R ⊔ D) := by
    intro h
    apply hne
    apply le_antisymm hNR
    intro r hr
    have : (⟨r, hRle hr⟩ : ↥(R ⊔ D : Subgroup G)) ∈ R.subgroupOf (R ⊔ D) := hr
    rw [← h] at this
    exact this
  obtain ⟨y, hyR, hyN, hy⟩ := a_normal_inf_center hPp' _ _ hNP hNR' hne'
  refine ⟨y.1, hyR, hyN, fun d hd => ?_⟩
  exact hy ⟨d, hDle hd⟩

theorem a_exists_conj {K S P : Subgroup G} (hSK : S ≤ K) (hPK : P ≤ K) (hP : IsPGroup 3 P)
    (hcard : Nat.card S = 3 ^ (Nat.card K).factorization 3) : ∃ g ∈ K, ∀ x ∈ P, g⁻¹ * x * g ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' : IsPGroup 3 (P.subgroupOf K) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  let S₀ : Sylow 3 K := Sylow.ofCard (S.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]; exact hcard)
  obtain ⟨S₂, hS₂⟩ := hP'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S₀ S₂
  refine ⟨k, k.2, fun x hx => ?_⟩
  have hxS : (⟨x, hPK hx⟩ : K) ∈ (S₂ : Subgroup K) :=
    hS₂ (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  have hS0 : (S₀ : Subgroup K) = S.subgroupOf K := rfl
  rw [hS0, Subgroup.mem_subgroupOf] at hxS
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply] using hxS

omit [Finite G] in
theorem a_mem_P3_iff {X : Subgroup G} {g : G} (hg : g ∈ X) :
    g ∈ P3 X ↔ mkX X g hg = 1 := by
  unfold mkX P3 GLAPPrimeCoreOf
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩; exact hh
  · intro h; exact ⟨⟨g, hg⟩, h, rfl⟩

theorem a_eq_one_of_P3 {X : Subgroup G} {g : G} (hg : g ∈ P3 X) {k : ℕ} (hk : g ^ (3 ^ k) = 1) :
    g = 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have hk' : h ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have h1 : orderOf (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk'))
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (GLAPPrimeCore 3 ↥X)) :=
    Nat.Coprime.pow_left _ CFSG.pPrimeCore_coprime_card
  have : orderOf (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  have h3 : (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) = 1 := orderOf_eq_one_iff.1 this
  have : h = 1 := congrArg Subtype.val h3
  simp [this]


omit [Finite G] in
theorem a_mem_barX_iff (p : ℕ) (X K : Subgroup G) (z : ↥X ⧸ GLAPPrimeCore p ↥X) :
    z ∈ barX p X K ↔ ∃ x : ↥X, (x : G) ∈ K ∧ (QuotientGroup.mk x : ↥X ⧸ GLAPPrimeCore p ↥X) = z := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf).2 hx, rfl⟩

omit [Finite G] in
theorem a_mk_comm_iff {X : Subgroup G} {g h : G} (hg : g ∈ X) (hh : h ∈ X) :
    g * h * g⁻¹ * h⁻¹ ∈ P3 X ↔ mkX X g hg * mkX X h hh = mkX X h hh * mkX X g hg := by
  have hm : g * h * g⁻¹ * h⁻¹ ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hg hh) (X.inv_mem hg))
    (X.inv_mem hh)
  rw [a_mem_P3_iff hm]
  have : mkX X (g * h * g⁻¹ * h⁻¹) hm = (mkX X g hg * mkX X h hh) * (mkX X g hg)⁻¹ *
      (mkX X h hh)⁻¹ := rfl
  rw [this, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

omit [Finite G] in
theorem a_comm_zpowers {X : Subgroup G} {l u v : G} (hl : l ∈ X) (hu : u ∈ X) (hv : v ∈ X)
    (hlu : l * u * l⁻¹ * u⁻¹ ∈ P3 X) (hlv : l * v * l⁻¹ * v⁻¹ ∈ P3 X) {g : G} (hg : g ∈ Subgroup.zpowers (u * v)) :
    l * g * l⁻¹ * g⁻¹ ∈ P3 X := by
  have hX : Subgroup.zpowers (u * v) ≤ X := by
    rw [Subgroup.zpowers_le]; exact X.mul_mem hu hv
  have hgX := hX hg
  let T : Subgroup ↥X := (Subgroup.centralizer ({mkX X l hl} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X))
  have hmem : ∀ (y : G) (hy : y ∈ X), (⟨y, hy⟩ : ↥X) ∈ T ↔ l * y * l⁻¹ * y⁻¹ ∈ P3 X := by
    intro y hy
    rw [a_mk_comm_iff hl hy]
    show _ ∈ Subgroup.centralizer _ ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have huT : (⟨u, hu⟩ : ↥X) ∈ T := (hmem u hu).2 hlu
  have hvT : (⟨v, hv⟩ : ↥X) ∈ T := (hmem v hv).2 hlv
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have : (⟨u, hu⟩ * ⟨v, hv⟩ : ↥X) ^ n ∈ T := T.zpow_mem (T.mul_mem huT hvT) n
  exact (hmem _ hgX).1 this


theorem a_finish (h25 : Lemma25Strong) {m : ℕ} (hS : GLStanding G m 3) {B D : Subgroup G}
    {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃) (hset : Lemma24Setup 3 B D b L₁)
    (hZ : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L₁))
    {u v : G} (hu : u ∈ L₁) (hv : v ∈ L₂) (hc : u * v = v * u) (hu3 : u ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (hnu : u ∉ Subgroup.zpowers b)
    (hD : ∀ d ∈ D, d * (u * v) * d⁻¹ = u * v) :
    b ∈ oPrimePOf 3 (Cb (u * v)) := by
  have hT := hR.tri
  have hu' : u ∈ Cb b := hT.comp₁.1 hu
  have hv' : v ∈ Cb b := hT.comp₂.1 hv
  have hx3 : (u * v) ^ 3 = 1 := by rw [(show Commute u v from hc).mul_pow, hu3, hv3, one_mul]
  have hx1 : u * v ≠ 1 := by
    intro h1
    have hv2 : u ∈ L₂ := by
      have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]; exact L₂.inv_mem hv
    have hcomm : ∀ l ∈ L₁, l * u * l⁻¹ * u⁻¹ ∈ P3 (Cb b) := fun l hl => by
      have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₁ hT.comp₂ hT.ne₁₂
        (Subgroup.commutator_mem_commutator hl hv2)
      simpa [commutatorElement_def] using this
    have hubar : mkX (Cb b) u hu' ∈ barX 3 (Cb b) L₁ :=
      (a_mem_barX_iff 3 (Cb b) L₁ _).2 ⟨⟨u, hu'⟩, hu, rfl⟩
    have hcen : mkX (Cb b) u hu' ∈ barX 3 (Cb b) (Subgroup.zpowers b) := by
      refine (hR.fus₁.Zcenter _).2 ⟨hubar, fun q hq => ?_⟩
      obtain ⟨⟨l, hl'⟩, hlL, rfl⟩ := (a_mem_barX_iff 3 (Cb b) L₁ _).1 hq
      exact ((a_mk_comm_iff hl' hu').1 (hcomm l hlL)).symm
    have hb3 : b ^ (3 ^ 1) = 1 := by simpa using hT.elemB.2 b hT.mem
    have hu3' : u ^ (3 ^ 1) = 1 := by simpa using hu3
    exact hnu (q_mem_zpowers_of_bar (X := Cb b) (Subgroup.mem_centralizer_singleton_iff.2 rfl) hb3
      hu' hu3' (Subgroup.mem_centralizer_singleton_iff.1 hu') hcen)
  have hord : orderOf (u * v) = 3 := orderOf_eq_prime hx3 hx1
  have hxC : u * v ∈ Cb b := (Cb b).mul_mem hu' hv'
  have hcB : ⁅L₃, Subgroup.zpowers (u * v)⁆ ≤ P3 (Cb b) := by
    refine Subgroup.commutator_le.2 fun l hl g hg => ?_
    have hl' : l ∈ Cb b := hT.comp₃.1 hl
    have h1 : l * u * l⁻¹ * u⁻¹ ∈ P3 (Cb b) := by
      have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₃ hT.comp₁
        hT.ne₁₃.symm (Subgroup.commutator_mem_commutator hl hu)
      simpa [commutatorElement_def] using this
    have h2 : l * v * l⁻¹ * v⁻¹ ∈ P3 (Cb b) := by
      have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₃ hT.comp₂
        hT.ne₂₃.symm (Subgroup.commutator_mem_commutator hl hv)
      simpa [commutatorElement_def] using this
    simpa [commutatorElement_def] using a_comm_zpowers hl' hu' hv' h1 h2 hg
  have hIB : IsBConjugate B L₁ L₃ := by
    obtain ⟨β, hβ, h2, h3, -⟩ := hT.cyc
    exact ⟨β * β, B.mul_mem hβ hβ, by rw [h3, h2, gLBConj_gLBConj]⟩
  have hDx : D ≤ Cb (u * v) := fun d hd => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.1 (hD d hd)
  have := h25 G m hS B D b L₁ hset L₃ hIB (u * v) hxC hord hcB
  exact this.2 (Or.inr ⟨hDx, hZ⟩)


omit [Finite G] in
theorem a_pgroup_of_exp {P : Subgroup G} (h : ∀ x ∈ P, x ^ 3 = 1) : IsPGroup 3 P :=
  fun x => ⟨1, Subtype.ext (by simpa using h x x.2)⟩

omit [Finite G] in
theorem a_pgroup_zpowers {a : G} (h : a ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers a) := by
  refine a_pgroup_of_exp fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem a_order_coprime {X : Subgroup G} {c : G} (hc : c ∈ P3 X) : Nat.Coprime (orderOf c) 3 := by
  obtain ⟨h, hh, rfl⟩ := hc
  have h1 : orderOf (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) ∣ Nat.card (GLAPPrimeCore 3 ↥X) :=
    orderOf_dvd_natCard _
  have : orderOf ((X.subtype h : G)) = orderOf (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) :=
    (Subgroup.orderOf_coe h).trans (Subgroup.orderOf_coe (⟨h, hh⟩ : GLAPPrimeCore 3 ↥X) :
      orderOf h = _)
  rw [this]
  exact (Nat.Coprime.coprime_dvd_left h1 CFSG.pPrimeCore_coprime_card.symm)

theorem a_cube_one {X L S : Subgroup G} {Z : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)} (hLX : L ≤ X)
    (hfus : FusData (barX 3 X L) Z) (hS : IsPGroup 3 S) {y : G} (hyS : y ∈ S) (hyL : y ∈ L) :
    y ^ 3 = 1 := by
  have hyX : y ∈ X := hLX hyL
  obtain ⟨k, hk⟩ := hS ⟨y, hyS⟩
  have hk' : y ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hmem : mkX X y hyX ∈ barX 3 X L := (a_mem_barX_iff 3 X L _).2 ⟨⟨y, hyX⟩, hyL, rfl⟩
  have hpow : (mkX X y hyX) ^ (3 ^ k) = 1 := by
    have : (mkX X y hyX) ^ (3 ^ k) = mkX X (y ^ (3 ^ k)) (X.pow_mem hyX _) := rfl
    refine this.trans ?_
    have e : (⟨y ^ (3 ^ k), X.pow_mem hyX _⟩ : ↥X) = 1 := Subtype.ext hk'
    unfold mkX
    rw [e]
    rfl
  have h3 := hfus.exp3 _ hmem ⟨k, hpow⟩
  have hy3X : y ^ 3 ∈ X := X.pow_mem hyX 3
  have : y ^ 3 ∈ P3 X := by
    rw [a_mem_P3_iff hy3X]
    exact h3
  exact a_eq_one_of_P3 this (k := k) (by rw [← pow_mul, mul_comm, pow_mul, hk', one_pow])

theorem a_exists_R1 {b : G} {L K S : Subgroup G}
    (hfus : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b)))
    (hKC : K ≤ Cb b) (hLK : L ≤ K) (hKL : K ≤ Subgroup.normalizer (L : Set G)) (hSK : S ≤ K)
    (hcard : Nat.card S = 3 ^ (Nat.card K).factorization 3) :
    ∃ y ∈ S ⊓ L, y ∉ Subgroup.zpowers b := by
  obtain ⟨ā, hāQ, hā3, hāZ⟩ := hfus.exists_noncentral
  obtain ⟨⟨a, haX⟩, haL, rfl⟩ := (a_mem_barX_iff 3 (Cb b) L _).1 hāQ
  have ha3X : a ^ 3 ∈ Cb b := (Cb b).pow_mem haX 3
  have hmkpow : ∀ n : ℕ, mkX (Cb b) (a ^ n) ((Cb b).pow_mem haX n) =
      (QuotientGroup.mk (⟨a, haX⟩ : ↥(Cb b)) : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) ^ n :=
    fun n => rfl
  have hc : a ^ 3 ∈ P3 (Cb b) := by
    rw [a_mem_P3_iff ha3X, hmkpow 3]; exact hā3
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime (a_order_coprime hc) (by norm_num)
  obtain ⟨n, hn, hn3⟩ : ∃ n : ℕ, n % 3 = 1 ∧ (a ^ n) ^ 3 = 1 := by
    refine ⟨orderOf (a ^ 3) * t, ht, ?_⟩
    calc (a ^ (orderOf (a ^ 3) * t)) ^ 3 = (a ^ 3) ^ (orderOf (a ^ 3) * t) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((a ^ 3) ^ orderOf (a ^ 3)) ^ t := by rw [pow_mul]
      _ = 1 := by rw [pow_orderOf_eq_one, one_pow]
  have han : a ^ n ∈ L := L.pow_mem haL _
  have hanX : a ^ n ∈ Cb b := (Cb b).pow_mem haX _
  have hmk : mkX (Cb b) (a ^ n) hanX = QuotientGroup.mk (⟨a, haX⟩ : ↥(Cb b)) := by
    rw [show mkX (Cb b) (a ^ n) hanX = _ from hmkpow n, ← Nat.div_add_mod n 3, hn, pow_add,
      pow_mul, hā3, one_pow, one_mul, pow_one]
  have hP : IsPGroup 3 (Subgroup.zpowers (a ^ n)) := a_pgroup_zpowers hn3
  have hPK : Subgroup.zpowers (a ^ n) ≤ K := by
    rw [Subgroup.zpowers_le]; exact hLK han
  obtain ⟨g, hgK, hg⟩ := a_exists_conj hSK hPK hP hcard
  have hy₀S := hg (a ^ n) (Subgroup.mem_zpowers _)
  have hy₀L : g⁻¹ * a ^ n * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hKL hgK)) (a ^ n)).1 han
    simpa using this
  refine ⟨g⁻¹ * a ^ n * g, ⟨hy₀S, hy₀L⟩, fun hb => hāZ ?_⟩
  have hgb : Commute g (g⁻¹ * a ^ n * g) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← hj]
    exact Commute.zpow_right
      (show Commute g b from Subgroup.mem_centralizer_singleton_iff.1 (hKC hgK)) j
  have h2 : a ^ n ∈ Subgroup.zpowers b := by
    have : g * (g⁻¹ * a ^ n * g) * g⁻¹ = g⁻¹ * a ^ n * g := by rw [hgb.eq]; group
    have h3 : a ^ n = g⁻¹ * a ^ n * g := by rw [← this]; group
    rw [h3]; exact hb
  rw [← hmk]
  exact (a_mem_barX_iff 3 (Cb b) _ _).2 ⟨⟨a ^ n, hanX⟩, h2, rfl⟩


omit [Finite G] in
theorem a_comm_of_elem {E : Subgroup G} (h : IsElemAbelian 3 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := CFSG.Open.IsElemAbelian.comm h hx hy

omit [Finite G] in
theorem a_gLBConj_sup (g : G) (X Y : Subgroup G) :
    GLBConj g (X ⊔ Y) = GLBConj g X ⊔ GLBConj g Y := by
  unfold GLBConj
  exact Subgroup.map_sup _ _ _

omit [Finite G] in
theorem a_mem_normalizer_of_eq {g : G} {K : Subgroup G} (h : GLBConj g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← mem_gLBConj, h]

omit [Finite G] in
theorem a_gLBConj_comm {g h : G} (hc : g * h = h * g) (X : Subgroup G) :
    GLBConj g (GLBConj h X) = GLBConj h (GLBConj g X) := by
  rw [gLBConj_gLBConj, gLBConj_gLBConj, hc]

omit [Finite G] in
theorem a_mem_normalizer_of_both {g : G} {R : Subgroup G} (h1 : ∀ x ∈ R, g * x * g⁻¹ ∈ R)
    (h2 : ∀ x ∈ R, g⁻¹ * x * g ∈ R) : g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun h => ?_⟩
  have := h2 _ h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem a_comm_zpowers_b {b : G} {r : G} (hr : r ∈ Cb b) {n : G} (hn : n ∈ Subgroup.zpowers b) :
    n * r = r * n := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have : Commute r b := Subgroup.mem_centralizer_singleton_iff.1 hr
  exact (this.zpow_right j).symm.eq

theorem a_b_mem {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L) (hb3 : b ^ 3 = 1)
    (hfus : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) : b ∈ L := by
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  refine q_mem_of_bar hL hbC (k := 1) (by simpa using hb3) (hfus.Zle ?_)
  exact (a_mem_barX_iff 3 (Cb b) _ _).2 ⟨⟨b, hbC⟩, Subgroup.mem_zpowers b, rfl⟩


theorem a_exists_uv {B D : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) (hset : Lemma24Setup 3 B D b L₁)
    (hconc : Lemma24Conclusion B D b L₁) :
    ∃ u ∈ L₁, ∃ v ∈ L₂, u * v = v * u ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u ∉ Subgroup.zpowers b ∧
      v ∉ Subgroup.zpowers b ∧ ∀ d ∈ D, d * (u * v) * d⁻¹ = u * v := by
  have hT := hR.tri
  have hB := hT.elemB
  have hDB : D ≤ B := hset.isEk.1
  have hDN : D ≤ Subgroup.normalizer (L₁ : Set G) := hconc.2.2.1.1
  have hb3 : b ^ 3 = 1 := hB.2 b hT.mem
  have hbL₁ : b ∈ L₁ := a_b_mem hT.comp₁ hb3 hR.fus₁
  obtain ⟨β, hβB, hβ2, hβ3, hβ1⟩ := hT.cyc
  have hKC : L₁ ⊔ L₂ ⊔ L₃ ≤ Cb b := sup_le (sup_le hT.comp₁.1 hT.comp₂.1) hT.comp₃.1
  have hL₁K : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hKL : L₁ ⊔ L₂ ⊔ L₃ ≤ Subgroup.normalizer (L₁ : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (q_le_normalizer_of_ne hT.comp₂ hT.comp₁ hT.ne₁₂.symm))
      (q_le_normalizer_of_ne hT.comp₃ hT.comp₁ hT.ne₁₃.symm)
  have hβK : GLBConj β (L₁ ⊔ L₂ ⊔ L₃) = L₁ ⊔ L₂ ⊔ L₃ := by
    rw [a_gLBConj_sup, a_gLBConj_sup, ← hβ2, ← hβ3, ← hβ1]
    ac_rfl
  have hβb : β * b = b * β := a_comm_of_elem hB hβB hT.mem
  have hdK : ∀ d ∈ D, GLBConj d (L₁ ⊔ L₂ ⊔ L₃) = L₁ ⊔ L₂ ⊔ L₃ := by
    intro d hd
    have hdβ : d * β = β * d := a_comm_of_elem hB (hDB hd) hβB
    have hd₁ : GLBConj d L₁ = L₁ := gLBConj_eq_of_mem_normalizer (hDN hd)
    have hd₂ : GLBConj d L₂ = L₂ := by
      conv_lhs => rw [hβ2]
      rw [a_gLBConj_comm hdβ, hd₁]
      exact hβ2.symm
    have hd₃ : GLBConj d L₃ = L₃ := by
      conv_lhs => rw [hβ3]
      rw [a_gLBConj_comm hdβ, hd₂]
      exact hβ3.symm
    rw [a_gLBConj_sup, a_gLBConj_sup, hd₁, hd₂, hd₃]
  set K : Subgroup G := L₁ ⊔ L₂ ⊔ L₃ with hK
  set A : Subgroup G := B ⊓ Subgroup.normalizer (K : Set G) with hAdef
  have hA : IsPGroup 3 A := a_pgroup_of_exp fun x hx => hB.2 x hx.1
  have hβA : β ∈ A := ⟨hβB, a_mem_normalizer_of_eq hβK⟩
  have hDA : D ≤ A := fun d hd => ⟨hDB hd, a_mem_normalizer_of_eq (hdK d hd)⟩
  let ψ : ↥A →* MulAut G := (MulAut.conj : G →* MulAut G).comp A.subtype
  have hH : ∀ a : ↥A, ∀ h ∈ K, ψ a h ∈ K := by
    intro a h hh
    have := (Subgroup.mem_normalizer_iff.1 a.2.2 h).1 hh
    simpa [ψ, MulAut.conj_apply] using this
  obtain ⟨S, hSK, hScard, hSinv⟩ := exists_fixed_sylow_of_action Nat.prime_three hA ψ hH
  have hSinv' : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := fun a ha s hs => by
    simpa [ψ, MulAut.conj_apply] using hSinv ⟨a, ha⟩ s hs
  have hS3 : IsPGroup 3 S := IsPGroup.of_card hScard
  have hbS : b ∈ S := by
    have hPK : Subgroup.zpowers b ≤ K := by
      rw [Subgroup.zpowers_le]; exact hL₁K hbL₁
    obtain ⟨g, hg, hgS⟩ := a_exists_conj hSK hPK (a_pgroup_zpowers hb3) hScard
    have := hgS b (Subgroup.mem_zpowers b)
    have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.1 (hKC hg)
    have e : g⁻¹ * b * g = b := by
      rw [mul_assoc, ← hgb]; group
    rwa [e] at this
  obtain ⟨y₀, hy₀, hy₀b⟩ := a_exists_R1 hR.fus₁ hKC hL₁K hKL hSK hScard
  have hD3 : IsPGroup 3 D := a_pgroup_of_exp fun x hx => hB.2 x (hDB hx)
  have hR₁ : IsPGroup 3 (S ⊓ L₁ : Subgroup G) := hS3.to_le inf_le_left
  have hDR : D ≤ Subgroup.normalizer ((S ⊓ L₁ : Subgroup G) : Set G) := by
    intro d hd
    apply a_mem_normalizer_of_both
    · intro x hx
      exact ⟨hSinv' d (hDA hd) x hx.1, (Subgroup.mem_normalizer_iff.1 (hDN hd) x).1 hx.2⟩
    · intro x hx
      refine ⟨?_, ?_⟩
      · simpa using hSinv' d⁻¹ ((A.inv_mem (hDA hd))) x hx.1
      · simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem (hDN hd)) x).1 hx.2
  have hNR : Subgroup.zpowers b ≤ S ⊓ L₁ := by
    rw [Subgroup.zpowers_le]; exact ⟨hbS, hbL₁⟩
  obtain ⟨y, hyR, hyb, hyD⟩ := a_fixed_class hR₁ hD3 hDR hNR
    (fun n hn r hr => a_comm_zpowers_b (hKC (hL₁K hr.2)) hn)
    (fun n hn d hd => a_comm_zpowers_b
      (Subgroup.mem_centralizer_singleton_iff.2 (a_comm_of_elem hB (hDB hd) hT.mem)) hn)
    (fun h => hy₀b (h ▸ hy₀))
  have hyS : y ∈ S := hyR.1
  have hyL : y ∈ L₁ := hyR.2
  have hy3 : y ^ 3 = 1 := a_cube_one hT.comp₁.1 hR.fus₁ hS3 hyS hyL
  have hβA' : β⁻¹ ∈ A := A.inv_mem hβA
  have hvS : β⁻¹ * y * β ∈ S := by simpa using hSinv' β⁻¹ hβA' y hyS
  have hvL : β⁻¹ * y * β ∈ L₂ := by
    rw [hβ2, mem_gLBConj]
    have : β * (β⁻¹ * y * β) * β⁻¹ = y := by group
    rw [this]; exact hyL
  have huS : y⁻¹ ∈ S := S.inv_mem hyS
  have huL : y⁻¹ ∈ L₁ := L₁.inv_mem hyL
  have hcomm : y⁻¹ * (β⁻¹ * y * β) = (β⁻¹ * y * β) * y⁻¹ := by
    have h1 : y⁻¹ * (β⁻¹ * y * β) * y⁻¹⁻¹ * (β⁻¹ * y * β)⁻¹ ∈ P3 (Cb b) := by
      have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₁ hT.comp₂ hT.ne₁₂
        (Subgroup.commutator_mem_commutator huL hvL)
      simpa [commutatorElement_def] using this
    have h2 : y⁻¹ * (β⁻¹ * y * β) * y⁻¹⁻¹ * (β⁻¹ * y * β)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem huS hvS) (S.inv_mem huS)) (S.inv_mem hvS)
    obtain ⟨k, hk⟩ := hS3 ⟨_, h2⟩
    have h3 := a_eq_one_of_P3 h1 (k := k) (by simpa using congrArg Subtype.val hk)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    simpa using h3
  have hβC : β ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 hβb
  have hvb : β⁻¹ * y * β ∉ Subgroup.zpowers b := by
    intro h
    apply hyb
    have e : β * (β⁻¹ * y * β) * β⁻¹ = β⁻¹ * y * β := by
      rw [← a_comm_zpowers_b hβC h]; group
    have : y = β⁻¹ * y * β := by
      calc y = β * (β⁻¹ * y * β) * β⁻¹ := by group
        _ = β⁻¹ * y * β := e
    rw [this]; exact h
  refine ⟨y⁻¹, huL, β⁻¹ * y * β, hvL, hcomm, ?_, ?_, fun h => hyb ((Subgroup.inv_mem_iff _).1 h),
    hvb, ?_⟩
  · rw [inv_pow, hy3, inv_one]
  · have := conj_pow (a := β⁻¹) (b := y) (i := 3)
    simpa [hy3] using this
  · intro d hd
    have hc : d * y * d⁻¹ * y⁻¹ ∈ Subgroup.zpowers b := hyD d hd
    have hcβ := a_comm_zpowers_b hβC hc
    have hdβ : Commute d β := a_comm_of_elem hB (hDB hd) hβB
    have key : d * (β⁻¹ * y * β) * d⁻¹ = β⁻¹ * (d * y * d⁻¹) * β := by
      calc d * (β⁻¹ * y * β) * d⁻¹ = (d * β⁻¹) * y * (β * d⁻¹) := by group
        _ = (β⁻¹ * d) * y * (d⁻¹ * β) := by
          rw [hdβ.inv_right.eq, hdβ.symm.inv_right.eq]
        _ = β⁻¹ * (d * y * d⁻¹) * β := by group
    have hdy : d * y * d⁻¹ = (d * y * d⁻¹ * y⁻¹) * y := by group
    set c := d * y * d⁻¹ * y⁻¹ with hcdef
    have hcc : β⁻¹ * c * β = c := by
      have : β⁻¹ * c * β = β⁻¹ * (c * β) := by group
      rw [this, hcβ]; group
    calc d * (y⁻¹ * (β⁻¹ * y * β)) * d⁻¹ = (d * y⁻¹ * d⁻¹) * (d * (β⁻¹ * y * β) * d⁻¹) := by group
      _ = (d * y * d⁻¹)⁻¹ * (β⁻¹ * (d * y * d⁻¹) * β) := by rw [key]; group
      _ = (c * y)⁻¹ * (β⁻¹ * (c * y) * β) := by rw [← hdy]
      _ = (c * y)⁻¹ * ((β⁻¹ * c * β) * (β⁻¹ * y * β)) := by group
      _ = y⁻¹ * (β⁻¹ * y * β) := by rw [hcc]; group

theorem case_a_good (h25 : Lemma25Strong) {m : ℕ} (hS : GLStanding G m 3) {B D : Subgroup G}
    {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃) (hset : Lemma24Setup 3 B D b L₁)
    (hconc : Lemma24Conclusion B D b L₁)
    (hZ : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L₁)) :
    ∃ u ∈ L₁, ∃ v ∈ L₂, u * v = v * u ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u ∉ Subgroup.zpowers b ∧
      v ∉ Subgroup.zpowers b ∧ b ∈ oPrimePOf 3 (Cb (u * v)) := by
  obtain ⟨u, hu, v, hv, hc, hu3, hv3, hnu, hnv, hD⟩ := a_exists_uv hR hset hconc
  exact ⟨u, hu, v, hv, hc, hu3, hv3, hnu, hnv,
    a_finish h25 hS hR hset hZ hu hv hc hu3 hv3 hnu hD⟩

end CaseA

section Sy3Sec

omit [Finite G] in
private theorem sy3_card_sup_mul_card_inf {K : Type*} [Group K] {A B : Subgroup K}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let μ : A × B →* K :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hcomm x x.2 y y.2
  have hμ : ∀ x : A × B, μ x = (x.1 : K) * x.2 := fun _ => rfl
  have hrange : μ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card μ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : K), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : K)⁻¹, B.inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact B.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Subtype.ext (Prod.ext rfl (Subtype.ext h))
  have h := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at h
  rwa [mul_comm]

omit [Finite G] in
private theorem sy3_sylow_inf_normal {K : Type*} [Group K] [Finite K] (S : Sylow 3 K)
    {N : Subgroup K} [N.Normal] :
    ∃ P : Sylow 3 ↥N, (P : Subgroup ↥N) = ((S : Subgroup K) ⊓ N).subgroupOf N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  let P : Subgroup ↥N := ((S : Subgroup K) ⊓ N).subgroupOf N
  have hP1 : IsPGroup 3 P := by
    have hSn : IsPGroup 3 (↥((S : Subgroup K) ⊓ N)) := S.isPGroup'.to_inf_left
    exact hSn.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup K) ⊓ N) (K := N) inf_le_right).symm
  have hrel1 :
      ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) *
          (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) =
        ((S : Subgroup K) ⊓ N).relIndex ((S : Subgroup K) ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H := (S : Subgroup K) ⊓ N)
      (K := (S : Subgroup K)) (L := (S : Subgroup K) ⊔ N) inf_le_left le_sup_left
  have hrel2 :
      ((S : Subgroup K) ⊓ N).relIndex N * N.relIndex ((S : Subgroup K) ⊔ N) =
        ((S : Subgroup K) ⊓ N).relIndex ((S : Subgroup K) ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H := (S : Subgroup K) ⊓ N) (K := N)
      (L := (S : Subgroup K) ⊔ N) inf_le_right le_sup_right
  have h2a : N.relIndex ((S : Subgroup K) ⊔ N) = N.relIndex (S : Subgroup K) :=
    Subgroup.relIndex_sup_right (H := (S : Subgroup K)) (K := N)
  have h2a' : N.relIndex (S : Subgroup K) = ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) :=
    (Subgroup.inf_relIndex_left (H := (S : Subgroup K)) (K := N)).symm
  have hrel2' :
      ((S : Subgroup K) ⊓ N).relIndex N * ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) =
        ((S : Subgroup K) ⊓ N).relIndex ((S : Subgroup K) ⊔ N) := by
    simpa [h2a, h2a'] using hrel2
  have hcanc : ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) ≠ 0 := by
    intro hz
    have hdvd : ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) ∣
        ((S : Subgroup K) ⊓ N).index :=
      Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup K) ⊓ N)
        (K := (S : Subgroup K)) inf_le_left
    have hSne : ((S : Subgroup K) ⊓ N).index ≠ 0 :=
      (Subgroup.finiteIndex_of_finite (H := (S : Subgroup K) ⊓ N)).index_ne_zero
    exact hSne (eq_zero_of_zero_dvd (by simpa [hz] using hdvd))
  have hrel : ((S : Subgroup K) ⊓ N).relIndex N =
      (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) := by
    have h' : ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) *
          (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) =
        ((S : Subgroup K) ⊓ N).relIndex N *
          ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) :=
      hrel1.trans hrel2'.symm
    have h'' : (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) *
          ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) =
        ((S : Subgroup K) ⊓ N).relIndex N *
          ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K) := by
      simpa [mul_comm] using h'
    exact (Nat.mul_right_cancel (m := ((S : Subgroup K) ⊓ N).relIndex (S : Subgroup K))
      (Nat.pos_of_ne_zero hcanc) h'').symm
  have hP2 : ¬ 3 ∣ P.index := by
    intro hp
    have hp' : 3 ∣ (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) := by
      change 3 ∣ ((S : Subgroup K) ⊓ N).relIndex N at hp
      rwa [hrel] at hp
    have hdvd : (S : Subgroup K).relIndex ((S : Subgroup K) ⊔ N) ∣
        (S : Subgroup K).index :=
      Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup K))
        (K := (S : Subgroup K) ⊔ N) le_sup_left
    exact S.not_dvd_index (hp'.trans hdvd)
  exact ⟨hP1.toSylow hP2, rfl⟩

omit [Finite G] in
private theorem sy3_card_sylow_inf_normal {K : Type*} [Group K] [Finite K] (S : Sylow 3 K)
    (N : Subgroup K) [N.Normal] :
    Nat.card ↥((S : Subgroup K) ⊓ N) = 3 ^ (Nat.card N).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P', hP'⟩ := sy3_sylow_inf_normal S (N := N)
  have e2 : Nat.card ↥((S : Subgroup K) ⊓ N) =
      Nat.card ↥(((S : Subgroup K) ⊓ N).subgroupOf N) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  rw [e2, ← hP']
  exact Sylow.card_eq_multiplicity P'

omit [Finite G] in
private theorem sy3_card_normal_mul {K : Type*} [Group K] (U V : Subgroup K) [U.Normal]
    [V.Normal] :
    Nat.card ↥(U ⊔ V) * Nat.card ↥(U ⊓ V) = Nat.card ↥U * Nat.card ↥V := by
  have h1 : Nat.card ↥V * V.relIndex (U ⊔ V) = Nat.card ↥(U ⊔ V) := by
    have hmul := (V.subgroupOf (U ⊔ V)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : V ≤ U ⊔ V)).toEquiv] at hmul
    exact hmul
  have h2 : Nat.card ↥(U ⊓ V) * (U ⊓ V).relIndex U = Nat.card ↥U := by
    have hmul := ((U ⊓ V).subgroupOf U).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : U ⊓ V ≤ U)).toEquiv] at hmul
    exact hmul
  have h3 : V.relIndex (U ⊔ V) = (U ⊓ V).relIndex U := by
    rw [Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_left]
  rw [← h1, ← h2, h3]
  ring

omit [Finite G] in
private theorem sy3_sup_inf {K : Type*} [Group K] [Finite K] (S : Sylow 3 K)
    (U V : Subgroup K) [U.Normal] [V.Normal]
    (hAB : ∀ a ∈ (S : Subgroup K) ⊓ U, ∀ b ∈ (S : Subgroup K) ⊓ V, a * b = b * a) :
    ((S : Subgroup K) ⊓ U) ⊔ ((S : Subgroup K) ⊓ V) = (S : Subgroup K) ⊓ (U ⊔ V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup K := (S : Subgroup K) ⊓ U with hA
  set B : Subgroup K := (S : Subgroup K) ⊓ V with hB
  have hAB' : A ⊓ B = (S : Subgroup K) ⊓ (U ⊓ V) := by
    ext y
    simp only [hA, hB, Subgroup.mem_inf]
    tauto
  have hcA := sy3_card_sylow_inf_normal S U
  have hcB := sy3_card_sylow_inf_normal S V
  have hcI := sy3_card_sylow_inf_normal S (U ⊓ V)
  have hcW := sy3_card_sylow_inf_normal S (U ⊔ V)
  have hprod := sy3_card_sup_mul_card_inf hAB
  have hN := sy3_card_normal_mul U V
  have hpos : ∀ N : Subgroup K, Nat.card ↥N ≠ 0 := fun N => Nat.card_pos.ne'
  have hfac := congrArg (fun n => n.factorization 3) hN
  simp only [Nat.factorization_mul (hpos _) (hpos _), Finsupp.add_apply] at hfac
  have hle : A ⊔ B ≤ (S : Subgroup K) ⊓ (U ⊔ V) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hd : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hd
  rw [hprod, hAB', hcW, hcI, hcA, hcB, ← pow_add, ← pow_add, hfac]

private theorem sy3_p3_trivial {C : Subgroup G} {z : G} (hz : z ∈ P3 C) {k : ℕ}
    (hk : z ^ (3 ^ k) = 1) : z = 1 := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  have h1 : z' ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have h2 : orderOf z' ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf z' ∣ Nat.card (GLAPPrimeCore 3 ↥C) := by
    have := orderOf_dvd_natCard (⟨z', hz'⟩ : GLAPPrimeCore 3 ↥C)
    simpa using this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (GLAPPrimeCore 3 ↥C)) :=
    Nat.Coprime.pow_left k (coprime_card_gLAPPrimeCore_aux 3 ↥C)
  have h4 : orderOf z' = 1 := (hcop.coprime_dvd_left h2).eq_one_of_dvd h3
  have : z' = 1 := orderOf_eq_one_iff.1 h4
  simp [this]

private theorem sy3_comm_R {b : G} {Li Lj R : Subgroup G} (hLi : GLAPComponent 3 (Cb b) Li)
    (hLj : GLAPComponent 3 (Cb b) Lj) (hne : Li ≠ Lj) (hR : IsPGroup 3 R) {a c : G}
    (ha : a ∈ R ⊓ Li) (hc : c ∈ R ⊓ Lj) : a * c = c * a := by
  have hcm := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hLi hLj hne
    (Subgroup.commutator_mem_commutator ha.2 hc.2)
  have hmem : a * c * a⁻¹ * c⁻¹ ∈ R :=
    mul_mem (mul_mem (mul_mem ha.1 hc.1) (inv_mem ha.1)) (inv_mem hc.1)
  obtain ⟨k, hk⟩ := hR ⟨_, hmem⟩
  have h1 : a * c * a⁻¹ * c⁻¹ = 1 :=
    sy3_p3_trivial hcm (k := k) (by simpa using congrArg Subtype.val hk)
  calc a * c = (a * c * a⁻¹ * c⁻¹) * (c * a) := by group
    _ = c * a := by rw [h1, one_mul]

omit [Finite G] in
private theorem sy3_conj_mem {B L : Subgroup G} {g : G} (hg : g ∈ B) {k : G}
    (hk : k ∈ bClosure B L) : g * k * g⁻¹ ∈ bClosure B L := by
  have hle : bClosure B L ≤ (bClosure B L).comap (MulAut.conj g).toMonoidHom := by
    change (⨆ b ∈ B, GLBConj b L) ≤ _
    refine iSup₂_le fun h hh y hy => ?_
    rw [mem_gLBConj] at hy
    show g * y * g⁻¹ ∈ bClosure B L
    have hmem : h * g⁻¹ ∈ B := mul_mem hh (inv_mem hg)
    have : g * y * g⁻¹ ∈ GLBConj (h * g⁻¹) L := by
      rw [mem_gLBConj]
      have e : h * g⁻¹ * (g * y * g⁻¹) * (h * g⁻¹)⁻¹ = h * y * h⁻¹ := by group
      rw [e]; exact hy
    exact (le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b L) (h * g⁻¹) hmem : GLBConj (h * g⁻¹) L ≤ bClosure B L) this
  exact hle hk

omit [Finite G] in
private theorem sy3_zpowers_pgroup {K : Type*} [Group K] {x : K} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rintro ⟨g, n, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [OneMemClass.coe_one, SubgroupClass.coe_pow]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_one, hx, one_zpow]

theorem three_sylow {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hT : Tri B b L₁ L₂ L₃)
    (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃) (hbK : b ∈ bClosure B L₁) :
    ∃ R R₁ R₂ R₃ : Subgroup G, SylData B b L₁ L₂ L₃ R R₁ R₂ R₃ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  rw [hK] at hbK
  set K : Subgroup G := L₁ ⊔ L₂ ⊔ L₃ with hKdef
  have hBp : IsPGroup 3 B := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hT.elemB.2 g hg
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := sy3_conj_mem (L := L₁) hg (k := x) (by rw [hK]; exact hx)
      rwa [hK] at this
    · intro hx
      have := sy3_conj_mem (L := L₁) (inv_mem hg) (k := g * x * g⁻¹) (by rw [hK]; exact hx)
      rw [hK] at this
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at this
  obtain ⟨S, hSK, hScard, hSB⟩ := exists_normalized_sylow hBp hBK
  let S' : Sylow 3 ↥K := Sylow.ofCard (S.subgroupOf K)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]; exact hScard)
  have hS' : (S' : Subgroup ↥K) = S.subgroupOf K := rfl
  have hLK₁ : L₁ ≤ K := le_trans le_sup_left le_sup_left
  have hLK₂ : L₂ ≤ K := le_trans le_sup_right le_sup_left
  have hLK₃ : L₃ ≤ K := le_sup_right
  have hN₁ : K ≤ Subgroup.normalizer (L₁ : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (q_le_normalizer_of_ne hT.comp₂ hT.comp₁ hT.ne₁₂.symm))
      (q_le_normalizer_of_ne hT.comp₃ hT.comp₁ hT.ne₁₃.symm)
  have hN₂ : K ≤ Subgroup.normalizer (L₂ : Set G) :=
    sup_le (sup_le (q_le_normalizer_of_ne hT.comp₁ hT.comp₂ hT.ne₁₂) Subgroup.le_normalizer)
      (q_le_normalizer_of_ne hT.comp₃ hT.comp₂ hT.ne₂₃.symm)
  have hN₃ : K ≤ Subgroup.normalizer (L₃ : Set G) :=
    sup_le (sup_le (q_le_normalizer_of_ne hT.comp₁ hT.comp₃ hT.ne₁₃)
      (q_le_normalizer_of_ne hT.comp₂ hT.comp₃ hT.ne₂₃)) Subgroup.le_normalizer
  have n₁ : (L₁.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK₁).2 hN₁
  have n₂ : (L₂.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK₂).2 hN₂
  have n₃ : (L₃.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK₃).2 hN₃
  have hbS : b ∈ S := by
    have hb3 : b ^ 3 = 1 := by simpa using hT.elemB.2 b hT.mem
    have hbC : ∀ k ∈ K, k * b = b * k := by
      intro k hk
      have hkC : k ∈ Cb b := by
        refine (sup_le (sup_le hT.comp₁.1 hT.comp₂.1) hT.comp₃.1 : K ≤ Cb b) hk
      simpa using Subgroup.mem_centralizer_singleton_iff.1 hkC
    let bK : ↥K := ⟨b, hbK⟩
    have : (Subgroup.zpowers bK).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : g * bK = bK * g := Subtype.ext (hbC g g.2)
      have : g * bK ^ m * g⁻¹ = bK ^ m := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (Commute.zpow_right (show Commute g bK from hc) m).eq
      rw [this]; exact Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩
    have hbS' : bK ∈ (S' : Subgroup ↥K) :=
      (sy3_zpowers_pgroup (x := bK) (Subtype.ext (by simpa [bK] using hb3))).le_sylow_of_normal S'
        (Subgroup.mem_zpowers bK)
    exact Subgroup.mem_subgroupOf.1 hbS'
  have hA : ∀ (Li Lj : Subgroup G), GLAPComponent 3 (Cb b) Li → GLAPComponent 3 (Cb b) Lj →
      Li ≠ Lj → ∀ a ∈ (S' : Subgroup ↥K) ⊓ Li.subgroupOf K,
        ∀ c ∈ (S' : Subgroup ↥K) ⊓ Lj.subgroupOf K, a * c = c * a := by
    intro Li Lj hLi hLj hne a ha c hc
    refine Subtype.ext ?_
    have := sy3_comm_R (R := S) hLi hLj hne (IsPGroup.of_card hScard)
      (a := (a : G)) (c := (c : G))
      ⟨Subgroup.mem_subgroupOf.1 ha.1, Subgroup.mem_subgroupOf.1 ha.2⟩
      ⟨Subgroup.mem_subgroupOf.1 hc.1, Subgroup.mem_subgroupOf.1 hc.2⟩
    simpa using this
  have hc12 := hA L₁ L₂ hT.comp₁ hT.comp₂ hT.ne₁₂
  have hc13 := hA L₁ L₃ hT.comp₁ hT.comp₃ hT.ne₁₃
  have hc23 := hA L₂ L₃ hT.comp₂ hT.comp₃ hT.ne₂₃
  have e12 := sy3_sup_inf S' (L₁.subgroupOf K) (L₂.subgroupOf K) hc12
  have hc3 : ∀ a ∈ (S' : Subgroup ↥K) ⊓ (L₁.subgroupOf K ⊔ L₂.subgroupOf K),
      ∀ c ∈ (S' : Subgroup ↥K) ⊓ L₃.subgroupOf K, a * c = c * a := by
    intro a ha c hc
    rw [← e12] at ha
    have hle : ((S' : Subgroup ↥K) ⊓ L₁.subgroupOf K) ⊔ ((S' : Subgroup ↥K) ⊓ L₂.subgroupOf K) ≤
        Subgroup.centralizer ({c} : Set ↥K) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hc13 x hx c hc)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hc23 x hx c hc)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
  have e123 := sy3_sup_inf S' (L₁.subgroupOf K ⊔ L₂.subgroupOf K) (L₃.subgroupOf K) hc3
  have htop : L₁.subgroupOf K ⊔ L₂.subgroupOf K ⊔ L₃.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLK₁ hLK₂,
      ← Subgroup.subgroupOf_sup (sup_le hLK₁ hLK₂) hLK₃]
    exact Subgroup.subgroupOf_self K
  have hSeq : (S' : Subgroup ↥K) = ((S' : Subgroup ↥K) ⊓ L₁.subgroupOf K) ⊔
      ((S' : Subgroup ↥K) ⊓ L₂.subgroupOf K) ⊔ ((S' : Subgroup ↥K) ⊓ L₃.subgroupOf K) := by
    rw [e12, e123, htop, inf_top_eq]
  have hmap : ∀ L : Subgroup G,
      ((S' : Subgroup ↥K) ⊓ L.subgroupOf K).map K.subtype = S ⊓ L := by
    intro L
    have : (S' : Subgroup ↥K) ⊓ L.subgroupOf K = (S ⊓ L).subgroupOf K := by
      ext x; simp [hS', Subgroup.mem_subgroupOf]
    rw [this]
    exact Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hSK)
  have hcard : ∀ (L : Subgroup G) (hLK : L ≤ K) [(L.subgroupOf K).Normal],
      Nat.card ↥(S ⊓ L) = 3 ^ (Nat.card ↥L).factorization 3 := by
    intro L hLK _
    have h1 : Nat.card ↥(S ⊓ L) = Nat.card ↥((S' : Subgroup ↥K) ⊓ L.subgroupOf K) := by
      rw [← hmap L]
      exact Subgroup.card_map_of_injective K.subtype_injective
    rw [h1, sy3_card_sylow_inf_normal S' (L.subgroupOf K),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv]
  have hprod : S = (S ⊓ L₁) ⊔ (S ⊓ L₂) ⊔ (S ⊓ L₃) := by
    have := congrArg (Subgroup.map K.subtype) hSeq
    rw [Subgroup.map_sup, Subgroup.map_sup, hmap, hmap, hmap, hS',
      Subgroup.map_subgroupOf_eq_of_le hSK] at this
    exact this
  refine ⟨S, S ⊓ L₁, S ⊓ L₂, S ⊓ L₃, ?_⟩
  exact
    { hRK := hSK
      hRp := IsPGroup.of_card hScard
      hRs := hScard
      hbR := hbS
      hRB := hSB
      h1 := rfl
      h2 := rfl
      h3 := rfl
      hprod := hprod
      c12 := fun a ha c hc => sy3_comm_R hT.comp₁ hT.comp₂ hT.ne₁₂ (IsPGroup.of_card hScard) ha hc
      c23 := fun a ha c hc => sy3_comm_R hT.comp₂ hT.comp₃ hT.ne₂₃ (IsPGroup.of_card hScard) ha hc
      c13 := fun a ha c hc => sy3_comm_R hT.comp₁ hT.comp₃ hT.ne₁₃ (IsPGroup.of_card hScard) ha hc
      s1 := hcard L₁ hLK₁
      s2 := hcard L₂ hLK₂
      s3 := hcard L₃ hLK₃ }

end Sy3Sec

section Rk5Sec

omit [Finite G] in
theorem rk5_mem_ZR_iff {R : Subgroup G} {z : G} :
    z ∈ ZR R ↔ z ∈ R ∧ ∀ r ∈ R, z * r = r * z := by
  unfold ZR
  constructor
  · rintro ⟨⟨z', hz'⟩, hc, rfl⟩
    refine ⟨hz', fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨r, hr⟩
    simpa using congrArg Subtype.val this.symm
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun r => ?_, rfl⟩
    exact Subtype.ext (hc r r.2).symm

omit [Finite G] in
theorem rk5_ZR_le {R : Subgroup G} : ZR R ≤ R := fun _ hz => (rk5_mem_ZR_iff.1 hz).1

theorem rk5_card_ZR {R : Subgroup G} (h27 : Nat.card R = 27)
    (hnab : ¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) : Nat.card (ZR R) = 3 := by
  have hcard : Nat.card (ZR R) = Nat.card (Subgroup.center ↥R) :=
    Subgroup.card_map_of_injective R.subtype_injective
  rw [hcard]
  have hp : IsPGroup 3 R := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card (n := 3) (by rw [h27]; norm_num)
  have : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial, h27]; norm_num
  have := hp.center_nontrivial
  have hdvd : Nat.card (Subgroup.center ↥R) ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥R)
    rwa [h27] at this
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hgt : 1 < Nat.card (Subgroup.center ↥R) := Finite.one_lt_card
  interval_cases k
  · omega
  · simpa using hkc
  · exfalso
    have hq : Nat.card (↥R ⧸ Subgroup.center ↥R) = 3 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥R)
      rw [h27, hkc] at this
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic (↥R ⧸ Subgroup.center ↥R) := isCyclic_of_prime_card hq
    apply hnab
    intro a ha c hc
    have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center ↥R)) (by simp)
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : R) ⟨c, hc⟩)
  · exfalso
    apply hnab
    intro a ha c hc
    have hcen : Subgroup.center ↥R = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hkc, h27]; norm_num)
    have : (⟨a, ha⟩ : R) ∈ Subgroup.center ↥R := by rw [hcen]; trivial
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 this ⟨c, hc⟩).symm

theorem rk5_local {R : Subgroup G} (h27 : Nat.card R = 27)
    (hnab : ¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) (hexp : ∀ a ∈ R, a ^ 3 = 1) {x : G} (hx : x ∈ R) :
    ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ZR R ≤ E ∧ E ≤ Cb x := by
  have hZc := rk5_card_ZR h27 hnab
  have hZcomm : ∀ z ∈ ZR R, ∀ r ∈ R, z * r = r * z := fun z hz => (rk5_mem_ZR_iff.1 hz).2
  obtain ⟨w, hwR, hwZ, hwx⟩ : ∃ w ∈ R, w ∉ ZR R ∧ w * x = x * w := by
    by_cases hxZ : x ∈ ZR R
    · by_contra hcon
      apply hnab
      intro a ha c hc
      by_cases haZ : a ∈ ZR R
      · exact hZcomm a haZ c hc
      · exact absurd ⟨a, ha, haZ, (hZcomm x hxZ a ha).symm⟩ hcon
    · exact ⟨x, hx, hxZ, rfl⟩
  have hw3 := hexp w hwR
  have hwc : ∀ h ∈ ZR R, h * w = w * h := fun h hh => hZcomm h hh w hwR
  have hZel : IsElemAbelian 3 (ZR R) :=
    ⟨⟨⟨fun a b => Subtype.ext (hZcomm a.1 a.2 b.1 (rk5_ZR_le b.2))⟩⟩,
      fun z hz => hexp z (rk5_ZR_le hz)⟩
  have hWel : IsElemAbelian 3 (Subgroup.zpowers w) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have hZW : ZR R ≤ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute w z from (hwc z hz).symm).zpow_left n).eq
  refine ⟨ZR R ⊔ Subgroup.zpowers w, sup_le rk5_ZR_le ((Subgroup.zpowers_le).2 hwR),
    isElemAbelian_sup_of_commute hZel hWel hZW, ?_, le_sup_left, sup_le ?_ ?_⟩
  · rw [card_sup_zpowers_of_pow_three_eq_one hw3 hwZ hwc, hZc]
  · intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hZcomm z hz x hx
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hwx

theorem rk5_inf_eq_bot {A B : Subgroup G} (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hne : A ≠ B) : A ⊓ B = ⊥ := by
  have hd : Nat.card ↥(A ⊓ B) ∣ 3 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    apply hne
    have h1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hA])
    have h2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hB])
    rw [← h1, h2]

theorem rk5_sup_eq {A B C : Subgroup G} (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hne : A ≠ B) (h9 : Nat.card ↥(A ⊔ B ⊔ C) = 9) : A ⊔ B = A ⊔ B ⊔ C := by
  have hd9 : Nat.card ↥(A ⊔ B) ∣ 9 := h9 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hd3 : 3 ∣ Nat.card ↥(A ⊔ B) := hA ▸ Subgroup.card_dvd_of_le le_sup_left
  have hcases : Nat.card ↥(A ⊔ B) = 3 ∨ Nat.card ↥(A ⊔ B) = 9 := by
    have : Nat.card ↥(A ⊔ B) ≤ 9 := Nat.le_of_dvd (by norm_num) hd9
    have h0 : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    interval_cases h : Nat.card ↥(A ⊔ B) <;> simp_all
  rcases hcases with h | h
  · exfalso
    apply hne
    have h1 : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hA])
    have h2 : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, hB])
    rw [h1, ← h2]
  · exact Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, h9])

omit [Finite G] in
theorem rk5_comm_of_mul_eq_one {x y r : G} (h : x * y = 1) (hr : r * y = y * r) :
    r * x = x * r := by
  have hx : x = y⁻¹ := eq_inv_of_mul_eq_one_left h
  subst hx
  exact ((show Commute r y from hr).inv_right).eq

omit [Finite G] in
theorem rk5_mul_aux (a b c a' b' c' : G) (e1 : b * a' = a' * b) (e2 : c * a' = a' * c)
    (e3 : c * b' = b' * c) : a * a' * (b * b') * (c * c') = a * b * c * (a' * b' * c') := by
  symm
  calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
    _ = a * b * (a' * c) * b' * c' := by rw [e2]
    _ = a * (b * a') * c * b' * c' := by group
    _ = a * (a' * b) * c * b' * c' := by rw [e1]
    _ = a * a' * b * (c * b') * c' := by group
    _ = a * a' * b * (b' * c) * c' := by rw [e3]
    _ = a * a' * (b * b') * (c * c') := by group

def rk5_psi (E₁ E₂ E₃ : Subgroup G) (h12 : ∀ a ∈ E₁, ∀ c ∈ E₂, a * c = c * a)
    (h23 : ∀ a ∈ E₂, ∀ c ∈ E₃, a * c = c * a) (h13 : ∀ a ∈ E₁, ∀ c ∈ E₃, a * c = c * a) :
    ↥E₁ × ↥E₂ × ↥E₃ →* G where
  toFun p := (p.1 : G) * p.2.1 * p.2.2
  map_one' := by simp
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    exact rk5_mul_aux _ _ _ _ _ _ (h12 a' a'.2 b b.2).symm (h13 a' a'.2 c c.2).symm
      (h23 b' b'.2 c c.2).symm

theorem rk5_core {R₁ R₂ R₃ E₁ E₂ E₃ : Subgroup G}
    (h12 : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a) (h23 : ∀ a ∈ R₂, ∀ c ∈ R₃, a * c = c * a)
    (h13 : ∀ a ∈ R₁, ∀ c ∈ R₃, a * c = c * a)
    (hZ1 : Nat.card (ZR R₁) = 3) (hZ2 : Nat.card (ZR R₂) = 3) (hZ3 : Nat.card (ZR R₃) = 3)
    (hZ : Nat.card ↥(ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃) = 9) (h12' : ZR R₁ ≠ ZR R₂)
    (hE1 : E₁ ≤ R₁) (hE2 : E₂ ≤ R₂) (hE3 : E₃ ≤ R₃)
    (hel1 : IsElemAbelian 3 E₁) (hel2 : IsElemAbelian 3 E₂) (hel3 : IsElemAbelian 3 E₃)
    (hc1 : Nat.card E₁ = 9) (hc2 : Nat.card E₂ = 9) (hc3 : Nat.card E₃ = 9)
    (hz1 : ZR R₁ ≤ E₁) (hz2 : ZR R₂ ≤ E₂) (hz3 : ZR R₃ ≤ E₃) :
    ∃ E : Subgroup G, E ≤ E₁ ⊔ E₂ ⊔ E₃ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
  have g12 : ∀ a ∈ E₁, ∀ c ∈ E₂, a * c = c * a := fun a ha c hc => h12 a (hE1 ha) c (hE2 hc)
  have g23 : ∀ a ∈ E₂, ∀ c ∈ E₃, a * c = c * a := fun a ha c hc => h23 a (hE2 ha) c (hE3 hc)
  have g13 : ∀ a ∈ E₁, ∀ c ∈ E₃, a * c = c * a := fun a ha c hc => h13 a (hE1 ha) c (hE3 hc)
  set ψ := rk5_psi E₁ E₂ E₃ g12 g23 g13 with hψ
  have hψapp : ∀ p : ↥E₁ × ↥E₂ × ↥E₃, ψ p = (p.1 : G) * p.2.1 * p.2.2 := fun _ => rfl
  have hker3 : Nat.card ψ.ker = 3 := by
    have hmem : ∀ p : ↥E₁ × ↥E₂ × ↥E₃, p ∈ ψ.ker → ((p.1 : G) ∈ ZR R₁ ∧ (p.2.1 : G) ∈ ZR R₂ ∧
        (p.2.2 : G) ∈ ZR R₃) := by
      rintro ⟨a, b, c⟩ hp
      have h1 : (a : G) * b * c = 1 := hp
      have hba : (b : G) * a = a * b := (g12 a a.2 b b.2).symm
      refine ⟨rk5_mem_ZR_iff.2 ⟨hE1 a.2, fun r hr => ?_⟩, rk5_mem_ZR_iff.2 ⟨hE2 b.2, fun r hr => ?_⟩,
        rk5_mem_ZR_iff.2 ⟨hE3 c.2, fun r hr => ?_⟩⟩
      · have hrb : Commute r (b : G) := h12 r hr b (hE2 b.2)
        have hrc : Commute r (c : G) := h13 r hr c (hE3 c.2)
        exact (rk5_comm_of_mul_eq_one (x := (a : G)) (y := b * c) (by rwa [← mul_assoc])
          (hrb.mul_right hrc).eq).symm
      · have hra : Commute r (a : G) := (h12 a (hE1 a.2) r hr).symm
        have hrc : Commute r (c : G) := h23 r hr c (hE3 c.2)
        exact (rk5_comm_of_mul_eq_one (x := (b : G)) (y := a * c)
          (by rw [← mul_assoc, hba]; exact h1) (hra.mul_right hrc).eq).symm
      · have hra : Commute r (a : G) := (h13 a (hE1 a.2) r hr).symm
        have hrb : Commute r (b : G) := (h23 b (hE2 b.2) r hr).symm
        exact (rk5_comm_of_mul_eq_one (x := (c : G)) (y := a * b) (mul_eq_one_comm.1 h1)
          (hra.mul_right hrb).eq).symm
    let f : ψ.ker → ↥(ZR R₃) := fun p => ⟨(p.1.2.2 : G), (hmem p.1 p.2).2.2⟩
    have hbot : ZR R₁ ⊓ ZR R₂ = ⊥ := rk5_inf_eq_bot hZ1 hZ2 h12'
    have hsup : ZR R₁ ⊔ ZR R₂ = ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃ := rk5_sup_eq hZ1 hZ2 h12' hZ
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨⟨a, b, c⟩, hp⟩ ⟨⟨a', b', c'⟩, hq⟩ hpq
        have hc : (c : G) = c' := by
          have := congrArg Subtype.val hpq
          exact this
        have h1 : (a : G) * b * c = 1 := hp
        have h1' : (a' : G) * b' * c' = 1 := hq
        obtain ⟨haZ, hbZ, -⟩ := hmem _ hp
        obtain ⟨ha'Z, hb'Z, -⟩ := hmem _ hq
        have hab : (a : G) * b = a' * b' := by
          have := h1.trans h1'.symm
          rw [hc] at this
          exact mul_right_cancel this
        have hg1 : (a' : G)⁻¹ * a ∈ ZR R₁ := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha'Z) haZ
        have hg2 : (a' : G)⁻¹ * a ∈ ZR R₂ := by
          have : (a' : G)⁻¹ * a * b = b' := by rw [mul_assoc, hab, inv_mul_cancel_left]
          rw [eq_mul_inv_of_mul_eq this]
          exact Subgroup.mul_mem _ hb'Z (Subgroup.inv_mem _ hbZ)
        have hg : (a' : G)⁻¹ * a ∈ ZR R₁ ⊓ ZR R₂ := ⟨hg1, hg2⟩
        rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hg
        have haa : (a : G) = a' := hg.symm
        have hbb : (b : G) = b' := by
          rw [haa] at hab
          exact mul_left_cancel hab
        exact Subtype.ext (Prod.ext (Subtype.ext haa) (Prod.ext (Subtype.ext hbb) (Subtype.ext hc)))
      · rintro ⟨c, hcZ⟩
        have hle : ZR R₃ ≤ ZR R₁ ⊔ ZR R₂ := by rw [hsup]; exact le_sup_right
        have hcm : (c : G)⁻¹ ∈ ZR R₁ ⊔ ZR R₂ := Subgroup.inv_mem _ (hle hcZ)
        have hcomm : ZR R₁ ≤ Subgroup.centralizer ((ZR R₂ : Subgroup G) : Set G) := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          exact (h12 z (rk5_ZR_le hz) h (rk5_ZR_le hh)).symm
        obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hcomm hcm
        refine ⟨⟨(⟨a, hz1 ha⟩, ⟨b, hz2 hb⟩, ⟨c, hz3 hcZ⟩), MonoidHom.mem_ker.2 ?_⟩, rfl⟩
        show a * b * c = 1
        rw [← hab]
        exact inv_mul_cancel _
    rw [Nat.card_congr (Equiv.ofBijective f hf), hZ3]
  refine ⟨ψ.range, ?_, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨p, rfl⟩
    rw [hψapp]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left p.1.2))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right p.2.1.2)))
      (Subgroup.mem_sup_right p.2.2.2)
  · obtain ⟨p, hp⟩ := x.2
    obtain ⟨q, hq⟩ := y.2
    show (x : G) * y = y * x
    rw [← hp, ← hq, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (Subtype.ext (elemAbelian_comm hel1 p.1.2 q.1.2))
      (Prod.ext (Subtype.ext (elemAbelian_comm hel2 p.2.1.2 q.2.1.2))
        (Subtype.ext (elemAbelian_comm hel3 p.2.2.2 q.2.2.2)))
  · rintro _ ⟨p, rfl⟩
    rw [← map_pow]
    have : p ^ 3 = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · simpa using hel1.2 _ p.1.2
      · simpa using hel2.2 _ p.2.1.2
      · simpa using hel3.2 _ p.2.2.2
    rw [this, map_one]
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker3, Nat.card_prod,
      Nat.card_prod, hc1, hc2, hc3] at h1
    omega

theorem rk5_le_pRank {H E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : k ≤ CFSG.Open.pRank 3 H :=
  CFSG.SectionRank.le_pRank (by norm_num) hEH hE hk

theorem rank5_of_three_extraspecial {R₁ R₂ R₃ : Subgroup G}
    (h12 : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a) (h23 : ∀ a ∈ R₂, ∀ c ∈ R₃, a * c = c * a)
    (h13 : ∀ a ∈ R₁, ∀ c ∈ R₃, a * c = c * a)
    (hR₁ : Nat.card R₁ = 27 ∧ (¬ ∀ a ∈ R₁, ∀ c ∈ R₁, a * c = c * a) ∧ ∀ a ∈ R₁, a ^ 3 = 1)
    (hR₂ : Nat.card R₂ = 27 ∧ (¬ ∀ a ∈ R₂, ∀ c ∈ R₂, a * c = c * a) ∧ ∀ a ∈ R₂, a ^ 3 = 1)
    (hR₃ : Nat.card R₃ = 27 ∧ (¬ ∀ a ∈ R₃, ∀ c ∈ R₃, a * c = c * a) ∧ ∀ a ∈ R₃, a ^ 3 = 1)
    (hZ : Nat.card ↥(ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃) = 9) (h12' : ZR R₁ ≠ ZR R₂) (h23' : ZR R₂ ≠ ZR R₃)
    (h13' : ZR R₁ ≠ ZR R₃) :
    ∀ x ∈ R₁ ⊔ R₂ ⊔ R₃, 5 ≤ CFSG.Open.pRank 3 ((R₁ ⊔ R₂ ⊔ R₃) ⊓ Cb x) := by
  intro x hx
  obtain ⟨hc1, hn1, he1⟩ := hR₁
  obtain ⟨hc2, hn2, he2⟩ := hR₂
  obtain ⟨hc3, hn3, he3⟩ := hR₃
  have hA : R₁ ⊔ R₂ ≤ Subgroup.centralizer ((R₃ : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_iff]; exact fun h hh => (h13 a ha h hh).symm
    · rw [Subgroup.mem_centralizer_iff]; exact fun h hh => (h23 a ha h hh).symm
  have hA' : R₁ ≤ Subgroup.centralizer ((R₂ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]; exact fun h hh => (h12 a ha h hh).symm
  obtain ⟨y, hy, x₃, hx₃, rfl⟩ := exists_mul_of_mem_sup hA hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup hA' hy
  obtain ⟨E₁, hE1, hel1, hcd1, hz1, hC1⟩ := rk5_local hc1 hn1 he1 hx₁
  obtain ⟨E₂, hE2, hel2, hcd2, hz2, hC2⟩ := rk5_local hc2 hn2 he2 hx₂
  obtain ⟨E₃, hE3, hel3, hcd3, hz3, hC3⟩ := rk5_local hc3 hn3 he3 hx₃
  have hcmb : ∀ {e : G} {x₁ x₂ x₃ : G}, Commute e x₁ → Commute e x₂ → Commute e x₃ →
      e ∈ Cb (x₁ * x₂ * x₃) := fun c1 c2 c3 =>
    Subgroup.mem_centralizer_singleton_iff.2 (((c1.mul_right c2).mul_right c3).eq)
  have hle : ∀ {E : Subgroup G}, E ≤ R₁ ⊔ R₂ ⊔ R₃ → (∀ e ∈ E, e ∈ Cb (x₁ * x₂ * x₃)) →
      E ≤ (R₁ ⊔ R₂ ⊔ R₃) ⊓ Cb (x₁ * x₂ * x₃) := fun h1 h2 e he => ⟨h1 he, h2 e he⟩
  have hH1 : E₁ ≤ (R₁ ⊔ R₂ ⊔ R₃) ⊓ Cb (x₁ * x₂ * x₃) := by
    refine hle ((hE1.trans le_sup_left).trans le_sup_left) fun e he => hcmb ?_ ?_ ?_
    · exact Subgroup.mem_centralizer_singleton_iff.1 (hC1 he)
    · exact h12 e (hE1 he) x₂ hx₂
    · exact h13 e (hE1 he) x₃ hx₃
  have hH2 : E₂ ≤ (R₁ ⊔ R₂ ⊔ R₃) ⊓ Cb (x₁ * x₂ * x₃) := by
    refine hle ((hE2.trans le_sup_right).trans le_sup_left) fun e he => hcmb ?_ ?_ ?_
    · exact (h12 x₁ hx₁ e (hE2 he)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.1 (hC2 he)
    · exact h23 e (hE2 he) x₃ hx₃
  have hH3 : E₃ ≤ (R₁ ⊔ R₂ ⊔ R₃) ⊓ Cb (x₁ * x₂ * x₃) := by
    refine hle ((hE3.trans le_sup_right)) fun e he => hcmb ?_ ?_ ?_
    · exact (h13 x₁ hx₁ e (hE3 he)).symm
    · exact (h23 x₂ hx₂ e (hE3 he)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.1 (hC3 he)
  obtain ⟨E, hEle, hEel, hEcard⟩ := rk5_core h12 h23 h13 (rk5_card_ZR hc1 hn1) (rk5_card_ZR hc2 hn2)
    (rk5_card_ZR hc3 hn3) hZ h12' hE1 hE2 hE3 hel1 hel2 hel3 hcd1 hcd2 hcd3 hz1 hz2 hz3
  exact rk5_le_pRank (sup_le (sup_le hH1 hH2) hH3 |> hEle.trans) hEel hEcard

end Rk5Sec

section B2Sec

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


theorem b2_core_cop (H : Type*) [Group H] [Finite H] :
    Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.pPrimeCore_coprime_card

theorem b2_mem_P3_iff {X : Subgroup G} {g : G} :
    g ∈ P3 X ↔ ∃ hg : g ∈ X, (QuotientGroup.mk (⟨g, hg⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore 3 ↥X) = 1 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, (QuotientGroup.eq_one_iff c).2 hc⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩

theorem b2_P3_le (X : Subgroup G) : P3 X ≤ X := by
  rintro _ ⟨c, _, rfl⟩
  exact c.2

theorem b2_three_core {X : Subgroup G} {g : G} (hg : g ∈ P3 X) {k : ℕ} (hk : g ^ (3 ^ k) = 1) :
    g = 1 := by
  obtain ⟨c, hc, rfl⟩ := hg
  let c' : ↥(GLAPPrimeCore 3 ↥X) := ⟨c, hc⟩
  have h1 : orderOf c' ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Subtype.ext
    simpa using hk
  have h2 : orderOf c' ∣ Nat.card (GLAPPrimeCore 3 ↥X) := orderOf_dvd_natCard c'
  have h3 : Nat.Coprime (orderOf c') (Nat.card (GLAPPrimeCore 3 ↥X)) :=
    Nat.Coprime.coprime_dvd_left h1 ((b2_core_cop ↥X).pow_left k)
  have h4 : orderOf c' = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
  have h5 : c' = 1 := orderOf_eq_one_iff.1 h4
  have : c = 1 := congrArg (fun t : ↥(GLAPPrimeCore 3 ↥X) => (t : ↥X)) h5
  simp [this]

theorem b2_mkX_eq_iff (X : Subgroup G) {g h : G} (hg : g ∈ X) (hh : h ∈ X) :
    mkX X g hg = mkX X h hh ↔ g⁻¹ * h ∈ P3 X := by
  unfold mkX
  rw [QuotientGroup.eq]
  constructor
  · intro h'
    exact ⟨_, h', rfl⟩
  · rintro ⟨c, hc, hcz⟩
    have : c = (⟨g, hg⟩ : ↥X)⁻¹ * ⟨h, hh⟩ := Subtype.ext hcz
    rwa [← this]

theorem b2_mkX_eq_one_iff (X : Subgroup G) {g : G} (hg : g ∈ X) :
    mkX X g hg = 1 ↔ g ∈ P3 X := by
  constructor
  · intro h
    exact b2_mem_P3_iff.2 ⟨hg, h⟩
  · intro h
    obtain ⟨hg', h'⟩ := b2_mem_P3_iff.1 h
    exact h'

theorem b2_mkX_mul (X : Subgroup G) {g h : G} (hg : g ∈ X) (hh : h ∈ X) :
    mkX X g hg * mkX X h hh = mkX X (g * h) (mul_mem hg hh) := rfl

theorem b2_mkX_inv (X : Subgroup G) {g : G} (hg : g ∈ X) :
    (mkX X g hg)⁻¹ = mkX X g⁻¹ (inv_mem hg) := rfl

theorem b2_mem_barX_iff {X Y : Subgroup G} {w : ↥X ⧸ GLAPPrimeCore 3 ↥X} :
    w ∈ barX 3 X Y ↔ ∃ (y : G) (hy : y ∈ X), y ∈ Y ∧ mkX X y hy = w := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, c.2, (Subgroup.mem_subgroupOf).1 hc, rfl⟩
  · rintro ⟨y, hy, hyY, rfl⟩
    exact ⟨⟨y, hy⟩, (Subgroup.mem_subgroupOf).2 hyY, rfl⟩

theorem b2_mkX_surj (X : Subgroup G) (w : ↥X ⧸ GLAPPrimeCore 3 ↥X) :
    ∃ (y : G) (hy : y ∈ X), mkX X y hy = w := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective w
  exact ⟨c, c.2, rfl⟩

theorem b2_comm_iff (X : Subgroup G) {g k : G} (hg : g ∈ X) (hk : k ∈ X) :
    mkX X g hg * mkX X k hk = mkX X k hk * mkX X g hg ↔ g * k * g⁻¹ * k⁻¹ ∈ P3 X := by
  have hmem : g * k * g⁻¹ * k⁻¹ ∈ X :=
    mul_mem (mul_mem (mul_mem hg hk) (inv_mem hg)) (inv_mem hk)
  rw [← b2_mkX_eq_one_iff X hmem]
  have e : mkX X (g * k * g⁻¹ * k⁻¹) hmem = mkX X g hg * mkX X k hk * (mkX X g hg)⁻¹ *
      (mkX X k hk)⁻¹ := rfl
  rw [e, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem b2_card_barX {X Y : Subgroup G} (hYX : Y ≤ X) (hinj : ∀ y ∈ Y, y ∈ P3 X → y = 1) :
    Nat.card ↥(barX 3 X Y) = Nat.card ↥Y := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun y : ↥Y => (⟨mkX X y (hYX y.2), b2_mem_barX_iff.2 ⟨y, hYX y.2, y.2, rfl⟩⟩ : ↥(barX 3 X Y)))
    ⟨fun y y' h => ?_, fun w => ?_⟩)
  · have h1 : mkX X y (hYX y.2) = mkX X y' (hYX y'.2) := congrArg Subtype.val h
    rw [b2_mkX_eq_iff] at h1
    have := hinj _ (Y.mul_mem (Y.inv_mem y.2) y'.2) h1
    apply Subtype.ext
    have h2 : (y : G)⁻¹ * y' = 1 := this
    exact (inv_mul_eq_one.1 h2)
  · obtain ⟨w, hw⟩ := w
    obtain ⟨y, hy, hyY, rfl⟩ := b2_mem_barX_iff.1 hw
    exact ⟨⟨y, hyY⟩, rfl⟩

theorem b2_sup3 {H : Type*} [Group H] (A₁ A₂ A₃ : Subgroup H)
    (h12 : ∀ a ∈ A₁, ∀ c ∈ A₂, a * c = c * a) (h23 : ∀ a ∈ A₂, ∀ c ∈ A₃, a * c = c * a)
    (h13 : ∀ a ∈ A₁, ∀ c ∈ A₃, a * c = c * a) {z : H} (hz : z ∈ A₁ ⊔ A₂ ⊔ A₃) :
    ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, ∃ a₃ ∈ A₃, z = a₁ * a₂ * a₃ := by
  let S : Subgroup H :=
    { carrier := {z | ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, ∃ a₃ ∈ A₃, z = a₁ * a₂ * a₃}
      one_mem' := ⟨1, A₁.one_mem, 1, A₂.one_mem, 1, A₃.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, rfl⟩
        refine ⟨a₁ * b₁, A₁.mul_mem ha₁ hb₁, a₂ * b₂, A₂.mul_mem ha₂ hb₂, a₃ * b₃,
          A₃.mul_mem ha₃ hb₃, ?_⟩
        have e1 : a₂ * b₁ = b₁ * a₂ := (h12 b₁ hb₁ a₂ ha₂).symm
        have e2 : a₃ * b₁ = b₁ * a₃ := (h13 b₁ hb₁ a₃ ha₃).symm
        have e3 : a₃ * b₂ = b₂ * a₃ := (h23 b₂ hb₂ a₃ ha₃).symm
        calc a₁ * a₂ * a₃ * (b₁ * b₂ * b₃)
            = a₁ * a₂ * (a₃ * b₁) * b₂ * b₃ := by simp only [mul_assoc]
          _ = a₁ * a₂ * (b₁ * a₃) * b₂ * b₃ := by rw [e2]
          _ = a₁ * (a₂ * b₁) * a₃ * b₂ * b₃ := by simp only [mul_assoc]
          _ = a₁ * (b₁ * a₂) * a₃ * b₂ * b₃ := by rw [e1]
          _ = a₁ * b₁ * a₂ * (a₃ * b₂) * b₃ := by simp only [mul_assoc]
          _ = a₁ * b₁ * a₂ * (b₂ * a₃) * b₃ := by rw [e3]
          _ = a₁ * b₁ * (a₂ * b₂) * (a₃ * b₃) := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, rfl⟩
        refine ⟨a₁⁻¹, A₁.inv_mem ha₁, a₂⁻¹, A₂.inv_mem ha₂, a₃⁻¹, A₃.inv_mem ha₃, ?_⟩
        have e1 : a₂⁻¹ * a₁⁻¹ = a₁⁻¹ * a₂⁻¹ :=
          ((Commute.inv_inv (h12 a₁ ha₁ a₂ ha₂))).symm.eq
        have e2 : a₃⁻¹ * a₁⁻¹ = a₁⁻¹ * a₃⁻¹ :=
          ((Commute.inv_inv (h13 a₁ ha₁ a₃ ha₃))).symm.eq
        have e3 : a₃⁻¹ * a₂⁻¹ = a₂⁻¹ * a₃⁻¹ :=
          ((Commute.inv_inv (h23 a₂ ha₂ a₃ ha₃))).symm.eq
        calc (a₁ * a₂ * a₃)⁻¹ = a₃⁻¹ * a₂⁻¹ * a₁⁻¹ := by simp [mul_assoc]
          _ = a₂⁻¹ * a₃⁻¹ * a₁⁻¹ := by rw [e3]
          _ = a₂⁻¹ * (a₃⁻¹ * a₁⁻¹) := by rw [mul_assoc]
          _ = a₂⁻¹ * (a₁⁻¹ * a₃⁻¹) := by rw [e2]
          _ = a₂⁻¹ * a₁⁻¹ * a₃⁻¹ := by rw [mul_assoc]
          _ = a₁⁻¹ * a₂⁻¹ * a₃⁻¹ := by rw [e1] }
  have : A₁ ⊔ A₂ ⊔ A₃ ≤ S := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact ⟨a, ha, 1, A₂.one_mem, 1, A₃.one_mem, by simp⟩
    · intro a ha
      exact ⟨1, A₁.one_mem, a, ha, 1, A₃.one_mem, by simp⟩
    · intro a ha
      exact ⟨1, A₁.one_mem, 1, A₂.one_mem, a, ha, by simp⟩
  exact this hz

theorem b2_conj_of_mem_normalizer {g : G} {L : Subgroup G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    GLBConj g L = L := by
  ext y
  rw [mem_gLBConj]
  exact (Subgroup.mem_normalizer_iff.1 hg y).symm

theorem b2_conj_conj (g b' : G) (L : Subgroup G) :
    GLBConj b' (GLBConj g L) = GLBConj (g * b') L := by
  ext y
  rw [mem_gLBConj, mem_gLBConj, mem_gLBConj]
  simp only [mul_inv_rev, mul_assoc]

theorem b2_bClosure_conj {B : Subgroup G} {g : G} (hg : g ∈ B) (L : Subgroup G) :
    bClosure B (GLBConj g L) = bClosure B L := by
  apply le_antisymm
  · refine iSup₂_le fun b' hb' => ?_
    rw [b2_conj_conj]
    exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b L) (g * b') (B.mul_mem hg hb')
  · refine iSup₂_le fun b' hb' => ?_
    have : GLBConj b' L = GLBConj (g⁻¹ * b') (GLBConj g L) := by
      rw [b2_conj_conj]; simp
    rw [this]
    exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b (GLBConj g L)) (g⁻¹ * b')
      (B.mul_mem (B.inv_mem hg) hb')

theorem b2_mkX_congr (X : Subgroup G) {g h : G} (hg : g ∈ X) (hh : h ∈ X) (e : g = h) :
    mkX X g hg = mkX X h hh := by
  subst e; rfl

theorem b2_mem_ZR {R : Subgroup G} {z : G} : z ∈ ZR R ↔ z ∈ R ∧ ∀ r ∈ R, r * z = z * r := by
  constructor
  · rintro ⟨z', hz', rfl⟩
    refine ⟨z'.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hz' ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (h y y.2), rfl⟩

theorem b2_ZR_le (R : Subgroup G) : ZR R ≤ R := fun _ hz => (b2_mem_ZR.1 hz).1

theorem b2_P3L_iff {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L) {l : G} (hl : l ∈ L) :
    l ∈ P3 L ↔ l ∈ P3 (Cb b) := by
  have h : L ⊓ P3 (Cb b) = P3 L :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hL.2.1
  have h2 := SetLike.ext_iff.1 h l
  constructor
  · intro h'
    exact (Subgroup.mem_inf.1 (h2.2 h')).2
  · intro h'
    exact h2.1 (Subgroup.mem_inf.2 ⟨hl, h'⟩)

structure b2_Good (b : G) (L Rl : Subgroup G) : Prop where
  comp : GLAPComponent 3 (Cb b) L
  le : Rl ≤ L
  exp : ∀ r ∈ Rl, r ^ 3 = 1
  c4 : Subgroup.center (barOf 3 L) ≤
    (Rl.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))
  c5 : ∀ w ∈ (Rl.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)),
    (∀ r ∈ (Rl.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)), w * r = r * w) →
      w ∈ Subgroup.center (barOf 3 L)

theorem b2_T1 {b : G} {L Rl : Subgroup G} (h : b2_Good b L Rl) {z : G} (hz : z ∈ Rl)
    (hzc : ∀ r ∈ Rl, z * r = r * z) {l : G} (hl : l ∈ L) :
    z * l * z⁻¹ * l⁻¹ ∈ P3 (Cb b) := by
  have hzL : z ∈ L := h.le hz
  have hw : mkX L z hzL ∈ (Rl.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) :=
    ⟨⟨z, hzL⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
  have hcen := h.c5 _ hw (by
    rintro _ ⟨⟨r, hrL⟩, hr, rfl⟩
    have hr' : r ∈ Rl := Subgroup.mem_subgroupOf.1 hr
    have := (b2_comm_iff L hzL hrL).2 (by rw [hzc r hr']; simp [one_mem])
    exact this)
  have h1 := Subgroup.mem_center_iff.1 hcen (mkX L l hl)
  have h2 := (b2_comm_iff L hzL hl).1 h1.symm
  exact (b2_P3L_iff h.comp (by
    exact mul_mem (mul_mem (mul_mem hzL hl) (inv_mem hzL)) (inv_mem hl))).1 h2

theorem b2_T2 {b : G} {L Rl : Subgroup G} (h : b2_Good b L Rl) {l : G} (hl : l ∈ L)
    (hlc : ∀ l' ∈ L, l * l' * l⁻¹ * l'⁻¹ ∈ P3 (Cb b)) :
    ∃ r ∈ Rl, (∀ r' ∈ Rl, r * r' = r' * r) ∧ l⁻¹ * r ∈ P3 (Cb b) := by
  have hcen : mkX L l hl ∈ Subgroup.center (barOf 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l', hl', rfl⟩ := b2_mkX_surj L g
    refine (b2_comm_iff L hl' hl).2 ?_
    refine (b2_P3L_iff h.comp (mul_mem (mul_mem (mul_mem hl' hl) (inv_mem hl')) (inv_mem hl))).2 ?_
    simpa [mul_assoc] using inv_mem (hlc l' hl')
  obtain ⟨⟨r, hrL⟩, hr, hreq⟩ := h.c4 hcen
  have hrR : r ∈ Rl := Subgroup.mem_subgroupOf.1 hr
  have hreq' : mkX L r hrL = mkX L l hl := hreq
  refine ⟨r, hrR, fun r' hr' => ?_, ?_⟩
  · have hr'L : r' ∈ L := h.le hr'
    have h1 := Subgroup.mem_center_iff.1 hcen (mkX L r' hr'L)
    rw [← hreq'] at h1
    have h2 := (b2_comm_iff L hr'L hrL).1 h1
    have h3 : r' * r * r'⁻¹ * r⁻¹ ∈ P3 (Cb b) :=
      (b2_P3L_iff h.comp (mul_mem (mul_mem (mul_mem hr'L hrL) (inv_mem hr'L)) (inv_mem hrL))).1 h2
    have h4 : (r' * r * r'⁻¹ * r⁻¹) ^ (3 ^ 1) = 1 := by
      simpa using h.exp _ (mul_mem (mul_mem (mul_mem hr' hrR) (inv_mem hr')) (inv_mem hrR))
    have h5 := b2_three_core h3 h4
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h5
    exact h5.symm
  · exact (b2_P3L_iff h.comp (mul_mem (inv_mem hl) hrL)).1 ((b2_mkX_eq_iff L hl hrL).1 hreq'.symm)

theorem b2_barX_sup {X Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X) :
    barX 3 X (Y ⊔ Y') = barX 3 X Y ⊔ barX 3 X Y' := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hY hY', Subgroup.map_sup]

theorem b2_barX_comm {b : G} {Li Lj : Subgroup G} (hi : GLAPComponent 3 (Cb b) Li)
    (hj : GLAPComponent 3 (Cb b) Lj) (hne : Li ≠ Lj) :
    ∀ a ∈ barX 3 (Cb b) Li, ∀ c ∈ barX 3 (Cb b) Lj, a * c = c * a := by
  intro a ha c hc
  obtain ⟨u, hu, huL, rfl⟩ := b2_mem_barX_iff.1 ha
  obtain ⟨v, hv, hvL, rfl⟩ := b2_mem_barX_iff.1 hc
  refine (b2_comm_iff _ hu hv).2 ?_
  have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hi hj hne
    (Subgroup.commutator_mem_commutator huL hvL)
  rwa [commutatorElement_def] at this

theorem b2_comm_other {b : G} {Li Lj : Subgroup G} (hi : GLAPComponent 3 (Cb b) Li)
    (hj : GLAPComponent 3 (Cb b) Lj) (hne : Li ≠ Lj) {u v : G} (hu : u ∈ Li) (hv : v ∈ Lj) :
    u * v * u⁻¹ * v⁻¹ ∈ P3 (Cb b) := by
  have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hi hj hne
    (Subgroup.commutator_mem_commutator hu hv)
  rwa [commutatorElement_def] at this

theorem b2_mem_barCenterAt {b : G} {K : Subgroup G} {w : CBar 3 b} :
    w ∈ barCenterAt 3 b K ↔ w ∈ barX 3 (Cb b) K ∧ ∀ v ∈ barX 3 (Cb b) K, v * w = w * v := by
  unfold barCenterAt
  constructor
  · rintro ⟨⟨c, hc⟩, hcz, rfl⟩
    refine ⟨hc, fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.1 hcz ⟨w, hw⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, h⟩
    exact ⟨⟨w, hz⟩, Subgroup.mem_center_iff.2 fun v => Subtype.ext (h v v.2), rfl⟩

theorem b2_cancel {H : Type*} [Group H] (A : Subgroup H) {x y w : H}
    (hy : ∀ a ∈ A, a * y = y * a) (hw : w = x * y) (hwc : ∀ a ∈ A, a * w = w * a) :
    ∀ a ∈ A, a * x = x * a := by
  intro a ha
  have h1 := hwc a ha
  rw [hw] at h1
  have h2 := hy a ha
  have h3 : a * x * y = x * a * y := by
    calc a * x * y = a * (x * y) := mul_assoc _ _ _
      _ = x * y * a := h1
      _ = x * (y * a) := mul_assoc _ _ _
      _ = x * (a * y) := by rw [h2]
      _ = x * a * y := (mul_assoc _ _ _).symm
  exact mul_right_cancel h3

theorem b2_comm_prod {H : Type*} [Group H] (A : Subgroup H) {a₂ a₃ : H}
    (h2 : ∀ a ∈ A, a * a₂ = a₂ * a) (h3 : ∀ a ∈ A, a * a₃ = a₃ * a) :
    ∀ a ∈ A, a * (a₂ * a₃) = (a₂ * a₃) * a := by
  intro a ha
  calc a * (a₂ * a₃) = a * a₂ * a₃ := (mul_assoc _ _ _).symm
    _ = a₂ * a * a₃ := by rw [h2 a ha]
    _ = a₂ * (a * a₃) := mul_assoc _ _ _
    _ = a₂ * (a₃ * a) := by rw [h3 a ha]
    _ = (a₂ * a₃) * a := (mul_assoc _ _ _).symm

structure b2_Setup (b : G) (L₁ L₂ L₃ R₁ R₂ R₃ : Subgroup G) : Prop where
  g₁ : b2_Good b L₁ R₁
  g₂ : b2_Good b L₂ R₂
  g₃ : b2_Good b L₃ R₃
  ne₁₂ : L₁ ≠ L₂
  ne₂₃ : L₂ ≠ L₃
  ne₁₃ : L₁ ≠ L₃
  c12 : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a
  c23 : ∀ a ∈ R₂, ∀ c ∈ R₃, a * c = c * a
  c13 : ∀ a ∈ R₁, ∀ c ∈ R₃, a * c = c * a
  p3 : ∀ y ∈ R₁ ⊔ R₂ ⊔ R₃, ∃ k : ℕ, y ^ (3 ^ k) = 1

theorem b2_cen_eq {b : G} {L₁ L₂ L₃ R₁ R₂ R₃ : Subgroup G}
    (hS : b2_Setup b L₁ L₂ L₃ R₁ R₂ R₃) :
    barX 3 (Cb b) (ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃) = barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃) := by
  have hC₁ : L₁ ≤ Cb b := hS.g₁.comp.1
  have hC₂ : L₂ ≤ Cb b := hS.g₂.comp.1
  have hC₃ : L₃ ≤ Cb b := hS.g₃.comp.1
  have hZ₁ : ZR R₁ ≤ L₁ := (b2_ZR_le R₁).trans hS.g₁.le
  have hZ₂ : ZR R₂ ≤ L₂ := (b2_ZR_le R₂).trans hS.g₂.le
  have hZ₃ : ZR R₃ ≤ L₃ := (b2_ZR_le R₃).trans hS.g₃.le
  have hK : barX 3 (Cb b) (L₁ ⊔ L₂ ⊔ L₃) =
      barX 3 (Cb b) L₁ ⊔ barX 3 (Cb b) L₂ ⊔ barX 3 (Cb b) L₃ := by
    rw [b2_barX_sup (sup_le hC₁ hC₂) hC₃, b2_barX_sup hC₁ hC₂]
  have hJ : barX 3 (Cb b) (ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃) =
      barX 3 (Cb b) (ZR R₁) ⊔ barX 3 (Cb b) (ZR R₂) ⊔ barX 3 (Cb b) (ZR R₃) := by
    rw [b2_barX_sup (sup_le (hZ₁.trans hC₁) (hZ₂.trans hC₂)) (hZ₃.trans hC₃),
      b2_barX_sup (hZ₁.trans hC₁) (hZ₂.trans hC₂)]
  have hKle : L₁ ⊔ L₂ ⊔ L₃ ≤ Cb b := sup_le (sup_le hC₁ hC₂) hC₃
  have key : ∀ z : G, ∀ hzC : z ∈ Cb b, z ∈ L₁ ⊔ L₂ ⊔ L₃ →
      (∀ l ∈ L₁, z * l * z⁻¹ * l⁻¹ ∈ P3 (Cb b)) → (∀ l ∈ L₂, z * l * z⁻¹ * l⁻¹ ∈ P3 (Cb b)) →
      (∀ l ∈ L₃, z * l * z⁻¹ * l⁻¹ ∈ P3 (Cb b)) →
      mkX (Cb b) z hzC ∈ barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃) := by
    intro z hzC hzK h1 h2 h3
    rw [b2_mem_barCenterAt]
    refine ⟨b2_mem_barX_iff.2 ⟨z, hzC, hzK, rfl⟩, ?_⟩
    rw [hK]
    have hle : barX 3 (Cb b) L₁ ⊔ barX 3 (Cb b) L₂ ⊔ barX 3 (Cb b) L₃ ≤
        Subgroup.centralizer ({mkX (Cb b) z hzC} : Set (CBar 3 b)) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        obtain ⟨l, hl, hlL, rfl⟩ := b2_mem_barX_iff.1 ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((b2_comm_iff _ hzC hl).2 (h1 l hlL)).symm
      · intro a ha
        obtain ⟨l, hl, hlL, rfl⟩ := b2_mem_barX_iff.1 ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((b2_comm_iff _ hzC hl).2 (h2 l hlL)).symm
      · intro a ha
        obtain ⟨l, hl, hlL, rfl⟩ := b2_mem_barX_iff.1 ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((b2_comm_iff _ hzC hl).2 (h3 l hlL)).symm
    intro v hv
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hv)
    exact this
  have hle1 : ∀ z ∈ ZR R₁, ∃ hzC : z ∈ Cb b,
      mkX (Cb b) z hzC ∈ barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃) := by
    intro z hz
    have hz' := b2_mem_ZR.1 hz
    have hzL : z ∈ L₁ := hS.g₁.le hz'.1
    exact ⟨hC₁ hzL, key z (hC₁ hzL) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hzL))
      (fun l hl => b2_T1 hS.g₁ hz'.1 (fun r hr => (hz'.2 r hr).symm) hl)
      (fun l hl => b2_comm_other hS.g₁.comp hS.g₂.comp hS.ne₁₂ hzL hl)
      (fun l hl => b2_comm_other hS.g₁.comp hS.g₃.comp hS.ne₁₃ hzL hl)⟩
  have hle2 : ∀ z ∈ ZR R₂, ∃ hzC : z ∈ Cb b,
      mkX (Cb b) z hzC ∈ barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃) := by
    intro z hz
    have hz' := b2_mem_ZR.1 hz
    have hzL : z ∈ L₂ := hS.g₂.le hz'.1
    exact ⟨hC₂ hzL, key z (hC₂ hzL) (Subgroup.mem_sup_left (Subgroup.mem_sup_right hzL))
      (fun l hl => b2_comm_other hS.g₂.comp hS.g₁.comp hS.ne₁₂.symm hzL hl)
      (fun l hl => b2_T1 hS.g₂ hz'.1 (fun r hr => (hz'.2 r hr).symm) hl)
      (fun l hl => b2_comm_other hS.g₂.comp hS.g₃.comp hS.ne₂₃ hzL hl)⟩
  have hle3 : ∀ z ∈ ZR R₃, ∃ hzC : z ∈ Cb b,
      mkX (Cb b) z hzC ∈ barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃) := by
    intro z hz
    have hz' := b2_mem_ZR.1 hz
    have hzL : z ∈ L₃ := hS.g₃.le hz'.1
    exact ⟨hC₃ hzL, key z (hC₃ hzL) (Subgroup.mem_sup_right hzL)
      (fun l hl => b2_comm_other hS.g₃.comp hS.g₁.comp hS.ne₁₃.symm hzL hl)
      (fun l hl => b2_comm_other hS.g₃.comp hS.g₂.comp hS.ne₂₃.symm hzL hl)
      (fun l hl => b2_T1 hS.g₃ hz'.1 (fun r hr => (hz'.2 r hr).symm) hl)⟩
  apply le_antisymm
  · rw [hJ]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro w hw
      obtain ⟨z, hzC, hzJ, rfl⟩ := b2_mem_barX_iff.1 hw
      obtain ⟨_, h⟩ := hle1 z hzJ
      exact h
    · intro w hw
      obtain ⟨z, hzC, hzJ, rfl⟩ := b2_mem_barX_iff.1 hw
      obtain ⟨_, h⟩ := hle2 z hzJ
      exact h
    · intro w hw
      obtain ⟨z, hzC, hzJ, rfl⟩ := b2_mem_barX_iff.1 hw
      obtain ⟨_, h⟩ := hle3 z hzJ
      exact h
  · intro w hw
    obtain ⟨hwK, hwc⟩ := b2_mem_barCenterAt.1 hw
    have hwK' : w ∈ barX 3 (Cb b) L₁ ⊔ barX 3 (Cb b) L₂ ⊔ barX 3 (Cb b) L₃ := hK ▸ hwK
    have e12 := b2_barX_comm hS.g₁.comp hS.g₂.comp hS.ne₁₂
    have e23 := b2_barX_comm hS.g₂.comp hS.g₃.comp hS.ne₂₃
    have e13 := b2_barX_comm hS.g₁.comp hS.g₃.comp hS.ne₁₃
    obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, rfl⟩ := b2_sup3 _ _ _ e12 e23 e13 hwK'
    have hwcA : ∀ i : Fin 3, ∀ a ∈ (![barX 3 (Cb b) L₁, barX 3 (Cb b) L₂, barX 3 (Cb b) L₃] i),
        a * (a₁ * a₂ * a₃) = (a₁ * a₂ * a₃) * a := by
      intro i a ha
      apply hwc
      rw [hK]
      fin_cases i
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ha)
      · exact Subgroup.mem_sup_right ha
    have cen₁ : ∀ a ∈ barX 3 (Cb b) L₁, a * a₁ = a₁ * a :=
      b2_cancel _ (y := a₂ * a₃)
        (b2_comm_prod _ (fun a ha => (e12 a ha a₂ ha₂)) (fun a ha => (e13 a ha a₃ ha₃)))
        (mul_assoc _ _ _) (hwcA 0)
    have cen₂ : ∀ a ∈ barX 3 (Cb b) L₂, a * a₂ = a₂ * a :=
      b2_cancel _ (y := a₁ * a₃)
        (b2_comm_prod _ (fun a ha => (e12 a₁ ha₁ a ha).symm) (fun a ha => (e23 a ha a₃ ha₃)))
        (by rw [e12 a₁ ha₁ a₂ ha₂, mul_assoc]) (hwcA 1)
    have cen₃ : ∀ a ∈ barX 3 (Cb b) L₃, a * a₃ = a₃ * a :=
      b2_cancel _ (y := a₁ * a₂)
        (b2_comm_prod _ (fun a ha => (e13 a₁ ha₁ a ha).symm) (fun a ha => (e23 a₂ ha₂ a ha).symm))
        (by rw [mul_assoc, e23 a₂ ha₂ a₃ ha₃, ← mul_assoc, e13 a₁ ha₁ a₃ ha₃, mul_assoc])
        (hwcA 2)
    obtain ⟨l₁, hl₁C, hl₁L, rfl⟩ := b2_mem_barX_iff.1 ha₁
    obtain ⟨l₂, hl₂C, hl₂L, rfl⟩ := b2_mem_barX_iff.1 ha₂
    obtain ⟨l₃, hl₃C, hl₃L, rfl⟩ := b2_mem_barX_iff.1 ha₃
    have hc₁ : ∀ l' ∈ L₁, l₁ * l' * l₁⁻¹ * l'⁻¹ ∈ P3 (Cb b) := fun l' hl' =>
      (b2_comm_iff _ hl₁C (hC₁ hl')).1
        ((cen₁ _ (b2_mem_barX_iff.2 ⟨l', hC₁ hl', hl', rfl⟩)).symm)
    have hc₂ : ∀ l' ∈ L₂, l₂ * l' * l₂⁻¹ * l'⁻¹ ∈ P3 (Cb b) := fun l' hl' =>
      (b2_comm_iff _ hl₂C (hC₂ hl')).1
        ((cen₂ _ (b2_mem_barX_iff.2 ⟨l', hC₂ hl', hl', rfl⟩)).symm)
    have hc₃ : ∀ l' ∈ L₃, l₃ * l' * l₃⁻¹ * l'⁻¹ ∈ P3 (Cb b) := fun l' hl' =>
      (b2_comm_iff _ hl₃C (hC₃ hl')).1
        ((cen₃ _ (b2_mem_barX_iff.2 ⟨l', hC₃ hl', hl', rfl⟩)).symm)
    obtain ⟨r₁, hr₁R, hr₁c, hr₁P⟩ := b2_T2 hS.g₁ hl₁L hc₁
    obtain ⟨r₂, hr₂R, hr₂c, hr₂P⟩ := b2_T2 hS.g₂ hl₂L hc₂
    obtain ⟨r₃, hr₃R, hr₃c, hr₃P⟩ := b2_T2 hS.g₃ hl₃L hc₃
    have hr₁C : r₁ ∈ Cb b := hC₁ (hS.g₁.le hr₁R)
    have hr₂C : r₂ ∈ Cb b := hC₂ (hS.g₂.le hr₂R)
    have hr₃C : r₃ ∈ Cb b := hC₃ (hS.g₃.le hr₃R)
    have e₁ : mkX (Cb b) l₁ hl₁C = mkX (Cb b) r₁ hr₁C := (b2_mkX_eq_iff _ _ _).2 hr₁P
    have e₂ : mkX (Cb b) l₂ hl₂C = mkX (Cb b) r₂ hr₂C := (b2_mkX_eq_iff _ _ _).2 hr₂P
    have e₃ : mkX (Cb b) l₃ hl₃C = mkX (Cb b) r₃ hr₃C := (b2_mkX_eq_iff _ _ _).2 hr₃P
    rw [e₁, e₂, e₃]
    have z₁ : r₁ ∈ ZR R₁ := b2_mem_ZR.2 ⟨hr₁R, fun r hr => (hr₁c r hr).symm⟩
    have z₂ : r₂ ∈ ZR R₂ := b2_mem_ZR.2 ⟨hr₂R, fun r hr => (hr₂c r hr).symm⟩
    have z₃ : r₃ ∈ ZR R₃ := b2_mem_ZR.2 ⟨hr₃R, fun r hr => (hr₃c r hr).symm⟩
    exact b2_mem_barX_iff.2 ⟨r₁ * r₂ * r₃, mul_mem (mul_mem hr₁C hr₂C) hr₃C,
      mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left z₁))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right z₂))) (Subgroup.mem_sup_right z₃), rfl⟩

theorem b2_card_J {b : G} {L₁ L₂ L₃ R₁ R₂ R₃ : Subgroup G}
    (hS : b2_Setup b L₁ L₂ L₃ R₁ R₂ R₃)
    (h9 : Nat.card ↥(barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃)) = 9) :
    Nat.card ↥(ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃) = 9 := by
  have hC₁ : L₁ ≤ Cb b := hS.g₁.comp.1
  have hC₂ : L₂ ≤ Cb b := hS.g₂.comp.1
  have hC₃ : L₃ ≤ Cb b := hS.g₃.comp.1
  have hZ₁ : ZR R₁ ≤ L₁ := (b2_ZR_le R₁).trans hS.g₁.le
  have hZ₂ : ZR R₂ ≤ L₂ := (b2_ZR_le R₂).trans hS.g₂.le
  have hZ₃ : ZR R₃ ≤ L₃ := (b2_ZR_le R₃).trans hS.g₃.le
  have hJC : ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃ ≤ Cb b :=
    sup_le (sup_le (hZ₁.trans hC₁) (hZ₂.trans hC₂)) (hZ₃.trans hC₃)
  have hJR : ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃ ≤ R₁ ⊔ R₂ ⊔ R₃ :=
    sup_le_sup (sup_le_sup (b2_ZR_le R₁) (b2_ZR_le R₂)) (b2_ZR_le R₃)
  have hc := b2_card_barX (X := Cb b) hJC (fun y hy hyP => by
    obtain ⟨k, hk⟩ := hS.p3 y (hJR hy)
    exact b2_three_core hyP hk)
  rw [b2_cen_eq hS, h9] at hc
  exact hc.symm

theorem b2_ZR_card_ne {R : Subgroup G} (h27 : Nat.card R = 27)
    (hna : ¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) : Nat.card (ZR R) ≠ 9 := by
  intro h9
  have h1 : Nat.card (Subgroup.center ↥R) = 9 := by
    have := Subgroup.card_map_of_injective (K := Subgroup.center ↥R) (f := R.subtype)
      R.subtype_injective
    rw [← this]; exact h9
  have h2 := Subgroup.card_mul_index (Subgroup.center ↥R)
  rw [h1, h27] at h2
  have h3 : (Subgroup.center ↥R).index = 3 := by omega
  have h4 : Nat.card (↥R ⧸ Subgroup.center ↥R) = 3 := by
    rw [← Subgroup.index]; exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (↥R ⧸ Subgroup.center ↥R) := isCyclic_of_prime_card h4
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center ↥R)) (by rw [QuotientGroup.ker_mk'])
  apply hna
  intro a ha c hc
  have := hcomm.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩
  exact congrArg Subtype.val this

theorem b2_all_eq {P₁ P₂ P₃ : Subgroup G} {β : G}
    (r1 : ∀ z, z ∈ P₂ ↔ β * z * β⁻¹ ∈ P₁) (r2 : ∀ z, z ∈ P₃ ↔ β * z * β⁻¹ ∈ P₂)
    (r3 : ∀ z, z ∈ P₁ ↔ β * z * β⁻¹ ∈ P₃) (h : P₁ = P₂ ∨ P₂ = P₃ ∨ P₁ = P₃) :
    P₁ = P₂ ∧ P₂ = P₃ := by
  have A1 : ∀ y, y ∈ P₁ ↔ β⁻¹ * y * β ∈ P₂ := fun y => by
    rw [r1]
    have : β * (β⁻¹ * y * β) * β⁻¹ = y := by group
    rw [this]
  have A2 : ∀ y, y ∈ P₂ ↔ β⁻¹ * y * β ∈ P₃ := fun y => by
    rw [r2]
    have : β * (β⁻¹ * y * β) * β⁻¹ = y := by group
    rw [this]
  have A3 : ∀ y, y ∈ P₃ ↔ β⁻¹ * y * β ∈ P₁ := fun y => by
    rw [r3]
    have : β * (β⁻¹ * y * β) * β⁻¹ = y := by group
    rw [this]
  rcases h with h12 | h23 | h13
  · have e : P₃ = P₁ := by
      refine Subgroup.ext fun y => ?_
      refine (A3 y).trans (Iff.trans ?_ (A1 y).symm)
      rw [h12]
    exact ⟨h12, h12.symm.trans e.symm⟩
  · have e : P₁ = P₂ := by
      refine Subgroup.ext fun y => ?_
      refine (A1 y).trans (Iff.trans ?_ (A2 y).symm)
      rw [h23]
    exact ⟨e, h23⟩
  · have e : P₂ = P₃ := by
      refine Subgroup.ext fun y => ?_
      refine (A2 y).trans (Iff.trans ?_ (A3 y).symm)
      rw [h13]
    exact ⟨h13.trans e.symm, e⟩

theorem b2_ZR_conj {R Ra Rb La Lb : Subgroup G} {β : G} (hβ : ∀ r ∈ R, β * r * β⁻¹ ∈ R)
    (hβ' : ∀ r ∈ R, β⁻¹ * r * β ∈ R) (ha : Ra = R ⊓ La) (hb : Rb = R ⊓ Lb)
    (hL : ∀ y, y ∈ Lb ↔ β * y * β⁻¹ ∈ La) (z : G) :
    z ∈ ZR Rb ↔ β * z * β⁻¹ ∈ ZR Ra := by
  have hmem : ∀ y, y ∈ Rb ↔ β * y * β⁻¹ ∈ Ra := by
    intro y
    rw [ha, hb, Subgroup.mem_inf, Subgroup.mem_inf, hL y]
    constructor
    · rintro ⟨hy, hl⟩
      exact ⟨hβ y hy, hl⟩
    · rintro ⟨hy, hl⟩
      refine ⟨?_, hl⟩
      have := hβ' _ hy
      have e : β⁻¹ * (β * y * β⁻¹) * β = y := by group
      rwa [e] at this
  rw [b2_mem_ZR, b2_mem_ZR]
  constructor
  · rintro ⟨hz, hzc⟩
    refine ⟨(hmem z).1 hz, fun r hr => ?_⟩
    have hr₀ : β⁻¹ * r * β ∈ Rb := by
      rw [hmem]
      have e : β * (β⁻¹ * r * β) * β⁻¹ = r := by group
      rwa [e]
    have := hzc _ hr₀
    calc r * (β * z * β⁻¹) = β * ((β⁻¹ * r * β) * z) * β⁻¹ := by group
      _ = β * (z * (β⁻¹ * r * β)) * β⁻¹ := by rw [this]
      _ = β * z * β⁻¹ * r := by group
  · rintro ⟨hz, hzc⟩
    refine ⟨(hmem z).2 hz, fun r hr => ?_⟩
    have := hzc _ ((hmem r).1 hr)
    calc r * z = β⁻¹ * ((β * r * β⁻¹) * (β * z * β⁻¹)) * β := by group
      _ = β⁻¹ * ((β * z * β⁻¹) * (β * r * β⁻¹)) * β := by rw [this]
      _ = z * r := by group

theorem b2_distinct {B : Subgroup G} {b : G} {L₁ L₂ L₃ R R₁ R₂ R₃ : Subgroup G}
    (hSyl : SylData B b L₁ L₂ L₃ R R₁ R₂ R₃) {β : G} (hβB : β ∈ B)
    (h2 : L₂ = GLBConj β L₁) (h3 : L₃ = GLBConj β L₂) (h1 : L₁ = GLBConj β L₃)
    (hJ9 : Nat.card ↥(ZR R₁ ⊔ ZR R₂ ⊔ ZR R₃) = 9) (h27 : Nat.card R₁ = 27)
    (hna : ¬ ∀ a ∈ R₁, ∀ c ∈ R₁, a * c = c * a) :
    ZR R₁ ≠ ZR R₂ ∧ ZR R₂ ≠ ZR R₃ ∧ ZR R₁ ≠ ZR R₃ := by
  have hβ : ∀ r ∈ R, β * r * β⁻¹ ∈ R := hSyl.hRB β hβB
  have hβ' : ∀ r ∈ R, β⁻¹ * r * β ∈ R := fun r hr => by
    simpa using hSyl.hRB β⁻¹ (B.inv_mem hβB) r hr
  have r1 := b2_ZR_conj (Ra := R₁) (Rb := R₂) (La := L₁) (Lb := L₂) hβ hβ' hSyl.h1 hSyl.h2
    (fun y => by rw [h2, mem_gLBConj])
  have r2 := b2_ZR_conj (Ra := R₂) (Rb := R₃) (La := L₂) (Lb := L₃) hβ hβ' hSyl.h2 hSyl.h3
    (fun y => by rw [h3, mem_gLBConj])
  have r3 := b2_ZR_conj (Ra := R₃) (Rb := R₁) (La := L₃) (Lb := L₁) hβ hβ' hSyl.h3 hSyl.h1
    (fun y => by rw [h1, mem_gLBConj])
  have key : ¬ (ZR R₁ = ZR R₂ ∨ ZR R₂ = ZR R₃ ∨ ZR R₁ = ZR R₃) := by
    intro h
    obtain ⟨e1, e2⟩ := b2_all_eq r1 r2 r3 h
    have e3 : ZR R₃ = ZR R₁ := e2.symm.trans e1.symm
    rw [← e1, e3, sup_idem, sup_idem] at hJ9
    exact b2_ZR_card_ne h27 hna hJ9
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr (Or.inl h)),
    fun h => key (Or.inr (Or.inr h))⟩

theorem b2_sylow_conj {K R : Subgroup G} (hRK : R ≤ K) (hRs : Nat.card R =
    3 ^ (Nat.card K).factorization 3) {x : G} (hx : x ∈ K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ c ∈ K, c * x * c⁻¹ ∈ R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (R.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [← hRs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  let P : Sylow 3 ↥K := Sylow.ofCard (R.subgroupOf K) hcard
  let x' : ↥K := ⟨x, hx⟩
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hord : orderOf x' = 3 := orderOf_eq_prime hx'3 hx'1
  have hQ : IsPGroup 3 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hQ'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) Q P
  have hmem : (MulAut.conj g) x' ∈ ((g • Q : Sylow 3 ↥K) : Subgroup ↥K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (Subgroup.mem_zpowers x'))
  rw [hg] at hmem
  refine ⟨g, g.2, ?_⟩
  have hmem' : (g * x' * g⁻¹ : ↥K) ∈ R.subgroupOf K := by
    have h := hmem
    rw [MulAut.conj_apply] at h
    exact h
  exact Subgroup.mem_subgroupOf.1 hmem'

theorem b2_good_of (i112f : Input11_2Four) {m : ℕ} (hS : GLStanding G m 3) {B : Subgroup G}
    {b : G} (hBel : IsElemAbelian 3 B) (hBC : B ≤ Cb b)
    (hrk : GLATwoLocalRank 3 ↥(Cb b) ≤ CFSG.Open.pRank 3 B) {L R : Subgroup G}
    (hL : GLAPComponent 3 (Cb b) L) (hn : ¬ B ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center ↥(barX 3 (Cb b) (bClosure B L)) ≠ ⊥) (hRL : R ≤ L)
    (hRc : Nat.card R = 3 ^ (Nat.card L).factorization 3) :
    (Nat.card R = 27 ∧ (¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) ∧ ∀ a ∈ R, a ^ 3 = 1) ∧
      b2_Good b L R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heq : Nat.card (R.subgroupOf L) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  have hcard : Nat.card (R.subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [heq]; exact hRc
  obtain ⟨h27, hna, hexp, hc4, hc5⟩ := i112f G m hS (Cb b) B L hBel hBC hrk hL hn hZ
    (Sylow.ofCard (R.subgroupOf L) hcard)
  have h27' : Nat.card (R.subgroupOf L) = 27 := h27
  have hna' : ¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a := by
    intro h
    apply hna
    intro r hr s hs
    exact Subtype.ext (h r (Subgroup.mem_subgroupOf.1 hr) s (Subgroup.mem_subgroupOf.1 hs))
  have hexp' : ∀ a ∈ R, a ^ 3 = 1 := by
    intro a ha
    have := hexp ⟨a, hRL ha⟩ (Subgroup.mem_subgroupOf.2 ha)
    exact congrArg Subtype.val this
  exact ⟨⟨heq ▸ h27', hna', hexp'⟩, ⟨hL, hRL, hexp', hc4, hc5⟩⟩

theorem b2_center_card {b : G} {K : Subgroup G} (hbK : b ∈ K) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hel : IsElemAbelian 3 (Subgroup.center ↥(barX 3 (Cb b) K)))
    (hle : Nat.card ↥(Subgroup.center ↥(barX 3 (Cb b) K)) ≤ 9)
    (hne : barX 3 (Cb b) (Subgroup.zpowers b) ≠ barCenterAt 3 b K) :
    Nat.card ↥(barCenterAt 3 b K) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzC : Subgroup.zpowers b ≤ Cb b := Subgroup.zpowers_le.2 hbC
  have hzK : Subgroup.zpowers b ≤ K := Subgroup.zpowers_le.2 hbK
  have hpow3 : ∀ y ∈ Subgroup.zpowers b, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hcT : Nat.card ↥(barX 3 (Cb b) (Subgroup.zpowers b)) = 3 := by
    rw [b2_card_barX hzC (fun y hy hyP => b2_three_core hyP (k := 1) (by simpa using hpow3 y hy)),
      Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hTle : barX 3 (Cb b) (Subgroup.zpowers b) ≤ barCenterAt 3 b K := by
    intro w hw
    obtain ⟨g, hg, hgz, rfl⟩ := b2_mem_barX_iff.1 hw
    rw [b2_mem_barCenterAt]
    refine ⟨b2_mem_barX_iff.2 ⟨g, hg, hzK hgz, rfl⟩, fun v hv => ?_⟩
    obtain ⟨y, hy, hyK, rfl⟩ := b2_mem_barX_iff.1 hv
    refine (b2_comm_iff _ hy hg).2 ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgz
    have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    have hyg : y * b ^ k = b ^ k * y := (Commute.zpow_right hyb k).eq
    rw [hyg]
    simp
  have hcard : Nat.card ↥(barCenterAt 3 b K) = Nat.card ↥(Subgroup.center ↥(barX 3 (Cb b) K)) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hpg : IsPGroup 3 ↥(Subgroup.center ↥(barX 3 (Cb b) K)) := fun g =>
    ⟨1, Subtype.ext (by simpa using hel.2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hgt : 3 < Nat.card ↥(barCenterAt 3 b K) := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_of_le_of_card_ge hTle (by rw [hcT]; exact h))
  rw [hcard, hn] at hgt ⊢
  rw [hn] at hle
  have hn3 : n < 3 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h
    norm_num at this
    omega
  interval_cases n <;> simp at hgt hle ⊢

theorem b2_center_ne_bot {X : Subgroup G} {K : Subgroup G} (h : Nat.card ↥(Subgroup.center ↥(barX 3 X K)) = 9) :
    Subgroup.center ↥(barX 3 X K) ≠ ⊥ := by
  intro h'
  rw [h', Subgroup.card_bot] at h
  omega

theorem b2_rank5 (i112 : Input11_2Full) (i112f : Input11_2Four) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L₁ L₂ L₃ : Subgroup G}
    (hT : Tri B b L₁ L₂ L₃) (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃) (hbK : b ∈ bClosure B L₁)
    (hnZ : barImageAt 3 b (Subgroup.zpowers b) ≠ barCenterAt 3 b (bClosure B L₁)) :
    ∀ x ∈ bClosure B L₁, x ≠ 1 → x ^ 3 = 1 → 5 ≤ CFSG.Open.pRank 3 (Cb x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := hT.elemB
  have hbB : b ∈ B := hT.mem
  have hb1 : b ≠ 1 := hT.ne_one
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hBC : B ≤ Cb b := fun g hg => Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hBel.1.is_comm.comm ⟨g, hg⟩ ⟨b, hbB⟩))
  have hrk : GLATwoLocalRank 3 ↥(Cb b) ≤ CFSG.Open.pRank 3 B :=
    (glaTwoLocalRank_subgroup_le Nat.prime_three (Cb b)).trans
      (hS.rank_eq.le.trans (hS.le_pRank' hB))
  obtain ⟨β, hβB, hβ2, hβ3, hβ1⟩ := hT.cyc
  have e2 : bClosure B L₂ = bClosure B L₁ := by
    rw [hβ2]; exact b2_bClosure_conj hβB L₁
  have e3 : bClosure B L₃ = bClosure B L₂ := by
    rw [hβ3]; exact b2_bClosure_conj hβB L₂
  have hK2 : bClosure B L₂ = L₁ ⊔ L₂ ⊔ L₃ := e2.trans hK
  have hK3 : bClosure B L₃ = L₁ ⊔ L₂ ⊔ L₃ := e3.trans hK2
  have hn₁ : ¬ B ≤ Subgroup.normalizer (L₁ : Set G) := fun h =>
    hT.ne₁₂ (hβ2.trans (b2_conj_of_mem_normalizer (h hβB))).symm
  have hn₂ : ¬ B ≤ Subgroup.normalizer (L₂ : Set G) := fun h =>
    hT.ne₂₃ (hβ3.trans (b2_conj_of_mem_normalizer (h hβB))).symm
  have hn₃ : ¬ B ≤ Subgroup.normalizer (L₃ : Set G) := fun h =>
    hT.ne₁₃ (hβ1.trans (b2_conj_of_mem_normalizer (h hβB)))
  have hbK' : b ∈ L₁ ⊔ L₂ ⊔ L₃ := hK ▸ hbK
  have hZinfo := (i112 G m 3 hS (Cb b) B L₁ hBel hBC hrk hT.comp₁ hn₁).2.2.2.1
  rw [hK] at hZinfo
  rw [hK] at hnZ
  have h9ZC : Nat.card ↥(barCenterAt 3 b (L₁ ⊔ L₂ ⊔ L₃)) = 9 :=
    b2_center_card hbK' hb3 hb1 hZinfo.1 hZinfo.2 hnZ
  have hc9 : Nat.card ↥(Subgroup.center ↥(barX 3 (Cb b) (L₁ ⊔ L₂ ⊔ L₃))) = 9 := by
    rw [← h9ZC]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  have hZne := b2_center_ne_bot hc9
  obtain ⟨R, R₁, R₂, R₃, hSyl⟩ := three_sylow hT hK hbK
  have hRL₁ : R₁ ≤ L₁ := by rw [hSyl.h1]; exact inf_le_right
  have hRL₂ : R₂ ≤ L₂ := by rw [hSyl.h2]; exact inf_le_right
  have hRL₃ : R₃ ≤ L₃ := by rw [hSyl.h3]; exact inf_le_right
  obtain ⟨hR₁, hG₁⟩ := b2_good_of i112f hS hBel hBC hrk hT.comp₁ hn₁
    (by rw [hK]; exact hZne) hRL₁ hSyl.s1
  obtain ⟨hR₂, hG₂⟩ := b2_good_of i112f hS hBel hBC hrk hT.comp₂ hn₂
    (by rw [hK2]; exact hZne) hRL₂ hSyl.s2
  obtain ⟨hR₃, hG₃⟩ := b2_good_of i112f hS hBel hBC hrk hT.comp₃ hn₃
    (by rw [hK3]; exact hZne) hRL₃ hSyl.s3
  have hp3 : ∀ y ∈ R₁ ⊔ R₂ ⊔ R₃, ∃ k : ℕ, y ^ (3 ^ k) = 1 := by
    intro y hy
    rw [← hSyl.hprod] at hy
    obtain ⟨k, hk⟩ := hSyl.hRp ⟨y, hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hSetup : b2_Setup b L₁ L₂ L₃ R₁ R₂ R₃ :=
    ⟨hG₁, hG₂, hG₃, hT.ne₁₂, hT.ne₂₃, hT.ne₁₃, hSyl.c12, hSyl.c23, hSyl.c13, hp3⟩
  have hJ9 := b2_card_J hSetup h9ZC
  have hdist := b2_distinct hSyl hβB hβ2 hβ3 hβ1 hJ9 hR₁.1 hR₁.2.1
  have hrank := rank5_of_three_extraspecial hSyl.c12 hSyl.c23 hSyl.c13 hR₁ hR₂ hR₃ hJ9
    hdist.1 hdist.2.1 hdist.2.2
  intro x hx hx1 hx3
  rw [hK] at hx
  obtain ⟨c, hcK, hcx⟩ := b2_sylow_conj hSyl.hRK hSyl.hRs hx hx3 hx1
  have h5 := hrank (c * x * c⁻¹) (by rw [← hSyl.hprod]; exact hcx)
  rw [← hSyl.hprod] at h5
  have hmap : ((R ⊓ Cb (c * x * c⁻¹)).map (MulAut.conj c⁻¹).toMonoidHom) ≤ Cb x := by
    rintro _ ⟨y, ⟨hyR, hyC⟩, rfl⟩
    have hyC' : y * (c * x * c⁻¹) = (c * x * c⁻¹) * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
    rw [Subgroup.mem_centralizer_singleton_iff]
    show c⁻¹ * y * c⁻¹⁻¹ * x = x * (c⁻¹ * y * c⁻¹⁻¹)
    calc c⁻¹ * y * c⁻¹⁻¹ * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [hyC']
      _ = x * (c⁻¹ * y * c⁻¹⁻¹) := by group
  exact h5.trans ((CFSG.SectionRank.pRank_le_map (by norm_num) (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective _).trans (CFSG.SectionRank.pRank_mono (by norm_num) hmap))

end B2Sec

section BfSec

open scoped commutatorElement

theorem bf_glaPLayer_gLBConj (g : G) (X : Subgroup G) :
    GLAPLayer 3 (GLBConj g X) = GLBConj g (GLAPLayer 3 X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer 3) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj g hL)

theorem bf_mem_normalizer_layer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer 3 X : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, ← bf_glaPLayer_gLBConj, gLBConj_eq_of_mem_normalizer hg]

omit [Finite G] in
theorem bf_layer_le (X : Subgroup G) : GLAPLayer 3 X ≤ X :=
  sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem bf_gLBConj_bClosure_le {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) ≤ bClosure B L := by
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  unfold bClosure
  refine iSup₂_le fun b hb => ?_
  intro z hz
  rw [Subgroup.mem_comap]
  have e : (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g := by
    simp
  rw [e]
  have hm : g⁻¹ * z * g ∈ GLBConj (b * g) L := by
    rw [mem_gLBConj]
    have e2 : b * g * (g⁻¹ * z * g) * (b * g)⁻¹ = b * z * b⁻¹ := by group
    rw [e2]
    exact mem_gLBConj.1 hz
  exact (le_iSup₂ (f := fun (c : G) (_ : c ∈ B) => GLBConj c L) (b * g)
    (B.mul_mem hb hg)) hm

omit [Finite G] in
theorem bf_gLBConj_bClosure_eq {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (bClosure B L) = bClosure B L := by
  refine le_antisymm (bf_gLBConj_bClosure_le hg) ?_
  have h0 : GLBConj g⁻¹ (bClosure B L) ≤ bClosure B L :=
    bf_gLBConj_bClosure_le (B.inv_mem hg)
  have h1 : GLBConj g (GLBConj g⁻¹ (bClosure B L)) ≤ GLBConj g (bClosure B L) :=
    gLBConj_mono g h0
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h1

omit [Finite G] in
theorem bf_le_normalizer_bClosure (B L : Subgroup G) :
    B ≤ Subgroup.normalizer (bClosure B L : Set G) := fun _ hg =>
  mem_normalizer_iff_gLBConj_eq.2 (bf_gLBConj_bClosure_eq hg)

omit [Finite G] in
theorem bf_inf_normalizer {A A' : Subgroup G} {g : G} (h : g ∈ Subgroup.normalizer (A : Set G))
    (h' : g ∈ Subgroup.normalizer (A' : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ A' : Subgroup G) : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, Subgroup.mem_inf] at h h' ⊢
  intro x
  rw [h x, h' x]

omit [Finite G] in
theorem bf_isElemAbelian_of_le {B E : Subgroup G} (hB : IsElemAbelian 3 B) (hEB : E ≤ B) :
    IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hB hEB

theorem bf_exists_elemAbelian {H : Subgroup G} {n : ℕ} (hn : 0 < n)
    (h : n ≤ CFSG.Open.pRank 3 H) :
    ∃ F : Subgroup G, F ≤ H ∧ IsElemAbelian 3 F ∧ ∃ k : ℕ, n ≤ k ∧ Nat.card F = 3 ^ k := by
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro j ⟨F, -, -, hF⟩
    have h1 : 3 ^ j ≤ Nat.card G :=
      hF ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card F)
    exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1
  have hne : {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}.Nonempty :=
    by
      rcases Set.eq_empty_or_nonempty
        {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} with h0 | h0
      · rw [CFSG.Open.pRank, h0] at h
        simp at h
        omega
      · exact h0
  obtain ⟨F, hFH, hF, hFk⟩ := Nat.sSup_mem hne hbdd
  exact ⟨F, hFH, hF, _, h, hFk⟩

theorem bf_not_even_of_five_le {e : G} (hrk4 : GLATwoLocalRank 3 G = 4)
    (h5 : 5 ≤ CFSG.Open.pRank 3 (Cb e)) : ¬ Even (Nat.card (P3 (Cb e))) := by
  intro hev
  obtain ⟨F, hFC, hF, k, hk5, hFk⟩ := bf_exists_elemAbelian (H := Cb e) (n := 5) (by norm_num) h5
  have hFp : IsPGroup 3 F := IsPGroup.of_card hFk
  have hFN : F ≤ Subgroup.normalizer (P3 (Cb e) : Set G) :=
    hFC.trans (le_normalizer_glaPPrimeCoreOf 3 (Cb e))
  obtain ⟨T, hT0, -, hT2, hFT⟩ := exists_twoGroup_normalized_of_coprime_even Nat.prime_three
    (by norm_num) hFp hFN (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _) hev
  have h1 := pRank_le_glaTwoLocalRank_of_normalizes Nat.prime_three hT0 hT2 hFT
  have h2 : k ≤ CFSG.Open.pRank 3 F := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hF hFk
  omega

theorem bf_exists_order3_fixed {A P : Subgroup G} (hA : IsPGroup 3 A) (hP : IsPGroup 3 P)
    (hPne : P ≠ ⊥) (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    ∃ x ∈ P, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ a ∈ A, a * x = x * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxP, hx1, hxA⟩ : ∃ x ∈ P, x ≠ 1 ∧ ∀ a ∈ A, a * x = x * a := by
    let φ : A →* MulAut P := (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hAP)
    let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P φ
    have hdvd : 3 ∣ Nat.card P := by
      rcases hP.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq P h) hPne
      · exact h
    have h1 : (1 : P) ∈ MulAction.fixedPoints A P := by
      intro a
      exact smul_one a
    obtain ⟨b, hb, hne⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := P) hdvd h1
    refine ⟨b, b.2, fun h => hne ?_, fun a ha => ?_⟩
    · exact (Subtype.ext h.symm)
    · have := congrArg (fun y : P => (y : G)) (hb ⟨a, ha⟩)
      have h2 : a * (b : G) * a⁻¹ = b := this
      calc a * (b : G) = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [h2]
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk')
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa using hj))
  have hord : orderOf x = 3 ^ j := hj
  refine ⟨x ^ (3 ^ (j - 1)), P.pow_mem hxP _, ?_, ?_, fun a ha => ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hord]
    exact pow_orderOf_eq_one x
  · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hord]
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos)
  · exact (Commute.pow_right (show Commute a x from hxA a ha) _).eq

theorem bf_center_quot_eq_bot {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) {a : Q}
    (ha : a ∉ Subgroup.center Q) : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  have := hQ.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q))
    with h | h
  · exact h
  · exfalso
    apply ha
    have key : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q := by
      intro x y
      rw [← QuotientGroup.eq_one_iff]
      have hy : (QuotientGroup.mk y : Q ⧸ Subgroup.center Q) ∈
          Subgroup.center (Q ⧸ Subgroup.center Q) := h ▸ Subgroup.mem_top _
      have h2 := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk x)
      exact commutatorElement_eq_one_iff_mul_comm.2 h2
    have hc : commutator Q ≤ Subgroup.center Q := by
      rw [commutator_def]
      exact Subgroup.commutator_le.2 fun x _ y _ => key x y
    rw [hQ.1] at hc
    exact hc (Subgroup.mem_top a)

theorem bf_exists_e0 (i112t : Input11_2Two) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L₁ L₂ L₃ : Subgroup G}
    (hT : Tri B b L₁ L₂ L₃) (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃)
    (hX3 : ∃ a : barOf 3 L₁, a ^ 3 = 1 ∧ a ∉ Subgroup.center (barOf 3 L₁)) :
    ∃ e₀ ∈ B, e₀ ∈ bClosure B L₁ ∧ e₀ ^ 3 = 1 ∧ e₀ ∉ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := hB.1.1
  obtain ⟨β, hβB, hβ2, -, -⟩ := hT.cyc
  have hβn : β ∉ Subgroup.normalizer (L₁ : Set G) := by
    intro h
    exact hT.ne₁₂ (hβ2.trans (gLBConj_eq_of_mem_normalizer h)).symm
  have hBn : ¬ B ≤ Subgroup.normalizer (L₁ : Set G) := fun h => hβn (h hβB)
  have hBC : B ≤ Cb b := le_centralizer_of_mem hBel hT.mem
  have hrk : GLATwoLocalRank 3 ↥(Cb b) ≤ CFSG.Open.pRank 3 B :=
    (glaTwoLocalRank_subgroup_le Nat.prime_three (Cb b)).trans
      (hS.rank_eq.le.trans (hS.le_pRank' hB))
  obtain ⟨e⟩ := i112t G m hS (Cb b) B L₁ hBel hBC hrk hT.comp₁ hBn β hβB hβn
  set L₀ : Subgroup G := GLAPLayer 3 (bClosure B L₁ ⊓ Subgroup.centralizer ({β} : Set G)) with hL₀
  have hKC : bClosure B L₁ ≤ Cb b := by
    rw [hK]
    exact sup_le (sup_le hT.comp₁.1 hT.comp₂.1) hT.comp₃.1
  have hL₀K : L₀ ≤ bClosure B L₁ := (bf_layer_le _).trans inf_le_left
  have hL₀C : L₀ ≤ Cb b := hL₀K.trans hKC
  have hb3 : b ^ 3 = 1 := hBel.2 b hT.mem
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hT.ne_one
  have h3 : 3 ∣ Nat.card L₀ := by
    obtain ⟨a, ha3, ha⟩ := hX3
    have hā3 : (QuotientGroup.mk a : barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁)) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, ha3, QuotientGroup.mk_one]
    have hā1 : (QuotientGroup.mk a : barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁)) ≠ 1 :=
      fun h => ha ((QuotientGroup.eq_one_iff a).1 h)
    have hd : 3 ∣ Nat.card (barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁)) := by
      have := orderOf_dvd_natCard (QuotientGroup.mk a : barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁))
      rwa [orderOf_eq_prime hā3 hā1] at this
    have h1 : Nat.card (barOf 3 L₀) =
        Nat.card (barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁)) := Nat.card_congr e.toEquiv
    have h2 : Nat.card (barOf 3 L₀) ∣ Nat.card L₀ :=
      Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥L₀)
    exact hd.trans (h1 ▸ h2)
  have hbL₀ : b ∉ L₀ := by
    intro hb
    obtain ⟨a, -, ha⟩ := hX3
    have hcen := bf_center_quot_eq_bot (isQuasisimple_quotient_of_glaPComponent hT.comp₁) ha
    have hbc : ∀ y ∈ L₀, b * y = y * b := fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hL₀C hy)).symm
    have hmem : e (QuotientGroup.mk ⟨b, hb⟩) ∈
        Subgroup.center (barOf 3 L₁ ⧸ Subgroup.center (barOf 3 L₁)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := e.surjective z
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      show (QuotientGroup.mk (y' * ⟨b, hb⟩) : barOf 3 L₀) = QuotientGroup.mk (⟨b, hb⟩ * y')
      congr 1
      exact Subtype.ext (hbc y' y'.2).symm
    rw [hcen, Subgroup.mem_bot] at hmem
    have h1 : (QuotientGroup.mk ⟨b, hb⟩ : barOf 3 L₀) = 1 := e.injective (by rw [hmem, map_one])
    have h2 : (⟨b, hb⟩ : ↥L₀) ∈ GLAPPrimeCore 3 ↥L₀ := (QuotientGroup.eq_one_iff _).1 h1
    have h3' : b ∈ P3 L₀ := ⟨_, h2, rfl⟩
    have h4 := Subgroup.orderOf_dvd_natCard (P3 L₀) h3'
    rw [hbord] at h4
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three L₀ h4
  have hBL₀ : B ≤ Subgroup.normalizer (L₀ : Set G) := fun g hg =>
    bf_mem_normalizer_layer (bf_inf_normalizer (bf_le_normalizer_bClosure B L₁ hg)
      (Subgroup.le_normalizer (le_centralizer_of_mem hBel hβB hg)))
  have hBp : IsPGroup 3 B := IsPGroup.of_card (hS.card_eq hB)
  obtain ⟨S, hSL, hScard, hSB⟩ := exists_normalized_sylow hBp hBL₀
  have hSne : S ≠ ⊥ := by
    intro h
    have h1 : 0 < (Nat.card L₀).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
    rw [h, Subgroup.card_bot] at hScard
    have : 3 ^ 1 ≤ 3 ^ (Nat.card L₀).factorization 3 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hSp : IsPGroup 3 S := IsPGroup.of_card hScard
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun s hs => hSB a ha s hs
  obtain ⟨x, hxS, hx3, hx1, hxB⟩ := bf_exists_order3_fixed hBp hSp hSne hBS
  have hE : IsElemAbelian 3 (B ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_zpowers hBel hx3 hxB
  have hsc : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB
  have hEq : B ⊔ Subgroup.zpowers x = B := hsc.2.2 _ le_top hE le_sup_left
  have hxB' : x ∈ B := by
    have : x ∈ B ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rwa [hEq] at this
  refine ⟨x, hxB', hL₀K (hSL hxS), hx3, fun hxb => ?_⟩
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hxb
  have heq : Subgroup.zpowers x = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hbord])
  have hbx : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
  exact hbL₀ (Subgroup.zpowers_le.2 (hSL hxS) hbx)

theorem b_final (i112t : Input11_2Two) (iB0 : InputB0T) {m : ℕ} (hS : GLStanding G m 3)
    (hrk4 : GLATwoLocalRank 3 G = 4) {B : Subgroup G} (hB : IsBZeroMax 3 B)
    (hwb : IsWeaklyBalancedWrt 3 2 B) {b : G} {L₁ L₂ L₃ : Subgroup G} (hT : Tri B b L₁ L₂ L₃)
    (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃) (hbK : b ∈ bClosure B L₁)
    (hX3 : ∃ a : barOf 3 L₁, a ^ 3 = 1 ∧ a ∉ Subgroup.center (barOf 3 L₁))
    (h5 : ∀ x ∈ bClosure B L₁, x ≠ 1 → x ^ 3 = 1 → 5 ≤ CFSG.Open.pRank 3 (Cb x)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB1 : IsBOneMax 3 B := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax le_rfl hB
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hodd : ∀ e ∈ bClosure B L₁, e ≠ 1 → e ^ 3 = 1 → ¬ Even (Nat.card (P3 (Cb e))) :=
    fun e he he1 he3 => bf_not_even_of_five_le hrk4 (h5 e he he1 he3)
  obtain ⟨e₀, he₀B, he₀K, -, he₀b⟩ := bf_exists_e0 i112t hS hB1 hT hK hX3
  obtain ⟨-, D, hDB, hD, -, hDev⟩ := hB
  have hDev' := hDev rfl
  have hDne : D ≠ ⊥ := by
    intro h
    have h1 := hD.2
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 < 3 ^ 2 := by norm_num
    omega
  have hBΔ : B ≤ Subgroup.normalizer (GLADelta 3 D : Set G) := le_normalizer_gLADelta hBel hDB
  have hcop : Nat.Coprime 3 (Nat.card (GLADelta 3 D)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta Nat.prime_three hDne
  have hΔK : CFSG.Open.IsKGroup ↥(GLADelta 3 D) := by
    refine CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hS.kProper ?_
    intro hΔ
    obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    have hle : GLADelta 3 D ≤ Subgroup.centralizer ({d} : Set G) :=
      (iInf₂_le d hdD).trans ((iInf_le _ hd1').trans
        (Subgroup.map_subtype_le _))
    rw [hΔ] at hle
    have hcen : d ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
    have hcn : (Subgroup.center G).Normal := inferInstance
    rcases hS.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h] at hcen
      exact hd1' (Subgroup.mem_bot.1 hcen)
    · obtain ⟨a, b, hab⟩ := hS.nonabelian
      apply hab
      have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
  obtain ⟨T, hTΔ, hT2, hBT, hTB⟩ := iB0 G B (GLADelta 3 D) hBel hBΔ hcop hΔK hDev'
  set E : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers e₀ with hE
  have hEB : E ≤ B := sup_le (Subgroup.zpowers_le.2 hT.mem) (Subgroup.zpowers_le.2 he₀B)
  have hEK : E ≤ bClosure B L₁ :=
    sup_le (Subgroup.zpowers_le.2 hbK) (Subgroup.zpowers_le.2 he₀K)
  have hEel : IsElemAbelian 3 E := bf_isElemAbelian_of_le hBel hEB
  have hbE : b ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have he₀E : e₀ ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀)
  have hEne : E ≠ ⊥ := fun h => hT.ne_one (Subgroup.mem_bot.1 (h ▸ hbE))
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  have hTcop : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hEN : E ≤ Subgroup.normalizer (T : Set G) := hEB.trans hBT
  have hgen := le_iSup_inf_centralizer_hyperplane hEel hEN hTcop
  have hb3 : b ^ 3 = 1 := hBel.2 b hT.mem
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hT.ne_one
  have key : ∃ e ∈ E, e ≠ 1 ∧ ⁅T ⊓ Cb e, B⁆ ≠ ⊥ := by
    by_contra hno
    apply hTB
    have hz : ∀ e ∈ E, e ≠ 1 → ⁅T ⊓ Cb e, B⁆ = ⊥ := fun e he he1 =>
      by_contra fun h => hno ⟨e, he, he1, h⟩
    have hTle : T ≤ Subgroup.centralizer (B : Set G) := by
      refine hgen.trans (iSup₂_le fun K hK => ?_)
      have hK0 : K ≠ ⊥ := by
        rintro rfl
        have hidx : Nat.card E = 3 := by
          have h1 := hK.2
          have h2 : ((⊥ : Subgroup G).subgroupOf E) = ⊥ := by
            ext y
            simp
          rw [h2, Subgroup.index_bot] at h1
          exact h1
        have hcz : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbord]
        have heq : Subgroup.zpowers b = E :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hidx, hcz])
        exact he₀b (heq ▸ he₀E)
      obtain ⟨⟨e, heK⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK0
      have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
      intro t ht
      have ht' : t ∈ T ⊓ Cb e :=
        ⟨ht.1, Subgroup.centralizer_le (Set.singleton_subset_iff.2 heK) ht.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro β hβ
      have h1 : (⁅t, β⁆ : G) ∈ (⁅T ⊓ Cb e, B⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ht' hβ
      rw [hz e (hK.1 heK) he1', Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun t ht β hβ => ?_)
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 (hTle ht) β hβ).symm
  obtain ⟨e, heE, he1, hS0⟩ := key
  have heB : e ∈ B := hEB heE
  have he3 : e ^ 3 = 1 := hBel.2 e heB
  have heK : e ∈ bClosure B L₁ := hEK heE
  have hwb' := hwb D ⟨hDB, hD.1, hD.2⟩ e heB he1
  have hS1 : ⁅T ⊓ Cb e, B⁆ ≤ P3 (Cb e) :=
    (Subgroup.commutator_mono (inf_le_inf_right _ hTΔ) le_rfl).trans hwb'
  have hS2 : ⁅T ⊓ Cb e, B⁆ ≤ T := by
    refine Subgroup.commutator_le.2 fun t ht β hβ => ?_
    have h1 : β * t⁻¹ * β⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 (hBT hβ) t⁻¹).1 (T.inv_mem ht.1)
    have h2 := T.mul_mem ht.1 h1
    rw [commutatorElement_def]
    simpa [mul_assoc] using h2
  have hSp : IsPGroup 2 ↥(⁅T ⊓ Cb e, B⁆ : Subgroup G) := hT2.to_le hS2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card (⁅T ⊓ Cb e, B⁆ : Subgroup G) :=
    (hSp.card_eq_or_dvd).resolve_left fun h => hS0 (Subgroup.eq_bot_of_card_eq _ h)
  exact hodd e heK he1 he3 (even_iff_two_dvd.2 (h2dvd.trans (Subgroup.card_dvd_of_le hS1)))

end BfSec

section JmSec

theorem jstar_mem {m : ℕ} (hS : GLStanding G m 3) {b : G} {L : Subgroup G}
    (hL : GLAPComponent 3 (Cb b) L) (hbL : b ∈ L) (hb3 : b ^ 3 = 1)
    (hfus : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b))) {x : G}
    (hxC : x ∈ Cb b) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxL : ⁅L, Subgroup.zpowers x⁆ ≤ P3 (Cb b)) :
    ∀ g ∈ L ⊓ Cb x, (∃ k : ℕ, g ^ (3 ^ k) = 1) → g ∈ GLAPLayer 3 (L ⊓ Cb x) := by
  have hLC : L ≤ Cb b := hL.1
  have hxn : x ∈ Subgroup.normalizer (L : Set G) := j_normalizes hL hxC hxL
  have hbarA := j_barX_A hLC hxC hx3 hxn hxL
  have hq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cb b) (L ⊓ Cb x)) := by
    rw [hbarA]; exact hL.2.2.1.2.2
  have hbot : GLAPPrimeCore 3 ↥(barX 3 (Cb b) (L ⊓ Cb x)) = ⊥ := by
    rw [hbarA]; exact j_core_bot hL.2.2.1.2.2 (j_center_card hfus)
  have hAC : L ⊓ Cb x ≤ Cb b := inf_le_left.trans hLC
  obtain ⟨-, J, hJ, hJtop, hJuniq⟩ := j_comp_A hAC hq hbot
  have hlayer : GLAPLayer 3 (L ⊓ Cb x) = J := by
    unfold GLAPLayer
    have : {L' | GLAPComponent 3 (L ⊓ Cb x) L'} = {J} :=
      Set.ext fun L' => ⟨fun h => hJuniq L' h, fun h => (Set.mem_singleton_iff.1 h) ▸ hJ⟩
    rw [this, sSup_singleton]
  rw [hlayer]
  rintro g hg ⟨k, hk⟩
  refine q_mem_of_bar hJ hg hk ?_
  rw [hJtop]
  exact Subgroup.mem_top _

end JmSec

section LcSec

open scoped commutatorElement

theorem lc_comm_comp {M J : Subgroup G} (hJ : GLAPComponent 3 M J) {s : ↥M}
    (hs : s ∈ oPrimeP 3 ↥M) {j : ↥M} (hj : j ∈ J.subgroupOf M) :
    ⁅j, s⁆ ∈ GLAPPrimeCore 3 ↥M := by
  have hcomp : IsComponentOf (barX 3 M J) ⊤ := hJ.2.2.1
  have hn : (CFSG.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M)).Normal := CFSG.pCore_normal
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes _
      (CFSG.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M)) hcomp with h | h
  · exfalso
    have hp : IsPGroup 3 ↥(barX 3 M J) :=
      IsPGroup.to_le (CFSG.pCore_isPGroup (p := 3) (G := ↥M ⧸ GLAPPrimeCore 3 ↥M)) h
    have hsolv : Group.IsSolvable ↥(barX 3 M J) := by
      have : Group.IsNilpotent ↥(barX 3 M J) := hp.isNilpotent
      infer_instance
    have hperf : Group.IsPerfect ↥(barX 3 M J) := ⟨hcomp.2.2.1⟩
    have hnt : Nontrivial ↥(barX 3 M J) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hcomp.2.2
    exact Group.IsPerfect.not_isSolvable _ hsolv
  · have h1 : ⁅QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) j,
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) s⁆ ∈
        ⁅barX 3 M J, CFSG.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hj) hs
    rw [h] at h1
    rw [← map_commutatorElement] at h1
    exact (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 h1)

theorem layer_comm_oPrimeP (M : Subgroup G) : ⁅GLAPLayer 3 M, oPrimePOf 3 M⁆ ≤ P3 M := by
  rw [Subgroup.commutator_le]
  intro g hg s hs
  obtain ⟨s', hs', rfl⟩ := hs
  set π : ↥M →* ↥M ⧸ GLAPPrimeCore 3 ↥M := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  let D : Subgroup ↥M := (Subgroup.centralizer ({π s'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))).comap π
  have hDiff : ∀ y : ↥M, y ∈ D ↔ ⁅y, s'⁆ ∈ GLAPPrimeCore 3 ↥M := by
    intro y
    rw [← QuotientGroup.eq_one_iff (N := GLAPPrimeCore 3 ↥M) ⁅y, s'⁆]
    show _ ↔ π ⁅y, s'⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    simp only [D, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    exact eq_comm
  have hD : GLAPLayer 3 M ≤ D.map M.subtype := by
    refine sSup_le fun J hJ => ?_
    intro x hx
    have hxM : x ∈ M := hJ.1 hx
    exact ⟨⟨x, hxM⟩, (hDiff _).2 (lc_comm_comp hJ hs' hx), rfl⟩
  obtain ⟨g', hg', rfl⟩ := hD hg
  exact ⟨_, (hDiff _).1 hg', rfl⟩

theorem lc_o_inf_le {M H : Subgroup G} (hHM : H ≤ M) :
    oPrimePOf 3 M ⊓ H ≤ oPrimePOf 3 H := by
  refine g2_crit (X := H) (N := oPrimePOf 3 M ⊓ H) inf_le_right ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro w hw
    have hwM : w ∈ M := hHM hw
    have h1 : w ∈ Subgroup.normalizer (oPrimePOf 3 M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (g2_oPrimePOf_le M)).1
        (g2_oPrimePOf_normal M) hwM
    have h2 : w ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hw
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro z
    simp only [Subgroup.mem_inf]
    rw [h1 z, h2 z]
  · intro g hg
    obtain ⟨k, hk⟩ := g2_mem_oPrimePOf hg.1
    refine ⟨k, ?_⟩
    have h1 := gLAPPrimeCoreOf_inf_le Nat.prime_three M H
    rw [inf_eq_right.2 hHM] at h1
    exact h1 ⟨hk, H.pow_mem hg.2 _⟩

theorem lc_core_map {A B : Type*} [Group A] [Group B] [Finite A] (ψ : A →* B)
    (hψ : Function.Injective ψ) (H : Subgroup A) :
    GLAPPrimeCoreOf 3 (H.map ψ) = (GLAPPrimeCoreOf 3 H).map ψ := by
  have hker : Nat.Coprime 3 (Nat.card ↥(H ⊓ ψ.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).2 hψ, inf_bot_eq]
    simp
  have h1 := glaPPrimeCore_map_subgroupMap Nat.prime_three ψ H hker
  have h2 : (H.map ψ).subtype.comp (ψ.subgroupMap H) = ψ.comp H.subtype := by
    ext x; rfl
  unfold GLAPPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem lc_layer_map {A B : Type*} [Group A] [Group B] [Finite A] (ψ : A →* B)
    (hψ : Function.Injective ψ) (H : Subgroup A) :
    GLAPLayer 3 (H.map ψ) = (GLAPLayer 3 H).map ψ := by
  have hker : Nat.Coprime 3 (Nat.card ↥(H ⊓ ψ.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).2 hψ, inf_bot_eq]
    simp
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨K, hK, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three ψ hker hL
    exact Subgroup.map_mono (le_sSup hK)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_map Nat.prime_three ψ hker hK)

omit [Finite G] in
theorem lc_layer_perfect (H : Subgroup G) : ⁅GLAPLayer 3 H, GLAPLayer 3 H⁆ = GLAPLayer 3 H := by
  apply le_antisymm
  · exact (Subgroup.commutator_le).2 fun a ha b hb =>
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine sSup_le fun K hK => ?_
  rw [← glaPComponent_perfect hK]
  exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem lc_trans (i145 : Input14_5) {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hKk : IsKGroup ↥K) (hK0 : GLAPPrimeCoreOf 3 K = ⊥) {z : X} (hzK : z ∈ K) (hz3 : z ^ 3 = 1) :
    ⁅GLAPLayer 3 (K ⊓ Subgroup.centralizer ({z} : Set X)),
      GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({z} : Set X))⁆ = ⊥ := by
  have h0 : GLAPPrimeCore 3 ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hK0
  have h1 := i145 ↥K hKk h0 ⟨z, hzK⟩ (Subtype.ext (by simpa using hz3))
  have hc : (Subgroup.centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({z} : Set X) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
      Subgroup.mem_inf, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨y'.2, ?_⟩
      have := congrArg Subtype.val hy'
      exact this
    · rintro ⟨hyK, hy⟩
      exact ⟨⟨y, hyK⟩, Subtype.ext hy, rfl⟩
  rw [← hc, lc_layer_map _ K.subtype_injective, lc_core_map _ K.subtype_injective,
    ← Subgroup.map_commutator, h1, Subgroup.map_bot]

theorem gcent (i145 : Input14_5) {X : Type} [Group X] [Finite X] {K : Subgroup X} (hK : K.Normal)
    (hKk : IsKGroup ↥K) (hK0 : GLAPPrimeCoreOf 3 K = ⊥) {z : X} (hzK : z ∈ K) (hz3 : z ^ 3 = 1)
    {S : Subgroup X} (hS3 : S ≤ oPrimePOf 3 (Subgroup.centralizer ({z} : Set X))) :
    S ≤ Subgroup.centralizer
      (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({z} : Set X)) : Set X) := by
  set M : Subgroup X := Subgroup.centralizer ({z} : Set X) with hM
  set MK : Subgroup X := K ⊓ M with hMK
  set Λ : Subgroup X := GLAPLayer 3 MK with hΛ
  have hMKM : MK ≤ M := inf_le_right
  have hΛMK : Λ ≤ MK := sSup_le fun _ hL => hL.1
  have hSM : S ≤ M := hS3.trans (g2_oPrimePOf_le M)
  have hA : ⁅S, MK⁆ ≤ oPrimePOf 3 MK := by
    rw [Subgroup.commutator_le]
    intro s hs m hm
    have hsO := hS3 hs
    have hsM := hSM hs
    have hnorm : M ≤ Subgroup.normalizer (oPrimePOf 3 M : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (g2_oPrimePOf_le M)).1
        (g2_oPrimePOf_normal M)
    have h1 : ⁅s, m⁆ ∈ oPrimePOf 3 M := by
      have h2 := (Subgroup.mem_normalizer_iff.1 (hnorm (hMKM hm)) s⁻¹).1 (inv_mem hsO)
      have h3 := mul_mem hsO h2
      have : ⁅s, m⁆ = s * (m * s⁻¹ * m⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]; exact h3
    have h4 : ⁅s, m⁆ ∈ MK := by
      have hsK : s * m * s⁻¹ ∈ K := hK.conj_mem m hm.1 s
      have hzs : Commute z s := Subgroup.mem_centralizer_iff.1 hsM z rfl
      have hzm : Commute z m := Subgroup.mem_centralizer_iff.1 hm.2 z rfl
      have hsmM : s * m * s⁻¹ ∈ M :=
        Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact ((hzs.mul_right hzm).mul_right hzs.inv_right).eq
      have : ⁅s, m⁆ = (s * m * s⁻¹) * m⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact mul_mem ⟨hsK, hsmM⟩ (inv_mem hm)
    exact lc_o_inf_le hMKM ⟨h1, h4⟩
  have hB : ⁅Λ, oPrimePOf 3 MK⁆ ≤ P3 MK := layer_comm_oPrimeP MK
  have hC : ⁅Λ, P3 MK⁆ = ⊥ := lc_trans i145 hKk hK0 hzK hz3
  have hC' : ⁅P3 MK, Λ⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hC
  have hD1 : ⁅⁅Λ, oPrimePOf 3 MK⁆, Λ⁆ = ⊥ :=
    le_bot_iff.1 (hC' ▸ Subgroup.commutator_mono hB le_rfl)
  have hD2 : ⁅⁅oPrimePOf 3 MK, Λ⁆, Λ⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (oPrimePOf 3 MK) Λ]; exact hD1
  have hD : ⁅Λ, oPrimePOf 3 MK⁆ = ⊥ := by
    have := Subgroup.commutator_commutator_eq_bot_of_rotate hD1 hD2
    rwa [lc_layer_perfect] at this
  have hE0 : ⁅S, Λ⁆ ≤ oPrimePOf 3 MK :=
    (Subgroup.commutator_mono le_rfl hΛMK).trans hA
  have hE1 : ⁅⁅S, Λ⁆, Λ⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅⁅S, Λ⁆, Λ⁆ ≤ ⁅oPrimePOf 3 MK, Λ⁆ := Subgroup.commutator_mono hE0 le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hD
  have hE2 : ⁅⁅Λ, S⁆, Λ⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Λ S]; exact hE1
  have hE := Subgroup.commutator_commutator_eq_bot_of_rotate hE2 hE1
  rw [lc_layer_perfect] at hE
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (by rw [Subgroup.commutator_comm]; exact hE)

end LcSec

section QrSec

theorem twoLocalRank_quot_le (W : Subgroup G) :
    GLATwoLocalRank 3 (↥W ⧸ GLAPPrimeCore 3 ↥W) ≤ GLATwoLocalRank 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  exact (glaTwoLocalRank_quotient_le Nat.prime_three (by norm_num) _ hN).trans
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le Nat.prime_three W)

end QrSec

section InvSec

theorem inv_matrix : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), M ^ 4 = 1 → M ^ 2 ≠ 1 → M ^ 2 = -1 := by
  decide +kernel

theorem inv_aut_sq {V : Type} [CommGroup V] [Finite V] (hV : Nat.card V = 9)
    (hexp : ∀ x : V, x ^ 3 = 1) (A : MulAut V) (h4 : A ^ 4 = 1) (h2 : A ^ 2 ≠ 1) :
    ∀ x : V, (A ^ 2) x = x⁻¹ := by
  classical
  let W := Additive V
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmod : ∀ x : W, (3:ℕ) • x = 0 := fun x => by
    show Additive.ofMul ((Additive.toMul x) ^ 3) = 0
    rw [hexp]; rfl
  let _ : Module (ZMod 3) W := AddCommGroup.zmodModule hmod
  have : Module.Finite (ZMod 3) W := Module.Finite.of_finite
  have : Fintype W := Fintype.ofFinite W
  have hcard : Nat.card W = 3 ^ Module.finrank (ZMod 3) W := by
    rw [Nat.card_eq_fintype_card]
    simpa using Module.card_eq_pow_finrank (K := ZMod 3) (V := W)
  have hrank : Module.finrank (ZMod 3) W = 2 := by
    have h9 : Nat.card W = 9 := hV
    rw [h9] at hcard
    have : (3:ℕ) ^ 2 = 3 ^ Module.finrank (ZMod 3) W := by simpa using hcard
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).symm
  let T : Module.End (ZMod 3) W :=
    AddMonoidHom.toZModLinearMap 3 (MulEquiv.toAdditive A).toAddMonoidHom
  have hT : ∀ (k : ℕ) (x : W), (T ^ k) x = Additive.ofMul ((A ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [pow_succ, Module.End.mul_apply, ih]; rfl
  let bs := Module.finBasisOfFinrankEq (ZMod 3) W hrank
  let e := LinearMap.toMatrixAlgEquiv bs
  have h4' : (e T) ^ 4 = 1 := by
    rw [← map_pow]
    have : T ^ 4 = 1 := by
      ext x
      rw [hT]; rw [h4]; rfl
    rw [this, map_one]
  have h2' : (e T) ^ 2 ≠ 1 := by
    intro h
    apply h2
    rw [← map_pow] at h
    have := e.injective (h.trans (map_one e).symm)
    ext x
    have := congrArg (fun f => f (Additive.ofMul x)) this
    simp only [hT] at this
    exact this
  have hm := inv_matrix (e T) h4' h2'
  have hm' : T ^ 2 = -1 := by
    apply e.injective
    rw [map_pow, hm, map_neg, map_one]
  intro x
  have := congrArg (fun f => f (Additive.ofMul x)) hm'
  simp only [hT] at this
  exact this

theorem inv_q8_inverter {K : Type} [Group K] [Finite K] {F : Subgroup K} (hF : IsElemAbelian 3 F)
    (hcard : Nat.card F = 9) (hQ : AutHasQ8 F) :
    ∃ n ∈ Subgroup.normalizer (F : Set K), ∀ x ∈ F, n * x * n⁻¹ = x⁻¹ := by
  obtain ⟨f, hf⟩ := hQ
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (f (QuaternionGroup.a 1))
  have hord : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 := QuaternionGroup.orderOf_a_one
  have h4 : f (QuaternionGroup.a 1) ^ 4 = 1 := by
    rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  have h2 : f (QuaternionGroup.a 1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    have := hf (h.trans (map_one f).symm)
    have h' := orderOf_dvd_of_pow_eq_one this
    rw [hord] at h'
    omega
  have hgn : (g : K) ∈ Subgroup.normalizer (F : Set K) := g.2.2
  let A : MulAut ↥F := F.normalizerMonoidHom ⟨(g : K), hgn⟩
  have hAk : ∀ k : ℕ, ∀ x : ↥F, (((A ^ k) x : ↥F) : K) = (g : K) ^ k * x * ((g : K) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp only [pow_zero, MulAut.one_apply, one_mul, inv_one, mul_one]
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih]
      show (g : K) ^ k * ((g : K) * x * (g : K)⁻¹) * ((g : K) ^ k)⁻¹ = _
      rw [pow_succ']
      group
  have hcent : ∀ k : ℕ, g ^ k ∈ (⊤ ⊓ Subgroup.centralizer (F : Set K)).subgroupOf
      (⊤ ⊓ Subgroup.normalizer (F : Set K)) → ∀ x : ↥F, (g : K) ^ k * x * ((g : K) ^ k)⁻¹ = x := by
    intro k hk x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hk
    have := Subgroup.mem_centralizer_iff.1 hk.2 x x.2
    push_cast at this
    calc (g : K) ^ k * x * ((g : K) ^ k)⁻¹ = (x * (g : K) ^ k) * ((g : K) ^ k)⁻¹ := by
          rw [← this]
      _ = x := by group
  have hA4 : A ^ 4 = 1 := by
    ext x
    rw [hAk]
    have h4' : g ^ 4 ∈ (⊤ ⊓ Subgroup.centralizer (F : Set K)).subgroupOf
        (⊤ ⊓ Subgroup.normalizer (F : Set K)) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_pow, hg]; exact h4
    have := hcent 4 h4' x
    simpa using this
  have hA2 : A ^ 2 ≠ 1 := by
    intro h
    apply h2
    rw [← hg, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨trivial, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun α : MulAut ↥F => (((α ⟨x, hx⟩ : ↥F)) : K)) h
    simp only [hAk, MulAut.one_apply] at this
    calc x * (g : K) ^ 2 = ((g : K) ^ 2 * x * ((g : K) ^ 2)⁻¹) * (g : K) ^ 2 := by rw [this]
      _ = (g : K) ^ 2 * x := by group
  let _ : CommGroup ↥F := { (inferInstance : Group ↥F) with
    mul_comm := fun a b => hF.1.is_comm.comm a b }
  have hexp : ∀ x : ↥F, x ^ 3 = 1 := fun x => Subtype.ext (hF.2 x x.2)
  have key := inv_aut_sq hcard hexp A hA4 hA2
  refine ⟨(g : K) ^ 2, ?_, ?_⟩
  · exact Subgroup.pow_mem _ hgn 2
  · intro x hx
    have := congrArg (fun y : ↥F => (y : K)) (key ⟨x, hx⟩)
    simp only [hAk] at this
    exact this

theorem inv_card_map_mul_card_inf_ker {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (S : Subgroup A) : Nat.card (S.map f) * Nat.card (S ⊓ f.ker : Subgroup A) = Nat.card S := by
  have h1 : (f.comp S.subtype).range = S.map f := by
    ext y; simp [MonoidHom.mem_range, Subgroup.mem_map]
  have h2 : Nat.card ((f.comp S.subtype).ker) = Nat.card (S ⊓ f.ker : Subgroup A) := by
    have : (f.comp S.subtype).ker.map S.subtype = (S ⊓ f.ker : Subgroup A) := by
      ext y
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_inf]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
      · rintro ⟨hy, hf⟩; exact ⟨⟨y, hy⟩, hf, rfl⟩
    rw [← this, Subgroup.card_map_of_injective S.subtype_injective]
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.comp S.subtype).ker
  have h4 := Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp S.subtype)).toEquiv
  rw [h1] at h4
  rw [← h2, ← h4]
  exact h3.symm

theorem inv_odd_pow_conj {K : Type} [Group K] {F : Subgroup K} {u : K}
    (hu : ∀ y ∈ F, u * y * u⁻¹ = y⁻¹) : ∀ j : ℕ, ∀ y ∈ F,
      u ^ (2 * j + 1) * y * (u ^ (2 * j + 1))⁻¹ = y⁻¹ := by
  intro j
  induction j with
  | zero => intro y hy; simpa using hu y hy
  | succ j ih =>
    intro y hy
    have e : u ^ (2 * (j + 1) + 1) = u * (u * u ^ (2 * j + 1)) := by
      rw [← pow_succ', ← pow_succ']; ring_nf
    rw [e]
    have h1 := ih y hy
    have h2 := hu y⁻¹ (F.inv_mem hy)
    have h3 := hu y hy
    calc u * (u * u ^ (2 * j + 1)) * y * (u * (u * u ^ (2 * j + 1)))⁻¹
        = u * (u * (u ^ (2 * j + 1) * y * (u ^ (2 * j + 1))⁻¹) * u⁻¹) * u⁻¹ := by group
      _ = y⁻¹ := by
        rw [h1, h2, inv_inv, h3]

theorem inv_frattini {L : Type} [Group L] [Finite L] {M R : Subgroup L} (hRM : R ≤ M)
    (hRs : Nat.card R = 3 ^ (Nat.card L).factorization 3) {m : L}
    (hm : ∀ r ∈ R, m * r * m⁻¹ ∈ M) :
    ∃ x ∈ M, x⁻¹ * m ∈ Subgroup.normalizer (R : Set L) := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set R' : Subgroup L := R.map (MulAut.conj m).toMonoidHom with hR'
  have hR'mem : ∀ h, h ∈ R' ↔ ∃ r ∈ R, m * r * m⁻¹ = h := by
    intro h
    simp [hR', Subgroup.mem_map]
  have hR'M : R' ≤ M := by
    intro h hh
    obtain ⟨r, hr, rfl⟩ := (hR'mem h).1 hh
    exact hm r hr
  have hR'card : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hMdvd : Nat.card M ∣ Nat.card L := Subgroup.card_subgroup_dvd_card M
  have hRdvd : Nat.card R ∣ Nat.card M := Subgroup.card_dvd_of_le hRM
  have hfac : (Nat.card M).factorization 3 = (Nat.card L).factorization 3 := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hMdvd 3
    · have h1 : (Nat.card R).factorization 3 ≤ (Nat.card M).factorization 3 :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hRdvd 3
      rw [hRs, Nat.Prime.factorization_pow Nat.prime_three] at h1
      simpa using h1
  have hc1 : Nat.card (R.subgroupOf M) = 3 ^ (Nat.card M).factorization 3 := by
    rw [hfac, ← hRs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv
  have hc2 : Nat.card (R'.subgroupOf M) = 3 ^ (Nat.card M).factorization 3 := by
    rw [hfac, ← hRs, ← hR'card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'M).toEquiv
  let P1 : Sylow 3 M := Sylow.ofCard (R.subgroupOf M) hc1
  let P2 : Sylow 3 M := Sylow.ofCard (R'.subgroupOf M) hc2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P1 P2
  have hgS : ∀ a : M, a ∈ (P2 : Subgroup M) ↔ g⁻¹ * a * g ∈ (P1 : Subgroup M) := by
    intro a
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g, g.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ a : L, a ∈ M → ∀ ha : a ∈ M, (a ∈ R') ↔ (g : L)⁻¹ * a * g ∈ R := by
    intro a _ ha
    have := hgS ⟨a, ha⟩
    exact this
  constructor
  · intro hh
    have hmh : m * h * m⁻¹ ∈ R' := (hR'mem _).2 ⟨h, hh, rfl⟩
    have := (key _ (hR'M hmh) (hR'M hmh)).1 hmh
    have e : (g : L)⁻¹ * m * h * ((g : L)⁻¹ * m)⁻¹ = (g : L)⁻¹ * (m * h * m⁻¹) * g := by group
    rw [e]; exact this
  · intro hh
    have e : m * h * m⁻¹ = (g : L) * ((g : L)⁻¹ * m * h * ((g : L)⁻¹ * m)⁻¹) * (g : L)⁻¹ := by group
    have hmM : m * h * m⁻¹ ∈ M := by
      rw [e]
      exact M.mul_mem (M.mul_mem g.2 (hRM hh)) (M.inv_mem g.2)
    have hmR' : m * h * m⁻¹ ∈ R' := by
      refine (key _ hmM hmM).2 ?_
      have e2 : (g : L)⁻¹ * (m * h * m⁻¹) * g = (g : L)⁻¹ * m * h * ((g : L)⁻¹ * m)⁻¹ := by group
      rw [e2]; exact hh
    obtain ⟨r, hr, hrh⟩ := (hR'mem _).1 hmR'
    have : r = h := (MulAut.conj m).injective hrh
    rw [← this]; exact hr

theorem inv_center_sub {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : 3 ^ n ∣ Nat.card (Subgroup.center X)) :
    ∃ S : Subgroup X, S ≤ Subgroup.center X ∧ Nat.card S = 3 ^ n := by
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.center X) 3 h
  refine ⟨T.map (Subgroup.center X).subtype, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩; exact x.2
  · rw [Subgroup.card_map_of_injective (Subgroup.center X).subtype_injective, hT]

theorem inv_abstract (i302 : Input30_2) {L : Type} [Group L] [Finite L] (N : Subgroup L) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (hX : IsSL3Eps (L ⧸ N)) {R : Subgroup L}
    (hRs : Nat.card R = 3 ^ (Nat.card L).factorization 3) (hR27 : Nat.card R = 27)
    (hexp : ∀ a ∈ R, a ^ 3 = 1) {b : L} (hbR : b ∈ R) (hb1 : b ≠ 1)
    (hZ : ∀ x, x ∈ Subgroup.zpowers b ↔ x ∈ R ∧ ∀ r ∈ R, x * r = r * x) :
    ∃ t : L, (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧ t ∈ Subgroup.normalizer (R : Set L) ∧
      ∀ r ∈ R, t * r * t⁻¹ * r ∈ Subgroup.zpowers b := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let π : L →* L ⧸ N := QuotientGroup.mk' N
  have hπ : ∀ x, π x = (x : L ⧸ N) := fun x => rfl
  have hRN : ∀ r ∈ R, π r = 1 → r = 1 := by
    intro r hr h1
    have hrN : r ∈ N := (QuotientGroup.eq_one_iff r).1 h1
    have d1 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp r hr)
    have d2 : orderOf r ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hrN
    have : orderOf r ∣ Nat.gcd 3 (Nat.card N) := Nat.dvd_gcd d1 d2
    rw [hN] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  have hcen : ∀ r ∈ R, π r ∈ Subgroup.center (L ⧸ N) → r ∈ Subgroup.zpowers b := by
    intro r hr hrc
    rw [hZ]
    refine ⟨hr, fun s hs => ?_⟩
    have h1 : π (r * s * r⁻¹ * s⁻¹) = 1 := by
      have := Subgroup.mem_center_iff.1 hrc (π s)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← this]
      group
    have h2 := hRN _ (R.mul_mem (R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr)) (R.inv_mem hs)) h1
    calc r * s = (r * s * r⁻¹ * s⁻¹) * (s * r) := by group
      _ = s * r := by rw [h2, one_mul]
  have hfacL : (Nat.card L).factorization 3 = 3 := by
    have : 3 ^ (Nat.card L).factorization 3 = 3 ^ 3 := by rw [← hRs, hR27]; norm_num
    exact Nat.pow_right_injective (le_refl _ |>.trans (by norm_num : 2 ≤ 3)) this
  have hLX : Nat.card L = Nat.card (L ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hfacX : (Nat.card (L ⧸ N)).factorization 3 = 3 := by
    have h1 : (Nat.card N).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun hd => by
        have := Nat.Coprime.eq_one_of_dvd hN hd
        omega)
    have h2 := congrArg (fun n => n.factorization 3) hLX
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h2
    simp only [Finsupp.add_apply, h1, add_zero] at h2
    omega
  have hPcard : Nat.card (R.map π) = 27 := by
    have := inv_card_map_mul_card_inf_ker π R
    have hk : (R ⊓ π.ker : Subgroup L) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hRN x hx.1 ((MonoidHom.mem_ker).1 hx.2)
    rw [hk, Subgroup.card_bot, mul_one] at this
    rw [this, hR27]
  have hPs : Nat.card (R.map π) = 3 ^ (Nat.card (L ⧸ N)).factorization 3 := by
    rw [hPcard, hfacX]; norm_num
  let P : Sylow 3 (L ⧸ N) := Sylow.ofCard (R.map π) hPs
  have hzb : orderOf (π b) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hexp b hbR, map_one])
  have hzbcard : Nat.card (Subgroup.zpowers (π b)) ≤ 3 := by
    rw [Nat.card_zpowers]; exact Nat.le_of_dvd (by norm_num) hzb
  have hSle : ∀ S : Subgroup (L ⧸ N), S ≤ Subgroup.center (L ⧸ N) → IsPGroup 3 S →
      S ≤ Subgroup.zpowers (π b) := by
    intro S hSc hSp
    have hSn : S.Normal := ⟨fun n hn g => by
      have := Subgroup.mem_center_iff.1 (hSc hn) g
      have e : g * n * g⁻¹ = n := by rw [this]; group
      rw [e]; exact hn⟩
    have hSP : S ≤ R.map π := hSp.le_sylow_of_normal P
    intro s hs
    obtain ⟨r, hr, rfl⟩ := hSP hs
    have := hcen r hr (hSc hs)
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem _ this
  have hZ9 : ¬ 9 ∣ Nat.card (Subgroup.center (L ⧸ N)) := by
    intro hd
    obtain ⟨S, hSc, hS⟩ := inv_center_sub (X := L ⧸ N) (n := 2) (by simpa using hd)
    have hSp : IsPGroup 3 S := IsPGroup.of_card (n := 2) (by rw [hS])
    have := Subgroup.card_le_of_le (hSle S hSc hSp)
    rw [hS] at this
    omega
  have hZ3 : 3 ∣ Nat.card (Subgroup.center (L ⧸ N)) := hX.2
  have hπbZ : π b ∈ Subgroup.center (L ⧸ N) := by
    obtain ⟨S, hSc, hS⟩ := inv_center_sub (X := L ⧸ N) (n := 1) (by simpa using hZ3)
    have hSp : IsPGroup 3 S := IsPGroup.of_card (n := 1) (by rw [hS])
    have hle := hSle S hSc hSp
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [hS]; simpa using hzbcard)
    exact hSc (this ▸ Subgroup.mem_zpowers (π b))
  let ψ : (L ⧸ N) →* ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N)) := QuotientGroup.mk' _
  let φ : L →* ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N)) := ψ.comp π
  have hφker : ∀ x, φ x = 1 ↔ π x ∈ Subgroup.center (L ⧸ N) :=
    fun x => QuotientGroup.eq_one_iff _
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hφb : φ b = 1 := (hφker b).2 hπbZ
  have hfacZ : (Nat.card (Subgroup.center (L ⧸ N))).factorization 3 = 1 := by
    have hpos : Nat.card (Subgroup.center (L ⧸ N)) ≠ 0 := Nat.card_pos.ne'
    have a1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (k := 1) hpos).1
      (by simpa using hZ3)
    have a2 : ¬ 2 ≤ (Nat.card (Subgroup.center (L ⧸ N))).factorization 3 := fun h =>
      hZ9 (by simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (k := 2) hpos).2 h)
    omega
  have hfacK : (Nat.card ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N))).factorization 3 = 2 := by
    have h2 := congrArg (fun n => n.factorization 3)
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (L ⧸ N)))
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h2
    simp only [Finsupp.add_apply, hfacZ] at h2
    omega
  have hker : (R ⊓ φ.ker : Subgroup L) = Subgroup.zpowers b := by
    ext x
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨hx, h1⟩
      exact hcen x hx ((hφker x).1 h1)
    · intro hx
      refine ⟨(Subgroup.zpowers_le.2 hbR) hx, ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [map_zpow, hφb, one_zpow]
  have hbord : orderOf b = 3 := orderOf_eq_prime (hexp b hbR) hb1
  have hFcard : Nat.card (R.map φ) = 9 := by
    have := inv_card_map_mul_card_inf_ker φ R
    rw [hker, Nat.card_zpowers, hbord, hR27] at this
    omega
  have hFs : Nat.card (R.map φ) = 3 ^ (Nat.card ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N))).factorization 3 := by
    rw [hFcard, hfacK]; norm_num
  let F' : Sylow 3 ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N)) := Sylow.ofCard (R.map φ) hFs
  obtain ⟨hFe, hFQ⟩ := (i302 (L ⧸ N) hX).2.1 hfacK F'
  have hFe' : IsElemAbelian 3 (R.map φ) := hFe
  have hFQ' : AutHasQ8 (R.map φ) := hFQ
  obtain ⟨n, hn, hninv⟩ := inv_q8_inverter hFe' hFcard hFQ'
  obtain ⟨m, rfl⟩ := hφsurj n
  have hRM : R ≤ (R.map φ).comap φ := fun r hr => Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem _ hr)
  have hm : ∀ r ∈ R, m * r * m⁻¹ ∈ (R.map φ).comap φ := by
    intro r hr
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hn (φ r)).1 (Subgroup.mem_map_of_mem _ hr)
  obtain ⟨x, hxM, hy⟩ := inv_frattini hRM hRs hm
  have hxF : φ x ∈ R.map φ := Subgroup.mem_comap.1 hxM
  have hyinv : ∀ z ∈ R.map φ, φ (x⁻¹ * m) * z * (φ (x⁻¹ * m))⁻¹ = z⁻¹ := by
    intro z hz
    have hc : (φ x)⁻¹ * z⁻¹ = z⁻¹ * (φ x)⁻¹ := by
      have := hFe'.1.is_comm.comm (⟨(φ x)⁻¹, (R.map φ).inv_mem hxF⟩ : ↥(R.map φ))
        ⟨z⁻¹, (R.map φ).inv_mem hz⟩
      exact congrArg Subtype.val this
    have := hninv z hz
    calc φ (x⁻¹ * m) * z * (φ (x⁻¹ * m))⁻¹
        = (φ x)⁻¹ * (φ m * z * (φ m)⁻¹) * φ x := by rw [map_mul, map_inv]; group
      _ = z⁻¹ := by rw [this, hc]; group
  generalize x⁻¹ * m = u at hy hyinv
  obtain ⟨k, c, hcodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u).ne'
  obtain ⟨j, rfl⟩ := hcodd
  refine ⟨u ^ (2 * j + 1), ⟨k, ?_⟩, Subgroup.pow_mem _ hy _, ?_⟩
  · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  · intro r hr
    have hnr : u ^ (2 * j + 1) * r * (u ^ (2 * j + 1))⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hy (2 * j + 1)) r).1 hr
    have h1 : u ^ (2 * j + 1) * r * (u ^ (2 * j + 1))⁻¹ * r ∈ R ⊓ φ.ker := by
      refine ⟨R.mul_mem hnr hr, ?_⟩
      show φ _ = 1
      have := inv_odd_pow_conj (F := R.map φ) (u := φ u) hyinv j (φ r)
        (Subgroup.mem_map_of_mem _ hr)
      simp only [map_mul, map_inv, map_pow]
      rw [this]
      group
    rwa [hker] at h1

theorem exists_inverter (i302 : Input30_2) {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) {L R : Subgroup G} (hL : L = L₁ ∨ L = L₂ ∨ L = L₃) (hRL : R ≤ L)
    (hRp : IsPGroup 3 R) (hRs : Nat.card R = 3 ^ (Nat.card L).factorization 3) (hbR : b ∈ R) :
    ∃ t ∈ L, (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧ t ∈ Subgroup.normalizer (R : Set G) ∧
      ∀ r ∈ R, t * r * t⁻¹ * r ∈ Subgroup.zpowers b := by
  have hX : IsSL3Eps (↥L ⧸ GLAPPrimeCore 3 ↥L) := by
    rcases hL with rfl | rfl | rfl
    · exact hR.eps₁
    · exact hR.eps₂
    · exact hR.eps₃
  have hSyl : Nat.card R = 27 ∧ (¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) ∧ (∀ a ∈ R, a ^ 3 = 1) ∧
      ZR R = Subgroup.zpowers b := by
    rcases hL with rfl | rfl | rfl
    · exact hR.syl₁ R hRL hRp hRs
    · exact hR.syl₂ R hRL hRp hRs
    · exact hR.syl₃ R hRL hRp hRs
  obtain ⟨h27, -, hexp, hZR⟩ := hSyl
  have hbL : b ∈ L := hRL hbR
  have hN : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  let b' : ↥L := ⟨b, hbL⟩
  have key : ∀ x : ↥L, x ∈ Subgroup.zpowers b' ↔ (x : G) ∈ Subgroup.zpowers b := by
    intro x
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp [b']⟩
    · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext (by simpa [b'] using hk)⟩
  let R' : Subgroup ↥L := R.subgroupOf L
  have hcard : Nat.card R' = Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  have hZ : ∀ x : ↥L, x ∈ Subgroup.zpowers b' ↔ x ∈ R' ∧ ∀ r ∈ R', x * r = r * x := by
    intro x
    rw [key, ← hZR]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : (y : G) = x := hyx
      refine ⟨show (x : G) ∈ R from hyx' ▸ y.2, fun r hr => ?_⟩
      have := Subgroup.mem_center_iff.1 hy ⟨(r : G), hr⟩
      apply Subtype.ext
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2 ⊢
      rw [← hyx']
      exact h2.symm
    · rintro ⟨hx, hc⟩
      refine ⟨⟨(x : G), hx⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      have := hc ⟨(g : G), hRL g.2⟩ g.2
      apply Subtype.ext
      have h2 := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h2 ⊢
      exact h2.symm
  obtain ⟨t, ⟨k, hk⟩, ht, hr⟩ := inv_abstract i302 (GLAPPrimeCore 3 ↥L) hN hX (R := R')
    (hcard ▸ hRs) (hcard ▸ h27) (fun a ha => Subtype.ext (by simpa using hexp a ha))
    (b := b') hbR (fun h => hR.tri.ne_one (congrArg Subtype.val h)) hZ
  refine ⟨(t : G), t.2, ⟨k, ?_⟩, ?_, ?_⟩
  · have := congrArg Subtype.val hk
    simpa using this
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact (Subgroup.mem_normalizer_iff.1 ht ⟨h, hRL hh⟩).1 hh
    · intro hh
      have hhL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem t.2) (hRL hh)) t.2
        simpa [mul_assoc] using this
      exact (Subgroup.mem_normalizer_iff.1 ht ⟨h, hhL⟩).2 hh
  · intro r hrR
    have := (key _).1 (hr ⟨r, hRL hrR⟩ hrR)
    exact this

end InvSec

section NilSec

@[expose] def nil_Nil3 {H : Type*} [Group H] (T : Subgroup H) : Prop :=
  ∃ N : Subgroup H, N ≤ T ∧ (∀ n ∈ N, Nat.Coprime 3 (orderOf n)) ∧
    ∀ t ∈ T, ∃ k : ℕ, t ^ (3 ^ k) ∈ N

theorem nil_mem_of_pow {H : Type*} [Group H] {N : Subgroup H} {x : H} {k : ℕ}
    (hx : Nat.Coprime 3 (orderOf x)) (h : x ^ (3 ^ k) ∈ N) : x ∈ N := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (hx.pow_left k)
  rw [← hm]
  exact N.pow_mem h m

theorem nil_mono {H : Type*} [Group H] {T V : Subgroup H} (h : nil_Nil3 T) (hVT : V ≤ T) :
    nil_Nil3 V := by
  obtain ⟨N, hNT, hN, hp⟩ := h
  refine ⟨N ⊓ V, inf_le_right, fun n hn => hN n hn.1, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := hp t (hVT ht)
  exact ⟨k, hk, V.pow_mem ht _⟩

theorem nil_map {A B : Type*} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    {T : Subgroup A} (h : nil_Nil3 T) : nil_Nil3 (T.map f) := by
  obtain ⟨N, hNT, hN, hp⟩ := h
  refine ⟨N.map f, Subgroup.map_mono hNT, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [orderOf_injective f hf]; exact hN n hn
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨k, hk⟩ := hp t ht
    exact ⟨k, by rw [← map_pow]; exact ⟨_, hk, rfl⟩⟩

theorem nil_coprime_card {H : Type*} [Group H] (N : Subgroup H) [Finite N]
    (h : ∀ n ∈ N, Nat.Coprime 3 (orderOf n)) : Nat.Coprime 3 (Nat.card N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 h3
  have := h (x : H) x.2
  rw [Subgroup.orderOf_coe, hx] at this
  simp at this

theorem nil_CE0 {M E : Type*} [Group M] [Finite M] [Group E] (ψ : M →* E)
    (hker : ∀ x ∈ ψ.ker, ∀ m : M, x * m = m * x) (hker3 : ∀ x ∈ ψ.ker, x ^ 3 = 1)
    (hrange : Nat.Coprime 3 (Nat.card ψ.range)) :
    ∃ K' : Subgroup M, (∀ m ∈ K', Nat.Coprime 3 (orderOf m)) ∧ ∀ m : M, m ^ 3 ∈ K' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 ψ.ker := fun x => ⟨1, Subtype.ext (by simpa using hker3 x x.2)⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hidx : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have hcop : Nat.Coprime (Nat.card ψ.ker) ψ.ker.index := by
    rw [hn, hidx]; exact hrange.pow_left n
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcardK : Nat.card K' = Nat.card ψ.range := by
    rw [← hidx]; exact hK'.symm.index_eq_card.symm
  refine ⟨K', fun m hm => ?_, fun m => ?_⟩
  · exact (hrange.coprime_dvd_right (hcardK ▸ Subgroup.orderOf_dvd_natCard K' hm))
  · obtain ⟨⟨⟨z, hz⟩, ⟨k, hk⟩⟩, hzk⟩ := hK'.2 m
    have hc : Commute z k := hker z hz k
    have hz3 := hker3 z hz
    have : m ^ 3 = k ^ 3 := by
      rw [← hzk, hc.mul_pow, hz3, one_mul]
    rw [this]; exact K'.pow_mem hk 3

theorem nil_CE {D E : Type*} [Group D] [Finite D] [Group E] (ψ : D →* E)
    (hker : ∀ x ∈ ψ.ker, ∀ d : D, x * d = d * x) (hker3 : ∀ x ∈ ψ.ker, x ^ 3 = 1)
    (N : Subgroup E) (hN : ∀ n ∈ N, Nat.Coprime 3 (orderOf n))
    (hq : ∀ d : D, ∃ k : ℕ, ψ d ^ (3 ^ k) ∈ N) :
    ∃ K'' : Subgroup D, (∀ n ∈ K'', Nat.Coprime 3 (orderOf n)) ∧
      ∀ d : D, ∃ k : ℕ, d ^ (3 ^ k) ∈ K'' := by
  set M : Subgroup D := N.comap ψ with hM
  set ψM : M →* E := ψ.comp M.subtype with hψM
  have hrange : Nat.Coprime 3 (Nat.card ψM.range) := by
    have : Finite ψM.range := Finite.of_surjective ψM.rangeRestrict ψM.rangeRestrict_surjective
    apply nil_coprime_card
    rintro _ ⟨m, rfl⟩
    exact hN _ m.2
  have hk1 : ∀ x ∈ ψM.ker, ∀ m : M, x * m = m * x := by
    intro x hx m
    exact Subtype.ext (hker x.1 hx m.1)
  have hk3 : ∀ x ∈ ψM.ker, x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (by simpa using hker3 x.1 hx)
  obtain ⟨K', hK'1, hK'2⟩ := nil_CE0 ψM hk1 hk3 hrange
  refine ⟨K'.map M.subtype, ?_, fun d => ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    show Nat.Coprime 3 (orderOf (m : D))
    rw [Subgroup.orderOf_coe]
    exact hK'1 m hm
  · obtain ⟨k, hk⟩ := hq d
    have hdM : d ^ (3 ^ k) ∈ M := by
      rw [hM, Subgroup.mem_comap, map_pow]; exact hk
    refine ⟨k + 1, ?_⟩
    have := hK'2 ⟨d ^ (3 ^ k), hdM⟩
    rw [pow_succ, pow_mul]
    exact ⟨_, this, rfl⟩


theorem nil_A (i302 : Input30_2) {X : Type} [Group X] [Finite X] (hε : IsSL3Eps X)
    (hX3 : (Nat.card X).factorization 3 = 3) (hZ3 : Nat.card (Subgroup.center X) = 3) {a : X}
    (ha3 : a ^ 3 = 1) (haZ : a ∉ Subgroup.center X) :
    nil_Nil3 (Subgroup.centralizer ({a} : Set X)) := by
  have hfp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center X with hZdef
  have hcardK : Nat.card (X ⧸ Z) * 3 = Nat.card X := by
    rw [← hZ3]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
  have hK0 : Nat.card (X ⧸ Z) ≠ 0 := Nat.card_pos.ne'
  have hKfac : (Nat.card (X ⧸ Z)).factorization 3 = 2 := by
    have h1 := hX3
    rw [← hcardK, Nat.factorization_mul hK0 (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three] at h1
    omega
  obtain ⟨-, hB, hC⟩ := i302 X hε
  set x : X ⧸ Z := (a : X ⧸ Z) with hx
  have hx3 : x ^ 3 = 1 := by rw [hx, ← QuotientGroup.mk_pow, ha3, QuotientGroup.mk_one]
  have hx1 : x ≠ 1 := fun h => haZ ((QuotientGroup.eq_one_iff a).1 h)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hzp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; simp)
  obtain ⟨P, hxP⟩ := hzp.exists_le_sylow
  have hxP' : x ∈ (P : Subgroup (X ⧸ Z)) := hxP (Subgroup.mem_zpowers x)
  obtain ⟨hPab, -⟩ := hB hKfac P
  obtain ⟨NK, hNKn, hNKc, hNKp⟩ := hC x hxo
    ⟨P, hxP', fun y hy => a_comm_of_elem hPab hxP' hy⟩
  set D := Subgroup.centralizer ({a} : Set X) with hD
  let f0 : ↥D →* X ⧸ Z := (QuotientGroup.mk' Z).comp D.subtype
  have hf0 : ∀ d, f0 d ∈ Subgroup.centralizer ({x} : Set (X ⧸ Z)) := by
    intro d
    have hd : (d : X) ∈ Subgroup.centralizer ({a} : Set X) := d.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (QuotientGroup.mk (d : X) : X ⧸ Z) * (QuotientGroup.mk a : X ⧸ Z) =
      (QuotientGroup.mk a : X ⧸ Z) * QuotientGroup.mk (d : X)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hd]
  let ψ : ↥D →* ↥(Subgroup.centralizer ({x} : Set (X ⧸ Z))) := f0.codRestrict _ hf0
  have hker : ∀ d ∈ ψ.ker, (d : X) ∈ Z := by
    intro d hd
    have h1 : ψ d = 1 := hd
    have h2 : f0 d = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff (d : X)).1 h2
  have hk1 : ∀ d ∈ ψ.ker, ∀ d' : ↥D, d * d' = d' * d := by
    intro d hd d'
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker d hd) d').symm
  have hk3 : ∀ d ∈ ψ.ker, d ^ 3 = 1 := by
    intro d hd
    have := pow_card_eq_one' (G := ↥Z) (x := (⟨d, hker d hd⟩ : ↥Z))
    rw [hZ3] at this
    have h2 : (d : X) ^ 3 = 1 := congrArg Subtype.val this
    exact Subtype.ext (by simpa using h2)
  have hNKo : ∀ n ∈ NK, Nat.Coprime 3 (orderOf n) := fun n hn =>
    hNKc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard NK hn)
  have hq : ∀ d : ↥D, ∃ k : ℕ, ψ d ^ (3 ^ k) ∈ NK := by
    intro d
    obtain ⟨k, hk⟩ := hNKp (QuotientGroup.mk (ψ d))
    refine ⟨k, (QuotientGroup.eq_one_iff _).1 ?_⟩
    rw [QuotientGroup.mk_pow]; exact hk
  obtain ⟨K'', hK1, hK2⟩ := nil_CE ψ hk1 hk3 NK hNKo hq
  refine ⟨K''.map D.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨d, -, rfl⟩; exact d.2
  · rintro _ ⟨d, hd, rfl⟩
    show Nat.Coprime 3 (orderOf (d : X))
    rw [Subgroup.orderOf_coe]; exact hK1 d hd
  · intro t ht
    obtain ⟨k, hk⟩ := hK2 ⟨t, ht⟩
    exact ⟨k, ⟨_, hk, by simp⟩⟩

theorem nil_fact3 {b : G} {L : Subgroup G} (hsyl : SylInfo b L) :
    (Nat.card (barOf 3 L)).factorization 3 = 3 := by
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥L))
  have hRc : Nat.card ((R : Subgroup ↥L).map L.subtype) = 3 ^ (Nat.card ↥L).factorization 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity]
  have h27 := (hsyl _ (Subgroup.map_subtype_le _) (R.isPGroup'.map L.subtype) hRc).1
  have hf : (Nat.card ↥L).factorization 3 = 3 := by
    have h' : (27 : ℕ) = 3 ^ (Nat.card ↥L).factorization 3 := h27.symm.trans hRc
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ 3 = 3 ^ _ by simpa using h')).symm
  have hN := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)
  have hnd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hN h
    omega
  have hz1 : Nat.card (↥L ⧸ GLAPPrimeCore 3 ↥L) ≠ 0 := Nat.card_pos.ne'
  have hz2 : Nat.card (GLAPPrimeCore 3 ↥L) ≠ 0 := Nat.card_pos.ne'
  rw [hmul, Nat.factorization_mul hz1 hz2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero] at hf
  exact hf

theorem nil_K1 (i302 : Input30_2) {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cb b) L)
    (hfus : FusData (barX 3 (Cb b) L) (barX 3 (Cb b) (Subgroup.zpowers b)))
    (hε : IsSL3Eps (barOf 3 L)) (hsyl : SylInfo b L)
    {a : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)} (haQ : a ∈ barX 3 (Cb b) L) (ha3 : a ^ 3 = 1)
    (haZ : a ∉ barX 3 (Cb b) (Subgroup.zpowers b)) :
    nil_Nil3 (barX 3 (Cb b) L ⊓
      Subgroup.centralizer ({a} : Set (↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)))) := by
  set Q := barX 3 (Cb b) L with hQ
  set Z := barX 3 (Cb b) (Subgroup.zpowers b) with hZ
  let e : barOf 3 L ≃* ↥Q := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  let φ : barOf 3 L →* (↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) := Q.subtype.comp e.toMonoidHom
  have hφi : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφQ : ∀ x, φ x ∈ Q := fun x => (e x).2
  have hsurj : ∀ y ∈ Q, ∃ x, φ x = y := fun y hy => ⟨e.symm ⟨y, hy⟩, by simp [φ]⟩
  have hcen : (Subgroup.center (barOf 3 L)).map φ = Z := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine (hfus.Zcenter _).2 ⟨hφQ z, fun q hq => ?_⟩
      obtain ⟨y, rfl⟩ := hsurj q hq
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y).symm]
    · intro hw
      obtain ⟨hwQ, hwc⟩ := (hfus.Zcenter w).1 hw
      obtain ⟨z, rfl⟩ := hsurj w hwQ
      refine ⟨z, Subgroup.mem_center_iff.2 fun y => hφi ?_, rfl⟩
      rw [map_mul, map_mul]
      exact (hwc _ (hφQ y)).symm
  have hZ3 : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    have := hfus.Zcard
    rw [← hcen, Subgroup.card_map_of_injective hφi] at this
    exact this
  obtain ⟨a₀, ha₀⟩ := hsurj a haQ
  have ha₀3 : a₀ ^ 3 = 1 := hφi (by rw [map_pow, ha₀, ha3, map_one])
  have ha₀Z : a₀ ∉ Subgroup.center (barOf 3 L) := by
    intro hz
    apply haZ
    rw [← hcen]
    exact ⟨a₀, hz, ha₀⟩
  have hnil := nil_A i302 hε (nil_fact3 hsyl) hZ3 ha₀3 ha₀Z
  refine nil_mono (nil_map φ hφi hnil) ?_
  rintro y ⟨hyQ, hyc⟩
  obtain ⟨y₀, rfl⟩ := hsurj y hyQ
  refine ⟨y₀, ?_, rfl⟩
  have hyc' : φ y₀ * a = a * φ y₀ := Subgroup.mem_centralizer_singleton_iff.1 hyc
  refine Subgroup.mem_centralizer_singleton_iff.2 (hφi ?_)
  rw [map_mul, map_mul, ha₀]
  exact hyc'

theorem nil_sup_decomp {H : Type*} [Group H] {A B : Subgroup H}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {z : H} (hz : z ∈ A ⊔ B) :
    ∃ x ∈ A, ∃ y ∈ B, z = x * y := by
  let S : Subgroup H :=
    { carrier := {z | ∃ x ∈ A, ∃ y ∈ B, z = x * y}
      mul_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        refine ⟨x * x', A.mul_mem hx hx', y * y', B.mul_mem hy hy', ?_⟩
        have := hc x' hx' y hy
        calc x * y * (x' * y') = x * (y * x') * y' := by group
          _ = x * (x' * y) * y' := by rw [← this]
          _ = x * x' * (y * y') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, A.inv_mem hx, y⁻¹, B.inv_mem hy, ?_⟩
        have := hc x hx y hy
        calc (x * y)⁻¹ = (y * x)⁻¹ := by rw [this]
          _ = x⁻¹ * y⁻¹ := by group }
  have hle : A ⊔ B ≤ S := sup_le (fun x hx => ⟨x, hx, 1, B.one_mem, by simp⟩)
    (fun y hy => ⟨1, A.one_mem, y, hy, by simp⟩)
  exact hle hz

theorem nil_pow_conj {H : Type*} [Group H] {g a y : H} (h : g * a * g⁻¹ = a * y)
    (hy : g * y = y * g) (k : ℕ) : g ^ k * a * (g ^ k)⁻¹ = a * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy' : g * y ^ k * g⁻¹ = y ^ k := by
      have : Commute g (y ^ k) := (show Commute g y from hy).pow_right k
      rw [this.eq]; group
    calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by group
      _ = g * (a * y ^ k) * g⁻¹ := by rw [ih]
      _ = (g * a * g⁻¹) * (g * y ^ k * g⁻¹) := by group
      _ = a * y ^ (k + 1) := by rw [h, hy', pow_succ', mul_assoc]

theorem nil_cube_comm {H : Type*} [Group H] {g a y : H} (h : g * a * g⁻¹ = a * y)
    (hy : g * y = y * g) (hy3 : y ^ 3 = 1) : g ^ 3 * a = a * g ^ 3 := by
  have := nil_pow_conj h hy 3
  rw [hy3, mul_one] at this
  exact mul_inv_eq_iff_eq_mul.1 this

theorem nil_K2 {H : Type*} [Group H] {Q₁ Q₂ Z : Subgroup H} (h₁ : FusData Q₁ Z)
    (h₂ : FusData Q₂ Z) (hc : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) {a c : H} (ha : a ∈ Q₁)
    (hcQ : c ∈ Q₂) (n₁ : nil_Nil3 (Q₁ ⊓ Subgroup.centralizer ({a} : Set H)))
    (n₂ : nil_Nil3 (Q₂ ⊓ Subgroup.centralizer ({c} : Set H))) :
    nil_Nil3 ((Q₁ ⊔ Q₂) ⊓ Subgroup.centralizer ({a * c} : Set H)) := by
  obtain ⟨N₁, hN₁T, hN₁o, hN₁p⟩ := n₁
  obtain ⟨N₂, hN₂T, hN₂o, hN₂p⟩ := n₂
  have hN₁Q : ∀ x ∈ N₁, x ∈ Q₁ ∧ x * a = a * x := fun x hx => by
    have := hN₁T hx
    exact ⟨this.1, Subgroup.mem_centralizer_singleton_iff.1 this.2⟩
  have hN₂Q : ∀ x ∈ N₂, x ∈ Q₂ ∧ x * c = c * x := fun x hx => by
    have := hN₂T hx
    exact ⟨this.1, Subgroup.mem_centralizer_singleton_iff.1 this.2⟩
  refine ⟨N₁ ⊔ N₂, ?_, ?_, ?_⟩
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hxQ, hxa⟩ := hN₁Q x hx
      refine ⟨Subgroup.mem_sup_left hxQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc x * (a * c) = (x * a) * c := by group
        _ = a * (x * c) := by rw [hxa]; group
        _ = a * (c * x) := by rw [hc x hxQ c hcQ]
        _ = a * c * x := by group
    · intro x hx
      obtain ⟨hxQ, hxc⟩ := hN₂Q x hx
      refine ⟨Subgroup.mem_sup_right hxQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc x * (a * c) = (x * a) * c := by group
        _ = (a * x) * c := by rw [(hc a ha x hxQ).symm]
        _ = a * (x * c) := by group
        _ = a * (c * x) := by rw [hxc]
        _ = a * c * x := by group
  · intro n hn
    obtain ⟨x, hx, y, hy, rfl⟩ := nil_sup_decomp (A := N₁) (B := N₂)
      (fun x hx y hy => hc x (hN₁Q x hx).1 y (hN₂Q y hy).1) hn
    have hcm : Commute x y := hc x (hN₁Q x hx).1 y (hN₂Q y hy).1
    exact ((hN₁o x hx).mul_right (hN₂o y hy)).coprime_dvd_right
      (hcm.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
  · rintro t ⟨htS, htc⟩
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := nil_sup_decomp hc htS
    have htc' : g₁ * g₂ * (a * c) = (a * c) * (g₁ * g₂) :=
      Subgroup.mem_centralizer_singleton_iff.1 htc
    have hg12 : g₁ * g₂ = g₂ * g₁ := hc g₁ hg₁ g₂ hg₂
    have e1 : g₂ * a = a * g₂ := (hc a ha g₂ hg₂).symm
    have hc'Q : g₂ * c * g₂⁻¹ ∈ Q₂ := Q₂.mul_mem (Q₂.mul_mem hg₂ hcQ) (Q₂.inv_mem hg₂)
    have e2 : g₁ * (g₂ * c * g₂⁻¹) = (g₂ * c * g₂⁻¹) * g₁ := hc g₁ hg₁ _ hc'Q
    have h0 : a * c = g₁ * g₂ * (a * c) * (g₁ * g₂)⁻¹ := by rw [htc']; group
    have hc'g : (g₂ * c * g₂⁻¹) * g₁⁻¹ = g₁⁻¹ * (g₂ * c * g₂⁻¹) :=
      (show Commute (g₂ * c * g₂⁻¹) g₁ from e2.symm).inv_right.eq
    have hmain : g₁ * a * g₁⁻¹ * (g₂ * c * g₂⁻¹) = a * c := by
      calc g₁ * a * g₁⁻¹ * (g₂ * c * g₂⁻¹) = g₁ * a * (g₁⁻¹ * (g₂ * c * g₂⁻¹)) := by group
        _ = g₁ * a * ((g₂ * c * g₂⁻¹) * g₁⁻¹) := by rw [hc'g]
        _ = g₁ * (a * g₂) * c * g₂⁻¹ * g₁⁻¹ := by group
        _ = g₁ * (g₂ * a) * c * g₂⁻¹ * g₁⁻¹ := by rw [e1]
        _ = g₁ * g₂ * (a * c) * (g₁ * g₂)⁻¹ := by group
        _ = a * c := h0.symm
    have hXc : g₁ * a * g₁⁻¹ = a * (c * (g₂ * c * g₂⁻¹)⁻¹) := by
      calc g₁ * a * g₁⁻¹ = (g₁ * a * g₁⁻¹ * (g₂ * c * g₂⁻¹)) * (g₂ * c * g₂⁻¹)⁻¹ := by group
        _ = a * c * (g₂ * c * g₂⁻¹)⁻¹ := by rw [hmain]
        _ = a * (c * (g₂ * c * g₂⁻¹)⁻¹) := by group
    set y : H := c * (g₂ * c * g₂⁻¹)⁻¹ with hydef
    have hyQ₂ : y ∈ Q₂ := Q₂.mul_mem hcQ (Q₂.inv_mem hc'Q)
    have hyQ₁ : y ∈ Q₁ := by
      have : y = a⁻¹ * (g₁ * a * g₁⁻¹) := by rw [hXc]; group
      rw [this]
      exact Q₁.mul_mem (Q₁.inv_mem ha) (Q₁.mul_mem (Q₁.mul_mem hg₁ ha) (Q₁.inv_mem hg₁))
    have hyZ : y ∈ Z := (h₁.Zcenter y).2 ⟨hyQ₁, fun q hq => (hc q hq y hyQ₂).symm⟩
    have hy1 : ∀ q ∈ Q₁, y * q = q * y := ((h₁.Zcenter y).1 hyZ).2
    have hy2 : ∀ q ∈ Q₂, y * q = q * y := ((h₂.Zcenter y).1 hyZ).2
    have hy3 : y ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥Z) (x := (⟨y, hyZ⟩ : ↥Z))
      rw [h₁.Zcard] at this
      exact congrArg Subtype.val this
    have hA : g₁ * a * g₁⁻¹ = a * y := hXc
    have hgy1 : g₁ * y = y * g₁ := (hy1 g₁ hg₁).symm
    have hcube1 : g₁ ^ 3 * a = a * g₁ ^ 3 := nil_cube_comm hA hgy1 hy3
    have hB : g₂ * c * g₂⁻¹ = c * y⁻¹ := by
      have h1 : g₂ * c * g₂⁻¹ = y⁻¹ * c := by rw [hydef]; group
      have h2 : y⁻¹ * c = c * y⁻¹ := (show Commute y c from hy2 c hcQ).inv_left.eq
      rw [h1, h2]
    have hgy2 : g₂ * y⁻¹ = y⁻¹ * g₂ :=
      (show Commute g₂ y from (hy2 g₂ hg₂).symm).inv_right.eq
    have hy3' : (y⁻¹) ^ 3 = 1 := by rw [inv_pow, hy3, inv_one]
    have hcube2 : g₂ ^ 3 * c = c * g₂ ^ 3 := nil_cube_comm hB hgy2 hy3'
    obtain ⟨k₁, hk₁⟩ := hN₁p (g₁ ^ 3)
      ⟨Q₁.pow_mem hg₁ 3, Subgroup.mem_centralizer_singleton_iff.2 hcube1⟩
    obtain ⟨k₂, hk₂⟩ := hN₂p (g₂ ^ 3)
      ⟨Q₂.pow_mem hg₂ 3, Subgroup.mem_centralizer_singleton_iff.2 hcube2⟩
    refine ⟨k₁ + k₂ + 1, ?_⟩
    have hp1 : (g₁ ^ 3) ^ (3 ^ (k₁ + k₂)) ∈ N₁ := by
      rw [pow_add, pow_mul]; exact N₁.pow_mem hk₁ _
    have hp2 : (g₂ ^ 3) ^ (3 ^ (k₁ + k₂)) ∈ N₂ := by
      rw [add_comm k₁ k₂, pow_add, pow_mul]; exact N₂.pow_mem hk₂ _
    have hcm : Commute g₁ g₂ := hg12
    have : (g₁ * g₂) ^ (3 ^ (k₁ + k₂ + 1)) =
        (g₁ ^ 3) ^ (3 ^ (k₁ + k₂)) * (g₂ ^ 3) ^ (3 ^ (k₁ + k₂)) := by
      rw [pow_succ', pow_mul, hcm.mul_pow, (hcm.pow_pow 3 3).mul_pow]
    rw [this]
    exact Subgroup.mul_mem_sup hp1 hp2

theorem nil_orderOf_conj {Γ : Type*} [Group Γ] (g h : Γ) : orderOf (g * h * g⁻¹) = orderOf h :=
  (SemiconjBy.orderOf_eq g (show SemiconjBy g h (g * h * g⁻¹) by
    simp [SemiconjBy, mul_assoc])).symm

theorem nil_coprime_of_pow {Γ : Type*} [Group Γ] {n : Γ} {r : ℕ} (hr : Nat.Coprime 3 r)
    (h : Nat.Coprime 3 (orderOf (n ^ r))) : Nat.Coprime 3 (orderOf n) := by
  have : orderOf n ∣ r * orderOf (n ^ r) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]; exact pow_orderOf_eq_one _
  exact (hr.mul_right h).coprime_dvd_right this

theorem nil_pc_coprime {C : Subgroup G} {x : ↥C} (hx : x ∈ GLAPPrimeCore 3 ↥C) :
    Nat.Coprime 3 (orderOf x) :=
  (coprime_card_gLAPPrimeCore_aux 3 ↥C).coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hx)

theorem nil_crit {C U : Subgroup G} (hUC : U ≤ C) (hN : nil_Nil3 (barX 3 C U)) :
    U ≤ oPrimePOf 3 U := by
  obtain ⟨N', hN'T, hN'o, hN'p⟩ := hN
  let f' : ↥U →* ↥C ⧸ GLAPPrimeCore 3 ↥C :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).comp (Subgroup.inclusion hUC)
  have hf'T : ∀ x : ↥U, f' x ∈ barX 3 C U := fun x =>
    ⟨⟨x, hUC x.2⟩, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩
  have hN'mem : ∀ y ∈ barX 3 C U, Nat.Coprime 3 (orderOf y) → y ∈ N' := by
    intro y hy hyo
    obtain ⟨k, hk⟩ := hN'p y hy
    exact nil_mem_of_pow hyo hk
  let Ñ : Subgroup ↥U := N'.comap f'
  have hnorm : Ñ.Normal := ⟨fun n hn x => by
    have hn' : f' n ∈ N' := hn
    show f' (x * n * x⁻¹) ∈ N'
    rw [map_mul, map_mul, map_inv]
    have hy : f' x * f' n * (f' x)⁻¹ ∈ barX 3 C U :=
      (barX 3 C U).mul_mem ((barX 3 C U).mul_mem (hf'T x) (hN'T hn')) ((barX 3 C U).inv_mem (hf'T x))
    refine hN'mem _ hy ?_
    rw [nil_orderOf_conj]
    exact hN'o _ hn'⟩
  have hord : ∀ n ∈ Ñ, Nat.Coprime 3 (orderOf n) := by
    intro n hn
    have hn' : f' n ∈ N' := hn
    have hr := hN'o _ hn'
    refine nil_coprime_of_pow hr ?_
    have h1 : f' (n ^ orderOf (f' n)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    have h2 : Subgroup.inclusion hUC (n ^ orderOf (f' n)) ∈ GLAPPrimeCore 3 ↥C :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 := nil_pc_coprime h2
    rwa [orderOf_injective (Subgroup.inclusion hUC) (Subgroup.inclusion_injective hUC)] at h3
  have hle : Ñ ≤ GLAPPrimeCore 3 ↥U := by
    have : Finite Ñ := inferInstance
    exact le_sSup ⟨hnorm, nil_coprime_card Ñ hord⟩
  refine g2_crit le_rfl ?_ ?_
  · rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top
  · intro g hg
    obtain ⟨k, hk⟩ := hN'p (f' ⟨g, hg⟩) (hf'T ⟨g, hg⟩)
    refine ⟨k, ?_⟩
    have hmem : (⟨g, hg⟩ : ↥U) ^ (3 ^ k) ∈ GLAPPrimeCore 3 ↥U := hle (by
      show f' ((⟨g, hg⟩ : ↥U) ^ (3 ^ k)) ∈ N'
      rw [map_pow]; exact hk)
    exact ⟨_, hmem, by simp⟩

omit [Finite G] in
theorem nil_barX_sup {N A B : Subgroup G} (hA : A ≤ N) (hB : B ≤ N) :
    barX 3 N (A ⊔ B) = barX 3 N A ⊔ barX 3 N B := by
  simp only [barX, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem nil_sn {b : G} {L₁ L₂ : Subgroup G} (hL₁ : GLAPComponent 3 (Cb b) L₁)
    (hL₂ : GLAPComponent 3 (Cb b) L₂) (x : G) :
    IsSubnormal ((L₁ ⊔ L₂) ⊓ Subgroup.centralizer ({x} : Set G))
      (Cb b ⊓ Subgroup.centralizer ({x} : Set G)) := by
  set E := GLAPLayer 3 (Cb b) with hE
  have hEC : E ≤ Cb b := bf_layer_le _
  have hCE : Cb b ≤ Subgroup.normalizer (E : Set G) := fun g hg =>
    bf_mem_normalizer_layer (Subgroup.le_normalizer hg)
  have hAE : L₁ ⊔ L₂ ≤ E := sup_le (le_sSup hL₁) (le_sSup hL₂)
  have hEN : ∀ {L : Subgroup G}, GLAPComponent 3 (Cb b) L →
      E ≤ Subgroup.normalizer (L : Set G) := by
    intro L hL
    refine sSup_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]; exact Subgroup.le_normalizer
    · exact q_le_normalizer_of_ne hL' hL h
  have hEA : E ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := by
    intro g hg
    have h1 := mem_normalizer_iff_gLBConj_eq.1 (hEN hL₁ hg)
    have h2 := mem_normalizer_iff_gLBConj_eq.1 (hEN hL₂ hg)
    exact a_mem_normalizer_of_eq (by rw [a_gLBConj_sup, h1, h2])
  have hUE : (L₁ ⊔ L₂) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      E ⊓ Subgroup.centralizer ({x} : Set G) := inf_le_inf_right _ hAE
  have hEW : E ⊓ Subgroup.centralizer ({x} : Set G) ≤ Cb b ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ hEC
  have hn1 : (((L₁ ⊔ L₂) ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (E ⊓ Subgroup.centralizer ({x} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUE]
    intro g hg
    exact bf_inf_normalizer (hEA hg.1) (Subgroup.le_normalizer hg.2)
  have hn2 : ((E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (Cb b ⊓ Subgroup.centralizer ({x} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEW]
    intro g hg
    exact bf_inf_normalizer (hCE hg.1) (Subgroup.le_normalizer hg.2)
  exact IsSubnormal.step hUE hn1 (IsSubnormal.step hEW hn2 (IsSubnormal.refl _))

theorem nil_cent (i302 : Input30_2) {B : Subgroup G} {b : G} {L₁ L₂ L₃ R R₁ R₂ R₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) (hSy : SylData B b L₁ L₂ L₃ R R₁ R₂ R₃) {u v : G} (hu : u ∈ R₁)
    (hv : v ∈ R₂) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hnu : u ∉ Subgroup.zpowers b)
    (hnv : v ∉ Subgroup.zpowers b) :
    (R₁ ⊔ R₂) ⊓ Cb (u * v) ≤ oPrimePOf 3 (Cb b ⊓ Cb (u * v)) := by
  have hT := hR.tri
  have hL₁ := hT.comp₁
  have hL₂ := hT.comp₂
  have hR₁L : R₁ ≤ L₁ := by rw [hSy.h1]; exact inf_le_right
  have hR₂L : R₂ ≤ L₂ := by rw [hSy.h2]; exact inf_le_right
  have hu1 : u ∈ L₁ := hR₁L hu
  have hv1 : v ∈ L₂ := hR₂L hv
  have hu' : u ∈ Cb b := hL₁.1 hu1
  have hv' : v ∈ Cb b := hL₂.1 hv1
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hb3 : b ^ (3 ^ 1) = 1 := by simpa using hT.elemB.2 b hT.mem
  have hxC : u * v ∈ Cb b := (Cb b).mul_mem hu' hv'
  have hmkpow : ∀ {g : G} (hg : g ∈ Cb b), g ^ 3 = 1 → mkX (Cb b) g hg ^ 3 = 1 := by
    intro g hg h3
    have : (⟨g, hg⟩ : ↥(Cb b)) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    unfold mkX
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hub : mkX (Cb b) u hu' ∈ barX 3 (Cb b) L₁ :=
    (a_mem_barX_iff 3 (Cb b) L₁ _).2 ⟨⟨u, hu'⟩, hu1, rfl⟩
  have hvb : mkX (Cb b) v hv' ∈ barX 3 (Cb b) L₂ :=
    (a_mem_barX_iff 3 (Cb b) L₂ _).2 ⟨⟨v, hv'⟩, hv1, rfl⟩
  have hubZ : mkX (Cb b) u hu' ∉ barX 3 (Cb b) (Subgroup.zpowers b) := fun h =>
    hnu (q_mem_zpowers_of_bar hbC hb3 hu' (k := 1) (by simpa using hu3)
      (Subgroup.mem_centralizer_singleton_iff.1 hu') h)
  have hvbZ : mkX (Cb b) v hv' ∉ barX 3 (Cb b) (Subgroup.zpowers b) := fun h =>
    hnv (q_mem_zpowers_of_bar hbC hb3 hv' (k := 1) (by simpa using hv3)
      (Subgroup.mem_centralizer_singleton_iff.1 hv') h)
  have hcomm : ∀ x ∈ barX 3 (Cb b) L₁, ∀ y ∈ barX 3 (Cb b) L₂, x * y = y * x := by
    intro x hx y hy
    have h1 := barX_le_centralizer (p := 3) (C := Cb b) (S := L₁) (T := L₂)
      (fun s hs t ht _ _ => by
        have hcm := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hL₁ hL₂ hT.ne₁₂
        apply hcm
        have := Subgroup.commutator_mem_commutator hs ht
        rwa [commutatorElement_def] at this) hx
    exact ((Subgroup.mem_centralizer_iff.1 h1) y hy).symm
  have n₁ := nil_K1 i302 hL₁ hR.fus₁ hR.eps₁ hR.syl₁ hub (hmkpow hu' hu3) hubZ
  have n₂ := nil_K1 i302 hL₂ hR.fus₂ hR.eps₂ hR.syl₂ hvb (hmkpow hv' hv3) hvbZ
  have hK2 := nil_K2 hR.fus₁ hR.fus₂ hcomm hub hvb n₁ n₂
  have hUC : (L₁ ⊔ L₂) ⊓ Cb (u * v) ≤ Cb b := inf_le_left.trans (sup_le hL₁.1 hL₂.1)
  have hbar : barX 3 (Cb b) ((L₁ ⊔ L₂) ⊓ Cb (u * v)) ≤
      (barX 3 (Cb b) L₁ ⊔ barX 3 (Cb b) L₂) ⊓
        Subgroup.centralizer ({mkX (Cb b) u hu' * mkX (Cb b) v hv'} :
          Set (↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b))) := by
    rintro _ ⟨⟨g, hgC⟩, hg, rfl⟩
    have hg' : g ∈ (L₁ ⊔ L₂) ⊓ Cb (u * v) := (Subgroup.mem_subgroupOf).1 hg
    refine ⟨?_, ?_⟩
    · rw [← nil_barX_sup hL₁.1 hL₂.1]
      exact ⟨⟨g, hgC⟩, (Subgroup.mem_subgroupOf).2 hg'.1, rfl⟩
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h2 : g * (u * v) = (u * v) * g := Subgroup.mem_centralizer_singleton_iff.1 hg'.2
      have : (⟨g, hgC⟩ : ↥(Cb b)) * ⟨u * v, hxC⟩ = ⟨u * v, hxC⟩ * ⟨g, hgC⟩ := Subtype.ext h2
      exact congrArg (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b))) this
  have hcrit := nil_crit hUC (nil_mono hK2 hbar)
  have hSU : (R₁ ⊔ R₂) ⊓ Cb (u * v) ≤ (L₁ ⊔ L₂) ⊓ Cb (u * v) :=
    inf_le_inf_right _ (sup_le_sup hR₁L hR₂L)
  exact hSU.trans (hcrit.trans (o_le_of_subnormal (nil_sn hL₁ hL₂ (u * v))))

end NilSec

section ExtqSec

omit [Finite G] in
theorem extq_comm_prod {R₁ R₂ : Subgroup G} (hc : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a)
    {a a' b b' : G} (ha : a ∈ R₁) (ha' : a' ∈ R₁) (hb : b ∈ R₂) (hb' : b' ∈ R₂) :
    a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹ =
      (a * a' * a⁻¹ * a'⁻¹) * (b * b' * b⁻¹ * b'⁻¹) := by
  have hcomm : ∀ (m : R₁) (n : R₂), Commute (R₁.subtype m) (R₂.subtype n) :=
    fun m n => hc m m.2 n n.2
  let φ := MonoidHom.noncommCoprod R₁.subtype R₂.subtype hcomm
  have h := congrArg φ (show ((⟨a, ha⟩ : R₁), (⟨b, hb⟩ : R₂)) * (⟨a', ha'⟩, ⟨b', hb'⟩) *
      ((⟨a, ha⟩ : R₁), (⟨b, hb⟩ : R₂))⁻¹ * ((⟨a', ha'⟩ : R₁), (⟨b', hb'⟩ : R₂))⁻¹ =
      ((⟨a * a' * a⁻¹ * a'⁻¹, R₁.mul_mem (R₁.mul_mem (R₁.mul_mem ha ha') (R₁.inv_mem ha))
        (R₁.inv_mem ha')⟩ : R₁),
       (⟨b * b' * b⁻¹ * b'⁻¹, R₂.mul_mem (R₂.mul_mem (R₂.mul_mem hb hb') (R₂.inv_mem hb))
        (R₂.inv_mem hb')⟩ : R₂)) from Prod.ext rfl rfl)
  simpa only [φ, MonoidHom.noncommCoprod_apply, map_mul, map_inv, Subgroup.coe_subtype] using h

omit [Finite G] in
theorem extq_mem_sup {R₁ R₂ : Subgroup G} (hc : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a) {x : G}
    (hx : x ∈ R₁ ⊔ R₂) : ∃ a ∈ R₁, ∃ b ∈ R₂, a * b = x := by
  have hconj : ∀ g ∈ R₁, ∀ x ∈ R₂, g * x * g⁻¹ = x := fun g hg x hx => by
    rw [hc g hg x hx, mul_assoc, mul_inv_cancel, mul_one]
  have hLE : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj g hg h hh]; exact hh
    · intro hh
      have e := hconj g⁻¹ (R₁.inv_mem hg) _ hh
      simp only [inv_inv] at e
      have h2 : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = _ := e
      rw [h2]; exact hh
  have := Subgroup.coe_mul_of_left_le_normalizer_right R₁ R₂ hLE
  rw [← SetLike.mem_coe, this] at hx
  exact hx

omit [Finite G] in
theorem extq_comm_of {x y : G} (h : x * y * x⁻¹ * y⁻¹ = 1) : x * y = y * x := by
  have := mul_inv_eq_one.1 h
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [this]

omit [Finite G] in
theorem extq_inv_comm {x y c : G} (hc : c = x * y * x⁻¹ * y⁻¹) (hcx : c * x = x * c) :
    x⁻¹ * y * x * y⁻¹ = c⁻¹ := by
  have e : x⁻¹ * y * x * y⁻¹ = x⁻¹ * c⁻¹ * x := by rw [hc]; group
  have h2 : c⁻¹ * x = x * c⁻¹ := (Commute.inv_left (show Commute c x from hcx)).eq
  rw [e, mul_assoc, h2, inv_mul_cancel_left]

omit [Finite G] in
theorem extq_mem_normalizer {P A Z : Subgroup G}
    (hcom : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z) (hZA : Z ≤ A) (hAP : A ≤ P) {g : G}
    (hg : g ∈ P) : g ∈ Subgroup.normalizer (A : Set G) := by
  have hfwd : ∀ g ∈ P, ∀ h ∈ A, g * h * g⁻¹ ∈ A := by
    intro g hg h hh
    have : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
    rw [this]
    exact A.mul_mem (hZA (hcom g hg h (hAP hh))) hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hfwd g hg h
  · intro hh
    have := hfwd g⁻¹ (P.inv_mem hg) _ hh
    simpa [mul_assoc] using this

theorem extq_card_sup_le {N H : Subgroup G} (hH : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ H) ≤ Nat.card N * Nat.card H := by
  have hs := Subgroup.coe_mul_of_right_le_normalizer_left N H hH
  let f : N × H → ↥(N ⊔ H) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    intro x
    have hx := x.2
    rw [← SetLike.mem_coe, hs] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card ↥(N ⊔ H) ≤ Nat.card (N × H) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card N * Nat.card H := Nat.card_prod _ _

theorem extq_comm_mem_ZR {R : Subgroup G} (h27 : Nat.card R = 27)
    (hnab : ¬ ∀ a ∈ R, ∀ c ∈ R, a * c = c * a) {a c : G} (ha : a ∈ R) (hc : c ∈ R) :
    a * c * a⁻¹ * c⁻¹ ∈ ZR R := by
  have hZ := rk5_card_ZR h27 hnab
  have hcenter : Nat.card (Subgroup.center ↥R) = 3 := by
    rw [← hZ]; exact (Subgroup.card_map_of_injective R.subtype_injective).symm
  have hq : Nat.card (↥R ⧸ Subgroup.center ↥R) = 3 ^ 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥R)
    rw [h27, hcenter] at this; omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcom := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hq
  have h1 : (⟨a, ha⟩ : R) * ⟨c, hc⟩ * (⟨a, ha⟩ : R)⁻¹ * (⟨c, hc⟩ : R)⁻¹ ∈
      Subgroup.center R := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hcm := hcom.is_comm.comm ((⟨a, ha⟩ : R) : ↥R ⧸ Subgroup.center ↥R)
      ((⟨c, hc⟩ : R) : ↥R ⧸ Subgroup.center ↥R)
    rw [hcm]; group
  refine rk5_mem_ZR_iff.2 ⟨R.mul_mem (R.mul_mem (R.mul_mem ha hc) (R.inv_mem ha)) (R.inv_mem hc),
    fun r hr => ?_⟩
  have := congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨r, hr⟩)
  simpa using this.symm

theorem ext_Q {R₁ R₂ : Subgroup G} {z : G} (hc : ∀ a ∈ R₁, ∀ c ∈ R₂, a * c = c * a)
    (hR₁ : Nat.card R₁ = 27 ∧ (¬ ∀ a ∈ R₁, ∀ c ∈ R₁, a * c = c * a) ∧ ∀ a ∈ R₁, a ^ 3 = 1)
    (hR₂ : Nat.card R₂ = 27 ∧ (¬ ∀ a ∈ R₂, ∀ c ∈ R₂, a * c = c * a) ∧ ∀ a ∈ R₂, a ^ 3 = 1)
    (hZ₁ : ZR R₁ = Subgroup.zpowers z) (hZ₂ : ZR R₂ = Subgroup.zpowers z) {u v : G} (hu : u ∈ R₁)
    (hv : v ∈ R₂) (hnu : u ∉ Subgroup.zpowers z) (hnv : v ∉ Subgroup.zpowers z) :
    ∃ Q : Subgroup G, Q ≤ (R₁ ⊔ R₂) ⊓ Subgroup.centralizer ({u * v} : Set G) ∧
      (Q.subgroupOf ((R₁ ⊔ R₂) ⊓ Subgroup.centralizer ({u * v} : Set G))).Normal ∧
      Nat.card Q = 27 ∧ (¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) ∧ (∀ a ∈ Q, a ^ 3 = 1) ∧
      ZR Q = Subgroup.zpowers z := by
  obtain ⟨h27₁, hnab₁, hexp₁⟩ := hR₁
  obtain ⟨h27₂, hnab₂, hexp₂⟩ := hR₂
  have hZ3 : Nat.card (ZR R₁) = 3 := rk5_card_ZR h27₁ hnab₁
  have hzmem₁ : z ∈ ZR R₁ := hZ₁ ▸ Subgroup.mem_zpowers z
  have hzmem₂ : z ∈ ZR R₂ := hZ₂ ▸ Subgroup.mem_zpowers z
  have hzc₁ : ∀ r ∈ R₁, z * r = r * z := (rk5_mem_ZR_iff.1 hzmem₁).2
  have hzc₂ : ∀ r ∈ R₂, z * r = r * z := (rk5_mem_ZR_iff.1 hzmem₂).2
  have hzR₁ : z ∈ R₁ := (rk5_mem_ZR_iff.1 hzmem₁).1
  have hzR₂ : z ∈ R₂ := (rk5_mem_ZR_iff.1 hzmem₂).1
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [← hZ₁]; exact hZ3
  have hord : orderOf z = 3 := by rw [← Nat.card_zpowers]; exact hzcard
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z; rwa [hord] at this
  have hz1 : z ≠ 1 := by intro h; rw [h, orderOf_one] at hord; omega
  have hZel : ∀ g ∈ Subgroup.zpowers z, g ≠ 1 → g = z ∨ g = z⁻¹ := by
    intro g hg hg1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hk : z ^ k = z ^ (k % 3) := by
      have := zpow_mod_orderOf z k
      rw [hord] at this
      simpa using this.symm
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · rw [hk, h] at hg1; simp at hg1
    · left; rw [hk, h]; simp
    · right; rw [hk, h]
      refine eq_inv_of_mul_eq_one_left ?_
      have : z ^ (2 : ℤ) * z = z ^ 3 := by
        rw [← zpow_natCast, ← zpow_add_one]; norm_num
      rw [this, hz3]
  set P := R₁ ⊔ R₂ with hP
  have hR₁P : R₁ ≤ P := le_sup_left
  have hR₂P : R₂ ≤ P := le_sup_right
  have hPcom : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := extq_mem_sup hc hx
    obtain ⟨a', ha', b', hb', rfl⟩ := extq_mem_sup hc hy
    rw [extq_comm_prod hc ha ha' hb hb']
    have h1 := extq_comm_mem_ZR h27₁ hnab₁ ha ha'
    have h2 := extq_comm_mem_ZR h27₂ hnab₂ hb hb'
    rw [hZ₁] at h1
    rw [hZ₂] at h2
    exact Subgroup.mul_mem _ h1 h2
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := extq_mem_sup hc hx
    rw [Commute.mul_pow (show Commute a b from hc a ha b hb), hexp₁ a ha, hexp₂ b hb, one_mul]
  have hzP : ∀ x ∈ P, z * x = x * z := by
    have : P ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact hzc₁ x hx
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact hzc₂ x hx
    intro x hx
    have := Subgroup.mem_centralizer_iff.1 (this hx) z (Set.mem_singleton z)
    exact this
  have hzPm : z ∈ P := hR₁P hzR₁
  obtain ⟨s, hsR, hsu⟩ : ∃ s ∈ R₁, u * s ≠ s * u := by
    by_contra hcon
    push Not at hcon
    apply hnu
    rw [← hZ₁]
    exact rk5_mem_ZR_iff.2 ⟨hu, hcon⟩
  obtain ⟨r, hrR, hrv⟩ : ∃ r ∈ R₂, v * r ≠ r * v := by
    by_contra hcon
    push Not at hcon
    apply hnv
    rw [← hZ₂]
    exact rk5_mem_ZR_iff.2 ⟨hv, hcon⟩
  have hc1 : s * u * s⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
    have := extq_comm_mem_ZR h27₁ hnab₁ hsR hu
    rwa [hZ₁] at this
  have hc2 : r * v * r⁻¹ * v⁻¹ ∈ Subgroup.zpowers z := by
    have := extq_comm_mem_ZR h27₂ hnab₂ hrR hv
    rwa [hZ₂] at this
  have hc1ne : s * u * s⁻¹ * u⁻¹ ≠ 1 := fun h => hsu (extq_comm_of h).symm
  have hc2ne : r * v * r⁻¹ * v⁻¹ ≠ 1 := fun h => hrv (extq_comm_of h).symm
  have hc2cent : (r * v * r⁻¹ * v⁻¹) * r = r * (r * v * r⁻¹ * v⁻¹) := by
    have : r * v * r⁻¹ * v⁻¹ ∈ ZR R₂ := by rw [hZ₂]; exact hc2
    exact (rk5_mem_ZR_iff.1 this).2 r hrR
  obtain ⟨r', hr'R, hr'⟩ : ∃ r' ∈ R₂, r' * v * r'⁻¹ * v⁻¹ = (s * u * s⁻¹ * u⁻¹)⁻¹ := by
    by_cases hh : r * v * r⁻¹ * v⁻¹ = (s * u * s⁻¹ * u⁻¹)⁻¹
    · exact ⟨r, hrR, hh⟩
    · refine ⟨r⁻¹, R₂.inv_mem hrR, ?_⟩
      have e : r⁻¹ * v * r⁻¹⁻¹ * v⁻¹ = (r * v * r⁻¹ * v⁻¹)⁻¹ := by
        rw [inv_inv]; exact extq_inv_comm rfl hc2cent
      rw [e]
      have h1 := hZel _ hc2 hc2ne
      have h2 := hZel _ (Subgroup.inv_mem _ hc1) (inv_ne_one.2 hc1ne)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hh
      · simp [h1, h2]
      · simp [h1, h2]
      · exact absurd (h1.trans h2.symm) hh
  have hr'P : r' ∈ P := hR₂P hr'R
  have hsP : s ∈ P := hR₁P hsR
  have huP : u ∈ P := hR₁P hu
  have hvP : v ∈ P := hR₂P hv
  set w := s * r' with hw
  have hwP : w ∈ P := P.mul_mem hsP hr'P
  have hw3 : w ^ 3 = 1 := hP3 w hwP
  have hwuv : w * (u * v) = (u * v) * w := by
    apply extq_comm_of
    rw [hw, extq_comm_prod hc hsR hu hr'R hv, hr', mul_inv_cancel]
  have hwu : w * u ≠ u * w := by
    intro h
    have h1 : r' * u = u * r' := (hc u hu r' hr'R).symm
    have h2 : s * u * r' = u * s * r' := by
      calc s * u * r' = s * (u * r') := mul_assoc _ _ _
        _ = s * (r' * u) := by rw [h1]
        _ = s * r' * u := (mul_assoc _ _ _).symm
        _ = u * (s * r') := h
        _ = u * s * r' := (mul_assoc _ _ _).symm
    exact hsu (mul_right_cancel h2).symm
  have hzu : z * u = u * z := hzc₁ u hu
  have hwz : w ∉ Subgroup.zpowers z := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hwu
    rw [← hk]
    exact (((Commute.zpow_left (show Commute z u from hzu) k)).eq)
  have hu3 : u ^ 3 = 1 := hexp₁ u hu
  have hu1 : u ≠ 1 := fun h => hnu (h ▸ Subgroup.one_mem _)
  set A := Subgroup.zpowers z ⊔ Subgroup.zpowers w with hA
  set Q := A ⊔ Subgroup.zpowers u with hQ
  have hAcard : Nat.card A = 9 := by
    have := card_sup_zpowers_of_pow_three_eq_one (H := Subgroup.zpowers z) hw3 hwz
      (fun h hh => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
        rw [← hk]
        exact ((Commute.zpow_left (show Commute z w from (hzP w hwP)) k)).eq)
    rw [hA, this, hzcard]
  have hzA : Subgroup.zpowers z ≤ A := le_sup_left
  have hzQ : Subgroup.zpowers z ≤ Q := hzA.trans le_sup_left
  have hAQ : A ≤ Q := le_sup_left
  have hAP : A ≤ P := sup_le ((Subgroup.zpowers_le).2 hzPm) ((Subgroup.zpowers_le).2 hwP)
  have hQP : Q ≤ P := sup_le hAP ((Subgroup.zpowers_le).2 huP)
  have huQ : u ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hwQ : w ∈ Q := hAQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have hzQm : z ∈ Q := hzQ (Subgroup.mem_zpowers z)
  have huA : u ∉ A := by
    intro h
    have : A ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact (hzP _ hwP).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; rfl
    have := Subgroup.mem_centralizer_iff.1 (this h) w (Set.mem_singleton w)
    exact hwu this
  have hQcard : Nat.card Q = 27 := by
    have hle : Nat.card Q ≤ 27 := by
      have h1 := extq_card_sup_le (N := A) (H := Subgroup.zpowers u)
        (fun g hg => by
          have hgP : g ∈ P := by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
            exact P.zpow_mem huP k
          exact extq_mem_normalizer hPcom (hzA) hAP hgP)
      have h2 : Nat.card (Subgroup.zpowers u) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1]
      rw [hAcard, h2] at h1
      exact h1
    have hdvd : 9 ∣ Nat.card Q := hAcard ▸ Subgroup.card_dvd_of_le hAQ
    have hgt : 9 < Nat.card Q := by
      have hle' : Nat.card A ≤ Nat.card Q := Subgroup.card_le_of_le hAQ
      rcases hle'.lt_or_eq with h | h
      · omega
      · exfalso
        exact huA (Subgroup.eq_of_le_of_card_ge hAQ h.ge ▸ huQ)
    have hpg : IsPGroup 3 Q := fun g => ⟨1, by
      simpa using Subtype.ext (by simpa using hP3 g (hQP g.2) : (g : G) ^ 3 = 1)⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
    have hn4 : n < 4 := by
      by_contra hcon
      have : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
      omega
    interval_cases n <;> omega
  have hQnab : ¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a := fun h => hwu (h w hwQ u huQ)
  have hQexp : ∀ a ∈ Q, a ^ 3 = 1 := fun a ha => hP3 a (hQP ha)
  have hQC : Q ≤ P ⊓ Subgroup.centralizer ({u * v} : Set G) := by
    refine le_inf hQP (sup_le (sup_le ?_ ?_) ?_)
    · refine (Subgroup.zpowers_le).2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact (hzP _ (P.mul_mem huP hvP)).symm
    · refine (Subgroup.zpowers_le).2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh; exact hwuv.symm
    · refine (Subgroup.zpowers_le).2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh
      calc u * v * u = u * (v * u) := mul_assoc _ _ _
        _ = u * (u * v) := by rw [hc u hu v hv]
        _ = _ := rfl
  refine ⟨Q, hQC, ?_, hQcard, hQnab, hQexp, ?_⟩
  · constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgP : (g : G) ∈ P := (inf_le_left : P ⊓ Subgroup.centralizer ({u * v} : Set G) ≤ P) g.2
    have hnorm := extq_mem_normalizer hPcom hzQ hQP hgP
    have := (Subgroup.mem_normalizer_iff.1 hnorm n).1 hn
    simpa using this
  · have hZQ3 := rk5_card_ZR hQcard hQnab
    have hle : Subgroup.zpowers z ≤ ZR Q :=
      (Subgroup.zpowers_le).2 (rk5_mem_ZR_iff.2 ⟨hzQm, fun x hx => hzP x (hQP hx)⟩)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZQ3, hzcard]) |>.symm

end ExtqSec

section CfgSec

theorem cfg_card_sup {Γ : Type*} [Group Γ] [Finite Γ] (A B : Subgroup Γ) [B.Normal]
    (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_sup_right A B
  have h2 : B.relIndex A = Nat.card A := by
    rw [← Subgroup.inf_relIndex_right B A, inf_comm, h, Subgroup.relIndex_bot_left]
  have h3 := Subgroup.card_mul_index (B.subgroupOf (A ⊔ B))
  have h4 : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h4] at h3
  have h5 : (B.subgroupOf (A ⊔ B)).index = Nat.card A := by
    rw [← h2, ← h1]; rfl
  rw [h5] at h3
  rw [← h3, mul_comm]

theorem cfg_inf_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {S N : Subgroup Γ} (hS : IsPGroup 3 S)
    (hcop : Nat.Coprime 3 (Nat.card N)) : S ⊓ N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hk⟩ := hS ⟨x, hx.1⟩
  have hk' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (⟨x, hx.2⟩ : ↥N) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk'))
  have h2 : orderOf (⟨x, hx.2⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h1 h2
  have := orderOf_eq_one_iff.1 h3
  simpa using congrArg Subtype.val this

open scoped Pointwise in
theorem cfg_syl_conj {Γ : Type*} [Group Γ] [Finite Γ] (N : Subgroup Γ) [N.Normal]
    (hcop : Nat.Coprime 3 (Nat.card N)) {S S' : Subgroup Γ} (hS : IsPGroup 3 S)
    (hcard : Nat.card S' = Nat.card S) (hle : S' ≤ S ⊔ N) :
    ∃ n ∈ N, ∀ s ∈ S', n * s * n⁻¹ ∈ S := by
  have hfp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := S ⊔ N with hM
  have hSM : S ≤ M := le_sup_left
  have hNM : N ≤ M := le_sup_right
  have hbot : S ⊓ N = ⊥ := cfg_inf_eq_bot hS hcop
  have hcardM : Nat.card M = Nat.card S * Nat.card N := cfg_card_sup S N hbot
  have hS' : IsPGroup 3 S' := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hS
    exact IsPGroup.of_card (hcard.trans ha)
  have key : ∀ A : Subgroup Γ, A ≤ M → IsPGroup 3 A → Nat.card A = Nat.card S →
      ∃ P : Sylow 3 ↥M, (P : Subgroup ↥M) = A.subgroupOf M := by
    intro A hAM hA hAc
    have hAcard : Nat.card (A.subgroupOf M) = Nat.card S := by
      rw [← hAc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
    have hAp : IsPGroup 3 (A.subgroupOf M) := by
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hA
      exact IsPGroup.of_card (hAcard.trans (hAc.symm.trans ha))
    obtain ⟨P, hP⟩ := hAp.exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    have hdvd : Nat.card (P : Subgroup ↥M) ∣ Nat.card S * Nat.card N := by
      rw [← hcardM]; exact Subgroup.card_subgroup_dvd_card _
    rw [ha] at hdvd
    have hdS : 3 ^ a ∣ Nat.card S :=
      (Nat.Coprime.pow_left a hcop).dvd_of_dvd_mul_right hdvd
    have : 3 ^ a ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos hdS
    rw [ha, hAcard]; exact this
  obtain ⟨P₁, hP₁⟩ := key S hSM hS rfl
  obtain ⟨P₂, hP₂⟩ := key S' (hle) hS' hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M P₁ P₂
  have hconj : ∀ s ∈ S', (g : Γ)⁻¹ * s * g ∈ S := by
    intro s hs
    have hsM : s ∈ M := hle hs
    have h1 : (⟨s, hsM⟩ : ↥M) ∈ (P₂ : Subgroup ↥M) := by
      rw [hP₂]; exact hs
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : g⁻¹ * (⟨s, hsM⟩ : ↥M) * g ∈ (P₁ : Subgroup ↥M) := by
      simpa [MulAut.smul_def] using h1
    rw [hP₁] at h2
    exact (Subgroup.mem_subgroupOf).1 h2
  have hgM : (g : Γ)⁻¹ ∈ M := M.inv_mem g.2
  have hgmem : (g : Γ)⁻¹ ∈ (S : Set Γ) * (N : Set Γ) := by
    rw [← Subgroup.mul_normal]; exact hgM
  obtain ⟨s₀, hs₀, n₀, hn₀, hgs⟩ := hgmem
  refine ⟨n₀, hn₀, fun s hs => ?_⟩
  have h1 := hconj s hs
  have hgs' : s₀ * n₀ = (g : Γ)⁻¹ := hgs
  have e : n₀ * s * n₀⁻¹ = s₀⁻¹ * ((g : Γ)⁻¹ * s * g) * s₀ := by
    have : (g : Γ) = (s₀ * n₀)⁻¹ := by rw [hgs']; simp
    rw [← hgs', this]; group
  rw [e]
  exact S.mul_mem (S.mul_mem (S.inv_mem hs₀) h1) hs₀

theorem cfg_syl_conj_amb {M N S S' : Subgroup G} (hNM : N ≤ M) (hn : (N.subgroupOf M).Normal)
    (hSM : S ≤ M) (hS : IsPGroup 3 S) (hcop : Nat.Coprime 3 (Nat.card N))
    (hcard : Nat.card S' = Nat.card S) (hle : S' ≤ S ⊔ N) :
    ∃ n ∈ N, ∀ s ∈ S', n * s * n⁻¹ ∈ S := by
  have hS'M : S' ≤ M := hle.trans (sup_le hSM hNM)
  have hcop' : Nat.Coprime 3 (Nat.card (N.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]; exact hcop
  have hS1 : IsPGroup 3 (S.subgroupOf M) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hS
    exact IsPGroup.of_card ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv).trans ha)
  have hcard' : Nat.card (S'.subgroupOf M) = Nat.card (S.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS'M).toEquiv]; exact hcard
  have hle' : S'.subgroupOf M ≤ S.subgroupOf M ⊔ N.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hSM hNM]; exact Subgroup.comap_mono hle
  obtain ⟨n, hnN, hn'⟩ := cfg_syl_conj (N.subgroupOf M) hcop' hS1 hcard' hle'
  refine ⟨n, (Subgroup.mem_subgroupOf).1 hnN, fun s hs => ?_⟩
  have := hn' ⟨s, hS'M hs⟩ ((Subgroup.mem_subgroupOf).2 hs)
  exact (Subgroup.mem_subgroupOf).1 this

theorem cfg_mem_normalizer {H : Subgroup G} {t : G} (h : ∀ x ∈ H, t * x * t⁻¹ ∈ H) :
    t ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj t).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  have heq : H.map (MulAut.conj t).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have hx' : t * x * t⁻¹ ∈ H.map (MulAut.conj t).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨z, hz, hzx⟩ := hx'
  have h3 : t * z * t⁻¹ = t * x * t⁻¹ := by simpa [MulAut.conj_apply] using hzx
  have : z = x := mul_left_cancel (mul_right_cancel h3)
  rw [← this]; exact hz

omit [Finite G] in
theorem cfg_mem_ZR {R : Subgroup G} {x : G} :
    x ∈ ZR R ↔ x ∈ R ∧ ∀ r ∈ R, x * r = r * x := by
  unfold ZR
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.1 hy ⟨r, hr⟩
    exact (congrArg Subtype.val this).symm
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.2 fun r => ?_
    exact Subtype.ext (h r r.2).symm

omit [Finite G] in
theorem cfg_P3_normalizer (X : Subgroup G) : X ≤ Subgroup.normalizer (P3 X : Set G) := by
  have hle : P3 X ≤ X := Subgroup.map_subtype_le _
  have hn : (P3 X).subgroupOf X = GLAPPrimeCore 3 ↥X := by
    unfold P3 GLAPPrimeCoreOf
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have : ((P3 X).subgroupOf X).Normal := by rw [hn]; infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 this

omit [Finite G] in
theorem cfg_odd_pow {S : Subgroup G} {b t : G} (hb : ∀ s ∈ S, s * b = b * s)
    (htb : t * b = b * t) (hS : ∀ s ∈ S, t * s * t⁻¹ ∈ S)
    (hinv : ∀ s ∈ S, t * s * t⁻¹ * s ∈ Subgroup.zpowers b) {m : ℕ} (hm : Odd m) :
    ∀ s ∈ S, t ^ m * s * (t ^ m)⁻¹ = t * s * t⁻¹ := by
  have hsq : ∀ s ∈ S, Commute (t ^ 2) s := by
    intro s hs
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hinv s hs)
    have hcs : Commute s (b ^ j) := Commute.zpow_right (hb s hs) j
    have hct : Commute t (b ^ j) := Commute.zpow_right htb j
    have e1 : t * s * t⁻¹ = b ^ j * s⁻¹ := by rw [hj]; group
    have htw : t * b ^ j * t⁻¹ = b ^ j := by rw [hct.eq]; group
    have hws : b ^ j * s = s * b ^ j := hcs.symm.eq
    show t ^ 2 * s = s * t ^ 2
    have : t ^ 2 * s * (t ^ 2)⁻¹ = s := by
      calc t ^ 2 * s * (t ^ 2)⁻¹ = t * (t * s * t⁻¹) * t⁻¹ := by rw [pow_two]; group
        _ = t * (b ^ j * s⁻¹) * t⁻¹ := by rw [e1]
        _ = (t * b ^ j * t⁻¹) * (t * s * t⁻¹)⁻¹ := by group
        _ = b ^ j * (b ^ j * s⁻¹)⁻¹ := by rw [htw, e1]
        _ = b ^ j * (s * (b ^ j)⁻¹) := by group
        _ = (b ^ j * s) * (b ^ j)⁻¹ := by group
        _ = s := by rw [hws]; group
    exact (mul_inv_eq_iff_eq_mul.1 this)
  obtain ⟨j, rfl⟩ := hm
  intro s hs
  have hc : Commute ((t ^ 2) ^ j) (t * s * t⁻¹) := (hsq _ (hS s hs)).pow_left j
  have e : t ^ (2 * j + 1) = (t ^ 2) ^ j * t := by rw [pow_succ, pow_mul]
  rw [e]
  calc (t ^ 2) ^ j * t * s * ((t ^ 2) ^ j * t)⁻¹
      = (t ^ 2) ^ j * (t * s * t⁻¹) * ((t ^ 2) ^ j)⁻¹ := by group
    _ = t * s * t⁻¹ := by rw [hc.eq]; group

theorem exists_config (i302 : Input30_2) {B : Subgroup G} {b : G} {L₁ L₂ L₃ R R₁ R₂ R₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) (hSy : SylData B b L₁ L₂ L₃ R R₁ R₂ R₃) :
    ∃ (u v t : G) (Q₁ Q : Subgroup G),
      u ∈ R₁ ∧ v ∈ R₂ ∧ u ∉ Subgroup.zpowers b ∧ v ∉ Subgroup.zpowers b ∧ u ^ 3 = 1 ∧
      v ^ 3 = 1 ∧ t ∈ L₁ ⊔ L₂ ∧ (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧ t * (u * v) * t⁻¹ = (u * v)⁻¹ ∧
      Q₁ = (R₁ ⊔ R₂) ⊓ Cb (u * v) ∧ t ∈ Subgroup.normalizer (Q₁ : Set G) ∧
      (∀ q ∈ Q₁, t * q * t⁻¹ * q ∈ Subgroup.zpowers b) ∧
      Q ≤ Q₁ ∧ (Q.subgroupOf Q₁).Normal ∧ Nat.card Q = 27 ∧
      (¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) ∧ (∀ a ∈ Q, a ^ 3 = 1) ∧ ZR Q = Subgroup.zpowers b ∧
      Q₁ ≤ oPrimePOf 3 (Cb b ⊓ Cb (u * v)) := by
  have hc1 := hR.tri.comp₁
  have hc2 := hR.tri.comp₂
  have hL₁C : L₁ ≤ Cb b := hc1.1
  have hL₂C : L₂ ≤ Cb b := hc2.1
  have hR₁R : R₁ ≤ R := by rw [hSy.h1]; exact inf_le_left
  have hR₂R : R₂ ≤ R := by rw [hSy.h2]; exact inf_le_left
  have hR₁L : R₁ ≤ L₁ := by rw [hSy.h1]; exact inf_le_right
  have hR₂L : R₂ ≤ L₂ := by rw [hSy.h2]; exact inf_le_right
  have hR₁p : IsPGroup 3 R₁ := hSy.hRp.to_le hR₁R
  have hR₂p : IsPGroup 3 R₂ := hSy.hRp.to_le hR₂R
  obtain ⟨h27₁, hna₁, h3₁, hZ₁⟩ := hR.syl₁ R₁ hR₁L hR₁p hSy.s1
  obtain ⟨h27₂, hna₂, h3₂, hZ₂⟩ := hR.syl₂ R₂ hR₂L hR₂p hSy.s2
  obtain ⟨hbR₁, hbc₁⟩ := cfg_mem_ZR.1 (show b ∈ ZR R₁ by rw [hZ₁]; exact Subgroup.mem_zpowers b)
  obtain ⟨hbR₂, hbc₂⟩ := cfg_mem_ZR.1 (show b ∈ ZR R₂ by rw [hZ₂]; exact Subgroup.mem_zpowers b)
  have hb3 : b ^ 3 = 1 := h3₁ b hbR₁
  have hR₁C : R₁ ≤ Cb b := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hbc₁ x hx).symm
  have hR₂C : R₂ ≤ Cb b := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hbc₂ x hx).symm
  have hSR : R₁ ⊔ R₂ ≤ R := by rw [hSy.hprod]; exact le_sup_left
  have hSp : IsPGroup 3 ↥(R₁ ⊔ R₂) := hSy.hRp.to_le hSR
  have hSC : R₁ ⊔ R₂ ≤ Cb b := sup_le hR₁C hR₂C
  have hCbS : ∀ s ∈ R₁ ⊔ R₂, s * b = b * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (hSC hs)
  obtain ⟨t₁, ht₁L, -, ht₁N, ht₁inv⟩ := exists_inverter i302 hR (L := L₁) (R := R₁)
    (Or.inl rfl) hR₁L hR₁p hSy.s1 hbR₁
  obtain ⟨t₂, ht₂L, -, ht₂N, ht₂inv⟩ := exists_inverter i302 hR (L := L₂) (R := R₂)
    (Or.inr (Or.inl rfl)) hR₂L hR₂p hSy.s2 hbR₂
  have ht₁R : ∀ r ∈ R₁, t₁ * r * t₁⁻¹ ∈ R₁ := fun r hr =>
    (Subgroup.mem_normalizer_iff.1 ht₁N r).1 hr
  have ht₂R : ∀ r ∈ R₂, t₂ * r * t₂⁻¹ ∈ R₂ := fun r hr =>
    (Subgroup.mem_normalizer_iff.1 ht₂N r).1 hr
  set M : Subgroup G := L₁ ⊔ L₂ with hMdef
  have hL₁M : L₁ ≤ M := le_sup_left
  have hL₂M : L₂ ≤ M := le_sup_right
  have hMC : M ≤ Cb b := sup_le hL₁C hL₂C
  have hSM : R₁ ⊔ R₂ ≤ M := sup_le (hR₁L.trans hL₁M) (hR₂L.trans hL₂M)
  set N : Subgroup G := P3 (Cb b) ⊓ M with hNdef
  have hNM : N ≤ M := inf_le_right
  have hMN : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    refine ⟨(Subgroup.mem_normalizer_iff.1 (cfg_P3_normalizer (Cb b) (hMC hg)) n).1 hn.1, ?_⟩
    exact M.mul_mem (M.mul_mem hg hn.2) (M.inv_mem hg)
  have hnormal : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 fun g hg => cfg_mem_normalizer (hMN g hg)
  have hcopP : Nat.Coprime 3 (Nat.card (P3 (Cb b))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three (Cb b))
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopP
  have hbot : (R₁ ⊔ R₂) ⊓ N = ⊥ := cfg_inf_eq_bot hSp hcop
  have hcomm12 : ∀ g ∈ L₁, ∀ h ∈ L₂, g * h * g⁻¹ * h⁻¹ ∈ P3 (Cb b) := by
    intro g hg h hh
    have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hc1 hc2 hR.tri.ne₁₂
      (Subgroup.commutator_mem_commutator hg hh)
    simpa only [commutatorElement_def] using this
  have hcomm21 : ∀ h ∈ L₂, ∀ g ∈ L₁, h * g * h⁻¹ * g⁻¹ ∈ P3 (Cb b) := by
    intro h hh g hg
    have := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hc2 hc1 hR.tri.ne₁₂.symm
      (Subgroup.commutator_mem_commutator hh hg)
    simpa only [commutatorElement_def] using this
  have hA : ∀ r ∈ R₁, ∃ n ∈ N, t₂ * r * t₂⁻¹ = r * n := by
    intro r hr
    refine ⟨r⁻¹ * (t₂ * r * t₂⁻¹), ⟨?_, ?_⟩, by group⟩
    · have := hcomm12 r⁻¹ (L₁.inv_mem (hR₁L hr)) t₂ ht₂L
      have e : r⁻¹ * (t₂ * r * t₂⁻¹) = r⁻¹ * t₂ * r⁻¹⁻¹ * t₂⁻¹ := by group
      rw [e]; exact this
    · exact M.mul_mem (M.inv_mem (hL₁M (hR₁L hr))) (M.mul_mem (M.mul_mem (hL₂M ht₂L)
        (hL₁M (hR₁L hr))) (M.inv_mem (hL₂M ht₂L)))
  have hB' : ∀ r ∈ R₂, ∃ n ∈ N, t₁ * r * t₁⁻¹ = r * n := by
    intro r hr
    refine ⟨r⁻¹ * (t₁ * r * t₁⁻¹), ⟨?_, ?_⟩, by group⟩
    · have := hcomm21 r⁻¹ (L₂.inv_mem (hR₂L hr)) t₁ ht₁L
      have e : r⁻¹ * (t₁ * r * t₁⁻¹) = r⁻¹ * t₁ * r⁻¹⁻¹ * t₁⁻¹ := by group
      rw [e]; exact this
    · exact M.mul_mem (M.inv_mem (hL₂M (hR₂L hr))) (M.mul_mem (M.mul_mem (hL₁M ht₁L)
        (hL₂M (hR₂L hr))) (M.inv_mem (hL₁M ht₁L)))
  have hT1 : ∀ r ∈ R₁, ∃ a ∈ R₁, ∃ m ∈ N,
      t₁ * t₂ * r * (t₁ * t₂)⁻¹ = a * m ∧ a = t₁ * r * t₁⁻¹ := by
    intro r hr
    obtain ⟨n, hn, e⟩ := hA r hr
    refine ⟨t₁ * r * t₁⁻¹, ht₁R r hr, t₁ * n * t₁⁻¹, hMN t₁ (hL₁M ht₁L) n hn, ?_, rfl⟩
    calc t₁ * t₂ * r * (t₁ * t₂)⁻¹ = t₁ * (t₂ * r * t₂⁻¹) * t₁⁻¹ := by group
      _ = t₁ * (r * n) * t₁⁻¹ := by rw [e]
      _ = (t₁ * r * t₁⁻¹) * (t₁ * n * t₁⁻¹) := by group
  have hT2 : ∀ r ∈ R₂, ∃ a ∈ R₂, ∃ m ∈ N,
      t₁ * t₂ * r * (t₁ * t₂)⁻¹ = a * m ∧ a = t₂ * r * t₂⁻¹ := by
    intro r hr
    obtain ⟨n, hn, e⟩ := hB' (t₂ * r * t₂⁻¹) (ht₂R r hr)
    refine ⟨t₂ * r * t₂⁻¹, ht₂R r hr, n, hn, ?_, rfl⟩
    calc t₁ * t₂ * r * (t₁ * t₂)⁻¹ = t₁ * (t₂ * r * t₂⁻¹) * t₁⁻¹ := by group
      _ = (t₂ * r * t₂⁻¹) * n := e
  have hle : (R₁ ⊔ R₂).map (MulAut.conj (t₁ * t₂)).toMonoidHom ≤ (R₁ ⊔ R₂) ⊔ N := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      obtain ⟨a, ha, m, hm, e, -⟩ := hT1 r hr
      have : (MulAut.conj (t₁ * t₂)).toMonoidHom r = a * m := by
        show (t₁ * t₂) * r * (t₁ * t₂)⁻¹ = a * m
        exact e
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
        (Subgroup.mem_sup_right hm)
    · rintro _ ⟨r, hr, rfl⟩
      obtain ⟨a, ha, m, hm, e, -⟩ := hT2 r hr
      have : (MulAut.conj (t₁ * t₂)).toMonoidHom r = a * m := by
        show (t₁ * t₂) * r * (t₁ * t₂)⁻¹ = a * m
        exact e
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ha))
        (Subgroup.mem_sup_right hm)
  have hcard : Nat.card ((R₁ ⊔ R₂).map (MulAut.conj (t₁ * t₂)).toMonoidHom) =
      Nat.card ↥(R₁ ⊔ R₂) := Subgroup.card_map_of_injective (MulAut.conj (t₁ * t₂)).injective
  obtain ⟨n, hnN, hn⟩ := cfg_syl_conj_amb hNM hnormal hSM hSp hcop hcard hle
  have ht'M : n * (t₁ * t₂) ∈ M :=
    M.mul_mem (hNM hnN) (M.mul_mem (hL₁M ht₁L) (hL₂M ht₂L))
  have ht'S : ∀ s ∈ R₁ ⊔ R₂, n * (t₁ * t₂) * s * (n * (t₁ * t₂))⁻¹ ∈ R₁ ⊔ R₂ := by
    intro s hs
    have := hn ((MulAut.conj (t₁ * t₂)).toMonoidHom s) ⟨s, hs, rfl⟩
    have e : n * (t₁ * t₂) * s * (n * (t₁ * t₂))⁻¹ =
        n * (t₁ * t₂ * s * (t₁ * t₂)⁻¹) * n⁻¹ := by group
    rw [e]; exact this
  have hkey : ∀ a ∈ R₁ ⊔ R₂, ∀ m ∈ N, ∀ r ∈ R₁ ⊔ R₂, t₁ * t₂ * r * (t₁ * t₂)⁻¹ = a * m →
      n * (t₁ * t₂) * r * (n * (t₁ * t₂))⁻¹ = a := by
    intro a ha m hm r hr e
    have hx : n * (t₁ * t₂) * r * (n * (t₁ * t₂))⁻¹ = n * (a * m) * n⁻¹ := by
      rw [← e]; group
    have hxS : n * (a * m) * n⁻¹ ∈ R₁ ⊔ R₂ := hx ▸ ht'S r hr
    have hxN : a⁻¹ * (n * (a * m) * n⁻¹) ∈ N := by
      have e2 : a⁻¹ * (n * (a * m) * n⁻¹) = (a⁻¹ * n * a⁻¹⁻¹) * m * n⁻¹ := by group
      rw [e2]
      exact N.mul_mem (N.mul_mem (hMN a⁻¹ (M.inv_mem (hSM ha)) n hnN) hm) (N.inv_mem hnN)
    have hmem : a⁻¹ * (n * (a * m) * n⁻¹) ∈ (R₁ ⊔ R₂) ⊓ N :=
      ⟨(R₁ ⊔ R₂).mul_mem ((R₁ ⊔ R₂).inv_mem ha) hxS, hxN⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hx]; exact (inv_mul_eq_one.1 hmem).symm
  have hact1 : ∀ r ∈ R₁, n * (t₁ * t₂) * r * (n * (t₁ * t₂))⁻¹ = t₁ * r * t₁⁻¹ := by
    intro r hr
    obtain ⟨a, ha, m, hm, e, rfl⟩ := hT1 r hr
    exact hkey _ (Subgroup.mem_sup_left ha) m hm r (Subgroup.mem_sup_left hr) e
  have hact2 : ∀ r ∈ R₂, n * (t₁ * t₂) * r * (n * (t₁ * t₂))⁻¹ = t₂ * r * t₂⁻¹ := by
    intro r hr
    obtain ⟨a, ha, m, hm, e, rfl⟩ := hT2 r hr
    exact hkey _ (Subgroup.mem_sup_right ha) m hm r (Subgroup.mem_sup_right hr) e
  have hdecomp : ∀ s ∈ R₁ ⊔ R₂, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, r₁ * r₂ = s := by
    have hle' : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := fun x hx =>
      cfg_mem_normalizer fun y hy => by
        rw [show x * y * x⁻¹ = y by rw [hSy.c12 x hx y hy]; group]; exact hy
    have := Subgroup.coe_mul_of_left_le_normalizer_right R₁ R₂ hle'
    intro s hs
    have hs' : s ∈ ((R₁ ⊔ R₂ : Subgroup G) : Set G) := hs
    rw [this] at hs'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hs'
    exact ⟨x, hx, y, hy, hxy⟩
  have hinv' : ∀ s ∈ R₁ ⊔ R₂, n * (t₁ * t₂) * s * (n * (t₁ * t₂))⁻¹ * s ∈ Subgroup.zpowers b := by
    intro s hs
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hdecomp s hs
    have e1 : n * (t₁ * t₂) * (r₁ * r₂) * (n * (t₁ * t₂))⁻¹ =
        (n * (t₁ * t₂) * r₁ * (n * (t₁ * t₂))⁻¹) * (n * (t₁ * t₂) * r₂ * (n * (t₁ * t₂))⁻¹) := by
      group
    rw [e1, hact1 r₁ hr₁, hact2 r₂ hr₂]
    obtain ⟨j₁, hj₁⟩ := Subgroup.mem_zpowers_iff.1 (ht₁inv r₁ hr₁)
    obtain ⟨j₂, hj₂⟩ := Subgroup.mem_zpowers_iff.1 (ht₂inv r₂ hr₂)
    have ha₁ : t₁ * r₁ * t₁⁻¹ = b ^ j₁ * r₁⁻¹ := by rw [hj₁]; group
    have ha₂ : t₂ * r₂ * t₂⁻¹ = b ^ j₂ * r₂⁻¹ := by rw [hj₂]; group
    rw [ha₁, ha₂]
    have hcr₁ : Commute r₁ b := (hbc₁ r₁ hr₁).symm
    have c1 : r₁⁻¹ * b ^ j₂ = b ^ j₂ * r₁⁻¹ := (Commute.zpow_right hcr₁ j₂).inv_left.eq
    have c2 : r₂⁻¹ * r₁ = r₁ * r₂⁻¹ :=
      (show Commute r₂ r₁ from (hSy.c12 r₁ hr₁ r₂ hr₂).symm).inv_left.eq
    refine Subgroup.mem_zpowers_iff.2 ⟨j₁ + j₂, ?_⟩
    calc b ^ (j₁ + j₂) = b ^ j₁ * b ^ j₂ := zpow_add b j₁ j₂
      _ = b ^ j₁ * (b ^ j₂ * r₁⁻¹) * (r₁ * r₂⁻¹) * r₂ := by group
      _ = b ^ j₁ * (r₁⁻¹ * b ^ j₂) * (r₂⁻¹ * r₁) * r₂ := by rw [c1, c2]
      _ = (b ^ j₁ * r₁⁻¹) * (b ^ j₂ * r₂⁻¹) * (r₁ * r₂) := by group
  have htb' : (n * (t₁ * t₂)) * b = b * (n * (t₁ * t₂)) :=
    Subgroup.mem_centralizer_singleton_iff.1 (hMC ht'M)
  obtain ⟨a, m, hmodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd
    (orderOf_pos (n * (t₁ * t₂))).ne'
  have hodd := cfg_odd_pow hCbS htb' ht'S hinv' hmodd
  set t : G := (n * (t₁ * t₂)) ^ m with htdef
  have htM : t ∈ M := M.pow_mem ht'M m
  have htC : t ∈ Cb b := (Cb b).pow_mem (hMC ht'M) m
  have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.1 htC
  have ht2 : t ^ (2 ^ a) = 1 := by
    rw [htdef, ← pow_mul]
    have : m * 2 ^ a = orderOf (n * (t₁ * t₂)) := by rw [hord, mul_comm]
    rw [this]; exact pow_orderOf_eq_one _
  have htS : ∀ s ∈ R₁ ⊔ R₂, t * s * t⁻¹ ∈ R₁ ⊔ R₂ := by
    intro s hs; rw [htdef, hodd s hs]; exact ht'S s hs
  have htinv : ∀ s ∈ R₁ ⊔ R₂, t * s * t⁻¹ * s ∈ Subgroup.zpowers b := by
    intro s hs; rw [htdef, hodd s hs]; exact hinv' s hs
  clear_value t
  have hcommz : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self b i j).eq
  obtain ⟨u, huR, hun⟩ : ∃ u ∈ R₁, u ∉ Subgroup.zpowers b := by
    by_contra h
    push Not at h
    exact hna₁ fun x hx y hy => hcommz x (h x hx) y (h y hy)
  obtain ⟨v₀, hv₀R, hv₀n⟩ : ∃ v ∈ R₂, v ∉ Subgroup.zpowers b := by
    by_contra h
    push Not at h
    exact hna₂ fun x hx y hy => hcommz x (h x hx) y (h y hy)
  have hy₀S : u * v₀ ∈ R₁ ⊔ R₂ := Subgroup.mul_mem_sup huR hv₀R
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (htinv _ hy₀S)
  set c : G := b ^ j with hc
  have hcR₂ : c ∈ R₂ := R₂.zpow_mem hbR₂ j
  have hc3 : c * c * c = 1 := by
    have : c ^ 3 = 1 := by
      rw [hc, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    simpa [pow_succ] using this
  have hcb : Commute c b := Commute.zpow_left (Commute.refl b) j
  have hvR : v₀ * c ∈ R₂ := R₂.mul_mem hv₀R hcR₂
  have hvn : v₀ * c ∉ Subgroup.zpowers b := by
    intro h
    apply hv₀n
    have : v₀ = v₀ * c * c⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) j))
  have hu3 : u ^ 3 = 1 := h3₁ u huR
  have hv3 : (v₀ * c) ^ 3 = 1 := by
    have hcomm : Commute v₀ c := Commute.zpow_right (show Commute v₀ b from (hbc₂ v₀ hv₀R).symm) j
    rw [hcomm.mul_pow, h3₂ v₀ hv₀R, one_mul]
    simpa [pow_succ] using hc3
  have hcy : Commute (u * v₀) c := Commute.zpow_right (hCbS _ hy₀S) j
  have htcc : t * c * t⁻¹ = c := by
    have h : t * c = c * t := (Commute.zpow_right (show Commute t b from htb) j).eq
    rw [h]; group
  have hty0 : t * (u * v₀) * t⁻¹ = c * (u * v₀)⁻¹ := by
    calc t * (u * v₀) * t⁻¹ = (t * (u * v₀) * t⁻¹ * (u * v₀)) * (u * v₀)⁻¹ := by group
      _ = c * (u * v₀)⁻¹ := by rw [← hj]
  have hty : t * (u * (v₀ * c)) * t⁻¹ = (u * (v₀ * c))⁻¹ := by
    calc t * (u * (v₀ * c)) * t⁻¹ = (t * (u * v₀) * t⁻¹) * (t * c * t⁻¹) := by group
      _ = (c * (u * v₀)⁻¹) * c := by rw [hty0, htcc]
      _ = c * c * (u * v₀)⁻¹ := by
        rw [mul_assoc, hcy.inv_left.eq, ← mul_assoc]
      _ = c⁻¹ * (u * v₀)⁻¹ := by rw [eq_inv_of_mul_eq_one_left hc3]
      _ = (u * (v₀ * c))⁻¹ := by group
  set y : G := u * (v₀ * c) with hydef
  have h1 : t * y⁻¹ * t⁻¹ = y := by
    rw [show t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ by group, hty, inv_inv]
  have hyinv : t⁻¹ * y * t = y⁻¹ := by
    calc t⁻¹ * y * t = t⁻¹ * (t * y⁻¹ * t⁻¹) * t := by rw [h1]
      _ = y⁻¹ := by group
  have hQ₁norm : t ∈ Subgroup.normalizer (((R₁ ⊔ R₂) ⊓ Cb y : Subgroup G) : Set G) := by
    refine cfg_mem_normalizer fun x hx => ⟨htS x hx.1, ?_⟩
    have hxy : x * y = y * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    have hxy' : x * y⁻¹ = y⁻¹ * x := (show Commute x y from hxy).inv_right.eq
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc t * x * t⁻¹ * y = t * x * (t⁻¹ * y * t) * t⁻¹ := by group
      _ = t * (x * y⁻¹) * t⁻¹ := by rw [hyinv]; group
      _ = t * (y⁻¹ * x) * t⁻¹ := by rw [hxy']
      _ = (t * y⁻¹ * t⁻¹) * (t * x * t⁻¹) := by group
      _ = y * (t * x * t⁻¹) := by rw [h1]
  obtain ⟨Q, hQle, hQn, hQ27, hQna, hQ3, hQZ⟩ := ext_Q hSy.c12 ⟨h27₁, hna₁, h3₁⟩
    ⟨h27₂, hna₂, h3₂⟩ hZ₁ hZ₂ huR hvR hun hvn
  have hnil := nil_cent i302 hR hSy huR hvR hu3 hv3 hun hvn
  exact ⟨u, v₀ * c, t, (R₁ ⊔ R₂) ⊓ Cb y, Q, huR, hvR, hun, hvn, hu3, hv3, htM, ⟨a, ht2⟩, hty, rfl,
    hQ₁norm, fun q hq => htinv q hq.1, hQle, hQn, hQ27, hQna, hQ3, hQZ, hnil⟩

end CfgSec

section D4Sec

abbrev d4_rho (W : Subgroup G) : ↥W →* (↥W ⧸ GLAPPrimeCore 3 ↥W) :=
  QuotientGroup.mk' (GLAPPrimeCore 3 ↥W)

theorem d4_mem_barX {W S : Subgroup G} {z : ↥W ⧸ GLAPPrimeCore 3 ↥W} :
    z ∈ barX 3 W S ↔ ∃ x : ↥W, (x : G) ∈ S ∧ d4_rho W x = z := by
  unfold barX
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem d4_isPGroup_subgroupOf {W S : Subgroup G} (hS : IsPGroup 3 S) (hSW : S ≤ W) :
    IsPGroup 3 (S.subgroupOf W) :=
  hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSW).symm

theorem d4_card_barX {W S : Subgroup G} (hS : IsPGroup 3 S) (hSW : S ≤ W) :
    Nat.card (barX 3 W S) = Nat.card S := by
  unfold barX
  rw [t2_map_card (GLAPPrimeCore 3 ↥W) (coprime_card_gLAPPrimeCore_aux 3 ↥W) _
    (d4_isPGroup_subgroupOf hS hSW)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSW).toEquiv

theorem d4_isPGroup_barX {W S : Subgroup G} (hS : IsPGroup 3 S) :
    IsPGroup 3 (barX 3 W S) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hz
  obtain ⟨k, hk⟩ := hS ⟨(x : G), hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (x : G) ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : x ^ (3 ^ k) = 1 := Subtype.ext (by simpa using h1)
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, h2, map_one]

theorem d4_inj {W S : Subgroup G} (hS : IsPGroup 3 S) (hSW : S ≤ W) {x y : ↥W} (hx : (x : G) ∈ S)
    (hy : (y : G) ∈ S) (h : d4_rho W x = d4_rho W y) : x = y := by
  have hxy : x⁻¹ * y ∈ S.subgroupOf W := by
    refine Subgroup.mem_subgroupOf.2 ?_
    exact S.mul_mem (S.inv_mem hx) hy
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥W) (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv]
    exact inv_mul_eq_one.2 h
  have := t2_inj_of_coprime (GLAPPrimeCore 3 ↥W) (coprime_card_gLAPPrimeCore_aux 3 ↥W) _
    (d4_isPGroup_subgroupOf hS hSW) hxy h1
  exact (inv_mul_eq_one.1 this)


theorem d4_ker_cop {A H : Type*} [Group A] [Group H] [Finite H] (ι : A →* H)
    (hι : Function.Injective ι) (S : Subgroup A) :
    Nat.Coprime 3
      (Nat.card ↥(S ⊓ ((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι).ker)) := by
  have h1 : Nat.card ↥(S ⊓ ((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι).ker) ∣
      Nat.card (GLAPPrimeCore 3 H) := by
    have hmap : Nat.card ((S ⊓ ((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι).ker).map ι) =
        Nat.card ↥(S ⊓ ((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι).ker) :=
      Subgroup.card_map_of_injective hι
    rw [← hmap]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨a, ⟨_, ha⟩, rfl⟩
    exact (QuotientGroup.eq_one_iff _).1 ha
  exact (coprime_card_gLAPPrimeCore_aux 3 H).coprime_dvd_right h1

theorem d4_map_cent {A H : Type*} [Group A] [Finite A] [Group H] [Finite H] (ι : A →* H)
    (hι : Function.Injective ι) {y : A} (hy : y ^ 3 = 1) :
    (Subgroup.centralizer ({y} : Set A)).map ((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι) =
      ((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι).range ⊓
        Subgroup.centralizer ({((QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι) y} :
          Set (H ⧸ GLAPPrimeCore 3 H)) := by
  set ψ := (QuotientGroup.mk' (GLAPPrimeCore 3 H)).comp ι with hψ
  ext w
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  · rintro ⟨⟨g, rfl⟩, hw⟩
    have hw' := Subgroup.mem_centralizer_singleton_iff.1 hw
    haveI := ψ.normal_ker
    have hg : g * y * g⁻¹ * y⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hw']
      group
    have hcop : Nat.Coprime 3 (Nat.card ψ.ker) := by
      have := d4_ker_cop ι hι ⊤
      rwa [top_inf_eq] at this
    obtain ⟨n, hn, hc⟩ := g_lift_centralizer Nat.prime_three ψ.ker hcop ⟨1, by simpa using hy⟩ hg
    refine ⟨g * n, Subgroup.mem_centralizer_singleton_iff.2 hc, ?_⟩
    show ψ (g * n) = ψ g
    rw [map_mul, (MonoidHom.mem_ker.1 hn), mul_one]

theorem d4_range_barX {W S : Subgroup G} (hSW : S ≤ W) :
    ((d4_rho W).comp (Subgroup.inclusion hSW)).range = barX 3 W S := by
  ext z
  rw [d4_mem_barX]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨Subgroup.inclusion hSW s, s.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), hx⟩, rfl⟩


abbrev d4_X (W : Subgroup G) : Type := ↥W ⧸ GLAPPrimeCore 3 ↥W

theorem d4_f3_barOf {M : Type*} [Group M] [Finite M] :
    (Nat.card M).factorization 3 = (Nat.card (M ⧸ GLAPPrimeCore 3 M)).factorization 3 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 M)
  have hc : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 M) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 M)
  rw [h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hc, add_zero]

theorem d4_comp_core (i145 : Input14_5) {W Js J : Subgroup G} (hJsW : Js ≤ W)
    (hJsn : (Js.subgroupOf W).Normal) (hXk : CFSG.Open.IsKGroup (d4_X W)) {b : G}
    (hbJs : b ∈ Js) (hb3 : b ^ 3 = 1) (hJc : GLAPComponent 3 (Js ⊓ Cb b) J) (hbJ : b ∈ J)
    (hε : IsSL3Eps (barOf 3 J))
    (hZ : Subgroup.center (barOf 3 J) =
      Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)))
    (hf3 : (Nat.card J).factorization 3 = 3) :
    ∃ Jb : Subgroup (d4_X W),
      IsComponentOf Jb (GLAPLayer 3 (barX 3 W Js ⊓
          Subgroup.centralizer ({d4_rho W ⟨b, hJsW hbJs⟩} : Set (d4_X W)))) ∧
      ∃ hbJb : d4_rho W ⟨b, hJsW hbJs⟩ ∈ Jb,
        IsSL3Eps (↥Jb ⧸ GLAPPrimeCore 3 ↥Jb) ∧
        Subgroup.center (↥Jb ⧸ GLAPPrimeCore 3 ↥Jb) =
          Subgroup.zpowers (QuotientGroup.mk (⟨d4_rho W ⟨b, hJsW hbJs⟩, hbJb⟩ : ↥Jb)) ∧
        (Nat.card Jb).factorization 3 = 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set ψ : ↥Js →* d4_X W := (d4_rho W).comp (Subgroup.inclusion hJsW) with hψ
  have hcop : ∀ S : Subgroup ↥Js, Nat.Coprime 3 (Nat.card ↥(S ⊓ ψ.ker)) :=
    fun S => d4_ker_cop (Subgroup.inclusion hJsW) (Subgroup.inclusion_injective hJsW) S
  set b' : ↥Js := ⟨b, hbJs⟩ with hb'
  set A_H : Subgroup ↥Js := Subgroup.centralizer ({b'} : Set ↥Js) with hAH
  have hAmap : A_H.map Js.subtype = Js ⊓ Cb b := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
    · rintro ⟨hgJ, hgC⟩
      exact ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)), rfl⟩
  obtain ⟨J', hJ', rfl⟩ := exists_glaPComponent_map_eq hp Js.subtype (s1t_ker_sub Js A_H)
    (K' := J) (by rw [hAmap]; exact hJc)
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hbt3 : ψ b' ^ 3 = 1 := by rw [← map_pow, hb'3, map_one]
  have hAψ : A_H.map ψ = barX 3 W Js ⊓ Subgroup.centralizer ({ψ b'} : Set (d4_X W)) := by
    rw [hAH, d4_map_cent (Subgroup.inclusion hJsW) (Subgroup.inclusion_injective hJsW) hb'3,
      ← hψ, hψ, d4_range_barX hJsW]
  have hc : GLAPComponent 3 (A_H.map ψ) (J'.map ψ) :=
    glaPComponent_map hp ψ (hcop A_H) hJ'
  rw [hAψ] at hc
  have hKn : (barX 3 W Js).Normal :=
    Subgroup.Normal.map hJsn _ (QuotientGroup.mk'_surjective _)
  have hsn : IsSubnormal (barX 3 W Js ⊓ Subgroup.centralizer ({ψ b'} : Set (d4_X W)))
      (Subgroup.centralizer ({ψ b'} : Set (d4_X W))) := by
    have := isSubnormal_inf (isSubnormal_of_normal hKn)
      (Subgroup.centralizer ({ψ b'} : Set (d4_X W)))
    rwa [top_inf_eq] at this
  have hcX : GLAPComponent 3 (Subgroup.centralizer ({ψ b'} : Set (d4_X W))) (J'.map ψ) :=
    j_comp_up hc hsn
  have hcore := glaPPrimeCore_quotient_eq_bot (Z := ↥W) hp
  have hcomm := i145 (d4_X W) (s1t_isKGroup_of_open hXk) hcore (ψ b') hbt3
  have hq := s1t_isQuasisimple hcX hcomm
  have hb'J : b' ∈ J' := by
    obtain ⟨x, hx, hxb⟩ := hbJ
    exact (Subtype.ext hxb : x = b') ▸ hx
  have hbtJ : ψ b' ∈ J'.map ψ := ⟨b', hb'J, rfl⟩
  let e : barOf 3 (J'.map Js.subtype) ≃* (↥(J'.map ψ) ⧸ GLAPPrimeCore 3 ↥(J'.map ψ)) :=
    (lcEquiv hp Js.subtype J' (s1t_ker_sub Js J')).symm.trans
      (lcEquiv hp ψ J' (by simpa using hcop J'))
  have hε' : IsSL3Eps (↥(J'.map ψ) ⧸ GLAPPrimeCore 3 ↥(J'.map ψ)) := s1t_isSL3Eps_of_equiv e hε
  have he_b : e (QuotientGroup.mk ⟨b, hbJ⟩) = QuotientGroup.mk ⟨ψ b', hbtJ⟩ := by
    have h1 : (lcEquiv hp Js.subtype J' (s1t_ker_sub Js J')).symm
        (QuotientGroup.mk ⟨b, hbJ⟩) = QuotientGroup.mk ⟨b', hb'J⟩ := by
      rw [MulEquiv.symm_apply_eq]; rfl
    have h2 : e (QuotientGroup.mk ⟨b, hbJ⟩) = lcEquiv hp ψ J' (by simpa using hcop J')
        ((lcEquiv hp Js.subtype J' (s1t_ker_sub Js J')).symm (QuotientGroup.mk ⟨b, hbJ⟩)) := rfl
    rw [h2, h1]; rfl
  have hZ' : Subgroup.center (↥(J'.map ψ) ⧸ GLAPPrimeCore 3 ↥(J'.map ψ)) =
      Subgroup.zpowers (QuotientGroup.mk (⟨ψ b', hbtJ⟩ : ↥(J'.map ψ))) := by
    rw [← s1t_center_map e, hZ, MonoidHom.map_zpowers]
    congr 1
  have hlay : J'.map ψ ≤ GLAPLayer 3 (barX 3 W Js ⊓
      Subgroup.centralizer ({ψ b'} : Set (d4_X W))) := le_sSup hc
  refine ⟨J'.map ψ, ⟨hlay, isSubnormal_of_le_of_le hc.2.1 hlay (sSup_le fun _ h => h.1), hq⟩,
    hbtJ, hε', hZ', ?_⟩
  have hcard := Nat.card_congr e.toEquiv
  rw [d4_f3_barOf (M := ↥(J'.map ψ)), ← hcard]
  exact (d4_f3_barOf (M := ↥(J'.map Js.subtype))).symm.trans hf3

theorem d4_ZR_barX {W Q : Subgroup G} {b : G} (hQ : IsPGroup 3 Q) (hQW : Q ≤ W) (hbW : b ∈ W)
    (hZ : ZR Q = Subgroup.zpowers b) :
    ZR (barX 3 W Q) = Subgroup.zpowers (d4_rho W ⟨b, hbW⟩) := by
  have hbQ : b ∈ Q := rk5_ZR_le (hZ ▸ Subgroup.mem_zpowers b)
  ext z
  rw [rk5_mem_ZR_iff]
  constructor
  · rintro ⟨hzQ, hcomm⟩
    obtain ⟨x, hxQ, rfl⟩ := d4_mem_barX.1 hzQ
    have hxZ : (x : G) ∈ ZR Q := by
      refine rk5_mem_ZR_iff.2 ⟨hxQ, fun r hr => ?_⟩
      have hy : d4_rho W ⟨r, hQW hr⟩ ∈ barX 3 W Q := d4_mem_barX.2 ⟨⟨r, hQW hr⟩, hr, rfl⟩
      have h1 := hcomm _ hy
      rw [← map_mul, ← map_mul] at h1
      have h2 := d4_inj hQ hQW (x := x * ⟨r, hQW hr⟩) (y := ⟨r, hQW hr⟩ * x)
        (Q.mul_mem hxQ hr) (Q.mul_mem hr hxQ) h1
      exact congrArg Subtype.val h2
    rw [hZ] at hxZ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hxZ
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have : (⟨b, hbW⟩ : ↥W) ^ n = x := Subtype.ext (by simpa using hn)
    rw [← map_zpow, this]
  · intro hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hbn : ((⟨b, hbW⟩ : ↥W) ^ n : ↥W) = ⟨b ^ n, Subgroup.zpow_mem _ hbW n⟩ :=
      Subtype.ext (by simp)
    have hbnQ : b ^ n ∈ Q := Subgroup.zpow_mem _ hbQ n
    have hbnZ : b ^ n ∈ ZR Q := hZ ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) n
    refine ⟨d4_mem_barX.2 ⟨_, ?_, rfl⟩, fun r hr => ?_⟩
    · show ((⟨b, hbW⟩ : ↥W) ^ n : ↥W).1 ∈ Q
      rw [hbn]; exact hbnQ
    · obtain ⟨y, hyQ, rfl⟩ := d4_mem_barX.1 hr
      rw [← map_zpow, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact (rk5_mem_ZR_iff.1 hbnZ).2 _ hyQ

theorem d4_nonab_barX {W Q : Subgroup G} (hQ : IsPGroup 3 Q) (hQW : Q ≤ W)
    (hna : ¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) :
    ¬ ∀ a ∈ barX 3 W Q, ∀ c ∈ barX 3 W Q, a * c = c * a := by
  intro h
  apply hna
  intro a ha c hc
  have h1 := h (d4_rho W ⟨a, hQW ha⟩) (d4_mem_barX.2 ⟨_, ha, rfl⟩)
    (d4_rho W ⟨c, hQW hc⟩) (d4_mem_barX.2 ⟨_, hc, rfl⟩)
  rw [← map_mul, ← map_mul] at h1
  have h2 := d4_inj hQ hQW (x := ⟨a, hQW ha⟩ * ⟨c, hQW hc⟩) (y := ⟨c, hQW hc⟩ * ⟨a, hQW ha⟩)
    (Q.mul_mem ha hc) (Q.mul_mem hc ha) h1
  exact congrArg Subtype.val h2

theorem d4_exp3_barX {W Q : Subgroup G} (hQ3 : ∀ a ∈ Q, a ^ 3 = 1) :
    ∀ z ∈ barX 3 W Q, z ^ 3 = 1 := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hz
  rw [← map_pow]
  have : x ^ 3 = 1 := Subtype.ext (by simpa using hQ3 _ hx)
  rw [this, map_one]

theorem d4_mem_normalizer_barX {W S : Subgroup G} {g : ↥W}
    (hg : (g : G) ∈ Subgroup.normalizer (S : Set G)) :
    d4_rho W g ∈ Subgroup.normalizer ((barX 3 W S : Subgroup (d4_X W)) : Set (d4_X W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hz
    refine d4_mem_barX.2 ⟨g * x * g⁻¹, ?_, by simp [map_mul]⟩
    have := (Subgroup.mem_normalizer_iff.1 hg (x : G)).1 hx
    simpa using this
  · intro hz
    obtain ⟨x, hx, hxz⟩ := d4_mem_barX.1 hz
    refine d4_mem_barX.2 ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 hg ((g : G)⁻¹ * x * g)).2
      have h2 : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x := by group
      rw [h2] at h1
      simpa using h1 hx
    · have : z = (d4_rho W g)⁻¹ * (d4_rho W g * z * (d4_rho W g)⁻¹) * d4_rho W g := by group
      rw [this, ← hxz]
      simp [map_mul, map_inv]

theorem d4_b_mem_frattini {W Q Q₁ : Subgroup G} {b : G} (hQ₁ : IsPGroup 3 Q₁) (hQle : Q ≤ Q₁)
    (hQ₁W : Q₁ ≤ W) (hQ27 : Nat.card Q = 27)
    (hna : ¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) (hQZ : ZR Q = Subgroup.zpowers b)
    (hbo : orderOf b = 3) (hbW : b ∈ W) :
    d4_rho W ⟨b, hbW⟩ ∈ (frattini ↥(barX 3 W Q₁)).map (barX 3 W Q₁).subtype := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  push Not at hna
  obtain ⟨a, ha, c, hc, hac⟩ := hna
  have hna' : ¬ ∀ r s : ↥Q, r * s = s * r := fun h =>
    hac (congrArg Subtype.val (h ⟨a, ha⟩ ⟨c, hc⟩))
  have hcen := t1_comm_mem_center hQ27 hna' ⟨a, ha⟩ ⟨c, hc⟩
  have hZmem : a * c * a⁻¹ * c⁻¹ ∈ ZR Q := by
    refine ⟨⟨a * c * a⁻¹ * c⁻¹, ?_⟩, hcen, rfl⟩
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hc) (Q.inv_mem ha)) (Q.inv_mem hc)
  rw [hQZ] at hZmem
  have hne : a * c * a⁻¹ * c⁻¹ ≠ 1 := by
    intro h
    apply hac
    have := mul_inv_eq_one.1 (by simpa [mul_assoc] using h : a * c * (c * a)⁻¹ = 1)
    exact this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (s1t_mem_zpowers_of_prime hbo hZmem hne)
  have haW : a ∈ W := hQ₁W (hQle ha)
  have hcW : c ∈ W := hQ₁W (hQle hc)
  have hab : d4_rho W ⟨a, haW⟩ ∈ barX 3 W Q₁ := d4_mem_barX.2 ⟨_, hQle ha, rfl⟩
  have hcb : d4_rho W ⟨c, hcW⟩ ∈ barX 3 W Q₁ := d4_mem_barX.2 ⟨_, hQle hc, rfl⟩
  have hcomm := CFSG.SectionRank.Ccomm.commutator_mem_frattini
    (d4_isPGroup_barX (W := W) hQ₁) (⟨_, hab⟩ : ↥(barX 3 W Q₁)) ⟨_, hcb⟩
  have hmem : d4_rho W ⟨a, haW⟩ * d4_rho W ⟨c, hcW⟩ * (d4_rho W ⟨a, haW⟩)⁻¹ *
      (d4_rho W ⟨c, hcW⟩)⁻¹ ∈ (frattini ↥(barX 3 W Q₁)).map (barX 3 W Q₁).subtype :=
    ⟨_, hcomm, rfl⟩
  have hpow := Subgroup.zpow_mem _ hmem k
  convert hpow using 1
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_zpow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
  exact hk.symm


theorem d4_o_inf_le (M A : Subgroup G) : oPrimePOf 3 M ⊓ A ≤ oPrimePOf 3 (M ⊓ A) := by
  refine g2_crit (X := M ⊓ A) (N := oPrimePOf 3 M ⊓ A)
    (inf_le_inf_right _ (g2_oPrimePOf_le M)) ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ (g2_oPrimePOf_le M))]
    intro w hw
    have h1 : w ∈ Subgroup.normalizer (oPrimePOf 3 M : Set G) := by
      have := (Subgroup.normal_subgroupOf_iff_le_normalizer (g2_oPrimePOf_le M)).1
        (g2_oPrimePOf_normal M)
      exact this hw.1
    have h2 : w ∈ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer hw.2
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro z
    simp only [Subgroup.mem_inf]
    rw [h1 z, h2 z]
  · intro g hg
    obtain ⟨k, hk⟩ := g2_mem_oPrimePOf hg.1
    exact ⟨k, gLAPPrimeCoreOf_inf_le Nat.prime_three M A ⟨hk, A.pow_mem hg.2 _⟩⟩

omit [Finite G] in
theorem d4_mem_normalizer_inf {M A : Subgroup G} {g : G} (h1 : g ∈ Subgroup.normalizer (M : Set G))
    (h2 : g ∈ Subgroup.normalizer (A : Set G)) : g ∈ Subgroup.normalizer ((M ⊓ A : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro z
  simp only [Subgroup.mem_inf]
  rw [h1 z, h2 z]

theorem d4_Q₁_le_O {W Q₁ : Subgroup G} {b y : G}
    (hW : W ≤ Subgroup.normalizer (Cb y : Set G)) (hQ₁W : Q₁ ≤ W)
    (hnil : Q₁ ≤ oPrimePOf 3 (Cb b ⊓ Cb y)) : Q₁ ≤ oPrimePOf 3 (W ⊓ Cb b) := by
  set H : Subgroup G := (W ⊓ Cb b) ⊓ Cb y with hH
  have hHM : H ≤ Cb b ⊓ Cb y := fun x hx => ⟨hx.1.2, hx.2⟩
  have h1 : Q₁ ≤ oPrimePOf 3 H := by
    intro q hq
    have hq1 := hnil hq
    have hqM : q ∈ Cb b ⊓ Cb y := g2_oPrimePOf_le _ hq1
    have hqH : q ∈ H := ⟨⟨hQ₁W hq, hqM.1⟩, hqM.2⟩
    have := d4_o_inf_le (Cb b ⊓ Cb y) H ⟨hq1, hqH⟩
    rwa [inf_eq_right.2 hHM] at this
  have hsn : IsSubnormal H (W ⊓ Cb b) := by
    refine IsSubnormal.step inf_le_left ?_ (IsSubnormal.refl _)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro g hg
    exact d4_mem_normalizer_inf (Subgroup.le_normalizer hg) (hW hg.1)
  exact h1.trans (o_le_of_subnormal hsn)

theorem d4_o_to_X {W : Subgroup G} {b : G} (hbW : b ∈ W) (hb3 : b ^ 3 = 1) {q : ↥W}
    (hq : (q : G) ∈ oPrimePOf 3 (W ⊓ Cb b)) :
    d4_rho W q ∈ oPrimePOf 3
      (Subgroup.centralizer ({d4_rho W ⟨b, hbW⟩} : Set (d4_X W))) := by
  set b' : ↥W := ⟨b, hbW⟩ with hb'
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hcent := s1t_map_cent (H := ↥W) hb'3
  let φ : ↥(W ⊓ Cb b) →* ↥(Subgroup.centralizer ({d4_rho W b'} : Set (d4_X W))) :=
    MonoidHom.codRestrict ((d4_rho W).comp (Subgroup.inclusion inf_le_left)) _ (fun g => by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      show d4_rho W (Subgroup.inclusion inf_le_left g) * d4_rho W b' =
        d4_rho W b' * d4_rho W (Subgroup.inclusion inf_le_left g)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2.2))
  have hφ : Function.Surjective φ := by
    intro w
    have hw : w.1 ∈ (Subgroup.centralizer ({b'} : Set ↥W)).map (d4_rho W) := by
      rw [hcent]; exact w.2
    obtain ⟨g, hg, hgw⟩ := hw
    have hgc : (g : G) * b = b * (g : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
    exact ⟨⟨(g : G), g.2, Subgroup.mem_centralizer_singleton_iff.2 hgc⟩, Subtype.ext hgw⟩
  have hle := o_map_hom_le φ hφ
  obtain ⟨a, ha, haq⟩ := hq
  refine ⟨φ a, hle (Subgroup.mem_map_of_mem φ ha), ?_⟩
  show d4_rho W (Subgroup.inclusion inf_le_left a) = d4_rho W q
  congr 1
  exact Subtype.ext haq

theorem d4_not_central {W Js : Subgroup G} {b : G} (hJsW : Js ≤ W) (hsub : IsSubnormal Js W)
    (hbJs : b ∈ Js) (hb3 : b ^ 3 = 1) (hnot : b ∉ oPrimePOf 3 Js) :
    ¬ (∀ g : ↥Js, d4_rho W (Subgroup.inclusion hJsW g) * d4_rho W ⟨b, hJsW hbJs⟩ =
      d4_rho W ⟨b, hJsW hbJs⟩ * d4_rho W (Subgroup.inclusion hJsW g)) := by
  intro hc
  apply hnot
  set Pj : Subgroup ↥Js := GLAPPrimeCore 3 ↥Js with hPj
  set b' : ↥Js := ⟨b, hbJs⟩ with hb'
  have hcomm : ∀ g : ↥Js, g * b' * g⁻¹ * b'⁻¹ ∈ Pj := by
    intro g
    have h1 : d4_rho W (Subgroup.inclusion hJsW g) * d4_rho W (Subgroup.inclusion hJsW b') =
        d4_rho W (Subgroup.inclusion hJsW b') * d4_rho W (Subgroup.inclusion hJsW g) :=
      hc g
    have h2 : d4_rho W (Subgroup.inclusion hJsW (g * b' * g⁻¹ * b'⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      group
    have h3 : Subgroup.inclusion hJsW (g * b' * g⁻¹ * b'⁻¹) ∈ GLAPPrimeCore 3 ↥W :=
      (QuotientGroup.eq_one_iff _).1 h2
    have h4 : ((g * b' * g⁻¹ * b'⁻¹ : ↥Js) : G) ∈ GLAPPrimeCoreOf 3 W := ⟨_, h3, rfl⟩
    have h5 : ((g * b' * g⁻¹ * b'⁻¹ : ↥Js) : G) ∈ Js ⊓ GLAPPrimeCoreOf 3 W := ⟨(g * b' * g⁻¹ * b'⁻¹).2, h4⟩
    rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hsub] at h5
    obtain ⟨c, hc', hcg⟩ := h5
    have : c = g * b' * g⁻¹ * b'⁻¹ := Subtype.ext hcg
    rw [← this]; exact hc'
  set m : ↥Js →* ↥Js ⧸ Pj := QuotientGroup.mk' Pj with hm
  have hmk : ∀ g : ↥Js, m g * m b' = m b' * m g := by
    intro g
    rw [← map_mul, ← map_mul, hm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hnormPj : Pj.Normal := inferInstance
    have := hnormPj.conj_mem _ (hcomm g⁻¹) b'⁻¹
    have e : (g * b')⁻¹ * (b' * g) = b'⁻¹ * (g⁻¹ * b' * g⁻¹⁻¹ * b'⁻¹) * b'⁻¹⁻¹ := by group
    rw [e]; exact this
  set N : Subgroup ↥Js := (Subgroup.zpowers (m b')).comap m with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn
    show m (g * n * g⁻¹) ∈ Subgroup.zpowers (m b')
    have hcm : Commute (m g) ((m b') ^ j) := (show Commute (m g) (m b') from hmk g).zpow_right j
    simp only [map_mul, map_inv]
    rw [← hj]
    have : m g * (m b') ^ j * (m g)⁻¹ = (m b') ^ j := by
      rw [hcm.eq]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩
  have hNle : N ≤ oPrimeP 3 ↥Js := by
    refine g2_crit_group hNn fun g hg => ?_
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    have hgj : m g = (m b') ^ j := hj.symm
    have : m (g ^ 3) = 1 := by
      rw [map_pow, hgj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ← map_pow, hb'3, map_one, one_zpow]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hb'N : b' ∈ N := Subgroup.mem_zpowers _
  exact ⟨b', hNle hb'N, rfl⟩

theorem d4_join_top {W Js Q₁ : Subgroup G} {t : G} (hJsW : Js ≤ W) (hQ₁W : Q₁ ≤ W) (htW : t ∈ W)
    (hW : W = Js ⊔ Q₁ ⊔ Subgroup.zpowers t) :
    barX 3 W Js ⊔ barX 3 W Q₁ ⊔ Subgroup.zpowers (d4_rho W ⟨t, htW⟩) = ⊤ := by
  have h1 : Js.subgroupOf W ⊔ Q₁.subgroupOf W ⊔ Subgroup.zpowers (⟨t, htW⟩ : ↥W) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hJsW, Subgroup.map_subgroupOf_eq_of_le hQ₁W,
      Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.subtype_apply]
    exact hW.symm
  unfold barX
  rw [← Subgroup.map_sup, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, h1]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem d4_gLBConj_cb {g y : G} (h : g * y * g⁻¹ = y⁻¹) : GLBConj g (Cb y) = Cb y := by
  have h2 : g⁻¹ * y⁻¹ * g = y := by
    calc g⁻¹ * y⁻¹ * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [h]
      _ = y := by group
  have key : g⁻¹ * y * g = y⁻¹ := by
    calc g⁻¹ * y * g = (g⁻¹ * y⁻¹ * g)⁻¹ := by group
      _ = y⁻¹ := by rw [h2]
  ext z
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have e1 : z * (g⁻¹ * y * g) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
  have e2 : (g⁻¹ * y * g) * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
  constructor
  · intro hz
    have h3 : z * (g⁻¹ * y * g) = (g⁻¹ * y * g) * z := by rw [e1, e2, hz]
    rw [key] at h3
    exact ((Commute.inv_right_iff (a := z) (b := y)).1 h3)
  · intro hz
    have h3 : z * (g⁻¹ * y * g) = (g⁻¹ * y * g) * z := by
      rw [key]; exact ((Commute.inv_right_iff (a := z) (b := y)).2 hz)
    rw [e1, e2] at h3
    have := mul_left_cancel (mul_right_cancel h3 : g⁻¹ * ((g * z * g⁻¹) * y) = g⁻¹ * (y * (g * z * g⁻¹)))
    exact this

theorem d4_normalizes {y b g : G} {Js : Subgroup G} (hJs : GLAPComponent 3 (Cb y) Js)
    (hbJs : b ∈ Js) (hnot : b ∉ oPrimePOf 3 Js) (hgC : GLBConj g (Cb y) = Cb y)
    (hgb : g * b = b * g) : g ∈ Subgroup.normalizer (Js : Set G) := by
  have hJ' : GLAPComponent 3 (Cb y) (GLBConj g Js) := by
    have := glaPComponent_gLBConj g hJs
    rwa [hgC] at this
  by_cases heq : GLBConj g Js = Js
  · exact mem_normalizer_iff_gLBConj_eq.2 heq
  · exfalso
    have hb : b ∈ Js ⊓ GLBConj g Js := ⟨hbJs, mem_gLBConj.2 (by
      have : g * b * g⁻¹ = b := by rw [hgb]; group
      rw [this]; exact hbJs)⟩
    exact hnot (inf_le_oPrimePOf_of_ne Nat.prime_three hJs hJ' (fun h => heq h.symm) hb)

theorem d4_y_ne_one {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {u v : G} (hu : u ∈ L₁) (hv : v ∈ L₂) (hu3 : u ^ 3 = 1) (hnu : u ∉ Subgroup.zpowers b) :
    u * v ≠ 1 := by
  intro h
  have hT := hR.tri
  have hb3 : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have huv : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
  have hu2 : u ∈ L₂ := by rw [huv]; exact L₂.inv_mem hv
  have huC : u ∈ Cb b := hT.comp₁.1 hu
  have hcomm := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₂ hT.comp₁
    (Ne.symm hT.ne₁₂)
  have hmem : mkX (Cb b) u huC ∈ barX 3 (Cb b) (Subgroup.zpowers b) := by
    refine (hR.fus₁.Zcenter _).2 ⟨⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩, ?_⟩
    rintro q ⟨l, hl, rfl⟩
    have hl' : (l : G) ∈ L₁ := Subgroup.mem_subgroupOf.1 hl
    have := (a_mk_comm_iff huC l.2 (h := (l : G))).1 (hcomm (Subgroup.commutator_mem_commutator hu2 hl'))
    exact this
  exact hnu (q_mem_zpowers_of_bar hbC (kb := 1) (by simpa using hb3) huC (k := 1)
    (by simpa using hu3) (Subgroup.mem_centralizer_singleton_iff.1 huC) hmem)

theorem d4_f3_of_syl {b : G} {L : Subgroup G} (h : SylInfo b L) :
    (Nat.card L).factorization 3 = 3 := by
  have hfp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain P : Sylow 3 ↥L := default
  set R : Subgroup G := (P : Subgroup ↥L).map L.subtype with hR
  have hRL : R ≤ L := fun x hx => by
    obtain ⟨a, -, rfl⟩ := hx
    exact a.2
  have hcardR : Nat.card R = 3 ^ (Nat.card L).factorization 3 := by
    rw [hR, Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity]
  have hRp : IsPGroup 3 R := IsPGroup.of_card hcardR
  have h27 := (h R hRL hRp hcardR).1
  rw [hcardR] at h27
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h27 : 3 ^ _ = 3 ^ 3)

theorem d4_zpowers_map {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y} {x : Y} (hx : x ∈ J) :
    ((Subgroup.zpowers x).subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) =
      Subgroup.zpowers (QuotientGroup.mk (⟨x, hx⟩ : ↥J)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hw)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have : (⟨x, hx⟩ : ↥J) ^ n = w := Subtype.ext (by simpa using hn)
    show (QuotientGroup.mk (⟨x, hx⟩ : ↥J) : ↥J ⧸ GLAPPrimeCore 3 ↥J) ^ n = QuotientGroup.mk' _ w
    rw [← this]
    simp
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨x, hx⟩ : ↥J) ^ n, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
    exact ⟨n, by simp⟩

theorem d4_P3_top {Y : Type} [Group Y] [Finite Y] (h : GLAPPrimeCore 3 Y = ⊥) :
    GLAPPrimeCoreOf 3 (⊤ : Subgroup Y) = ⊥ := by
  have hiso := glaPPrimeCore_map_iso 3 (Subgroup.topEquiv (G := Y))
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨c, hc, rfl⟩
  have h1 : (Subgroup.topEquiv (G := Y)).toMonoidHom c ∈ GLAPPrimeCore 3 Y := by
    rw [← hiso]; exact ⟨c, hc, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  have : c = 1 := (Subgroup.topEquiv (G := Y)).injective (by simpa using h1)
  simp [this]

theorem d4_isD4_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : IsD4Type A) :
    IsD4Type B := by
  obtain ⟨p, f, hp, hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  refine ⟨p, f, hp, hadm, K, hK, hKf, hcard, ⟨?_⟩⟩
  exact (QuotientGroup.congr (Subgroup.center B) (Subgroup.center A) e.symm
    (s1t_center_map e.symm)).trans e'


theorem d4_core (i145 : Input14_5) (i1433 : Input14_33) {m : ℕ}
    (hS : GLStanding G m 3) (hrk4 : GLATwoLocalRank 3 G = 4) {B : Subgroup G} {b : G}
    {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃) {u v t : G} {Q₁ Q : Subgroup G}
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hc : u * v = v * u)
    (hy1 : u * v ≠ 1) (ht : t ∈ L₁ ⊔ L₂)
    (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1)
    (hty : t * (u * v) * t⁻¹ = (u * v)⁻¹) (hQ₁p : IsPGroup 3 Q₁)
    (hQ₁C : Q₁ ≤ Cb b ⊓ Cb (u * v)) (hyQ₁ : u * v ∈ Q₁)
    (htQ₁ : t ∈ Subgroup.normalizer (Q₁ : Set G))
    (hinv : ∀ q ∈ Q₁, t * q * t⁻¹ * q ∈ Subgroup.zpowers b) (hQle : Q ≤ Q₁)
    (hQn : (Q.subgroupOf Q₁).Normal) (hQ27 : Nat.card Q = 27)
    (hQna : ¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) (hQ3 : ∀ a ∈ Q, a ^ 3 = 1)
    (hQZ : ZR Q = Subgroup.zpowers b) (hnil : Q₁ ≤ oPrimePOf 3 (Cb b ⊓ Cb (u * v)))
    {Js J : Subgroup G} (hJs : GLAPComponent 3 (Cb (u * v)) Js) (hbJs : b ∈ Js)
    (hnotJs : b ∉ oPrimePOf 3 Js) (hJc2 : GLAPComponent 3 (Js ⊓ Cb b) J) (hbJ : b ∈ J)
    (hbarJ : barX 3 (Cb b) J = barX 3 (Cb b) L₃) (hJL : J ≤ L₃) :
    IsD4Type (barOf 3 Js) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hT := hR.tri
  have hb3 : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hT.ne_one
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hbL₃ : b ∈ L₃ := hJL hbJ
  have hy3 : (u * v) ^ 3 = 1 := by
    rw [(show Commute u v from hc).mul_pow, hu3, hv3, one_mul]
  set W : Subgroup G := Js ⊔ Q₁ ⊔ Subgroup.zpowers t with hWdef
  have hJsC : Js ≤ Cb (u * v) := hJs.1
  have hJsW : Js ≤ W := le_sup_left.trans le_sup_left
  have hQ₁W : Q₁ ≤ W := le_sup_right.trans le_sup_left
  have htW : t ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htC : GLBConj t (Cb (u * v)) = Cb (u * v) := d4_gLBConj_cb hty
  have htCb : t ∈ Cb b := sup_le hT.comp₁.1 hT.comp₂.1 ht
  have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.1 htCb
  have hnorm_Q : ∀ g ∈ Q₁, g ∈ Subgroup.normalizer (Js : Set G) := fun g hg =>
    d4_normalizes hJs hbJs hnotJs (j_gLBConj_self (hQ₁C hg).2)
      (Subgroup.mem_centralizer_singleton_iff.1 (hQ₁C hg).1)
  have hnorm_t : t ∈ Subgroup.normalizer (Js : Set G) := d4_normalizes hJs hbJs hnotJs htC htb
  have hWn : W ≤ Subgroup.normalizer (Js : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hnorm_Q) (Subgroup.zpowers_le.2 hnorm_t)
  have hJsn : (Js.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJsW).2 hWn
  have hsubJW : IsSubnormal Js W := IsSubnormal.step hJsW hJsn (IsSubnormal.refl W)
  have hWC : W ≤ Subgroup.normalizer (Cb (u * v) : Set G) :=
    sup_le (sup_le (hJsC.trans Subgroup.le_normalizer)
      (fun g hg => Subgroup.le_normalizer (hQ₁C hg).2))
      (Subgroup.zpowers_le.2 (mem_normalizer_iff_gLBConj_eq.2 htC))
  have hWne : W ≠ ⊤ := by
    intro htop
    have hsimple : IsSimpleGroup G := hS.simple
    have hn : Subgroup.normalizer (Cb (u * v) : Set G) = ⊤ := top_le_iff.1 (htop ▸ hWC)
    have hnormal : (Cb (u * v)).Normal := Subgroup.normalizer_eq_top_iff.1 hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Cb (u * v)) with h | h
    · have : u * v ∈ Cb (u * v) := Subgroup.mem_centralizer_singleton_iff.2 rfl
      exact hy1 (Subgroup.mem_bot.1 (h ▸ this))
    · exact centralizer_ne_top_of_simple hS.nonabelian hy1 h
  have hWk : CFSG.Open.IsKGroup ↥W := isKGroup_of_isKProper hS.kProper hWne
  have hXk : CFSG.Open.IsKGroup (d4_X W) := s1t_isKGroup_quotient hWk _
  have hbW : b ∈ W := hJsW hbJs
  set b' : ↥W := ⟨b, hbW⟩ with hb'
  set bb : d4_X W := d4_rho W b' with hbb
  have hbb3 : bb ^ 3 = 1 := by
    rw [hbb, ← map_pow]
    have : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hQp : IsPGroup 3 Q := hQ₁p.to_le hQle
  have hQW : Q ≤ W := hQle.trans hQ₁W
  have hZ : (Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype = Subgroup.zpowers bb :=
    d4_ZR_barX hQp hQW hbW hQZ
  have hbbK : bb ∈ barX 3 W Js := d4_mem_barX.2 ⟨b', hbJs, rfl⟩
  have hKn : (barX 3 W Js).Normal := Subgroup.Normal.map hJsn _ (QuotientGroup.mk'_surjective _)
  have hKq : CFSG.IsQuasisimple ↥(barX 3 W Js) :=
    s1t_isQuasisimple_of_open (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp3 hJsW hsubJW) (isQuasisimple_quotient_of_glaPComponent hJs))
  have hKk : CFSG.IsKGroup ↥(barX 3 W Js) := s1t_isKGroup_of_open (s1t_isKGroup_of_subgroup hXk _)
  have hcore : GLAPPrimeCore 3 (d4_X W) = ⊥ := glaPPrimeCore_quotient_eq_bot hp3
  have hyW : u * v ∈ W := hQ₁W hyQ₁
  set y' : ↥W := ⟨u * v, hyW⟩ with hy'
  have hyb3 : d4_rho W y' ^ 3 = 1 := by
    rw [← map_pow]
    have : y' ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hyb1 : d4_rho W y' ≠ 1 := by
    intro h
    have h' : y' = 1 := d4_inj hQ₁p hQ₁W (x := y') (y := 1) hyQ₁ (Q₁.one_mem) (by rw [h, map_one])
    exact hy1 (congrArg Subtype.val h')
  have hord : orderOf (d4_rho W y') = 3 := orderOf_eq_prime hyb3 hyb1
  have hrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer
      ((barX 3 W Js : Subgroup (d4_X W)) : Set (d4_X W))) := by
    refine rk5_le_pRank (E := Subgroup.zpowers (d4_rho W y')) ?_ (j_isElemAbelian_zpowers hyb3)
      (k := 1) ?_
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
      obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hz
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.1 (hJsC hx)
      show (x : G) * (u * v) = (u * v) * (x : G)
      exact this
    · rw [Nat.card_zpowers, hord, pow_one]
  have hrk : GLATwoLocalRank 3 (d4_X W) ≤ 4 := (twoLocalRank_quot_le W).trans hrk4.le
  have htn : d4_rho W ⟨t, htW⟩ ∈ Subgroup.normalizer
      ((barX 3 W Q₁ : Subgroup (d4_X W)) : Set (d4_X W)) :=
    d4_mem_normalizer_barX (g := ⟨t, htW⟩) htQ₁
  have ht2' : ∃ k : ℕ, d4_rho W ⟨t, htW⟩ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := ht2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨t, htW⟩ : ↥W) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hFr := d4_b_mem_frattini hQ₁p hQle hQ₁W hQ27 hQna hQZ hbo hbW
  have hfr : ∀ q ∈ barX 3 W Q₁, d4_rho W ⟨t, htW⟩ * q * (d4_rho W ⟨t, htW⟩)⁻¹ * q ∈
      (frattini ↥(barX 3 W Q₁)).map (barX 3 W Q₁).subtype := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hq
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hinv (x : G) hx)
    have hpow := Subgroup.zpow_mem _ hFr n
    convert hpow using 1
    have : (⟨t, htW⟩ : ↥W) * x * (⟨t, htW⟩ : ↥W)⁻¹ * x = b' ^ n :=
      Subtype.ext (by simpa using hn.symm)
    rw [← map_zpow, ← this]
    simp only [map_mul, map_inv]
  have hjoin := d4_join_top hJsW hQ₁W htW hWdef
  have hQ'le : barX 3 W Q ≤ barX 3 W Q₁ := t2_barX_mono' hQle
  have hQnorm : Q₁ ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).1 hQn
  have hQ'n : ((barX 3 W Q).subgroupOf (barX 3 W Q₁)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ'le]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hz
    exact d4_mem_normalizer_barX (hQnorm hx)
  have hQ'card : Nat.card (barX 3 W Q) = 27 := (d4_card_barX hQp hQW).trans hQ27
  have hbbZ : bb ∈ (Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype := by
    rw [hZ]; exact Subgroup.mem_zpowers bb
  have hnotZ : ¬ ((Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype ≤
      (Subgroup.center ↥(barX 3 W Js)).map (barX 3 W Js).subtype) := fun hle => by
    obtain ⟨c, hcK, hceq⟩ := hle hbbZ
    refine d4_not_central hJsW hsubJW hbJs hb3 hnotJs fun g => ?_
    have hkK : d4_rho W (Subgroup.inclusion hJsW g) ∈ barX 3 W Js :=
      d4_mem_barX.2 ⟨⟨g.1, hJsW g.2⟩, g.2, rfl⟩
    have h1 := Subgroup.mem_center_iff.1 hcK ⟨_, hkK⟩
    have h2 := congrArg Subtype.val h1
    have hc' : (c : d4_X W) = bb := hceq
    simp only [Subgroup.coe_mul, hc'] at h2
    exact h2
  have hZK : (Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype ≤ barX 3 W Js := by
    rw [hZ]; exact Subgroup.zpowers_le.2 hbbK
  have hJ : ∃ J₀ : Subgroup (d4_X W), IsComponentOf J₀ (GLAPLayer 3 (barX 3 W Js ⊓
        Subgroup.centralizer
          (((Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype : Subgroup (d4_X W)) :
            Set (d4_X W)))) ∧
      (Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype ≤ J₀ ∧
      IsSL3Eps (↥J₀ ⧸ GLAPPrimeCore 3 ↥J₀) ∧
      (((Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype).subgroupOf J₀).map
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J₀)) =
        Subgroup.center (↥J₀ ⧸ GLAPPrimeCore 3 ↥J₀) ∧
      (Nat.card J₀).factorization 3 = 3 := by
    obtain ⟨e, he⟩ := s1_equiv (hJL.trans hT.comp₃.1) hT.comp₃.1 hbarJ
    have hε : IsSL3Eps (barOf 3 J) := s1_eps_of_equiv e.symm hR.eps₃
    have hZJ : Subgroup.center (barOf 3 J) =
        Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)) := by
      refine s1_center_zpowers e _ ?_
      rw [he b hbJ hbL₃]
      exact s1_center_barOf hT.comp₃ hbC hbL₃ hR.fus₃
    have hf3 : (Nat.card J).factorization 3 = 3 := by
      have h1 := d4_f3_barOf (M := ↥J)
      have h2 := d4_f3_barOf (M := ↥L₃)
      have h4 : (Nat.card (↥J ⧸ GLAPPrimeCore 3 ↥J)).factorization 3 =
          (Nat.card (↥L₃ ⧸ GLAPPrimeCore 3 ↥L₃)).factorization 3 :=
        congrArg (fun n => n.factorization 3) (Nat.card_congr e.toEquiv)
      rw [h1, h4, ← h2]
      exact d4_f3_of_syl hR.syl₃
    obtain ⟨Jb, hJbc, hbJb, hεJ, hZJb, hf3J⟩ :=
      d4_comp_core i145 hJsW hJsn hXk hbJs hb3 hJc2 hbJ hε hZJ hf3
    refine ⟨Jb, ?_, ?_, hεJ, ?_, hf3J⟩
    · rw [hZ, j_centralizer_zpowers]; exact hJbc
    · rw [hZ]; exact Subgroup.zpowers_le.2 hbJb
    · rw [hZ, d4_zpowers_map hbJb]; exact hZJb.symm
  have hK0 : GLAPPrimeCoreOf 3 (barX 3 W Js) = ⊥ :=
    le_bot_iff.1 ((CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp3
      (isSubnormal_of_normal hKn)).trans (d4_P3_top hcore).le)
  have hQ'cent : barX 3 W Q ≤ Subgroup.centralizer (GLAPLayer 3 (barX 3 W Js ⊓
      Subgroup.centralizer
        (((Subgroup.center ↥(barX 3 W Q)).map (barX 3 W Q).subtype : Subgroup (d4_X W)) :
          Set (d4_X W))) : Set (d4_X W)) := by
    rw [hZ, j_centralizer_zpowers]
    refine gcent i145 hKn hKk hK0 hbbK hbb3 ?_
    intro z hz
    obtain ⟨x, hx, rfl⟩ := d4_mem_barX.1 hz
    exact d4_o_to_X hbW hb3 (d4_Q₁_le_O hWC hQ₁W hnil (hQle hx))
  have hD4 : IsD4Type ↥(barX 3 W Js) :=
    i1433 (d4_X W) (barX 3 W Js) (barX 3 W Q₁) (barX 3 W Q) (d4_rho W ⟨t, htW⟩) hjoin hKn hKq hKk
      hcore hrank hrk (d4_isPGroup_barX hQ₁p) ht2' htn hfr hQ'le hQ'n hQ'card
      (d4_nonab_barX hQp hQW hQna) (d4_exp3_barX hQ3) hnotZ hZK hJ hQ'cent
  exact d4_isD4_of_equiv (quotEquivBarX hp3 hJsW hsubJW).symm hD4

theorem b1_d4 (i183 : Input18_3_4) (i145 : Input14_5) (i1433 : Input14_33) {m : ℕ}
    (hS : GLStanding G m 3) (hrk4 : GLATwoLocalRank 3 G = 4) {B : Subgroup G} {b : G}
    {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃) {u v t : G} {Q₁ Q : Subgroup G}
    (hu : u ∈ L₁) (hv : v ∈ L₂) (hc : u * v = v * u) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1)
    (hnu : u ∉ Subgroup.zpowers b) (hnv : v ∉ Subgroup.zpowers b)
    (hnot : b ∉ oPrimePOf 3 (Cb (u * v))) (ht : t ∈ L₁ ⊔ L₂) (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1)
    (hty : t * (u * v) * t⁻¹ = (u * v)⁻¹) (hQ₁p : IsPGroup 3 Q₁)
    (hQ₁C : Q₁ ≤ Cb b ⊓ Cb (u * v)) (hyQ₁ : u * v ∈ Q₁)
    (htQ₁ : t ∈ Subgroup.normalizer (Q₁ : Set G))
    (hinv : ∀ q ∈ Q₁, t * q * t⁻¹ * q ∈ Subgroup.zpowers b) (hQle : Q ≤ Q₁)
    (hQn : (Q.subgroupOf Q₁).Normal) (hQ27 : Nat.card Q = 27)
    (hQna : ¬ ∀ a ∈ Q, ∀ c ∈ Q, a * c = c * a) (hQ3 : ∀ a ∈ Q, a ^ 3 = 1)
    (hQZ : ZR Q = Subgroup.zpowers b) (hnil : Q₁ ≤ oPrimePOf 3 (Cb b ⊓ Cb (u * v))) :
    ∃ Js : Subgroup G, GLAPComponent 3 (Cb (u * v)) Js ∧ b ∈ Js ∧ IsD4Type (barOf 3 Js) ∧
      (∀ g ∈ L₃, g * (u * v) = (u * v) * g → g ^ 3 = 1 → g ∈ Js) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hT := hR.tri
  have hb3 : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hbL₃ : b ∈ L₃ := s1_b_mem hT.comp₃ hR.fus₃ hb3
  have huC : u ∈ Cb b := hT.comp₁.1 hu
  have hvC : v ∈ Cb b := hT.comp₂.1 hv
  have hyC : u * v ∈ Cb b := (Cb b).mul_mem huC hvC
  have hy3 : (u * v) ^ 3 = 1 := by
    rw [(show Commute u v from hc).mul_pow, hu3, hv3, one_mul]
  have hy1 : u * v ≠ 1 := d4_y_ne_one hR hu hv hu3 hnu
  have hxL : ⁅L₃, Subgroup.zpowers (u * v)⁆ ≤ P3 (Cb b) := by
    rw [Subgroup.commutator_le]
    intro l hl g hg
    have hlu : l * u * l⁻¹ * u⁻¹ ∈ P3 (Cb b) :=
      commutator_le_gLAPPrimeCore_of_ne hp3 hT.comp₃ hT.comp₁ (Ne.symm hT.ne₁₃)
        (Subgroup.commutator_mem_commutator hl hu)
    have hlv : l * v * l⁻¹ * v⁻¹ ∈ P3 (Cb b) :=
      commutator_le_gLAPPrimeCore_of_ne hp3 hT.comp₃ hT.comp₂ (Ne.symm hT.ne₂₃)
        (Subgroup.commutator_mem_commutator hl hv)
    exact a_comm_zpowers (hT.comp₃.1 hl) huC hvC hlu hlv hg
  obtain ⟨hJW, hbJ, hbarJ, hJs, hJJs, hJc2⟩ :=
    jstar i183 hS hT.comp₃ hbL₃ hb3 hR.fus₃ hyC hy3 hy1 hxL
  have hjm := jstar_mem hS hT.comp₃ hbL₃ hb3 hR.fus₃ hyC hy3 hy1 hxL
  have hbJs : b ∈ (⨆ g ∈ GLAPLayer 3 (Cb (u * v)), GLBConj g (GLAPLayer 3 (L₃ ⊓ Cb (u * v)))) :=
    hJJs hbJ
  have hnotJs : b ∉ oPrimePOf 3 (⨆ g ∈ GLAPLayer 3 (Cb (u * v)),
      GLBConj g (GLAPLayer 3 (L₃ ⊓ Cb (u * v)))) := fun h => hnot (o_le_of_subnormal hJs.2.1 h)
  refine ⟨_, hJs, hbJs, ?_, fun g hg hgc hg3 => ?_⟩
  · exact d4_core i145 i1433 hS hrk4 hR hu3 hv3 hc hy1 ht ht2 hty hQ₁p hQ₁C hyQ₁ htQ₁ hinv hQle
      hQn hQ27 hQna hQ3 hQZ hnil hJs hbJs hnotJs hJc2 hbJ hbarJ
      (sSup_le fun _ h => h.1 |>.trans inf_le_left)
  · have hgC : g ∈ Cb (u * v) := Subgroup.mem_centralizer_singleton_iff.2 hgc
    exact hJJs (hjm g ⟨hg, hgC⟩ ⟨1, by simpa using hg3⟩)

end D4Sec

section D4rSec

open scoped Matrix commutatorElement

theorem d4r_core_eq_one {H : Type*} [Group H] [Finite H] {g : H} (hg : g ∈ GLAPPrimeCore 3 H)
    {k : ℕ} (hk : g ^ (3 ^ k) = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card (GLAPPrimeCore 3 H) := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : GLAPPrimeCore 3 H)
    rwa [Subgroup.orderOf_mk] at this
  have hc : Nat.Coprime (3 ^ k) (Nat.card (GLAPPrimeCore 3 H)) :=
    (coprime_card_gLAPPrimeCore_aux 3 H).pow_left k
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hc h1 h2)

theorem d4r_lift {Z A : Type*} [Group Z] [Finite Z] [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (f : Z →* A) (hker : ∀ z, f z = 1 → ∀ k : ℕ, z ^ (p ^ k) = 1 → z = 1)
    {Eb : Subgroup A} (hE : IsElemAbelian p Eb) (hEf : Eb ≤ f.range) :
    ∃ S : Subgroup Z, IsElemAbelian p S ∧ S.map f = Eb ∧ Nat.card S = Nat.card Eb := by
  have hEp : IsPGroup p Eb := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hcard⟩ := hEp.exists_card_eq
  set Pc : Subgroup Z := Eb.comap f with hPc
  set f₁ : Pc →* Eb := (f.comp Pc.subtype).codRestrict Eb fun s => s.2 with hf₁
  have hf₁s : Function.Surjective f₁ := by
    intro e
    obtain ⟨z, hz⟩ := hEf e.2
    exact ⟨⟨z, by simp [hPc, hz]⟩, Subtype.ext hz⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p Pc))
  have hT : Nat.card (S.mapSurjective hf₁s) = p ^ k := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.Prime.factorization_pow hp.out,
      Finsupp.single_eq_same]
  set ι : S →* Z := Pc.subtype.comp (S : Subgroup Pc).subtype
  set φ : S →* Eb := f₁.comp (S : Subgroup Pc).subtype with hφdef
  have hker' : ∀ s : S, ι s ∈ f.ker → s = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := S.isPGroup' s
    have h1 : (ι s) ^ (p ^ k) = 1 := by
      rw [← map_pow, hk, map_one]
    have := hker (ι s) hs k h1
    exact Subtype.ext (Subtype.ext this)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h2 : f (ι s) = 1 := congrArg Subtype.val hs
    exact (Subgroup.mem_bot).2 (hker' s h2)
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hrange : φ.range = (S.mapSurjective hf₁s : Subgroup Eb) := by
    rw [Sylow.coe_mapSurjective, hφdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardS : Nat.card S = p ^ k := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hrange, hT]
  have := hE.1
  have hsurj : Function.Surjective φ :=
    (hφ.bijective_of_nat_card_le (by rw [hcard, hcardS])).2
  refine ⟨ι.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : Z) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    apply hφ
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have : x ^ p = 1 := by
      apply hφ
      rw [map_pow, map_one]
      exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ (φ x).2)
    rw [this, map_one]
  · ext e
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact (φ s).2
    · intro he
      obtain ⟨s, hs⟩ := hsurj ⟨e, he⟩
      exact ⟨ι s, ⟨s, rfl⟩, congrArg Subtype.val hs⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, hcardS, hcard]

theorem d4r_exists_elem {A : Type*} [Group A] [Finite A] {H : Subgroup A} {n : ℕ}
    (h : n ≤ CFSG.Open.pRank 3 H) : ∃ E ≤ H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ n := by
  obtain ⟨E, hEH, hE, hc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) H
  have hd : 3 ^ n ∣ Nat.card E := by rw [hc]; exact pow_dvd_pow 3 h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hd
  have hin : Function.Injective E.subtype := E.subtype_injective
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEH, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    change (a : A) * b = b * a
    exact congrArg Subtype.val (hE.1.is_comm.comm a b)
  · rintro _ ⟨a, ha, rfl⟩
    exact hE.2 _ a.2
  · rw [Subgroup.card_map_of_injective hin, hK]


noncomputable def d4r_perm (K : Type) [Field K] :
    Equiv.Perm (Fin 4) →* GL (Fin 4 ⊕ Fin 4) K :=
  (MonoidHom.toHomUnits (Matrix.permMatrixHom (n := Fin 4 ⊕ Fin 4) (R := K))).comp
    ((Equiv.Perm.sumCongrHom (Fin 4) (Fin 4)).comp
      (MonoidHom.prod (MonoidHom.id _) (MonoidHom.id _)))

theorem d4r_perm_mem (K : Type) [Field K] (σ : Equiv.Perm (Fin 4)) :
    d4r_perm K σ ∈ Subgroup.closure {A : GL (Fin 4 ⊕ Fin 4) K |
      ∀ v, StatedQuadPlus 4 K ((A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) =
        StatedQuadPlus 4 K v} := by
  refine Subgroup.subset_closure ?_
  intro v
  have h : ((d4r_perm K σ : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v =
      v ∘ ⇑(Equiv.sumCongr σ⁻¹ σ⁻¹ : Equiv.Perm (Fin 4 ⊕ Fin 4)) := by
    have : ((d4r_perm K σ : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
        (((Equiv.sumCongr σ σ : Equiv.Perm (Fin 4 ⊕ Fin 4))⁻¹ : Equiv.Perm (Fin 4 ⊕ Fin 4)).permMatrix K) := rfl
    rw [this, Matrix.permMatrix_mulVec]
    rfl
  rw [h]
  unfold StatedQuadPlus
  simp only [Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  exact Equiv.sum_comp σ⁻¹ (fun i => v (Sum.inl i) * v (Sum.inr i))

theorem d4r_order3 (K : Type) [Field K] :
    ∃ g : StatedProj (StatedOmega (StatedQuadPlus 4 K)), orderOf g = 3 := by
  set c : Equiv.Perm (Fin 4) := ⁅Equiv.swap (0 : Fin 4) 1, Equiv.swap (0 : Fin 4) 2⁆ with hc
  have hc3 : c ^ 3 = 1 := by decide
  have hc0 : c⁻¹ 0 ≠ 0 := by decide
  have hgO : d4r_perm K c ∈ StatedOmega (StatedQuadPlus 4 K) := by
    rw [hc, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (d4r_perm_mem K _) (d4r_perm_mem K _)
  have hgs : d4r_perm K c ∉ StatedScalars (Fin 4 ⊕ Fin 4) K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun A : GL (Fin 4 ⊕ Fin 4) K =>
      (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (Sum.inl 0) (Sum.inl (c⁻¹ 0))) hu
    simp at h1
    have hne : (Sum.inl 0 : Fin 4 ⊕ Fin 4) ≠ Sum.inl (Equiv.symm c 0) := by
      intro h
      exact hc0 (Sum.inl_injective h).symm
    rw [Matrix.diagonal_apply_ne _ hne] at h1
    have hR : ((d4r_perm K c : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)
        (Sum.inl 0) (Sum.inl (Equiv.symm c 0)) = 1 := by
      have : ((d4r_perm K c : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
          (((Equiv.sumCongr c c : Equiv.Perm (Fin 4 ⊕ Fin 4))⁻¹ : Equiv.Perm (Fin 4 ⊕ Fin 4)).permMatrix K) := rfl
      rw [this]
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [hR] at h1
    exact one_ne_zero h1.symm
  have hx3 : (⟨d4r_perm K c, hgO⟩ : ↥(StatedOmega (StatedQuadPlus 4 K))) ^ 3 = 1 := by
    apply Subtype.ext
    change (d4r_perm K c) ^ 3 = 1
    rw [← map_pow, hc3, map_one]
  refine ⟨QuotientGroup.mk (⟨d4r_perm K c, hgO⟩ : ↥(StatedOmega (StatedQuadPlus 4 K))), ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, hx3]
    rfl
  · intro h
    exact hgs ((Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 h))

theorem d4r_three_dvd {X : Type} [Group X] [Finite X] (h : IsD4Type X) : 3 ∣ Nat.card X := by
  obtain ⟨p, f, -, hmodel⟩ := h
  obtain ⟨-, K, fK, -, -, ⟨e⟩⟩ := hmodel
  obtain ⟨g, hg⟩ := d4r_order3 K
  have h1 : orderOf (e.symm g) = 3 := by rw [MulEquiv.orderOf_eq, hg]
  have h2 : 3 ∣ Nat.card (X ⧸ Subgroup.center X) := h1 ▸ orderOf_dvd_natCard _
  exact h2.trans (Subgroup.card_quotient_dvd_card _)

theorem d4_rank (iD4 : InputD4) {m : ℕ} (hS : GLStanding G m 3) {y : G} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) {Js : Subgroup G} (hJs : GLAPComponent 3 (Cb y) Js)
    (hD4 : IsD4Type (barOf 3 Js)) :
    (∀ x ∈ Js, x ≠ 1 → x ^ 3 = 1 → 5 ≤ CFSG.Open.pRank 3 (Cb y ⊓ Cb x)) ∧
      5 ≤ CFSG.Open.pRank 3 (Cb y) := by
  have := hS.simple
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hCne : Cb y ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hy1
  have hJsne : Js ≠ ⊤ := fun h => hCne (top_le_iff.1 (h ▸ hJs.1))
  have hKJs : CFSG.Open.IsKGroup ↥Js := isKGroup_of_isKProper hS.kProper hJsne
  have hKY : CFSG.Open.IsKGroup (barOf 3 Js) := s1t_isKGroup_quotient hKJs _
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 Js) := isQuasisimple_quotient_of_glaPComponent hJs
  obtain ⟨hZ, hrk⟩ := iD4 (barOf 3 Js) (s1t_isQuasisimple_of_open hQ) (s1t_isKGroup_of_open hKY) hD4
  have hJC : ∀ z ∈ Js, z * y = y * z := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJs.1 hz)
  have hcore : ∀ z : ↥Js, z ^ 3 = 1 → (QuotientGroup.mk z : barOf 3 Js) = 1 → z = 1 := by
    intro z hz3 hz
    exact d4r_core_eq_one (k := 1) ((QuotientGroup.eq_one_iff _).1 hz) (by rwa [pow_one])
  have hyJs : y ∉ Js := by
    intro hyJ
    have hcen : (QuotientGroup.mk (⟨y, hyJ⟩ : ↥Js) : barOf 3 Js) ∈ Subgroup.center (barOf 3 Js) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hJC z.1 z.2)
    have hy3' : (⟨y, hyJ⟩ : ↥Js) ^ 3 = 1 := Subtype.ext hy3
    have h1 := hZ _ hcen 1 (by rw [pow_one, ← QuotientGroup.mk_pow, hy3']; rfl)
    exact hy1 (congrArg Subtype.val (hcore _ hy3' h1))
  have hi : ∀ x ∈ Js, x ≠ 1 → x ^ 3 = 1 → 5 ≤ CFSG.Open.pRank 3 (Cb y ⊓ Cb x) := by
    intro x hxJ hx1 hx3
    have hx3' : (⟨x, hxJ⟩ : ↥Js) ^ 3 = 1 := Subtype.ext hx3
    have hxb3 : (QuotientGroup.mk (⟨x, hxJ⟩ : ↥Js) : barOf 3 Js) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hx3']; rfl
    have hxb1 : (QuotientGroup.mk (⟨x, hxJ⟩ : ↥Js) : barOf 3 Js) ≠ 1 := fun h =>
      hx1 (congrArg Subtype.val (hcore _ hx3' h))
    obtain ⟨Eb, hEbc', hEb, hEbc⟩ := d4r_exists_elem (hrk _ hxb3 hxb1)
    let f : ↥(Js ⊓ Cb x) →* barOf 3 Js :=
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Js)).comp (Subgroup.inclusion inf_le_left)
    have hker : ∀ z, f z = 1 → ∀ k : ℕ, z ^ (3 ^ k) = 1 → z = 1 := by
      intro z hz k hzk
      have h1 : Subgroup.inclusion (inf_le_left : Js ⊓ Cb x ≤ Js) z ∈ GLAPPrimeCore 3 ↥Js :=
        (QuotientGroup.eq_one_iff _).1 hz
      have h2 : (Subgroup.inclusion (inf_le_left : Js ⊓ Cb x ≤ Js) z) ^ (3 ^ k) = 1 := by
        rw [← map_pow, hzk, map_one]
      exact Subgroup.inclusion_injective _ (by rw [d4r_core_eq_one h1 h2, map_one])
    have hzx : IsPGroup 3 (Subgroup.zpowers x) := by
      intro g
      refine ⟨1, ?_⟩
      obtain ⟨n, hn⟩ := g.2
      apply Subtype.ext
      change (g : G) ^ (3 ^ 1) = 1
      rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3,
        one_zpow]
    have hbar := barX_inf_centralizer hp hxJ (le_refl Js) (Subgroup.le_normalizer hxJ) hzx
    rw [barX_self, top_inf_eq] at hbar
    have hEf : Eb ≤ f.range := by
      intro e he
      have he' : e ∈ barX 3 Js (Js ⊓ Cb x) := by
        rw [hbar]
        exact hEbc' he
      obtain ⟨w, hw, hwe⟩ := he'
      exact ⟨⟨w.1, (Subgroup.mem_subgroupOf).1 hw⟩, hwe⟩
    obtain ⟨S, hSe, -, hScard⟩ := d4r_lift f hker hEb hEf
    set E : Subgroup G := S.map (Js ⊓ Cb x).subtype with hE
    have hEcard : Nat.card E = 3 ^ 4 := by
      rw [hE, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hScard, hEbc]
    have hEel : IsElemAbelian 3 E := by
      refine ⟨⟨⟨?_⟩⟩, ?_⟩
      · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
        apply Subtype.ext
        change (a : G) * b = b * a
        exact congrArg (fun s : ↥S => ((s : ↥(Js ⊓ Cb x)) : G)) (hSe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      · rintro _ ⟨a, ha, rfl⟩
        have := hSe.2 a ha
        exact congrArg (fun s : ↥(Js ⊓ Cb x) => (s : G)) this
    have hEJ : ∀ e ∈ E, e ∈ Js ∧ e ∈ Cb x := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hyE : y ∉ E := fun h => hyJs (hEJ y h).1
    have hcomm : ∀ e ∈ E, e * y = y * e := fun e he => hJC e (hEJ e he).1
    have hel := isElemAbelian_sup_zpowers hEel hy3 hcomm
    have hcard := card_sup_zpowers_of_pow_three_eq_one hy3 hyE hcomm
    have hle : E ⊔ Subgroup.zpowers y ≤ Cb y ⊓ Cb x := by
      refine sup_le (fun e he => ⟨hJs.1 (hEJ e he).1, (hEJ e he).2⟩) ?_
      rw [Subgroup.zpowers_le]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hJC x hxJ).symm
    exact CFSG.SectionRank.le_pRank (by norm_num) hle hel (k := 5)
      (by rw [hcard, hEcard]; norm_num [pow_succ])
  refine ⟨hi, ?_⟩
  have h3 : 3 ∣ Nat.card ↥Js :=
    (d4r_three_dvd hD4).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hw1 : (w : G) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    omega
  have hw3 : (w : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    exact congrArg Subtype.val this
  exact (hi w w.2 hw1 hw3).trans (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left)

end D4rSec

section C5Sec

theorem c5_conj_of_comm {H : Type*} [Group H] {d x : H} (h : d * x = x * d) :
    d * x * d⁻¹ = x := by
  rw [h]; group

theorem c5_alg {H : Type*} [Group H] {c₁ c₂ c₃ x₁ x₂ x₃ y₁ y₂ y₃ : H}
    (h₁ : c₁ * x₁ * c₁⁻¹ = y₁) (h₂ : c₂ * x₂ * c₂⁻¹ = y₂) (h₃ : c₃ * x₃ * c₃⁻¹ = y₃)
    (e21 : c₂ * x₁ = x₁ * c₂) (e31 : c₃ * x₁ = x₁ * c₃) (e32 : c₃ * x₂ = x₂ * c₃)
    (d12 : c₁ * y₂ = y₂ * c₁) (d13 : c₁ * y₃ = y₃ * c₁) (d23 : c₂ * y₃ = y₃ * c₂) :
    (c₁ * c₂ * c₃) * (x₁ * x₂ * x₃) * (c₁ * c₂ * c₃)⁻¹ = y₁ * y₂ * y₃ := by
  have k1 : (c₁ * c₂ * c₃) * x₁ * (c₁ * c₂ * c₃)⁻¹ = y₁ := by
    calc (c₁ * c₂ * c₃) * x₁ * (c₁ * c₂ * c₃)⁻¹
        = c₁ * (c₂ * (c₃ * x₁ * c₃⁻¹) * c₂⁻¹) * c₁⁻¹ := by group
      _ = y₁ := by rw [c5_conj_of_comm e31, c5_conj_of_comm e21, h₁]
  have k2 : (c₁ * c₂ * c₃) * x₂ * (c₁ * c₂ * c₃)⁻¹ = y₂ := by
    calc (c₁ * c₂ * c₃) * x₂ * (c₁ * c₂ * c₃)⁻¹
        = c₁ * (c₂ * (c₃ * x₂ * c₃⁻¹) * c₂⁻¹) * c₁⁻¹ := by group
      _ = y₂ := by rw [c5_conj_of_comm e32, h₂, c5_conj_of_comm d12]
  have k3 : (c₁ * c₂ * c₃) * x₃ * (c₁ * c₂ * c₃)⁻¹ = y₃ := by
    calc (c₁ * c₂ * c₃) * x₃ * (c₁ * c₂ * c₃)⁻¹
        = c₁ * (c₂ * (c₃ * x₃ * c₃⁻¹) * c₂⁻¹) * c₁⁻¹ := by group
      _ = y₃ := by rw [h₃, c5_conj_of_comm d23, c5_conj_of_comm d13]
  calc (c₁ * c₂ * c₃) * (x₁ * x₂ * x₃) * (c₁ * c₂ * c₃)⁻¹
      = ((c₁ * c₂ * c₃) * x₁ * (c₁ * c₂ * c₃)⁻¹) * ((c₁ * c₂ * c₃) * x₂ * (c₁ * c₂ * c₃)⁻¹) *
        ((c₁ * c₂ * c₃) * x₃ * (c₁ * c₂ * c₃)⁻¹) := by group
    _ = y₁ * y₂ * y₃ := by rw [k1, k2, k3]

theorem c5_barcomm {b : G} {Li Lj : Subgroup G} (hLi : GLAPComponent 3 (Cb b) Li)
    (hLj : GLAPComponent 3 (Cb b) Lj) (hne : Li ≠ Lj) :
    ∀ x ∈ barX 3 (Cb b) Li, ∀ y ∈ barX 3 (Cb b) Lj, x * y = y * x := by
  have hle := barX_le_centralizer (p := 3) (C := Cb b) (S := Li) (T := Lj) (by
    intro s hs t ht _ _
    exact commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hLi hLj hne
      (Subgroup.commutator_mem_commutator hs ht))
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm

theorem c5_idx {b : G} (hb3 : b ^ 3 = 1) {Li : Subgroup G} (hLi : GLAPComponent 3 (Cb b) Li)
    (hf : FusData (barX 3 (Cb b) Li) (barX 3 (Cb b) (Subgroup.zpowers b)))
    {a a' : G} (ha : a ∈ Li) (ha' : a' ∈ Li) (ha3 : a ^ 3 = 1) (ha'3 : a' ^ 3 = 1)
    (h : (a = a' ∧ a ∈ Subgroup.zpowers b) ∨
      (a ∉ Subgroup.zpowers b ∧ a' ∉ Subgroup.zpowers b)) :
    ∃ c ∈ barX 3 (Cb b) Li,
      c * mkX (Cb b) a (hLi.1 ha) * c⁻¹ = mkX (Cb b) a' (hLi.1 ha') := by
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hb3' : b ^ (3 ^ 1) = 1 := by simpa using hb3
  have hnz : ∀ {w : G} (hwC : w ∈ Cb b), w ^ 3 = 1 → w ∉ Subgroup.zpowers b →
      mkX (Cb b) w hwC ∉ barX 3 (Cb b) (Subgroup.zpowers b) := by
    intro w hwC hw3 hnw hmem
    exact hnw (q_mem_zpowers_of_bar hbC hb3' hwC (k := 1) (by simpa using hw3)
      (Subgroup.mem_centralizer_singleton_iff.1 hwC) hmem)
  have hpow : ∀ {w : G} (hwC : w ∈ Cb b), w ^ 3 = 1 → mkX (Cb b) w hwC ^ 3 = 1 := by
    intro w hwC hw3
    rw [r1_mkX_pow]
    simp only [hw3]
    rfl
  rcases h with ⟨rfl, -⟩ | ⟨hn, hn'⟩
  · exact ⟨1, one_mem _, by simp⟩
  · exact tc_one hf (r1_mem_barX (hLi.1 ha) ha) (r1_mem_barX (hLi.1 ha') ha')
      (hpow _ ha3) (hpow _ ha'3) (hnz _ ha3 hn) (hnz _ ha'3 hn')

theorem c5_conj3 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {a₁ a₂ a₃ a₁' a₂' a₃' : G} (h1 : a₁ ∈ L₁) (h2 : a₂ ∈ L₂) (h3 : a₃ ∈ L₃)
    (h1' : a₁' ∈ L₁) (h2' : a₂' ∈ L₂) (h3' : a₃' ∈ L₃)
    (c12 : a₁ * a₂ = a₂ * a₁) (c13 : a₁ * a₃ = a₃ * a₁) (c23 : a₂ * a₃ = a₃ * a₂)
    (c12' : a₁' * a₂' = a₂' * a₁') (c13' : a₁' * a₃' = a₃' * a₁')
    (c23' : a₂' * a₃' = a₃' * a₂')
    (e1 : a₁ ^ 3 = 1) (e2 : a₂ ^ 3 = 1) (e3 : a₃ ^ 3 = 1)
    (e1' : a₁' ^ 3 = 1) (e2' : a₂' ^ 3 = 1) (e3' : a₃' ^ 3 = 1)
    (z₁ : (a₁ = a₁' ∧ a₁ ∈ Subgroup.zpowers b) ∨
      (a₁ ∉ Subgroup.zpowers b ∧ a₁' ∉ Subgroup.zpowers b))
    (z₂ : (a₂ = a₂' ∧ a₂ ∈ Subgroup.zpowers b) ∨
      (a₂ ∉ Subgroup.zpowers b ∧ a₂' ∉ Subgroup.zpowers b))
    (z₃ : (a₃ = a₃' ∧ a₃ ∈ Subgroup.zpowers b) ∨
      (a₃ ∉ Subgroup.zpowers b ∧ a₃' ∉ Subgroup.zpowers b)) :
    ∃ c ∈ Cb b, c * (a₁ * a₂ * a₃) * c⁻¹ = a₁' * a₂' * a₃' := by
  have hT := hR.tri
  have hb3 : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hC1 := hT.comp₁.1
  have hC2 := hT.comp₂.1
  have hC3 := hT.comp₃.1
  have b12 := c5_barcomm hT.comp₁ hT.comp₂ hT.ne₁₂
  have b13 := c5_barcomm hT.comp₁ hT.comp₃ hT.ne₁₃
  have b23 := c5_barcomm hT.comp₂ hT.comp₃ hT.ne₂₃
  obtain ⟨k₁, hk₁, hk₁e⟩ := c5_idx hb3 hT.comp₁ hR.fus₁ h1 h1' e1 e1' z₁
  obtain ⟨k₂, hk₂, hk₂e⟩ := c5_idx hb3 hT.comp₂ hR.fus₂ h2 h2' e2 e2' z₂
  obtain ⟨k₃, hk₃, hk₃e⟩ := c5_idx hb3 hT.comp₃ hR.fus₃ h3 h3' e3 e3' z₃
  have m1 := r1_mem_barX (hC1 h1) h1
  have m2 := r1_mem_barX (hC2 h2) h2
  have m3 := r1_mem_barX (hC3 h3) h3
  have m1' := r1_mem_barX (hC1 h1') h1'
  have m2' := r1_mem_barX (hC2 h2') h2'
  have m3' := r1_mem_barX (hC3 h3') h3'
  have key := c5_alg hk₁e hk₂e hk₃e (b12 _ m1 _ hk₂).symm (b13 _ m1 _ hk₃).symm
    (b23 _ m2 _ hk₃).symm (b12 _ hk₁ _ m2') (b13 _ hk₁ _ m3') (b23 _ hk₂ _ m3')
  obtain ⟨c₀, hc₀⟩ := QuotientGroup.mk_surjective (k₁ * k₂ * k₃)
  let W : ↥(Cb b) := ⟨a₁ * a₂ * a₃, mul_mem (mul_mem (hC1 h1) (hC2 h2)) (hC3 h3)⟩
  let W' : ↥(Cb b) := ⟨a₁' * a₂' * a₃', mul_mem (mul_mem (hC1 h1') (hC2 h2')) (hC3 h3')⟩
  have hW3 : W ^ 3 = 1 := by
    apply Subtype.ext
    show (a₁ * a₂ * a₃) ^ 3 = 1
    rw [(show Commute (a₁ * a₂) a₃ from Commute.mul_left (show Commute a₁ a₃ from c13)
      (show Commute a₂ a₃ from c23)).mul_pow, (show Commute a₁ a₂ from c12).mul_pow, e1, e2, e3]
    simp
  have hW'3 : W' ^ 3 = 1 := by
    apply Subtype.ext
    show (a₁' * a₂' * a₃') ^ 3 = 1
    rw [(show Commute (a₁' * a₂') a₃' from Commute.mul_left (show Commute a₁' a₃' from c13')
      (show Commute a₂' a₃' from c23')).mul_pow, (show Commute a₁' a₂' from c12').mul_pow,
      e1', e2', e3']
    simp
  have hcong : (c₀ * W * c₀⁻¹) * W'⁻¹ ∈ GLAPPrimeCore 3 ↥(Cb b) := by
    have hq : (QuotientGroup.mk (c₀ * W * c₀⁻¹) : ↥(Cb b) ⧸ GLAPPrimeCore 3 ↥(Cb b)) =
        QuotientGroup.mk W' := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc₀]
      exact key
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one]
    exact hq
  obtain ⟨n, hn, hne⟩ := g_conj_of_cong (p := 3) Nat.prime_three (GLAPPrimeCore 3 ↥(Cb b))
    (coprime_card_gLAPPrimeCore_aux 3 ↥(Cb b)) (u := c₀ * W * c₀⁻¹) (v := W')
    ⟨1, by rw [pow_one, conj_pow, hW3]; group⟩ ⟨1, by rw [pow_one, hW'3]⟩ hcong
  refine ⟨((n * c₀ : ↥(Cb b)) : G), (n * c₀).2, ?_⟩
  have := congrArg Subtype.val hne
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  calc (n : G) * c₀ * (a₁ * a₂ * a₃) * ((n : G) * c₀)⁻¹
      = (n : G) * (c₀ * (a₁ * a₂ * a₃) * (c₀ : G)⁻¹) * (n : G)⁻¹ := by group
    _ = a₁' * a₂' * a₃' := this

omit [Finite G] in
theorem c5_mem_shift {L L' : Subgroup G} {β : G} (h : L' = GLBConj β L) {y : G} :
    (y ∈ L → β⁻¹ * y * β⁻¹⁻¹ ∈ L') ∧ (y ∈ L' → β * y * β⁻¹ ∈ L) := by
  subst h
  constructor
  · intro hy
    rw [mem_gLBConj]
    have : β * (β⁻¹ * y * β⁻¹⁻¹) * β⁻¹ = y := by group
    rwa [this]
  · intro hy
    exact mem_gLBConj.1 hy

omit [Finite G] in
theorem c5_zcomm {b z y : G} (hz : z ∈ Subgroup.zpowers b) (hy : y * b = b * y) :
    z * y = y * z := by
  obtain ⟨k, rfl⟩ := hz
  exact ((Commute.zpow_right (show Commute y b from hy) k).eq).symm

omit [Finite G] in
theorem c5_notZ {b d y : G} (hd : d * b = b * d) (hy : y ∉ Subgroup.zpowers b) :
    d * y * d⁻¹ ∉ Subgroup.zpowers b := by
  intro hz
  apply hy
  have hzd : (d * y * d⁻¹) * d = d * (d * y * d⁻¹) := c5_zcomm hz hd
  have : y = d * y * d⁻¹ := by
    calc y = d⁻¹ * ((d * y * d⁻¹) * d) := by group
      _ = d⁻¹ * (d * (d * y * d⁻¹)) := by rw [hzd]
      _ = d * y * d⁻¹ := by group
  rw [this]; exact hz

omit [Finite G] in
theorem c5_conj_comm {d p q : G} (h : p * q = q * p) :
    (d * p * d⁻¹) * (d * q * d⁻¹) = (d * q * d⁻¹) * (d * p * d⁻¹) := by
  calc (d * p * d⁻¹) * (d * q * d⁻¹) = d * (p * q) * d⁻¹ := by group
    _ = d * (q * p) * d⁻¹ := by rw [h]
    _ = (d * q * d⁻¹) * (d * p * d⁻¹) := by group

omit [Finite G] in
theorem c5_conj_cube {d y : G} (h : y ^ 3 = 1) : (d * y * d⁻¹) ^ 3 = 1 := by
  rw [conj_pow, h]; group

theorem c5_s1 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {p w : G} (hp : p ∈ L₁) (hw : w ∈ L₃) (hp3 : p ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hpn : p ∉ Subgroup.zpowers b) (hwn : w ∉ Subgroup.zpowers b) : ∃ c : G, c * p * c⁻¹ = w := by
  obtain ⟨β, hβB, h21, h32, h13⟩ := hR.tri.cyc
  have hβb : β * b = b * β := r1_commute_of_B hR.tri.elemB hβB hR.tri.mem
  have hβ' : β⁻¹ * b = b * β⁻¹ := (Commute.inv_left (show Commute β b from hβb)).eq
  have hw' : β⁻¹ * w * β⁻¹⁻¹ ∈ L₁ := (c5_mem_shift h13).1 hw
  obtain ⟨c, -, hce⟩ := c5_conj3 hR (a₁ := p) (a₂ := 1) (a₃ := 1) (a₁' := β⁻¹ * w * β⁻¹⁻¹)
    (a₂' := 1) (a₃' := 1) hp (one_mem _) (one_mem _) hw' (one_mem _) (one_mem _)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hp3 (by simp) (by simp)
    (c5_conj_cube hw3) (by simp) (by simp) (Or.inr ⟨hpn, c5_notZ hβ' hwn⟩)
    (Or.inl ⟨rfl, one_mem _⟩) (Or.inl ⟨rfl, one_mem _⟩)
  refine ⟨β * c, ?_⟩
  simp only [mul_one] at hce
  calc β * c * p * (β * c)⁻¹ = β * (c * p * c⁻¹) * β⁻¹ := by group
    _ = w := by rw [hce]; group

theorem c5_s2 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {p w : G} (hp : p ∈ L₂) (hw : w ∈ L₃) (hp3 : p ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hpn : p ∉ Subgroup.zpowers b) (hwn : w ∉ Subgroup.zpowers b) : ∃ c : G, c * p * c⁻¹ = w := by
  obtain ⟨β, hβB, h21, h32, h13⟩ := hR.tri.cyc
  have hβb : β * b = b * β := r1_commute_of_B hR.tri.elemB hβB hR.tri.mem
  have hw' : β * w * β⁻¹ ∈ L₂ := (c5_mem_shift h32).2 hw
  obtain ⟨c, -, hce⟩ := c5_conj3 hR (a₁ := 1) (a₂ := p) (a₃ := 1) (a₁' := 1)
    (a₂' := β * w * β⁻¹) (a₃' := 1) (one_mem _) hp (one_mem _) (one_mem _) hw' (one_mem _)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hp3 (by simp)
    (by simp) (c5_conj_cube hw3) (by simp) (Or.inl ⟨rfl, one_mem _⟩)
    (Or.inr ⟨hpn, c5_notZ hβb hwn⟩) (Or.inl ⟨rfl, one_mem _⟩)
  refine ⟨β⁻¹ * c, ?_⟩
  simp only [one_mul, mul_one] at hce
  calc β⁻¹ * c * p * (β⁻¹ * c)⁻¹ = β⁻¹ * (c * p * c⁻¹) * β⁻¹⁻¹ := by group
    _ = w := by rw [hce]; group

theorem c5_s3 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {p w : G} (hp : p ∈ L₃) (hw : w ∈ L₃) (hp3 : p ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hpn : p ∉ Subgroup.zpowers b) (hwn : w ∉ Subgroup.zpowers b) : ∃ c : G, c * p * c⁻¹ = w := by
  obtain ⟨c, -, hce⟩ := c5_conj3 hR (a₁ := 1) (a₂ := 1) (a₃ := p) (a₁' := 1)
    (a₂' := 1) (a₃' := w) (one_mem _) (one_mem _) hp (one_mem _) (one_mem _) hw
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hp3
    (by simp) (by simp) hw3 (Or.inl ⟨rfl, one_mem _⟩) (Or.inl ⟨rfl, one_mem _⟩)
    (Or.inr ⟨hpn, hwn⟩)
  exact ⟨c, by simpa using hce⟩

theorem c5_d12 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {p q u v : G} (hp : p ∈ L₁) (hq : q ∈ L₂) (hu : u ∈ L₁) (hv : v ∈ L₂)
    (hpq : p * q = q * p) (huv : u * v = v * u) (hp3 : p ^ 3 = 1) (hq3 : q ^ 3 = 1)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hpn : p ∉ Subgroup.zpowers b)
    (hqn : q ∉ Subgroup.zpowers b) (hun : u ∉ Subgroup.zpowers b)
    (hvn : v ∉ Subgroup.zpowers b) : ∃ c : G, c * (p * q) * c⁻¹ = u * v := by
  obtain ⟨c, -, hce⟩ := c5_conj3 hR (a₁ := p) (a₂ := q) (a₃ := 1) (a₁' := u)
    (a₂' := v) (a₃' := 1) hp hq (one_mem _) hu hv (one_mem _) hpq (by simp) (by simp) huv
    (by simp) (by simp) hp3 hq3 (by simp) hu3 hv3 (by simp) (Or.inr ⟨hpn, hun⟩)
    (Or.inr ⟨hqn, hvn⟩) (Or.inl ⟨rfl, one_mem _⟩)
  exact ⟨c, by simpa using hce⟩

theorem c5_d23 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {p q u v : G} (hp : p ∈ L₂) (hq : q ∈ L₃) (hu : u ∈ L₁) (hv : v ∈ L₂)
    (hpq : p * q = q * p) (huv : u * v = v * u) (hp3 : p ^ 3 = 1) (hq3 : q ^ 3 = 1)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hpn : p ∉ Subgroup.zpowers b)
    (hqn : q ∉ Subgroup.zpowers b) (hun : u ∉ Subgroup.zpowers b)
    (hvn : v ∉ Subgroup.zpowers b) : ∃ c : G, c * (p * q) * c⁻¹ = u * v := by
  obtain ⟨β, hβB, h21, h32, h13⟩ := hR.tri.cyc
  have hβb : β * b = b * β := r1_commute_of_B hR.tri.elemB hβB hR.tri.mem
  have hβ' : β⁻¹ * b = b * β⁻¹ := (Commute.inv_left (show Commute β b from hβb)).eq
  have hu' : β⁻¹ * u * β⁻¹⁻¹ ∈ L₂ := (c5_mem_shift h21).1 hu
  have hv' : β⁻¹ * v * β⁻¹⁻¹ ∈ L₃ := (c5_mem_shift h32).1 hv
  obtain ⟨c, -, hce⟩ := c5_conj3 hR (a₁ := 1) (a₂ := p) (a₃ := q) (a₁' := 1)
    (a₂' := β⁻¹ * u * β⁻¹⁻¹) (a₃' := β⁻¹ * v * β⁻¹⁻¹) (one_mem _) hp hq (one_mem _) hu' hv'
    (by simp) (by simp) hpq (by simp) (by simp) (c5_conj_comm huv) (by simp) hp3 hq3
    (by simp) (c5_conj_cube hu3) (c5_conj_cube hv3) (Or.inl ⟨rfl, one_mem _⟩)
    (Or.inr ⟨hpn, c5_notZ hβ' hun⟩) (Or.inr ⟨hqn, c5_notZ hβ' hvn⟩)
  refine ⟨β * c, ?_⟩
  simp only [one_mul] at hce
  calc β * c * (p * q) * (β * c)⁻¹ = β * (c * (p * q) * c⁻¹) * β⁻¹ := by group
    _ = u * v := by rw [hce]; group

theorem c5_d13 {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    {p q u v : G} (hp : p ∈ L₁) (hq : q ∈ L₃) (hu : u ∈ L₁) (hv : v ∈ L₂)
    (hpq : p * q = q * p) (huv : u * v = v * u) (hp3 : p ^ 3 = 1) (hq3 : q ^ 3 = 1)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hpn : p ∉ Subgroup.zpowers b)
    (hqn : q ∉ Subgroup.zpowers b) (hun : u ∉ Subgroup.zpowers b)
    (hvn : v ∉ Subgroup.zpowers b) : ∃ c : G, c * (p * q) * c⁻¹ = u * v := by
  obtain ⟨β, hβB, h21, h32, h13⟩ := hR.tri.cyc
  have hβb : β * b = b * β := r1_commute_of_B hR.tri.elemB hβB hR.tri.mem
  have hu' : β * u * β⁻¹ ∈ L₃ := (c5_mem_shift h13).2 hu
  have hv' : β * v * β⁻¹ ∈ L₁ := (c5_mem_shift h21).2 hv
  obtain ⟨c, -, hce⟩ := c5_conj3 hR (a₁ := p) (a₂ := 1) (a₃ := q) (a₁' := β * v * β⁻¹)
    (a₂' := 1) (a₃' := β * u * β⁻¹) hp (one_mem _) hq hv' (one_mem _) hu'
    (by simp) hpq (by simp) (by simp) (c5_conj_comm huv.symm) (by simp) hp3 (by simp) hq3
    (c5_conj_cube hv3) (by simp) (c5_conj_cube hu3) (Or.inr ⟨hpn, c5_notZ hβb hvn⟩)
    (Or.inl ⟨rfl, one_mem _⟩) (Or.inr ⟨hqn, c5_notZ hβb hun⟩)
  refine ⟨β⁻¹ * c, ?_⟩
  simp only [mul_one, one_mul] at hce
  calc β⁻¹ * c * (p * q) * (β⁻¹ * c)⁻¹ = β⁻¹ * (c * (p * q) * c⁻¹) * β⁻¹⁻¹ := by group
    _ = v * u := by rw [hce]; group
    _ = u * v := huv.symm

theorem c5_core {B : Subgroup G} {b : G} {L₁ L₂ L₃ R R₁ R₂ R₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) (hSy : SylData B b L₁ L₂ L₃ R R₁ R₂ R₃) {u v w : G} (hu : u ∈ R₁)
    (hv : v ∈ R₂) (hw : w ∈ R₃) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hnu : u ∉ Subgroup.zpowers b) (hnv : v ∉ Subgroup.zpowers b)
    (hnw : w ∉ Subgroup.zpowers b) {y : G} (hy : y ∈ R) :
    y ∈ Subgroup.zpowers b ∨ (∃ c : G, c * y * c⁻¹ = w) ∨ (∃ c : G, c * y * c⁻¹ = u * v) ∨
      (∃ c : G, c * y * c⁻¹ = w * (u * v)) := by
  classical
  have hT := hR.tri
  have hR1 : R₁ ≤ L₁ := by rw [hSy.h1]; exact inf_le_right
  have hR2 : R₂ ≤ L₂ := by rw [hSy.h2]; exact inf_le_right
  have hR3 : R₃ ≤ L₃ := by rw [hSy.h3]; exact inf_le_right
  have hP1 : IsPGroup 3 R₁ := hSy.hRp.to_le (by rw [hSy.h1]; exact inf_le_left)
  have hP2 : IsPGroup 3 R₂ := hSy.hRp.to_le (by rw [hSy.h2]; exact inf_le_left)
  have hP3 : IsPGroup 3 R₃ := hSy.hRp.to_le (by rw [hSy.h3]; exact inf_le_left)
  have hI1 := hR.syl₁ R₁ hR1 hP1 hSy.s1
  have hI2 := hR.syl₂ R₂ hR2 hP2 hSy.s2
  have hI3 := hR.syl₃ R₃ hR3 hP3 hSy.s3
  have hbR1 : b ∈ R₁ := rk5_ZR_le (by rw [hI1.2.2.2]; exact Subgroup.mem_zpowers b)
  have hbR2 : b ∈ R₂ := rk5_ZR_le (by rw [hI2.2.2.2]; exact Subgroup.mem_zpowers b)
  have hbR3 : b ∈ R₃ := rk5_ZR_le (by rw [hI3.2.2.2]; exact Subgroup.mem_zpowers b)
  have hZ1 : Subgroup.zpowers b ≤ R₁ := Subgroup.zpowers_le.2 hbR1
  have hZ2 : Subgroup.zpowers b ≤ R₂ := Subgroup.zpowers_le.2 hbR2
  have hZ3 : Subgroup.zpowers b ≤ R₃ := Subgroup.zpowers_le.2 hbR3
  have hC1 : ∀ a ∈ R₁, a ∈ Cb b := fun a ha => hT.comp₁.1 (hR1 ha)
  have hC2 : ∀ a ∈ R₂, a ∈ Cb b := fun a ha => hT.comp₂.1 (hR2 ha)
  have hC3 : ∀ a ∈ R₃, a ∈ Cb b := fun a ha => hT.comp₃.1 (hR3 ha)
  have hzc : ∀ z ∈ Subgroup.zpowers b, ∀ a ∈ Cb b, z * a = a * z :=
    fun z hz a ha => c5_zcomm hz (r1_ex_of_cb ha)
  have hy' : y ∈ (R₁ ⊔ R₂) ⊔ R₃ := hSy.hprod ▸ hy
  have hcm : ∀ x ∈ R₁ ⊔ R₂, ∀ z ∈ R₃, x * z = z * x := by
    have : R₁ ⊔ R₂ ≤ Subgroup.centralizer (R₃ : Set G) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 (fun h hh => (hSy.c13 a ha h hh).symm))
        (fun a ha => Subgroup.mem_centralizer_iff.2 (fun h hh => (hSy.c23 a ha h hh).symm))
    intro x hx z hz
    exact ((Subgroup.mem_centralizer_iff.1 (this hx)) z hz).symm
  obtain ⟨p12, hp12, a₃, ha₃, rfl⟩ := r1_mem_sup_of_comm hcm hy'
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := r1_mem_sup_of_comm hSy.c12 hp12
  have e1 : a₁ ^ 3 = 1 := hI1.2.2.1 a₁ ha₁
  have e2 : a₂ ^ 3 = 1 := hI2.2.2.1 a₂ ha₂
  have e3 : a₃ ^ 3 = 1 := hI3.2.2.1 a₃ ha₃
  have c12 := hSy.c12 a₁ ha₁ a₂ ha₂
  have c13 := hSy.c13 a₁ ha₁ a₃ ha₃
  have c23 := hSy.c23 a₂ ha₂ a₃ ha₃
  have huv : u * v = v * u := hSy.c12 u hu v hv
  have huw : u * w = w * u := hSy.c13 u hu w hw
  have hvw : v * w = w * v := hSy.c23 v hv w hw
  by_cases z₁ : a₁ ∈ Subgroup.zpowers b <;> by_cases z₂ : a₂ ∈ Subgroup.zpowers b <;>
    by_cases z₃ : a₃ ∈ Subgroup.zpowers b
  ·
    exact Or.inl (mul_mem (mul_mem z₁ z₂) z₃)
  ·
    have hp : a₁ * a₂ * a₃ ∈ R₃ := mul_mem (mul_mem (hZ3 z₁) (hZ3 z₂)) ha₃
    have hpn : a₁ * a₂ * a₃ ∉ Subgroup.zpowers b := fun h => z₃ (by
      have : a₃ = (a₁ * a₂)⁻¹ * (a₁ * a₂ * a₃) := by group
      rw [this]; exact mul_mem (inv_mem (mul_mem z₁ z₂)) h)
    exact Or.inr (Or.inl (c5_s3 hR (hR3 hp) (hR3 hw) (hI3.2.2.1 _ hp) hw3 hpn hnw))
  ·
    have hp : a₁ * a₂ * a₃ ∈ R₂ := mul_mem (mul_mem (hZ2 z₁) ha₂) (hZ2 z₃)
    have hpn : a₁ * a₂ * a₃ ∉ Subgroup.zpowers b := fun h => z₂ (by
      have : a₂ = a₁⁻¹ * (a₁ * a₂ * a₃) * a₃⁻¹ := by group
      rw [this]; exact mul_mem (mul_mem (inv_mem z₁) h) (inv_mem z₃))
    exact Or.inr (Or.inl (c5_s2 hR (hR2 hp) (hR3 hw) (hI2.2.2.1 _ hp) hw3 hpn hnw))
  ·
    have hp : a₁ * a₂ ∈ R₂ := mul_mem (hZ2 z₁) ha₂
    have hpn : a₁ * a₂ ∉ Subgroup.zpowers b := fun h => z₂ (by
      have : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
      rw [this]; exact mul_mem (inv_mem z₁) h)
    have hcom : (a₁ * a₂) * a₃ = a₃ * (a₁ * a₂) :=
      (Commute.mul_left (show Commute a₁ a₃ from hzc a₁ z₁ a₃ (hC3 a₃ ha₃))
        (show Commute a₂ a₃ from c23)).eq
    exact Or.inr (Or.inr (Or.inl (c5_d23 hR (hR2 hp) (hR3 ha₃) (hR1 hu) (hR2 hv) hcom huv
      (hI2.2.2.1 _ hp) e3 hu3 hv3 hpn z₃ hnu hnv)))
  ·
    have hp : a₁ * a₂ * a₃ ∈ R₁ := mul_mem (mul_mem ha₁ (hZ1 z₂)) (hZ1 z₃)
    have hpn : a₁ * a₂ * a₃ ∉ Subgroup.zpowers b := fun h => z₁ (by
      have : a₁ = (a₁ * a₂ * a₃) * (a₂ * a₃)⁻¹ := by group
      rw [this]; exact mul_mem h (inv_mem (mul_mem z₂ z₃)))
    exact Or.inr (Or.inl (c5_s1 hR (hR1 hp) (hR3 hw) (hI1.2.2.1 _ hp) hw3 hpn hnw))
  ·
    have hp : a₁ * a₂ ∈ R₁ := mul_mem ha₁ (hZ1 z₂)
    have hpn : a₁ * a₂ ∉ Subgroup.zpowers b := fun h => z₁ (by
      have : a₁ = (a₁ * a₂) * a₂⁻¹ := by group
      rw [this]; exact mul_mem h (inv_mem z₂))
    have hcom : (a₁ * a₂) * a₃ = a₃ * (a₁ * a₂) :=
      (Commute.mul_left (show Commute a₁ a₃ from c13)
        (show Commute a₂ a₃ from hzc a₂ z₂ a₃ (hC3 a₃ ha₃))).eq
    exact Or.inr (Or.inr (Or.inl (c5_d13 hR (hR1 hp) (hR3 ha₃) (hR1 hu) (hR2 hv) hcom huv
      (hI1.2.2.1 _ hp) e3 hu3 hv3 hpn z₃ hnu hnv)))
  ·
    have hp : a₁ * a₃ ∈ R₁ := mul_mem ha₁ (hZ1 z₃)
    have hpn : a₁ * a₃ ∉ Subgroup.zpowers b := fun h => z₁ (by
      have : a₁ = (a₁ * a₃) * a₃⁻¹ := by group
      rw [this]; exact mul_mem h (inv_mem z₃))
    have hcom : (a₁ * a₃) * a₂ = a₂ * (a₁ * a₃) :=
      (Commute.mul_left (show Commute a₁ a₂ from c12)
        (show Commute a₃ a₂ from hzc a₃ z₃ a₂ (hC2 a₂ ha₂))).eq
    have hx : a₁ * a₂ * a₃ = (a₁ * a₃) * a₂ := by
      calc a₁ * a₂ * a₃ = a₁ * (a₂ * a₃) := mul_assoc _ _ _
        _ = a₁ * (a₃ * a₂) := by rw [← hzc a₃ z₃ a₂ (hC2 a₂ ha₂)]
        _ = (a₁ * a₃) * a₂ := (mul_assoc _ _ _).symm
    obtain ⟨c, hc⟩ := c5_d12 hR (hR1 hp) (hR2 ha₂) (hR1 hu) (hR2 hv) hcom huv
      (hI1.2.2.1 _ hp) e2 hu3 hv3 hpn z₂ hnu hnv
    exact Or.inr (Or.inr (Or.inl ⟨c, by rw [hx]; exact hc⟩))
  ·
    obtain ⟨c, -, hc⟩ := c5_conj3 hR (hR1 ha₁) (hR2 ha₂) (hR3 ha₃) (hR1 hu) (hR2 hv) (hR3 hw)
      c12 c13 c23 huv huw hvw e1 e2 e3 hu3 hv3 hw3 (Or.inr ⟨z₁, hnu⟩) (Or.inr ⟨z₂, hnv⟩)
      (Or.inr ⟨z₃, hnw⟩)
    refine Or.inr (Or.inr (Or.inr ⟨c, ?_⟩))
    rw [hc]
    calc u * v * w = u * (v * w) := mul_assoc _ _ _
      _ = u * (w * v) := by rw [hvw]
      _ = (u * w) * v := (mul_assoc _ _ _).symm
      _ = (w * u) * v := by rw [huw]
      _ = w * (u * v) := mul_assoc _ _ _

theorem three_classes {B : Subgroup G} {b : G} {L₁ L₂ L₃ R R₁ R₂ R₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) (hSy : SylData B b L₁ L₂ L₃ R R₁ R₂ R₃) {u v w : G} (hu : u ∈ R₁)
    (hv : v ∈ R₂) (hw : w ∈ R₃) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hnu : u ∉ Subgroup.zpowers b) (hnv : v ∉ Subgroup.zpowers b)
    (hnw : w ∉ Subgroup.zpowers b) {x : G} (hx : x ∈ L₁ ⊔ L₂ ⊔ L₃) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    x ∈ Subgroup.zpowers b ∨ (∃ c : G, c * x * c⁻¹ = w) ∨ (∃ c : G, c * x * c⁻¹ = u * v) ∨
      (∃ c : G, c * x * c⁻¹ = w * (u * v)) := by
  classical
  have hT := hR.tri
  have hKC : L₁ ⊔ L₂ ⊔ L₃ ≤ Cb b := sup_le (sup_le hT.comp₁.1 hT.comp₂.1) hT.comp₃.1
  let P : Sylow 3 ↥(L₁ ⊔ L₂ ⊔ L₃) := Sylow.ofCard (R.subgroupOf (L₁ ⊔ L₂ ⊔ L₃)) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSy.hRK).toEquiv]; exact hSy.hRs)
  obtain ⟨g, hg⟩ := t1_sylow_conj P (⟨x, hx⟩ : ↥(L₁ ⊔ L₂ ⊔ L₃))
    ⟨1, by apply Subtype.ext; simpa using hx3⟩
  have hxR : (g : G)⁻¹ * x * g ∈ R := hg
  have hgb : (g : G)⁻¹ * b = b * (g : G)⁻¹ :=
    (Commute.inv_left (show Commute (g : G) b from r1_ex_of_cb (hKC g.2))).eq
  rcases c5_core hR hSy hu hv hw hu3 hv3 hw3 hnu hnv hnw hxR with h | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · left
    by_contra hxz
    exact c5_notZ hgb hxz (by simpa using h)
  · exact Or.inr (Or.inl ⟨c * (g : G)⁻¹, by rw [← hc]; group⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c * (g : G)⁻¹, by rw [← hc]; group⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c * (g : G)⁻¹, by rw [← hc]; group⟩))

end C5Sec

section B1Sec

private theorem b1_exists_elem {H : Subgroup G} (h5 : 5 ≤ CFSG.Open.pRank 3 H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ ∃ k, 5 ≤ k ∧ Nat.card E = 3 ^ k := by
  unfold CFSG.Open.pRank at h5
  rcases Set.eq_empty_or_nonempty
    {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} with h | hne
  · rw [h] at h5
    simp at h5
  · have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ k} := by
      refine ⟨Nat.card G, ?_⟩
      rintro j ⟨F, -, -, hj⟩
      have h1 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
      have h2 : j < 3 ^ j := Nat.lt_pow_self (by norm_num)
      rw [hj] at h1
      exact (h2.le).trans h1
    obtain ⟨E, hE, hel, hc⟩ := Nat.sSup_mem hne hbdd
    exact ⟨E, hE, hel, _, h5, hc⟩

private theorem b1_transfer (c : G) {H H' : Subgroup G} (hHH' : ∀ h ∈ H, c * h * c⁻¹ ∈ H')
    (h5 : 5 ≤ CFSG.Open.pRank 3 H) : 5 ≤ CFSG.Open.pRank 3 H' := by
  obtain ⟨E, hEH, hel, k, hk5, hk⟩ := b1_exists_elem h5
  let φ : G →* G := (MulAut.conj c).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj c).injective
  haveI := hel.1
  have hcard : Nat.card (E.map φ) = 3 ^ k := by
    rw [← hk]; exact (Nat.card_congr (E.equivMapOfInjective φ hφ).toEquiv).symm
  refine le_trans hk5 (rk5_le_pRank (E := E.map φ) ?_ ⟨inferInstance, ?_⟩ hcard)
  · rintro _ ⟨e, he, rfl⟩
    exact hHH' e (hEH he)
  · rintro _ ⟨e, he, rfl⟩
    show (c * e * c⁻¹) ^ 3 = 1
    rw [conj_pow, hel.2 e he]
    group

private theorem b1_uv_ne_one {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G}
    (hR : RData B b L₁ L₂ L₃) {u v : G} (hu : u ∈ L₁) (hv : v ∈ L₂) (hu3 : u ^ 3 = 1)
    (hnu : u ∉ Subgroup.zpowers b) : u * v ≠ 1 := by
  intro h1
  have hT := hR.tri
  have hbC : b ∈ Cb b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hb3 : b ^ (3 ^ 1) = 1 := by simpa using hT.elemB.2 b hT.mem
  have hu1 : u ∈ Cb b := hT.comp₁.1 hu
  have hv1 : v ∈ Cb b := hT.comp₂.1 hv
  have hcomm : ∀ x ∈ barX 3 (Cb b) L₁, ∀ y ∈ barX 3 (Cb b) L₂, x * y = y * x := by
    have hle := barX_le_centralizer (p := 3) (C := Cb b) (S := L₁) (T := L₂) (by
      intro s hs t ht _ _
      exact commutator_le_gLAPPrimeCore_of_ne Nat.prime_three hT.comp₁ hT.comp₂ hT.ne₁₂
        (Subgroup.commutator_mem_commutator hs ht))
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) y hy).symm
  have hAB : mkX (Cb b) u hu1 * mkX (Cb b) v hv1 = 1 := by
    unfold mkX
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have : (⟨u, hu1⟩ * ⟨v, hv1⟩ : ↥(Cb b)) = 1 := Subtype.ext h1
    rw [this]
    exact one_mem _
  have hA2 : mkX (Cb b) u hu1 ∈ barX 3 (Cb b) L₂ := by
    have : mkX (Cb b) u hu1 = (mkX (Cb b) v hv1)⁻¹ := eq_inv_of_mul_eq_one_left hAB
    rw [this]
    exact inv_mem (r1_mem_barX hv1 hv)
  have hcm : mkX (Cb b) u hu1 ∈ barX 3 (Cb b) (Subgroup.zpowers b) :=
    (hR.fus₂.Zcenter _).2 ⟨hA2, fun q hq => hcomm _ (r1_mem_barX hu1 hu) q hq⟩
  have hpow : mkX (Cb b) u hu1 ^ 3 = 1 := by
    rw [r1_mkX_pow]
    simp only [hu3]
    rfl
  exact hnu (q_mem_zpowers_of_bar hbC hb3 hu1 (k := 1) (by simpa using hu3)
    (Subgroup.mem_centralizer_singleton_iff.1 hu1) hcm)

private theorem b1_cb {x z c : G} (hc : c * x * c⁻¹ = z) :
    ∀ h ∈ Cb z, c⁻¹ * h * c⁻¹⁻¹ ∈ Cb x := by
  intro h hh
  have hh' : h * z = z * h := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hh
    first | exact this | exact this.symm
  subst hc
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have e : c⁻¹ * h * c⁻¹⁻¹ * x = x * (c⁻¹ * h * c⁻¹⁻¹) := by
    calc c⁻¹ * h * c⁻¹⁻¹ * x = c⁻¹ * (h * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * h) * c := by rw [hh']
      _ = x * (c⁻¹ * h * c⁻¹⁻¹) := by group
  first | exact e | exact e.symm

theorem b1_rank5 (i183 : Input18_3_4) (i145 : Input14_5) (i302 : Input30_2) (i1433 : Input14_33)
    (iD4 : InputD4) {m : ℕ} (hS : GLStanding G m 3) (hrk4 : GLATwoLocalRank 3 G = 4)
    {B : Subgroup G} {b : G} {L₁ L₂ L₃ : Subgroup G} (hR : RData B b L₁ L₂ L₃)
    (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃) (hbK : b ∈ bClosure B L₁) (hnY : ¬ Y2 b L₁ L₂) :
    ∀ x ∈ bClosure B L₁, x ≠ 1 → x ^ 3 = 1 → 5 ≤ CFSG.Open.pRank 3 (Cb x) := by
  have hT := hR.tri
  obtain ⟨R, R₁, R₂, R₃, hSy⟩ := three_sylow hT hK hbK
  obtain ⟨u, v, t, Q₁, Q, huR, hvR, hnu, hnv, hu3, hv3, ht, ht2, hty, hQ₁, htQ₁, hinv, hQle,
    hQn, hQ27, hQna, hQ3, hQZ, hnil⟩ := exists_config i302 hR hSy
  have hu : u ∈ L₁ := by rw [hSy.h1] at huR; exact huR.2
  have hv : v ∈ L₂ := by rw [hSy.h2] at hvR; exact hvR.2
  have hc : u * v = v * u := hSy.c12 u huR v hvR
  have hy3 : (u * v) ^ 3 = 1 := by
    rw [(show Commute u v from hc).mul_pow, hu3, hv3, one_mul]
  have hy1 : u * v ≠ 1 := b1_uv_ne_one hR hu hv hu3 hnu
  have hnot : b ∉ oPrimePOf 3 (Cb (u * v)) := fun h => hnY (y2_of_exists hR hu hv hc hu3 hv3 hnu hnv h)
  have hR₁R : R₁ ≤ R := by rw [hSy.h1]; exact inf_le_left
  have hR₂R : R₂ ≤ R := by rw [hSy.h2]; exact inf_le_left
  have hR₃R : R₃ ≤ R := by rw [hSy.h3]; exact inf_le_left
  have hQ₁p : IsPGroup 3 Q₁ := by
    refine IsPGroup.to_le hSy.hRp ?_
    rw [hQ₁]
    exact inf_le_left.trans (sup_le hR₁R hR₂R)
  have hQ₁C : Q₁ ≤ Cb b ⊓ Cb (u * v) := by
    rw [hQ₁]
    refine le_inf ?_ inf_le_right
    refine inf_le_left.trans (sup_le ?_ ?_)
    · rw [hSy.h1]; exact inf_le_right.trans hT.comp₁.1
    · rw [hSy.h2]; exact inf_le_right.trans hT.comp₂.1
  have hyQ₁ : u * v ∈ Q₁ := by
    rw [hQ₁]
    exact ⟨mul_mem (le_sup_left (a := R₁) (b := R₂) huR) (le_sup_right (a := R₁) (b := R₂) hvR),
      Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨Js, hJs, hbJ, hD4, hL₃⟩ := b1_d4 i183 i145 i1433 hS hrk4 hR hu hv hc hu3 hv3 hnu hnv
    hnot ht ht2 hty hQ₁p hQ₁C hyQ₁ htQ₁ hinv hQle hQn hQ27 hQna hQ3 hQZ hnil
  obtain ⟨hrkJ, hrkY⟩ := d4_rank iD4 hS hy3 hy1 hJs hD4
  obtain ⟨hc27, hna, hex, hZ⟩ := hR.syl₃ R₃ (by rw [hSy.h3]; exact inf_le_right)
    (IsPGroup.to_le hSy.hRp hR₃R) hSy.s3
  obtain ⟨w, hwR, w', hw'R, hww⟩ : ∃ w ∈ R₃, ∃ w' ∈ R₃, w * w' ≠ w' * w := by
    by_contra hcon
    push_neg at hcon
    exact hna hcon
  have hnw : w ∉ Subgroup.zpowers b := by
    intro hw
    rw [← hZ] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    apply hww
    rw [← hzw]
    exact (Subgroup.mem_center_iff.1 hz ⟨w', hw'R⟩ |> congrArg Subtype.val).symm
  have hw3 : w ^ 3 = 1 := hex w hwR
  have hw1 : w ≠ 1 := fun h => hnw (h ▸ one_mem _)
  have hwL₃ : w ∈ L₃ := by rw [hSy.h3] at hwR; exact hwR.2
  have hwy : w * (u * v) = (u * v) * w := by
    rw [← mul_assoc, (hSy.c13 u huR w hwR).symm, mul_assoc, (hSy.c23 v hvR w hwR).symm,
      ← mul_assoc]
  have hwJ : w ∈ Js := hL₃ w hwL₃ hwy hw3
  have hrkw : 5 ≤ CFSG.Open.pRank 3 (Cb w) := by
    refine b1_transfer 1 (fun h hh => ?_) (hrkJ w hwJ hw1 hw3)
    simpa using hh.2
  have hrkwy : 5 ≤ CFSG.Open.pRank 3 (Cb (w * (u * v))) := by
    refine b1_transfer 1 (fun h hh => ?_) (hrkJ w hwJ hw1 hw3)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hh.1
    have h2 := Subgroup.mem_centralizer_singleton_iff.1 hh.2
    simp only [one_mul, inv_one, mul_one]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← mul_assoc, h2, mul_assoc, h1, ← mul_assoc]
  have hb3 : b ^ 3 = 1 := hT.elemB.2 b hT.mem
  have hrkb : 5 ≤ CFSG.Open.pRank 3 (Cb b) := by
    refine b1_transfer 1 (fun h hh => ?_) (hrkJ b hbJ hT.ne_one hb3)
    simpa using hh.2
  intro x hx hx1 hx3
  rw [hK] at hx
  rcases three_classes hR hSy huR hvR hwR hu3 hv3 hw3 hnu hnv hnw hx hx3 hx1 with
    hxb | ⟨c, hc'⟩ | ⟨c, hc'⟩ | ⟨c, hc'⟩
  · refine b1_transfer 1 (fun h hh => ?_) hrkb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxb
    simp only [one_mul, inv_one, mul_one]
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    exact (Commute.zpow_right (show Commute h b from Subgroup.mem_centralizer_singleton_iff.1 hh) j).eq
  · exact b1_transfer _ (b1_cb hc') hrkw
  · exact b1_transfer _ (b1_cb hc') hrkY
  · exact b1_transfer _ (b1_cb hc') hrkwy

end B1Sec

section NcSec

theorem exists_noncentral_of_four (i112f : Input11_2Four) {m : ℕ} (hS : GLStanding G m 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L₁ L₂ L₃ : Subgroup G}
    (hT : Tri B b L₁ L₂ L₃) (hK : bClosure B L₁ = L₁ ⊔ L₂ ⊔ L₃) (hbK : b ∈ bClosure B L₁) :
    ∃ a : barOf 3 L₁, a ^ 3 = 1 ∧ a ∉ Subgroup.center (barOf 3 L₁) := by
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hb3 : b ^ 3 = 1 := hBel.2 b hT.mem
  have hb1 : b ≠ 1 := hT.ne_one
  have hBC : B ≤ Cb b := le_centralizer_of_mem hBel hT.mem
  have hrk : GLATwoLocalRank 3 ↥(Cb b) ≤ CFSG.Open.pRank 3 B := by
    have := hS.simple
    exact (glaTwoLocalRank_subgroup_le Nat.prime_three (Cb b)).trans
      (hS.rank_eq.le.trans (hS.le_pRank' hB))
  obtain ⟨β, hβB, hβ2, -, -⟩ := hT.cyc
  have hBn : ¬ B ≤ Subgroup.normalizer (L₁ : Set G) := fun h =>
    hT.ne₁₂ (hβ2.trans (gLBConj_eq_of_mem_normalizer (h hβB))).symm
  have hbC : b ∈ Cb b := by rw [Subgroup.mem_centralizer_singleton_iff]
  have hcen : Subgroup.center ↥(barX 3 (Cb b) (bClosure B L₁)) ≠ ⊥ := by
    intro h
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b)) ⟨b, hbC⟩ ∈
        barX 3 (Cb b) (bClosure B L₁) :=
      ⟨⟨b, hbC⟩, (Subgroup.mem_subgroupOf).2 hbK, rfl⟩
    have hz : (⟨_, hmem⟩ : ↥(barX 3 (Cb b) (bClosure B L₁))) ∈
        Subgroup.center ↥(barX 3 (Cb b) (bClosure B L₁)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective g.1
      show g.1 * QuotientGroup.mk ⟨b, hbC⟩ = QuotientGroup.mk ⟨b, hbC⟩ * g.1
      rw [← hx]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 x.2
    rw [h, Subgroup.mem_bot] at hz
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cb b)) ⟨b, hbC⟩ = 1 :=
      congrArg Subtype.val hz
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hd : orderOf (⟨b, hbC⟩ : ↥(Cb b)) ∣ Nat.card (GLAPPrimeCore 3 ↥(Cb b)) :=
      Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_mk, orderOf_eq_prime hb3 hb1] at hd
    have := Nat.Coprime.eq_one_of_dvd (coprime_card_gLAPPrimeCore_aux 3 ↥(Cb b)) hd
    omega
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥L₁))
  obtain ⟨-, hRna, hR3, -, -⟩ :=
    i112f G m hS (Cb b) B L₁ hBel hBC hrk hT.comp₁ hBn hcen R
  have hN := coprime_card_gLAPPrimeCore_aux 3 ↥L₁
  have hRp : IsPGroup 3 (R : Subgroup ↥L₁) := R.isPGroup'
  have hex : ∃ r ∈ (R : Subgroup ↥L₁), ∃ s ∈ (R : Subgroup ↥L₁), r * s ≠ s * r := by
    by_contra hcon
    push Not at hcon
    exact hRna hcon
  obtain ⟨r, hr, s, hs, hrs⟩ := hex
  have hne : (QuotientGroup.mk r : barOf 3 L₁) * QuotientGroup.mk s ≠
      QuotientGroup.mk s * QuotientGroup.mk r := by
    intro h1
    apply hrs
    have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L₁) (r * s * (s * r)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      show QuotientGroup.mk r * QuotientGroup.mk s *
        (QuotientGroup.mk s * QuotientGroup.mk r)⁻¹ = 1
      rw [h1]
      simp
    have := t2_inj_of_coprime _ hN _ hRp
      ((R : Subgroup ↥L₁).mul_mem ((R : Subgroup ↥L₁).mul_mem hr hs)
        ((R : Subgroup ↥L₁).inv_mem ((R : Subgroup ↥L₁).mul_mem hs hr))) h2
    exact mul_inv_eq_one.1 this
  by_cases hrc : (QuotientGroup.mk r : barOf 3 L₁) ∈ Subgroup.center (barOf 3 L₁)
  · refine ⟨QuotientGroup.mk s, ?_, ?_⟩
    · rw [← QuotientGroup.mk_pow, hR3 s hs, QuotientGroup.mk_one]
    · intro hsc
      apply hne
      exact (Subgroup.mem_center_iff.1 hsc) (QuotientGroup.mk r)
  · refine ⟨QuotientGroup.mk r, ?_, hrc⟩
    rw [← QuotientGroup.mk_pow, hR3 r hr, QuotientGroup.mk_one]

end NcSec


section MainA

@[expose] def Lemma27a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) → b ∈ bClosure B L →
      (∃ D : Subgroup G, Lemma24Setup 3 B D b L ∧ Lemma24Conclusion B D b L ∧
          barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)) →
      ∀ Lᵢ Lⱼ : Subgroup G, IsBConjugate B L Lᵢ → IsBConjugate B L Lⱼ →
        ∀ x ∈ Lᵢ ⊔ Lⱼ, orderOf x = 3 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G))

theorem lemma27a_of_inputs (h25 : Lemma25Strong) (i112 : Input11_2Full)
    (i112f : Input11_2Four) (i302 : Input30_2) (i183 : Input18_3_4) (i145 : Input14_5)
    (i253 : Input25_3) : Lemma27a := by
  intro G _ _ m hS B hB b hbB hb1 L hL hn hbK hA Li Lj hLi hLj x hx hx3
  obtain ⟨D, hset, hconc, hZ⟩ := hA
  have hB1 : IsBOneMax 3 B := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax
    (by norm_num) hB
  obtain ⟨L₂, L₃, hT, hK, hall⟩ := exists_tri i112 hS hB1 hbB hb1 hL hn
  have htype : IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L) := by
    rcases hconc.2.1 with ⟨K, hF, hfin, -, he⟩ | ⟨K, hF, hfin, q, hq, -, he⟩
    · exact Or.inl ⟨K, hF, hfin, he⟩
    · exact Or.inr ⟨K, hF, hfin, q, hq, he⟩
  have hR := rData_of_inputs i112f i302 hS hB1 hT hK hbK hZ htype
  obtain ⟨u, hu, v, hv, hc, hu3, hv3, hnu, hnv, hgood⟩ := case_a_good h25 hS hR hset hconc hZ
  have hY := y2_of_exists hR hu hv hc hu3 hv3 hnu hnv hgood
  exact r_main i183 i145 i253 hS hR hY (hall Li hLi) (hall Lj hLj) hx hx3

end MainA

section MainB

@[expose] def Lemma27b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) → b ∈ bClosure B L →
      (GLATwoLocalRank 3 G = 4 ∧ (IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L)) ∧
          (Nat.card L).factorization 3 = 3 ∧ IsWeaklyBalancedWrt 3 2 B) →
      ∀ Lᵢ Lⱼ : Subgroup G, IsBConjugate B L Lᵢ → IsBConjugate B L Lⱼ →
        ∀ x ∈ Lᵢ ⊔ Lⱼ, orderOf x = 3 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G))

theorem lemma27b_of_inputs (i112 : Input11_2Full) (i112f : Input11_2Four) (i112t : Input11_2Two)
    (iB0 : InputB0T) (i302 : Input30_2) (i183 : Input18_3_4) (i145 : Input14_5)
    (i253 : Input25_3) (i1433 : Input14_33) (iD4 : InputD4) : Lemma27b := by
  intro G _ _ m hS B hB b hbB hb1 L hL hn hbK hbd Li Lj hLi hLj x hx hx3
  obtain ⟨hrk4, htype, -, hwb⟩ := hbd
  have hB1 : IsBOneMax 3 B := CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax
    (by norm_num) hB
  obtain ⟨L₂, L₃, hT, hK, hall⟩ := exists_tri i112 hS hB1 hbB hb1 hL hn
  have hX3 := exists_noncentral_of_four i112f hS hB1 hT hK hbK
  by_cases hZ : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)
  · have hR := rData_of_inputs i112f i302 hS hB1 hT hK hbK hZ htype
    have hY : Y2 b L L₂ := by
      by_contra hnY
      exact b_final i112t iB0 hS hrk4 hB hwb hT hK hbK hX3
        (b1_rank5 i183 i145 i302 i1433 iD4 hS hrk4 hR hK hbK hnY)
    exact r_main i183 i145 i253 hS hR hY (hall Li hLi) (hall Lj hLj) hx hx3
  · exact (b_final i112t iB0 hS hrk4 hB hwb hT hK hbK hX3
      (b2_rank5 i112 i112f hS hB1 hT hK hbK hZ)).elim

end MainB

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  Lemma27Ns

theorem lemma27_of_inputs (_h24 : Lemma24) (h25 : Lemma25Strong) (i112 : Input11_2Full)
    (i112f : Input11_2Four) (i112t : Input11_2Two) (iB0 : InputB0T) (i302 : Input30_2)
    (i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4) (i145 : Input14_5)
    (i253 : Input25_3) (i1433 : Input14_33)
    (iD4 : InputD4) : Lemma27 := by
  intro G _ _ m hS B hB b hb hb1 L hL hn hbK hcase Li Lj hLi hLj x hx hx3
  rcases hcase with hA | hb'
  · exact lemma27a_of_inputs h25 i112 i112f i302 i183 i145 i253 G m hS B hB b hb hb1 L hL hn hbK
      hA Li Lj hLi hLj x hx hx3
  · exact lemma27b_of_inputs i112 i112f i112t iB0 i302 i183 i145 i253 i1433 iD4 G m hS B hB b hb
      hb1 L hL hn hbK hb' Li Lj hLi hLj x hx hx3

end CFSG.HardMathSupport.Solomon.LocalBalance
