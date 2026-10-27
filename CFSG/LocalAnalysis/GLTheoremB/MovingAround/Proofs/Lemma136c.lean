module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma136c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut localDeltaIn)

@[expose] def Input19_1_O2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], CFSG.Open.IsKProper G →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (k : ℕ), 1 ≤ k →
    ∀ (X D : Subgroup G), X ≠ ⊤ → IsEkIn p k X D →
      (∀ K : Subgroup G, GLAPComponent p X K →
          localDeltaTwoIn X D ≤ Subgroup.normalizer (K : Set G)) ∧
      (∀ x ∈ localDeltaTwoIn X D, ∀ y ∈ pPrimePCore p X, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X) ∧
      (∀ K : Subgroup G, GLAPComponent p X K → ¬ ⁅K, localDeltaTwoIn X D⁆ ≤ GLAPPrimeCoreOf p X →
        D ≤ Subgroup.normalizer (K : Set G) ∧ centBar p D K = ⊥ ∧ ¬ IsCompLocallyOTwoBalanced p k D K)

@[expose] def Alt19_16a (p k : ℕ) (K : Type) [Group K] [Finite K] (B : Subgroup (MulAut K)) (m r : ℕ) : Prop :=
  (r = 2 ∨ r = 4) ∧ 0 < m ∧
    ∃ (n : ℕ), n = m * p ^ k + r ∧ ∃ (e : K ≃* alternatingGroup (Fin n))
      (σ : MulAut K →* Equiv.Perm (Fin n)),
      (∀ (φ : MulAut K) (x : K), (e (φ x) : Equiv.Perm (Fin n)) = σ φ * e x * (σ φ)⁻¹) ∧
      ∃ D : Subgroup (MulAut K), IsEkIn p 2 B D ∧
        (∃ F : Finset (Fin n), F.card = r ∧ (∀ i ∈ F, ∀ φ ∈ D, σ φ i = i) ∧
          (∀ i ∉ F, ∀ φ ∈ D, φ ≠ 1 → σ φ i ≠ i)) ∧
        Nat.card (localDeltaIn p (⊤ : Subgroup (MulAut K)) D) = r

@[expose] def Alt19_16b (p k : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  p = 5 ∧ k = 2 ∧ IsSporType .Fi22 K

@[expose] def Alt19_16c (p k : ℕ) (K : Type) [Group K] [Finite K] (B : Subgroup (MulAut K)) : Prop :=
  ∃ q₀ q : ℕ, ((∃ n : ℕ, (2 ^ n - 1).Prime ∧ q₀ = 2 ^ n - 1) ∨
      (∃ n : ℕ, (2 ^ (2 ^ n) + 1).Prime ∧ q₀ = 2 ^ (2 ^ n) + 1) ∨ q₀ = 2 ∨ q₀ = 9) ∧
    q = q₀ ^ 2 ∧ p ∣ q - 1 ∧ k = 2 ∧ IsLpType p q (K ⧸ Subgroup.center K) ∧
    B ≤ innerAut K

@[expose] def Alt19_16 (p k : ℕ) (K : Type) [Group K] [Finite K] (B : Subgroup (MulAut K)) : Prop :=
  (∃ (m r : ℕ), Alt19_16a p k K B m r) ∨ Alt19_16b p k K ∨ Alt19_16c p k K B

@[expose] def Input19_16 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → GLAPPrimeCore p K = ⊥ →
    ∀ (k : ℕ), 2 ≤ k → ∀ B : Subgroup (MulAut K), IsEkIn p k ⊤ B →
      IsLocallyOTwoBalanced p k B ∨ Alt19_16 p k K B

section Transport

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround

variable {G : Type} [Group G] [Finite G]

theorem l136c_centralizer_ne_top [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {d : G}
    (hd : d ≠ 1) : Subgroup.centralizer ({d} : Set G) ≠ ⊤ := by
  intro htop
  have hdz : d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({d} : Set G) := by rw [htop]; exact Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_iff] at hg
    exact (hg d (Set.mem_singleton d)).symm
  have hZ : Subgroup.center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact absurd (h ▸ hdz) (by simpa using hd)
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  apply hab
  have ha : a ∈ Subgroup.center G := by rw [hZ]; exact Subgroup.mem_top a
  exact (Subgroup.mem_center_iff.1 ha b).symm

theorem l136c_isEkIn_autBar {p k : ℕ} {X B K : Subgroup G} (hB : IsEkIn p k X B)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hcent : centBar p B K = ⊥) :
    IsEkIn p k ⊤ (autBar p B K) := by
  obtain ⟨-, hEA, hcard⟩ := hB
  have hinj : Function.Injective ((barAut p K).comp
      ((B ⊓ Subgroup.normalizer (K : Set G)).subgroupOf (Subgroup.normalizer (K : Set G))).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxB : (x : G) ∈ B := by
      have := x.2
      rw [Subgroup.mem_subgroupOf] at this
      exact (Subgroup.mem_inf.1 this).1
    have hmem : (x : G) ∈ centBar p B K := by
      rw [centBar, Subgroup.mem_inf]
      refine ⟨Subgroup.mem_map.2 ⟨x.1, ?_, rfl⟩, hxB⟩
      exact hx
    rw [hcent, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  set N : Subgroup G := Subgroup.normalizer (K : Set G)
  set H : Subgroup ↥N := (B ⊓ N).subgroupOf N with hH
  set g : ↥H →* MulAut (↥K ⧸ GLAPPrimeCore p ↥K) := (barAut p K).comp H.subtype with hg
  have hrng : g.range = autBar p B K := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hBN : B ⊓ N = B := inf_eq_left.2 hBK
  have hmemB : ∀ a : ↥H, (a.1 : G) ∈ B := fun a => (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 a.2)).1
  have hBc : ∀ u v : G, u ∈ B → v ∈ B → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val (hEA.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcardH : Nat.card ↥H = Nat.card B := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ N ≤ N)).toEquiv, hBN]
  have hcardImg : Nat.card ↥(autBar p B K) = Nat.card ↥H := by
    rw [← hrng]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine ⟨le_top, ⟨⟨?_⟩, ?_⟩, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a', ha'⟩ := MonoidHom.mem_range.1 (show (a : MulAut (↥K ⧸ GLAPPrimeCore p ↥K)) ∈ g.range by
      rw [hrng]; exact a.2)
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.1 (show (b : MulAut (↥K ⧸ GLAPPrimeCore p ↥K)) ∈ g.range by
      rw [hrng]; exact b.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hBc _ _ (hmemB a') (hmemB b')
  · intro x hx
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (show x ∈ g.range by rw [hrng]; exact hx)
    rw [← ha, ← map_pow]
    have h1 : a ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      exact hEA.2 _ (hmemB a)
    rw [h1, map_one]
  · rw [hcardImg, hcardH, hcard]

end Transport

@[expose] def CentralizerFStarFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Y : Subgroup G), Y ≤ X → IsPGroup 2 ↥Y →
    (∀ K : Subgroup G, GLAPComponent 3 X K → Y ≤ Subgroup.normalizer (K : Set G)) →
    (∀ y ∈ Y, ∀ z ∈ pPrimePCore 3 X, y * z * y⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 X) →
    (∀ K : Subgroup G, GLAPComponent 3 X K → ⁅K, Y⁆ ≤ GLAPPrimeCoreOf 3 X) →
    Y ≤ GLAPPrimeCoreOf 3 X

@[expose] def IIHardPrinted {G : Type} [Group G] [Finite G] (B L D : Subgroup G) {d : G} (hN : D ≤ Subgroup.normalizer (L : Set G))
    (hd : d ∈ D) (b : G) (B1 : Subgroup G) : Prop :=
  (b ∈ B ⊓ L) ∧ (∀ hb : b ∈ Subgroup.normalizer (L : Set G),
      barAut 3 L ⟨b, hb⟩ = barAut 3 L ⟨d, hN hd⟩) ∧
    B1 ≤ B ⊓ L ∧ B1 ⊓ Subgroup.zpowers b = ⊥ ∧ B1 ⊔ Subgroup.zpowers b = B ⊓ L

@[expose] noncomputable def bStarOf {G : Type} [Group G] [Finite G] (B L D : Subgroup G) (b : G) : Subgroup G :=
  Subgroup.zpowers b ⊔ (centBar 3 B L ⊓ Subgroup.centralizer (D : Set G))

@[expose] noncomputable def s1Of {G : Type} [Group G] [Finite G] (B L D : Subgroup G) (d b : G) (B1 : Subgroup G) : Subgroup G :=
  ⁅B1, Subgroup.centralizer (bStarOf B L D b : Set G) ⊓ pCoreOf 2 (L ⊓ Cg d)⁆

@[expose] def IIHardSetupData {G : Type} [Group G] [Finite G] (B L D : Subgroup G) (d : G) (Bs S1 : Subgroup G) :
    Prop :=
  Bs ≤ B ⊓ Cg d ∧ (∃ r : ℕ, 2 ≤ r ∧ IsEkIn 3 r (Cg d) Bs) ∧ S1 ≤ localDeltaTwoIn (Cg d) Bs ∧
    IsPGroup 2 ↥S1 ∧ S1 ≤ Cg d ∧ pCoreOf 2 (L ⊓ Cg d) ≤ S1 ⊔ GLAPPrimeCoreOf 3 (Cg d)

@[expose] def IIHardReduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
      ∃ (b : G) (B1 : Subgroup G), IIHardPrinted B L D hN hd b B1 ∧
        IIHardSetupData B L D d (bStarOf B L D b) (s1Of B L D d b B1)

@[expose] def IIHardCases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    (hN : D ≤ Subgroup.normalizer (L : Set G)) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1),
    pCoreOf 2 (fixSub (barAut 3 L ⟨d, hN hd⟩)) ≠ ⊥ →
    ∀ (b : G) (B1 : Subgroup G), IIHardPrinted B L D hN hd b B1 →
    IIHardSetupData B L D d (bStarOf B L D b) (s1Of B L D d b B1) →
    ∀ (r : ℕ), 2 ≤ r → IsEkIn 3 r (Cg d) (bStarOf B L D b) →
    ∀ (K : Subgroup G), GLAPComponent 3 (Cg d) K →
      ¬ ⁅K, s1Of B L D d b B1⁆ ≤ GLAPPrimeCoreOf 3 (Cg d) →
      bStarOf B L D b ≤ Subgroup.normalizer (K : Set G) → centBar 3 (bStarOf B L D b) K = ⊥ →
      ¬ Alt19_16 3 r (barOf 3 K) (autBar 3 (bStarOf B L D b) K)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma136c

end
