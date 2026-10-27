module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Tstar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem pow_conj_of_inverts {B : Subgroup G} {g : G} (hg : ∀ b ∈ B, g * b * g⁻¹ = b⁻¹) :
    ∀ k : ℕ, ∀ b ∈ B, g ^ (2 * k) * b * (g ^ (2 * k))⁻¹ = b ∧
      g ^ (2 * k + 1) * b * (g ^ (2 * k + 1))⁻¹ = b⁻¹ := by
  have hbi : ∀ b ∈ B, g * b⁻¹ * g⁻¹ = b := by
    intro b hb
    have h := hg b hb
    calc g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ := by group
      _ = b := by rw [h, inv_inv]
  intro k
  induction k with
  | zero =>
    intro b hb
    exact ⟨by simp, by simpa using hg b hb⟩
  | succ k ih =>
    intro b hb
    obtain ⟨-, h2⟩ := ih b hb
    have e1 : g ^ (2 * (k + 1)) * b * (g ^ (2 * (k + 1)))⁻¹ =
        g * (g ^ (2 * k + 1) * b * (g ^ (2 * k + 1))⁻¹) * g⁻¹ := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ']
      group
    have e2 : g ^ (2 * (k + 1) + 1) * b * (g ^ (2 * (k + 1) + 1))⁻¹ =
        g * (g * (g ^ (2 * k + 1) * b * (g ^ (2 * k + 1))⁻¹) * g⁻¹) * g⁻¹ := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, pow_succ', pow_succ']
      group
    refine ⟨?_, ?_⟩
    · rw [e1, h2, hbi b hb]
    · rw [e2, h2, hbi b hb, hg b hb]

theorem exists_two_element_inverting {B : Subgroup G} {g : G} (hg : ∀ b ∈ B, g * b * g⁻¹ = b⁻¹) :
    ∃ m a : ℕ, (g ^ m) ^ (2 ^ a) = 1 ∧ ∀ b ∈ B, g ^ m * b * (g ^ m)⁻¹ = b⁻¹ := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨m, a, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  · obtain ⟨j, rfl⟩ := hm
    intro b hb
    exact (pow_conj_of_inverts hg j b hb).2

theorem mem_normalizer_of_inverts {B : Subgroup G} {g : G} (hg : ∀ b ∈ B, g * b * g⁻¹ = b⁻¹) :
    g ∈ Subgroup.normalizer (B : Set G) := by
  have hinv : ∀ c ∈ B, g⁻¹ * c * g = c⁻¹ := by
    intro c hc
    have h := hg c⁻¹ (B.inv_mem hc)
    rw [inv_inv] at h
    calc g⁻¹ * c * g = g⁻¹ * (g * c⁻¹ * g⁻¹) * g := by rw [h]
      _ = c⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [hg b hb]
    exact B.inv_mem hb
  · intro hb
    have h := hinv _ hb
    have e : b = (g⁻¹ * (g * b * g⁻¹) * g) := by group
    rw [e, h]
    exact B.inv_mem hb

theorem mem_normalizer_commutator_of {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((⁅A, C⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hC ⊢
  rw [Subgroup.map_commutator, hA, hC]

theorem exists_sylow_coe {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hT
  rw [Subgroup.relIndex_top_right] at hidx
  exact ⟨h2.toSylow hidx, IsPGroup.toSylow_coe h2 hidx⟩

theorem mem_smul_sylow_iff {Q : Sylow 2 G} {x y : G} :
    y ∈ ((x • Q : Sylow 2 G) : Subgroup G) ↔ x⁻¹ * y * x ∈ (Q : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hy
    exact ⟨x⁻¹ * y * x, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem map_conj_eq_of_centralizes {P D : Subgroup G} (hDP : D ≤ P) {c : G}
    (hc : c ∈ Subgroup.centralizer (P : Set G)) : D.map (MulAut.conj c).toMonoidHom = D := by
  have hfix : ∀ y ∈ D, (MulAut.conj c).toMonoidHom y = y := by
    intro y hy
    have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.1 hc y (hDP hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hcy]
    group
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hfix y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem pRank_le_one_of_card_eq {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hcard : Nat.card P = p) :
    CFSG.Open.pRank p P ≤ 1 := by
  unfold CFSG.Open.pRank
  by_cases hs : {k | ∃ E : Subgroup G, E ≤ P ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k}.Nonempty
  · refine csSup_le hs ?_
    rintro k ⟨E, hEP, -, hEk⟩
    have hle : Nat.card E ≤ Nat.card P := Subgroup.card_le_of_le hEP
    rw [hEk, hcard] at hle
    by_contra hk
    have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p < p ^ 2 := by
      have := hp.two_le
      nlinarith
    omega
  · rw [Set.not_nonempty_iff_eq_empty.1 hs, csSup_empty]
    exact bot_le

theorem map_eq_one_of_sq {H : Type*} [Group H] (f : G →* H) {b : G} (hb : Odd (orderOf b))
    (h2 : f b ^ 2 = 1) : f b = 1 := by
  have h1 : orderOf (f b) ∣ orderOf b := orderOf_map_dvd f b
  have h3 : orderOf (f b) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf (f b) ∣ Nat.gcd (orderOf b) 2 := Nat.dvd_gcd h1 h3
  have h5 : Nat.gcd (orderOf b) 2 = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_two_left).2 hb
  rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

end CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open NotIsPrimePowTwoPowSubOne

variable {G : Type} [Group G] [Finite G]

theorem not_isPrimePow_two_pow_sub_one {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) : ¬ IsPrimePow (2 ^ e - 1) := by
  intro hr
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  set D₀ : Subgroup G := ⁅B, P⁆ with hD₀
  set act := DeltaConjugationAction.act (p := p) hP ρ with hact
  have h520 := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  have hD₀Δ : D₀ ∈ Delta p P ρ := h520.1
  set d₀ : Delta p P ρ := ⟨D₀, hD₀Δ⟩ with hd₀
  have hTab : IsMulCommutative (Tstar P T) :=
    (sylow_image_directProduct_and_isMulCommutative_and_centralizer_scalar hc hr).1.2.2.2
  rw [Tstar_eq hP] at hTab
  have hTcomm : ∀ u ∈ T, ∀ v ∈ T, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    intro u hu v hv
    have hφ : FaithfulPImageVocabulary.conjOnP P hP u * FaithfulPImageVocabulary.conjOnP P hP v =
        FaithfulPImageVocabulary.conjOnP P hP v * FaithfulPImageVocabulary.conjOnP P hP u :=
      congrArg Subtype.val (hTab.is_comm.comm ⟨_, ⟨u, hu, rfl⟩⟩ ⟨_, ⟨v, hv, rfl⟩⟩)
    have hφ' : FaithfulPImageVocabulary.conjOnP P hP (u * v * u⁻¹ * v⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφ]
      group
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥P => ((φ ⟨x, hx⟩ : ↥P) : G)) hφ'
    simp only [FaithfulPImageVocabulary.conjOnP_apply, MulAut.one_apply] at h1
    calc x * (u * v * u⁻¹ * v⁻¹) = ((u * v * u⁻¹ * v⁻¹) * x * (u * v * u⁻¹ * v⁻¹)⁻¹) *
          (u * v * u⁻¹ * v⁻¹) := by rw [h1]
      _ = (u * v * u⁻¹ * v⁻¹) * x := by group
  have hactC : ∀ c ∈ Subgroup.centralizer (P : Set G), act c = 1 := by
    intro c hc'
    refine Equiv.ext fun E => Subtype.ext ?_
    rw [hact, DeltaConjugationAction.apply_eq]
    exact map_conj_eq_of_centralizes E.2.1 hc'
  have hCn : (Subgroup.centralizer (P : Set G)).Normal := by
    haveI := hP
    exact Subgroup.normal_centralizer
  obtain ⟨g, hg⟩ := ActorInversion.inverted hc
  obtain ⟨m, a, hga, hgB⟩ := exists_two_element_inverting hg
  set g₂ : G := g ^ m with hg₂
  have hg₂2 : IsPGroup 2 (Subgroup.zpowers g₂) := by
    have hdvd : orderOf g₂ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hga
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hg₂d₀ : act g₂ d₀ = d₀ := by
    have hB : g₂ ∈ Subgroup.normalizer (B : Set G) := mem_normalizer_of_inverts hgB
    have hPn : g₂ ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hP]
      exact Subgroup.mem_top _
    have hD : g₂ ∈ Subgroup.normalizer (D₀ : Set G) := mem_normalizer_commutator_of hB hPn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hD
    refine Subtype.ext ?_
    rw [hact, DeltaConjugationAction.apply_eq]
    exact hD
  obtain ⟨T₀, hT₀⟩ := exists_sylow_coe hc.faithfulBinaryIrreducibleAction.sylow
  have hS2 : IsPGroup 2 (twoCoreCommutator T B) :=
    ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype).to_le
      (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  obtain ⟨T₁, hT₁⟩ := hS2.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hg₂2.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G T₁ Q
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G T₀ Q
  have hg₂Q : g₂ ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g₂)
  have htrans : ∀ E : Delta p P ρ, ∃ s ∈ (Q : Subgroup G), act s d₀ = E := by
    intro E
    obtain ⟨s₀, hs₀, hE⟩ := h520.2.2.2.2.1 (act y⁻¹ d₀).1 (act y⁻¹ d₀).2 (act y⁻¹ E).1 (act y⁻¹ E).2
    refine ⟨y * s₀ * y⁻¹, ?_, ?_⟩
    · rw [← hy, mem_smul_sylow_iff]
      have : y⁻¹ * (y * s₀ * y⁻¹) * y = s₀ := by group
      rw [this]
      exact hT₁ hs₀
    · have hE' : act s₀ (act y⁻¹ d₀) = act y⁻¹ E := by
        refine Subtype.ext ?_
        rw [hact, DeltaConjugationAction.apply_eq]
        exact hE.symm
      calc act (y * s₀ * y⁻¹) d₀ = act y (act s₀ (act y⁻¹ d₀)) := by
            rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        _ = act y (act y⁻¹ E) := by rw [hE']
        _ = E := by rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have hQcomm : ∀ u ∈ (Q : Subgroup G), ∀ v ∈ (Q : Subgroup G),
      u * v * u⁻¹ * v⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    intro u hu v hv
    rw [← hx, mem_smul_sylow_iff, hT₀] at hu hv
    have h := hTcomm _ hu _ hv
    have e : u * v * u⁻¹ * v⁻¹ =
        x * ((x⁻¹ * u * x) * (x⁻¹ * v * x) * (x⁻¹ * u * x)⁻¹ * (x⁻¹ * v * x)⁻¹) * x⁻¹ := by group
    rw [e]
    exact hCn.conj_mem _ h x
  have hg₂1 : act g₂ = 1 := by
    refine Equiv.ext fun E => ?_
    obtain ⟨s, hs, rfl⟩ := htrans E
    have hc' := hQcomm _ (Subgroup.inv_mem _ hg₂Q) _ (Subgroup.inv_mem _ hs)
    rw [inv_inv, inv_inv] at hc'
    have e : g₂ * s = s * g₂ * (g₂⁻¹ * s⁻¹ * g₂ * s) := by group
    rw [Equiv.Perm.one_apply, ← Equiv.Perm.mul_apply, ← map_mul, e, map_mul, map_mul, hactC _ hc', mul_one,
      Equiv.Perm.mul_apply, hg₂d₀]
  have hB1 : ∀ b ∈ B, act b = 1 := by
    intro b hb
    have hbo : Odd (orderOf b) := by
      have h1 : orderOf (⟨b, hb⟩ : B) ∣ Nat.card B := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hc.oddPrimeClassTwoAction.setting.oddOrder h1
    refine map_eq_one_of_sq act hbo ?_
    have h1 : act b⁻¹ = act b := by
      rw [← hgB b hb, map_mul, map_mul, hg₂1, map_inv, hg₂1]
      group
    rw [map_inv] at h1
    rw [pow_two]
    nth_rewrite 2 [← h1]
    exact mul_inv_cancel _
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    have he : 2 < e := hc.oddPrimeClassTwoAction.two_lt
    have hne : 2 ^ e - 1 ≠ 1 := by
      have : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
      omega
    obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hrB : r ∈ piOf B := by
      rw [hc.oddPrimeClassTwoAction.pi_eq]
      exact ⟨hrp, hrd⟩
    have hrB' : r ∣ Nat.card B := hrB.2
    by_contra hall
    push Not at hall
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hall
    rw [hbot, Subgroup.card_bot, Nat.dvd_one] at hrB'
    exact hrp.one_lt.ne' hrB'
  have hΔ : ∀ E : Delta p P ρ, E = d₀ := by
    intro E
    by_contra hE
    have hEne : (E : Subgroup G) ≠ D₀ := fun h => hE (Subtype.ext h)
    have hbN : b ∈ Subgroup.normalizer ((E : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have h1 := congrArg Subtype.val (Equiv.ext_iff.1 (hB1 b hb) E)
      rw [hact, DeltaConjugationAction.apply_eq] at h1
      exact h1
    exact h520.2.2.2.1 b hb hb1 E E.2 hEne hbN
  have hint := isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc
  have htop : fixedSubmodule ρ D₀ = ⊤ := by
    have h := hint.submodule_iSup_eq_top
    refine eq_top_iff.2 ?_
    rw [← h]
    refine iSup_le fun E => ?_
    rw [hΔ E]
  have hD₀bot : D₀ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    apply hc.faithfulBinaryIrreducibleAction.faithful
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ fixedSubmodule ρ D₀ := by rw [htop]; exact Submodule.mem_top
    exact (Representation.mem_invariants _ v).1 hv ⟨d, hd⟩
  have hcard : Nat.card P = p := by
    have h := hD₀Δ.2.1
    rw [hD₀bot, Subgroup.relIndex_bot_left] at h
    exact h
  have hle := pRank_le_one_of_card_eq hc.oddPrimeClassTwoAction.setting.prime hcard
  have hgt := hc.faithfulBinaryIrreducibleAction.rank_gt
  omega

end CFSG.LocalAnalysis.RankThreeUC.Section5
