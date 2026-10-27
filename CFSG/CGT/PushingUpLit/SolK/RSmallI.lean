module

public import CFSG.CGT.PushingUpLit.SolK.RSmallPerm

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

theorem inv_conj_pow {G : Type*} [Group G] (g t : G) (k : ℕ) :
    (g⁻¹ * t * g) ^ k = g⁻¹ * t ^ k * g := by
  induction k with
  | zero => group
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem mem_M_of_comm_R {r c : G} (hr : r ∈ rOf M X) (hr1 : r ≠ 1) (hc : c * r * c⁻¹ = r) :
    c ∈ M := by
  have hZ2 : IsPGroup 2 (Subgroup.zpowers r) := by
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' M ⟨r, hr.1⟩
    have hj' : r ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hord : orderOf r ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hZ : Subgroup.zpowers r ≠ ⊥ := by simpa [Subgroup.zpowers_eq_bot] using hr1
  have hloc : IsPLocal 2 (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) :=
    ⟨_, hZ, hZ2, rfl⟩
  have hCN : Subgroup.centralizer ((Subgroup.zpowers r : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hxr : ∀ x ∈ X, x * r * x⁻¹ = r := fun x hx => by
    have := Subgroup.mem_centralizer_iff.1 hr.2 x hx
    rw [this]
    group
  have hXN : X ≤ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G) := fun x hx =>
    hCN (mem_centralizer_zpowers_iff.2 (hxr x hx))
  have hle := local_le_of_unique S.hyp.unique hloc hXN
  exact hle (hCN (mem_centralizer_zpowers_iff.2 hc))

theorem conjR_normal_of_comm (g : G) {t c τ : G} (ht : t ∈ conjSubgroup g (rOf M X)) (ht1 : t ≠ 1)
    (hc : c * t * c⁻¹ = t) (hτ : τ ∈ conjSubgroup g (rOf M X)) :
    c * τ * c⁻¹ ∈ conjSubgroup g (rOf M X) := by
  have hr : g⁻¹ * t * g ∈ rOf M X := mem_conjSubgroup.1 ht
  have hr1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply ht1
    have : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hc' : (g⁻¹ * c * g) * (g⁻¹ * t * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * t * g := by
    calc (g⁻¹ * c * g) * (g⁻¹ * t * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * t * c⁻¹) * g := by group
      _ = g⁻¹ * t * g := by rw [hc]
  have hcM : g⁻¹ * c * g ∈ M := S.mem_M_of_comm_R hr hr1 hc'
  have hτR : g⁻¹ * τ * g ∈ rOf M X := mem_conjSubgroup.1 hτ
  have h1 := S.R_normalized hcM hτR
  refine mem_conjSubgroup.2 ?_
  have e : g⁻¹ * (c * τ * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * τ * g) * (g⁻¹ * c * g)⁻¹ := by group
  rw [e]
  exact h1

omit [Finite G] S in
theorem conjR_two (g : G) {t : G} (ht : t ∈ conjSubgroup g (rOf M X)) :
    ∃ j : ℕ, t ^ (2 ^ j) = 1 := by
  have h0 : g⁻¹ * t * g ∈ rOf M X := mem_conjSubgroup.1 ht
  obtain ⟨j, hj⟩ := isPGroup_pCoreOf' M ⟨g⁻¹ * t * g, h0.1⟩
  refine ⟨j, ?_⟩
  have h1 : (g⁻¹ * t * g) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  rw [inv_conj_pow] at h1
  have : t ^ (2 ^ j) = g * (g⁻¹ * t ^ (2 ^ j) * g) * g⁻¹ := by group
  rw [this, h1]
  group

theorem false_of_caseI (hP : TightDataPlus S) {g : G} (hTM : conjSubgroup g (rOf M X) ≤ M)
    (hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M = ⊥) (hcard : 3 ≤ Nat.card ↥(rOf M X)) :
    False := by
  classical
  set R := rOf M X with hR
  set T := conjSubgroup g R with hT
  have hnorm : ∀ t ∈ T, t ≠ 1 → ∀ c : G, c * t * c⁻¹ = t → ∀ τ ∈ T, c * τ * c⁻¹ ∈ T :=
    fun t ht ht1 c hc τ hτ => S.conjR_normal_of_comm g ht ht1 hc hτ
  have hT2 : ∀ t ∈ T, ∃ j : ℕ, t ^ (2 ^ j) = 1 := fun t ht => conjR_two g ht
  have hinj : ∀ τ : ↥M, (τ : G) ∈ T → S.θ τ = 1 → τ = 1 := by
    intro τ hτ h1
    have hQ : (τ : G) ∈ pCoreOf 2 M := hP.ker_two τ h1 (hT2 τ hτ)
    have : (τ : G) ∈ T ⊓ pCoreOf 2 M := ⟨hτ, hQ⟩
    rw [hTQ] at this
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  set T' : Subgroup ↥M := T.subgroupOf M with hT'
  have hmemT' : ∀ τ : ↥M, τ ∈ T' ↔ (τ : G) ∈ T := fun τ => Subgroup.mem_subgroupOf
  set P : Subgroup (Perm (Fin (2 * n + 1))) := T'.map S.θ with hPdef
  have hP2 : IsPGroup 2 P := by
    intro σ
    obtain ⟨τ, hτ, hτσ⟩ := σ.2
    obtain ⟨j, hj⟩ := hT2 τ ((hmemT' τ).1 hτ)
    refine ⟨j, Subtype.ext ?_⟩
    show (σ : Perm (Fin (2 * n + 1))) ^ (2 ^ j) = 1
    rw [← hτσ, ← map_pow]
    have : τ ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
    rw [this, map_one]
  have hcardP : 3 ≤ Nat.card P := by
    have h1 : Nat.card T' ≤ Nat.card P := by
      refine Nat.card_le_card_of_injective
        (fun τ : ↥T' => (⟨S.θ (τ : ↥M), Subgroup.mem_map_of_mem _ τ.2⟩ : ↥P)) ?_
      intro τ₁ τ₂ h
      have h' : S.θ (τ₁ : ↥M) = S.θ (τ₂ : ↥M) := congrArg Subtype.val h
      have hq : S.θ ((τ₁ : ↥M) * (τ₂ : ↥M)⁻¹) = 1 := by
        rw [map_mul, map_inv, h', mul_inv_cancel]
      have hmem : ((τ₁ : ↥M) * (τ₂ : ↥M)⁻¹ : ↥M) ∈ T' := T'.mul_mem τ₁.2 (T'.inv_mem τ₂.2)
      have h0 := hinj _ ((hmemT' _).1 hmem) hq
      exact Subtype.ext (mul_inv_eq_one.1 h0)
    have h2 : Nat.card T' = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv
    have h3 : Nat.card T = Nat.card R := Subgroup.card_map_of_injective (MulAut.conj g).injective
    omega
  have hd : Odd (2 * n + 1) := odd_two_mul_add_one n
  obtain ⟨σ, hσP, τ, hτP, hσ1, hτ1, v, hv1, hv2⟩ := exists_fixed_ne hd P hP2 hcardP
  obtain ⟨a, ha, haσ⟩ := Subgroup.mem_map.1 hσP
  obtain ⟨b, hb, hbτ⟩ := Subgroup.mem_map.1 hτP
  have haT : (a : G) ∈ T := (hmemT' a).1 ha
  have hbT : (b : G) ∈ T := (hmemT' b).1 hb
  have ha1 : (a : G) ≠ 1 := by
    intro h
    apply hσ1
    rw [← haσ]
    have : a = 1 := Subtype.ext h
    rw [this, map_one]
  obtain ⟨w, hw⟩ := S.D.β.surjective v
  have hwQ : (w : G) ∈ pCoreOf 2 M := S.W_le_Q w.2
  have hwM : ∀ m : ↥M, (m : G) * (w : G) * (m : G)⁻¹ ∈ S.D.W := fun m => S.W_normalized m.2 w.2
  have hcomm_iff : ∀ m : ↥M, (m : G) * (w : G) * (m : G)⁻¹ = (w : G) ↔
      coreAct (2 * n + 1) (S.θ m) v = v := by
    intro m
    have hspec := S.θ_spec m w (hwM m)
    rw [hw] at hspec
    constructor
    · intro h
      have : (⟨(m : G) * (w : G) * (m : G)⁻¹, hwM m⟩ : ↥S.D.W) = w := Subtype.ext h
      rw [this, hw] at hspec
      exact hspec.symm
    · intro h
      rw [h] at hspec
      have h2 : (⟨(m : G) * (w : G) * (m : G)⁻¹, hwM m⟩ : ↥S.D.W) = w :=
        S.D.β.injective (hspec.trans hw.symm)
      exact congrArg Subtype.val h2
  have hcomm : ∀ q ∈ pCoreOf 2 M, ∀ t ∈ T, t ≠ 1 → q * t * q⁻¹ = t →
      ∀ τ' ∈ T, q * τ' * q⁻¹ = τ' := by
    intro q hq t ht ht1 hqt τ' hτ'
    have h1 : q * τ' * q⁻¹ ∈ T := hnorm t ht ht1 q hqt τ' hτ'
    have hτ'M : τ' ∈ M := hTM hτ'
    have h2 : τ' * q⁻¹ * τ'⁻¹ ∈ pCoreOf 2 M :=
      pCoreOf_normalized M hτ'M ((pCoreOf 2 M).inv_mem hq)
    have h3 : (q * τ' * q⁻¹) * τ'⁻¹ ∈ T := T.mul_mem h1 (T.inv_mem hτ')
    have h4 : (q * τ' * q⁻¹) * τ'⁻¹ ∈ pCoreOf 2 M := by
      have : (q * τ' * q⁻¹) * τ'⁻¹ = q * (τ' * q⁻¹ * τ'⁻¹) := by group
      rw [this]
      exact (pCoreOf 2 M).mul_mem hq h2
    have h5 : (q * τ' * q⁻¹) * τ'⁻¹ ∈ T ⊓ pCoreOf 2 M := ⟨h3, h4⟩
    rw [hTQ] at h5
    have h6 := Subgroup.mem_bot.1 h5
    calc q * τ' * q⁻¹ = (q * τ' * q⁻¹ * τ'⁻¹) * τ' := by group
      _ = τ' := by rw [h6, one_mul]
  have hac : (a : G) * (w : G) * (a : G)⁻¹ = (w : G) := by
    rw [hcomm_iff a, haσ]
    exact hv1
  have hwa : (w : G) * (a : G) * (w : G)⁻¹ = (a : G) := by
    have h' : (a : G) * (w : G) = (w : G) * (a : G) := mul_inv_eq_iff_eq_mul.1 hac
    calc (w : G) * (a : G) * (w : G)⁻¹ = (a : G) * (w : G) * (w : G)⁻¹ := by rw [← h']
      _ = (a : G) := by group
  have hwb : (w : G) * (b : G) * (w : G)⁻¹ = (b : G) := hcomm w hwQ a haT ha1 hwa b hbT
  have hbw : (b : G) * (w : G) * (b : G)⁻¹ = (w : G) := by
    have h' : (w : G) * (b : G) = (b : G) * (w : G) := mul_inv_eq_iff_eq_mul.1 hwb
    calc (b : G) * (w : G) * (b : G)⁻¹ = (w : G) * (b : G) * (b : G)⁻¹ := by rw [← h']
      _ = (w : G) := by group
  apply hv2
  rw [← hbτ]
  exact (hcomm_iff b).1 hbw

theorem rSmall_of_caseII (hP : TightDataPlus S)
    (hII : ∀ g : G, g ∉ M → conjSubgroup g (rOf M X) ≤ M → conjSubgroup g (rOf M X) ≠ rOf M X →
      conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M ≠ ⊥ → RSmall S) : RSmall S := by
  by_cases hbot : rOf M X = ⊥
  · unfold RSmall
    rw [hbot, Subgroup.card_bot]
    norm_num
  · obtain ⟨g, hgM', hgne⟩ := hP.nonweak hbot
    have hgn : g ∉ M := by
      intro hg
      apply hgne
      apply le_antisymm
      · intro x hx
        have h1 := mem_conjSubgroup.1 hx
        have h2 := S.R_normalized hg h1
        have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rwa [this] at h2
      · intro x hx
        refine mem_conjSubgroup.2 ?_
        have h2 := S.R_normalized (M.inv_mem hg) hx
        simpa using h2
    by_cases hTQ : conjSubgroup g (rOf M X) ⊓ pCoreOf 2 M = ⊥
    · by_contra hRS
      unfold RSmall at hRS
      exact S.false_of_caseI hP hgM' hTQ (by omega)
    · exact hII g hgn hgM' hgne hTQ

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
