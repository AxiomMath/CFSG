module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar
import all CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5
  CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar
open scoped commutatorElement

section Generic

variable {H : Type} [Group H]

theorem le_normalizer_of_forall_conj_mem {X N : Subgroup H} (h : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    X ≤ Subgroup.normalizer (N : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h x hx n, fun hn => ?_⟩
  have h1 := h x⁻¹ (X.inv_mem hx) _ hn
  have e : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
  rwa [e] at h1

theorem mul_comm_of_mem_center {S : Subgroup H} {z : H} (hz : z ∈ (Subgroup.center S).map S.subtype)
    {ψ : H} (hψ : ψ ∈ S) : z * ψ = ψ * z := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨ψ, hψ⟩)).symm

theorem forall_eq_or_forall_eq_inv [Finite H] {Q : Subgroup H} (hQ : (Nat.card Q).Prime) (z : MulAut H)
    (hz2 : ∀ x, z (z x) = x) (hzQ : ∀ x ∈ Q, z x ∈ Q) :
    (∀ x ∈ Q, z x = x) ∨ (∀ x ∈ Q, z x = x⁻¹) := by
  have hgen : ∀ a ∈ Q, a ≠ 1 → ∀ x ∈ Q, x ∈ Subgroup.zpowers a := by
    intro a ha ha1 x hx
    have hord : orderOf a = Nat.card Q := by
      rcases (Nat.dvd_prime hQ).mp (Subgroup.orderOf_dvd_natCard Q ha) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ha1
      · exact h
    have heq : Subgroup.zpowers a = Q :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha) (by rw [Nat.card_zpowers, hord])
    rw [heq]
    exact hx
  obtain ⟨g, hgQ, hg1⟩ : ∃ g ∈ Q, g ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr h
    rw [hbot, Subgroup.card_bot] at hQ
    exact Nat.not_prime_one hQ
  have hcomm : g * z g = z g * g := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen g hgQ hg1 (z g) (hzQ g hgQ))
    rw [← hj]
    exact (Commute.self_zpow g j).eq
  by_cases ha : g * z g = 1
  · right
    have hzg : z g = g⁻¹ := eq_inv_of_mul_eq_one_right ha
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen g hgQ hg1 x hx)
    rw [map_zpow, hzg, inv_zpow]
  · left
    have hza : z (g * z g) = g * z g := by
      rw [map_mul, hz2]
      exact hcomm.symm
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen _ (Q.mul_mem hgQ (hzQ g hgQ)) ha x hx)
    rw [map_zpow, hza]

theorem false_of_forall_apply_apply_eq_inv [Finite H] (hcomm : ∀ a b : H, a * b = b * a) {D : Subgroup H}
    (hD : D.index.Prime) (hD2 : D.index ≠ 2) {u₁ u₂ : MulAut H} (hu₁ : ∀ x, x ∈ D ↔ u₁ x ∈ D)
    (hu₂ : ∀ x, x ∈ D ↔ u₂ x ∈ D) (hinv : ∀ x, u₁ (u₂ x) = (u₂ (u₁ x))⁻¹) : False := by
  haveI : D.Normal := ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  haveI : Fact D.index.Prime := ⟨hD⟩
  haveI : IsCyclic (H ⧸ D) := isCyclic_of_prime_card (p := D.index) D.index_eq_card.symm
  obtain ⟨m₁, hm₁⟩ := MonoidHom.map_cyclic (QuotientGroup.map D D u₁.toMonoidHom fun x hx => (hu₁ x).mp hx)
  obtain ⟨m₂, hm₂⟩ := MonoidHom.map_cyclic (QuotientGroup.map D D u₂.toMonoidHom fun x hx => (hu₂ x).mp hx)
  have h₁ : ∀ x : H, ((u₁ x : H) : H ⧸ D) = (x : H ⧸ D) ^ m₁ := fun x => hm₁ x
  have h₂ : ∀ x : H, ((u₂ x : H) : H ⧸ D) = (x : H ⧸ D) ^ m₂ := fun x => hm₂ x
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : H, x₀ ∉ D := by
    by_contra h
    push Not at h
    have htop : D = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, Subgroup.index_top] at hD
    exact Nat.not_prime_one hD
  set y : H ⧸ D := (x₀ : H ⧸ D) with hy
  have hy1 : y ≠ 1 := fun h => hx₀ ((QuotientGroup.eq_one_iff x₀).mp h)
  have hyord : orderOf y = D.index := by
    have hdvd : orderOf y ∣ D.index := by
      rw [D.index_eq_card]
      exact orderOf_dvd_natCard y
    rcases (Nat.dvd_prime hD).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have key : y ^ (m₂ * m₁) = (y ^ (m₁ * m₂))⁻¹ := by
    have h := congrArg (fun w : H => (w : H ⧸ D)) (hinv x₀)
    simp only [QuotientGroup.mk_inv, h₁, h₂, ← zpow_mul] at h
    exact h
  have hsq : y ^ (2 * (m₁ * m₂)) = 1 := by
    have h : y ^ (m₂ * m₁) * y ^ (m₁ * m₂) = 1 := by rw [key, inv_mul_cancel]
    rwa [← zpow_add, mul_comm m₂ m₁, ← two_mul] at h
  have hpZ : Prime (D.index : ℤ) := Nat.prime_iff_prime_int.mp hD
  have hdvd : (D.index : ℤ) ∣ 2 * (m₁ * m₂) := by
    rw [← hyord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hsq
  rcases hpZ.dvd_or_dvd hdvd with h2 | h12
  · have h2' : D.index ∣ 2 := by exact_mod_cast h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h | h
    · rw [h] at hD
      exact Nat.not_prime_one hD
    · exact hD2 h
  · have hpow : ∀ m : ℤ, (D.index : ℤ) ∣ m → y ^ m = 1 := fun m hm =>
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hyord]; exact hm)
    rcases hpZ.dvd_or_dvd h12 with h1 | h2
    · have h : ((u₁ x₀ : H) : H ⧸ D) = 1 := by rw [h₁, ← hy]; exact hpow m₁ h1
      exact hx₀ ((hu₁ x₀).mpr ((QuotientGroup.eq_one_iff _).mp h))
    · have h : ((u₂ x₀ : H) : H ⧸ D) = 1 := by rw [h₂, ← hy]; exact hpow m₂ h2
      exact hx₀ ((hu₂ x₀).mpr ((QuotientGroup.eq_one_iff _).mp h))

theorem map_eq_self_of_forall_apply_eq_inv {z : MulAut H} (hz : ∀ x, z x = x⁻¹) (K : Subgroup H) :
    K.map z.toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show z y ∈ K
    rw [hz]
    exact K.inv_mem hy
  · intro hx
    refine ⟨x⁻¹, K.inv_mem hx, ?_⟩
    show z x⁻¹ = x
    rw [hz, inv_inv]

end Generic

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem mem_Sstar_iff (hP : P.Normal) {ψ : MulAut ↥P} :
    ψ ∈ Sstar P T B ↔ ∃ s ∈ twoCoreCommutator T B, conjOnP P hP s = ψ := by
  rw [show Sstar P T B = (twoCoreCommutator T B).map (conjOnP P hP) from (image_eq P hP _).symm,
    Subgroup.mem_map]

theorem map_subtype_map_conjOnP (hP : P.Normal) (g : G) (K : Subgroup ↥P) :
    (K.map (conjOnP P hP g).toMonoidHom).map P.subtype =
      (K.map P.subtype).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_conjOnP_eq_iff (hP : P.Normal) (g : G) {D : Subgroup G} (hDP : D ≤ P) :
    (D.subgroupOf P).map (conjOnP P hP g).toMonoidHom = D.subgroupOf P ↔
      g ∈ Subgroup.normalizer (D : Set G) := by
  have hN : g ∈ Subgroup.normalizer (D : Set G) ↔ D.map (MulAut.conj g).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq
  rw [hN]
  have hD : (D.subgroupOf P).map P.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDP
  constructor
  · intro h
    have h1 : ((D.subgroupOf P).map (conjOnP P hP g).toMonoidHom).map P.subtype =
        (D.subgroupOf P).map P.subtype := by rw [h]
    rwa [map_subtype_map_conjOnP, hD] at h1
  · intro h
    apply Subgroup.map_injective P.subtype_injective
    rw [map_subtype_map_conjOnP, hD, h]

theorem apply_eq_zpow_of_commute (hc : BinaryActionRankCounterexample G p P T B e ρ) {z : MulAut ↥P}
    (hz : ∀ ψ ∈ Sstar P T B, z * ψ = ψ * z) (k : ℤ)
    (hQ : ∀ x : ↥P, (x : G) ∈ Subgroup.centralizer (B : Set G) → z x = x ^ k) (x : ↥P) : z x = x ^ k := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  have hcommP : ∀ a b : ↥P, a * b = b * a := fun a b =>
    (CentralBinaryBlocks.elemAbelian hc).1.is_comm.comm a b
  let F : Subgroup G :=
    { carrier := {y | ∃ h : y ∈ P, z ⟨y, h⟩ = ⟨y, h⟩ ^ k}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨ha, hza⟩ := ha
        obtain ⟨hb, hzb⟩ := hb
        refine ⟨P.mul_mem ha hb, ?_⟩
        have e : (⟨a * b, P.mul_mem ha hb⟩ : ↥P) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [e, map_mul, hza, hzb, (show Commute (⟨a, ha⟩ : ↥P) ⟨b, hb⟩ from hcommP _ _).mul_zpow k]
      one_mem' := ⟨P.one_mem, by
        have e : (⟨1, P.one_mem⟩ : ↥P) = 1 := rfl
        rw [e, map_one, one_zpow]⟩
      inv_mem' := by
        intro a ha
        obtain ⟨ha, hza⟩ := ha
        refine ⟨P.inv_mem ha, ?_⟩
        have e : (⟨a⁻¹, P.inv_mem ha⟩ : ↥P) = (⟨a, ha⟩ : ↥P)⁻¹ := rfl
        rw [e, map_inv, hza, inv_zpow] }
  have hgen := (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.2.2.2.2.1
  have hX : {x : G | ∃ s ∈ twoCoreCommutator T B, x ∈ (P ⊓ Subgroup.centralizer (B : Set G)).map
      (MulAut.conj s).toMonoidHom} ⊆ F := by
    rintro x ⟨s, hs, q, hq, rfl⟩
    have hqP : q ∈ P := hq.1
    have hφs : conjOnP P hP s ∈ Sstar P T B := (mem_Sstar_iff hP).mpr ⟨s, hs, rfl⟩
    have hxP : (MulAut.conj s).toMonoidHom q ∈ P := hP.conj_mem q hqP s
    refine ⟨hxP, ?_⟩
    have e : (⟨(MulAut.conj s).toMonoidHom q, hxP⟩ : ↥P) = conjOnP P hP s ⟨q, hqP⟩ :=
      Subtype.ext (by rw [conjOnP_apply]; rfl)
    have hzq : z ⟨q, hqP⟩ = ⟨q, hqP⟩ ^ k := hQ ⟨q, hqP⟩ hq.2
    rw [e]
    calc z (conjOnP P hP s ⟨q, hqP⟩) = (z * conjOnP P hP s) ⟨q, hqP⟩ := rfl
      _ = (conjOnP P hP s * z) ⟨q, hqP⟩ := by rw [hz _ hφs]
      _ = conjOnP P hP s (z ⟨q, hqP⟩) := rfl
      _ = (conjOnP P hP s ⟨q, hqP⟩) ^ k := by rw [hzq, map_zpow]
  obtain ⟨h, hzx⟩ := hgen.le.trans ((Subgroup.closure_le F).mpr hX) x.2
  exact hzx

theorem eq_one_of_commute_of_fixes (hc : BinaryActionRankCounterexample G p P T B e ρ) {z : MulAut ↥P}
    (hz : ∀ ψ ∈ Sstar P T B, z * ψ = ψ * z)
    (hQ : ∀ x : ↥P, (x : G) ∈ Subgroup.centralizer (B : Set G) → z x = x) : z = 1 :=
  MulEquiv.ext fun x => by
    rw [apply_eq_zpow_of_commute hc hz 1 (fun y hy => by rw [hQ y hy, zpow_one]) x, zpow_one]
    rfl

theorem apply_mem_centralizer_of_mem_centralizer (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {z : MulAut ↥P} (hz : z ∈ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P))) {x : ↥P}
    (hx : (x : G) ∈ Subgroup.centralizer (B : Set G)) :
    ((z x : ↥P) : G) ∈ Subgroup.centralizer (B : Set G) := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hβ : conjOnP P hP b ∈ Bstar P B := (mem_Bstar_iff hP).mpr ⟨b, hb, rfl⟩
  have hcomm : conjOnP P hP b * z = z * conjOnP P hP b := Subgroup.mem_centralizer_iff.mp hz _ hβ
  have hbx : conjOnP P hP b x = x := Subtype.ext (by
    rw [conjOnP_apply, Subgroup.mem_centralizer_iff.mp hx b hb]
    group)
  have h1 : ((conjOnP P hP b (z x) : ↥P) : G) = ((z x : ↥P) : G) := by
    calc ((conjOnP P hP b (z x) : ↥P) : G) = (((conjOnP P hP b * z) x : ↥P) : G) := rfl
      _ = (((z * conjOnP P hP b) x : ↥P) : G) := by rw [hcomm]
      _ = ((z x : ↥P) : G) := by rw [MulAut.mul_apply, hbx]
  rw [conjOnP_apply] at h1
  calc b * ((z x : ↥P) : G) = (b * ((z x : ↥P) : G) * b⁻¹) * b := by group
    _ = ((z x : ↥P) : G) * b := by rw [h1]

theorem inverts_of_commute (hc : BinaryActionRankCounterexample G p P T B e ρ) {z : MulAut ↥P}
    (hzS : ∀ ψ ∈ Sstar P T B, z * ψ = ψ * z) (hzB : z ∈ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)))
    (hz2 : ∀ y : ↥P, z (z y) = y) (hz1 : z ≠ 1) (x : ↥P) : z x = x⁻¹ := by
  set Q' : Subgroup ↥P := (P ⊓ Subgroup.centralizer (B : Set G)).subgroupOf P with hQ'
  have hmemQ' : ∀ y : ↥P, y ∈ Q' ↔ (y : G) ∈ Subgroup.centralizer (B : Set G) := fun y => by
    rw [hQ', Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  have hcardQ' : Nat.card Q' = p := by
    rw [hQ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact PFixedLineDimension.card_eq hc
  have hprQ : (Nat.card Q').Prime := by
    rw [hcardQ']
    exact hc.oddPrimeClassTwoAction.setting.prime
  rcases forall_eq_or_forall_eq_inv hprQ z hz2
      (fun y hy => (hmemQ' _).mpr (apply_mem_centralizer_of_mem_centralizer hc hzB ((hmemQ' y).mp hy))) with
    hfix | hinv
  · exact absurd (eq_one_of_commute_of_fixes hc hzS (fun y hy => hfix y ((hmemQ' y).mpr hy))) hz1
  · rw [apply_eq_zpow_of_commute hc hzS (-1)
      (fun y hy => by rw [hinv y ((hmemQ' y).mpr hy), zpow_neg_one]) x, zpow_neg_one]

theorem inverts_of_mem_center (hc : BinaryActionRankCounterexample G p P T B e ρ) {z : MulAut ↥P}
    (hz : z ∈ (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype) (hz1 : z ≠ 1) (x : ↥P) :
    z x = x⁻¹ := by
  obtain ⟨hsp, hZ⟩ := isSpecialPGroup_Sstar_and_center_eq_centralizer hc
  have hS2 : IsPGroup 2 (Sstar P T B) :=
    (CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).1
  have hcomm : ∀ ψ ∈ Sstar P T B, z * ψ = ψ * z := fun ψ hψ => mul_comm_of_mem_center hz hψ
  have hzB : z ∈ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
    have h := hz
    rw [hZ] at h
    exact (Subgroup.mem_inf.mp h).2
  have hz2 : ∀ y : ↥P, z (z y) = y := by
    obtain ⟨w, hw, rfl⟩ := hz
    have hw2 : w ^ 2 = 1 := CenterElementary.center_sq_eq_one _ hS2 hsp w hw
    have hw2' : (w : MulAut ↥P) * (w : MulAut ↥P) = 1 := by
      have h := congrArg Subtype.val hw2
      simpa [pow_two] using h
    intro y
    have h := congrArg (fun f : MulAut ↥P => f y) hw2'
    simpa using h
  exact inverts_of_commute hc hcomm hzB hz2 hz1 x

theorem map_eq_of_mem_center (hc : BinaryActionRankCounterexample G p P T B e ρ) {z : MulAut ↥P}
    (hz : z ∈ (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype) (K : Subgroup ↥P) :
    K.map z.toMonoidHom = K := by
  by_cases hz1 : z = 1
  · subst hz1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · exact map_eq_self_of_forall_apply_eq_inv (inverts_of_mem_center hc hz hz1) K

theorem card_center_Sstar (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Nat.card (Subgroup.center ↥(Sstar P T B)) = 2 := by
  obtain ⟨hS2, hSne, -, -⟩ :=
    CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥(Sstar P T B) := (Subgroup.nontrivial_iff_ne_bot _).mpr hSne
  haveI : Nontrivial (Subgroup.center ↥(Sstar P T B)) := hS2.center_nontrivial
  rw [Nat.card_eq_two_iff' (1 : Subgroup.center ↥(Sstar P T B))]
  obtain ⟨y, hy⟩ := exists_ne (1 : Subgroup.center ↥(Sstar P T B))
  have hmem : ∀ c : Subgroup.center ↥(Sstar P T B), ((c : ↥(Sstar P T B)) : MulAut ↥P) ∈
      (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype := fun c => ⟨c, c.2, rfl⟩
  have hne : ∀ c : Subgroup.center ↥(Sstar P T B), c ≠ 1 → ((c : ↥(Sstar P T B)) : MulAut ↥P) ≠ 1 :=
    fun c hc1 h => hc1 (Subtype.ext (Subtype.ext h))
  refine ⟨y, hy, fun y' hy' => ?_⟩
  have h1 := inverts_of_mem_center hc (hmem y) (hne y hy)
  have h2 := inverts_of_mem_center hc (hmem y') (hne y' hy')
  exact Subtype.ext (Subtype.ext (MulEquiv.ext fun x => by rw [h1, h2]))

theorem conjOnP_mem_center_of_mem_normalizer (hc : BinaryActionRankCounterexample G p P T B e ρ) {s : G}
    (hs : s ∈ twoCoreCommutator T B) (hsD : s ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G)) :
    conjOnP P hc.faithfulBinaryIrreducibleAction.normal s ∈
      (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  set φ := conjOnP P hP with hφ
  set D₀ : Subgroup G := ⁅B, P⁆ with hD₀
  obtain ⟨hsp, hZ⟩ := isSpecialPGroup_Sstar_and_center_eq_centralizer hc
  have hS2 : IsPGroup 2 (Sstar P T B) :=
    (CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).1
  have h520 := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  have hDΔ : D₀ ∈ Delta p P ρ := h520.1
  have hcommP : ∀ a b : ↥P, a * b = b * a := fun a b =>
    (CentralBinaryBlocks.elemAbelian hc).1.is_comm.comm a b
  set N : Subgroup (MulAut ↥P) := (twoCoreCommutator T B ⊓ Subgroup.normalizer (D₀ : Set G)).map φ with hN
  have hNS : N ≤ Sstar P T B := by
    rw [show Sstar P T B = (twoCoreCommutator T B).map φ from (image_eq P hP _).symm]
    exact Subgroup.map_mono inf_le_left
  have hBD : ∀ b ∈ B, b ∈ Subgroup.normalizer (D₀ : Set G) := fun b hb =>
    NotIsPrimePowTwoPowSubOne.mem_normalizer_commutator_of (Subgroup.le_normalizer hb)
      (hc.oddPrimeClassTwoAction.setting.normB hb)
  have hBS : ∀ b ∈ B, b ∈ Subgroup.normalizer ((twoCoreCommutator T B : Subgroup G) : Set G) := fun b hb => by
    have hK : B ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (B ⊔ T) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
    exact NotIsPrimePowTwoPowSubOne.mem_normalizer_commutator_of (hK hb) (Subgroup.le_normalizer hb)
  have hBN : Bstar P B ≤ Subgroup.normalizer (N : Set (MulAut ↥P)) := by
    refine le_normalizer_of_forall_conj_mem fun β hβ u hu => ?_
    obtain ⟨b, hb, rfl⟩ := (mem_Bstar_iff hP).mp hβ
    obtain ⟨s', hs', rfl⟩ := hu
    refine ⟨b * s' * b⁻¹, ⟨(Subgroup.mem_normalizer_iff.mp (hBS b hb) s').mp hs'.1, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBD b hb) hs'.2) (Subgroup.inv_mem _ (hBD b hb))
    · rw [map_mul, map_mul, map_inv]
  have hu : ∀ g ∈ Subgroup.normalizer (D₀ : Set G), ∀ x : ↥P,
      x ∈ D₀.subgroupOf P ↔ φ g x ∈ D₀.subgroupOf P := by
    intro g hg x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hφ, conjOnP_apply]
    exact Subgroup.mem_normalizer_iff.mp hg x
  have hidx : (D₀.subgroupOf P).index = p := hDΔ.2.1
  have hidxp : (D₀.subgroupOf P).index.Prime := by
    rw [hidx]
    exact hc.oddPrimeClassTwoAction.setting.prime
  have hidx2 : (D₀.subgroupOf P).index ≠ 2 := by
    rw [hidx]
    exact fun h => CentralBinaryDecomposition.p_ne_two hc h
  have hNab : ∀ u ∈ N, ∀ u' ∈ N, u * u' = u' * u := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
    have h1 : φ s₁ ∈ Sstar P T B := hNS ⟨s₁, hs₁, rfl⟩
    have h2 : φ s₂ ∈ Sstar P T B := hNS ⟨s₂, hs₂, rfl⟩
    set c := φ s₁ * φ s₂ * (φ s₁)⁻¹ * (φ s₂)⁻¹ with hcdef
    have hcZ : c ∈ (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype := by
      rw [hsp.1]
      refine ⟨⁅(⟨φ s₁, h1⟩ : ↥(Sstar P T B)), ⟨φ s₂, h2⟩⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
      simp [commutatorElement_def, hcdef]
    by_cases hc1 : c = 1
    · calc φ s₁ * φ s₂ = c * (φ s₂ * φ s₁) := by rw [hcdef]; group
        _ = φ s₂ * φ s₁ := by rw [hc1, one_mul]
    · exfalso
      have hinv := inverts_of_mem_center hc hcZ hc1
      refine false_of_forall_apply_apply_eq_inv hcommP hidxp hidx2 (hu s₁ hs₁.2) (hu s₂ hs₂.2) fun x => ?_
      have h := hinv (φ s₂ (φ s₁ x))
      have e : c (φ s₂ (φ s₁ x)) = φ s₁ (φ s₂ x) := by
        rw [hcdef]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      rwa [e] at h
  have hcomm : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext (hNab a a.2 b b.2)⟩⟩
  have hC := Bstar_le_centralizer_of_isMulCommutative hc (hS2.to_le hNS) hcomm hBN
  have hmem : φ s ∈ N := ⟨s, ⟨hs, hsD⟩, rfl⟩
  rw [hZ]
  refine Subgroup.mem_inf.mpr ⟨hNS hmem, Subgroup.mem_centralizer_iff.mpr fun β hβ => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hC hβ) _ hmem).symm

end CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar
  CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem isExtraspecialPGroup_Sstar (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    CFSG.IsExtraspecialPGroup 2 ↥(Sstar P T B) := by
  obtain ⟨hS2, -, -, -⟩ :=
    CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction
  obtain ⟨⟨h1, h2⟩, -⟩ := isSpecialPGroup_Sstar_and_center_eq_centralizer hc
  have hinj : Function.Injective (Sstar P T B).subtype := Subtype.val_injective
  exact ⟨hS2, (Subgroup.map_injective hinj h1).symm, (Subgroup.map_injective hinj h2).symm,
    card_center_Sstar hc⟩

theorem mem_center_Sstar_iff (hc : BinaryActionRankCounterexample G p P T B e ρ) {ψ : MulAut ↥P}
    (hψ : ψ ∈ Sstar P T B) :
    ψ ∈ (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype ↔
      ((⁅B, P⁆ : Subgroup G).subgroupOf P).map ψ.toMonoidHom = (⁅B, P⁆ : Subgroup G).subgroupOf P := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  have hDP : (⁅B, P⁆ : Subgroup G) ≤ P :=
    (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).1.1
  refine ⟨fun hz => map_eq_of_mem_center hc hz _, fun h => ?_⟩
  obtain ⟨s, hs, rfl⟩ := (mem_Sstar_iff hP).mp hψ
  exact conjOnP_mem_center_of_mem_normalizer hc hs ((map_conjOnP_eq_iff hP s hDP).mp h)

theorem map_conj_eq_of_mem_normalizer_commutator (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∀ s ∈ twoCoreCommutator T B, s ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) →
      ∀ E ∈ Delta p P ρ, E.map (MulAut.conj s).toMonoidHom = E := by
  intro s hs hsD E hE
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  have h520 := cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc
  have hDP : (⁅B, P⁆ : Subgroup G) ≤ P := h520.1.1
  obtain ⟨s', hs', rfl⟩ := h520.2.2.2.2.1 ⁅B, P⁆ h520.1 E hE
  have hz := conjOnP_mem_center_of_mem_normalizer hc hs hsD
  have hcomm : conjOnP P hP s * conjOnP P hP s' = conjOnP P hP s' * conjOnP P hP s :=
    mul_comm_of_mem_center hz ((mem_Sstar_iff hP).mpr ⟨s', hs', rfl⟩)
  have hN : s'⁻¹ * (s * s') ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
    rw [← map_conjOnP_eq_iff hP _ hDP]
    have h1 : conjOnP P hP (s'⁻¹ * (s * s')) = conjOnP P hP s := by
      rw [map_mul, map_mul, map_inv, hcomm, inv_mul_cancel_left]
    rw [h1, map_conjOnP_eq_iff hP _ hDP]
    exact hsD
  rw [Subgroup.map_map]
  have e : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s').toMonoidHom = (MulAut.conj (s * s')).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]
  exact (map_conj_eq_map_conj_iff (s * s') s' _).mpr hN

theorem commutator_mem_normalizer_and_mul_self_mem_normalizer
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∀ s ∈ twoCoreCommutator T B, ∀ s' ∈ twoCoreCommutator T B,
      s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) ∧
        s * s ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
  intro s hs s' hs'
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  have hDP : (⁅B, P⁆ : Subgroup G) ≤ P :=
    (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).1.1
  obtain ⟨hsp, -⟩ := isSpecialPGroup_Sstar_and_center_eq_centralizer hc
  have hS2 : IsPGroup 2 (Sstar P T B) :=
    (CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction).1
  have h1 : conjOnP P hP s ∈ Sstar P T B := (mem_Sstar_iff hP).mpr ⟨s, hs, rfl⟩
  have h2 : conjOnP P hP s' ∈ Sstar P T B := (mem_Sstar_iff hP).mpr ⟨s', hs', rfl⟩
  have hZ : ∀ g : G, conjOnP P hP g ∈ (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype →
      g ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := fun g hg =>
    (map_conjOnP_eq_iff hP g hDP).mp (map_eq_of_mem_center hc hg _)
  refine ⟨hZ _ ?_, hZ _ ?_⟩
  · rw [hsp.1]
    refine ⟨⁅(⟨_, h1⟩ : ↥(Sstar P T B)), ⟨_, h2⟩⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
    simp [commutatorElement_def, map_mul, map_inv]
  · rw [hsp.2]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (IsPGroup 2 ↥(Sstar P T B)) := ⟨hS2⟩
    refine ⟨(⟨_, h1⟩ : ↥(Sstar P T B)) ^ 2, CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _, ?_⟩
    simp [pow_two, map_mul]

end CFSG.LocalAnalysis.RankThreeUC.Section5
