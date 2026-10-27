module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstruction

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

section Defs

variable {G : Type} [Group G]

structure IsExceptionalLayer (σ : Setting G) (J : Subgroup G) : Prop where
  le : J ≤ σ.L₀
  sup_eq : σ.L₀ = J ⊔ σ.ON
  centralizes : J ≤ Subgroup.centralizer (σ.ON : Set G)
  normal : σ.N ≤ Subgroup.normalizer (J : Set G)
  q_eq : σ.q = 9
  height_eq : σ.height = 1
  card_inf : Nat.card (J ⊓ σ.ON : Subgroup G) = 3

structure TIFactsQ9 [Finite G] (σ : Setting G) : Prop where
  cyclic : ∀ J : Subgroup G, IsExceptionalLayer σ J → IsCyclic (σ.C ⊓ J : Subgroup G)
  centralizer_le : ∀ J : Subgroup G, IsExceptionalLayer σ J → ∀ g ∈ σ.C,
    g ∈ Subgroup.centralizer ((σ.C ⊓ J : Subgroup G) : Set G) → g ∈ σ.L
  signalizer_le : ∀ J : Subgroup G, IsExceptionalLayer σ J → ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ X ∈ signalizers J σ.C r, X ≤ σ.ON
  permutable_le : ∀ J : Subgroup G, IsExceptionalLayer σ J → ∀ U : Subgroup G, U ≤ σ.N →
    Odd (Nat.card U) → (U : Set G) * (σ.C : Set G) = (σ.C : Set G) * (U : Set G) →
      U ≤ σ.C ⊔ σ.ON

end Defs

namespace DataConstructionQD

open DataConstruction

variable {G : Type} [Group G] {σ : Setting G}

theorem not_deltaEpsMinus_of_exceptionalLayer {J : Subgroup G} (hJ : IsExceptionalLayer σ J) :
    ¬ σ.DeltaEpsMinus := by
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · rw [hJ.q_eq] at h
    exact absurd h (by norm_num)
  · exact h hJ.height_eq

theorem inf_ON_ne_bot_of_exceptionalLayer {J : Subgroup G} (hJ : IsExceptionalLayer σ J) :
    J ⊓ σ.ON ≠ ⊥ := by
  intro h
  have h3 := hJ.card_inf
  rw [h, Subgroup.card_bot] at h3
  exact absurd h3 (by norm_num)

theorem exists_pGroup_le_J_le_sup_ON [Finite G] (hσ : σ.IsValid) {J : Subgroup G}
    (hJle : J ≤ σ.L₀) (hsup : σ.L₀ = J ⊔ σ.ON) (hcent : J ≤ Subgroup.centralizer (σ.ON : Set G))
    (hnorm : σ.N ≤ Subgroup.normalizer (J : Set G)) {r : ℕ} (hr : r.Prime) {U : Subgroup G}
    (hUL₀ : U ≤ σ.L₀) (hU : IsPGroup r U) (hCU : σ.C ≤ Subgroup.normalizer (U : Set G)) :
    ∃ X : Subgroup G, X ≤ J ∧ IsPGroup r X ∧ σ.C ≤ Subgroup.normalizer (X : Set G) ∧
      U ≤ X ⊔ σ.ON := by
  have : Fact r.Prime := ⟨hr⟩
  have hJN : J ≤ σ.N := hJle.trans hσ.L₀_le_N
  have hUN : U ≤ σ.N := hUL₀.trans hσ.L₀_le_N
  have hONJ : σ.ON ≤ Subgroup.centralizer (J : Set G) := Subgroup.le_centralizer_iff.mp hcent
  set K := (U ⊔ σ.ON) ⊓ J with hK
  have hKJ : K ≤ J := inf_le_right
  have hUK : U ≤ K ⊔ σ.ON := by
    intro u hu
    have hu' : u ∈ ((J ⊔ σ.ON : Subgroup G) : Set G) := by
      rw [← hsup]
      exact hUL₀ hu
    rw [Subgroup.coe_mul_of_left_le_normalizer_right J σ.ON
      (hJN.trans σ.N_le_normalizer_ON)] at hu'
    obtain ⟨j, hj, o, ho, rfl⟩ := hu'
    have hjK : j ∈ K := by
      refine ⟨?_, hj⟩
      have := (U ⊔ σ.ON).mul_mem (Subgroup.mem_sup_left hu)
        (Subgroup.mem_sup_right (σ.ON.inv_mem ho))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjK) (Subgroup.mem_sup_right ho)
  obtain ⟨R, hR⟩ := exists_isSylowOf r K
  have hRK : R ≤ K := hR.le
  set B := R ⊔ σ.ON with hB
  have hBA : B ≤ U ⊔ σ.ON := sup_le (hRK.trans inf_le_left) le_sup_right
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (hRK.trans Subgroup.le_normalizer)
      ((hONJ.trans (Subgroup.centralizer_le hKJ)).trans (Subgroup.centralizer_le_normalizer _))
  have hKB : K ⊔ B = U ⊔ σ.ON :=
    le_antisymm (sup_le inf_le_left hBA)
      (sup_le (hUK.trans (sup_le_sup_left le_sup_right _)) (le_sup_right.trans le_sup_right))
  have h1 : B.relIndex (U ⊔ σ.ON) = B.relIndex K := by
    rw [← hKB]
    exact relIndex_sup_eq_relIndex_of_le_normalizer hBK
  have h2 : ¬ r ∣ B.relIndex K := by
    intro hdvd
    apply (isSylowOf_iff.mp hR).2.2
    rw [← Subgroup.relIndex_mul_relIndex R (B ⊓ K) K (le_inf le_sup_left hRK) inf_le_right,
      Subgroup.inf_relIndex_right]
    exact hdvd.mul_left _
  have h3 : B.relIndex (U ⊔ σ.ON) ∣ Nat.card U := by
    have h4 := Subgroup.relIndex_mul_relIndex σ.ON B (U ⊔ σ.ON) le_sup_right hBA
    rw [relIndex_sup_right_of_le_normalizer (hUN.trans σ.N_le_normalizer_ON)] at h4
    exact (Dvd.intro_left _ h4).trans (Subgroup.relIndex_dvd_card _ _)
  have h5 : B.relIndex (U ⊔ σ.ON) = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
    rw [hk] at h3
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp h3
    rcases j with _ | j
    · rwa [pow_zero] at hj
    · exact absurd (h1 ▸ hj ▸ dvd_pow_self r (Nat.succ_ne_zero j)) h2
  have hUB : U ⊔ σ.ON ≤ B := Subgroup.relIndex_eq_one.mp h5
  have hKR : K ≤ Subgroup.normalizer (R : Set G) := by
    intro k hk
    have hk' : k ∈ ((R ⊔ σ.ON : Subgroup G) : Set G) := hUB ((inf_le_left : K ≤ U ⊔ σ.ON) hk)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R σ.ON
      ((((hRK.trans hKJ).trans hJN)).trans σ.N_le_normalizer_ON)] at hk'
    obtain ⟨ρ, hρ, o, ho, rfl⟩ := hk'
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hρ)
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (hRK.trans hKJ) (hONJ ho)))
  have hCK : σ.C ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf (le_normalizer_sup hCU (σ.C_le_N.trans σ.N_le_normalizer_ON))
      (σ.C_le_N.trans hnorm)
  refine ⟨pCoreIn r K, (pCoreIn_le r K).trans hKJ, isPGroup_pCoreIn r K,
    hCK.trans (normalizer_le_normalizer_pCoreIn r K), ?_⟩
  exact le_sup_left.trans (hUB.trans (sup_le_sup_right (le_pCoreIn hRK hKR hR.isPGroup) _))

variable [Finite G] {r : ℕ} {J : Subgroup G}

theorem le_ON_of_mem_signalizers_qd (hσ : σ.IsValid) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hJ : IsExceptionalLayer σ J) (hr : r.Prime) (hr2 : r ≠ 2) (hti : σ.TotallyInverted r)
    {U : Subgroup G} (hU : U ∈ signalizers σ.N σ.C r) : U ≤ σ.ON := by
  obtain ⟨X, hXJ, hX, hCX, hUX⟩ := exists_pGroup_le_J_le_sup_ON hσ hJ.le hJ.sup_eq
    hJ.centralizes hJ.normal hr (hT.signalizer_le r hr hr2 U hU) hU.2.1 hU.2.2.1
  have hXON := hT9.signalizer_le J hJ r hr hr2 X
    ⟨hXJ, hX, hCX, inf_C_eq_bot hr hti hX (hXJ.trans (hJ.le.trans L₀_le_L))⟩
  exact hUX.trans (sup_le hXON le_rfl)

theorem lemma71_zero_qd (hσ : σ.IsValid) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hJ : IsExceptionalLayer σ J) (hr : r.Prime) (hr2 : r ≠ 2) (hti : σ.TotallyInverted r)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) :
    maximals (signalizers σ.N σ.C r) = {σ.Ps r 0} := by
  have : Fact r.Prime := ⟨hr⟩
  have hmem : σ.Ps r 0 ∈ signalizers σ.N σ.C r :=
    ⟨pCoreIn_le r _, isPGroup_pCoreIn r _, σ.C_le_N.trans (N_le_normalizer_Ps_zero σ r),
      inf_C_eq_bot hr hti (isPGroup_pCoreIn r _) (hP₀.le.trans (ON_le_L hσ))⟩
  have hcov : ∀ U ∈ signalizers σ.N σ.C r, U ≤ σ.Ps r 0 := fun U hU =>
    le_of_isSylowOf_of_le_normalizer hP₀ (le_ON_of_mem_signalizers_qd hσ hT hT9 hJ hr hr2 hti hU)
      hU.2.1 (hU.1.trans (N_le_normalizer_Ps_zero σ r))
  rw [← Set.pair_eq_singleton]
  exact maximals_eq_pair hmem hmem (fun U hU => Or.inl (hcov U hU)) (fun _ => rfl) (fun _ => rfl)

theorem lemma72_zero_qd (hσ : σ.IsValid) (hT9 : TIFactsQ9 σ) (hJ : IsExceptionalLayer σ J)
    (hr : r.Prime) (hr2 : r ≠ 2) (hti : σ.TotallyInverted r) (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON)
    {R : Subgroup G} (hR : IsSylowOf r R σ.C) :
    {U | U ∈ maximals (signalizersPerm σ.N σ.T σ.C r) ∧ R ≤ U} = {R ⊔ σ.Ps r 0} := by
  have : Fact r.Prime := ⟨hr⟩
  have hRC := hR.le
  have hCP : σ.C ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) :=
    σ.C_le_N.trans (N_le_normalizer_Ps_zero σ r)
  have hsyl : IsSylowOf r (R ⊔ σ.Ps r 0) (σ.C ⊔ σ.ON) :=
    isSylowOf_sup (σ.C_le_N.trans σ.N_le_normalizer_ON) hR hP₀ (hRC.trans hCP)
      (eq_bot_iff.mpr ((inf_L_eq_bot hr hti hR.isPGroup hRC) ▸
        inf_le_inf_left R (hP₀.le.trans (ON_le_L hσ))))
  have hmem : R ⊔ σ.Ps r 0 ∈ signalizersPerm σ.N σ.T σ.C r := by
    have hp := hsyl.isPGroup
    refine ⟨⟨sup_le (hRC.trans σ.C_le_N) (pCoreIn_le r _), hp, ?_,
      inf_eq_bot_of_isPGroup hr Nat.prime_two hr2 hp (isPGroup_T hσ)⟩,
      sup_mul_comm_of_le hRC hCP⟩
    exact le_normalizer_sup ((Subgroup.le_centralizer_iff.mp hRC).trans
      (Subgroup.centralizer_le_normalizer _)) ((σ.T_le_N hσ).trans (N_le_normalizer_Ps_zero σ r))
  have hcov : ∀ U ∈ signalizersPerm σ.N σ.T σ.C r, R ≤ U → U ≤ R ⊔ σ.Ps r 0 := by
    rintro U ⟨⟨hUN, hU, -, -⟩, hperm⟩ hRU
    exact le_sup_of_isSylowOf_sup hsyl (isPGroup_pCoreIn r _)
      (hT9.permutable_le J hJ U hUN (odd_card_of_isPGroup hr hr2 hU) hperm) hU hRU
      (hUN.trans (N_le_normalizer_Ps_zero σ r))
  rw [← Set.pair_eq_singleton]
  exact setOf_maximals_ge_eq_pair hmem hmem le_sup_left le_sup_left
    (fun U hU hRU => Or.inl (hcov U hU hRU)) (fun _ => rfl) (fun _ => rfl)

variable {a : G}

theorem lemma71_all_qd (hσ : σ.IsValid) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hJ : IsExceptionalLayer σ J) (hr : r.Prime) (hr2 : r ≠ 2) (hti : σ.TotallyInverted r)
    (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON) (haN : a ∈ Subgroup.normalizer (σ.T : Set G))
    (hcyc : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)) (i : Fin 3) :
    maximals (signalizers (σ.Ns i) σ.C r) = {σ.Ps r i} := by
  have h := maximals_image_conjSub (a ^ (i : ℕ)) (signalizers σ.N σ.C r)
  rw [← signalizers_conjSub, conjSub_pow_N hcyc, conjSub_pow_C haN,
    lemma71_zero_qd hσ hT hT9 hJ hr hr2 hti hP₀, Set.image_singleton, conjSub_pow_Ps hcyc] at h
  exact h

theorem lemma72_all_qd (hσ : σ.IsValid) (hT9 : TIFactsQ9 σ) (hJ : IsExceptionalLayer σ J)
    (hr : r.Prime) (hr2 : r ≠ 2) (hti : σ.TotallyInverted r) (hP₀ : IsSylowOf r (σ.Ps r 0) σ.ON)
    (haN : a ∈ Subgroup.normalizer (σ.T : Set G))
    (hcyc : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)) (i : Fin 3) (R : Subgroup G)
    (hR : IsSylowOf r R σ.C) :
    {U | U ∈ maximals (signalizersPerm (σ.Ns i) σ.T σ.C r) ∧ R ≤ U} = {R ⊔ σ.Ps r i} := by
  have : Fact r.Prime := ⟨hr⟩
  have hR' : IsSylowOf r (conjSub (a ^ (i : ℕ))⁻¹ R) σ.C := by
    have := isSylowOf_conjSub hR (a ^ (i : ℕ))⁻¹
    rwa [conjSub_pow_inv_C haN] at this
  have h := setOf_image_conjSub_ge (a ^ (i : ℕ)) (maximals (signalizersPerm σ.N σ.T σ.C r))
    (conjSub (a ^ (i : ℕ))⁻¹ R)
  rw [conjSub_conjSub_inv, ← maximals_image_conjSub, ← signalizersPerm_conjSub,
    conjSub_pow_N hcyc, conjSub_pow_T haN, conjSub_pow_C haN,
    lemma72_zero_qd hσ hT9 hJ hr hr2 hti hP₀ hR', Set.image_singleton] at h
  rw [h, conjSub_sup, conjSub_conjSub_inv, conjSub_pow_Ps hcyc]

theorem isCyclic_W_qd (hT9 : TIFactsQ9 σ) (hJ : IsExceptionalLayer σ J) :
    IsCyclic (oddCoreIn (σ.C ⊓ J)) :=
  have := hT9.cyclic J hJ
  Subgroup.isCyclic_of_le (oddCoreIn_le _)

omit [Finite G] in
theorem not_dvd_card_W_qd (hti : σ.TotallyInverted r) (hJ : J ≤ σ.L₀) :
    ¬ r ∣ Nat.card (oddCoreIn (σ.C ⊓ J)) := fun h =>
  hti (h.trans (Subgroup.card_dvd_of_le ((oddCoreIn_le _).trans
    (inf_le_inf_left _ (hJ.trans L₀_le_L)))))

theorem pCoreIn_C_eq_bot_qd (hT9 : TIFactsQ9 σ) (hr : r.Prime) (hti : σ.TotallyInverted r)
    (hJ : IsExceptionalLayer σ J) : pCoreIn r σ.C = ⊥ := by
  set X := pCoreIn r σ.C
  have hXC : X ≤ σ.C := pCoreIn_le r σ.C
  have hXL : X ⊓ σ.L = ⊥ := inf_L_eq_bot hr hti (isPGroup_pCoreIn r σ.C) hXC
  have hCJ : σ.C ≤ Subgroup.normalizer ((σ.C ⊓ J : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (σ.C_le_N.trans hJ.normal)
  have hinf : X ⊓ (σ.C ⊓ J) = ⊥ :=
    eq_bot_iff.mpr (hXL ▸ inf_le_inf_left X (inf_le_right.trans (hJ.le.trans L₀_le_L)))
  have hcent : X ≤ Subgroup.centralizer ((σ.C ⊓ J : Subgroup G) : Set G) :=
    le_centralizer_of_inf_eq_bot (hXC.trans hCJ)
      (inf_le_left.trans (le_normalizer_pCoreIn r σ.C)) hinf
  have hXL' : X ≤ σ.L := fun g hg => hT9.centralizer_le J hJ g (hXC hg) (hcent hg)
  rw [← inf_eq_left.mpr hXL', hXL]

theorem nonempty_data_of_exceptionalLayer (hσ : σ.IsValid)
    (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (hA : automizerIndex σ.T = 6) (hV : σ.CorollaryV61) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hr : r.Prime) (hdvd : r ∣ Nat.card σ.ON) (hexc : σ.Exceptional r)
    (hti : σ.TotallyInverted r) (hJ : IsExceptionalLayer σ J) : Nonempty (Data σ r) := by
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdvd
  have hc : ¬ (σ.DeltaEpsMinus ∧ r ∣ σ.q) := fun h => not_deltaEpsMinus_of_exceptionalLayer hJ h.1
  obtain ⟨a, haN, ha3, ha1, ha2⟩ := exists_a hσ hA
  have hcyc := xs_cycle hσ ha1 ha2
  obtain ⟨d, hdD, hd2⟩ := hd
  have hd1 := conj_x_of_mem_D hσ hdD
  obtain ⟨hP₀, hP₀inv, hP₀ab⟩ := Ps_zero_facts hσ hV hr hdvd hti
  obtain ⟨P, hPsyl, hPD, hPL⟩ := exists_P hT hr hr2 hti
  exact ⟨{
    prime := hr
    ne_two := hr2
    dvd := hdvd
    exceptional := hexc
    totallyInverted := hti
    a := a
    a_mem := normalizer_T_le_M haN
    a_three := ha3
    a_cycle := hcyc
    d := d
    d_mem := hdD
    d_x := hd1
    d_x₂ := hd2
    M_eq := M_eq hσ hF₀ hT haN ha1 ha2 hdD hd1 hd2
    F₀_sylow := hF₀
    F₀_abelian := hT.F₀_abelian
    F₀_omega := hT.F₀_omega
    L_normal := N_le_normalizer_L hσ hT
    T_le_L := T_le_L hσ
    J := J
    J_le := hJ.le
    L₀_eq := hJ.sup_eq
    J_centralizes := hJ.centralizes
    J_normal := hJ.normal
    J_inf := Or.inr ⟨hJ.q_eq, hJ.height_eq, hJ.card_inf⟩
    J_sl2 := fun h => absurd h (inf_ON_ne_bot_of_exceptionalLayer hJ)
    W := oddCoreIn (σ.C ⊓ J)
    W_eq := rfl
    W_cyclic := isCyclic_W_qd hT9 hJ
    W_coprime := not_dvd_card_W_qd hti hJ.le
    Op_C := pCoreIn_C_eq_bot_qd hT9 hr hti hJ
    P_conj := conjSub_Ps hcyc r
    P_abelian := Ps_abelian hcyc hP₀ab
    P_centralized := fun i => pCoreIn_le r (σ.Ns i)
    P_inverted := fun i j hji _ hu => Ps_inverted hcyc hP₀inv i j hji hu
    P_sylow := hP₀
    Q := fun _ => ⊥
    Qs := fun _ => ⊥
    Q_trivial := fun _ _ => ⟨rfl, rfl⟩
    Q_le := fun _ => ⟨bot_le, bot_le⟩
    Q_pgroup := fun _ => ⟨IsPGroup.of_bot, IsPGroup.of_bot⟩
    Q_C := fun _ => ⟨le_normalizer_bot _, le_normalizer_bot _⟩
    Q_conj := fun _ => ⟨conjSub_bot a, conjSub_bot a⟩
    Q_cases := fun h => absurd h hc
    P := P
    P_sylowC := hPsyl
    P_D := hPD
    P_L := hPL
    lemma71 := fun i => by
      rw [ite_eq_right hc]
      exact lemma71_all_qd hσ hT hT9 hJ hr hr2 hti hP₀ haN hcyc i
    lemma72 := fun i R hR => by
      rw [ite_eq_right hc]
      exact lemma72_all_qd hσ hT9 hJ hr hr2 hti hP₀ haN hcyc i R hR }⟩

end DataConstructionQD

open DataConstructionQD

theorem nonempty_data_qd {G : Type} [Group G] [Finite G] {σ : Setting G} (hσ : σ.IsValid)
    (hh : σ.height = 1)
    (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (hA : automizerIndex σ.T = 6) (hV : σ.CorollaryV61) (hT : σ.TIFacts)
    (hT9 : TIFactsQ9 σ)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card σ.ON) (hexc : σ.Exceptional r)
    (hti : σ.TotallyInverted r) : Nonempty (Data σ r) := by
  by_cases hJ : DataConstruction.NoExceptionalLayer σ
  · exact nonempty_data_core hσ hd hF₀ hJ hA hV hT hr hdvd hexc hti
  · simp only [DataConstruction.NoExceptionalLayer, not_forall, not_not] at hJ
    obtain ⟨J, hJle, hsup, hcent, hnorm, hq, -, hcard⟩ := hJ
    exact nonempty_data_of_exceptionalLayer hσ hd hF₀ hA hV hT hT9 hr hdvd hexc hti
      ⟨hJle, hsup, hcent, hnorm, hq, hh, hcard⟩

end CFSG.ABGTheoremB.TotallyInverted
