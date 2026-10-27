module

public import CFSG.GH74.KGroups.L3EpsWreath
public import CFSG.GH74.KGroups.L3EpsLinSyl
public import CFSG.GH74.KGroups.L3EpsUniSyl

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

section Linear

variable {F : Type} [Field F] [Finite F]

theorem wr_Pexp {r : ℕ} (hr : r ∣ Nat.card F - 1) (hr3 : ¬ 3 ∣ r) :
    WrPres ↥(Pexp (F := F) r) r := by
  have hcard : Nat.card (mu r F) = r := card_mu hr
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(mu r F))
  have hgo : orderOf g = r := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hθinj := thetaMu_injective (F := F) hr3
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : projectiveSL 3 F, u₀ = thetaMu r (g, 1) := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : projectiveSL 3 F, v₀ = thetaMu r (1, g) := ⟨_, rfl⟩
  have hu₀J : u₀ ∈ Jexp (F := F) r := ⟨(g, 1), hu₀.symm⟩
  have hv₀J : v₀ ∈ Jexp (F := F) r := ⟨(1, g), hv₀.symm⟩
  have hθ : ∀ a b : ℕ, u₀ ^ a * v₀ ^ b = thetaMu r (g ^ a, g ^ b) := by
    intro a b
    rw [hu₀, hv₀, ← map_pow, ← map_pow, ← map_mul]
    congr 1
    simp
  refine ⟨⟨u₀, Jexp_le_Pexp r hu₀J⟩, ⟨v₀, Jexp_le_Pexp r hv₀J⟩, ⟨tauBar, tauBar_mem_Pexp r⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (Jexp_comm r _ hu₀J _ hv₀J)
  · exact Subtype.ext (Jexp_pow r _ hu₀J)
  · exact Subtype.ext (Jexp_pow r _ hv₀J)
  · exact Subtype.ext tauBar_sq
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [tauBar_inv, hu₀, hv₀]
    have := tauBar_conj_theta (F := F) r g 1
    rwa [tauBar_inv] at this
  · intro a b hab
    have h1 : u₀ ^ a * v₀ ^ b = 1 := congrArg Subtype.val hab
    rw [hθ, ← map_one (thetaMu r : mu r F × mu r F →* projectiveSL 3 F)] at h1
    have h2 := hθinj h1
    have ha : g ^ a = 1 := congrArg Prod.fst h2
    have hb : g ^ b = 1 := congrArg Prod.snd h2
    rw [← hgo]
    exact ⟨orderOf_dvd_iff_pow_eq_one.2 ha, orderOf_dvd_iff_pow_eq_one.2 hb⟩
  · intro w
    obtain ⟨j, hj, hw⟩ := w.2
    obtain ⟨⟨x, y⟩, rfl⟩ := hj
    obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.2 (hg x)
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hg y)
    have hi' : g ^ i = x := hi
    have hk' : g ^ k = y := hk
    have hxy : thetaMu r (x, y) = u₀ ^ i * v₀ ^ k := by
      rw [hθ, hi', hk']
    rcases hw with hw | hw
    · refine ⟨i, k, 0, by norm_num, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [← hxy]
      simpa using hw
    · refine ⟨i, k, 1, by norm_num, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [← hxy, pow_one]
      exact hw

end Linear

section Models

variable {X : Type} [Group X] {p f : ℕ}

theorem lin_wr (hp2 : p ≠ 2) (h1 : p ^ f % 4 = 1) (hX : StatedClassicalModel X .PSL 3 p f)
    {R : Subgroup X} (hR : IsPGroup 2 R) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → R ≤ T → T ≤ R) :
    WrPres ↥R (ordProj[2] (p ^ f - 1)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hp : p.Prime := hX.1.1
  have hq2 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hF2 : Nat.card F % 2 = 1 := by rw [hF]; exact hq2
  have hF4 : Nat.card F % 4 = 1 := by rw [hF]; exact h1
  set r := ordProj[2] (p ^ f - 1) with hr
  have hrF : r = ordProj[2] (Nat.card F - 1) := by rw [hF]
  have hrdvd : r ∣ Nat.card F - 1 := hrF ▸ Nat.ordProj_dvd _ 2
  have hr3 : ¬ 3 ∣ r := by
    intro h3
    rw [hr] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨hP2, hPmax⟩ := Pexp_sylow (F := F) (r := r) hF2 hF4 hrF
  have hRm := isMaxPGroup_map e hR hmax
  obtain ⟨e3⟩ := nonempty_mulEquiv_of_sylow hRm.1 hRm.2 hP2 (card_of_isMaxPGroup hP2 hPmax)
  exact (wr_Pexp hrdvd hr3).congr ((R.equivMapOfInjective e.toMonoidHom e.injective).trans e3).symm

theorem uni_wr (hp2 : p ≠ 2) (h3 : p ^ f % 4 = 3) (hX : StatedClassicalModel X .PSU 3 p f)
    {R : Subgroup X} (hR : IsPGroup 2 R) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → R ≤ T → T ≤ R) :
    WrPres ↥R (ordProj[2] (p ^ f + 1)) := by
  obtain ⟨K, _, hU, ⟨ψ⟩⟩ := exists_unitary_quotient_equiv hX
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : CharP K p := hU.charP
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  set D := (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)) with hD
  have hmodels := odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2 (G₀ := 1)
    (bar_one_apply' hU) hdet D le_rfl
  obtain ⟨⟨P, hP⟩, -, -, -, h3part, -⟩ := hmodels
  obtain ⟨⟨l, hl, hlo⟩, hall⟩ := h3part h3
  obtain ⟨u, v, τ, -, -, -, hvu, huv, hou, hov, hτ2, -, -, hφ, hnf, hW2, -, hinj, hWbar2,
    hWbarcard⟩ := hall P hP l hl hlo
  set W := Subgroup.closure ({u, v, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))) with hW
  set s := ordProj[2] (p ^ f + 1) with hs
  have hs0 : 0 < s := Nat.ordProj_pos _ _
  have hmaxQ := isMaxPGroup_map ψ hR hmax
  obtain ⟨e1⟩ := nonempty_mulEquiv_of_sylow hmaxQ.1 hmaxQ.2 hWbar2 hWbarcard
  let e : R ≃* W := (ψ.subgroupMap R).trans
    (e1.trans (equivMapOfInjOn (QuotientGroup.mk' D) W hinj).symm)
  have huW : u ∈ W := Subgroup.subset_closure (by simp)
  have hvW : v ∈ W := Subgroup.subset_closure (by simp)
  have hτW : τ ∈ W := Subgroup.subset_closure (by simp)
  have hus : u ^ s = 1 := by rw [← hou]; exact pow_orderOf_eq_one u
  have hvs : v ^ s = 1 := by rw [← hov]; exact pow_orderOf_eq_one v
  have hWr : WrPres ↥W s := by
    refine ⟨⟨u, huW⟩, ⟨v, hvW⟩, ⟨τ, hτW⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subtype.ext huv.eq
    · exact Subtype.ext (by simpa using hus)
    · exact Subtype.ext (by simpa using hvs)
    · exact Subtype.ext (by simpa using hτ2)
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hvu.symm
    · intro a b hab
      have h1 : u ^ a * v ^ b = 1 := by simpa using congrArg Subtype.val hab
      rw [pow_eq_pow_mod a hus, pow_eq_pow_mod b hvs] at h1
      have hamod : a % s < s := Nat.mod_lt _ hs0
      have hbmod : b % s < s := Nat.mod_lt _ hs0
      have h' : (fun x : Fin s × Fin s × Fin 2 => u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ))
          (⟨a % s, hamod⟩, ⟨b % s, hbmod⟩, 0) =
          (fun x : Fin s × Fin s × Fin 2 => u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ))
          (⟨0, hs0⟩, ⟨0, hs0⟩, 0) := by simp [h1]
      have h2 := hφ h'
      have e1 : a % s = 0 := congrArg (fun x : Fin s × Fin s × Fin 2 => (x.1 : ℕ)) h2
      have e2 : b % s = 0 := congrArg (fun x : Fin s × Fin s × Fin 2 => (x.2.1 : ℕ)) h2
      exact ⟨Nat.dvd_of_mod_eq_zero e1, Nat.dvd_of_mod_eq_zero e2⟩
    · intro w
      obtain ⟨i, j, e, -, -, he, hw⟩ := hnf w.1 w.2
      exact ⟨i, j, e, he, Subtype.ext (by simpa using hw)⟩
  exact hWr.congr e.symm

theorem ordProj_two_eq_four_mul {N : ℕ} (hN : N ≠ 0) (h4 : N % 4 = 0) :
    ∃ n : ℕ, ordProj[2] N = 4 * 2 ^ n := by
  have h4' : 2 ^ 2 ∣ N := by simpa using Nat.dvd_of_mod_eq_zero h4
  have hv : 2 ≤ N.factorization 2 := (Nat.prime_two.pow_dvd_iff_le_factorization hN).1 h4'
  obtain ⟨k, hk⟩ : ∃ k, N.factorization 2 = k + 2 := ⟨N.factorization 2 - 2, by omega⟩
  refine ⟨k, ?_⟩
  show 2 ^ N.factorization 2 = 4 * 2 ^ k
  rw [hk, pow_add]
  ring

theorem l3eps_wreathed {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hcong : (t = .PSL → p ^ f % 4 = 1) ∧ (t = .PSU → p ^ f % 4 = 3))
    (hX : StatedClassicalModel X t 3 p f) {R : Subgroup X} (hR : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup X, IsPGroup 2 T → R ≤ T → T ≤ R) :
    ∃ n : ℕ, WrPres ↥R (4 * 2 ^ n) ∧ (t = .PSL → ordProj[2] (p ^ f - 1) = 4 * 2 ^ n) ∧
      (t = .PSU → ordProj[2] (p ^ f + 1) = 4 * 2 ^ n) := by
  rcases ht with rfl | rfl
  · obtain ⟨n, hn⟩ := ordProj_two_eq_four_mul (N := p ^ f - 1) (by omega)
      (by have := hcong.1 rfl; omega)
    refine ⟨n, ?_, fun _ => hn, fun h => absurd h (by decide)⟩
    rw [← hn]
    exact lin_wr hp2 (hcong.1 rfl) hX hR hmax
  · obtain ⟨n, hn⟩ := ordProj_two_eq_four_mul (N := p ^ f + 1) (by omega)
      (by have := hcong.2 rfl; omega)
    refine ⟨n, ?_, fun h => absurd h (by decide), fun _ => hn⟩
    rw [← hn]
    exact uni_wr hp2 (hcong.2 rfl) hX hR hmax

theorem eq_of_mul_self_eq_one_of_cyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z] {x y : Z}
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype Z := Fintype.ofFinite Z
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have hdvd : 2 ∣ Fintype.card Z := hx2 ▸ orderOf_dvd_card
  have hc := IsCyclic.card_orderOf_eq_totient hdvd
  rw [Nat.totient_two] at hc
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
  have hxa : x ∈ ({a} : Finset Z) := by rw [← ha]; simp [hx2]
  have hya : y ∈ ({a} : Finset Z) := by rw [← ha]; simp [hy2]
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

theorem l3eps_unique_central_involution {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X t 3 p f) {R : Subgroup X} (hR : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup X, IsPGroup 2 T → R ≤ T → T ≤ R) :
    ∀ x y : ↥R, (∀ r : ↥R, x * r = r * x) → (∀ r : ↥R, y * r = r * y) → x * x = 1 → y * y = 1 →
      x ≠ 1 → y ≠ 1 → x = y := by
  intro x y hxc hyc hx2 hy2 hx1 hy1
  have hfin : Finite X := by
    rcases ht with rfl | rfl
    · exact (lin_model_card hp2 hX).1
    · exact (uni_model_card hp2 hX).1
  obtain ⟨hcyc, -, -⟩ := l3eps_center_sylow ht hp2 hX hR hmax
  have hZ : ∀ x : ↥R, (∀ r : ↥R, x * r = r * x) →
      (x : X) ∈ R ⊓ Subgroup.centralizer (R : Set X) := by
    intro x hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (hx ⟨g, hg⟩).symm
  have hx2' : (⟨(x : X), hZ x hxc⟩ : ↥(R ⊓ Subgroup.centralizer (R : Set X))) *
      ⟨(x : X), hZ x hxc⟩ = 1 := by
    apply Subtype.ext
    show (x : X) * (x : X) = 1
    exact congrArg Subtype.val hx2
  have hy2' : (⟨(y : X), hZ y hyc⟩ : ↥(R ⊓ Subgroup.centralizer (R : Set X))) *
      ⟨(y : X), hZ y hyc⟩ = 1 := by
    apply Subtype.ext
    show (y : X) * (y : X) = 1
    exact congrArg Subtype.val hy2
  have hx1' : (⟨(x : X), hZ x hxc⟩ : ↥(R ⊓ Subgroup.centralizer (R : Set X))) ≠ 1 := by
    intro h
    apply hx1
    apply Subtype.ext
    have h' : (x : X) = 1 := congrArg Subtype.val h
    exact h'
  have hy1' : (⟨(y : X), hZ y hyc⟩ : ↥(R ⊓ Subgroup.centralizer (R : Set X))) ≠ 1 := by
    intro h
    apply hy1
    apply Subtype.ext
    have h' : (y : X) = 1 := congrArg Subtype.val h
    exact h'
  have key := eq_of_mul_self_eq_one_of_cyclic hx2' hy2' hx1' hy1'
  exact Subtype.ext (Subtype.mk.inj key)

end Models

end CFSG.GH74.KGroups.L3Eps
