module

public import CFSG.Quasithin.H13.A5W1622x
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Matrix

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_rho_theta_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    [hsP : IsSimpleGroup ↥(S.plus K)] (hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a) :
    ∃ (ρ : ↥K →* ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K))
      (θ : ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K) →* ↥(S.plus K)),
      Function.Surjective ρ ∧ Function.Surjective θ ∧
      (∀ k : ↥K, ρ k = 1 → ∃ n : ℕ, (k : G) ^ 2 ^ n = 1) ∧
      ∀ k : ↥K, θ (ρ k) = 1 ↔
        (k : G) ∈ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set W := S.WK K with hWdef
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hYz.1 hT
  have hKW : K ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left : K ≤ S.HK K).trans hR.2.1
  have hKG : K ≤ Gv := le_of_mem_cComp hK
  set N₂ := CFSG.pCore 2 ↥Gv with hN₂
  have hN₂n : N₂.Normal := CFSG.pCore_normal
  set σ : ↥Gv →* ↥Gv ⧸ N₂ := QuotientGroup.mk' N₂ with hσ
  set X := modO2Image Gv K with hX
  let ρ : ↥K →* ↥X := (σ.comp (Subgroup.inclusion hKG)).codRestrict X
    (fun k => ⟨⟨k, hKG k.2⟩, k.2, rfl⟩)
  have hρσ : ∀ k : ↥K, ((ρ k : ↥X) : ↥Gv ⧸ N₂) = σ ⟨k, hKG k.2⟩ := fun k => rfl
  have hρs : Function.Surjective ρ := by
    rintro ⟨x, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hρ1 : ∀ k : ↥K, ρ k = 1 → ∃ n : ℕ, (k : G) ^ 2 ^ n = 1 := by
    intro k hk
    have h1 : σ ⟨k, hKG k.2⟩ = 1 := by
      rw [← hρσ, hk]
      rfl
    have h2 : (⟨k, hKG k.2⟩ : ↥Gv) ∈ N₂ := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Gv)) ⟨_, h2⟩
    refine ⟨n, ?_⟩
    have := congrArg (fun x : ↥N₂ => ((x : ↥Gv) : G)) hn
    simpa using this
  let φ : ↥K →* ↥(S.plus K) := InternalSec.autOnHom hKW
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW
  have hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ Subgroup.centralizer ((W : Subgroup G) : Set G) :=
    fun k => MonoidHom.mem_ker.symm.trans (InternalSec.mem_ker_autOnHom hKW k)
  have hO2P : pCoreOf 2 (S.plus K) = ⊥ := by
    rw [pCoreOf, ← CFSG.pCore_eq_open, pCore_two_eq_bot_of_simple hna, Subgroup.map_bot]
  have hle : ρ.ker ≤ φ.ker := by
    have h1 : ρ.ker ≤ CFSG.pCore 2 ↥K := by
      have hp : IsPGroup 2 ↥ρ.ker := fun x => by
        obtain ⟨n, hn⟩ := hρ1 x x.2
        exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn))⟩
      exact le_sSup ⟨inferInstance, hp⟩
    exact h1.trans (InternalSec.pCore_le_ker_autOnHom hKW hO2P)
  let θ : ↥X →* ↥(S.plus K) := ρ.liftOfSurjective hρs ⟨φ, hle⟩
  have hθρ : ∀ k, θ (ρ k) = φ k := fun k => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  refine ⟨ρ, θ, hρs, fun y => ?_, hρ1, fun k => by rw [hθρ]; exact hφk k⟩
  obtain ⟨k, rfl⟩ := hφs y
  exact ⟨ρ k, hθρ k⟩

theorem exists_reduced_of_case3_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) [hsP : IsSimpleGroup ↥(S.plus K)]
    (hna : ∃ a b : ↥(S.plus K), a * b ≠ b * a) (h168 : Nat.card ↥(S.plus K) = 168)
    (h3 : A36Case3 ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K)) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧ K₀ ∈ lFamily S.Tv ∧ S.Tv ≤ Subgroup.normalizer (K₀ : Set G) ∧
      S.Lv ≤ Subgroup.normalizer (K₀ : Set G) ∧ autOn K₀ (S.WK K) = S.plus K ∧
      IsPGroup 2 ↥(K₀ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  set W := S.WK K with hWdef
  set C := Subgroup.centralizer ((W : Subgroup G) : Set G) with hCdef
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hYz.1 hT
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) := hKHK.trans hR.2.1
  have hTW : S.Tv ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    (S.Tv_le_HK K).trans hR.2.1
  have hLvW : S.Lv ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    ((le_sup_right.trans le_sup_left : S.Lv ≤ S.HK K)).trans hR.2.1
  have hLvK : S.Lv ≤ Subgroup.normalizer (K : Set G) :=
    S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  have hKG : K ≤ Gv := le_of_mem_cComp hK
  have hCN : ∀ g ∈ Subgroup.normalizer ((W : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizer_of_mem_normalizer hg

  set P := K ⊓ C with hPdef
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hCN k (hKW hk)⟩
  have hTP : S.Tv ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hT ht, hCN t (hTW ht)⟩
  set S₂ := S.Tv ⊓ P with hS₂def
  have hsylKT : IsSylowTwoOf S.Tv (K ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right (sup_le hKG S.Tv_le_Gv)
  have hS₂ : IsSylowTwoOf S₂ P :=
    A4.isSylowTwoOf_inf_normal hsylKT (inf_le_left.trans le_sup_left) (sup_le hKP hTP)
  have hS₂2 : ∀ g ∈ S₂, ∃ n : ℕ, g ^ 2 ^ n = 1 := fun g hg => by
    obtain ⟨n, hn⟩ := hS₂.2.1 ⟨g, hg⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

  set N₂ := CFSG.pCore 2 ↥Gv with hN₂
  have hN₂n : N₂.Normal := CFSG.pCore_normal
  set σ : ↥Gv →* ↥Gv ⧸ N₂ := QuotientGroup.mk' N₂ with hσ
  set X := modO2Image Gv K with hX
  let ρ : ↥K →* ↥X := (σ.comp (Subgroup.inclusion hKG)).codRestrict X
    (fun k => ⟨⟨k, hKG k.2⟩, k.2, rfl⟩)
  have hρσ : ∀ k : ↥K, ((ρ k : ↥X) : ↥Gv ⧸ N₂) = σ ⟨k, hKG k.2⟩ := fun k => rfl
  have hρs : Function.Surjective ρ := by
    rintro ⟨x, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hρ1 : ∀ k : ↥K, ρ k = 1 → ∃ n : ℕ, (k : G) ^ 2 ^ n = 1 := by
    intro k hk
    have h1 : σ ⟨k, hKG k.2⟩ = 1 := by
      rw [← hρσ, hk]
      rfl
    have h2 : (⟨k, hKG k.2⟩ : ↥Gv) ∈ N₂ := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Gv)) ⟨_, h2⟩
    refine ⟨n, ?_⟩
    have := congrArg (fun x : ↥N₂ => ((x : ↥Gv) : G)) hn
    simpa using this

  let φ : ↥K →* ↥(S.plus K) := InternalSec.autOnHom hKW
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW
  have hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ C := fun k =>
    MonoidHom.mem_ker.symm.trans (InternalSec.mem_ker_autOnHom hKW k)
  have hO2P : pCoreOf 2 (S.plus K) = ⊥ := by
    rw [pCoreOf, ← CFSG.pCore_eq_open, pCore_two_eq_bot_of_simple hna, Subgroup.map_bot]
  have hle : ρ.ker ≤ φ.ker := by
    have h1 : ρ.ker ≤ CFSG.pCore 2 ↥K := by
      have hp : IsPGroup 2 ↥ρ.ker := fun x => by
        obtain ⟨n, hn⟩ := hρ1 x x.2
        exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn))⟩
      exact le_sSup ⟨inferInstance, hp⟩
    exact h1.trans (InternalSec.pCore_le_ker_autOnHom hKW hO2P)
  let θ : ↥X →* ↥(S.plus K) := ρ.liftOfSurjective hρs ⟨φ, hle⟩
  have hθρ : ∀ k, θ (ρ k) = φ k := fun k => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k
  have hθs : Function.Surjective θ := fun y => by
    obtain ⟨k, rfl⟩ := hφs y
    exact ⟨ρ k, hθρ k⟩

  set FX := CFSG.fittingSubgroup ↥X with hFX
  obtain ⟨p, hp, hp3, -, -, e, ψ, hψs, hψk, hact⟩ := h3
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    omega
  have hFc : ∀ a ∈ FX, ∀ b ∈ FX, a * b = b * a := by
    intro a ha b hb
    have h1 : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (e.injective h1)
  have hFcard : Nat.card FX = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hFcop : ∀ x ∈ FX, ∀ N : ℕ, Nat.Coprime N p → x ^ N = 1 → x = 1 := by
    intro x hx N hN hxN
    have h1 : orderOf (⟨x, hx⟩ : ↥FX) ∣ N :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxN))
    have h2 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥FX)
    rw [hFcard] at h2
    have h3 : Nat.Coprime (orderOf (⟨x, hx⟩ : ↥FX)) (p ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.Coprime.coprime_dvd_left h1 hN)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2))
  have hcop2 : ∀ n : ℕ, Nat.Coprime (2 ^ n) p := fun n =>
    Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  have hFθ : FX ≤ θ.ker := le_ker_of_simple hFc hna θ hθs

  have : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  let m : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := -1
  have hmm : ((m : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
    simp only [m, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    rfl
  have hmc : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), A * m = m * A := fun A => by
    rw [show m = -1 from rfl, mul_neg_one, neg_one_mul]
  have hm1 : m ≠ 1 := by
    intro h
    have h1 : ((m : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 =
        ((1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 :=
      by rw [h]
    rw [hmm, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h1
    have : Fact (2 < p) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one h1

  have hpm : ∀ k : ↥K, (k : G) ∈ C → ψ (ρ k) = 1 ∨ ψ (ρ k) = m := by
    intro k hkC
    rcases psi_eq_of_mem_ker ψ hψs hψk hFc hp hp5 hna θ hθs
      (by rw [hθρ]; exact (hφk k).mpr hkC) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.trans hmm.symm))

  have hψF : ∀ x : ↥X, ψ x = 1 → x ∈ FX := fun x hx => by
    have h := MonoidHom.mem_ker.mpr hx
    rwa [hψk] at h

  have hcard : Nat.card ↥(S.plus K) ≠ p * (p ^ 2 - 1) := by
    rw [h168]
    intro h
    rcases Nat.lt_or_ge p 6 with hp6 | hp6
    · interval_cases p
      omega
    · have h1 : 35 ≤ p ^ 2 - 1 := by
        have : 36 ≤ p ^ 2 := by nlinarith
        omega
      have h2 : 6 * 35 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp6 h1
      omega
  obtain ⟨x₀, hx₀θ, hx₀ψ⟩ := exists_mem_ker_neg_one ψ hψs hψk hFc hp hp5 hna θ hθs hcard
  obtain ⟨k₀, rfl⟩ := hρs x₀
  have hk₀C : (k₀ : G) ∈ C := (hφk k₀).mp (by rw [← hθρ]; exact hx₀θ)
  have hk₀m : ψ (ρ k₀) = m := Subtype.ext (hx₀ψ.trans hmm.symm)

  obtain ⟨j, n₀, hn₀, hjn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k₀).ne'
  set u := k₀ ^ n₀ with hu
  have hu2 : (u : G) ^ 2 ^ j = 1 := by
    have h1 : u ^ 2 ^ j = 1 := by
      rw [hu, ← pow_mul, mul_comm, ← hjn, pow_orderOf_eq_one]
    simpa using congrArg Subtype.val h1
  have hum : ψ (ρ u) = m := by
    rw [hu, map_pow, map_pow, hk₀m, show m = -1 from rfl]
    exact hn₀.neg_one_pow
  have huP : (u : G) ∈ P := ⟨u.2, by rw [hu, Subgroup.coe_pow]; exact C.pow_mem hk₀C n₀⟩
  have hzu : IsPGroup 2 (Subgroup.zpowers (u : G)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨j, Subtype.ext ?_⟩
    show ((u : G) ^ i) ^ 2 ^ j = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
  obtain ⟨q, hqP, hqle⟩ := F7.isSylowTwoOf_exists_conj_le hS₂ (Subgroup.zpowers_le.mpr huP) hzu
  have hs'mem : q⁻¹ * (u : G) * q ∈ S₂ := mem_conjSub.mp (hqle (Subgroup.mem_zpowers _))
  set q' : ↥K := ⟨q, hqP.1⟩ with hq'
  set sK : ↥K := q'⁻¹ * u * q' with hsK
  have hsKG : (sK : G) = q⁻¹ * (u : G) * q := by simp [hsK, hq']
  have hsS₂ : (sK : G) ∈ S₂ := hsKG ▸ hs'mem
  have hsm : ψ (ρ sK) = m := by
    rw [hsK]
    simp only [map_mul, map_inv]
    rw [hum, hmc, inv_mul_cancel_right]

  have hsC : (sK : G) ∈ C := (hS₂.1 hsS₂).2
  have hs2' : ρ sK * ρ sK = 1 := by
    have hF1 : ρ sK * ρ sK ∈ FX := hψF _ (by
      rw [map_mul, hsm, show m = -1 from rfl, neg_mul_neg, one_mul])
    obtain ⟨n, hn⟩ := hS₂2 _ hsS₂
    refine hFcop _ hF1 (2 ^ n) (hcop2 n) ?_
    rw [← map_mul, ← map_pow]
    have : (sK * sK) ^ 2 ^ n = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul]
      have h1 : sK ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [h1, one_pow]
    rw [this, map_one]
  have huniq : ∀ k : ↥K, (k : G) ∈ S₂ → ψ (ρ k) = m → ρ k = ρ sK := by
    intro k hk hkm
    have hF1 : ρ (k * sK⁻¹) ∈ FX := hψF _ (by rw [map_mul, map_mul, map_inv, map_inv, hkm,
      hsm, mul_inv_cancel])
    have hkS : ((k * sK⁻¹ : ↥K) : G) ∈ S₂ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact S₂.mul_mem hk (S₂.inv_mem hsS₂)
    obtain ⟨n, hn⟩ := hS₂2 _ hkS
    have h1 := hFcop _ hF1 (2 ^ n) (hcop2 n) (by
      rw [← map_pow]
      have : (k * sK⁻¹) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [this, map_one])
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hρs1 : ρ sK ≠ 1 := fun h => hm1 (by rw [← hsm, h, map_one])

  have hconj_m : ∀ k : ↥K, (k : G) ∈ C → (∃ n : ℕ, (k : G) ^ 2 ^ n = 1) →
      (ρ k = 1 → ρ sK = 1) → ψ (ρ k) = m := by
    intro k hkC ⟨n, hn⟩ himp
    rcases hpm k hkC with h | h
    · exfalso
      apply hρs1
      apply himp
      refine hFcop _ (hψF _ h) (2 ^ n) (hcop2 n) ?_
      rw [← map_pow]
      have : k ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [this, map_one]
    · exact h

  set σs : ↥Gv ⧸ N₂ := σ ⟨sK, hKG sK.2⟩ with hσs
  have hσconj : ∀ (g : G) (hg : g ∈ Gv) (hgK : g * (sK : G) * g⁻¹ ∈ K),
      ρ ⟨g * (sK : G) * g⁻¹, hgK⟩ = ρ sK → σ ⟨g, hg⟩ * σs = σs * σ ⟨g, hg⟩ := by
    intro g hg hgK h
    have h1 := congrArg Subtype.val h
    rw [hρσ, hρσ] at h1
    have h2 : (⟨g * (sK : G) * g⁻¹, hKG hgK⟩ : ↥Gv) = ⟨g, hg⟩ * ⟨sK, hKG sK.2⟩ * ⟨g, hg⟩⁻¹ :=
      Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc σ ⟨g, hg⟩ * σs = σ ⟨g, hg⟩ * σs * (σ ⟨g, hg⟩)⁻¹ * σ ⟨g, hg⟩ := by group
      _ = σs * σ ⟨g, hg⟩ := by rw [h1]

  have hconj1 : ∀ (g : G) (hg : g ∈ Gv) (hgK : g * (sK : G) * g⁻¹ ∈ K),
      ρ ⟨g * (sK : G) * g⁻¹, hgK⟩ = 1 → ρ sK = 1 := by
    intro g hg hgK h
    have h1 := congrArg Subtype.val h
    rw [hρσ] at h1
    have h2 : (⟨g * (sK : G) * g⁻¹, hKG hgK⟩ : ↥Gv) = ⟨g, hg⟩ * ⟨sK, hKG sK.2⟩ * ⟨g, hg⟩⁻¹ :=
      Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_inv] at h1
    apply Subtype.ext
    rw [hρσ]
    calc σ ⟨sK, hKG sK.2⟩ = (σ ⟨g, hg⟩)⁻¹ * (σ ⟨g, hg⟩ * σ ⟨sK, hKG sK.2⟩ * (σ ⟨g, hg⟩)⁻¹) *
          σ ⟨g, hg⟩ := by group
      _ = 1 := by rw [h1]; simp
  have hS₂conj : ∀ (g : G), (∃ n : ℕ, (sK : G) ^ 2 ^ n = 1) →
      ∃ n : ℕ, (g * (sK : G) * g⁻¹) ^ 2 ^ n = 1 := by
    rintro g ⟨n, hn⟩
    exact ⟨n, by rw [conj_pow, hn]; group⟩

  have hTs : ∀ t (ht : t ∈ S.Tv), σ ⟨t, S.Tv_le_Gv ht⟩ * σs = σs * σ ⟨t, S.Tv_le_Gv ht⟩ := by
    intro t ht
    have hk : t * (sK : G) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT ht) _).mp sK.2
    have hS : t * (sK : G) * t⁻¹ ∈ S₂ := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTP ht⟩) _).mp hsS₂
    refine hσconj t (S.Tv_le_Gv ht) hk (huniq ⟨_, hk⟩ hS ?_)
    exact hconj_m ⟨_, hk⟩ (hS₂.1 hS).2 (hS₂2 _ hS) (hconj1 t (S.Tv_le_Gv ht) hk)

  have hsT : (sK : G) ∈ S.Tv := hsS₂.1
  have hLvn : (S.LvQ.subgroupOf S.Lv).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer S.LvQ_le_Lv).mpr S.Lv_le_normalizer_LvQ
  have hidx : (S.LvQ.subgroupOf S.Lv).index ≤ 3 := S.relIndex_LvQ_le
  have hidx0 : (S.LvQ.subgroupOf S.Lv).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hLvs : ∀ y (hy : y ∈ S.Lv), σ ⟨y, S.Lv_le_Gv hy⟩ * σs = σs * σ ⟨y, S.Lv_le_Gv hy⟩ := by
    intro y hy
    have hyG := S.Lv_le_Gv hy
    have hk : y * (sK : G) * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hLvK hy) _).mp sK.2
    have hkC : y * (sK : G) * y⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hCN y (hLvW hy)) _).mp hsC
    have hkm : ψ (ρ ⟨_, hk⟩) = m :=
      hconj_m ⟨_, hk⟩ hkC (hS₂conj y (hS₂2 _ hsS₂)) (hconj1 y hyG hk)
    refine hσconj y hyG hk ?_

    have hc : y * (sK : G) * y⁻¹ * (sK : G)⁻¹ ∈ S.Lv := by
      have h1 : (sK : G) * y⁻¹ * (sK : G)⁻¹ ∈ S.Lv :=
        (Subgroup.mem_normalizer_iff.mp (S.Tv_le_normalizer_Lv hsT) _).mp (S.Lv.inv_mem hy)
      have e1 : y * (sK : G) * y⁻¹ * (sK : G)⁻¹ = y * ((sK : G) * y⁻¹ * (sK : G)⁻¹) := by group
      rw [e1]
      exact S.Lv.mul_mem hy h1

    have hcQ : (y * (sK : G) * y⁻¹ * (sK : G)⁻¹) ^ (S.LvQ.subgroupOf S.Lv).index ∈ S.LvQ := by
      have := Subgroup.pow_index_mem (S.LvQ.subgroupOf S.Lv) (⟨_, hc⟩ : ↥S.Lv)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    obtain ⟨n, hn⟩ := S.isPGroup_LvQ ⟨_, hcQ⟩
    have hcop : Nat.Coprime ((S.LvQ.subgroupOf S.Lv).index * 2 ^ n) p := by
      refine Nat.coprime_mul_iff_left.mpr ⟨?_, hcop2 n⟩
      refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hidx0) hd
      omega
    have hF1 : ρ (⟨_, hk⟩ * sK⁻¹) ∈ FX := hψF _ (by
      rw [map_mul, map_mul, map_inv, map_inv, hkm, hsm, mul_inv_cancel])
    have h1 := hFcop _ hF1 _ hcop (by
      rw [← map_pow]
      have : (⟨_, hk⟩ * sK⁻¹ : ↥K) ^ ((S.LvQ.subgroupOf S.Lv).index * 2 ^ n) = 1 := by
        apply Subtype.ext
        rw [pow_mul]
        simpa using congrArg Subtype.val hn
      rw [this, map_one])
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1

  set CQ := Subgroup.centralizer ({σs} : Set (↥Gv ⧸ N₂)) with hCQ
  set PC : Subgroup G := K ⊓ (CQ.comap σ).map Gv.subtype with hPC
  have hmemPC : ∀ g (hg : g ∈ K), g ∈ PC ↔ σ ⟨g, hKG hg⟩ * σs = σs * σ ⟨g, hKG hg⟩ := by
    intro g hg
    constructor
    · rintro ⟨-, g', hg', rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp hg'
    · intro h
      exact ⟨hg, ⟨g, hKG hg⟩, Subgroup.mem_centralizer_singleton_iff.mpr h, rfl⟩
  have hPCnorm : ∀ g (hg : g ∈ Gv), g ∈ Subgroup.normalizer (K : Set G) →
      σ ⟨g, hg⟩ * σs = σs * σ ⟨g, hg⟩ → g ∈ Subgroup.normalizer (PC : Set G) := by
    intro g hg hgK hgs
    refine mem_normalizer_of_conj_mem fun k hk => ?_
    have hkK : k ∈ K := hk.1
    have hk' : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK k).mp hkK
    rw [hmemPC _ hk']
    have hks := (hmemPC k hkK).mp hk
    have h2 : (⟨g * k * g⁻¹, hKG hk'⟩ : ↥Gv) = ⟨g, hg⟩ * ⟨k, hKG hkK⟩ * ⟨g, hg⟩⁻¹ :=
      Subtype.ext rfl
    rw [h2, map_mul, map_mul, map_inv]
    have hginv : (σ ⟨g, hg⟩)⁻¹ * σs = σs * (σ ⟨g, hg⟩)⁻¹ := by
      calc (σ ⟨g, hg⟩)⁻¹ * σs = (σ ⟨g, hg⟩)⁻¹ * (σs * σ ⟨g, hg⟩) * (σ ⟨g, hg⟩)⁻¹ := by group
        _ = (σ ⟨g, hg⟩)⁻¹ * (σ ⟨g, hg⟩ * σs) * (σ ⟨g, hg⟩)⁻¹ := by rw [hgs]
        _ = σs * (σ ⟨g, hg⟩)⁻¹ := by group
    calc σ ⟨g, hg⟩ * σ ⟨k, hKG hkK⟩ * (σ ⟨g, hg⟩)⁻¹ * σs
        = σ ⟨g, hg⟩ * σ ⟨k, hKG hkK⟩ * ((σ ⟨g, hg⟩)⁻¹ * σs) := by group
      _ = σ ⟨g, hg⟩ * σ ⟨k, hKG hkK⟩ * (σs * (σ ⟨g, hg⟩)⁻¹) := by rw [hginv]
      _ = σ ⟨g, hg⟩ * (σ ⟨k, hKG hkK⟩ * σs) * (σ ⟨g, hg⟩)⁻¹ := by group
      _ = σ ⟨g, hg⟩ * (σs * σ ⟨k, hKG hkK⟩) * (σ ⟨g, hg⟩)⁻¹ := by rw [hks]
      _ = (σ ⟨g, hg⟩ * σs) * σ ⟨k, hKG hkK⟩ * (σ ⟨g, hg⟩)⁻¹ := by group
      _ = (σs * σ ⟨g, hg⟩) * σ ⟨k, hKG hkK⟩ * (σ ⟨g, hg⟩)⁻¹ := by rw [hgs]
      _ = σs * (σ ⟨g, hg⟩ * σ ⟨k, hKG hkK⟩ * (σ ⟨g, hg⟩)⁻¹) := by group
  have hTPC : S.Tv ≤ Subgroup.normalizer (PC : Set G) := fun t ht =>
    hPCnorm t (S.Tv_le_Gv ht) (hT ht) (hTs t ht)
  have hLvPC : S.Lv ≤ Subgroup.normalizer (PC : Set G) := fun y hy =>
    hPCnorm y (S.Lv_le_Gv hy) (hLvK hy) (hLvs y hy)

  have hodd : Odd (Nat.card FX) := by rw [hFcard]; exact (hp.odd_of_ne_two (by omega)).pow
  have hsmat : ((ψ (ρ sK) : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by rw [hsm]; exact hmm
  have hsinv : (ρ sK)⁻¹ = ρ sK := (eq_inv_of_mul_eq_one_left hs2').symm
  have hfr : ∀ k : ↥K, ∃ k₄ : ↥K, (k₄ : G) ∈ C ∧ ((k₄ * k : ↥K) : G) ∈ PC := by
    intro k
    set k₃ : ↥K := k * sK * k⁻¹ with hk₃
    have hk₃C : (k₃ : G) ∈ C := by
      simp only [hk₃, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hCN k (hKW k.2)) _).mp hsC
    have hk₃K : (k : G) * (sK : G) * (k : G)⁻¹ ∈ K := k₃.2
    have hk₃m : ψ (ρ k₃) = m := hconj_m k₃ hk₃C (hS₂conj k (hS₂2 _ hsS₂))
      (fun h => hconj1 k (hKG k.2) hk₃K h)
    have hf₀ : (ρ sK)⁻¹ * ρ k₃ ∈ FX := hψF _ (by rw [map_mul, map_inv, hsm, hk₃m, inv_mul_cancel])
    set f₀ : ↥X := (ρ sK)⁻¹ * ρ k₃ with hf₀def
    set f₁ : ↥X := f₀ ^ ((p ^ 2 + 1) / 2) with hf₁def
    have hf₁ : f₁ ∈ FX := FX.pow_mem hf₀ _
    have hf₁sq : f₁ * f₁ = f₀ := by
      have h1 : f₀ ^ (p ^ 2) = 1 := by
        have := pow_card_eq_one' (G := ↥FX) (x := ⟨f₀, hf₀⟩)
        rw [hFcard] at this
        simpa using congrArg Subtype.val this
      have h2 : (p ^ 2 + 1) / 2 * 2 = p ^ 2 + 1 :=
        Nat.div_mul_cancel ((hp.odd_of_ne_two (by omega)).pow.add_one.two_dvd)
      calc f₁ * f₁ = f₀ ^ ((p ^ 2 + 1) / 2 * 2) := by
            rw [hf₁def, pow_mul, pow_two (f₀ ^ ((p ^ 2 + 1) / 2))]
        _ = f₀ := by rw [h2, pow_succ, h1, one_mul]
    have hconj : f₁⁻¹ * ρ sK * f₁ = ρ k₃ := by
      have h1 : (ρ sK)⁻¹ * f₁⁻¹ * ρ sK = f₁ := by
        rw [show (ρ sK)⁻¹ * f₁⁻¹ * ρ sK = ρ sK * f₁⁻¹ * (ρ sK)⁻¹ by rw [hsinv],
          conj_eq_inv_of_neg_one e ψ hact hsmat ⟨f₁⁻¹, FX.inv_mem hf₁⟩]
        simp
      calc f₁⁻¹ * ρ sK * f₁ = ρ sK * ((ρ sK)⁻¹ * f₁⁻¹ * ρ sK) * f₁ := by group
        _ = ρ sK * f₀ := by rw [h1, mul_assoc, hf₁sq]
        _ = ρ k₃ := by rw [hf₀def, mul_inv_cancel_left]
    obtain ⟨k₄, hk₄⟩ := hρs f₁
    have hk₄C : (k₄ : G) ∈ C := (hφk k₄).mp (by rw [← hθρ, hk₄]; exact hFθ hf₁)
    refine ⟨k₄, hk₄C, (hmemPC _ (k₄ * k).2).mpr ?_⟩
    have hX : ρ (k₄ * k) * ρ sK = ρ sK * ρ (k₄ * k) := by
      have ha : ρ k₃ = ρ k * ρ sK * (ρ k)⁻¹ := by rw [hk₃, map_mul, map_mul, map_inv]
      have h1 := hconj.trans ha
      rw [map_mul, hk₄]
      calc f₁ * ρ k * ρ sK = f₁ * (ρ k * ρ sK * (ρ k)⁻¹) * ρ k := by group
        _ = f₁ * (f₁⁻¹ * ρ sK * f₁) * ρ k := by rw [h1]
        _ = ρ sK * (f₁ * ρ k) := by group
    have := congrArg Subtype.val hX
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hρσ, hρσ] at this
    exact this

  have hPCK : PC ≤ K := inf_le_left
  have hPCW : PC ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) := hPCK.trans hKW
  have hPCim : autOn PC W = S.plus K := by
    apply le_antisymm (A4.autOn_mono hPCK)
    intro a ha
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 ha
    obtain ⟨k₄, hk₄C, hk₄PC⟩ := hfr ⟨k, hk⟩
    refine Setup.mem_autOn_iff.2 ⟨⟨(k₄ : G) * k, hPCW hk₄PC⟩, hk₄PC, ?_⟩
    have h1 : conjAct W ⟨k₄, hKW k₄.2⟩ = 1 := conjAct_eq_one_of_mem_centralizer _ hk₄C
    calc conjAct W ⟨(k₄ : G) * k, hPCW hk₄PC⟩ =
        conjAct W (⟨k₄, hKW k₄.2⟩ * ⟨k, hkN⟩) := rfl
      _ = conjAct W ⟨k, hkN⟩ := by rw [map_mul, h1, one_mul]

  set K₀ := perfectCore PC with hK₀def
  have hK₀PC : K₀ ≤ PC := perfectCore_le PC
  have hK₀W : K₀ ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) := hK₀PC.trans hPCW
  have hpP := qs_perfect_ne_bot (S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT)
  have hK₀im : autOn K₀ W = S.plus K := by
    rw [hK₀def, autOn_perfectCore hPCW, hPCim, perfectCore_eq_self_of_perfect hpP.1]
  have hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G) :=
    hTPC.trans (normalizer_le_normalizer_perfectCore PC)
  have hLvK₀ : S.Lv ≤ Subgroup.normalizer (K₀ : Set G) :=
    hLvPC.trans (normalizer_le_normalizer_perfectCore PC)
  have hK₀2 : IsPGroup 2 ↥(K₀ ⊓ C) := by
    rintro ⟨k, hkK₀, hkC⟩
    have hkPC := hK₀PC hkK₀
    have hkK : k ∈ K := hkPC.1
    have hcomm : ρ ⟨k, hkK⟩ * ρ sK = ρ sK * ρ ⟨k, hkK⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hρσ, hρσ]
      exact (hmemPC k hkK).mp hkPC
    have hx : ψ (ρ ⟨k, hkK⟩) = 1 ∨ ψ (ρ ⟨k, hkK⟩) = ψ (ρ sK) := by
      rw [hsm]
      exact hpm ⟨k, hkK⟩ hkC
    rcases eq_one_or_eq_of_commute e ψ hψk hact hodd hsmat hx hcomm with h | h
    · obtain ⟨n, hn⟩ := hρ1 _ h
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · have h2 : ρ (⟨k, hkK⟩ * ⟨k, hkK⟩) = 1 := by rw [map_mul, h, hs2']
      obtain ⟨n, hn⟩ := hρ1 _ h2
      refine ⟨n + 1, Subtype.ext ?_⟩
      have h3 : k ^ 2 ^ (n + 1) = (k * k) ^ 2 ^ n := by
        rw [← sq, ← pow_mul, ← pow_succ']
      simpa [h3] using hn
  have hQ : autOn K₀ W ∈ cComp (autOn K₀ W) := by
    rw [hK₀im]
    have : Group.IsSolvable ↥(MonoidHom.id ↥(S.plus K)).ker := by
      rw [MonoidHom.ker_id]
      infer_instance
    exact S151S9U.mem_cComp_self_of_simple_quotient (MonoidHom.id _) Function.surjective_id
      hpP.2 hpP.1 this
  have : Group.IsNilpotent ↥(K₀ ⊓ C) := hK₀2.isNilpotent
  exact ⟨K₀, hK₀PC.trans hPCK, mem_lFamily_of_autOn (perfectCore_perfect PC) hK₀W hTK₀
    inferInstance hQ, hTK₀, hLvK₀, hK₀im, hK₀2⟩

end Setting

end CFSG.Quasithin.H13.A5
