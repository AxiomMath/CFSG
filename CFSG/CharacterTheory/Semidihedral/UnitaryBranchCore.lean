module

public import CFSG.CharacterTheory.DefectZeroSylow.Main
public import CFSG.Permutation.SylowTrivialIntersection

public section

open scoped Pointwise

namespace CFSG.Semidihedral.UnitaryBranch

open Subgroup MonoidHom


theorem three_mul_le_of_dvd_sub {p f m k : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hk : 2 ≤ k)
    (hkp : ¬ p ∣ k) (hfm : f < m) (hdvd : (p ^ f - 1) * k ∣ p ^ m - p ^ f) : 3 * f ≤ m := by
  obtain ⟨h, rfl⟩ : ∃ h, m = f + h := ⟨m - f, by omega⟩
  have hp1 : 1 < p := hp.one_lt
  have hpf : 1 < p ^ f := Nat.one_lt_pow (by omega) hp1
  have hph : 1 < p ^ h := Nat.one_lt_pow (by omega) hp1
  have hsplit : p ^ (f + h) - p ^ f = p ^ f * (p ^ h - 1) := by
    rw [pow_add, Nat.mul_sub, mul_one]
  rw [hsplit] at hdvd
  have hcop : Nat.Coprime ((p ^ f - 1) * k) (p ^ f) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul_left
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
      have h2 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h1 hd
      rw [Nat.sub_sub_self (by omega)] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      exact hkp
  have hdvd' : (p ^ f - 1) * k ∣ p ^ h - 1 := hcop.dvd_of_dvd_mul_left hdvd
  have hle : (p ^ f - 1) * k ≤ p ^ h - 1 := Nat.le_of_dvd (by omega) hdvd'
  have hdvd1 : p ^ f - 1 ∣ p ^ h - 1 := (Dvd.intro k rfl).trans hdvd'
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one p f h
  rw [Nat.gcd_eq_left hdvd1] at hgcd
  have hfg : f = Nat.gcd f h := by
    have : p ^ f = p ^ Nat.gcd f h := by omega
    exact Nat.pow_right_injective (le_refl 2 |>.trans hp.two_le) this
  have hfh : f ∣ h := by
    rw [hfg]
    exact Nat.gcd_dvd_right f h
  have hlt : f < h := by
    by_contra hcon
    have : p ^ h ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : (p ^ f - 1) * 2 ≤ (p ^ f - 1) * k := Nat.mul_le_mul_left _ hk
    omega
  obtain ⟨c, rfl⟩ := hfh
  rcases c with _ | _ | c
  · omega
  · omega
  · nlinarith

theorem conj_eq_of_mem {G : Type*} [Group G] [Finite G] {x : G} {K : Subgroup G}
    (hKcent : ∀ r ∈ K, ∀ g ∈ Subgroup.centralizer {x}, g * r = r * g)
    (hKconf : ∀ r ∈ K, r ≠ 1 → Subgroup.centralizer {r} ≤ Subgroup.centralizer {x})
    (S : Sylow 2 G) (hSN : (S : Subgroup G) ≤ Subgroup.centralizer {x})
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.centralizer {x})
    {r : G} (hr : r ∈ K) (g : G) (hg : g * r * g⁻¹ ∈ K) : g * r * g⁻¹ = r := by
  by_cases hr1 : r = 1
  · rw [hr1, mul_one, mul_inv_cancel]
  set N := Subgroup.centralizer ({x} : Set G) with hN
  have hr1' : g * r * g⁻¹ ≠ 1 := by
    intro h
    apply hr1
    have : r = g⁻¹ * (g * r * g⁻¹) * g := by group
    rw [this, h]
    group
  have hCN : ∀ y ∈ K, y ≠ 1 → Subgroup.centralizer {y} = N := by
    intro y hy hy1
    refine le_antisymm (hKconf y hy hy1) fun c hc => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKcent y hy c hc
  have hS1 : (S : Subgroup G) ≤ N := hSN
  have hS2 : ((g • S : Sylow 2 G) : Subgroup G) ≤ N := by
    rw [← hCN _ hg hr1']
    intro c hc
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hc
    have hc' : (MulAut.conj g)⁻¹ • c ∈ N := hS1 hc
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hc'
    rw [← hCN _ hr hr1, Subgroup.mem_centralizer_singleton_iff] at hc'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [this]
    calc g * (g⁻¹ * c * g) * g⁻¹ * (g * r * g⁻¹) = g * ((g⁻¹ * c * g) * r) * g⁻¹ := by group
      _ = g * (r * (g⁻¹ * c * g)) * g⁻¹ := by rw [hc']
      _ = g * r * g⁻¹ * (g * (g⁻¹ * c * g) * g⁻¹) := by group
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N (S.subtype hS1) ((g • S).subtype hS2)
  rw [Sylow.smul_subtype hS1 c] at hc
  have hcS : ((c : G) • S : Sylow 2 G) = g • S := Sylow.subtype_injective hc
  have hmem : (c : G)⁻¹ * g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [mul_smul, ← hcS, ← mul_smul, inv_mul_cancel, one_smul]
  have hgN : g ∈ N := by
    have : g = (c : G) * ((c : G)⁻¹ * g) := by group
    rw [this]
    exact N.mul_mem c.2 (hNS hmem)
  rw [hKcent r hr g hgN, mul_assoc, mul_inv_cancel, mul_one]




theorem isComplement'_ker_transfer {X : Type*} [Group X] [Finite X] (K : Subgroup X)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hfus : ∀ g r : X, r ∈ K → g * r * g⁻¹ ∈ K → g * r * g⁻¹ = r)
    (hcop : Nat.Coprime (Nat.card K) K.index) :
    ∃ L : Subgroup X, L.Normal ∧ IsComplement' L K := by
  have : IsMulCommutative K :=
    ⟨⟨fun a b => Subtype.ext (hKcomm a a.2 b b.2)⟩⟩
  open scoped IsMulCommutative in
  let τ : X →* K := transfer (MonoidHom.id K)
  have hτ : ∀ g : K, τ g = g ^ K.index := by
    intro g
    have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * (g : X) ^ k * g₀ ∈ K →
        g₀⁻¹ * (g : X) ^ k * g₀ = (g : X) ^ k := by
      intro k g₀ hmem
      have h := hfus g₀⁻¹ ((g : X) ^ k) (K.pow_mem g.2 k) (by rwa [inv_inv])
      rwa [inv_inv] at h
    open scoped IsMulCommutative in
    have := transfer_eq_pow (MonoidHom.id K) (g : X) key
    rw [this]
    apply Subtype.ext
    simp
  have hf : Function.Bijective (τ.domRestrict K) := by
    have : ⇑(τ.domRestrict K) = ⇑(powCoprime hcop) := by
      funext g
      rw [powCoprime_apply, MonoidHom.domRestrict_apply, hτ]
    rw [this]
    exact (powCoprime hcop).bijective
  refine ⟨τ.ker, inferInstance, ?_⟩
  rw [Function.Bijective, ← range_eq_top, domRestrict_range] at hf
  have := range_eq_top.mp (top_le_iff.mp (hf.2.ge.trans (map_le_range τ K)))
  rw [← (comap_injective this).eq_iff, comap_top, comap_map_eq, sup_comm, SetLike.ext'_iff,
    normal_mul, ← ker_eq_bot_iff, ← map_subtype_inj,
    ker_domRestrict, subgroupOf_map_subtype, Subgroup.map_bot, coe_top] at hf
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hf.1) hf.2




theorem card_dvd_card_of_free {H X : Type*} [Group H] [MulAction H X] [Finite H] [Finite X]
    (hfree : ∀ (h : H) (x : X), h • x = x → h = 1) : Nat.card H ∣ Nat.card X := by
  classical
  have := Fintype.ofFinite (Quotient (MulAction.orbitRel H X))
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer H X), Nat.card_sigma]
  apply Finset.dvd_sum
  intro ω _
  have hstab : MulAction.stabilizer H ω.out = ⊥ := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    exact ⟨hfree h _, fun h1 => h1 ▸ one_smul _ _⟩
  rw [hstab, Nat.card_congr (QuotientGroup.quotientBot (G := H)).toEquiv]

theorem eq_of_sq_eq_one_of_isCyclic {K : Type*} [Group K] [Finite K] [IsCyclic K] {a b : K}
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (hb : b ^ 2 = 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite K
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := K) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset K) ⊆ Finset.univ.filter (fun c : K => c ^ 2 = 1) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;> simp [*]
  have h3 : ({1, a, b} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem mem_of_orderOf_dvd_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (K : Subgroup H) {h : H} (hh : orderOf h ∣ Nat.card K) : h ∈ K := by
  classical
  have := Fintype.ofFinite H
  set k := Nat.card K
  have hk : 0 < k := Nat.card_pos
  have hle := IsCyclic.card_pow_eq_one_le (α := H) hk
  let T : Finset H := Finset.univ.filter (fun c : H => c ^ k = 1)
  let KS : Finset H := Finset.univ.filter (fun c : H => c ∈ K)
  have hKS : KS ⊆ T := by
    intro c hc
    simp only [KS, T, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    have h' : ((⟨c, hc⟩ : K) ^ k) = 1 := pow_card_eq_one'
    have h'' := congrArg (fun y : K => (y : H)) h'
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h''
    exact h''
  have hKScard : KS.card = k := by
    simp only [KS, k]
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have heq : KS = T := Finset.eq_of_subset_of_card_le hKS (by rw [hKScard]; exact hle)
  have hT : h ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact orderOf_dvd_iff_pow_eq_one.mp hh
  rw [← heq] at hT
  simpa [KS] using hT




theorem exists_pElement_complement {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (X K : Subgroup G) (hKX : K ≤ X)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hfus : ∀ r ∈ K, ∀ g : G, g * r * g⁻¹ ∈ K → g * r * g⁻¹ = r)
    (hKp : ¬ p ∣ Nat.card K) {e : ℕ} (hX : Nat.card X = Nat.card K * p ^ e) :
    ∃ Q : Subgroup G, Q ≤ X ∧ Nat.card Q = p ^ e ∧ Q ⊓ K = ⊥ ∧
      (∀ g ∈ X, ∃ a ∈ Q, ∃ b ∈ K, g = a * b) ∧
      (∀ g ∈ X, (∃ k : ℕ, orderOf g = p ^ k) → g ∈ Q) := by
  set K' : Subgroup X := K.subgroupOf X with hK'
  have hK'card : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
  have hK'index : K'.index = p ^ e := by
    have h := Subgroup.card_mul_index K'
    rw [hK'card, hX] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hcop : Nat.Coprime (Nat.card K') K'.index := by
    rw [hK'card, hK'index]
    exact Nat.Coprime.pow_right e (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      hKp))
  obtain ⟨L, hLn, hLK⟩ := isComplement'_ker_transfer K'
    (fun a ha b hb => Subtype.ext (hKcomm a ha b hb))
    (fun g r hr hgr => Subtype.ext (hfus r hr g hgr)) hcop
  have hLcard : Nat.card L = p ^ e := by
    have h := hLK.card_mul_card
    rw [hK'card, hX, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  refine ⟨L.map X.subtype, map_subtype_le L, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hLcard]
  · rw [eq_bot_iff]
    rintro g ⟨⟨l, hl, rfl⟩, hlK⟩
    have hlK' : l ∈ K' := hlK
    have h1 : l ∈ L ⊓ K' := ⟨hl, hlK'⟩
    rw [disjoint_iff.mp hLK.disjoint] at h1
    rw [Subgroup.mem_bot] at h1 ⊢
    rw [h1]
    rfl
  · intro g hg
    obtain ⟨⟨a, b⟩, hab, -⟩ := hLK.existsUnique ⟨g, hg⟩
    refine ⟨a, ⟨a, a.2, rfl⟩, b, b.2, ?_⟩
    have := congrArg Subtype.val hab
    simpa using this.symm
  · rintro g hg ⟨k, hk⟩
    obtain ⟨⟨a, b⟩, hab, -⟩ := hLK.existsUnique ⟨g, hg⟩
    simp only at hab
    have hbL : (b : X) ^ p ^ k ∈ L := by
      rw [← QuotientGroup.eq_one_iff (N := L), QuotientGroup.mk_pow]
      have ha1 : ((a : X) : X ⧸ L) = 1 := (QuotientGroup.eq_one_iff _).mpr a.2
      have hg1 : (((⟨g, hg⟩ : X)) : X ⧸ L) ^ p ^ k = 1 := by
        rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr]
        have : (⟨g, hg⟩ : X) ^ p ^ k = 1 := by
          apply Subtype.ext
          simp [← hk, pow_orderOf_eq_one]
        rw [this]
        exact L.one_mem
      rw [← hab, QuotientGroup.mk_mul, ha1, one_mul] at hg1
      exact hg1
    have hbK : (b : X) ^ p ^ k ∈ K' := K'.pow_mem b.2 _
    have hb1 : (b : X) ^ p ^ k = 1 := by
      have h1 : (b : X) ^ p ^ k ∈ L ⊓ K' := ⟨hbL, hbK⟩
      rwa [disjoint_iff.mp hLK.disjoint, Subgroup.mem_bot] at h1
    have hbo : orderOf (b : X) ∣ Nat.card K := by
      have h := orderOf_dvd_natCard (⟨(b : X), b.2⟩ : K')
      rwa [Subgroup.orderOf_mk, hK'card] at h
    have hbo' : orderOf (b : X) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hb1
    have hcop' : Nat.Coprime (Nat.card K) (p ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hKp))
    have hb : (b : X) = 1 := by
      rw [← orderOf_eq_one_iff]
      exact Nat.eq_one_of_dvd_coprimes hcop' hbo hbo'
    refine ⟨a, a.2, ?_⟩
    rw [hb, mul_one] at hab
    rw [hab]
    rfl

theorem eq_of_isPGroup_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Q₀ N T : Subgroup G} {f : ℕ} (hQ₀card : Nat.card Q₀ = p ^ f) (hQ₀N : Q₀ ≤ N)
    (hsyl : ¬ p ∣ Q₀.relIndex N) (hT : IsPGroup p T) (hTN : T ≤ N) (hQ₀T : Q₀ ≤ T) :
    T = Q₀ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := hT.exists_card_eq
  have hN : Nat.card N = p ^ f * Q₀.relIndex N := by
    have h := Subgroup.relIndex_mul_card (H := Q₀) (K := N)
    rw [inf_eq_left.mpr hQ₀N, hQ₀card] at h
    rw [← h, mul_comm]
  have hdvd : p ^ j ∣ p ^ f * Q₀.relIndex N := hj ▸ hN ▸ Subgroup.card_dvd_of_le hTN
  have hjf : j ≤ f := by
    by_contra hjf
    have h1 : p ^ f * p ∣ p ^ f * Q₀.relIndex N :=
      (pow_succ p f ▸ Nat.pow_dvd_pow p (by omega : f + 1 ≤ j)).trans hdvd
    exact hsyl (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos f) h1)
  refine (Subgroup.eq_of_le_of_card_ge hQ₀T ?_).symm
  rw [hj, hQ₀card]
  exact Nat.pow_le_pow_right hp.pos hjf

theorem exists_sylow_of_centralizer_data {G : Type} [Group G] [Finite G]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (x : G) (hx : orderOf x = 2)
    (K : Subgroup G) (hxK : x ∈ K)
    (hKcent : ∀ r ∈ K, ∀ g ∈ Subgroup.centralizer {x}, g * r = r * g)
    (hKp : ¬ p ∣ Nat.card K)
    (hKconf : ∀ r ∈ K, r ≠ 1 → Subgroup.centralizer {r} ≤ Subgroup.centralizer {x})
    (S : Sylow 2 G) (hSN : (S : Subgroup G) ≤ Subgroup.centralizer {x})
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.centralizer {x})
    (Q₀ : Subgroup G) (hQ₀card : Nat.card Q₀ = p ^ f)
    (hQ₀comm : ∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a)
    (hQ₀N : Q₀ ≤ Subgroup.centralizer {x})
    (hQ₀syl : ¬ p ∣ Q₀.relIndex (Subgroup.centralizer {x}))
    (H : Subgroup G) (hHQ₀ : H ≤ Subgroup.normalizer (Q₀ : Set G)) (hHcyc : IsCyclic H)
    (hKH : K ≤ H) (hHcard : Nat.card H = (p ^ f - 1) * Nat.card K)
    (hcent : ∀ u : G, u ≠ 1 → (∃ k : ℕ, orderOf u = p ^ k) →
      Nat.card (Subgroup.centralizer {u}) ∣ Nat.card K * (p ^ f) ^ 3)
    (hG : Nat.card G = Nat.card K * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1))
    {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G) (hχdeg : χ 1 = (((p ^ f) ^ 3 : ℕ) : ℂ)) :
    ∃ Q : Sylow p G, Nat.card Q = (p ^ f) ^ 3 ∧
      H ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧
      Nat.card G = (p ^ f) ^ 3 * ((p ^ f) ^ 3 + 1) * Nat.card H ∧
      ∃ Q₁ : Sylow p G, (Q : Subgroup G) ⊓ (Q₁ : Subgroup G) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set q := p ^ f with hqdef
  set N := Subgroup.centralizer ({x} : Set G) with hNdef
  set X := Subgroup.centralizer (Q₀ : Set G) with hXdef
  have hq1 : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hxN : x ∈ N := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKN : K ≤ N := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKcent r hr x hxN).symm
  have hKX : K ≤ X := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hKcent r hr a (hQ₀N ha)
  have hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := fun a ha b hb =>
    (hKcent a ha b (hKN hb)).symm
  have hfus : ∀ r ∈ K, ∀ g : G, g * r * g⁻¹ ∈ K → g * r * g⁻¹ = r :=
    fun r hr g hg => conj_eq_of_mem hKcent hKconf S hSN hNS hr g hg
  have hpelt : ∀ (T : Subgroup G) (e : ℕ), Nat.card T = p ^ e → ∀ g ∈ T,
      ∃ k : ℕ, orderOf g = p ^ k := by
    intro T e hT g hg
    have h := orderOf_dvd_natCard (⟨g, hg⟩ : T)
    rw [Subgroup.orderOf_mk, hT] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp h
    exact ⟨k, hk⟩
  obtain ⟨u, huQ₀, hu1⟩ : ∃ u ∈ Q₀, u ≠ 1 := by
    by_contra h
    push Not at h
    have h0 : Q₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [h0, Subgroup.card_bot] at hQ₀card
    omega
  have hXu : X ≤ Subgroup.centralizer {u} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huQ₀)
  have hXdvd : Nat.card X ∣ Nat.card K * q ^ 3 :=
    (Subgroup.card_dvd_of_le hXu).trans (hcent u hu1 (hpelt Q₀ f hQ₀card u huQ₀))
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hKX
  have hc' : c ∣ p ^ (f * 3) := by
    rw [hc, ← pow_mul] at hXdvd
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hXdvd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).mp hc'
  obtain ⟨Q, hQX, hQcard, hQK, hXdec, hQp⟩ :=
    exists_pElement_complement hp X K hKX hKcomm hfus hKp (e := e) (by rw [hc, he])
  have hQ₀X : Q₀ ≤ X := fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    hQ₀comm b hb a ha
  have hQ₀Q : Q₀ ≤ Q := fun a ha => hQp a (hQ₀X ha) (hpelt Q₀ f hQ₀card a ha)
  have hQpg : IsPGroup p Q := IsPGroup.of_card hQcard
  have hnormQ₀ : ∀ h ∈ Subgroup.normalizer (Q₀ : Set G), ∀ a, a ∈ Q₀ ↔ h * a * h⁻¹ ∈ Q₀ :=
    fun h hh a => Subgroup.mem_normalizer_iff.mp hh a
  have hconjX : ∀ h ∈ Subgroup.normalizer (Q₀ : Set G), ∀ g ∈ X, h * g * h⁻¹ ∈ X := by
    intro h hh g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro b hb
    have hb' : h⁻¹ * b * h ∈ Q₀ := by
      have := (hnormQ₀ h⁻¹ (Subgroup.inv_mem _ hh) b).mp hb
      rwa [inv_inv] at this
    have h1 := hg _ hb'
    calc b * (h * g * h⁻¹) = h * ((h⁻¹ * b * h) * g) * h⁻¹ := by group
      _ = h * (g * (h⁻¹ * b * h)) * h⁻¹ := by rw [h1]
      _ = h * g * h⁻¹ * b := by group
  have hconjQ : ∀ h ∈ Subgroup.normalizer (Q₀ : Set G), ∀ g ∈ Q, h * g * h⁻¹ ∈ Q := by
    intro h hh g hg
    refine hQp _ (hconjX h hh g (hQX hg)) ?_
    obtain ⟨k, hk⟩ := hpelt Q e hQcard g hg
    have h1 : (h * g * h⁻¹) ^ p ^ k = 1 := by
      rw [conj_pow, ← hk, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  have hHQ : H ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconjQ h (hHQ₀ hh) g, fun hg => ?_⟩
    have := hconjQ h⁻¹ (Subgroup.inv_mem _ (hHQ₀ hh)) _ hg
    simpa [mul_assoc] using this
  have hcopG : Nat.Coprime p (Nat.card K * (q - 1) * (q ^ 3 + 1)) := by
    have h1 : Nat.Coprime p (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hKp
    have h2 : Nat.Coprime p (q - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have h3 : p ∣ q - (q - 1) := Nat.dvd_sub hpq hd
      rw [Nat.sub_sub_self (by omega)] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    have h3 : Nat.Coprime p (q ^ 3 + 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have h4 : p ∣ q ^ 3 := dvd_pow hpq (by norm_num)
      have h5 : p ∣ q ^ 3 + 1 - q ^ 3 := Nat.dvd_sub hd h4
      rw [Nat.add_sub_cancel_left] at h5
      exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
    exact (h1.mul_right h2).mul_right h3
  have hGfac : Nat.card G = p ^ (3 * f) * (Nat.card K * (q - 1) * (q ^ 3 + 1)) := by
    rw [hG, hqdef, ← pow_mul]
    ring_nf
  have hfacG : (Nat.card G).factorization p = 3 * f := by
    rw [hGfac, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by
      intro h0
      rw [h0] at hGfac
      simp at hGfac
      exact (Nat.card_pos (α := G)).ne' hGfac)]
    rw [Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hp.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd hcopG h)), add_zero]
  have he3 : e ≤ 3 * f := by
    have h1 : p ^ e ∣ Nat.card G := hQcard ▸ Subgroup.card_subgroup_dvd_card Q
    rw [hGfac] at h1
    have h2 : p ^ e ∣ p ^ (3 * f) :=
      (Nat.Coprime.pow_left e hcopG).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
  have hQN : Q ⊓ N = Q₀ := eq_of_isPGroup_of_le hp hQ₀card hQ₀N hQ₀syl
    (hQpg.to_le inf_le_left) inf_le_right (le_inf hQ₀Q hQ₀N)
  have hfe : f ≤ e := by
    have h1 : p ^ f ∣ p ^ e := by
      have := Subgroup.card_dvd_of_le hQ₀Q
      rwa [hQ₀card, hQcard, hqdef] at this
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
  have hKcyc : IsCyclic K := by
    have : IsCyclic (K.subgroupOf H) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hKH).surjective
  have h3f : 3 * f ≤ e := by
    rcases (Nat.lt_or_eq_of_le hfe) with hlt | heq
    ·
      let Ω := {g : G // g ∈ Q ∧ g ∉ Q₀}
      have hQ₀inv : ∀ h ∈ H, ∀ g, h * g * h⁻¹ ∈ Q₀ → g ∈ Q₀ := fun h hh g hg =>
        (hnormQ₀ h (hHQ₀ hh) g).mpr hg
      let : MulAction H Ω :=
        { smul := fun h ω => ⟨h * ω.1 * h⁻¹, hconjQ h (hHQ₀ h.2) ω.1 ω.2.1,
            fun hmem => ω.2.2 (hQ₀inv h h.2 ω.1 hmem)⟩
          one_smul := fun ω => Subtype.ext (by
            show ((1 : H) : G) * ω.1 * ((1 : H) : G)⁻¹ = ω.1
            simp)
          mul_smul := fun h₁ h₂ ω => Subtype.ext (by
            show ((h₁ * h₂ : H) : G) * ω.1 * ((h₁ * h₂ : H) : G)⁻¹ =
              (h₁ : G) * ((h₂ : G) * ω.1 * (h₂ : G)⁻¹) * (h₁ : G)⁻¹
            rw [Subgroup.coe_mul]
            group) }
      have hfree : ∀ (h : H) (ω : Ω), h • ω = ω → h = 1 := by
        intro h ω hω
        have hcomm : (h : G) * ω.1 * (h : G)⁻¹ = ω.1 := congrArg Subtype.val hω
        have hω1 : ω.1 ≠ 1 := fun h1 => ω.2.2 (h1 ▸ Q₀.one_mem)
        have hhC : (h : G) ∈ Subgroup.centralizer {ω.1} := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (h : G) * ω.1 = (h : G) * ω.1 * (h : G)⁻¹ * h := by group
            _ = ω.1 * h := by rw [hcomm]
        have ho1 : orderOf (h : G) ∣ Nat.card K * q ^ 3 := by
          refine dvd_trans ?_ (hcent ω.1 hω1 (hpelt Q e hQcard ω.1 ω.2.1))
          have := orderOf_dvd_natCard (⟨h, hhC⟩ : Subgroup.centralizer {ω.1})
          rwa [Subgroup.orderOf_mk] at this
        have ho2 : orderOf (h : G) ∣ (q - 1) * Nat.card K := by
          rw [← hHcard, Subgroup.orderOf_coe]
          exact orderOf_dvd_natCard h
        have hcop1 : Nat.Coprime (q - 1) (q ^ 3) := by
          apply Nat.Coprime.pow_right
          have : q = (q - 1) + 1 := by omega
          conv_rhs => rw [this]
          exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
        have ho : orderOf (h : G) ∣ Nat.card K := by
          have ho1' : orderOf (h : G) ∣ q ^ 3 * Nat.card K := by
            rw [mul_comm]
            exact ho1
          have h1 := Nat.dvd_gcd ho2 ho1'
          rw [Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hcop1, one_mul] at h1
          exact h1
        have hhK : (h : G) ∈ K := by
          have hcardK' : Nat.card (K.subgroupOf H) = Nat.card K :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
          rw [Subgroup.orderOf_coe] at ho
          exact mem_of_orderOf_dvd_of_isCyclic (K.subgroupOf H) (h := h) (by rw [hcardK']; exact ho)
        by_contra hh1
        have hh1' : (h : G) ≠ 1 := fun h' => hh1 (Subtype.ext h')
        have hωN : ω.1 ∈ N := by
          apply hKconf _ hhK hh1'
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp hhC).symm
        have : ω.1 ∈ Q ⊓ N := ⟨ω.2.1, hωN⟩
        rw [hQN] at this
        exact ω.2.2 this
      have hdvdΩ : Nat.card H ∣ Nat.card Ω := card_dvd_card_of_free hfree
      have hΩ : Nat.card Ω = p ^ e - p ^ f := by
        have h1 : Nat.card Ω = ((Q : Set G) \ (Q₀ : Set G)).ncard := by
          rw [← Nat.card_coe_set_eq]
          rfl
        rw [h1, Set.ncard_sdiff (hQ₀Q : (Q₀ : Set G) ⊆ Q), ← Nat.card_coe_set_eq,
          ← Nat.card_coe_set_eq]
        change Nat.card Q - Nat.card Q₀ = _
        rw [hQcard, hQ₀card]
      have hK2 : 2 ≤ Nat.card K := by
        have := (Subgroup.one_lt_card_iff_ne_bot K).mpr (fun hb => hx1 (by
          rw [hb] at hxK
          exact (Subgroup.mem_bot).mp hxK))
        omega
      rw [hHcard, hΩ] at hdvdΩ
      exact three_mul_le_of_dvd_sub hp hf hK2 hKp hlt hdvdΩ
    ·
      exfalso
      have hQQ₀ : Q = Q₀ :=
        (Subgroup.eq_of_le_of_card_ge hQ₀Q (by rw [hQcard, hQ₀card, hqdef, heq])).symm
      obtain ⟨P, hP⟩ := (IsPGroup.of_card hQ₀card).exists_le_sylow
      have hPcard : Nat.card P = p ^ (3 * f) := by
        rw [Sylow.card_eq_multiplicity, hfacG]
      have hlt : Q₀.subgroupOf P < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have h1 : Nat.card (Q₀.subgroupOf P) = Nat.card Q₀ :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
        rw [htop, Subgroup.card_top, hPcard, hQ₀card] at h1
        have := Nat.pow_right_injective (le_refl 2 |>.trans hp.two_le) h1
        omega
      have : Group.IsNilpotent P := (Sylow.isPGroup' P).isNilpotent
      obtain ⟨g, hgN, hgQ₀⟩ :=
        IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
      have hgQ₀' : (g : G) ∉ Q₀ := fun h => hgQ₀ h
      set g' : G := (g : G) with hg'
      have hgnorm : ∀ a ∈ Q₀, g'⁻¹ * a * g' ∈ Q₀ := by
        intro a ha
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) ⟨a, hP ha⟩).mp ha
        have h2 := Subgroup.mem_subgroupOf.mp h1
        simpa [hg'] using h2
      have hy : g' * x * g'⁻¹ ∈ X := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have h1 := Subgroup.mem_centralizer_iff.mp (hKX hxK) _ (hgnorm b hb)
        calc b * (g' * x * g'⁻¹) = g' * ((g'⁻¹ * b * g') * x) * g'⁻¹ := by group
          _ = g' * (x * (g'⁻¹ * b * g')) * g'⁻¹ := by rw [h1]
          _ = g' * x * g'⁻¹ * b := by group
      obtain ⟨a, haQ, b, hbK, hab⟩ := hXdec _ hy
      rw [hQQ₀] at haQ
      have hab_comm : a * b = b * a := Subgroup.mem_centralizer_iff.mp (hKX hbK) a haQ
      have hy2 : ((g : G) * x * (g : G)⁻¹) ^ 2 = 1 := by
        rw [← MulAut.conj_apply, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
      have ha2 : a ^ 2 = 1 := by
        rw [hab, (Commute.mul_pow hab_comm 2)] at hy2
        have hmem : a ^ 2 ∈ Q₀ ⊓ K := by
          refine ⟨Q₀.pow_mem haQ 2, ?_⟩
          have : a ^ 2 = (b ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hy2
          rw [this]
          exact K.inv_mem (K.pow_mem hbK 2)
        rw [← hQQ₀, hQK, Subgroup.mem_bot] at hmem
        exact hmem
      have ha1 : a = 1 := by
        obtain ⟨k, hk⟩ := hpelt Q₀ f hQ₀card a haQ
        have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
        rw [hk] at h1
        rcases k with _ | k
        · rw [pow_zero, orderOf_eq_one_iff] at hk
          exact hk
        · exfalso
          have h2 : p ∣ 2 := (dvd_pow_self p (Nat.succ_ne_zero k)).trans h1
          exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      rw [ha1, one_mul] at hab
      have hyx : (g : G) * x * (g : G)⁻¹ = x := by
        have hb1 : b ≠ 1 := by
          intro hb1
          rw [hb1] at hab
          apply hx1
          have : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g := by group
          rw [this, hab]
          group
        have hb2 : b ^ 2 = 1 := by rw [← hab]; exact hy2
        have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
        have := eq_of_sq_eq_one_of_isCyclic (K := K) (a := ⟨b, hbK⟩) (b := ⟨x, hxK⟩)
          (Subtype.ext (by simpa using hb2)) (fun h => hb1 (congrArg Subtype.val h))
          (Subtype.ext (by simpa using hx2)) (fun h => hx1 (congrArg Subtype.val h))
        rw [hab]
        exact congrArg Subtype.val this
      have hgNx : (g : G) ∈ N := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * g := by group
          _ = x * g := by rw [hyx]
      set Y := Q₀ ⊔ Subgroup.zpowers (g : G)
      have hYP : Y ≤ P := sup_le hP ((Subgroup.zpowers_le).mpr g.2)
      have hYN : Y ≤ N := sup_le hQ₀N ((Subgroup.zpowers_le).mpr hgNx)
      have hYeq := eq_of_isPGroup_of_le hp hQ₀card hQ₀N hQ₀syl ((Sylow.isPGroup' P).to_le hYP)
        hYN le_sup_left
      exact hgQ₀' (hYeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (g : G)))
  have he : e = 3 * f := le_antisymm he3 h3f
  let QS : Sylow p G := Sylow.ofCard Q (by rw [hQcard, hfacG, he])
  have hQS : (QS : Subgroup G) = Q := rfl
  have hQScard : Nat.card QS = q ^ 3 := by
    change Nat.card Q = q ^ 3
    rw [hQcard, he, hqdef, ← pow_mul, mul_comm]
  have := Fintype.ofFinite G
  obtain ⟨Q₁, hQ₁⟩ := CFSG.DefectZeroSylow.exists_sylow_inf_eq_bot_of_degree_eq_card QS hχ
    (by rw [hχdeg, hQScard])
  refine ⟨QS, hQScard, hQS ▸ hHQ, ?_, Q₁, hQ₁⟩
  rw [hG, hHcard]
  ring

theorem statedClassicalModel_psu_of_centralizer_data
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (x : G) (hx : orderOf x = 2)
    (K : Subgroup G) (hxK : x ∈ K)
    (hKcent : ∀ r ∈ K, ∀ g ∈ Subgroup.centralizer {x}, g * r = r * g)
    (hKp : ¬ p ∣ Nat.card K)
    (hKconf : ∀ r ∈ K, r ≠ 1 → Subgroup.centralizer {r} ≤ Subgroup.centralizer {x})
    (S : Sylow 2 G) (hSN : (S : Subgroup G) ≤ Subgroup.centralizer {x})
    (hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.centralizer {x})
    (Q₀ : Subgroup G) (hQ₀card : Nat.card Q₀ = p ^ f)
    (hQ₀comm : ∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a)
    (hQ₀N : Q₀ ≤ Subgroup.centralizer {x})
    (hQ₀syl : ¬ p ∣ Q₀.relIndex (Subgroup.centralizer {x}))
    (H : Subgroup G) (hHQ₀ : H ≤ Subgroup.normalizer (Q₀ : Set G)) (hHcyc : IsCyclic H)
    (hKH : K ≤ H) (hHcard : Nat.card H = (p ^ f - 1) * Nat.card K)
    (hcent : ∀ u : G, u ≠ 1 → (∃ k : ℕ, orderOf u = p ^ k) →
      Nat.card (Subgroup.centralizer {u}) ∣ Nat.card K * (p ^ f) ^ 3)
    (hG : Nat.card G = Nat.card K * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1))
    {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G) (hχdeg : χ 1 = (((p ^ f) ^ 3 : ℕ) : ℂ))
    (hd : Nat.card K * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  obtain ⟨Q, hQcard, hHQ, hGH, Q₁, hQ₁⟩ := exists_sylow_of_centralizer_data p f hp hpodd hf x hx
    K hxK hKcent hKp hKconf S hSN hNS Q₀ hQ₀card hQ₀comm hQ₀N hQ₀syl H hHQ₀ hHcyc hKH hHcard
    hcent hG hχ hχdeg
  have hgpos : 0 < Nat.gcd (p ^ f + 1) 3 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  have hHcard' : Nat.card H = ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3 := by
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      zify [h1, Nat.one_le_pow 2 (p ^ f) (by omega)]
      ring
    have h2 : (p ^ f - 1) * (p ^ f + 1) =
        (p ^ f - 1) * Nat.card K * Nat.gcd (p ^ f + 1) 3 := by
      rw [mul_assoc, hd]
    rw [hsq, h2, Nat.mul_div_cancel _ hgpos, hHcard]
  exact CFSG.Permutation.SylowTrivialIntersection.statedClassicalModel_psu_of_sylow_normalizer
    hnonab p f hp hpodd hf Q hQcard H hHQ hHcyc hHcard' hGH hQ₁

end CFSG.Semidihedral.UnitaryBranch
