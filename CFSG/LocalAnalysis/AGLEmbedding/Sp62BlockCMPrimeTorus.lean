module

public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Block

variable {G : Type} [Group G]

theorem conj_mem_blockCentralizer_of_normal {M L : Subgroup G} (hLn : (barM M L).Normal)
    {m b : G} (hm : m ∈ M) (hb : b ∈ blockCentralizer M L) :
    m * b * m⁻¹ ∈ blockCentralizer M L := by
  obtain ⟨b', hb', rfl⟩ := hb
  have : (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).Normal :=
    Subgroup.normal_centralizer
  exact ⟨⟨m, hm⟩ * b' * ⟨m, hm⟩⁻¹, (Subgroup.Normal.comap this _).conj_mem _ hb' _, rfl⟩

theorem mem_blockCentralizer_of_conjNormal {M L : Subgroup G} [(barM M L).Normal] {g : M}
    (hg : MulAut.conjNormal (H := barM M L) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) g) = 1) :
    (g : G) ∈ blockCentralizer M L := by
  refine ⟨g, ?_, rfl⟩
  show g ∈ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro l hl
  have h := congrArg Subtype.val (congrArg (fun φ : MulAut (barM M L) => φ ⟨l, hl⟩) hg)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem false_of_torusPrime {G Q : Type} [Group G] [Finite G] [Group Q] {M L H C : Subgroup G}
    [hLn : (barM M L).Normal] (hCL : blockCentralizer M L ≤ GLBPrimeCore 3 H) {x : G}
    (hC : C ≤ Subgroup.centralizer ({x} : Set G)) (hxM : x ∈ M)
    (hxbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M L)
    (hcard : Nat.card (Subgroup.centralizer
      ({MulAut.conj (⟨_, hxbL⟩ : barM M L)} : Set (MulAut (barM M L)))) ∣ 2 ^ 7 * 3 ^ 7)
    (φ : C →* Q) {U : Subgroup Q} (hU : IsPGroup 3 U)
    (hUX : U ≤ ((C ⊓ M).subgroupOf C).map φ) {c : Q}
    (hcX : c ∈ ((C ⊓ M).subgroupOf C).map φ)
    (hcN : c ∈ Subgroup.normalizer (U : Set Q)) (hc6 : Nat.Coprime (orderOf c) 6)
    (hcu : ∃ u ∈ U, c * u * c⁻¹ ≠ u) : False := by
  obtain ⟨u, huU, hcu⟩ := hcu
  obtain ⟨c₀, hc₀, rfl⟩ := hcX
  have hc₀M : (c₀ : G) ∈ M := (Subgroup.mem_subgroupOf.mp hc₀).2
  set N₀ : ℕ := 2 ^ 7 * 3 ^ 7 with hN₀
  set g : M := ⟨c₀, hc₀M⟩ with hg
  have hgx : QuotientGroup.mk' (CFSG.pCore 2 ↥M) g * QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      ⟨x, hxM⟩ = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) g := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hC c₀.2))
  have hgs : MulAut.conjNormal (H := barM M L) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) g) ∈
      Subgroup.centralizer ({MulAut.conj (⟨_, hxbL⟩ : barM M L)} : Set (MulAut (barM M L))) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← MulAut.conjNormal_val]
    have h2 := congrArg (MulAut.conjNormal (H := barM M L)) hgx
    rw [map_mul, map_mul] at h2
    exact h2
  have hpow : (MulAut.conjNormal (H := barM M L) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) g)) ^ N₀
      = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hgs).trans hcard)
  have hB : (c₀ : G) ^ N₀ ∈ blockCentralizer M L := by
    have h4 : MulAut.conjNormal (H := barM M L) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (g ^ N₀))
        = 1 := by
      rw [map_pow, map_pow]
      exact hpow
    simpa [g] using mem_blockCentralizer_of_conjNormal h4
  have hcomm : ∀ v ∈ U, (φ c₀) ^ N₀ * v = v * (φ c₀) ^ N₀ := by
    intro v hv
    obtain ⟨v₀, hv₀, rfl⟩ := hUX hv
    have hv₀M : (v₀ : G) ∈ M := (Subgroup.mem_subgroupOf.mp hv₀).2
    set w : C := v₀ * c₀ ^ N₀ * v₀⁻¹ * (c₀ ^ N₀)⁻¹ with hw
    have hwB : (w : G) ∈ blockCentralizer M L := by
      simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      exact (blockCentralizer M L).mul_mem (conj_mem_blockCentralizer_of_normal hLn hv₀M hB)
        ((blockCentralizer M L).inv_mem hB)
    have hw3 : Nat.Coprime 3 (orderOf w) := by
      rw [← Subgroup.orderOf_coe]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ (hCL hwB))
        (glbPrimeCore_coprime 3 H)
    have hφw : φ w = φ v₀ * (φ c₀) ^ N₀ * (φ v₀)⁻¹ * ((φ c₀) ^ N₀)⁻¹ := by
      simp [hw]
    have hcNN : (φ c₀) ^ N₀ ∈ Subgroup.normalizer (U : Set Q) := Subgroup.pow_mem _ hcN N₀
    have hwU : φ w ∈ U := by
      have h6 : (φ c₀) ^ N₀ * (φ v₀)⁻¹ * ((φ c₀) ^ N₀)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hcNN _).mp (U.inv_mem hv)
      rw [hφw, mul_assoc (φ v₀ * _), mul_assoc (φ v₀)]
      exact U.mul_mem hv (by rwa [← mul_assoc])
    have h7 : φ w = 1 := eq_one_of_mem_of_coprime hU hwU
      (Nat.Coprime.coprime_dvd_right (orderOf_map_dvd φ w) hw3).symm
    rw [hφw] at h7
    have h8 : (φ c₀) ^ N₀ * φ v₀ * ((φ c₀) ^ N₀)⁻¹ = φ v₀ := by
      calc (φ c₀) ^ N₀ * φ v₀ * ((φ c₀) ^ N₀)⁻¹
          = (φ v₀ * (φ c₀) ^ N₀ * (φ v₀)⁻¹ * ((φ c₀) ^ N₀)⁻¹)⁻¹ * φ v₀ := by group
        _ = φ v₀ := by rw [h7, inv_one, one_mul]
    exact mul_inv_eq_iff_eq_mul.mp h8
  have hcop : Nat.Coprime N₀ (orderOf (φ c₀)) := by
    have h9 : Nat.Coprime (orderOf (φ c₀)) (6 ^ 7) := Nat.Coprime.pow_right 7 hc6
    exact (Nat.Coprime.coprime_dvd_right (by norm_num [hN₀]) h9).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hcu' : (φ c₀) ^ N₀ ∈ Subgroup.centralizer ({u} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm u huU)
  have h10 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.pow_mem _ hcu' m)
  rw [hm] at h10
  exact hcu (mul_inv_eq_of_eq_mul h10)

end Block

section Torus

variable {K : Type} [Group K] [Finite K]

theorem exists_torusPrime {T : Sylow 3 K} {n e : ℕ}
    (hF : @OneLieTorusFacts 3 ⟨Nat.prime_three⟩ K _ _ T n e) :
    (∃ V : Subgroup K, V ≤ T ∧ IsElemAbelian 3 V ∧ Nat.card V = 3 ^ n) ∧
      2 ≤ n ∧ ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
        Nat.Coprime (orderOf c) 6 ∧ ∃ u ∈ (T : Subgroup K), c * u * c⁻¹ ≠ u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ, hψi, hψr, hψt⟩ := hF.torus
  have hn2 := hF.two_le
  have hVT : ψ.range ≤ T := hψr ▸ inf_le_left
  refine ⟨⟨ψ.range, hVT, ⟨?_, ?_⟩, ?_⟩, hn2, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
    obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    simp only [Subgroup.coe_mul, ← ha', ← hb', ← map_mul, mul_comm a' b']
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul,
        show ((3 : ℕ) : GaloisField 3 n) = 0 from CharP.cast_eq_zero _ 3, zero_mul]
    rw [this, map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψi, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, GaloisField.card 3 n (by omega)]
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    ·
      have hn : n = 2 := by omega
      obtain ⟨-, -, -, hpair⟩ := hF.pair hn
      obtain ⟨c, hcN, hc5, hc⟩ := hpair 5 Nat.prime_five (by norm_num)
        (fun k hk0 hk4 => by interval_cases k <;> norm_num)
      obtain ⟨⟨u, huT, hu⟩, -⟩ := hc 1 (by norm_num)
      refine ⟨c, hcN, by rw [hc5]; norm_num, u, huT, fun h => hu ?_⟩
      rw [pow_one, h, mul_inv_cancel]
      exact Subgroup.one_mem _
    ·
      have htorus : ∃ φ : Multiplicative (GaloisField 3 n) ≃* ψ.range,
          ∀ μ : (GaloisField 3 n)ˣ, ∃ t ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
            ∀ a : Multiplicative (GaloisField 3 n), t * (φ a : K) * t⁻¹ =
              φ (Multiplicative.ofAdd ((μ : GaloisField 3 n) ^ 2 * Multiplicative.toAdd a)) := by
        refine ⟨MonoidHom.ofInjective hψi, fun μ => ?_⟩
        rcases hF.e_cases with rfl | ⟨rfl, -⟩
        · obtain ⟨c, hcN, hc⟩ := hψt (μ ^ 2)
          refine ⟨c, hcN, fun a => ?_⟩
          simp only [MonoidHom.ofInjective_apply, hc, pow_one, Units.val_pow_eq_pow_val]
        · obtain ⟨c, hcN, hc⟩ := hψt μ
          exact ⟨c, hcN, fun a => by simp only [MonoidHom.ofInjective_apply, hc]⟩
      obtain ⟨r, t, hr, -, hr2, hr3, -, -, htB, -, htp, -, ⟨x, hxX, hx⟩, -⟩ :=
        exists_ppd_torus_element (by norm_num) hn3 htorus
      have : Fact r.Prime := ⟨hr⟩
      have ht6 : Nat.Coprime (orderOf t) 6 := by
        obtain ⟨k, hk⟩ := htp.exists_card_eq
        rw [Nat.card_zpowers] at hk
        rw [hk, show (6 : ℕ) = 2 * 3 by norm_num]
        exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right
          ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
          ((Nat.coprime_primes hr Nat.prime_three).mpr hr3))
      exact ⟨t, htB, ht6, x, hVT hxX, hx⟩

theorem exists_torusPrime_of_sylow {T₀ : Sylow 3 K} {n e : ℕ}
    (hF : @OneLieTorusFacts 3 ⟨Nat.prime_three⟩ K _ _ T₀ n e) (T : Sylow 3 K) :
    (∃ V : Subgroup K, V ≤ T ∧ IsElemAbelian 3 V ∧ Nat.card V = 3 ^ n) ∧
      2 ≤ n ∧ ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
        Nat.Coprime (orderOf c) 6 ∧ ∃ u ∈ (T : Subgroup K), c * u * c⁻¹ ≠ u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨V, hVT, hVel, hVc⟩, hn2, c, hcN, hc6, u, huT, hcu⟩ := exists_torusPrime hF
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K T₀ T
  have hT : ((g • T₀ : Sylow 3 K) : Subgroup K) =
      (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  rw [hT]
  refine ⟨⟨V.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hVT,
    elementary_abelian_map 3 hVel _, by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hVc]⟩, hn2,
    MulAut.conj g c, ?_, by rwa [MulEquiv.orderOf_eq], MulAut.conj g u,
    Subgroup.mem_map_of_mem _ huT, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hcN
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact fun h => hcu ((MulAut.conj g).injective h)

end Torus

end CFSG.AGLEmbedding
