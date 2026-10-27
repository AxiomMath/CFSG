module

public import CFSG.GH74.GLS.Balance.Bender.Ambient
public import CFSG.GH74.GLS.Balance.Bender.Sum
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
theorem map_conj_le {X Y : Subgroup G} (hYX : Y ≤ X) {g : G} (hg : g ∈ normalizer (X : Set G)) :
    Y.map (MulAut.conj g).toMonoidHom ≤ X := by
  rintro _ ⟨n, hn, rfl⟩
  have h1 := (mem_normalizer_iff.mp hg n).mp (hYX hn)
  simpa using h1

omit [Finite G] in
theorem normal_map_conj {X Y : Subgroup G} (hYX : Y ≤ X) (hYn : (Y.subgroupOf X).Normal) {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    ((Y.map (MulAut.conj g).toMonoidHom).subgroupOf X).Normal := by
  refine ⟨fun m hm y => ?_⟩
  obtain ⟨n, hn, hnm⟩ := hm
  have hg' : g⁻¹ ∈ normalizer (X : Set G) := (normalizer (X : Set G)).inv_mem hg
  have hyX : g⁻¹ * (y : G) * g ∈ X := by
    have := (mem_normalizer_iff.mp hg' (y : G)).mp y.2
    simpa using this
  have hn' := hYn.conj_mem ⟨n, hYX hn⟩ hn ⟨g⁻¹ * y * g, hyX⟩
  have hn'' : (g⁻¹ * (y : G) * g) * n * (g⁻¹ * (y : G) * g)⁻¹ ∈ Y := hn'
  refine ⟨_, hn'', ?_⟩
  have hnm' : g * n * g⁻¹ = (m : G) := hnm
  show g * ((g⁻¹ * (y : G) * g) * n * (g⁻¹ * (y : G) * g)⁻¹) * g⁻¹ = (y : G) * (m : G) * (y : G)⁻¹
  rw [← hnm']
  group

omit [Finite G] in
theorem opStar_conj_mem {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) {x : G}
    (hx : x ∈ OpStar p Y) : g * x * g⁻¹ ∈ OpStar p Y := by
  have key : OpStar p Y ≤ (OpStar p Y).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun N hN => ?_
    obtain ⟨hNY, hNn, hNp⟩ := hN
    have hmem : N.map (MulAut.conj g).toMonoidHom ∈
        {N : Subgroup G | N ≤ Y ∧ (N.subgroupOf Y).Normal ∧ IsPStar p ↥N} :=
      ⟨map_conj_le hNY hg, normal_map_conj hNY hNn hg,
        IsPStar.of_mulEquiv (Subgroup.equivMapOfInjective N (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective) hNp⟩
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup hmem
  exact key hx

omit [Finite G] in
theorem opStar_le_opStarP (p : ℕ) (X : Subgroup G) : OpStar p X ≤ OpStarP p X := by
  intro o ho
  refine ⟨⟨o, opStar_le p X ho⟩, ?_, rfl⟩
  have h1 : (⟨o, opStar_le p X ho⟩ : ↥X) ∈ (OpStar p X).subgroupOf X := ho
  have : (QuotientGroup.mk' ((OpStar p X).subgroupOf X)) ⟨o, opStar_le p X ho⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 h1
  rw [SetLike.mem_coe, Subgroup.mem_comap, this]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem opStarP_le (p : ℕ) (X : Subgroup G) : OpStarP p X ≤ X := Subgroup.map_subtype_le _

instance opStarP_normal (p : ℕ) (X : Subgroup G) : ((OpStarP p X).subgroupOf X).Normal := by
  have e : (OpStarP p X).subgroupOf X =
      (pCore p (↥X ⧸ (OpStar p X).subgroupOf X)).comap
        (QuotientGroup.mk' ((OpStar p X).subgroupOf X)) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [e]
  exact Subgroup.Normal.comap inferInstance _

omit [Finite G] in
theorem opStarP_pow_mem (p : ℕ) (X : Subgroup G) {x : G} (hx : x ∈ OpStarP p X) :
    ∃ k : ℕ, x ^ p ^ k ∈ OpStar p X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hp : IsPGroup p (pCore p (↥X ⧸ (OpStar p X).subgroupOf X)) := pCore_isPGroup
  obtain ⟨k, hk⟩ := hp ⟨_, hy⟩
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk' ((OpStar p X).subgroupOf X)) (y ^ p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  have h2 : y ^ p ^ k ∈ (OpStar p X).subgroupOf X := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

omit [Finite G] [Fact p.Prime] in
theorem le_opStarP {X Y : Subgroup G} (hYX : Y ≤ X) (hYn : (Y.subgroupOf X).Normal)
    (hpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ OpStar p X) : Y ≤ OpStarP p X := by
  set O' : Subgroup ↥X := (OpStar p X).subgroupOf X with hO'
  set π : ↥X →* ↥X ⧸ O' := QuotientGroup.mk' O' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O'
  have hDn : (Y.subgroupOf X |>.map π).Normal := hYn.map π hπs
  have hDp : IsPGroup p ↥((Y.subgroupOf X).map π) := by
    rintro ⟨_, ⟨z, hz, rfl⟩⟩
    obtain ⟨k, hk⟩ := hpow (z : G) hz
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (π z) ^ p ^ k = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hk
  have hDle : (Y.subgroupOf X).map π ≤ pCore p (↥X ⧸ O') := le_sSup ⟨hDn, hDp⟩
  intro y hy
  refine ⟨⟨y, hYX hy⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  exact hDle ⟨⟨y, hYX hy⟩, hy, rfl⟩

omit [Finite G] in
theorem opStarP_conj_mem {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) {x : G}
    (hx : x ∈ OpStarP p X) : g * x * g⁻¹ ∈ OpStarP p X := by
  have hg' : g⁻¹ ∈ normalizer (X : Set G) := (normalizer (X : Set G)).inv_mem hg
  have hle : (OpStarP p X).map (MulAut.conj g).toMonoidHom ≤ OpStarP p X := by
    refine le_opStarP (map_conj_le (opStarP_le p X) hg) (normal_map_conj (opStarP_le p X)
      (opStarP_normal p X) hg) ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨j, hj⟩ := opStarP_pow_mem p X hk
    refine ⟨j, ?_⟩
    have h1 := opStar_conj_mem (p := p) (Y := X) hg hj
    simpa [MulAut.conj_apply, mul_pow, ← mul_assoc, conj_pow] using h1
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem pCore_quotient_opStarP (p : ℕ) [Fact p.Prime] (X : Subgroup G) :
    pCore p (↥X ⧸ (OpStarP p X).subgroupOf X) = ⊥ := by
  set N' : Subgroup ↥X := (OpStarP p X).subgroupOf X with hN'
  set π : ↥X →* ↥X ⧸ N' := QuotientGroup.mk' N' with hπ
  set D : Subgroup (↥X ⧸ N') := pCore p (↥X ⧸ N') with hD
  have hDn : D.Normal := pCore_normal
  have hDp : IsPGroup p ↥D := pCore_isPGroup
  set D' : Subgroup ↥X := D.comap π with hD'
  have hD'n : D'.Normal := hDn.comap π
  set Y : Subgroup G := D'.map X.subtype with hY
  have hYX : Y ≤ X := Subgroup.map_subtype_le _
  have hYsub : Y.subgroupOf X = D' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hYn : (Y.subgroupOf X).Normal := by rw [hYsub]; exact hD'n
  have hYle : Y ≤ OpStarP p X := by
    refine le_opStarP hYX hYn ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzD : π z ∈ D := hz
    obtain ⟨k, hk⟩ := hDp ⟨_, hzD⟩
    have hk' : (π z) ^ p ^ k = 1 := congrArg Subtype.val hk
    have h1 : z ^ p ^ k ∈ N' := by
      rw [← map_pow] at hk'
      exact (QuotientGroup.eq_one_iff _).1 hk'
    have h2 : ((z ^ p ^ k : ↥X) : G) ∈ OpStarP p X := h1
    obtain ⟨j, hj⟩ := opStarP_pow_mem p X h2
    refine ⟨k + j, ?_⟩
    have : ((z : G) ^ p ^ k) ^ p ^ j = (z : G) ^ p ^ (k + j) := by
      rw [← pow_mul, ← pow_add]
    show (z : G) ^ p ^ (k + j) ∈ OpStar p X
    rw [← this]
    simpa using hj
  rw [eq_bot_iff]
  intro d hd
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective d
  have hzD' : z ∈ D' := hd
  have : ((z : ↥X) : G) ∈ OpStarP p X := hYle ⟨z, hzD', rfl⟩
  have hzN' : z ∈ N' := this
  exact (Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff _).2 hzN'))

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {O : Subgroup G} {x : G} {n : ℕ}
    (hcop : Nat.Coprime n (orderOf x)) (h : x ^ n ∈ O) : x ∈ O := by
  have hbez := Nat.gcd_eq_gcd_ab n (orderOf x)
  rw [hcop.gcd_eq_one] at hbez
  have hx : x = (x ^ n) ^ (Nat.gcdA n (orderOf x)) := by
    have h1 : x ^ (1 : ℤ) = x ^ ((n : ℤ) * Nat.gcdA n (orderOf x) + (orderOf x : ℤ) * Nat.gcdB n (orderOf x)) := by
      rw [← hbez]; rfl
    rw [zpow_one, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one, one_zpow,
      mul_one] at h1
    exact h1
  rw [hx]
  exact O.zpow_mem h _

omit [Finite G] in
theorem oResOf_opStarP_le (p : ℕ) [Fact p.Prime] (X : Subgroup G) :
    oResOf p (OpStarP p X) ≤ OpStar p X := by
  refine oResOf_le_of fun x hx hxo => ?_
  obtain ⟨k, hk⟩ := opStarP_pow_mem p X hx
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left k hxo.symm) hk

theorem oResOf_opStarP (h56 : BenderL56 p) (X : Subgroup G) :
    oResOf p (OpStarP p X) = OpStar p X :=
  le_antisymm (oResOf_opStarP_le p X) <| by
    have h := (isPStar_opStar h56 X).oResOf_eq
    calc OpStar p X = oResOf p (OpStar p X) := h.symm
      _ ≤ oResOf p (OpStarP p X) := oResOf_mono (opStar_le_opStarP p X)

end CFSG.GH74.GLS.Balance
