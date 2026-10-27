module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Pow

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime {N : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ N) (hb : x ^ b ∈ N) : x ∈ N := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (u * (a : ℤ) + v * (b : ℤ)) = 1 := by exact_mod_cast huv
    rw [mul_comm (a : ℤ) u, mul_comm (b : ℤ) v, this, zpow_one]
  rw [h]
  exact N.mul_mem (N.zpow_mem ha u) (N.zpow_mem hb v)

theorem mem_of_pow_odd_mem {N : Subgroup G} {x : G} {m : ℕ} (hm : Odd m) {k : ℕ}
    (hk : x ^ (2 ^ k) ∈ N) (hxm : x ^ m ∈ N) : x ∈ N :=
  mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)) hk hxm

end Pow

section Core

variable {G : Type*} [Group G] [Finite G]

theorem inf_eq_bot_of_pGroup {M P : Subgroup G} [hPn : P.Normal] (hP2 : IsPGroup 2 P)
    (hMs : IsSimpleGroup ↥M) (hM2 : ¬ IsPGroup 2 ↥M) : P ⊓ M = ⊥ := by
  haveI hnorm : (P.subgroupOf M).Normal := Subgroup.Normal.subgroupOf hPn M
  rcases hMs.eq_bot_or_eq_top_of_normal (P.subgroupOf M) with h | h
  · rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hy.2⟩ : ↥M) ∈ P.subgroupOf M := hy.1
    rw [h] at this
    simpa using this
  · exfalso
    apply hM2
    have hle : M ≤ P := by
      intro y hy
      have : (⟨y, hy⟩ : ↥M) ∈ P.subgroupOf M := by rw [h]; exact Subgroup.mem_top _
      exact this
    exact hP2.to_le hle

theorem pCore_eq_of_levi {U N M : Subgroup G} {m : ℕ} (hm : Odd m) (hU : IsPGroup 2 U)
    (hUN : U ≤ N) (hMN : M ≤ N) (hUn : U.Normal) (hNn : N.Normal)
    (hN : ∀ x ∈ N, ∃ u ∈ U, ∃ y ∈ M, x = u * y) (hq : ∀ g : G, g ^ m ∈ N)
    (hMs : IsSimpleGroup ↥M) (hM2 : ¬ IsPGroup 2 ↥M) :
    CFSG.pCore 2 G = U := by
  have hOn : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal (p := 2) (G := G)
  have hO2 : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup (p := 2) (G := G)
  have hUO : U ≤ CFSG.pCore 2 G := le_sSup ⟨hUn, hU⟩
  have hON : CFSG.pCore 2 G ≤ N := by
    intro x hx
    obtain ⟨k, hk⟩ := hO2 ⟨x, hx⟩
    exact mem_of_pow_odd_mem hm (k := k)
      (by rw [show x ^ 2 ^ k = 1 from congrArg Subtype.val hk]; exact N.one_mem) (hq x)
  set P : Subgroup G := CFSG.pCore 2 G ⊓ N with hP
  have hPn : P.Normal := inferInstance
  have hP2 : IsPGroup 2 P := hO2.to_le inf_le_left
  have hPM : P ⊓ M = ⊥ := inf_eq_bot_of_pGroup hP2 hMs hM2
  have hPU : P ≤ U := by
    intro x hx
    obtain ⟨u, hu, y, hy, rfl⟩ := hN x hx.2
    have hyP : y ∈ P := by
      have h1 : u⁻¹ * (u * y) ∈ P := P.mul_mem (P.inv_mem ⟨hUO hu, hUN hu⟩) hx
      rwa [inv_mul_cancel_left] at h1
    have : y ∈ P ⊓ M := ⟨hyP, hy⟩
    rw [hPM, Subgroup.mem_bot] at this
    rw [this, mul_one]
    exact hu
  refine le_antisymm (fun x hx => hPU ⟨hx, hON hx⟩) hUO

theorem map_pElementSubgroup_le {H : Type*} [Group H] (f : G →* H) (A : Subgroup G) :
    (pElementSubgroup 2 A).map f ≤ pElementSubgroup 2 (A.map f) := by
  rw [pElementSubgroup, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxA, k, hk⟩, rfl⟩
  refine ⟨⟨x, hxA, rfl⟩, ?_⟩
  have hd : orderOf (f x) ∣ 2 ^ k := hk ▸ orderOf_map_dvd f x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨j, hj⟩

theorem le_pElementSubgroup_of_gen {M : Subgroup G}
    (hMgen : ∀ P : Subgroup G, (∀ x ∈ M, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) → M ≤ P) :
    M ≤ pElementSubgroup 2 M := by
  refine hMgen _ fun x hx hk => ?_
  obtain ⟨k, hk⟩ := hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  exact Subgroup.subset_closure ⟨hx, j, hj⟩

theorem exists_mulEquiv_of_levi {U N M : Subgroup G} {m : ℕ} (hm : Odd m) (hU : IsPGroup 2 U)
    (hUN : U ≤ N) (hMN : M ≤ N) (hUn : U.Normal) (hNn : N.Normal)
    (hN : ∀ x ∈ N, ∃ u ∈ U, ∃ y ∈ M, x = u * y) (hq : ∀ g : G, g ^ m ∈ N)
    (hMs : IsSimpleGroup ↥M) (hM2 : ¬ IsPGroup 2 ↥M)
    (hMgen : ∀ P : Subgroup G, (∀ x ∈ M, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) → M ≤ P) :
    Nonempty (↥(pElementSubgroup 2 (⊤ : Subgroup (G ⧸ CFSG.pCore 2 G))) ≃* ↥M) := by
  have hMgen' := le_pElementSubgroup_of_gen hMgen
  have hcore := pCore_eq_of_levi hm hU hUN hMN hUn hNn hN hq hMs hM2
  set q : G →* G ⧸ CFSG.pCore 2 G := QuotientGroup.mk' (CFSG.pCore 2 G) with hqdef
  have hUM : U ⊓ M = ⊥ := inf_eq_bot_of_pGroup hU hMs hM2
  have hinj : Function.Injective (q.comp M.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : G) ∈ CFSG.pCore 2 G := by
      have := MonoidHom.mem_ker.1 hy
      simpa [hqdef, QuotientGroup.eq_one_iff] using this
    rw [hcore] at h1
    have : (y : G) ∈ U ⊓ M := ⟨h1, y.2⟩
    rw [hUM, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hrange : M.map q = pElementSubgroup 2 (⊤ : Subgroup (G ⧸ CFSG.pCore 2 G)) := by
    apply le_antisymm
    · refine (Subgroup.map_mono hMgen').trans ?_
      refine (map_pElementSubgroup_le q M).trans ?_
      unfold pElementSubgroup
      exact Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_top _, hx.2⟩
    · unfold pElementSubgroup
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨-, k, hk⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      have hx2 : x ^ 2 ^ k ∈ N := by
        have h1 : (QuotientGroup.mk x : G ⧸ CFSG.pCore 2 G) ^ 2 ^ k = 1 := by
          rw [← hk]; exact pow_orderOf_eq_one _
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hcore] at h1
        exact hUN h1
      have hxN : x ∈ N := mem_of_pow_odd_mem hm hx2 (hq x)
      obtain ⟨u, hu, y, hy, rfl⟩ := hN x hxN
      have hq1 : q u = 1 := by
        rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcore]
        exact hu
      exact ⟨y, hy, by show q y = q (u * y); rw [map_mul, hq1, one_mul]⟩
  have hrange' : (q.comp M.subtype).range =
      pElementSubgroup 2 (⊤ : Subgroup (G ⧸ CFSG.pCore 2 G)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hrange
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange')).symm⟩

end Core

section Surj

variable {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]

theorem exists_mulEquiv_of_levi_surj (ψ : H →* G) (hψ : Function.Surjective ψ)
    (hker : ∀ x, ψ x = 1 → x ∈ Subgroup.center H) {U N M : Subgroup H} {m : ℕ} (hm : Odd m)
    (hU : IsPGroup 2 U) (hUN : U ≤ N) (hMN : M ≤ N) (hUn : U.Normal) (hNn : N.Normal)
    (hN : ∀ x ∈ N, ∃ u ∈ U, ∃ y ∈ M, x = u * y) (hq : ∀ h : H, h ^ m ∈ N)
    (hMs : IsSimpleGroup ↥M) (hMnc : ¬ IsMulCommutative ↥M) (hM2 : ¬ IsPGroup 2 ↥M)
    (hMgen : ∀ P : Subgroup H, (∀ x ∈ M, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) → M ≤ P) :
    Nonempty (↥(pElementSubgroup 2 (⊤ : Subgroup (G ⧸ CFSG.pCore 2 G))) ≃* ↥M) := by
  have hcen : Subgroup.center ↥M = ⊥ := by
    haveI : (Subgroup.center ↥M).Normal := inferInstance
    rcases hMs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M) with h | h
    · exact h
    · exfalso
      apply hMnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have : a ∈ Subgroup.center ↥M := by rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_center_iff.1 this b).symm
  have hinj : Function.Injective (ψ.comp M.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have h1 : (y : H) ∈ Subgroup.center H := hker _ (MonoidHom.mem_ker.1 hy)
    have h2 : y ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (Subgroup.mem_center_iff.1 h1 (z : H))
    rw [hcen, Subgroup.mem_bot] at h2
    exact h2
  have hrM : (ψ.comp M.subtype).range = M.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  set eM : ↥M ≃* ↥(M.map ψ) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrM) with heM
  haveI : IsSimpleGroup ↥(M.map ψ) := eM.symm.isSimpleGroup
  have hM2' : ¬ IsPGroup 2 ↥(M.map ψ) := fun h => hM2 (h.of_equiv eM.symm)
  have hMgen' : ∀ P : Subgroup G, (∀ x ∈ M.map ψ, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) →
      M.map ψ ≤ P := by
    intro P hP
    rw [Subgroup.map_le_iff_le_comap]
    refine hMgen (P.comap ψ) fun x hx hk => ?_
    obtain ⟨k, hk⟩ := hk
    exact hP (ψ x) ⟨x, hx, rfl⟩ ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hN' : ∀ x ∈ N.map ψ, ∃ u ∈ U.map ψ, ∃ y ∈ M.map ψ, x = u * y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, y, hy, rfl⟩ := hN x hx
    exact ⟨ψ u, ⟨u, hu, rfl⟩, ψ y, ⟨y, hy, rfl⟩, map_mul ψ u y⟩
  have hq' : ∀ g : G, g ^ m ∈ N.map ψ := by
    intro g
    obtain ⟨h, rfl⟩ := hψ g
    exact ⟨h ^ m, hq h, map_pow ψ h m⟩
  obtain ⟨e⟩ := exists_mulEquiv_of_levi hm (hU.map ψ) (Subgroup.map_mono hUN)
    (Subgroup.map_mono hMN) (hUn.map ψ hψ) (hNn.map ψ hψ) hN' hq' inferInstance hM2' hMgen'
  exact ⟨e.trans eM.symm⟩

end Surj

section Map

variable {K Y : Type*} [Group K] [Finite K] [Group Y]

theorem exists_mulEquiv_of_levi_map (ψ : K →* Y) (hker : ∀ x, ψ x = 1 → x ∈ Subgroup.center K)
    {Xt U N M : Subgroup K} {m : ℕ} (hm : Odd m) (hUN : U ≤ N) (hNX : N ≤ Xt) (hMN : M ≤ N)
    (hU : IsPGroup 2 U) (hUn : Xt ≤ Subgroup.normalizer (U : Set K))
    (hNn : Xt ≤ Subgroup.normalizer (N : Set K))
    (hN : ∀ x ∈ N, ∃ u ∈ U, ∃ y ∈ M, x = u * y) (hq : ∀ x ∈ Xt, x ^ m ∈ N)
    (hMs : IsSimpleGroup ↥M) (hMnc : ¬ IsMulCommutative ↥M) (hM2 : ¬ IsPGroup 2 ↥M)
    (hMgen : ∀ P : Subgroup K, (∀ x ∈ M, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) → M ≤ P) :
    Nonempty (↥(pElementSubgroup 2 (⊤ : Subgroup (↥(Xt.map ψ) ⧸ CFSG.pCore 2 ↥(Xt.map ψ)))) ≃*
      ↥M) := by
  have hUX : U ≤ Xt := hUN.trans hNX
  have hMX : M ≤ Xt := hMN.trans hNX
  let ψ' : ↥Xt →* ↥(Xt.map ψ) :=
    (ψ.comp Xt.subtype).codRestrict (Xt.map ψ) fun x => ⟨x, x.2, rfl⟩
  have hψ' : Function.Surjective ψ' := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  haveI : Finite ↥(Xt.map ψ) := Finite.of_surjective ψ' hψ'
  have hker' : ∀ x, ψ' x = 1 → x ∈ Subgroup.center ↥Xt := by
    intro x hx
    have h1 : ψ (x : K) = 1 := congrArg Subtype.val hx
    have h2 := Subgroup.mem_center_iff.1 (hker _ h1)
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (h2 (z : K))
  have eU : ↥(U.subgroupOf Xt) ≃* ↥U := Subgroup.subgroupOfEquivOfLe hUX
  have eN : ↥(N.subgroupOf Xt) ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNX
  have eM : ↥(M.subgroupOf Xt) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMX
  haveI : (U.subgroupOf Xt).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).2 hUn
  haveI : (N.subgroupOf Xt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hNn
  haveI : IsSimpleGroup ↥(M.subgroupOf Xt) := eM.isSimpleGroup
  have hMgen' : ∀ P : Subgroup ↥Xt, (∀ x ∈ M.subgroupOf Xt, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) →
      M.subgroupOf Xt ≤ P := by
    intro P hP y hy
    have hy' : (y : K) ∈ P.map Xt.subtype := by
      refine hMgen (P.map Xt.subtype) (fun x hx hk => ?_) hy
      obtain ⟨k, hk⟩ := hk
      exact ⟨⟨x, hMX hx⟩, hP ⟨x, hMX hx⟩ hx ⟨k, Subtype.ext hk⟩, rfl⟩
    obtain ⟨p, hp, hpy⟩ := hy'
    have : p = y := Subtype.ext hpy
    rwa [← this]
  obtain ⟨e⟩ := exists_mulEquiv_of_levi_surj ψ' hψ' hker' (U := U.subgroupOf Xt)
    (N := N.subgroupOf Xt) (M := M.subgroupOf Xt) hm (hU.of_equiv eU.symm)
    (fun x hx => hUN hx) (fun x hx => hMN hx) inferInstance inferInstance
    (by
      intro x hx
      obtain ⟨u, hu, y, hy, hxy⟩ := hN (x : K) hx
      exact ⟨⟨u, hUX hu⟩, hu, ⟨y, hMX hy⟩, hy, Subtype.ext hxy⟩)
    (fun x => hq x x.2) inferInstance
    (by
      intro hc
      refine hMnc ⟨⟨fun a b => ?_⟩⟩
      have h2 := congrArg eM (hc.is_comm.comm (eM.symm a) (eM.symm b))
      simpa using h2)
    (fun h => hM2 (h.of_equiv eM)) hMgen'
  exact ⟨e.trans eM⟩

end Map

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
