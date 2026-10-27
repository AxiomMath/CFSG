module

public import CFSG.GH74.GLS.Stage4.T2Frat
public import CFSG.GH74.GLS.Stage4.T2SylSL
public import CFSG.GH74.GLS.IVK.Lifted.CentSylow
public import CFSG.GH74.GLS.Stage4.T2Norm
public import CFSG.GH74.GLS.Stage4.T2Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

structure T2SCtx {G : Type} [Group G] (z : G) (K₁ K₂ S : Subgroup G) : Prop where
  S2 : IsPGroup 2 ↥S
  Sidx : ¬ 2 ∣ S.index
  zS : z ∈ S
  Sz : ∀ s ∈ S, s * z = z * s
  SK : (S ⊓ (K₁ ⊔ K₂)).relIndex S = 2

section R2

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F] [Finite F]

theorem t2C_cent_sylow_K (hodd : Odd (Nat.card F)) (e : ↥K ≃* SL2 F) {P : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hPidx : ¬ 2 ∣ P.relIndex K) {z : G} (hzK : z ∈ K)
    (hze : e ⟨z, hzK⟩ = negOne F) :
    ∀ x ∈ K, (∀ p ∈ P, x * p = p * x) → x ∈ Subgroup.zpowers z := by
  intro x hx hcent
  let P' : Subgroup (SL2 F) := (P.subgroupOf K).map e.toMonoidHom
  have hP' : IsPGroup 2 ↥P' := (hP.comap_subtype).map e.toMonoidHom
  have hidx : ¬ 2 ∣ P'.index := by
    have : P'.index = (P.subgroupOf K).index :=
      Subgroup.index_map_of_bijective e.bijective _
    rw [this]; exact hPidx
  have key := t2C_cent_sylow_sl2 hodd P' hP' hidx (e ⟨x, hx⟩) (by
    rintro _ ⟨p, hp, rfl⟩
    show e ⟨x, hx⟩ * e p = e p * e ⟨x, hx⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcent (p : G) (Subgroup.mem_subgroupOf.1 hp)))
  rcases key with h | h
  · have : (⟨x, hx⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
    have hx1 : x = 1 := by simpa using congrArg Subtype.val this
    rw [hx1]; exact Subgroup.one_mem _
  · have : (⟨x, hx⟩ : ↥K) = ⟨z, hzK⟩ := e.injective (by rw [h, hze])
    have hxz : x = z := by simpa using congrArg Subtype.val this
    rw [hxz]; exact Subgroup.mem_zpowers z

end R2

section ZS

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ S : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2C_sylow_inf_K (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hS : T2SCtx z K₁ K₂ S) : ¬ 2 ∣ (S ⊓ K₁).relIndex K₁ ∧ ¬ 2 ∣ (S ⊓ K₂).relIndex K₂ := by
  have hSA : S ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    le_oPrimeResidualOf_centralizer hS.S2 hS.Sz
  have hSidx : ¬ 2 ∣ S.relIndex (oPrimeResidualOf 2 (centralizer ({z} : Set G))) :=
    fun h => hS.Sidx (h.trans (Subgroup.relIndex_dvd_index_of_le hSA))
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  exact ⟨t2C_sylow_inf_odd (le_sup_left.trans hSet.le_residual) hn₁ hSidx,
    t2C_sylow_inf_odd (le_sup_right.trans hSet.le_residual) hn₂ hSidx⟩

omit [Finite G] in
theorem t2C_coords (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    (∃ e₁ : ↥K₁ ≃* SL2 F₁, e₁ ⟨z, hSet.z_mem₁⟩ = negOne F₁) ∧
    (∃ e₂ : ↥K₂ ≃* SL2 F₂, e₂ ⟨z, hSet.z_mem₂⟩ = negOne F₂) := by
  have hz1 := t2C_z_ne hSet
  have hzc₁ : ∀ k ∈ K₁, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_left hk))
  have hzc₂ : ∀ k ∈ K₂, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer (Subgroup.mem_sup_right hk))
  obtain ⟨e₁⟩ := hSet.iso₁
  obtain ⟨e₂⟩ := hSet.iso₂
  exact ⟨⟨e₁, (t2C_Z_of_sl2 e₁ hz1 hSet.z_mem₁ hzc₁).1⟩, ⟨e₂, (t2C_Z_of_sl2 e₂ hz1 hSet.z_mem₂ hzc₂).1⟩⟩

theorem t2C_cent_K (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hS : T2SCtx z K₁ K₂ S) :
    ∀ x ∈ K₁ ⊔ K₂, (∀ s ∈ S, x * s = s * x) → x ∈ Subgroup.zpowers z := by
  intro x hxK hxc
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem hS
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hxK
  have hP₁ : IsPGroup 2 ↥(S ⊓ K₁) := hS.S2.to_le inf_le_left
  have hP₂ : IsPGroup 2 ↥(S ⊓ K₂) := hS.S2.to_le inf_le_left
  have ha1 : a ∈ Subgroup.zpowers z := by
    refine t2C_cent_sylow_K hodd₁ e₁ hP₁ hs₁ hSet.z_mem₁ hze₁ a ha
      (fun p hp => ?_)
    have h1 := hxc p hp.1
    have h2 : b * p = p * b := (hSet.comm p hp.2 b hb).symm
    have : a * p * b = p * a * b := by
      calc a * p * b = a * (p * b) := by group
        _ = a * (b * p) := by rw [h2]
        _ = a * b * p := by group
        _ = p * (a * b) := h1
        _ = p * a * b := by group
    exact mul_right_cancel this
  have hb1 : b ∈ Subgroup.zpowers z := by
    refine t2C_cent_sylow_K hodd₂ e₂ hP₂ hs₂ hSet.z_mem₂ hze₂ b hb
      (fun p hp => ?_)
    have h1 := hxc p hp.1
    have h2 : a * p = p * a := hSet.comm a ha p hp.2
    have : a * (b * p) = a * (p * b) := by
      calc a * (b * p) = a * b * p := by group
        _ = p * (a * b) := h1
        _ = (p * a) * b := by group
        _ = (a * p) * b := by rw [h2]
        _ = a * (p * b) := by group
    exact mul_left_cancel this
  exact Subgroup.mul_mem _ ha1 hb1

theorem t2C_ZS
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hC : T2Comp z K₁ K₂) (hS : T2SCtx z K₁ K₂ S) :
    ∀ x ∈ S, (∀ s ∈ S, x * s = s * x) → x ∈ Subgroup.zpowers z := by
  intro x hxS hxc
  have := hSet.finite₁
  have := hSet.finite₂
  have hSA : S ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) :=
    le_oPrimeResidualOf_centralizer hS.S2 hS.Sz
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem hS
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  by_cases hxK : x ∈ K₁ ⊔ K₂
  · exact t2C_cent_K hSet hRem hS x hxK hxc
  · exfalso
    have h4 : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
    have h2₁ : (2 : F₁) ≠ 0 := two_ne_zero_of_odd_card hodd₁
    have hq : CFSG.IsQuasisimple ↥K₁ :=
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e₁).2
        (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (by omega))
    have hno : ∀ u v : ↥K₁, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v := by
      intro u v hu hv _
      have hinv : ∀ w : ↥K₁, orderOf w = 2 → e₁ w = negOne F₁ := by
        intro w hw
        have hww : w * w = 1 := by
          have := pow_orderOf_eq_one w
          rwa [hw, pow_two] at this
        have hw1 : w ≠ 1 := by
          intro h1
          rw [h1, orderOf_one] at hw
          omega
        refine eq_negOne_of_involution h2₁ (by rw [← map_mul, hww, map_one]) ?_
        intro h1
        exact hw1 (e₁.injective (by rw [h1, map_one]))
      exact e₁.injective ((hinv u hu).trans (hinv v hv).symm)
    have hP : IsPGroup 2 ↥((S ⊓ K₁).subgroupOf K₁) := (hS.S2.to_le inf_le_left).comap_subtype
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P : Sylow 2 ↥K₁ := hP.toSylow hs₁
    have hPcoe : (P : Subgroup ↥K₁) = (S ⊓ K₁).subgroupOf K₁ := IsPGroup.toSylow_coe hP hs₁
    have hxn : x ∈ normalizer (K₁ : Set G) :=
      Subgroup.mem_normalizer_fintype (fun y hy => (t2C_C₁_normalizes hRem hSet.comm).1 x (hSA hxS) y hy)
    let ρ : MulAut ↥K₁ := Subgroup.normalizerMonoidHom K₁ ⟨x, hxn⟩
    have hρ : ∀ y : ↥K₁, ((ρ y : ↥K₁) : G) = x * y * x⁻¹ := fun y => rfl
    have hxo : ∃ j : ℕ, x ^ (2 ^ j) = 1 := by
      obtain ⟨j, hj⟩ := hS.S2 ⟨x, hxS⟩
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩
    have hk : ∃ k : ℕ, orderOf ρ = 2 ^ k := by
      obtain ⟨j, hj⟩ := hxo
      have hρj : ρ ^ (2 ^ j) = 1 := by
        ext y
        have hpow : ∀ m : ℕ, ((ρ ^ m) y : G) = x ^ m * y * (x ^ m)⁻¹ := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            rw [pow_succ', MulAut.mul_apply, hρ, ih, pow_succ']
            group
        rw [hpow, hj]
        simp
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hρj)
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hk
    have hfix : ∀ p ∈ (P : Subgroup ↥K₁), ρ p = p := by
      intro p hp
      rw [hPcoe] at hp
      apply Subtype.ext
      rw [hρ]
      have := hxc (p : G) (Subgroup.mem_subgroupOf.1 hp).1
      calc x * (p : G) * x⁻¹ = (p : G) * x * x⁻¹ := by rw [this]
        _ = p := by group
    have h1 : ρ = 1 :=
      CFSG.GH74.GLS.IVK.Lifted.sl2_no_central_sylow hodd₁ h4 e₁ hq hno ρ hk P hfix
    refine t2C_not_cent_K₁ hSet hRem hC (hSA hxS) hxK (fun y hy => ?_)
    have h2 := congrArg (fun r : MulAut ↥K₁ => ((r ⟨y, hy⟩ : ↥K₁) : G)) h1
    simp only [hρ] at h2
    have h3 : x * y * x⁻¹ = y := by simpa using h2
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h3]

end ZS

section CentStr

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem t2C_cent_structure (hS2 : IsPGroup 2 ↥S) (hSidx : ¬ 2 ∣ S.index) (hSz : ∀ s ∈ S, s * z = z * s)
    (hzS : z ∈ S) (hzz : z * z = 1)
    (hZS : ∀ x ∈ S, (∀ s ∈ S, x * s = s * x) → x ∈ Subgroup.zpowers z)
    {F : Subgroup G}
    (hF : F = (pPrimeCore 2 ↥(centralizer (S : Set G))).map (centralizer (S : Set G)).subtype) :
    (∀ f ∈ F, Odd (orderOf f) ∧ ∀ s ∈ S, f * s = s * f) ∧
      (∀ x ∈ centralizer (S : Set G), Odd (orderOf x) → x ∈ F) ∧
      centralizer (S : Set G) = Subgroup.zpowers z ⊔ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CS : Subgroup G := centralizer (S : Set G) with hCS
  have hmemCS : ∀ x, x ∈ CS ↔ ∀ s ∈ S, s * x = x * s := fun x => Subgroup.mem_centralizer_iff
  have hzCS : z ∈ CS := (hmemCS z).2 hSz
  let Q : Sylow 2 G := hS2.toSylow hSidx
  have hQS : (Q : Subgroup G) = S := IsPGroup.toSylow_coe hS2 hSidx
  have h2el : ∀ x ∈ CS, (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ Subgroup.zpowers z := by
    rintro x hx ⟨k, hk⟩
    have hxp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
      intro g
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
      refine ⟨k, ?_⟩
      apply Subtype.ext
      show (g : G) ^ (2 ^ k) = 1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hxn : x ∈ Subgroup.normalizer (Q : Set G) := by
      refine Subgroup.mem_normalizer_fintype (fun y hy => ?_)
      have hy' : y ∈ S := by rw [← hQS]; exact hy
      have h1 := (hmemCS x).1 hx y hy'
      have e : x * y * x⁻¹ = y := by rw [← h1]; group
      rw [e]; exact hy
    have hxmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (Q : Set G) :=
      ⟨Subgroup.mem_zpowers x, hxn⟩
    rw [hxp.inf_normalizer_sylow Q] at hxmem
    have hxS : x ∈ S := by rw [← hQS]; exact hxmem.2
    exact hZS x hxS (fun s hs => ((hmemCS x).1 hx s hs).symm)
  let Z : Subgroup ↥CS := (Subgroup.zpowers z).subgroupOf CS
  have hZp0 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rcases t2C_zpowers_cases hzz g.2 with h | h
    · simp [h]
    · simp [h, pow_two, hzz]
  have hZp : IsPGroup 2 ↥Z := hZp0.comap_subtype
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hPZ : (P : Subgroup ↥CS) = Z := by
    refine le_antisymm ?_ hZP
    intro p hp
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hp⟩
    have hk' : ((p : G)) ^ (2 ^ k) = 1 := by
      have := congrArg (fun w : ↥P => ((w : ↥CS) : G)) hk
      simpa using this
    exact Subgroup.mem_subgroupOf.2 (h2el _ p.2 ⟨k, hk'⟩)
  have hZidx : ¬ 2 ∣ Z.index := by
    rw [← hPZ]; exact P.not_dvd_index
  have hZc : ∀ a ∈ Z, ∀ x : ↥CS, a * x = x * a := by
    intro a ha x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 ha)
    apply Subtype.ext
    have hc : Commute (z : G) (x : G) := (hmemCS x).1 x.2 z hzS
    show ((a : ↥CS) : G) * (x : G) = (x : G) * ((a : ↥CS) : G)
    rw [← hn]
    exact (hc.zpow_left n).eq
  obtain ⟨M, hMn, hModd, hMall, -, hMsup⟩ := t2C_exists_odd_normal Z hZp hZidx hZc
  have hodd_of : ∀ (m : ↥CS) (hm : m ∈ M), Odd (orderOf (m : G)) := by
    intro m hm
    have h1 : orderOf (⟨m, hm⟩ : ↥M) ∣ Nat.card ↥M := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hModd h1
  have hTM : pPrimeCore 2 ↥CS = M := by
    apply le_antisymm
    · unfold pPrimeCore
      refine sSup_le ?_
      rintro K ⟨hKn, hKc⟩ x hx
      apply hMall
      have h1 : orderOf (⟨x, hx⟩ : ↥K) ∣ Nat.card ↥K := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right h1 hKc)
    · unfold pPrimeCore
      exact le_sSup ⟨hMn, Nat.coprime_two_left.2 hModd⟩
  have hFM : F = M.map CS.subtype := by rw [hF, hTM]
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    rw [hFM] at hf
    obtain ⟨m, hm, rfl⟩ := hf
    exact ⟨hodd_of m hm, fun s hs => ((hmemCS (m : G)).1 m.2 s hs).symm⟩
  · intro x hx hxodd
    rw [hFM]
    refine ⟨⟨x, hx⟩, hMall _ ?_, rfl⟩
    rw [Subgroup.orderOf_mk]; exact hxodd
  · apply le_antisymm
    · intro x hx
      have hxM : (⟨x, hx⟩ : ↥CS) ∈ M ⊔ Z := by rw [hMsup]; trivial
      obtain ⟨m, hm, ζ, hζ, hmζ⟩ := Subgroup.mem_sup_of_normal_left.1 hxM
      have hx' : x = (m : G) * (ζ : G) := by
        have := congrArg (fun w : ↥CS => (w : G)) hmζ
        simpa using this.symm
      rw [hx']
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
      · rw [hFM]; exact ⟨m, hm, rfl⟩
      · exact Subgroup.mem_subgroupOf.1 hζ
    · refine sup_le (Subgroup.zpowers_le.2 hzCS) ?_
      rw [hFM]; exact Subgroup.map_subtype_le _

end CentStr

end CFSG.GH74.GLS.Stage4.Rest
