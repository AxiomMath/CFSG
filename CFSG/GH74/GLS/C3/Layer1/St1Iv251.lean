module

public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag3

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv251

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem exists_mul_mem_centralizer_of_odd {P N₀ : Subgroup G} (hP : IsPGroup 2 P)
    (hN₀ : Odd (Nat.card N₀)) (hPN : ∀ p ∈ P, ∀ n ∈ N₀, p * n * p⁻¹ ∈ N₀)
    {l : G} (hcomm : ∀ p ∈ P, l⁻¹ * (p * l * p⁻¹) ∈ N₀) :
    ∃ n ∈ N₀, ∀ p ∈ P, p * (l * n) = (l * n) * p := by
  classical
  have hclosed : ∀ p ∈ P, ∀ g : G, l⁻¹ * g ∈ N₀ → l⁻¹ * (p * g * p⁻¹) ∈ N₀ := by
    intro p hp g hg
    have e : l⁻¹ * (p * g * p⁻¹) = (l⁻¹ * (p * l * p⁻¹)) * (p * (l⁻¹ * g) * p⁻¹) := by group
    rw [e]
    exact N₀.mul_mem (hcomm p hp) (hPN p hp _ hg)
  let α : Type := {g : G // l⁻¹ * g ∈ N₀}
  let _ : MulAction P α :=
    { smul := fun p g => ⟨p * g.1 * (p : G)⁻¹, hclosed p p.2 g.1 g.2⟩
      one_smul := fun g => Subtype.ext (by
        change ((1 : P) : G) * g.1 * ((1 : P) : G)⁻¹ = g.1
        simp)
      mul_smul := fun p q g => Subtype.ext (by
        change ((p * q : P) : G) * g.1 * ((p * q : P) : G)⁻¹ =
          (p : G) * ((q : G) * g.1 * (q : G)⁻¹) * (p : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hcard : Nat.card α = Nat.card N₀ := by
    refine Nat.card_congr
      { toFun := fun g => ⟨l⁻¹ * g.1, g.2⟩
        invFun := fun n => ⟨l * n.1, by simp⟩
        left_inv := fun g => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hnd : ¬ 2 ∣ Nat.card α := by
    rw [hcard]
    have := Nat.odd_iff.mp hN₀
    omega
  obtain ⟨⟨g, hg⟩, hfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α hnd
  refine ⟨l⁻¹ * g, hg, fun p hp => ?_⟩
  have h1 := hfix ⟨p, hp⟩
  have h2 : p * g * (p : G)⁻¹ = g := congrArg Subtype.val h1
  have h3 : p * g = g * p := by
    calc p * g = (p * g * p⁻¹) * p := by group
      _ = g * p := by rw [h2]
  simpa using h3

theorem exists_isSylowOf_ge {C Q : Subgroup G} (hQC : Q ≤ C) (hQ : IsPGroup 2 Q) :
    ∃ R : Subgroup G, IsSylowOf 2 R C ∧ Q ≤ R := by
  have hQ' : IsPGroup 2 (Q.subgroupOf C) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup C).map C.subtype, ⟨S, rfl⟩, fun q hq => ?_⟩
  have : (⟨q, hQC hq⟩ : C) ∈ Q.subgroupOf C := hq
  exact ⟨⟨q, hQC hq⟩, hS this, rfl⟩

variable [Finite G]

theorem exists_invariant_sylow {C Q V : Subgroup G} (hQC : Q ≤ C) (hQ : IsPGroup 2 Q)
    (hV : IsPGroup 2 V) (hVC : V ≤ normalizer (C : Set G)) (hVQ : V ≤ normalizer (Q : Set G)) :
    ∃ Q' : Subgroup G, IsSylowOf 2 Q' C ∧ Q ≤ Q' ∧ V ≤ normalizer (Q' : Set G) := by
  have hQV : IsPGroup 2 ↥(Q ⊔ V) := hQ.to_sup_of_normal_left' hV hVQ
  obtain ⟨S, hS, hQVS⟩ := exists_isSylowOf_ge (C := C ⊔ V) (Q := Q ⊔ V)
    (sup_le (hQC.trans le_sup_left) le_sup_right) hQV
  refine ⟨S ⊓ C, hS.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hVC),
    le_inf (le_sup_left.trans hQVS) hQC, fun v hv => ?_⟩
  have hvS : v ∈ S := hQVS ((le_sup_right : V ≤ Q ⊔ V) hv)
  exact TwoThin.mem_normalizer_inf (Subgroup.le_normalizer hvS) (hVC hv)

theorem exists_central_involution {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQP : Q ≤ P)
    (hPQ : P ≤ normalizer (Q : Set G)) (hQ : Q ≠ ⊥) :
    ∃ z ∈ Q, orderOf z = 2 ∧ ∀ p ∈ P, z * p = p * z := by
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  let Q' : Subgroup ↥P := Q.subgroupOf P
  have hQ'n : Q'.Normal := normal_subgroupOf_of_le_normalizer hPQ
  have hQ'ne : Q' ≠ ⊥ := by
    intro h
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hQP hq⟩ : ↥P) ∈ Q' := hq
    rw [h] at this
    have h1 : (⟨q, hQP hq⟩ : ↥P) = 1 := this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)
  have hH := Group.IsNilpotent.inf_center_ne_bot_of_normal hQ'ne
  have hHp : IsPGroup 2 ↥(Q' ⊓ center ↥P) := hP.to_subgroup _
  have hcard : 2 ∣ Nat.card ↥(Q' ⊓ center ↥P) := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hn1 : n ≠ 0 := by
      rintro rfl
      exact hH (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn1
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q' ⊓ center ↥P)) 2 hcard
  have hh1 : (h : ↥P) ∈ Q' := (Subgroup.mem_inf.mp h.2).1
  have hh2 : (h : ↥P) ∈ center ↥P := (Subgroup.mem_inf.mp h.2).2
  refine ⟨((h : ↥P) : G), hh1, ?_, fun p hp => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hh]
  · have := Subgroup.mem_center_iff.mp hh2 ⟨p, hp⟩
    exact (congrArg Subtype.val this).symm

end General

section Residual

variable {G : Type} [Group G]

theorem oPrimeResidualOf_eq_closure (p : ℕ) (K : Subgroup G) :
    oPrimeResidualOf p K = Subgroup.closure {x | x ∈ K ∧ ∃ k : ℕ, x ^ p ^ k = 1} := by
  rw [oPrimeResidualOf, oPrimeResidual, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hk])⟩, rfl⟩

theorem mem_oPrimeResidualOf {X : Subgroup G} {g : G} (hg : g ∈ X) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ oPrimeResidualOf 2 X := by
  rw [oPrimeResidualOf_eq_closure]
  exact Subgroup.subset_closure ⟨hg, k, hk⟩

theorem oPrimeResidualOf_mono_of_two_elt {X X' : Subgroup G}
    (h : ∀ g ∈ X, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ X') :
    oPrimeResidualOf 2 X ≤ oPrimeResidualOf 2 X' := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro g ⟨hg, k, hk⟩
  exact mem_oPrimeResidualOf (h g hg k hk) hk

theorem oPrimeResidualOf_le_self (p : ℕ) (X : Subgroup G) : oPrimeResidualOf p X ≤ X :=
  Subgroup.map_subtype_le _

theorem le_normalizer_oPrimeResidualOf {H K : Subgroup G} (hHK : H ≤ normalizer (K : Set G)) :
    H ≤ normalizer (oPrimeResidualOf 2 K : Set G) := by
  rw [oPrimeResidualOf_eq_closure]
  intro h hh
  have key : ∀ g ∈ H, ∀ y ∈ Subgroup.closure {x | x ∈ K ∧ ∃ k : ℕ, x ^ 2 ^ k = 1},
      g * y * g⁻¹ ∈ Subgroup.closure {x | x ∈ K ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxK, k, hk⟩ := hx
      refine Subgroup.subset_closure ⟨?_, k, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hHK hg) x).mp hxK
      · rw [conj_pow, hk, mul_one, mul_inv_cancel]
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key h hh y
  · intro hy
    have := key h⁻¹ (inv_mem hh) _ hy
    simpa [mul_assoc] using this

theorem mem_normalizer_centralizer {Q : Subgroup G} {s : G} (hs : s ∈ normalizer (Q : Set G)) :
    s ∈ normalizer ((centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ s ∈ normalizer (Q : Set G), ∀ c ∈ centralizer (Q : Set G),
      s * c * s⁻¹ ∈ centralizer (Q : Set G) := by
    intro s hs c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : s⁻¹ * q * s ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hs) q).mp hq
      simpa using this
    have h := Subgroup.mem_centralizer_iff.mp hc (s⁻¹ * q * s) hq'
    calc q * (s * c * s⁻¹) = s * ((s⁻¹ * q * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * q * s)) * s⁻¹ := by rw [h]
      _ = (s * c * s⁻¹) * q := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key s hs c
  · intro h
    have := key s⁻¹ (inv_mem hs) _ h
    simpa [mul_assoc] using this

end Residual

section Components

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_of_le {W W' Λ : Subgroup G} (h : IsPCompIn 2 W Λ) (hΛ : Λ ≤ W') (hW' : W' ≤ W) :
    IsPCompIn 2 W' Λ := by
  obtain ⟨-, h2⟩ := isPCompIn_two_iff.mp h
  exact isPCompIn_two_iff.mpr ⟨hΛ, ComponentClassification.TwoComponentTransport.restrict_nested
    Λ W' W hΛ hW' h2⟩

theorem isPCompIn_conj_of_mem_normalizer {X K : Subgroup G} (h : IsPCompIn 2 X K) {s : G}
    (hs : s ∈ normalizer (X : Set G)) : IsPCompIn 2 X (K.map (MulAut.conj s).toMonoidHom) := by
  have hX : X.map (MulAut.conj s).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
  have := isPCompIn_map_conj h s
  rwa [hX] at this

theorem eq_of_isPCompIn_of_cover {Y K₁ K₂ P : Subgroup G} (h₁ : IsPCompIn 2 Y K₁)
    (h₂ : IsPCompIn 2 Y K₂) (hP₁ : P ≤ K₁) (hP₂ : P ≤ K₂)
    (hcov : ∀ k ∈ K₁, ∃ p ∈ P, ∃ o ∈ pPrimeCoreOf 2 K₁, k = p * o) : K₁ = K₂ := by
  by_contra hne
  have hc : K₂ ≤ cSec K₁ := le_cSec_of_ne h₂ h₁ (Ne.symm hne)
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple' (isQuasisimple_hat h₁)
  have hcentral : ∀ (p : G) (hp : p ∈ P) (b : Hat K₁),
      b * hatMk K₁ ⟨p, hP₁ hp⟩ = hatMk K₁ ⟨p, hP₁ hp⟩ * b := by
    intro p hp b
    obtain ⟨b', rfl⟩ := hatMk_surjective K₁ b
    have h1 : ⁅(b' : G), p⁆ ∈ pPrimeCoreOf 2 K₁ := (hc (hP₂ hp)).2.2 (b' : G) b'.2
    have hmem : ⁅(b' : G), p⁆ ∈ K₁ := TwoThin.pPrimeCoreOf_le K₁ h1
    have h2 : hatMk K₁ ⟨⁅(b' : G), p⁆, hmem⟩ = 1 := (hatMk_eq_one_iff K₁ _).mpr h1
    have h3 : (⟨⁅(b' : G), p⁆, hmem⟩ : ↥K₁) = ⁅b', ⟨p, hP₁ hp⟩⁆ := rfl
    rw [h3, map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hall : ∀ y : Hat K₁, ∃ (p : G) (hp : p ∈ P), y = hatMk K₁ ⟨p, hP₁ hp⟩ := by
    intro y
    obtain ⟨k, rfl⟩ := hatMk_surjective K₁ y
    obtain ⟨p, hp, o, ho, hk⟩ := hcov k k.2
    refine ⟨p, hp, ?_⟩
    have h1 : hatMk K₁ ⟨o, TwoThin.pPrimeCoreOf_le K₁ ho⟩ = 1 := (hatMk_eq_one_iff K₁ _).mpr ho
    have : k = ⟨p, hP₁ hp⟩ * ⟨o, TwoThin.pPrimeCoreOf_le K₁ ho⟩ := Subtype.ext hk
    rw [this, map_mul, h1, mul_one]
  obtain ⟨p, hp, rfl⟩ := hall a
  exact hab (hcentral p hp b).symm

end Components

section Cores

variable {G : Type} [Group G] [Finite G]

theorem exists_two_elt_mul {K' D : Subgroup G} (hD : D ≤ K') {t d o' : G} (ht : t ∈ K')
    (hd : d ∈ D) (ho' : o' ∈ pPrimeCoreOf 2 K') (htd : t = d * o') {a : ℕ} (hta : t ^ 2 ^ a = 1) :
    ∃ e ∈ D, e ^ 2 ^ a = 1 ∧ ∃ o ∈ pPrimeCoreOf 2 K', t = e * o := by
  have hdK : d ∈ K' := hD hd
  have ho'K : o' ∈ K' := TwoThin.pPrimeCoreOf_le K' ho'
  have hdO : d ^ 2 ^ a ∈ pPrimeCoreOf 2 K' := by
    have h1 : hatMk K' ⟨o', ho'K⟩ = 1 := (hatMk_eq_one_iff K' _).mpr ho'
    have h2 : (⟨t, ht⟩ : ↥K') = ⟨d, hdK⟩ * ⟨o', ho'K⟩ := Subtype.ext htd
    have h3 : hatMk K' ⟨d, hdK⟩ ^ 2 ^ a = 1 := by
      have h4 : hatMk K' ⟨t, ht⟩ = hatMk K' ⟨d, hdK⟩ := by rw [h2, map_mul, h1, mul_one]
      rw [← h4, ← map_pow]
      have : (⟨t, ht⟩ : ↥K') ^ 2 ^ a = 1 := Subtype.ext (by simpa using hta)
      rw [this, map_one]
    have h5 : hatMk K' (⟨d, hdK⟩ ^ 2 ^ a) = 1 := by rw [map_pow]; exact h3
    exact (hatMk_eq_one_iff K' (⟨d, hdK⟩ ^ 2 ^ a)).mp h5
  set O := pPrimeCoreOf 2 K' with hO
  have hodd : Odd (Nat.card O) := TwoThin.card_pPrimeCoreOf_odd K'
  have hgr : (d ^ 2 ^ a) ^ Nat.card O = 1 := by
    have h := pow_card_eq_one' (G := O) (x := ⟨d ^ 2 ^ a, hdO⟩)
    have h' := congrArg Subtype.val h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h'
  have hcop : Nat.Coprime (Nat.card O) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : d ^ ((2 ^ a * Nat.card O : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, pow_mul]; exact hgr
  refine ⟨d ^ (u * (Nat.card O : ℤ)), zpow_mem hd _, ?_, (d ^ 2 ^ a) ^ v * o',
    mul_mem (zpow_mem hdO _) ho', ?_⟩
  · calc (d ^ (u * (Nat.card O : ℤ))) ^ 2 ^ a
        = d ^ (u * (Nat.card O : ℤ) * ((2 ^ a : ℕ) : ℤ)) := by
          rw [← zpow_natCast, ← zpow_mul]
      _ = (d ^ ((2 ^ a * Nat.card O : ℕ) : ℤ)) ^ u := by
          rw [← zpow_mul]; congr 1; push_cast; ring
      _ = 1 := by rw [h1, one_zpow]
  · have hd' : d = d ^ (u * (Nat.card O : ℤ)) * (d ^ 2 ^ a) ^ v := by
      calc d = d ^ (u * (Nat.card O : ℤ) + v * ((2 ^ a : ℕ) : ℤ)) := by rw [huv, zpow_one]
        _ = d ^ (u * (Nat.card O : ℤ)) * (d ^ 2 ^ a) ^ v := by
          rw [zpow_add, ← zpow_natCast d (2 ^ a), ← zpow_mul]
          congr 2
          ring
    rw [htd, ← mul_assoc, ← hd']

theorem inf_pPrimeCoreOf_le {A B : Subgroup G} (hAB : A ≤ B) :
    A ⊓ pPrimeCoreOf 2 B ≤ pPrimeCoreOf 2 A := by
  intro k hk
  obtain ⟨hkA, hkO⟩ := Subgroup.mem_inf.mp hk
  have hkB : k ∈ B := hAB hkA
  refine PumpRigid.mem_pPrimeCoreOf_of_barMk_eq_one' (Y' := B) hAB hkA hkB ?_
  exact (hatMk_eq_one_iff B ⟨k, hkB⟩).mpr hkO

theorem pPrimeCoreOf_le_of_cover {P K' : Subgroup G} (hPK : P ≤ K')
    (hcov : ∀ k ∈ K', ∃ p ∈ P, ∃ o ∈ pPrimeCoreOf 2 K', k = p * o) :
    pPrimeCoreOf 2 P ≤ pPrimeCoreOf 2 K' := by
  set π := hatMk K' with hπ
  set M : Subgroup ↥K' := (pPrimeCoreOf 2 P).subgroupOf K' with hM
  have hMK : pPrimeCoreOf 2 P ≤ K' := (TwoThin.pPrimeCoreOf_le P).trans hPK
  set Mb : Subgroup (Hat K') := M.map π with hMb
  have hnorm : Mb.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨k, rfl⟩ := hatMk_surjective K' g
    obtain ⟨p, hp, o, ho, hk⟩ := hcov k k.2
    have hπo : π ⟨o, TwoThin.pPrimeCoreOf_le K' ho⟩ = 1 := (hatMk_eq_one_iff K' _).mpr ho
    have hkp : π k = π ⟨p, hPK hp⟩ := by
      have : k = ⟨p, hPK hp⟩ * ⟨o, TwoThin.pPrimeCoreOf_le K' ho⟩ := Subtype.ext hk
      rw [this, map_mul, hπo, mul_one]
    have hmM : (m : G) ∈ pPrimeCoreOf 2 P := Subgroup.mem_subgroupOf.mp hm
    have hconj : p * (m : G) * p⁻¹ ∈ pPrimeCoreOf 2 P := TwoThin.pPrimeCoreOf_normalized P hp hmM
    refine ⟨⟨p * (m : G) * p⁻¹, hMK hconj⟩, Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    rw [hkp, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hodd : Nat.Coprime 2 (Nat.card Mb) := by
    have h1 : Nat.card Mb ∣ Nat.card M := Subgroup.card_map_dvd _ _
    have h2 : Nat.card M = Nat.card (pPrimeCoreOf 2 P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv
    have h3 : Odd (Nat.card Mb) := Odd.of_dvd_nat (h2 ▸ TwoThin.card_pPrimeCoreOf_odd P) h1
    exact Nat.coprime_two_left.mpr h3
  have hMb : Mb ≤ pPrimeCore 2 (Hat K') := le_sSup ⟨hnorm, hodd⟩
  have hbot : pPrimeCore 2 (Hat K') = ⊥ := pPrimeCore_quotient_eq_bot ↥K'
  intro m hm
  have hmK : m ∈ K' := hMK hm
  have hm1 : π ⟨m, hmK⟩ ∈ Mb := ⟨⟨m, hmK⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  have := hMb hm1
  rw [hbot, Subgroup.mem_bot] at this
  exact (hatMk_eq_one_iff K' ⟨m, hmK⟩).mp this

end Cores

end CFSG.GH74.GLS.C3.Layer1.Iv251
