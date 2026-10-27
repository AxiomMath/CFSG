module

public import CFSG.GH74.GLS.LU.Local.GenCore
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Y

variable {Y : Type} [Group Y]

theorem commutator_eq_bot_of_le_centralizer {K Z : Subgroup Y} (hK : ⁅K, K⁆ = K)
    (h : ⁅K, Z⁆ ≤ centralizer (K : Set Y)) : ⁅K, Z⁆ = ⊥ := by
  have h1 : ⁅⁅K, Z⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  have h2 : ⁅⁅Z, K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Z K]; exact h1
  have h3 : ⁅⁅K, K⁆, Z⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hK] at h3

end Y

variable {Y : Type} [Group Y] [Finite Y]

theorem inf_pPrimeCore_eq_bot {K : Subgroup Y} (hKq : IsQuasisimple K) {s : Y} (hs : orderOf s = 2)
    (hsK : s ∈ K) (hKc : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k ∈ zpowers s) :
    K ⊓ pPrimeCore 2 Y = ⊥ := by
  have hN : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  have hM : ((pPrimeCore 2 Y).subgroupOf K).Normal := Subgroup.normal_subgroupOf
  have hodd : Odd (Nat.card (pPrimeCore 2 Y)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hM with h | h
  · exfalso
    have hsN : s ∈ pPrimeCore 2 Y := by
      have : (⟨s, hsK⟩ : K) ∈ (pPrimeCore 2 Y).subgroupOf K := by rw [h]; exact mem_top _
      exact this
    have hdvd := Subgroup.orderOf_dvd_natCard _ hsN
    rw [hs] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  · rw [eq_bot_iff]
    rintro x ⟨hxK, hxN⟩
    have hxM : (⟨x, hxK⟩ : K) ∈ (pPrimeCore 2 Y).subgroupOf K := hxN
    have hxc : (⟨x, hxK⟩ : K) ∈ center K := h hxM
    have h1 : ∀ k' ∈ K, x * k' = k' * x := by
      intro k' hk'
      have := Subgroup.mem_center_iff.mp hxc ⟨k', hk'⟩
      exact (congrArg Subtype.val this).symm
    have hxz : x ∈ zpowers s := hKc x hxK h1
    have h2 : orderOf x ∣ 2 := hs ▸ orderOf_dvd_of_mem_zpowers hxz
    have h3 : orderOf x ∣ Nat.card (pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ hxN
    have h4 : orderOf x ∣ Nat.gcd 2 (Nat.card (pPrimeCore 2 Y)) := Nat.dvd_gcd h2 h3
    have h5 : Nat.gcd 2 (Nat.card (pPrimeCore 2 Y)) = 1 := pPrimeCore_coprime_card
    rw [h5] at h4
    have : orderOf x = 1 := Nat.dvd_one.mp h4
    rw [orderOf_eq_one_iff] at this
    rw [this]; exact one_mem _

omit [Finite Y] in
theorem comm_of_mem_pPrimeCore_of_mem_centralizer {K : Subgroup Y} {s : Y}
    (hKn : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hK1 : K ⊓ pPrimeCore 2 Y = ⊥) {d : Y} (hdN : d ∈ pPrimeCore 2 Y)
    (hds : d ∈ centralizer ({s} : Set Y)) {k : Y} (hk : k ∈ K) : d * k = k * d := by
  have hN : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  have h1 : d * k * d⁻¹ * k⁻¹ ∈ K := mul_mem (hKn d hds k hk) (inv_mem hk)
  have h2 : d * k * d⁻¹ * k⁻¹ ∈ pPrimeCore 2 Y := by
    have : d * (k * d⁻¹ * k⁻¹) ∈ pPrimeCore 2 Y :=
      mul_mem hdN (hN.conj_mem _ (inv_mem hdN) k)
    simpa [mul_assoc] using this
  have h3 : d * k * d⁻¹ * k⁻¹ ∈ K ⊓ pPrimeCore 2 Y := ⟨h1, h2⟩
  rw [hK1, mem_bot] at h3
  calc d * k = (d * k * d⁻¹ * k⁻¹) * (k * d) := by group
    _ = k * d := by rw [h3, one_mul]

def commModN (s : Y) (K : Subgroup Y) : Subgroup Y where
  carrier := {y | y ∈ centralizer ({s} : Set Y) ∧ ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pPrimeCore 2 Y}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun k hk => ?_⟩
    have hN : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
    have h1 := ha' k hk
    have h2 := hb' k hk
    have h3 : a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ ∈ pPrimeCore 2 Y := hN.conj_mem _ h2 a
    have : a * b * k * (a * b)⁻¹ * k⁻¹ =
        (a * (b * k * b⁻¹ * k⁻¹) * a⁻¹) * (a * k * a⁻¹ * k⁻¹) := by group
    rw [this]
    exact mul_mem h3 h1
  one_mem' := ⟨one_mem _, fun k _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun k hk => ?_⟩
    have hN : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
    have h1 := ha' k hk
    have h3 := hN.conj_mem _ (inv_mem h1) a⁻¹
    rw [inv_inv] at h3
    have : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a := by group
    rw [this]; exact h3

omit [Finite Y] in
theorem comm_of_commutator_mem_pPrimeCore {K : Subgroup Y} {s : Y} (hKp : ⁅K, K⁆ = K)
    (hKs : K ≤ centralizer ({s} : Set Y))
    (hKn : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hK1 : K ⊓ pPrimeCore 2 Y = ⊥) {y : Y} (hy : y ∈ centralizer ({s} : Set Y))
    (hyN : ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pPrimeCore 2 Y) : ∀ k ∈ K, y * k = k * y := by
  have hyZ : y ∈ commModN s K := ⟨hy, hyN⟩
  have hle : ⁅K, commModN s K⁆ ≤ centralizer (K : Set Y) := by
    rw [Subgroup.commutator_le]
    intro k hk w hw
    obtain ⟨hws, hwN⟩ := hw
    rw [mem_centralizer_iff]
    intro k' hk'
    have hk's : k ∈ centralizer ({s} : Set Y) := hKs hk
    have hcN : ⁅k, w⁆ ∈ pPrimeCore 2 Y := by
      have := inv_mem (hwN k hk)
      have e : ⁅k, w⁆ = (w * k * w⁻¹ * k⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [e]; exact this
    have hcs : ⁅k, w⁆ ∈ centralizer ({s} : Set Y) := by
      have e : ⁅k, w⁆ = k * w * k⁻¹ * w⁻¹ := rfl
      rw [e]
      exact mul_mem (mul_mem (mul_mem hk's hws) (inv_mem hk's)) (inv_mem hws)
    exact (comm_of_mem_pPrimeCore_of_mem_centralizer hKn hK1 hcN hcs hk').symm
  have hbot := commutator_eq_bot_of_le_centralizer hKp hle
  intro k hk
  have : ⁅k, y⁆ ∈ ⁅K, commModN s K⁆ := Subgroup.commutator_mem_commutator hk hyZ
  rw [hbot, mem_bot] at this
  rw [commutatorElement_def] at this
  calc y * k = (k * y * k⁻¹ * y⁻¹)⁻¹ * (k * y) := by group
    _ = k * y := by rw [this]; simp

theorem centralizer_map_barMk {K : Subgroup Y} {s : Y} (hs : orderOf s = 2) (hsK : s ∈ K)
    (hKp : ⁅K, K⁆ = K) (hKs : K ≤ centralizer ({s} : Set Y))
    (hKn : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hK1 : K ⊓ pPrimeCore 2 Y = ⊥) :
    centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) =
      (centralizer (K : Set Y)).map (barMk Y) := by
  ext yb
  constructor
  · intro hyb
    have hybs : yb ∈ centralizer ({barMk Y s} : Set (barQ Y)) := by
      rw [mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (mem_centralizer_iff.mp hyb) (barMk Y s) (Subgroup.mem_map_of_mem _ hsK)
    rw [← map_centralizer_barMk hs] at hybs
    obtain ⟨y, hy, rfl⟩ := hybs
    have hy' : y ∈ centralizer ({s} : Set Y) := hy
    refine ⟨y, ?_, rfl⟩
    show y ∈ centralizer (K : Set Y)
    rw [mem_centralizer_iff]
    intro k hk
    have hk' := comm_of_commutator_mem_pPrimeCore hKp hKs hKn hK1 hy' (fun k hk => by
      have h1 := (mem_centralizer_iff.mp hyb) (barMk Y k) (Subgroup.mem_map_of_mem _ hk)
      rw [← ker_barMk]
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [← h1]; group) k hk
    exact hk'.symm
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer (K : Set Y) := hy
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hy') k hk]

omit [Finite Y] in
theorem eq_of_mem_zpowers_of_orderOf_two {s c : Y} (hs : orderOf s = 2) (hc : orderOf c = 2)
    (h : c ∈ zpowers s) : c = s := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : s ^ m = s ^ (m % (orderOf s : ℤ)) := (zpow_mod_orderOf s m).symm
  rw [hs] at h1
  have h2 : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h2 | h2
  · rw [h2] at h1
    rw [← hm, h1] at hc
    simp at hc
  · rw [h2] at h1
    rw [← hm, h1]; simp

theorem involution_eq_of_cyclic_sylow {C : Subgroup Y} {s c : Y} (hsC : s ∈ C) (hcC : c ∈ C)
    (hs : orderOf s = 2) (hc : orderOf c = 2) (hsc : ∀ x ∈ C, x * s = s * x)
    (hcyc : ∀ T : Sylow 2 ↥C, IsCyclic ↥T) : c = s := by
  classical
  let c' : ↥C := ⟨c, hcC⟩
  let s' : ↥C := ⟨s, hsC⟩
  have hc' : orderOf c' = 2 := by rw [← Subgroup.orderOf_coe]; exact hc
  have hs' : orderOf s' = 2 := by rw [← Subgroup.orderOf_coe]; exact hs
  have hpc : IsPGroup 2 (zpowers c') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hc']; simp)
  have hps : IsPGroup 2 (zpowers s') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs']; simp)
  have hsn : (zpowers s').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcm : Commute g s' := Subtype.ext (hsc g.1 g.2)
    rw [(hcm.zpow_right m).eq, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
  obtain ⟨T, hT⟩ := hpc.exists_le_sylow
  have hsT : zpowers s' ≤ T := hps.le_sylow_of_normal T
  have hcT : c' ∈ T := hT (mem_zpowers c')
  have hsT' : s' ∈ T := hsT (mem_zpowers s')
  have := hcyc T
  let cT : ↥(T : Subgroup ↥C) := ⟨c', hcT⟩
  let sT : ↥(T : Subgroup ↥C) := ⟨s', hsT'⟩
  have hcT2 : orderOf cT = 2 := by rw [← Subgroup.orderOf_coe]; exact hc'
  have hsT2 : orderOf sT = 2 := by rw [← Subgroup.orderOf_coe]; exact hs'
  have hcard : Nat.card (zpowers cT) = Nat.card (zpowers sT) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hcT2, hsT2]
  have heq : zpowers cT = zpowers sT := IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
  have hmem : cT ∈ zpowers sT := heq ▸ mem_zpowers cT
  have h1 := eq_of_mem_zpowers_of_orderOf_two hsT2 hcT2 hmem
  exact congrArg (fun x : ↥(T : Subgroup ↥C) => ((x : ↥C) : Y)) h1

theorem eq_barMk_of_involution {K : Subgroup Y} {s : Y} (hs : orderOf s = 2) (hsK : s ∈ K)
    (hKp : ⁅K, K⁆ = K) (hKs : K ≤ centralizer ({s} : Set Y))
    (hKn : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hK1 : K ⊓ pPrimeCore 2 Y = ⊥)
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    {c : barQ Y} (hcC : c ∈ centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)))
    (hc : orderOf c = 2) : c = barMk Y s := by
  rw [centralizer_map_barMk hs hsK hKp hKs hKn hK1] at hcC
  obtain ⟨y, hy, rfl⟩ := hcC
  have hyC : y ∈ centralizer (K : Set Y) := hy
  have hmodd : Odd (Nat.card (pPrimeCore 2 Y)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hc2 : barMk Y y ^ 2 = 1 := by
    have := pow_orderOf_eq_one (barMk Y y)
    rwa [hc] at this
  have hy2N : y ^ 2 ∈ pPrimeCore 2 Y := by
    rw [← ker_barMk, MonoidHom.mem_ker, map_pow]; exact hc2
  have hy2m : (y ^ 2) ^ (Nat.card (pPrimeCore 2 Y)) = 1 := by
    have h1 : (⟨y ^ 2, hy2N⟩ : ↥(pPrimeCore 2 Y)) ^ (Nat.card (pPrimeCore 2 Y)) = 1 :=
      pow_card_eq_one'
    exact congrArg Subtype.val h1
  set m := Nat.card (pPrimeCore 2 Y) with hm
  have hy'sq : (y ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; exact hy2m
  have hy'C : y ^ m ∈ centralizer (K : Set Y) := pow_mem hyC m
  have hbar : barMk Y (y ^ m) = barMk Y y := by
    rw [map_pow]
    obtain ⟨k, hk⟩ := hmodd
    rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul]
  have hne : y ^ m ≠ 1 := by
    intro h
    rw [h, map_one] at hbar
    have : barMk Y y = 1 := hbar.symm
    rw [this, orderOf_one] at hc
    omega
  have hord : orderOf (y ^ m) = 2 := orderOf_eq_prime hy'sq hne
  have hsC : s ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]; intro k hk; exact (mem_centralizer_iff.mp (hKs hk)) s rfl |>.symm
  have heq : y ^ m = s := by
    refine involution_eq_of_cyclic_sylow (C := centralizer (K : Set Y)) hsC hy'C hs hord ?_ hcyc
    intro x hx
    exact ((mem_centralizer_iff.mp hx) s hsK).symm
  rw [← hbar, heq]

theorem exists_component_ge {s : Y} (hs : orderOf s = 2) {K : Subgroup Y}
    (hKs : K ≤ centralizer ({s} : Set Y)) (hsK : s ∈ K)
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({s} : Set Y)))) :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧ K.map (barMk Y) ≤ L ∧ barMk Y s ∈ L := by
  have hJ : K.map (barMk Y) ≤ ⨆ g ∈ CFSG.layer (barQ Y),
      (K.map (barMk Y)).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    refine Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (one_mem _) ?_)
    exact ⟨x, hx, by simp⟩
  obtain ⟨L, hL, hcases, -⟩ := pumpup_structure (J := K) hs hKs hK hJ
  have hs' : orderOf (barMk Y s) = 2 := orderOf_barMk hs
  have hsK' : barMk Y s ∈ K.map (barMk Y) := Subgroup.mem_map_of_mem _ hsK
  rcases hcases with ⟨-, hKL⟩ | ⟨hne, hAB, hdiag⟩
  · exact ⟨L, hL, hKL, hKL hsK'⟩
  · exfalso
    apply hne
    have hmem := hdiag hsK'
    obtain ⟨x, hx⟩ := hmem
    have hsup : barMk Y s ∈ L ⊔ conjSub (barMk Y s)⁻¹ L := by
      have h1 : swapDiag hAB x ∈ L ⊔ conjSub (barMk Y s)⁻¹ L := swapDiag_mem_sup hAB x
      rw [hx] at h1; exact h1
    have hcomm : ∀ h ∈ L, ∀ k ∈ conjSub (barMk Y s)⁻¹ L, h * k = k * h := by
      intro h hh k hk
      have := Subgroup.commutator_mem_commutator hh hk
      rw [hAB, Subgroup.mem_bot, commutatorElement_def] at this
      calc h * k = (h * k * h⁻¹ * k⁻¹) * (k * h) := by group
        _ = k * h := by rw [this, one_mul]
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm hsup
    have hsn : ∀ h : barQ Y, h ∈ L ↔ barMk Y s * h * (barMk Y s)⁻¹ ∈ L := by
      intro h
      constructor
      · intro hh
        rw [hab]
        have e : a * b * h * (a * b)⁻¹ = a * h * a⁻¹ := by
          have := hcomm h hh b hb
          calc a * b * h * (a * b)⁻¹ = a * (b * h) * b⁻¹ * a⁻¹ := by group
            _ = a * (h * b) * b⁻¹ * a⁻¹ := by rw [← this]
            _ = a * h * a⁻¹ := by group
        rw [e]; exact mul_mem (mul_mem ha hh) (inv_mem ha)
      · intro hh
        rw [hab] at hh
        have hxL : a⁻¹ * (a * b * h * (a * b)⁻¹) * a ∈ L :=
          mul_mem (mul_mem (inv_mem ha) hh) ha
        have hbc := hcomm _ hxL b hb
        have e : a⁻¹ * (a * b * h * (a * b)⁻¹) * a = b * h * b⁻¹ := by group
        rw [e] at hxL hbc
        have h3 : b⁻¹ * (b * h * b⁻¹) * b = b * h * b⁻¹ := by
          rw [mul_assoc, hbc, ← mul_assoc, inv_mul_cancel, one_mul]
        have h4 : h = b * h * b⁻¹ := by
          calc h = b⁻¹ * (b * h * b⁻¹) * b := by group
            _ = b * h * b⁻¹ := h3
        rw [h4]; exact hxL
    have hinv : (barMk Y s)⁻¹ = barMk Y s := inv_eq_self_of_orderOf_eq_two hs'
    have hgg : barMk Y s * barMk Y s = 1 := by
      have := mul_inv_cancel (barMk Y s)
      rwa [hinv] at this
    rw [hinv]
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hsn k).mp hk
    · intro hy
      refine ⟨barMk Y s * y * (barMk Y s)⁻¹, (hsn y).mp hy, ?_⟩
      show barMk Y s * (barMk Y s * y * (barMk Y s)⁻¹) * (barMk Y s)⁻¹ = y
      rw [hinv]
      calc barMk Y s * (barMk Y s * y * barMk Y s) * barMk Y s
          = (barMk Y s * barMk Y s) * y * (barMk Y s * barMk Y s) := by group
        _ = y := by rw [hgg]; simp

omit [Finite Y] in
theorem odd_normal_eq_bot {K : Subgroup Y} (hKq : IsQuasisimple K) {s : Y} (hs : orderOf s = 2)
    (hsK : s ∈ K) (hKc : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k ∈ zpowers s)
    {M : Subgroup ↥K} (hM : M.Normal) (hodd : Odd (Nat.card M)) : M = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hM with h | h
  · exfalso
    have : (⟨s, hsK⟩ : K) ∈ M := by rw [h]; exact mem_top _
    have hdvd := Subgroup.orderOf_dvd_natCard _ this
    have : orderOf (⟨s, hsK⟩ : K) = 2 := by rw [← Subgroup.orderOf_coe]; exact hs
    rw [this] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  · rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ center K := h hx
    have h1 : ∀ k' ∈ K, (x : Y) * k' = k' * x := by
      intro k' hk'
      have := Subgroup.mem_center_iff.mp hxc ⟨k', hk'⟩
      exact (congrArg Subtype.val this).symm
    have hxz : (x : Y) ∈ zpowers s := hKc x x.2 h1
    have h2 : orderOf (x : Y) ∣ 2 := hs ▸ orderOf_dvd_of_mem_zpowers hxz
    have h2' : orderOf x ∣ 2 := by rwa [Subgroup.orderOf_coe] at h2
    have h3 : orderOf x ∣ Nat.card M := Subgroup.orderOf_dvd_natCard _ hx
    have h4 : orderOf x ∣ Nat.gcd 2 (Nat.card M) := Nat.dvd_gcd h2' h3
    have h5 : Nat.gcd 2 (Nat.card M) = 1 := Nat.coprime_two_left.mpr hodd
    rw [h5] at h4
    have : orderOf x = 1 := Nat.dvd_one.mp h4
    rw [orderOf_eq_one_iff] at this
    rw [this]; exact one_mem _

theorem isTwoComponent_of_normal_quasisimple {s : Y} (hs : orderOf s = 2) {K : Subgroup Y}
    (hKs : K ≤ centralizer ({s} : Set Y))
    (hKn : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hKq : IsQuasisimple K)
    (hsK : s ∈ K) (hKc : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k ∈ zpowers s) :
    TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({s} : Set Y))) := by
  have hnorm : (K.subgroupOf (centralizer ({s} : Set Y))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := hKn g.1 g.2 n.1 hn
    exact this
  have hsub : (K.subgroupOf (centralizer ({s} : Set Y))).IsSubnormal := hnorm.isSubnormal
  have hc : pPrimeCore 2 ↥K = ⊥ := by
    refine odd_normal_eq_bot hKq hs hsK hKc (M := pPrimeCore 2 ↥K) pPrimeCore_normal ?_
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h1 : CFSG.IsPComponent 2 (⊤ : Subgroup ↥K) :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.isPComponent_top hKq hc
  have h2 : TwoComponents.IsTwoComponent (⊤ : Subgroup ↥K) :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).mp h1
  have h3 : TwoComponents.IsTwoComponent (K.subgroupOf K) := by
    rw [Subgroup.subgroupOf_self]; exact h2
  exact TwoComponentTransport.extend_nested K K (centralizer ({s} : Set Y)) le_rfl hKs hsub h3

structure KComp (Y : Type) [Group Y] (s : Y) (K : Subgroup Y) : Prop where
  ord : orderOf s = 2
  mem : s ∈ K
  le : K ≤ centralizer ({s} : Set Y)
  norm : ∀ c ∈ centralizer ({s} : Set Y), ∀ k ∈ K, c * k * c⁻¹ ∈ K
  quasi : IsQuasisimple K
  cen : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k ∈ zpowers s
  only : ∀ Λ : Subgroup Y, Λ ≤ centralizer ({s} : Set Y) →
    TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y))) → Λ = K

namespace KComp

variable {s : Y} {K : Subgroup Y}

omit [Finite Y] in
theorem perfect (h : KComp Y s K) : ⁅K, K⁆ = K := by
  have hp : Group.IsPerfect ↥K := h.quasi.1
  have h1 : (_root_.commutator ↥K).map K.subtype = K := by
    rw [hp.commutator_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    range_subtype] at h1
  exact h1

theorem inf_bot (h : KComp Y s K) : K ⊓ pPrimeCore 2 Y = ⊥ :=
  inf_pPrimeCore_eq_bot h.quasi h.ord h.mem h.cen

theorem isTwoComponent (h : KComp Y s K) :
    TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({s} : Set Y))) :=
  isTwoComponent_of_normal_quasisimple h.ord h.le h.norm h.quasi h.mem h.cen

theorem exists_component (h : KComp Y s K) :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧ K.map (barMk Y) ≤ L ∧ barMk Y s ∈ L :=
  exists_component_ge h.ord h.le h.mem h.isTwoComponent

end KComp

end CFSG.GH74.GLS.LU.Local
