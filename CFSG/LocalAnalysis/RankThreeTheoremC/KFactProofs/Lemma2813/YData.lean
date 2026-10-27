module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Klein
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.HbarFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem ys_psi_eq_iff {ψ : ↥X →* GL32} (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) (u v : ↥X) :
    ψ u = ψ v ↔ (u : A)⁻¹ * (v : A) ∈ pCoreOf 2 X := by
  have h1 : ψ u = ψ v ↔ u⁻¹ * v ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  rw [h1, hψk, Subgroup.mem_subgroupOf]
  rfl

theorem ys_comm_mem (h : Hyp2813 X K R P) {b : A}
    (hb : b ∈ normalizer (X : Set A)) (hbK : ⁅zpowers b, K⁆ ≤ pCoreOf 2 X) {c : A}
    (hc : c ∈ zpowers b) {x : A} (hx : x ∈ X) : x⁻¹ * (c * x * c⁻¹) ∈ pCoreOf 2 X := by
  obtain ⟨k, hk, o, ho, rfl⟩ := h.mem_X_iff.1 hx
  have hnQ : normalizer (X : Set A) ≤ normalizer (pCoreOf 2 X : Set A) :=
    normalizer_le_normalizer_pCoreOf (le_refl _)
  have hcN : c ∈ normalizer (pCoreOf 2 X : Set A) :=
    hnQ ((Subgroup.zpowers_le.2 hb) hc)
  have hco : c * o * c⁻¹ ∈ pCoreOf 2 X := (mem_normalizer_iff.1 hcN o).1 ho
  have hcomm : c * k⁻¹ * c⁻¹ * k ∈ pCoreOf 2 X := by
    have := hbK (Subgroup.commutator_mem_commutator hc (K.inv_mem hk))
    simpa [commutatorElement_def] using this
  have e : (k * o)⁻¹ * (c * (k * o) * c⁻¹) =
      o⁻¹ * (c * k⁻¹ * c⁻¹ * k)⁻¹ * (c * o * c⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem ho)
    ((pCoreOf 2 X).inv_mem hcomm)) hco

theorem ys_conj_psi (h : Hyp2813 X K R P) {ψ : ↥X →* GL32}
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) {b : A}
    (hb : b ∈ normalizer (X : Set A)) (hbK : ⁅zpowers b, K⁆ ≤ pCoreOf 2 X)
    {x₀ : A} (hx₀ : x₀ ∈ X) {c : A} (hc : c ∈ zpowers b) {s : A} (hs : s ∈ X)
    (hsy : (x₀ * c)⁻¹ * s * (x₀ * c) ∈ X) :
    ψ ⟨(x₀ * c)⁻¹ * s * (x₀ * c), hsy⟩ = (ψ ⟨x₀, hx₀⟩)⁻¹ * ψ ⟨s, hs⟩ * ψ ⟨x₀, hx₀⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul, ys_psi_eq_iff hψk]
  have hx' : x₀⁻¹ * s * x₀ ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hx₀) hs) hx₀
  have h1 := ys_comm_mem h hb hbK ((zpowers b).inv_mem hc) hx'
  have h2 := (pCoreOf 2 X).inv_mem h1
  have e : ((x₀ * c)⁻¹ * s * (x₀ * c))⁻¹ * (x₀⁻¹ * s * x₀) =
      (((x₀⁻¹ * s * x₀)⁻¹ * (c⁻¹ * (x₀⁻¹ * s * x₀) * c⁻¹⁻¹)))⁻¹ := by group
  show ((x₀ * c)⁻¹ * s * (x₀ * c))⁻¹ * (x₀⁻¹ * s * x₀) ∈ pCoreOf 2 X
  rw [e]
  exact h2

theorem ys_key (h : Hyp2813 X K R P) {b : A} (hb : b ∈ normalizer (X : Set A))
    (hbK : ⁅zpowers b, K⁆ ≤ pCoreOf 2 X) {d₀ : A} (hd₀P : d₀ ∈ P) (hd₀3 : orderOf d₀ = 3)
    {y : A} (hy : y ∈ X ⊔ zpowers b) (hyd : y * d₀ = d₀ * y) {s : A} (hs : s ∈ pCoreOf 2 P) :
    y⁻¹ * s * y ∈ pCoreOf 2 P := by
  obtain ⟨ψ, hψs, hψk⟩ := h.exists_psi
  have hd₀X : d₀ ∈ X := h.P_le hd₀P
  have hbN : zpowers b ≤ normalizer (X : Set A) := Subgroup.zpowers_le.2 hb
  have hyN : y ∈ normalizer (X : Set A) := (sup_le Subgroup.le_normalizer hbN) hy
  have hset : ((X ⊔ zpowers b : Subgroup A) : Set A) = (X : Set A) * (zpowers b : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left X (zpowers b) hbN
  have hy' : y ∈ (X : Set A) * (zpowers b : Set A) := by
    rw [← hset]
    exact hy
  obtain ⟨x₀, hx₀, c, hc, rfl⟩ := hy'
  have hx₀' : x₀ ∈ X := hx₀
  have hc' : c ∈ zpowers b := hc
  have hq₁ := ys_comm_mem h hb hbK hc' hd₀X
  have e1 : d₀ * x₀ = x₀ * (c * d₀ * c⁻¹) := by
    calc d₀ * x₀ = d₀ * (x₀ * c) * c⁻¹ := by group
      _ = x₀ * c * d₀ * c⁻¹ := by rw [← hyd]
      _ = x₀ * (c * d₀ * c⁻¹) := by group
  have hcomm : ψ ⟨x₀, hx₀'⟩ * ψ ⟨d₀, hd₀X⟩ = ψ ⟨d₀, hd₀X⟩ * ψ ⟨x₀, hx₀'⟩ := by
    rw [← map_mul, ← map_mul, ys_psi_eq_iff hψk]
    have e2 : (x₀ * d₀)⁻¹ * (d₀ * x₀) = d₀⁻¹ * (c * d₀ * c⁻¹) := by
      rw [e1]
      group
    show (x₀ * d₀)⁻¹ * (d₀ * x₀) ∈ pCoreOf 2 X
    rw [e2]
    exact hq₁
  have hzp : ψ ⟨x₀, hx₀'⟩ ∈ zpowers (ψ ⟨d₀, hd₀X⟩) :=
    centralizer_order3 (dbar_order X hψk hd₀X hd₀3) hcomm
  have hdn : ψ ⟨d₀, hd₀X⟩ ∈ normalizer (Hbar X ψ (pCoreOf 2 P) : Set GL32) :=
    dbar_mem_normalizer X ψ h.P_le hd₀P
  have hxn : ψ ⟨x₀, hx₀'⟩ ∈ normalizer (Hbar X ψ (pCoreOf 2 P) : Set GL32) :=
    (Subgroup.zpowers_le.2 hdn) hzp
  have hsX : s ∈ X := h.P_le (pCoreOf_le_self P hs)
  have hty : (x₀ * c)⁻¹ * s * (x₀ * c) ∈ X := (mem_normalizer_iff''.1 hyN s).1 hsX
  have hψt := ys_conj_psi h hψk hb hbK hx₀' hc' hsX hty
  have hmem : ψ ⟨s, hsX⟩ ∈ Hbar X ψ (pCoreOf 2 P) :=
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 hs)
  have hmem2 : ψ ⟨(x₀ * c)⁻¹ * s * (x₀ * c), hty⟩ ∈ Hbar X ψ (pCoreOf 2 P) := by
    rw [hψt]
    exact (mem_normalizer_iff''.1 hxn _).1 hmem
  obtain ⟨s'', hs'', hs''eq⟩ := Subgroup.mem_map.1 hmem2
  have hq := (ys_psi_eq_iff hψk s'' _).1 hs''eq
  have hq' : (s'' : A)⁻¹ * ((x₀ * c)⁻¹ * s * (x₀ * c)) ∈ pCoreOf 2 P :=
    h.pCore_X_le_pCore_P hq
  have hs''S : (s'' : A) ∈ pCoreOf 2 P := Subgroup.mem_subgroupOf.1 hs''
  have := (pCoreOf 2 P).mul_mem hs''S hq'
  simpa using this

theorem Hyp2813.normalizes_S_of_comm (h : Hyp2813 X K R P) {b : A}
    (hb : b ∈ normalizer (X : Set A)) (hbK : ⁅zpowers b, K⁆ ≤ pCoreOf 2 X) {d₀ : A} (hd₀P : d₀ ∈ P)
    (hd₀3 : orderOf d₀ = 3) {y : A} (hy : y ∈ X ⊔ zpowers b) (hyd : y * d₀ = d₀ * y) :
    y ∈ normalizer (pCoreOf 2 P : Set A) := by
  rw [mem_normalizer_iff'']
  intro s
  refine ⟨fun hs => ys_key h hb hbK hd₀P hd₀3 hy hyd hs, fun hs => ?_⟩
  have hy' : y⁻¹ ∈ X ⊔ zpowers b := (X ⊔ zpowers b).inv_mem hy
  have hyd' : y⁻¹ * d₀ = d₀ * y⁻¹ := (Commute.inv_left (show Commute y d₀ from hyd))
  have := ys_key h hb hbK hd₀P hd₀3 hy' hyd' hs
  simpa [mul_assoc] using this

end B

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem yd_not_mem_X (h : Hyp2813 X K R P) {b : A} (hb3 : b ^ 3 = 1)
    (hbK : ⁅zpowers b, K⁆ ≤ pCoreOf 2 X) (hbx : ∃ x ∈ X, b * x ≠ x * b) : b ∉ X := by
  intro hbX
  obtain ⟨ψ, hψs, hψk⟩ := h.exists_psi
  have hker_mem : ∀ {g : A} (hg : g ∈ X), g ∈ pCoreOf 2 X → ψ ⟨g, hg⟩ = 1 := by
    intro g hg hgq
    have : (⟨g, hg⟩ : ↥X) ∈ ψ.ker := by
      rw [hψk, Subgroup.mem_subgroupOf]
      exact hgq
    exact this
  have hker : ∀ k (hk : k ∈ K),
      ψ ⟨b, hbX⟩ * ψ ⟨k, h.K_le hk⟩ = ψ ⟨k, h.K_le hk⟩ * ψ ⟨b, hbX⟩ := by
    intro k hk
    have hkX : k ∈ X := h.K_le hk
    have hq : b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 X :=
      hbK (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hk)
    have h1 := hker_mem (g := b * k * b⁻¹ * k⁻¹)
      (X.mul_mem (X.mul_mem (X.mul_mem hbX hkX) (X.inv_mem hbX)) (X.inv_mem hkX)) hq
    have h2 : ψ (⟨b, hbX⟩ * ⟨k, hkX⟩ * ⟨b, hbX⟩⁻¹ * ⟨k, hkX⟩⁻¹) = 1 := h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm (g₁ := ψ ⟨b, hbX⟩) (g₂ := ψ ⟨k, hkX⟩)).1 h2
  have hcen : ψ ⟨b, hbX⟩ ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hψs g
    obtain ⟨k, hk, o, ho, hxko⟩ := h.mem_X_iff.1 x.2
    have hx : x = ⟨k, h.K_le hk⟩ * ⟨o, pCoreOf_le_self X ho⟩ := Subtype.ext hxko
    rw [hx, map_mul, hker_mem (pCoreOf_le_self X ho) ho, mul_one]
    exact (hker k hk).symm
  rw [CFSG.QuasithinUnique.Setup.Family.center_GL32, Subgroup.mem_bot] at hcen
  have hbQ : b ∈ pCoreOf 2 X := by
    have : (⟨b, hbX⟩ : ↥X) ∈ ψ.ker := hcen
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact this
  obtain ⟨n, hn⟩ := isPGroup_pCoreOf X ⟨b, hbQ⟩
  have hbn : b ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hord : orderOf b = 1 := by
    have h1 : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    have h2 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hbn
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at this
  have hb1 : b = 1 := orderOf_eq_one_iff.1 hord
  obtain ⟨x, -, hne⟩ := hbx
  exact hne (by rw [hb1, one_mul, mul_one])

theorem yd_card_sup {b : A} (hb : b ∈ normalizer (X : Set A)) (hb3 : b ^ 3 = 1) (hbX : b ∉ X) :
    Nat.card ↥(X ⊔ zpowers b) = Nat.card ↥X * 3 := by
  have hb1 : b ≠ 1 := fun h1 => hbX (h1 ▸ X.one_mem)
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hzc : Nat.card ↥(zpowers b) = 3 := by rw [Nat.card_zpowers, hord]
  have hnorm : zpowers b ≤ normalizer (X : Set A) := Subgroup.zpowers_le.2 hb
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
  have hinf : Nat.card ↥(X ⊓ zpowers b) = 1 := by
    have hdvd : Nat.card ↥(X ⊓ zpowers b) ∣ Nat.card ↥(zpowers b) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hzc] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact h1
    · exfalso
      have heq : X ⊓ zpowers b = zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hzc, h3])
      apply hbX
      have : b ∈ X ⊓ zpowers b := by
        rw [heq]
        exact Subgroup.mem_zpowers b
      exact this.1
  rw [hinf, hzc] at hprod
  simpa using hprod

theorem yd_card_B (h : Hyp2813 X K R P) {B' : Subgroup A} {b : A}
    (hb : b ∈ normalizer (X : Set A)) (hb3 : b ^ 3 = 1) (hbX : b ∉ X)
    (hB'le : B' ≤ X ⊔ zpowers b) (hB'3 : IsPGroup 3 B')
    (hB'i : ¬ 3 ∣ (B'.subgroupOf (X ⊔ zpowers b)).index) : Nat.card ↥B' = 9 := by
  have hY := yd_card_sup hb hb3 hbX
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (isPGroup_pCoreOf X)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hB'3
  have hX := h.card_X
  have hidx := Subgroup.card_mul_index (B'.subgroupOf (X ⊔ zpowers b))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'le).toEquiv, hY, hX, hm, hn] at hidx
  generalize (B'.subgroupOf (X ⊔ zpowers b)).index = idx at hidx hB'i
  have hidx' : 3 ^ n * idx = 2 ^ m * 504 := by rw [hidx]; ring
  have hcop : Nat.Coprime (3 ^ n) (2 ^ m) :=
    Nat.Coprime.pow n m (by norm_num)
  have hd504 : 3 ^ n ∣ 504 := hcop.dvd_of_dvd_mul_left (Dvd.intro idx hidx')
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := h27.trans hd504
    norm_num at this
  generalize 2 ^ m = t at hidx'
  have hn2' : n = 2 := by
    interval_cases n
    · exfalso
      apply hB'i
      omega
    · exfalso
      apply hB'i
      omega
    · rfl
  rw [hn, hn2']
  norm_num

theorem Hyp2813.y_data (h : Hyp2813 X K R P) {D B' : Subgroup A} {b : A} (hDP : D ≤ P)
    (hD3 : IsPGroup 3 D) (hDi : ¬ 3 ∣ (D.subgroupOf P).index)
    (hb : b ∈ normalizer (X : Set A)) (hb3 : b ^ 3 = 1) (hbK : ⁅zpowers b, K⁆ ≤ pCoreOf 2 X)
    (hbx : ∃ x ∈ X, b * x ≠ x * b) (hB'le : B' ≤ X ⊔ zpowers b) (hB'3 : IsPGroup 3 B')
    (hDB' : D ≤ B') (hB'i : ¬ 3 ∣ (B'.subgroupOf (X ⊔ zpowers b)).index) :
    ∀ y ∈ B', y ∈ normalizer (X : Set A) ∧ y ∈ normalizer (pCoreOf 2 P : Set A) ∧
      ∀ d ∈ D, y * d = d * y := by
  have hbX : b ∉ X := yd_not_mem_X h hb3 hbK hbx
  have hcard : Nat.card ↥B' = 9 := yd_card_B h hb hb3 hbX hB'le hB'3 hB'i
  haveI : IsMulCommutative ↥B' :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
  have hcomm : ∀ y ∈ B', ∀ d ∈ B', y * d = d * y := fun y hy d hd =>
    congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥B') ⟨d, hd⟩)
  have hXb : X ⊔ zpowers b ≤ normalizer (X : Set A) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hb)
  obtain ⟨d₀, hd₀D, -, hd₀3⟩ := h.D_cyclic hDP hD3 hDi
  intro y hy
  refine ⟨hXb (hB'le hy), ?_, fun d hd => hcomm y hy d (hDB' hd)⟩
  exact h.normalizes_S_of_comm hb hbK (hDP hd₀D) hd₀3 (hB'le hy) (hcomm y hy d₀ (hDB' hd₀D))

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
