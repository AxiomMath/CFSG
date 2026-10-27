module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section CentralProduct

variable {X : Type*} [Group X]

theorem comm_comm_eq_one_of_central_comm {a b t : X} (ha : ⁅a, t⁆ ∈ Subgroup.center X)
    (hb : ⁅b, t⁆ ∈ Subgroup.center X) : ⁅⁅a, b⁆, t⁆ = 1 := by
  set c := ⁅a, t⁆ with hc
  set d := ⁅b, t⁆ with hd
  have hcc : ∀ x : X, c * x = x * c := fun x => (Subgroup.mem_center_iff.mp ha x).symm
  have hdc : ∀ x : X, d * x = x * d := fun x => (Subgroup.mem_center_iff.mp hb x).symm
  have E1 : a * t = c * t * a := by
    rw [hc, commutatorElement_def]; group
  have E2 : b * t = d * t * b := by
    rw [hd, commutatorElement_def]; group
  have hci : c⁻¹ ∈ Subgroup.center X := inv_mem ha
  have hdi : d⁻¹ ∈ Subgroup.center X := inv_mem hb
  have E1' : a⁻¹ * t = c⁻¹ * t * a⁻¹ := by
    have : a⁻¹ * (c * t) = t * a⁻¹ := by
      calc a⁻¹ * (c * t) = a⁻¹ * (c * t * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * t) * a⁻¹ := by rw [E1]
        _ = t * a⁻¹ := by group
    have h2 : c * (a⁻¹ * t) = t * a⁻¹ := by rw [← this, ← mul_assoc, ← mul_assoc, hcc a⁻¹]
    calc a⁻¹ * t = c⁻¹ * (c * (a⁻¹ * t)) := by group
      _ = c⁻¹ * (t * a⁻¹) := by rw [h2]
      _ = c⁻¹ * t * a⁻¹ := by group
  have E2' : b⁻¹ * t = d⁻¹ * t * b⁻¹ := by
    have : b⁻¹ * (d * t) = t * b⁻¹ := by
      calc b⁻¹ * (d * t) = b⁻¹ * (d * t * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * t) * b⁻¹ := by rw [E2]
        _ = t * b⁻¹ := by group
    have h2 : d * (b⁻¹ * t) = t * b⁻¹ := by rw [← this, ← mul_assoc, ← mul_assoc, hdc b⁻¹]
    calc b⁻¹ * t = d⁻¹ * (d * (b⁻¹ * t)) := by group
      _ = d⁻¹ * (t * b⁻¹) := by rw [h2]
      _ = d⁻¹ * t * b⁻¹ := by group
  have hmv : ∀ (z : X), z ∈ Subgroup.center X → ∀ p q : X, p * (z * q) = z * (p * q) := by
    intro z hz p q
    rw [← mul_assoc, ← mul_assoc, (Subgroup.mem_center_iff.mp hz p)]
  rw [commutatorElement_eq_one_iff_mul_comm]
  calc ⁅a, b⁆ * t = a * (b * (a⁻¹ * (b⁻¹ * t))) := by rw [commutatorElement_def]; group
    _ = a * (b * (a⁻¹ * (d⁻¹ * (t * b⁻¹)))) := by rw [E2', mul_assoc]
    _ = d⁻¹ * (a * (b * (a⁻¹ * (t * b⁻¹)))) := by
      rw [hmv d⁻¹ hdi a⁻¹ _, hmv d⁻¹ hdi b _, hmv d⁻¹ hdi a _]
    _ = d⁻¹ * (a * (b * ((a⁻¹ * t) * b⁻¹))) := by group
    _ = d⁻¹ * (a * (b * ((c⁻¹ * t * a⁻¹) * b⁻¹))) := by rw [E1']
    _ = d⁻¹ * (a * (b * (c⁻¹ * (t * a⁻¹ * b⁻¹)))) := by group
    _ = d⁻¹ * (c⁻¹ * (a * (b * (t * a⁻¹ * b⁻¹)))) := by
      rw [hmv c⁻¹ hci b _, hmv c⁻¹ hci a _]
    _ = d⁻¹ * (c⁻¹ * (a * ((b * t) * a⁻¹ * b⁻¹))) := by group
    _ = d⁻¹ * (c⁻¹ * (a * ((d * t * b) * a⁻¹ * b⁻¹))) := by rw [E2]
    _ = d⁻¹ * (c⁻¹ * (a * (d * (t * b * a⁻¹ * b⁻¹)))) := by group
    _ = d⁻¹ * (c⁻¹ * (d * (a * (t * b * a⁻¹ * b⁻¹)))) := by rw [hmv d hb a _]
    _ = c⁻¹ * (d⁻¹ * (d * (a * (t * b * a⁻¹ * b⁻¹)))) := by rw [hmv c⁻¹ hci d⁻¹ _]
    _ = c⁻¹ * (a * (t * b * a⁻¹ * b⁻¹)) := by rw [inv_mul_cancel_left]
    _ = c⁻¹ * ((a * t) * (b * a⁻¹ * b⁻¹)) := by group
    _ = c⁻¹ * ((c * t * a) * (b * a⁻¹ * b⁻¹)) := by rw [E1]
    _ = t * ⁅a, b⁆ := by rw [commutatorElement_def]; group

theorem comm_mul_mul_eq_of_commute_pair {y k y' k' : X} (h1 : Commute y k')
    (h2 : Commute y' k) (h3 : Commute y k) (h4 : Commute y' k') :
    ⁅y * k, y' * k'⁆ = ⁅y, y'⁆ * ⁅k, k'⁆ := by
  have c1 : Commute (k * k' * k⁻¹) y⁻¹ :=
    ((h3.symm.inv_right.mul_left h1.symm.inv_right).mul_left h3.symm.inv_inv)
  have c2 : Commute (k * k' * k⁻¹ * k'⁻¹) y'⁻¹ :=
    (((h2.symm.inv_right.mul_left h4.symm.inv_right).mul_left h2.symm.inv_inv).mul_left
      h4.symm.inv_inv)
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  calc y * k * (y' * k') * (y * k)⁻¹ * (y' * k')⁻¹
      = y * (k * y') * k' * k⁻¹ * y⁻¹ * k'⁻¹ * y'⁻¹ := by group
    _ = y * (y' * k) * k' * k⁻¹ * y⁻¹ * k'⁻¹ * y'⁻¹ := by rw [h2.eq.symm]
    _ = y * y' * ((k * k' * k⁻¹) * y⁻¹) * k'⁻¹ * y'⁻¹ := by group
    _ = y * y' * (y⁻¹ * (k * k' * k⁻¹)) * k'⁻¹ * y'⁻¹ := by rw [c1.eq]
    _ = y * y' * y⁻¹ * ((k * k' * k⁻¹ * k'⁻¹) * y'⁻¹) := by group
    _ = y * y' * y⁻¹ * (y'⁻¹ * (k * k' * k⁻¹ * k'⁻¹)) := by rw [c2.eq]
    _ = y * y' * y⁻¹ * y'⁻¹ * (k * k' * k⁻¹ * k'⁻¹) := by group

theorem inf_le_center_of_central_product {K Y : Subgroup X} [K.Normal]
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k) (hsup : Y ⊔ K = ⊤) :
    K ⊓ Y ≤ Subgroup.center X := by
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Y ⊔ K := hsup ▸ Subgroup.mem_top g
  obtain ⟨y, hy, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg
  calc y * k * c = y * (k * c) := mul_assoc _ _ _
    _ = y * (c * k) := by rw [hKY k hk c hc.2]
    _ = (y * c) * k := (mul_assoc _ _ _).symm
    _ = (c * y) * k := by rw [(hKY c hc.1 y hy).symm]
    _ = c * (y * k) := mul_assoc _ _ _

theorem comm_mul_comm_eq_one {y k t : X} (hcomm : y * ⁅k, t⁆ = ⁅k, t⁆ * y)
    (hx : y * k * t = t * (y * k)) : ⁅k, t⁆ * ⁅y, t⁆ = 1 := by
  calc ⁅k, t⁆ * ⁅y, t⁆ = (⁅k, t⁆ * y) * t * y⁻¹ * t⁻¹ := by rw [commutatorElement_def y t]; group
    _ = (y * ⁅k, t⁆) * t * y⁻¹ * t⁻¹ := by rw [← hcomm]
    _ = y * (⁅k, t⁆ * t) * y⁻¹ * t⁻¹ := by group
    _ = y * (k * t * k⁻¹) * y⁻¹ * t⁻¹ := by rw [commutatorElement_def k t]; group
    _ = (y * k) * t * (y * k)⁻¹ * t⁻¹ := by group
    _ = 1 := by rw [hx]; group

theorem central_comm_of_central_product {K Y : Subgroup X} [K.Normal]
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k) (hsup : Y ⊔ K = ⊤) {y k t : X} (hy : y ∈ Y)
    (hk : k ∈ K) (hx : y * k * t = t * (y * k)) :
    ⁅k, t⁆ ∈ Subgroup.center X ∧ ⁅y, t⁆ ∈ Subgroup.center X := by
  have ht : t ∈ Y ⊔ K := hsup ▸ Subgroup.mem_top t
  obtain ⟨y₀, hy₀, k₀, hk₀, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ht
  have hu : ⁅k, k₀⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hk₀) (K.inv_mem hk)) (K.inv_mem hk₀)
  have e1 : ⁅k, y₀ * k₀⁆ = ⁅k, k₀⁆ := by
    have c : y₀ * ⁅k, k₀⁆ = ⁅k, k₀⁆ * y₀ := (hKY _ hu y₀ hy₀).symm
    calc ⁅k, y₀ * k₀⁆ = (k * y₀) * k₀ * k⁻¹ * k₀⁻¹ * y₀⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (y₀ * k) * k₀ * k⁻¹ * k₀⁻¹ * y₀⁻¹ := by rw [hKY k hk y₀ hy₀]
      _ = y₀ * ⁅k, k₀⁆ * y₀⁻¹ := by rw [commutatorElement_def]; group
      _ = ⁅k, k₀⁆ := by rw [c]; group
  have e2 : ⁅y, y₀ * k₀⁆ = ⁅y, y₀⁆ := by
    have hcomm : k₀ * y⁻¹ = y⁻¹ * k₀ := hKY k₀ hk₀ y⁻¹ (Y.inv_mem hy)
    calc ⁅y, y₀ * k₀⁆ = y * y₀ * (k₀ * y⁻¹) * k₀⁻¹ * y₀⁻¹ := by
          rw [commutatorElement_def]; group
      _ = y * y₀ * (y⁻¹ * k₀) * k₀⁻¹ * y₀⁻¹ := by rw [hcomm]
      _ = ⁅y, y₀⁆ := by rw [commutatorElement_def]; group
  have hK : ⁅k, y₀ * k₀⁆ ∈ K := by rw [e1]; exact hu
  have hY : ⁅y, y₀ * k₀⁆ ∈ Y := by
    rw [e2, commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy₀) (Y.inv_mem hy)) (Y.inv_mem hy₀)
  have hprod : ⁅k, y₀ * k₀⁆ * ⁅y, y₀ * k₀⁆ = 1 :=
    comm_mul_comm_eq_one (hKY _ hK y hy).symm hx
  have hinv : ⁅k, y₀ * k₀⁆ = (⁅y, y₀ * k₀⁆)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hKY' : ⁅k, y₀ * k₀⁆ ∈ K ⊓ Y := ⟨hK, hinv ▸ Y.inv_mem hY⟩
  have hc : ⁅k, y₀ * k₀⁆ ∈ Subgroup.center X := inf_le_center_of_central_product hKY hsup hKY'
  refine ⟨hc, ?_⟩
  have : ⁅y, y₀ * k₀⁆ = (⁅k, y₀ * k₀⁆)⁻¹ := by rw [hinv, inv_inv]
  rw [this]
  exact inv_mem hc

theorem commutator_centralizer_le_of_central_product {K Y : Subgroup X} [K.Normal]
    (hKY : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k) (hsup : Y ⊔ K = ⊤) (t : X) :
    ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ ≤
      (Y ⊓ centralizer ({t} : Set X)) ⊔ (K ⊓ centralizer ({t} : Set X)) := by
  rw [Subgroup.commutator_le]
  intro x hx x' hx'
  have hxt : x * t = t * x := by
    have := Subgroup.mem_centralizer_iff.mp hx t (Set.mem_singleton t)
    exact this.symm
  have hxt' : x' * t = t * x' := by
    have := Subgroup.mem_centralizer_iff.mp hx' t (Set.mem_singleton t)
    exact this.symm
  obtain ⟨y, hy, k, hk, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.1 (hsup ▸ Subgroup.mem_top x : x ∈ Y ⊔ K)
  obtain ⟨y', hy', k', hk', rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.1 (hsup ▸ Subgroup.mem_top x' : x' ∈ Y ⊔ K)
  obtain ⟨hkc, hyc⟩ := central_comm_of_central_product hKY hsup hy hk hxt
  obtain ⟨hkc', hyc'⟩ := central_comm_of_central_product hKY hsup hy' hk' hxt'
  rw [comm_mul_mul_eq_of_commute_pair (hKY k' hk' y hy).symm (hKY k hk y' hy').symm
    (hKY k hk y hy).symm (hKY k' hk' y' hy').symm]
  refine Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨?_, ?_⟩) (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hy') (Y.inv_mem hy)) (Y.inv_mem hy')
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp (comm_comm_eq_one_of_central_comm hyc hyc')
  · rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp (comm_comm_eq_one_of_central_comm hkc hkc')

theorem conj_mem_centralizer_of_central_comm {x δ t : X} (hx : ⁅x, t⁆ ∈ Subgroup.center X)
    (hδ : δ ∈ centralizer ({t} : Set X)) : x * δ * x⁻¹ ∈ centralizer ({t} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hδ ⊢
  set z := ⁅x, t⁆ with hz
  have hzc : ∀ g : X, g * z⁻¹ = z⁻¹ * g := fun g => Subgroup.mem_center_iff.mp (inv_mem hx) g
  have e : x * t * x⁻¹ = z * t := by rw [hz, commutatorElement_def]; group
  have e' : t = z⁻¹ * (x * t * x⁻¹) := by rw [e]; group
  calc x * δ * x⁻¹ * t = x * δ * x⁻¹ * (z⁻¹ * (x * t * x⁻¹)) := by rw [← e']
    _ = z⁻¹ * (x * δ * x⁻¹ * (x * t * x⁻¹)) := by
      rw [← mul_assoc, hzc (x * δ * x⁻¹), mul_assoc]
    _ = z⁻¹ * (x * (δ * t) * x⁻¹) := by group
    _ = z⁻¹ * (x * (t * δ) * x⁻¹) := by rw [hδ]
    _ = (z⁻¹ * (x * t * x⁻¹)) * (x * δ * x⁻¹) := by group
    _ = t * (x * δ * x⁻¹) := by rw [← e']

end CentralProduct

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_of_normal_overgroup {A B C : Subgroup G} (hAB : A ≤ B)
    (hBC : B ≤ C) (hA : (A.subgroupOf B).IsSubnormal) (hB : (B.subgroupOf C).Normal) :
    (A.subgroupOf C).IsSubnormal := by
  have hAC : A.subgroupOf C ≤ B.subgroupOf C := Subgroup.subgroupOf_mono C hAB
  refine Subgroup.IsSubnormal.trans hAC ?_ hB.isSubnormal
  let e : ↥(B.subgroupOf C) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBC
  have : (A.subgroupOf C).subgroupOf (B.subgroupOf C) =
      (A.subgroupOf B).comap e.toMonoidHom := by
    ext x
    rfl
  rw [this]
  exact hA.comap _

end Subnormal

section TwoComponents

theorem le_of_le_sup_odd_of_primeResidual {D : Type*} [Group D] [Finite D] {N O L : Subgroup D}
    [N.Normal] (hO : Odd (Nat.card O)) (hL : primeResidual 2 ↥L = ⊤) (h : L ≤ N ⊔ O) :
    L ≤ N := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ x ∈ L, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ N := by
    intro x hx ⟨j, hj⟩
    obtain ⟨n, hn, o, ho, hxno⟩ := Subgroup.mem_sup_of_normal_left.1 (h hx)
    let ρ : D →* D ⧸ N := QuotientGroup.mk' N
    have hρn : ρ n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    have hx1 : ρ x = ρ o := by rw [← hxno, map_mul, hρn, one_mul]
    have h1 : orderOf (ρ x) ∣ 2 ^ j := hj ▸ orderOf_map_dvd ρ x
    have h2 : orderOf (ρ x) ∣ Nat.card O := by
      rw [hx1]
      exact (orderOf_map_dvd ρ o).trans (Subgroup.orderOf_dvd_natCard O ho)
    have hcop : Nat.Coprime (2 ^ j) (Nat.card O) := (Nat.coprime_two_left.2 hO).pow_left j
    have h3 : orderOf (ρ x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)
  have hcl : primeResidual 2 ↥L ≤ N.comap L.subtype := by
    rw [primeResidual_eq_closure, Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    exact hpow x x.2 ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ primeResidual 2 ↥L := by rw [hL]; exact Subgroup.mem_top _
  exact hcl hy'

theorem isPComponent_le_or_le_of_commutator_le {D : Type*} [Group D] [Finite D]
    {N M L : Subgroup D} [N.Normal] [M.Normal] (hD : commutator D ≤ N ⊔ M)
    (hL : IsPComponent 2 L) : L ≤ N ∨ L ≤ M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : primeResidual 2 ↥L = ⊤ := (isPComponent_two_iff.1 hL).2.1
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  set O : Subgroup D := pPrimeCore 2 D with hOdef
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  let π : D →* D ⧸ O := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : π.ker = O := QuotientGroup.ker_mk' O
  have hNn : (N.map π).Normal := Subgroup.Normal.map ‹_› π hπs
  have hMn : (M.map π).Normal := Subgroup.Normal.map ‹_› π hπs
  have key : ∀ (P : Subgroup D) [P.Normal], K ≤ P.map π → L ≤ P := by
    intro P _ hKP
    have h1 : L ≤ (L.map π).comap π := Subgroup.le_comap_map π L
    rw [hLK] at h1
    have h2 : K.comap π ≤ (P.map π).comap π := Subgroup.comap_mono hKP
    rw [Subgroup.comap_map_eq, hker] at h2
    exact le_of_le_sup_odd_of_primeResidual hOodd hgen (h1.trans h2)
  rcases CFSG.LocalCores.component_normal_subgroup hK hNn with hN | hN
  · exact Or.inl (key N hN)
  rcases CFSG.LocalCores.component_normal_subgroup hK hMn with hM | hM
  · exact Or.inr (key M hM)
  exfalso
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hD' : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ : Subgroup D) ≤ N ⊔ M := by
    rw [← _root_.commutator_def]
    exact hD
  have hKle : K ≤ N.map π ⊔ M.map π := by
    calc K = ⁅K, K⁆ := hperf.symm
      _ ≤ ⁅(⊤ : Subgroup (D ⧸ O)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = Subgroup.map π ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ := by
        rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs]
      _ ≤ (N ⊔ M).map π := Subgroup.map_mono hD'
      _ = N.map π ⊔ M.map π := Subgroup.map_sup _ _ _
  have hcomm : ∀ k ∈ K, ∀ y ∈ N.map π ⊔ M.map π, k * y = y * k := by
    intro k hk y hy
    have hle : N.map π ⊔ M.map π ≤ centralizer ({k} : Set (D ⧸ O)) := by
      refine sup_le ?_ ?_
      · intro n hn
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hN hk) n hn
      · intro n hn
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hM hk) n hn
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hbot : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy k (hKle hk)
  rw [hperf] at hbot
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this hbot

end TwoComponents

end CFSG.OddStandard.Solomon75
