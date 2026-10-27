module

public import CFSG.GH74.GLS.C3.Layer1.Back114Defs
public import CFSG.GH74.GLS.C3.Layer1.BackAuxCI

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_pPrimeCoreOf_of_normal {H A : Subgroup G} (hAH : A ≤ H)
    (hn : ∀ g ∈ H, ∀ y ∈ A, g * y * g⁻¹ ∈ A) (hodd : Odd (Nat.card A)) :
    A ≤ pPrimeCoreOf 2 H := by
  have hAn : (A.subgroupOf H).Normal := ⟨fun y hy g => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact hn g g.2 y hy⟩
  have hcop : Nat.Coprime 2 (Nat.card (A.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  intro y hy
  have hmem : (⟨y, hAH hy⟩ : ↥H) ∈ A.subgroupOf H := hy
  have hle : A.subgroupOf H ≤ pPrimeCore 2 ↥H := le_sSup ⟨hAn, hcop⟩
  exact ⟨⟨y, hAH hy⟩, hle hmem, rfl⟩

theorem odd_orderOf_of_mem_pPrimeCoreOf {H : Subgroup G} {u : G} (hu : u ∈ pPrimeCoreOf 2 H) :
    Odd (orderOf u) :=
  Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd H) (Subgroup.orderOf_dvd_natCard _ hu)

omit [Finite G] in
theorem card_map_conj (H : Subgroup G) (a : G) :
    Nat.card ↥(H.map (MulAut.conj a).toMonoidHom) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
    (fun _ _ hxy => (MulAut.conj a).injective hxy)

end Core

section Burnside

theorem exists_normal_two_complement_isComplement {H : Type} [Group H] [Finite H] {x : H}
    (hx : orderOf x = 2) (hxc : ∀ h : H, h * x = x * h) {P : Subgroup H}
    (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hcard : Nat.card P = 4) (hxP : x ∈ P) :
    ∃ N : Subgroup H, N.Normal ∧ Odd (Nat.card N) ∧
      (∀ g : H, Odd (orderOf g) → g ∈ N) ∧ IsComplement' N P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 H := hP.toSylow hPidx
  have hS : (S : Subgroup H) = P := hP.toSylow_coe hPidx
  have hSset : (S : Set H) = (P : Set H) := congrArg (SetLike.coe : Subgroup H → Set H) hS
  have hnorm : normalizer (S : Set H) ≤ centralizer (S : Set H) := by
    rw [hSset]
    exact C3.Layer1.Back.normalizer_le_centralizer_of_central_involution hx hxc hPidx hcard hxP
  refine ⟨(MonoidHom.transferSylow S hnorm).ker, MonoidHom.normal_ker _, ?_, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (by
      have := MonoidHom.not_dvd_card_ker_transferSylow S hnorm
      omega)
  · intro g hg
    rw [MonoidHom.mem_ker]
    set t := MonoidHom.transferSylow S hnorm g with ht
    have hdvd : orderOf t ∣ orderOf g := orderOf_map_dvd _ g
    have hoddt : Odd (orderOf t) := Odd.of_dvd_nat hg hdvd
    have hpg : IsPGroup 2 ↥S := S.isPGroup'
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hpg) t
    have hk0 : k = 0 := by
      by_contra hne
      rw [hk] at hoddt
      exact (Nat.not_even_iff_odd.2 hoddt) (Nat.even_pow.2 ⟨even_two, hne⟩)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  · have h := MonoidHom.ker_transferSylow_isComplement' S hnorm
    exact hS ▸ h

theorem exists_normal_two_complement {H : Type} [Group H] [Finite H] {x : H} (hx : orderOf x = 2)
    (hxc : ∀ h : H, h * x = x * h) {P : Subgroup H} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hcard : Nat.card P = 4) (hxP : x ∈ P) :
    ∃ N : Subgroup H, N.Normal ∧ Odd (Nat.card N) ∧ ∀ g : H, Odd (orderOf g) → g ∈ N := by
  obtain ⟨N, hNn, hNodd, hNall, -⟩ :=
    exists_normal_two_complement_isComplement hx hxc hP hPidx hcard hxP
  exact ⟨N, hNn, hNodd, hNall⟩

end Burnside

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfigW

omit [Finite G] in
theorem W_le_C : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ centralizer ({x} : Set G) :=
  TwoThin.pPrimeCoreOf_le _

omit [Finite G] in
theorem W_normal {c w : G} (hc : c ∈ centralizer ({x} : Set G))
    (hw : w ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G))) :
    c * w * c⁻¹ ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
  TwoThin.pPrimeCoreOf_normalized _ hc hw

theorem W_centralizes_K (h : IsAConfigW n x K T Q S a) {w k : G}
    (hw : w ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G))) (hk : k ∈ K) : k * w = w * k := by
  have hKC : K ≤ centralizer ({x} : Set G) := h.K_le_C
  have hcomp : CFSG.IsComponent (K.subgroupOf (centralizer ({x} : Set G))) := h.terminal.2.1.2
  have hNn : ((pPrimeCoreOf 2 (centralizer ({x} : Set G))).subgroupOf
      (centralizer ({x} : Set G))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := TwoThin.pPrimeCoreOf_normalized (centralizer ({x} : Set G)) g.2 hn
    simpa using this⟩
  rcases CFSG.LocalCores.component_normal_subgroup hcomp hNn with hle | hcomm
  · exfalso
    have hKW : K ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
      intro k' hk'
      have : (⟨k', hKC hk'⟩ : ↥(centralizer ({x} : Set G))) ∈
          K.subgroupOf (centralizer ({x} : Set G)) := hk'
      exact hle this
    have h1 : Nat.card ↥K ∣ Nat.card ↥(pPrimeCoreOf 2 (centralizer ({x} : Set G))) :=
      Subgroup.card_dvd_of_le hKW
    have h2 : 2 ∣ Nat.card ↥(pPrimeCoreOf 2 (centralizer ({x} : Set G))) :=
      (h.terminal.2.2.1).trans h1
    exact (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd (centralizer ({x} : Set G))))
      (even_iff_two_dvd.2 h2)
  · have hmem : ⁅(⟨k, hKC hk⟩ : ↥(centralizer ({x} : Set G))),
        (⟨w, W_le_C hw⟩ : ↥(centralizer ({x} : Set G)))⁆ ∈
        ⁅K.subgroupOf (centralizer ({x} : Set G)),
          (pPrimeCoreOf 2 (centralizer ({x} : Set G))).subgroupOf (centralizer ({x} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.2 hk)
        (Subgroup.mem_subgroupOf.2 hw)
    rw [hcomm, Subgroup.mem_bot] at hmem
    have h2 := commutatorElement_eq_one_iff_mul_comm.1 hmem
    exact congrArg Subtype.val h2

theorem W_le_CxK (h : IsAConfigW n x K T Q S a) :
    pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ CxK x K := by
  intro w hw
  refine ⟨W_le_C hw, C3.Layer1.Back.mem_centralizerSection_of_centralizes
    (fun k hk => (h.W_centralizes_K hw hk).symm) (TwoThin.pPrimeCoreOf_le K)⟩

theorem CxK_normal (h : IsAConfigW n x K T Q S a) {c y : G} (hc : c ∈ centralizer ({x} : Set G))
    (hy : y ∈ CxK x K) : c * y * c⁻¹ ∈ CxK x K := by
  obtain ⟨hyC, hyN, hyO, hyk⟩ := hy
  have hnormK : ∀ m ∈ centralizer ({x} : Set G), ∀ l ∈ K, m * l * m⁻¹ ∈ K := h.normalInC
  have hcyc : c * y * c⁻¹ ∈ centralizer ({x} : Set G) :=
    mul_mem (mul_mem hc hyC) (inv_mem hc)
  refine ⟨hcyc, ?_, ?_, fun k hk => ?_⟩
  · exact mul_mem (mul_mem (C3.Layer1.U1a.mem_normalizer_of_norm hnormK hc) hyN)
      (inv_mem (C3.Layer1.U1a.mem_normalizer_of_norm hnormK hc))
  · exact mul_mem (mul_mem (C3.Layer1.U1a.mem_normalizer_pPrimeCoreOf hnormK hc) hyO)
      (inv_mem (C3.Layer1.U1a.mem_normalizer_pPrimeCoreOf hnormK hc))
  · have hk' : c⁻¹ * k * c ∈ K := by
      have := hnormK c⁻¹ (inv_mem hc) k hk
      simpa using this
    have h1 := hyk _ hk'
    have h2 := C3.Layer1.U1a.pPrimeCoreOf_norm hnormK hc h1
    have h3 : ⁅k, c * y * c⁻¹⁆ = c * ⁅c⁻¹ * k * c, y⁆ * c⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]
    exact h2

theorem odd_mem_W (h : IsAConfigW n x K T Q S a) {u : G} (hu : u ∈ CxK x K)
    (hodd : Odd (orderOf u)) : u ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set X : Subgroup G := CxK x K with hX
  have hXC : X ≤ C := CxK_le_C
  have hQX : Q ≤ X := h.Q_le_CxK
  let x' : ↥X := ⟨x, h.x_mem_CxK⟩
  have hx' : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact h.x_order
  have hxc : ∀ g : ↥X, g * x' = x' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (hXC g.2))
  have hP : IsPGroup 2 (Q.subgroupOf X) := h.sylowQ.isPGroup.comap_subtype
  have hPidx : ¬ 2 ∣ (Q.subgroupOf X).index := (isSylowOf_iff.1 h.sylowQ).2.2
  have hPcard : Nat.card ↥(Q.subgroupOf X) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]; exact h.card_Q
  have hx'P : x' ∈ Q.subgroupOf X := h.x_mem_Q
  obtain ⟨N, hNn, hNodd, hNall⟩ := exists_normal_two_complement hx' hxc hP hPidx hPcard hx'P
  set N₂ : Subgroup G := N.map X.subtype with hN₂
  have hN₂X : N₂ ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hN₂card : Odd (Nat.card ↥N₂) := by
    rw [hN₂, Subgroup.card_map_of_injective X.subtype_injective]
    exact hNodd
  have hN₂mem : ∀ y ∈ N₂, Odd (orderOf y) := by
    intro y hy
    exact Odd.of_dvd_nat hN₂card (Subgroup.orderOf_dvd_natCard _ hy)
  have hN₂norm : ∀ c ∈ C, ∀ y ∈ N₂, c * y * c⁻¹ ∈ N₂ := by
    intro c hc y hy
    have hyX : y ∈ X := hN₂X hy
    have hcy : c * y * c⁻¹ ∈ X := h.CxK_normal hc hyX
    have hord : Odd (orderOf (c * y * c⁻¹)) := by
      have : orderOf (c * y * c⁻¹) = orderOf y := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective y
        simpa [MulAut.conj_apply] using this
      rw [this]; exact hN₂mem y hy
    have hmem : (⟨c * y * c⁻¹, hcy⟩ : ↥X) ∈ N := by
      apply hNall
      rw [Subgroup.orderOf_mk]
      exact hord
    exact ⟨⟨c * y * c⁻¹, hcy⟩, hmem, rfl⟩
  have hN₂W : N₂ ≤ pPrimeCoreOf 2 C := le_pPrimeCoreOf_of_normal (hN₂X.trans hXC) hN₂norm hN₂card
  have huN : (⟨u, hu⟩ : ↥X) ∈ N := by
    apply hNall
    rw [Subgroup.orderOf_mk]
    exact hodd
  exact hN₂W ⟨⟨u, hu⟩, huN, rfl⟩

end IsAConfigW

end Config

end CFSG.GH74.GLS
