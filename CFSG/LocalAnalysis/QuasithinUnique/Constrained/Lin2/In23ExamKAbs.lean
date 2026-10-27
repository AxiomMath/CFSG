module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBasic
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure ExamAbs (K : Type) [Group K] (A A' P R : Subgroup K) (m : ℕ) : Prop where
  two_le : 2 ≤ m
  A_le_R : A ≤ R
  A'_le_R : A' ≤ R
  R_eq : R = A ⊔ A'
  A_elem : IsElemAbelian 2 A
  A'_elem : IsElemAbelian 2 A'
  card_A : Nat.card A = 2 ^ (3 * m)
  card_A' : Nat.card A' = 2 ^ (3 * m)
  card_R : Nat.card R = 2 ^ (4 * m)
  R_le_P : R ≤ P
  sylowP : IsSylowTwoOf P ⊤
  strong : ∀ i ∈ R, i ^ 2 = 1 → ∀ g : K, g⁻¹ * i * g ∈ P → g⁻¹ * i * g ∈ R
  elem_le : ∀ E : Subgroup K, E ≤ R → IsElemAbelian 2 E → E ≤ A ∨ E ≤ A'
  center_inf_R : ∀ z ∈ Subgroup.center K, z ∈ R → z = 1

section ToAbs

variable {G : Type} [Group G] [Finite G] {K B B' P R : Subgroup G} {m : ℕ}

omit [Finite G] in
theorem blockU_le_of_short {L : Subgroup G} (hL : IsShort2 L) : blockU L ≤ L :=
  (C1.blockU_le_blockQ hL).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)

omit [Finite G] in
theorem isElemAbelian_subgroupOf {H E : Subgroup G} (h : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf h H

omit [Finite G] in
theorem isElemAbelian_map_subtype {H : Subgroup G} {E : Subgroup H} (h : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map H.subtype) := CFSG.Open.IsElemAbelian.map h _

omit [Finite G] in
theorem ExamConfig.toAbs (h : ExamConfig K B B' P R m) :
    ExamAbs ↥K ((blockU B).subgroupOf K) ((blockU B').subgroupOf K) (P.subgroupOf K)
      (R.subgroupOf K) m := by
  have hBK : B ≤ K := h.le_K
  have hB'K : B' ≤ K := h.le_K'
  have hAK : blockU B ≤ K := (blockU_le_of_short h.short).trans hBK
  have hA'K : blockU B' ≤ K := (blockU_le_of_short h.short').trans hB'K
  have hRK : R ≤ K := h.R_le_K
  have hPK : P ≤ K := h.sylowP.1
  have hAR : blockU B ≤ R := h.R_eq ▸ le_sup_left
  have hA'R : blockU B' ≤ R := h.R_eq ▸ le_sup_right
  refine ⟨h.two_le, fun x hx => hAR hx, fun x hx => hA'R hx, ?_,
    isElemAbelian_subgroupOf h.isElemAbelian_blockU,
    isElemAbelian_subgroupOf h.isElemAbelian_blockU', ?_, ?_, ?_, fun x hx => h.R_le_P hx,
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf h.sylowP, ?_, ?_,
    fun z hz hzR => h.center_inf_R z hz hzR⟩
  · rw [h.R_eq, Subgroup.subgroupOf_sup hAK hA'K]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, h.card_U]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'K).toEquiv, h.card_U']
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, h.card_R]
  · intro i hi hi2 g hg
    have hi' : ((i : ↥K) : G) ∈ R := hi
    have hi2' : ((i : ↥K) : G) ^ 2 = 1 := by
      have := congrArg (fun x : ↥K => (x : G)) hi2
      simpa using this
    exact h.strong (i : G) hi' hi2' (g : G) g.2 hg
  · intro E hER hE
    have hE' : IsElemAbelian 2 (E.map K.subtype) := isElemAbelian_map_subtype hE
    have hER' : E.map K.subtype ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hER hx
    rcases h.elem_le _ hER' hE' with hle | hle
    · left
      intro x hx
      exact hle ⟨x, hx, rfl⟩
    · right
      intro x hx
      exact hle ⟨x, hx, rfl⟩

end ToAbs

section Transport

variable {Kg : Type} [Group Kg] [Finite Kg] {A A' P R : Subgroup Kg} {m : ℕ}

theorem card_map_of_inf_ker_eq_bot {Y X : Type} [Group Y] [Group X] (H : Subgroup Y) (f : Y →* X)
    (h : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : H => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : H.map f)) ⟨?_, ?_⟩)
  · intro x y hxy
    have hxy' : f x = f y := congrArg Subtype.val hxy
    have : (x : Y)⁻¹ * y = 1 := h _ (H.mul_mem (H.inv_mem x.2) y.2) (by rw [map_mul, map_inv, hxy',
      inv_mul_cancel])
    apply Subtype.ext
    exact inv_mul_eq_one.mp this
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite Kg] in
theorem isElemAbelian_map' {Y X : Type} [Group Y] [Group X] {E : Subgroup Y} (h : IsElemAbelian 2 E)
    (f : Y →* X) : IsElemAbelian 2 (E.map f) := CFSG.SectionRank.isElemAbelian_map h _

omit [Finite Kg] in
theorem ExamAbs.exists_bar_elem (h : ExamAbs Kg A A' P R m) :
    ∃ Ab : Subgroup (Kg ⧸ Subgroup.center Kg), IsElemAbelian 2 Ab ∧
      Nat.card Ab = 2 ^ (3 * m) := by
  set π := QuotientGroup.mk' (Subgroup.center Kg) with hπ
  refine ⟨A.map π, isElemAbelian_map' h.A_elem π, ?_⟩
  rw [card_map_of_inf_ker_eq_bot A π (fun x hx hπx =>
    h.center_inf_R x ((QuotientGroup.eq_one_iff _).mp hπx) (h.A_le_R hx)), h.card_A]

omit [Finite Kg] in
theorem mem_of_central_two_element [Finite Kg] {z : Kg} (hP : IsSylowTwoOf P ⊤)
    (hz : z ∈ Subgroup.center Kg) {k : ℕ} (hk : z ^ (2 ^ k) = 1) : z ∈ P := by
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    have hx : (x : Kg) = z ^ j := hj.symm
    rw [Subgroup.coe_pow, hx, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk,
      one_zpow]
    rfl
  obtain ⟨S, hS, hzS⟩ := EscapingLocal.exists_isSylowTwoOf_ge (le_top : Subgroup.zpowers z ≤ ⊤) hzp
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS hP
  have h1 : g * z * g⁻¹ ∈ P := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem _ (hzS (Subgroup.mem_zpowers z))
  have h2 : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
  rwa [h2] at h1

theorem ExamAbs.exists_Rprime (h : ExamAbs Kg A A' P R m) {X : Type} [Group X] [Finite X]
    (θ : Kg →* X) (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center Kg)
    (U : Subgroup X) (hU : IsSylowTwoOf U ⊤) :
    ∃ R₀ A₀ : Subgroup X, R₀ ≤ U ∧
      (∀ n ∈ Subgroup.normalizer (U : Set X), ∀ r ∈ R₀, n * r * n⁻¹ ∈ R₀) ∧
      Nat.card R₀ = 2 ^ (4 * m) ∧ ¬ IsElemAbelian 2 R₀ ∧ A₀ ≤ R₀ ∧ IsElemAbelian 2 A₀ ∧
      Nat.card A₀ = 2 ^ (3 * m) ∧
      (∀ r ∈ R₀, r * r = 1 → ∀ g : X, g * r * g⁻¹ ∈ U → g * r * g⁻¹ ∈ R₀) := by
  have hP2 : IsPGroup 2 P := h.sylowP.2.1
  have hPX : IsSylowTwoOf (P.map θ) ⊤ := CFSG.Quasithin.A312.isSylowTwoOf_top_map θ hθ h.sylowP
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hPX hU
  let Θ : Kg →* X := (MulAut.conj g).toMonoidHom.comp θ
  have hΘsurj : Function.Surjective Θ := (MulAut.conj g).surjective.comp hθ
  have hΘP : P.map Θ = U := by
    rw [← hg, Subgroup.map_map]
  have hΘker : ∀ x, Θ x = 1 → θ x = 1 := by
    intro x hx
    have : g * θ x * g⁻¹ = 1 := hx
    simpa using this
  have hkerR : ∀ x ∈ R, Θ x = 1 → x = 1 := fun x hx hΘx =>
    h.center_inf_R x (hker (MonoidHom.mem_ker.mpr (hΘker x hΘx))) hx
  have hRP : ∀ x ∈ R, x ∈ P := fun x hx => h.R_le_P hx
  have hRelem : ∀ x ∈ R, x ∈ A ∨ x ∈ A' → x ^ 2 = 1 := by
    rintro x - (hx | hx)
    · exact h.A_elem.2 x hx
    · exact h.A'_elem.2 x hx
  have hstrong : ∀ x ∈ R, x ^ 2 = 1 → ∀ n : X, n * Θ x * n⁻¹ ∈ U →
      n * Θ x * n⁻¹ ∈ R.map Θ := by
    intro x hxR hx2 n hU'
    obtain ⟨κ, hκ⟩ := hΘsurj n⁻¹
    have hconj : n * Θ x * n⁻¹ = Θ (κ⁻¹ * x * κ) := by
      rw [map_mul, map_mul, map_inv, hκ]; simp
    rw [← hΘP] at hU'
    obtain ⟨p, hp, hpe⟩ := hU'
    rw [hconj] at hpe
    have hz : p⁻¹ * (κ⁻¹ * x * κ) ∈ Subgroup.center Kg := by
      apply hker
      rw [MonoidHom.mem_ker]
      have : Θ (p⁻¹ * (κ⁻¹ * x * κ)) = 1 := by rw [map_mul, map_inv, hpe, inv_mul_cancel]
      exact hΘker _ this
    set z := p⁻¹ * (κ⁻¹ * x * κ) with hzdef
    have hxe : κ⁻¹ * x * κ = p * z := by rw [hzdef]; group
    have hsq : (κ⁻¹ * x * κ) ^ 2 = 1 := by
      rw [sq, show κ⁻¹ * x * κ * (κ⁻¹ * x * κ) = κ⁻¹ * (x * x) * κ by group, ← sq, hx2]
      group
    have hzc : ∀ w : Kg, w * z = z * w := fun w => Subgroup.mem_center_iff.mp hz w
    have hpz : (p * z) ^ 2 = p ^ 2 * z ^ 2 := Commute.mul_pow (show Commute p z from hzc p) 2
    have hpz2 : p ^ 2 * z ^ 2 = 1 := by rw [← hpz, ← hxe]; exact hsq
    have hz2P : z ^ 2 = (p ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hpz2
    obtain ⟨k, hk⟩ := hP2 ⟨(p ^ 2)⁻¹, P.inv_mem (P.pow_mem hp 2)⟩
    have hzk : z ^ (2 ^ (k + 1)) = 1 := by
      have hk' : ((p ^ 2)⁻¹) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      rw [pow_succ', pow_mul, hz2P, hk']
    have hzP : z ∈ P := mem_of_central_two_element h.sylowP hz hzk
    have hpP : κ⁻¹ * x * κ ∈ P := by rw [hxe]; exact P.mul_mem hp hzP
    have hxR' : κ⁻¹ * x * κ ∈ R := h.strong x hxR hx2 κ hpP
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ hxR'
  have hnorm : ∀ n ∈ Subgroup.normalizer (U : Set X), ∀ ρ ∈ R, n * Θ ρ * n⁻¹ ∈ R.map Θ := by
    intro n hn ρ hρ
    have hρ' : ρ ∈ A ⊔ A' := h.R_eq ▸ hρ
    rw [Subgroup.sup_eq_closure] at hρ'
    clear hρ
    induction hρ' using Subgroup.closure_induction with
    | mem x hx =>
      have hxR : x ∈ R := by
        rcases hx with hx | hx
        · exact h.A_le_R hx
        · exact h.A'_le_R hx
      have hx2 : x ^ 2 = 1 := hRelem x hxR (by simpa using hx)
      have hU' : n * Θ x * n⁻¹ ∈ U := by
        have hx' : Θ x ∈ U := by rw [← hΘP]; exact Subgroup.mem_map_of_mem _ (hRP x hxR)
        exact (Subgroup.mem_normalizer_iff.mp hn (Θ x)).mp hx'
      exact hstrong x hxR hx2 n hU'
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : n * Θ (x * y) * n⁻¹ = (n * Θ x * n⁻¹) * (n * Θ y * n⁻¹) := by
        rw [map_mul]; group
      rw [this]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      have : n * Θ x⁻¹ * n⁻¹ = (n * Θ x * n⁻¹)⁻¹ := by
        rw [map_inv]; group
      rw [this]
      exact Subgroup.inv_mem _ ihx
  refine ⟨R.map Θ, A.map Θ, ?_, ?_, ?_, ?_, Subgroup.map_mono h.A_le_R, ?_, ?_, ?_⟩
  · rw [← hΘP]
    exact Subgroup.map_mono h.R_le_P
  · rintro n hn _ ⟨ρ, hρ, rfl⟩
    exact hnorm n hn ρ hρ
  · rw [card_map_of_inf_ker_eq_bot R Θ (fun x hx => hkerR x hx), h.card_R]
  · intro hel
    have hR1 : IsElemAbelian 2 R := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have hab : ((a : Kg) * b * (a : Kg)⁻¹ * (b : Kg)⁻¹) ∈ R :=
          R.mul_mem (R.mul_mem (R.mul_mem a.2 b.2) (R.inv_mem a.2)) (R.inv_mem b.2)
        have hcomm := hel.1.is_comm.comm ⟨Θ a, Subgroup.mem_map_of_mem _ a.2⟩
          ⟨Θ b, Subgroup.mem_map_of_mem _ b.2⟩
        have h2 : Θ a * Θ b = Θ b * Θ a := congrArg Subtype.val hcomm
        have h3 : Θ ((a : Kg) * b * (a : Kg)⁻¹ * (b : Kg)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]; group
        have h4 := hkerR _ hab h3
        apply Subtype.ext
        calc (a : Kg) * b = ((a : Kg) * b * (a : Kg)⁻¹ * (b : Kg)⁻¹) * (b * a) := by group
          _ = b * a := by rw [h4, one_mul]
      · have hx2 : Θ (x ^ 2) = 1 := by
          rw [map_pow]; exact hel.2 _ (Subgroup.mem_map_of_mem _ hx)
        exact hkerR _ (R.pow_mem hx 2) hx2
    rcases h.elem_le R le_rfl hR1 with hle | hle
    · have := Subgroup.card_le_of_le hle
      rw [h.card_R, h.card_A] at this
      have hm := h.two_le
      have : 2 ^ (3 * m) < 2 ^ (4 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    · have := Subgroup.card_le_of_le hle
      rw [h.card_R, h.card_A'] at this
      have hm := h.two_le
      have : 2 ^ (3 * m) < 2 ^ (4 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
  · exact isElemAbelian_map' h.A_elem Θ
  · rw [card_map_of_inf_ker_eq_bot A Θ (fun x hx => hkerR x (h.A_le_R hx)), h.card_A]
  · rintro _ ⟨ρ, hρ, rfl⟩ hr2 g hg
    have hρ2 : ρ ^ 2 = 1 :=
      hkerR (ρ ^ 2) (R.pow_mem hρ 2) (by rw [map_pow, sq]; exact hr2)
    exact hstrong ρ hρ hρ2 g hg

end Transport

end CFSG.QuasithinUnique.Lin2
