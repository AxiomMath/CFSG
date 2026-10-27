module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open Subgroup
open scoped commutatorElement

theorem s3_orderOf_dvd_card_of_mem {G : Type} [Group G] (S : Subgroup G) {q : G} (hq : q ∈ S) :
    orderOf q ∣ Nat.card S := by
  rw [← Subgroup.orderOf_mk q hq]
  exact orderOf_dvd_natCard _

theorem s3_card_map_of_inj {X Y : Type} [Group X] [Group Y] (π : X →* Y) (B : Subgroup X)
    (hinj : ∀ b ∈ B, π b = 1 → b = 1) : Nat.card (B.map π) = Nat.card B := by
  have hψ : Function.Injective (π.comp B.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x.1 x.2 hx)
  have h1 := Subgroup.card_map_of_injective (K := (⊤ : Subgroup B)) hψ
  rw [Subgroup.card_top] at h1
  have h2 : (⊤ : Subgroup B).map (π.comp B.subtype) = B.map π := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [h2] at h1
  exact h1

theorem s3_dvd_card_of_map_eq {X Y : Type} [Group X] [Group Y] (π : X →* Y) (H : Subgroup X)
    (T : Subgroup Y) (hHT : H.map π = T) (hT27 : Nat.card T = 27) : 3 ^ 3 ∣ Nat.card H := by
  have hfT : (π.comp H.subtype).range = T := by
    rw [← hHT]
    ext y
    simp [Subgroup.mem_map]
  have h1 := Subgroup.card_mul_index (π.comp H.subtype).ker
  have h2 := Subgroup.index_ker (π.comp H.subtype)
  rw [hfT, hT27] at h2
  rw [← h1, h2]
  exact Dvd.dvd.mul_left (by norm_num) _

theorem s3_comm_of_inj {X Y : Type} [Group X] [Group Y] (π : X →* Y) (B : Subgroup X)
    (T : Subgroup Y) (hBT : B.map π = T) (hinj : ∀ b ∈ B, π b = 1 → b = 1)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hT3 : ∀ t ∈ T, t ^ 3 = 1) :
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ ∀ b ∈ B, b ^ 3 = 1 := by
  have hBT' : ∀ a ∈ B, π a ∈ T := by
    intro a ha
    rw [← hBT]
    exact Subgroup.mem_map_of_mem π ha
  refine ⟨fun a ha b hb => ?_, fun b hb => ?_⟩
  · have hu : a * b * (b * a)⁻¹ ∈ B := B.mul_mem (B.mul_mem ha hb) (B.inv_mem (B.mul_mem hb ha))
    have hab := hTab _ (hBT' a ha) _ (hBT' b hb)
    have hπu : π (a * b * (b * a)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj _ hu hπu)
  · exact hinj _ (B.pow_mem hb 3) (by rw [map_pow]; exact hT3 _ (hBT' b hb))

theorem exists_sylow_three_lift {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (J : Subgroup X) (hker : ¬ 3 ∣ Nat.card π.ker) (T : Subgroup Y) (hT : T ≤ J.map π)
    (hT27 : Nat.card T = 27) (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hT3 : ∀ t ∈ T, t ^ 3 = 1) :
    ∃ B : Subgroup X, B ≤ J ∧ Nat.card B = 27 ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      (∀ b ∈ B, b ^ 3 = 1) ∧ B.map π = T ∧ ∀ b ∈ B, π b = 1 → b = 1 := by
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup X, H = J ⊓ T.comap π := ⟨_, rfl⟩
  have hmemH : ∀ x : X, x ∈ H ↔ x ∈ J ∧ π x ∈ T := by
    intro x
    rw [hHdef, Subgroup.mem_inf, Subgroup.mem_comap]
  have hHT : H.map π = T := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, hHdef]
      exact inf_le_right
    · intro t ht
      obtain ⟨j, hjJ, hjt⟩ := Subgroup.mem_map.mp (hT ht)
      exact Subgroup.mem_map.mpr ⟨j, (hmemH j).mpr ⟨hjJ, by rw [hjt]; exact ht⟩, hjt⟩
  have hHJ : H ≤ J := fun x hx => ((hmemH x).mp hx).1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ :=
    Sylow.exists_subgroup_card_pow_prime 3 (s3_dvd_card_of_map_eq π H T hHT hT27)
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup X, B = P.map H.subtype := ⟨_, rfl⟩
  have hBcard : Nat.card B = 3 ^ 3 := by
    rw [hBdef, Subgroup.card_map_of_injective H.subtype_injective, hP]
  have hBH : B ≤ H := by
    rw [hBdef]
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  have hinj : ∀ b ∈ B, π b = 1 → b = 1 := by
    intro b hb hπb
    have h1 : orderOf b ∣ 3 ^ 3 := by
      have h := s3_orderOf_dvd_card_of_mem B hb
      rwa [hBcard] at h
    have h2 : orderOf b ∣ Nat.card π.ker :=
      s3_orderOf_dvd_card_of_mem π.ker (MonoidHom.mem_ker.mpr hπb)
    have hcop : Nat.Coprime (3 ^ 3) (Nat.card π.ker) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hBT : B.map π = T := by
    haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT27]; norm_num)
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hHT]
      exact Subgroup.map_mono hBH
    · rw [hT27, s3_card_map_of_inj π B hinj, hBcard] <;> norm_num
  obtain ⟨hcomm, hcube⟩ := s3_comm_of_inj π B T hBT hinj hTab hT3
  exact ⟨B, hBH.trans hHJ, hBcard.trans (by norm_num), hcomm, hcube, hBT, hinj⟩

theorem exists_three_element_lift {X Y : Type} [Group X] [Finite X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker) {g : Y} {n : ℕ} (hg : g ^ 3 ^ n = 1) :
    ∃ s : X, π s = g ∧ ∃ m : ℕ, s ^ 3 ^ m = 1 := by
  obtain ⟨s₀, hs₀⟩ := hπ g
  have hmem : s₀ ^ 3 ^ n ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hs₀, hg]
  have hcop3 : Nat.Coprime 3 (orderOf (s₀ ^ 3 ^ n)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (fun h => hker (dvd_trans h (s3_orderOf_dvd_card_of_mem π.ker hmem)))
  have hcop : Nat.Coprime (orderOf (s₀ ^ 3 ^ n)) (3 ^ n) :=
    (Nat.Coprime.pow_left n hcop3).symm
  have hφ : Nat.totient (3 ^ n) ≠ 0 :=
    (Nat.totient_pos.mpr (pow_pos (by norm_num) n)).ne'
  obtain ⟨e, hge, hpow⟩ : ∃ e : ℕ, g ^ e = g ∧ (s₀ ^ 3 ^ n) ^ e = 1 := by
    refine ⟨orderOf (s₀ ^ 3 ^ n) ^ Nat.totient (3 ^ n), ?_, ?_⟩
    · have he1 : orderOf (s₀ ^ 3 ^ n) ^ Nat.totient (3 ^ n) ≡ 1 [MOD 3 ^ n] :=
        Nat.ModEq.pow_totient hcop
      have he2 : orderOf (s₀ ^ 3 ^ n) ^ Nat.totient (3 ^ n) ≡ 1 [MOD orderOf g] :=
        Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hg) he1
      have h3 := pow_eq_pow_iff_modEq.mpr he2
      rwa [pow_one] at h3
    · exact orderOf_dvd_iff_pow_eq_one.mp (dvd_pow_self _ hφ)
  refine ⟨s₀ ^ e, ?_, n, ?_⟩
  · rw [map_pow, hs₀, hge]
  · rw [← pow_mul, mul_comm, pow_mul, hpow]

@[instance_reducible]
def si_conjMDMA {X : Type} [Group X] (A H : Subgroup X)
    (hH : ∀ h ∈ H, ∀ a ∈ A, h * a * h⁻¹ ∈ A) : MulDistribMulAction H A where
  smul h a := ⟨(h : X) * (a : X) * (h : X)⁻¹, hH _ h.2 _ a.2⟩
  one_smul a := Subtype.ext (show ((1 : H) : X) * (a : X) * ((1 : H) : X)⁻¹ = a by simp)
  mul_smul h k a := Subtype.ext (show ((h * k : H) : X) * (a : X) * ((h * k : H) : X)⁻¹ =
    (h : X) * ((k : X) * (a : X) * (k : X)⁻¹) * (h : X)⁻¹ by
      simp only [Subgroup.coe_mul]
      group)
  smul_mul h a b := Subtype.ext (show (h : X) * ((a : X) * (b : X)) * (h : X)⁻¹ =
    ((h : X) * (a : X) * (h : X)⁻¹) * ((h : X) * (b : X) * (h : X)⁻¹) by group)
  smul_one h := Subtype.ext (show (h : X) * ((1 : A) : X) * (h : X)⁻¹ = ((1 : A) : X) by
    simp)

theorem si_sylow_conj {X : Type} [Group X] [Finite X] (A R₁ R₂ : Subgroup X) (q : ℕ)
    (hq : q.Prime) (hR₁A : R₁ ≤ A) (hR₂A : R₂ ≤ A) (hR₁ : IsPGroup q R₁) (hR₂ : IsPGroup q R₂)
    (h₁ : ¬ q ∣ R₁.relIndex A) (h₂ : ¬ q ∣ R₂.relIndex A) :
    ∃ g ∈ A, ∀ y : X, y ∈ R₂ ↔ g * y * g⁻¹ ∈ R₁ := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Finite (Sylow q A) := Sylow.finite_of_finiteIndex (Classical.arbitrary (Sylow q A))
  have hP₁ : IsPGroup q (R₁.subgroupOf A) :=
    hR₁.of_injective (Subgroup.subgroupOfEquivOfLe hR₁A).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hR₁A).injective
  have hP₂ : IsPGroup q (R₂.subgroupOf A) :=
    hR₂.of_injective (Subgroup.subgroupOfEquivOfLe hR₂A).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hR₂A).injective
  let S₁ : Sylow q A := hP₁.toSylow h₁
  let S₂ : Sylow q A := hP₂.toSylow h₂
  have hmem₁ : ∀ w : A, w ∈ S₁ ↔ (w : X) ∈ R₁ := fun w =>
    (IsPGroup.mem_toSylow hP₁ h₁).trans Subgroup.mem_subgroupOf
  have hmem₂ : ∀ w : A, w ∈ S₂ ↔ (w : X) ∈ R₂ := fun w =>
    (IsPGroup.mem_toSylow hP₂ h₂).trans Subgroup.mem_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥A) S₂ S₁
  have fwd : ∀ (h w : A) (P : Sylow q A), w ∈ P → MulAut.conj h w ∈ h • P := by
    intro h w P hw
    show MulAut.conj h w ∈ ((h • P : Sylow q A) : Subgroup A)
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hw
  have bwd : ∀ (h w : A) (P : Sylow q A), w ∈ h • P → (MulAut.conj h)⁻¹ w ∈ P := by
    intro h w P hw
    have hw' : w ∈ ((h • P : Sylow q A) : Subgroup A) := hw
    rw [Sylow.coe_subgroup_smul] at hw'
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hw'
  have hval : ∀ (h w : A), ((MulAut.conj h w : A) : X) = (h : X) * (w : X) * (h : X)⁻¹ := by
    intro h w
    simp [MulAut.conj_apply]
  have hval' : ∀ (h w : A), (((MulAut.conj h)⁻¹ w : A) : X) = (h : X)⁻¹ * (w : X) * (h : X) := by
    intro h w
    simp [MulAut.conj_inv_apply]
  refine ⟨(g : X), g.2, fun y => ?_⟩
  constructor
  · intro hy
    have hyA : y ∈ A := hR₂A hy
    have h1 : (⟨y, hyA⟩ : A) ∈ S₂ := (hmem₂ _).mpr hy
    have h2 : MulAut.conj g ⟨y, hyA⟩ ∈ S₁ := by
      rw [← hg]
      exact fwd g _ S₂ h1
    have h3 := (hmem₁ _).mp h2
    rw [hval] at h3
    exact h3
  · intro hy
    have hyA : y ∈ A := by
      have h1 : (g : X) * y * (g : X)⁻¹ ∈ A := hR₁A hy
      have h2 := A.mul_mem (A.mul_mem (A.inv_mem g.2) h1) g.2
      have e : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) = y := by group
      rwa [e] at h2
    have h1 : (⟨(g : X) * y * (g : X)⁻¹, hR₁A hy⟩ : A) ∈ S₁ := (hmem₁ _).mpr hy
    have h2 : (MulAut.conj g)⁻¹ ⟨(g : X) * y * (g : X)⁻¹, hR₁A hy⟩ ∈ S₂ := by
      rw [← hg] at h1
      exact bwd g _ S₂ h1
    have h3 := (hmem₂ _).mp h2
    have h4 : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) ∈ R₂ := by
      rw [hval'] at h3
      exact h3
    have e : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) = y := by group
    rwa [e] at h4

theorem exists_invariant_sylow_zpowers {X : Type} [Group X] [Finite X] (A : Subgroup X) (s : X)
    (hsA : ∀ a : X, a ∈ A ↔ s * a * s⁻¹ ∈ A) (hs3 : ∃ n : ℕ, s ^ 3 ^ n = 1)
    (h3A : ¬ 3 ∣ Nat.card A) (q : ℕ) (hq : q.Prime) :
    ∃ R : Subgroup X, R ≤ A ∧ IsPGroup q R ∧ ¬ q ∣ R.relIndex A ∧
      s ∈ Subgroup.normalizer (R : Set X) := by
  have hzN : Subgroup.zpowers s ≤ Subgroup.normalizer (A : Set X) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr hsA)
  have hcong : ∀ h ∈ Subgroup.zpowers s, ∀ a ∈ A, h * a * h⁻¹ ∈ A := fun h hh a ha =>
    (Subgroup.mem_normalizer_iff.mp (hzN hh) a).mp ha
  letI := si_conjMDMA A (Subgroup.zpowers s) hcong
  have hval : ∀ (h : Subgroup.zpowers s) (a : A),
      ((h • a : A) : X) = (h : X) * (a : X) * (h : X)⁻¹ := fun _ _ => rfl
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hpgroup : IsPGroup 3 (Subgroup.zpowers s) := by
    obtain ⟨n, hn⟩ := hs3
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hn)
    exact IsPGroup.iff_card.mpr ⟨m, by rw [Nat.card_zpowers, hm]⟩
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
    (G := ↥A) (A := ↥(Subgroup.zpowers s)) 3 q hpgroup h3A
  set R : Subgroup X := (P : Subgroup A).map A.subtype with hR
  have hRA : R ≤ A := Subgroup.map_subtype_le _
  have hRq : IsPGroup q R := P.isPGroup'.map A.subtype
  have hRsub : R.subgroupOf A = (P : Subgroup A) := by
    ext y
    rw [Subgroup.mem_subgroupOf, hR]
    exact Subgroup.mem_map_iff_mem (K := (P : Subgroup A)) (x := y) A.subtype_injective
  refine ⟨R, hRA, hRq, ?_, ?_⟩
  · rw [Subgroup.relIndex, hRsub]
    exact Sylow.not_dvd_index P
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    show x ∈ R ↔ s * x * s⁻¹ ∈ R
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : (y : X) = x := hyx
      refine Subgroup.mem_map.mpr ⟨(⟨s, Subgroup.mem_zpowers s⟩ : Subgroup.zpowers s) • y,
        hP _ y hy, ?_⟩
      show (((⟨s, Subgroup.mem_zpowers s⟩ : Subgroup.zpowers s) • y : A) : X) = s * x * s⁻¹
      rw [hval, ← hyx']
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      have hz' : (z : X) = s * x * s⁻¹ := hzx
      have hxA : x ∈ A := (hsA x).mpr (by rw [← hz']; exact z.2)
      have hw : (⟨s⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers s)⟩ : Subgroup.zpowers s) • z
          = (⟨x, hxA⟩ : A) := by
        apply Subtype.ext
        show s⁻¹ * (z : X) * s⁻¹⁻¹ = x
        rw [hz']
        group
      have hmem := hP ⟨s⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers s)⟩ z hz
      rw [hw] at hmem
      exact Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, hmem, rfl⟩

theorem frattini_argument_subgroup {X : Type} [Group X] [Finite X] (J A R : Subgroup X) (q : ℕ)
    (hq : q.Prime) (hAJ : A ≤ J) (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (hRA : R ≤ A)
    (hRq : IsPGroup q R) (hRsyl : ¬ q ∣ R.relIndex A) :
    ∀ j ∈ J, ∃ a ∈ A, a * j ∈ Subgroup.normalizer (R : Set X) := by
  intro j hj
  have hinj : Function.Injective (MulAut.conj j).toMonoidHom := (MulAut.conj j).injective
  have hfapp : ∀ x : X, (MulAut.conj j).toMonoidHom x = j * x * j⁻¹ := fun x => rfl
  have hAmap : A.map (MulAut.conj j).toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      rw [hfapp]
      exact hAn j hj a ha
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨j⁻¹ * x * j⁻¹⁻¹, hAn j⁻¹ (J.inv_mem hj) x hx, ?_⟩
      rw [hfapp]
      group
  have hR₂A : R.map (MulAut.conj j).toMonoidHom ≤ A := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hfapp]
    exact hAn j hj r (hRA hr)
  have hR₂syl : ¬ q ∣ (R.map (MulAut.conj j).toMonoidHom).relIndex A := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj j).toMonoidHom) R A hinj
    rw [hAmap] at h
    rw [h]
    exact hRsyl
  obtain ⟨g, hgA, hg⟩ := si_sylow_conj A R (R.map (MulAut.conj j).toMonoidHom) q hq hRA hR₂A
    hRq (hRq.map _) hRsyl hR₂syl
  refine ⟨g, hgA, ?_⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  show x ∈ R ↔ g * j * x * (g * j)⁻¹ ∈ R
  have e : g * j * x * (g * j)⁻¹ = g * (MulAut.conj j).toMonoidHom x * g⁻¹ := by
    rw [hfapp]
    group
  rw [e, ← hg ((MulAut.conj j).toMonoidHom x)]
  exact (Subgroup.mem_map_iff_mem hinj).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
