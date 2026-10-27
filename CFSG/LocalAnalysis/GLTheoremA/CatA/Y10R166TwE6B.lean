module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F166
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.Quasithin.Background.SmithC27RTypeGen
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open scoped commutatorElement

section PerfectLift

variable {K C : Type} [Group K] [Finite K] [Group C] [Finite C]

theorem lift_perfect_trivialMult (π : K →* C) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {X : Subgroup C} (hXperf : commutator ↥X = ⊤)
    (hXmult : TrivialMultiplierT ↥X) :
    (Subgroup.comap π X = π.ker ⊔ ⁅Subgroup.comap π X, Subgroup.comap π X⁆) ∧
      (⁅⁅Subgroup.comap π X, Subgroup.comap π X⁆,
          ⁅Subgroup.comap π X, Subgroup.comap π X⁆⁆ =
        ⁅Subgroup.comap π X, Subgroup.comap π X⁆) ∧
      Subgroup.map π ⁅Subgroup.comap π X, Subgroup.comap π X⁆ = X ∧
      ⁅Subgroup.comap π X, Subgroup.comap π X⁆ ⊓ π.ker = ⊥ ∧
      Nonempty (↥⁅Subgroup.comap π X, Subgroup.comap π X⁆ ≃* ↥X) := by
  classical
  have hXeq : ⁅X, X⁆ = X :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.mk hXperf)
  set H : Subgroup K := Subgroup.comap π X with hHdef
  set D : Subgroup K := ⁅H, H⁆ with hDdef
  have hkerN : π.ker.Normal := MonoidHom.normal_ker π
  have hmapH : Subgroup.map π H = X := Subgroup.map_comap_eq_self_of_surjective hπ X
  have hmapD : Subgroup.map π D = X := by
    rw [hDdef, Subgroup.map_commutator, hmapH, hXeq]
  have hsup : H = D ⊔ π.ker := by
    rw [← Subgroup.comap_map_eq π D, hmapD, hHdef]
  have hmem : ∀ h ∈ H, ∃ d ∈ D, ∃ z ∈ π.ker, d * z = h := by
    intro h hh
    haveI : π.ker.Normal := hkerN
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hsup ▸ hh)
    exact ⟨d, hd, z, hz, rfl⟩
  have hle : D ≤ ⁅D, D⁆ := by
    conv_lhs => rw [hDdef]
    refine Subgroup.commutator_le.mpr fun h₁ hh₁ h₂ hh₂ => ?_
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hmem h₁ hh₁
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hmem h₂ hh₂
    rw [show d₁ * z₁ = z₁ * d₁ from Subgroup.mem_center_iff.mp (hker hz₁) d₁,
      show d₂ * z₂ = z₂ * d₂ from Subgroup.mem_center_iff.mp (hker hz₂) d₂,
      CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hker hz₁) (hker hz₂)]
    exact Subgroup.commutator_mem_commutator hd₁ hd₂
  have hDD : ⁅D, D⁆ = D := le_antisymm (Subgroup.commutator_le_self D) hle
  have hDperf : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hDD
  let πD : ↥D →* ↥X :=
    (π.comp D.subtype).codRestrict X fun d => by
      have h : π (d : K) ∈ Subgroup.map π D := ⟨(d : K), d.2, rfl⟩
      simpa [hmapD] using h
  have hπD : Function.Surjective πD := by
    intro x
    have hx : (x : C) ∈ Subgroup.map π D := by rw [hmapD]; exact x.2
    obtain ⟨d, hd, hdx⟩ := hx
    exact ⟨⟨d, hd⟩, Subtype.ext hdx⟩
  have hkerD' : πD.ker ≤ Subgroup.center ↥D := by
    intro d hd
    refine Subgroup.mem_center_iff.mpr fun e => Subtype.ext ?_
    have h1 : ((d : ↥D) : K) ∈ π.ker := MonoidHom.mem_ker.mpr (congrArg Subtype.val hd)
    exact Subgroup.mem_center_iff.mp (hker h1) (e : K)
  have hbotD : πD.ker = ⊥ :=
    hXmult ↥D (Group.isPerfect_def.mp hDperf) πD hπD hkerD'
  have hdisj : D ⊓ π.ker = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥D) ∈ πD.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext hx.2
    rw [hbotD, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have hinj : Function.Injective πD := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hbotD
  refine ⟨?_, hDD, hmapD, hdisj, ?_⟩
  · rw [hsup, sup_comm]
  · exact ⟨MulEquiv.ofBijective πD ⟨hinj, hπD⟩⟩

end PerfectLift

section TwoGroupLift

variable {K C : Type} [Group K] [Finite K] [Group C] [Finite C]

theorem lift_twoGroup (π : K →* C) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (hodd : Odd (Nat.card π.ker))
    {Y : Subgroup C} (hY : IsPGroup 2 ↥Y) :
    ∃ S : Subgroup K, S ≤ Subgroup.comap π Y ∧ IsPGroup 2 ↥S ∧
      Subgroup.map π S = Y ∧
      Subgroup.comap π Y = S ⊔ π.ker ∧ S ⊓ π.ker = ⊥ ∧
      Subgroup.comap π Y ≤ Subgroup.normalizer (S : Set K) ∧
      Nonempty (↥S ≃* ↥Y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup K := Subgroup.comap π Y with hHdef
  let φ : ↥H →* ↥Y :=
    (π.comp H.subtype).codRestrict Y fun h => by
      exact h.2
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : C) ∈ Subgroup.map π H := by
      rw [Subgroup.map_comap_eq_self_of_surjective hπ Y]
      exact y.2
    obtain ⟨k, hk, hky⟩ := hy
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hkerφ : φ.ker ≤ Subgroup.center ↥H := by
    intro h hh
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    have h1 : ((h : ↥H) : K) ∈ π.ker :=
      MonoidHom.mem_ker.mpr (congrArg Subtype.val hh)
    exact Subgroup.mem_center_iff.mp (hker h1) (g : K)
  haveI hYnil : Group.IsNilpotent ↥Y := hY.isNilpotent
  haveI hHnil : Group.IsNilpotent ↥H := isNilpotent_of_ker_le_center φ hkerφ
  have hdvd : Nat.card ↥Y ∣ Nat.card ↥H := Subgroup.card_dvd_of_surjective hφ
  obtain ⟨S', hS'card, hS'normal⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (G := ↥H) hdvd
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  have hS'card' : Nat.card ↥S' = 2 ^ a := by rw [hS'card, ha]
  let S : Subgroup K := S'.map H.subtype
  have hSH : S ≤ H := Subgroup.map_subtype_le S'
  have hScoe : S.subgroupOf H = S' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSH]
  have hScard : Nat.card ↥S = 2 ^ a := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hS'card']
  have hS2 : IsPGroup 2 ↥S := IsPGroup.of_card hScard
  have hcop : Nat.Coprime (2 ^ a) (Nat.card π.ker) :=
    (Nat.coprime_two_left.mpr hodd).pow_left a
  have hdisj : S ⊓ π.ker = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hScard]
    exact hcop
  have hkerφ_eq : φ.ker = π.ker.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥π.ker := by
    rw [hkerφ_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
      intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact Y.one_mem)).toEquiv
  have hcardH : Nat.card ↥H = Nat.card ↥Y * Nat.card π.ker := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφ
    rw [hcardker, mul_comm] at h1
    exact h1.symm
  have hkerN : π.ker.Normal := MonoidHom.normal_ker π
  have hkerS : π.ker ≤ Subgroup.normalizer (S : Set K) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hc : z * s * z⁻¹ = s := by
      rw [show z * s = s * z from (Subgroup.mem_center_iff.mp (hker hz) s).symm]
      group
    rw [hc]
  have hsup : H = S ⊔ π.ker := by
    have hle : S ⊔ π.ker ≤ H := sup_le hSH (by
      intro z hz
      rw [hHdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
      exact Y.one_mem)
    have hcard : Nat.card ↥(S ⊔ π.ker) = Nat.card ↥S * Nat.card π.ker :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S π.ker hkerS
        (disjoint_iff.mpr hdisj)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcard, hcardH, hScard, ← ha]
  have hinj : Function.Injective (π.subgroupMap S) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine le_bot_iff.mp ?_
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx1 : ((x : ↥S) : K) ∈ S ⊓ π.ker :=
      ⟨x.2, MonoidHom.mem_ker.mpr (by simpa using congrArg Subtype.val hx)⟩
    rw [hdisj, Subgroup.mem_bot] at hx1
    exact hx1
  have hcardImage : Nat.card ↥(Subgroup.map π S) = Nat.card ↥S :=
    (Nat.card_congr (Equiv.ofBijective (π.subgroupMap S)
      ⟨hinj, MonoidHom.subgroupMap_surjective π S⟩)).symm
  have hmapS : Subgroup.map π S = Y := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      have hsH : s ∈ H := hSH hs
      rw [hHdef, Subgroup.mem_comap] at hsH
      exact hsH
    · rw [hcardImage, hScard, ← ha]
  refine ⟨S, hSH, hS2, hmapS, hsup, hdisj, ?_, ?_⟩
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hSH, hScoe]
    exact hS'normal
  · exact ⟨MulEquiv.ofBijective (π.subgroupMap S)
      ⟨hinj, MonoidHom.subgroupMap_surjective π S⟩ |>.trans (MulEquiv.subgroupCongr hmapS)⟩

end TwoGroupLift

section LiftLayer

variable {K C : Type} [Group K] [Finite K] [Group C] [Finite C]

private def pairCommutatorHom (π : K →* C) (hker : π.ker ≤ Subgroup.center K)
    {ebar fbar : C} {e f : K} (he : π e = ebar) (hf : π f = fbar)
    {Hbar : Subgroup C} (hH : Hbar ≤ Subgroup.centralizer ({ebar, fbar} : Set C)) :
    ↥(Subgroup.comap π Hbar) →* (↥π.ker × ↥π.ker) where
  toFun h :=
    (⟨⁅(h : K), e⁆, by
        rw [MonoidHom.mem_ker, map_commutatorElement, he]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp (hH h.2) ebar (by simp)).symm⟩,
      ⟨⁅(h : K), f⁆, by
        rw [MonoidHom.mem_ker, map_commutatorElement, hf]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp (hH h.2) fbar (by simp)).symm⟩)
  map_one' := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_mul' a b := by
    have hbe : ⁅(b : K), e⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, he]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (hH b.2) ebar (by simp)).symm
    have hbf : ⁅(b : K), f⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, hf]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (hH b.2) fbar (by simp)).symm
    have hae : ⁅(a : K), e⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, he]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (hH a.2) ebar (by simp)).symm
    have haf : ⁅(a : K), f⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, hf]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (hH a.2) fbar (by simp)).symm
    have hce : Commute ⁅(a : K), e⁆ ⁅(b : K), e⁆ :=
      Subgroup.mem_center_iff.mp (hker hbe) ⁅(a : K), e⁆
    have hcf : Commute ⁅(a : K), f⁆ ⁅(b : K), f⁆ :=
      Subgroup.mem_center_iff.mp (hker hbf) ⁅(a : K), f⁆
    apply Prod.ext <;> apply Subtype.ext
    · show ⁅((a : K) * (b : K)), e⁆ = ⁅(a : K), e⁆ * ⁅(b : K), e⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hconj : (a : K) * ⁅(b : K), e⁆ * (a : K)⁻¹ = ⁅(b : K), e⁆ := by
        rw [show (a : K) * ⁅(b : K), e⁆ = ⁅(b : K), e⁆ * (a : K) from
          Subgroup.mem_center_iff.mp (hker hbe) (a : K)]
        group
      rw [hconj, hce.eq.symm]
    · show ⁅((a : K) * (b : K)), f⁆ = ⁅(a : K), f⁆ * ⁅(b : K), f⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hconj : (a : K) * ⁅(b : K), f⁆ * (a : K)⁻¹ = ⁅(b : K), f⁆ := by
        rw [show (a : K) * ⁅(b : K), f⁆ = ⁅(b : K), f⁆ * (a : K) from
          Subgroup.mem_center_iff.mp (hker hbf) (a : K)]
        group
      rw [hconj, hcf.eq.symm]

private theorem pairCommutatorHom_ker (π : K →* C) (hker : π.ker ≤ Subgroup.center K)
    {ebar fbar : C} {e f : K} (he : π e = ebar) (hf : π f = fbar)
    {Hbar : Subgroup C} (hH : Hbar ≤ Subgroup.centralizer ({ebar, fbar} : Set C)) :
    (pairCommutatorHom π hker he hf hH).ker =
      (Subgroup.centralizer ({e, f} : Set K)).subgroupOf (Subgroup.comap π Hbar) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    have h1 : ⁅(x : K), e⁆ = 1 := congrArg (fun z : ↥π.ker × ↥π.ker => ((z.1 : ↥π.ker) : K)) hx
    have h2 : ⁅(x : K), f⁆ = 1 := congrArg (fun z : ↥π.ker × ↥π.ker => ((z.2 : ↥π.ker) : K)) hx
    intro y hy
    rcases (by simpa using hy : y = e ∨ y = f) with rfl | rfl
    · exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    · exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  · intro hx
    have h1 : ⁅(x : K), e⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hx e (by simp)).symm
    have h2 : ⁅(x : K), f⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hx f (by simp)).symm
    apply Prod.ext <;> apply Subtype.ext
    · exact h1
    · exact h2

theorem centralizer_pair_normal_of_le_centralizer (π : K →* C)
    (hker : π.ker ≤ Subgroup.center K) {ebar fbar : C} {e f : K} (he : π e = ebar)
    (hf : π f = fbar) {Hbar : Subgroup C}
    (hH : Hbar ≤ Subgroup.centralizer ({ebar, fbar} : Set C)) :
    ((Subgroup.centralizer ({e, f} : Set K)).subgroupOf (Subgroup.comap π Hbar)).Normal := by
  rw [← pairCommutatorHom_ker π hker he hf hH]
  exact MonoidHom.normal_ker _

theorem quotient_centralizer_pair_isMulCommutative (π : K →* C)
    (hker : π.ker ≤ Subgroup.center K) {ebar fbar : C} {e f : K} (he : π e = ebar)
    (hf : π f = fbar) {Hbar : Subgroup C}
    (hH : Hbar ≤ Subgroup.centralizer ({ebar, fbar} : Set C))
    [hN : ((Subgroup.centralizer ({e, f} : Set K)).subgroupOf
      (Subgroup.comap π Hbar)).Normal] :
    IsMulCommutative (↥(Subgroup.comap π Hbar) ⧸
      (Subgroup.centralizer ({e, f} : Set K)).subgroupOf (Subgroup.comap π Hbar)) := by
  classical
  letI := hN
  let Φ := pairCommutatorHom π hker he hf hH
  haveI hKcomm : IsMulCommutative ↥π.ker :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hker b.2) (a : K))
  haveI hT : IsMulCommutative (↥π.ker × ↥π.ker) :=
    IsMulCommutative.of_comm fun a b =>
      Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2)
  haveI : IsMulCommutative ↥Φ.range :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (mul_comm' (a : ↥π.ker × ↥π.ker) (b : ↥π.ker × ↥π.ker))
  have hker : Φ.ker =
      (Subgroup.centralizer ({e, f} : Set K)).subgroupOf (Subgroup.comap π Hbar) :=
    pairCommutatorHom_ker π hker he hf hH
  haveI : Φ.ker.Normal := MonoidHom.normal_ker Φ
  have hcomm : IsMulCommutative (↥(Subgroup.comap π Hbar) ⧸ Φ.ker) :=
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange Φ).symm inferInstance
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq hker) hcomm


variable {K C : Type} [Group K] [Finite K] [Group C] [Finite C]

theorem lift_layer (π : K →* C) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {ebar fbar : C} {e f : K} (he : π e = ebar)
    (hf : π f = fbar) {Hbar : Subgroup C}
    (hH : Hbar = Subgroup.centralizer ({ebar, fbar} : Set C))
    {Lbar : Subgroup C} (hLsn : IsSubnormal Lbar Hbar) (hLq : CFSG.Open.IsQuasisimple ↥Lbar)
    (h3 : 3 ∣ Nat.card (↥Lbar ⧸ Subgroup.center ↥Lbar)) :
    ∃ D : Subgroup K,
      D = ⁅Subgroup.comap π Lbar, Subgroup.comap π Lbar⁆ ∧
      D ≤ Subgroup.centralizer ({e, f} : Set K) ∧
      IsSubnormal D (Subgroup.centralizer ({e, f} : Set K)) ∧
      CFSG.Open.IsQuasisimple ↥D ∧
      3 ∣ Nat.card (↥D ⧸ Subgroup.center ↥D) ∧
      Subgroup.map π D = Lbar := by
  classical
  have hLH : Lbar ≤ Hbar := hLsn.le
  have hHle : Hbar ≤ Subgroup.centralizer ({ebar, fbar} : Set C) := le_of_eq hH
  have hLperf : ⁅Lbar, Lbar⁆ = Lbar := Subgroup.isPerfect_iff.mp (Group.IsPerfect.mk hLq.1)
  set H : Subgroup K := Subgroup.comap π Lbar with hHdef
  set Hh : Subgroup K := Subgroup.comap π Hbar with hHhdef
  set CK : Subgroup K := Subgroup.centralizer ({e, f} : Set K) with hCKdef
  have hHleHh : H ≤ Hh := by
    rw [hHdef, hHhdef]
    exact Subgroup.comap_mono hLH
  let ψ : ↥H →* ↥Lbar :=
    (π.comp H.subtype).codRestrict Lbar fun h => by
      have h' : (h : K) ∈ Subgroup.comap π Lbar := h.2
      exact h'
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : C) ∈ Subgroup.map π H := by
      rw [hHdef, Subgroup.map_comap_eq_self_of_surjective hπ Lbar]
      exact x.2
    obtain ⟨k, hk, hkx⟩ := hx
    exact ⟨⟨k, hk⟩, Subtype.ext hkx⟩
  have hkerψ : ψ.ker ≤ Subgroup.center ↥H := by
    intro h hh
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    have h1 : ((h : ↥H) : K) ∈ π.ker :=
      MonoidHom.mem_ker.mpr (congrArg Subtype.val hh)
    exact Subgroup.mem_center_iff.mp (hker h1) (g : K)
  set D : Subgroup K := ⁅H, H⁆ with hDdef
  have hDqCF : CFSG.IsQuasisimple ↥(commutator ↥H) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective ψ hψ hkerψ
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hLq)
  have hmapD : Subgroup.map π D = Lbar := by
    rw [hDdef, Subgroup.map_commutator, hHdef,
      Subgroup.map_comap_eq_self_of_surjective hπ Lbar, hLperf]
  have hDmap : Subgroup.map H.subtype (commutator ↥H) = D := by
    rw [Subgroup.map_subtype_commutator, hDdef]
  have hDqCF' : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.equivMapOfInjective (commutator ↥H) H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr hDmap)) hDqCF
  have hDq : CFSG.Open.IsQuasisimple ↥D := CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hDqCF'
  have hDperf : Group.IsPerfect ↥D := hDqCF'.1
  have hDleH : D ≤ H := hDdef ▸ Subgroup.commutator_le_self H
  have hDleHh : D ≤ Hh := hDleH.trans hHleHh
  have hCKleHh : CK ≤ Hh := by
    intro k hk
    rw [hHhdef, Subgroup.mem_comap, hH, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases (by simpa using hy : y = ebar ∨ y = fbar) with rfl | rfl
    · have hke : e * k = k * e := Subgroup.mem_centralizer_iff.mp hk e (by simp)
      simpa [he] using congrArg π hke
    · have hkf : f * k = k * f := Subgroup.mem_centralizer_iff.mp hk f (by simp)
      simpa [hf] using congrArg π hkf
  haveI hN : (CK.subgroupOf Hh).Normal :=
    centralizer_pair_normal_of_le_centralizer π hker he hf hHle
  have hquot : IsMulCommutative (↥Hh ⧸ CK.subgroupOf Hh) :=
    quotient_centralizer_pair_isMulCommutative π hker he hf hHle
  have hcommCK : ∀ a b : ↥Hh, ⁅a, b⁆ ∈ CK.subgroupOf Hh := by
    intro a b
    have h1 : QuotientGroup.mk' (CK.subgroupOf Hh) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hDCK : D ≤ CK := by
    rw [hDdef]
    refine Subgroup.commutator_le.mpr fun d₁ hd₁ d₂ hd₂ => ?_
    exact hcommCK ⟨d₁, hHleHh hd₁⟩ ⟨d₂, hHleHh hd₂⟩
  have hDnormalH : (D.subgroupOf H).Normal := by
    have hDcoe : D.subgroupOf H = commutator ↥H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hDleH, hDmap]
    rw [hDcoe, commutator_def]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hDsnH : IsSubnormal D H :=
    CFSG.Quasithin.A3.subnormal_of_normal hDleH hDnormalH
  have hHsnHh : IsSubnormal H Hh := by
    rw [hHdef, hHhdef]
    exact hLsn.comap π
  have hDsnHh : IsSubnormal D Hh := CFSG.Quasithin.A3.subnormal_trans hDsnH hHsnHh
  have hDsnCK : IsSubnormal D CK := by
    have h := CFSG.Quasithin.A3.subnormal_inf_right hDsnHh hCKleHh
    rwa [inf_eq_left.mpr hDCK] at h
  have hdvd : 3 ∣ Nat.card (↥D ⧸ Subgroup.center ↥D) := by
    let πD : ↥D →* ↥Lbar :=
      (π.comp D.subtype).codRestrict Lbar fun d => by
        have h' : π (d : K) ∈ Subgroup.map π D := ⟨(d : K), d.2, rfl⟩
        simpa [hmapD] using h'
    have hπD : Function.Surjective πD := by
      intro x
      have hx : (x : C) ∈ Subgroup.map π D := by rw [hmapD]; exact x.2
      obtain ⟨d, hd, hdx⟩ := hx
      exact ⟨⟨d, hd⟩, Subtype.ext hdx⟩
    have hkerπD : πD.ker ≤ Subgroup.center ↥D := by
      intro d hd
      refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
      have h1 : ((d : ↥D) : K) ∈ π.ker :=
        MonoidHom.mem_ker.mpr (congrArg Subtype.val hd)
      exact Subgroup.mem_center_iff.mp (hker h1) (g : K)
    haveI : Group.IsPerfect ↥D := hDperf
    have e1 : (↥D ⧸ Subgroup.center ↥D) ≃* (↥Lbar ⧸ Subgroup.center ↥Lbar) :=
      CFSG.Quasithin.SmithC27.quotCenterEquivOfSurjective πD hπD hkerπD
    rw [Nat.card_congr e1.toEquiv]
    exact h3
  exact ⟨D, rfl, hDCK, hDsnCK, hDq, hdvd, hmapD⟩

theorem lift_layer_glaPLayer (π : K →* C) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {ebar fbar : C} {e f z : K} (he : π e = ebar)
    (hf : π f = fbar) (hz : z ∈ π.ker) {Hbar : Subgroup C}
    (hH : Hbar = Subgroup.centralizer ({ebar, fbar} : Set C))
    {Lbar : Subgroup C} (hLsn : IsSubnormal Lbar Hbar) (hLq : CFSG.Open.IsQuasisimple ↥Lbar)
    (h3 : 3 ∣ Nat.card (↥Lbar ⧸ Subgroup.center ↥Lbar)) :
    GLAPLayer 3 (Subgroup.centralizer ({z, e, f} : Set K)) ≠ ⊥ := by
  classical
  obtain ⟨D, -, hDCK, hDsn, hDq, hdvd, -⟩ := lift_layer π hπ hker he hf hH hLsn hLq h3
  have hzK : z ∈ Subgroup.center K := hker hz
  have hset : Subgroup.centralizer ({z, e, f} : Set K) = Subgroup.centralizer ({e, f} : Set K) := by
    ext k
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro h
      intro y hy
      exact h y (by simp [hy])
    · intro h y hy
      have hy' : y = z ∨ y = e ∨ y = f := by simpa using hy
      rcases hy' with hz' | he' | hf'
      · rw [hz']; exact (Subgroup.mem_center_iff.mp hzK k).symm
      · rw [he']; exact h e (by simp)
      · rw [hf']; exact h f (by simp)
  rw [hset]
  exact glaPLayer_ne_bot_of_isSubnormal_quasisimple Nat.prime_three hDsn hDq hdvd


end LiftLayer

end CFSG.LocalAnalysis.GLTheoremA.Y10F
