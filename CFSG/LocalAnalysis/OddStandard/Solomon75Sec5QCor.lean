module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseZ
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QAlt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QGrp

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

namespace Sec5Data

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem exists_unique_comp (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) :
    ∃ A : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A ∧
      K0 X n (normalizer (Z : Set X)) = A := by
  obtain ⟨A, hA, -⟩ := h.exists_comp
  exact ⟨A, hA, K0_eq_of_sec5Comp_unique h1 hA⟩

theorem Z_eq_zpowers (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) : Z = zpowers z := by
  obtain ⟨A, hA, hKA⟩ := h.exists_unique_comp h1
  have hZA : Z ≤ A := hKA ▸ h.Z_le_K0
  have hAN : A ≤ normalizer (Z : Set X) := hKA ▸ K0_le n _
  have hn : 8 ≤ n := h.maxdeg.1
  let M : AhatModel X n A := AhatModel.ofCover hA.2
  let φ : ↥A →* Perm (Fin n) :=
    M.C.ρ.comp (M.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥A)))
  have hφ : ∀ a : ↥A, φ a = M.C.ρ (M.e (QuotientGroup.mk a)) := fun a => rfl
  let W : Subgroup (Perm (Fin n)) := (Z.subgroupOf A).map φ
  have hW : W = ⊥ := by
    refine eq_bot_of_normal_exp_two (by simp; omega) ?_ ?_ ?_
    · rintro _ ⟨w, -, rfl⟩
      rw [hφ, Perm.mem_alternatingGroup]
      exact M.C.sign_ρ _
    · intro a ha y hy
      obtain ⟨k, hk⟩ := M.C.exists_ρ_eq (Perm.mem_alternatingGroup.1 ha)
      obtain ⟨a₀, rfl⟩ := M.surj_mk k
      obtain ⟨w, hw, rfl⟩ := hy
      refine ⟨a₀ * w * a₀⁻¹, ?_, ?_⟩
      · have hw' : (w : X) ∈ Z := hw
        have := (Subgroup.mem_normalizer_iff.1 (hAN a₀.2) (w : X)).1 hw'
        show ((a₀ * w * a₀⁻¹ : ↥A) : X) ∈ Z
        simpa using this
      · rw [map_mul, map_mul, map_inv, hφ a₀, hk]
    · rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul]
      have : w * w = 1 := Subtype.ext (h.Z_sq_eq_one hw)
      rw [this, map_one]
  have hφ1 : ∀ x ∈ Z, ∀ hx : x ∈ A, M.e (QuotientGroup.mk (⟨x, hx⟩ : ↥A)) ∈ center M.K := by
    intro x hx hxA
    rw [← M.C.ρ_eq_one_iff, ← hφ]
    have : φ ⟨x, hxA⟩ ∈ W := ⟨⟨x, hxA⟩, hx, rfl⟩
    rw [hW] at this
    exact Subgroup.mem_bot.1 this
  have hzc : ∀ k : M.K, M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) * k =
      k * M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) := by
    intro k
    obtain ⟨b, rfl⟩ := M.surj_mk k
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (h.Z_le_center_K0 h.z_mem (hKA.ge b.2))
  have hz1 : M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) ≠ 1 := by
    intro h1'
    have h2 : (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 :=
      M.e.injective (by rw [map_one]; exact h1')
    have h3 : z ∈ oddCoreOf A :=
      mem_oddCoreOf_iff.2 ⟨hZA h.z_mem, (QuotientGroup.eq_one_iff _).1 h2⟩
    have h4 := eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A) h3
      (h.Z_sq_eq_one h.z_mem)
    have := h.orderOf_z
    rw [h4, orderOf_one] at this
    exact absurd this (by norm_num)
  apply le_antisymm
  · intro x hx
    have hxA : x ∈ A := hZA hx
    have hxc := hφ1 x hx hxA
    by_cases hx1 : M.e (QuotientGroup.mk (⟨x, hxA⟩ : ↥A)) = 1
    · have h2 : (QuotientGroup.mk (⟨x, hxA⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 :=
        M.e.injective (by rw [map_one]; exact hx1)
      have h3 : x ∈ oddCoreOf A :=
        mem_oddCoreOf_iff.2 ⟨hxA, (QuotientGroup.eq_one_iff _).1 h2⟩
      rw [eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A) h3 (h.Z_sq_eq_one hx)]
      exact one_mem _
    · have hzc' : M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) ∈ center M.K :=
        Subgroup.mem_center_iff.2 fun k => (hzc k).symm
      have h2 := M.C.center_eq_of_ne_one hxc hzc' hx1 hz1
      have h3 := QuotientGroup.eq.1 (M.e.injective h2)
      have h4 : x⁻¹ * z ∈ oddCoreOf A := by
        rw [mem_oddCoreOf_iff]
        refine ⟨mul_mem (inv_mem hxA) (hZA h.z_mem), ?_⟩
        have : (⟨x, hxA⟩ : ↥A)⁻¹ * ⟨z, hZA h.z_mem⟩ = ⟨x⁻¹ * z, _⟩ := rfl
        rw [← this]
        exact h3
      have h5 : x⁻¹ * z ∈ Z := mul_mem (inv_mem hx) h.z_mem
      have h6 := eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A) h4 (h.Z_sq_eq_one h5)
      have : x = z := inv_mul_eq_one.1 h6
      rw [this]
      exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    exact h.z_mem

theorem exists_sq_eq_z (h : Sec5Data X n z Z S) (h1 : Sec5One X n Z) {s : X}
    (hsN : s ∈ normalizer (Z : Set X)) (hs : s * s = 1) :
    ∃ x ∈ K0 X n (normalizer (Z : Set X)), x * s = s * x ∧ x * x = z := by
  obtain ⟨A, hA, hKA⟩ := h.exists_unique_comp h1
  have hZA : Z ≤ A := hKA ▸ h.Z_le_K0
  have hNA : normalizer (Z : Set X) ≤ normalizer (A : Set X) :=
    hKA ▸ le_normalizer_K0 X n _
  have hn : 8 ≤ n := h.maxdeg.1
  have hsA : s ∈ normalizer (A : Set X) := hNA hsN
  let M : AhatModel X n A := AhatModel.ofCover hA.2
  have hind := M.induces_perm hn s hsA
  have key : ∀ (c : X) (hc : c ∈ normalizer (A : Set X)), c = 1 → M.perm c hc = 1 := by
    rintro c hc rfl
    exact M.perm_one hn
  have hσ2 : M.perm s hsA * M.perm s hsA = 1 := by
    rw [← M.perm_mul hn hsA hsA]
    exact key _ _ hs
  have ht : ∃ t ∈ AhatData.fixSub (M.autOf s hsA), t * t ≠ 1 ∧ t * t ∈ center M.K := by
    by_cases hσ1 : M.perm s hsA = 1
    · have hind1 : M.C.Induces (M.autOf s hsA) 1 := by rw [← hσ1]; exact hind
      have hcomm := hind1.commutator_le_fixSub ⊤ (fun x _ => by simp)
      have htop : (⁅(⊤ : Subgroup M.K), ⊤⁆ : Subgroup M.K) = ⊤ :=
        M.C.hX.1.1.commutator_eq_top
      have hfix : ∀ k : M.K, M.autOf s hsA k = k := fun k => by
        have hk : k ∈ (⁅(⊤ : Subgroup M.K), ⊤⁆ : Subgroup M.K) := by
          rw [htop]; exact Subgroup.mem_top k
        exact hcomm hk
      have hF : 4 ≤ (Finset.univ : Finset (Fin n)).card := by simp; omega
      obtain ⟨a, b, c, d, -, -, -, -, hab, hac, had, hbc, hbd, hcd⟩ := exists_four_distinct _ hF
      have hsign : sign (swap a b * swap c d) = 1 := by
        rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
        decide
      obtain ⟨x, hx⟩ := M.C.exists_ρ_eq hsign
      refine ⟨x, AhatData.mem_fixSub.2 (hfix x), M.C.sq_dbl_ne_one hn hab hac had hbc hbd hcd hx,
        M.C.sq_mem_center ?_⟩
      rw [hx]
      exact dbl_mul_self hab hac had hbc hbd hcd
    · obtain ⟨k, hk⟩ := involution_support_even hσ2
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        rw [hk0', mul_zero, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hk
        exact hσ1 hk
      exact hind.exists_mem_fixSub_sq_ne_one hn hσ2 hk hk1
  obtain ⟨t, htfix, htsq, htc⟩ := ht
  obtain ⟨a₀, rfl⟩ := M.surj_mk t
  have hfa : (a₀ : X)⁻¹ * (s * (a₀ : X) * s⁻¹) ∈ oddCoreOf A := by
    have h2 := AhatData.mem_fixSub.1 htfix
    rw [M.autOf_mk] at h2
    have h3 := QuotientGroup.eq.1 (M.e.injective h2).symm
    rw [mem_oddCoreOf_iff]
    refine ⟨?_, h3⟩
    refine mul_mem (inv_mem a₀.2) ?_
    have := (conjAut hsA a₀).2
    rwa [coe_conjAut] at this
  obtain ⟨p, hp, hfixp⟩ := exists_fixed_mem_coset (odd_card_oddCoreOf A)
    (a := s) (k := 1) (by simpa [sq] using hs) (mem_normalizer_oddCoreOf_of_mem_normalizer hsA)
    hfa
  set x₀ : X := (a₀ : X) * p with hx₀
  have hx₀A : x₀ ∈ A := mul_mem a₀.2 (oddCoreOf_le A hp)
  have hx₀s : x₀ * s = s * x₀ := by
    have : s * x₀ * s⁻¹ = x₀ := hfixp
    calc x₀ * s = (s * x₀ * s⁻¹) * s := by rw [this]
      _ = s * x₀ := by group
  have hex₀ : M.e (QuotientGroup.mk (⟨x₀, hx₀A⟩ : ↥A)) = M.e (QuotientGroup.mk a₀) := by
    congr 1
    rw [QuotientGroup.eq]
    have : (⟨x₀, hx₀A⟩ : ↥A)⁻¹ * a₀ = ⟨p⁻¹, inv_mem (oddCoreOf_le A hp)⟩ := by
      apply Subtype.ext
      simp [hx₀]
    rw [this]
    exact (mem_oddCoreOf_iff.1 (inv_mem hp)).2
  have hzbar : M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) ∈ center M.K := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨b, rfl⟩ := M.surj_mk k
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (h.Z_le_center_K0 h.z_mem (hKA.ge b.2)).symm
  have hzne : M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) ≠ 1 := by
    intro h1'
    have h2 : (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 :=
      M.e.injective (by rw [map_one]; exact h1')
    have h3 : z ∈ oddCoreOf A :=
      mem_oddCoreOf_iff.2 ⟨hZA h.z_mem, (QuotientGroup.eq_one_iff _).1 h2⟩
    have h4 := eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A) h3
      (h.Z_sq_eq_one h.z_mem)
    have := h.orderOf_z
    rw [h4, orderOf_one] at this
    exact absurd this (by norm_num)
  have hsqz : M.e (QuotientGroup.mk (⟨x₀ * x₀, mul_mem hx₀A hx₀A⟩ : ↥A)) =
      M.e (QuotientGroup.mk (⟨z, hZA h.z_mem⟩ : ↥A)) := by
    have e1 : M.e (QuotientGroup.mk (⟨x₀ * x₀, mul_mem hx₀A hx₀A⟩ : ↥A)) =
        M.e (QuotientGroup.mk a₀) * M.e (QuotientGroup.mk a₀) := by
      rw [← hex₀, ← map_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [e1]
    exact M.C.center_eq_of_ne_one htc hzbar htsq hzne
  have hoz : z⁻¹ * (x₀ * x₀) ∈ oddCoreOf A := by
    rw [mem_oddCoreOf_iff]
    refine ⟨mul_mem (inv_mem (hZA h.z_mem)) (mul_mem hx₀A hx₀A), ?_⟩
    have := QuotientGroup.eq.1 (M.e.injective hsqz).symm
    exact this
  set o : X := z⁻¹ * (x₀ * x₀) with ho
  have hxo : x₀ * x₀ = z * o := by rw [ho]; group
  have hzo : z * o = o * z := by
    have : o ∈ A := oddCoreOf_le A hoz
    exact h.Z_le_center_K0 h.z_mem (hKA.ge this)
  have hoodd : Odd (orderOf o) := by
    have h1' : orderOf (⟨o, hoz⟩ : oddCoreOf A) ∣ Nat.card (oddCoreOf A) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1'
    exact Odd.of_dvd_nat (odd_card_oddCoreOf A) h1'
  refine ⟨x₀ ^ orderOf o, ?_, ?_, ?_⟩
  · exact hKA ▸ pow_mem hx₀A _
  · exact ((Commute.pow_left (hx₀s) _)).eq
  · have hz2 : z * z = 1 := h.Z_sq_eq_one h.z_mem
    have hzc : Commute z o := hzo
    calc x₀ ^ orderOf o * x₀ ^ orderOf o = (x₀ * x₀) ^ orderOf o :=
          ((Commute.refl x₀).mul_pow _).symm
      _ = (z * o) ^ orderOf o := by rw [hxo]
      _ = z ^ orderOf o * o ^ orderOf o := hzc.mul_pow _
      _ = z := by
          rw [pow_orderOf_eq_one, mul_one]
          obtain ⟨m, hm⟩ := hoodd
          rw [hm, pow_succ, pow_mul, sq, hz2, one_pow, one_mul]

theorem Z_le_Sec5Syl (h : Sec5Data X n z Z S) : Z ≤ Sec5Syl S := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZN : Z ≤ normalizer (Z : Set X) := Subgroup.le_normalizer
  have hnormal : (Z.subgroupOf (normalizer (Z : Set X))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).2 le_rfl
  have hp : IsPGroup 2 ↥(Z.subgroupOf (normalizer (Z : Set X))) :=
    h.isPGroup_Z.of_equiv (Subgroup.subgroupOfEquivOfLe hZN).symm
  have hle := hp.le_sylow_of_normal S
  have := Subgroup.map_mono (f := (normalizer (Z : Set X)).subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hZN] at this

end Sec5Data

theorem cor56 : Solomon75Cor56 := by
  intro X _ _ n z Z S h h1
  refine ⟨h.Z_eq_zpowers h1, ?_⟩
  have hZ := h.Z_eq_zpowers h1
  have hz2 := h.orderOf_z
  have hNC : normalizer (Z : Set X) = centralizer ({z} : Set X) := by
    rw [hZ]; exact normalizer_zpowers_eq_centralizer hz2
  have hzz : z * z = 1 := h.Z_sq_eq_one h.z_mem
  obtain ⟨s, hsS, hsZ, g, hg⟩ : ∃ s : X, s ∈ Sec5Syl S ∧ s ∉ Z ∧ ∃ g : X, g⁻¹ * s * g ∈ Z := by
    by_contra hcon
    push Not at hcon
    apply h.l52.e
    ext x
    constructor
    · rintro ⟨hxS, g', hg'⟩
      by_contra hxZ
      exact hcon x hxS hxZ g' hg'
    · exact fun hx => ⟨h.Z_le_Sec5Syl hx, 1, by simpa using hx⟩
  have hsN : s ∈ centralizer ({z} : Set X) := by
    rw [← hNC]
    exact Subgroup.map_subtype_le _ hsS
  have hs1 : s ≠ 1 := fun h1' => hsZ (h1' ▸ Z.one_mem)
  have hgz : g⁻¹ * s * g = z := by
    rw [hZ] at hg
    rcases (mem_zpowers_iff_of_orderOf_two hz2).1 hg with h2 | h2
    · exact absurd (by simpa [mul_assoc] using congrArg (fun w => g * w * g⁻¹) h2) hs1
    · exact h2
  have hs2 : s * s = 1 := by
    have : g⁻¹ * (s * s) * g = 1 := by
      calc g⁻¹ * (s * s) * g = (g⁻¹ * s * g) * (g⁻¹ * s * g) := by group
        _ = 1 := by rw [hgz]; exact hzz
    simpa [mul_assoc] using congrArg (fun w => g * w * g⁻¹) this
  have hsN' : s ∈ normalizer (Z : Set X) := by rw [hNC]; exact hsN
  obtain ⟨x, -, hxs, hxx⟩ := h.exists_sq_eq_z h1 hsN' hs2
  set y : X := g⁻¹ * x * g with hy
  have hyz : y * z = z * y := by
    calc y * z = (g⁻¹ * x * g) * (g⁻¹ * s * g) := by rw [hy, hgz]
      _ = g⁻¹ * (x * s) * g := by group
      _ = g⁻¹ * (s * x) * g := by rw [hxs]
      _ = (g⁻¹ * s * g) * (g⁻¹ * x * g) := by group
      _ = z * y := by rw [hgz, hy]
  have hyN : y ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hyz
  have hyN' : y ∈ normalizer (Z : Set X) := by rw [hNC]; exact hyN
  have hyy : y * y = g⁻¹ * z * g := by
    rw [hy]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = g⁻¹ * z * g := by rw [hxx]
  have hy4 : y ^ (2 ^ 2) = 1 := by
    have h4 : y ^ (2 ^ 2) = (y * y) * (y * y) := by
      rw [show 2 ^ 2 = 4 from rfl]; simp [pow_succ, mul_assoc]
    rw [h4, hyy]
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz]; group
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow_of_pow (G := ↥(normalizer (Z : Set X))) (S : Sylow 2 _)
    (y := ⟨y, hyN'⟩) (j := 2) (Subtype.ext (by simpa using hy4))
  have hx₁S : (c : X) * y * (c : X)⁻¹ ∈ Sec5Syl S :=
    Subgroup.mem_map.2 ⟨c * ⟨y, hyN'⟩ * c⁻¹, hc, by simp⟩
  have hcC : (c : X) ∈ centralizer ({z} : Set X) := by rw [← hNC]; exact c.2
  have hs₁ : ((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹) =
      (g * (c : X)⁻¹)⁻¹ * z * (g * (c : X)⁻¹) := by
    calc ((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹) = (c : X) * (y * y) * (c : X)⁻¹ := by
          group
      _ = (g * (c : X)⁻¹)⁻¹ * z * (g * (c : X)⁻¹) := by rw [hyy]; group
  have hw2 : (((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹)) *
      (((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹)) = 1 := by
    rw [hs₁]
    calc (g * (c : X)⁻¹)⁻¹ * z * (g * (c : X)⁻¹) * ((g * (c : X)⁻¹)⁻¹ * z * (g * (c : X)⁻¹)) =
        (g * (c : X)⁻¹)⁻¹ * (z * z) * (g * (c : X)⁻¹) := by group
      _ = 1 := by rw [hzz]; group
  have hw1 : ((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹) ≠ 1 := by
    intro h1'
    rw [hs₁] at h1'
    have : z = 1 := by
      have := congrArg (fun w => (g * (c : X)⁻¹) * w * (g * (c : X)⁻¹)⁻¹) h1'
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹), (c : X) * y * (c : X)⁻¹,
    mul_mem hx₁S hx₁S, hx₁S, ?_, ?_, ⟨g * (c : X)⁻¹, hs₁.symm⟩, rfl⟩
  · exact orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  · intro hmem
    have hmem' : ((c : X) * y * (c : X)⁻¹) * ((c : X) * y * (c : X)⁻¹) ∈ zpowers z := hZ ▸ hmem
    rcases (mem_zpowers_iff_of_orderOf_two hz2).1 hmem' with h2 | h2
    · exact hw1 h2
    · rw [hs₁] at h2
      have hg'z : (g * (c : X)⁻¹) * z = z * (g * (c : X)⁻¹) := by
        have : z * (g * (c : X)⁻¹) =
            (g * (c : X)⁻¹) * ((g * (c : X)⁻¹)⁻¹ * z * (g * (c : X)⁻¹)) := by group
        rw [this, h2]
      have hcz : (c : X) * z = z * (c : X) := Subgroup.mem_centralizer_singleton_iff.1 hcC
      have hgz' : g * z = z * g := by
        calc g * z = (g * (c : X)⁻¹) * ((c : X) * z) := by group
          _ = (g * (c : X)⁻¹) * (z * (c : X)) := by rw [hcz]
          _ = ((g * (c : X)⁻¹) * z) * (c : X) := by group
          _ = (z * (g * (c : X)⁻¹)) * (c : X) := by rw [hg'z]
          _ = z * g := by group
      apply hsZ
      have : s = z := by
        calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
          _ = g * z * g⁻¹ := by rw [hgz]
          _ = z := by rw [hgz']; group
      rw [this]
      exact h.z_mem

end CFSG.OddStandard.Solomon75
