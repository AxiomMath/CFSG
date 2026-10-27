module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.GH74.GLS.C3.Layer1.Th2AltInv
public import CFSG.GH74.GLS.C3.Layer1.Th2L84Syl
public import CFSG.GH74.GLS.C3.Layer1.BkL114SE
public import CFSG.GH74.GLS.C3.Layer1.BkSEAbs

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85

@[expose] def B_thm2_p85_alt_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Struct x y K T S M L → Ivk73Alt (imgM M K) (imgM M L) →
      (¬ IsTerminalPair 2 x K → centralizer ({x} : Set G) ≤ M) ∧
      ∀ W : Subgroup G, IsSylowOf 2 W M → T ⊓ M ≤ W → ∀ v ∈ W, orderOf v = 2 →
        (∀ w ∈ W, v * w = w * v) → centralizer ({v} : Set G) ≤ M

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.Th2.P85.Alt

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

section SE

variable {G : Type} [Group G]

theorem mem_of_conj_conj' {N : Subgroup G} {y : G} (hy : centralizer ({y} : Set G) ≤ N) {t : G}
    {c d g : G} (hcN : c ∈ N) (hdN : d ∈ N) (hc : c * y * c⁻¹ = t)
    (hd : d * y * d⁻¹ = g⁻¹ * t * g) : g ∈ N := by
  have hm : d⁻¹ * g⁻¹ * c ∈ centralizer ({y} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc d⁻¹ * g⁻¹ * c * y = (d⁻¹ * g⁻¹ * c * y * c⁻¹ * g * d) * (d⁻¹ * g⁻¹ * c) := by group
      _ = (d⁻¹ * (g⁻¹ * (c * y * c⁻¹) * g) * d) * (d⁻¹ * g⁻¹ * c) := by group
      _ = (d⁻¹ * (g⁻¹ * t * g) * d) * (d⁻¹ * g⁻¹ * c) := by rw [hc]
      _ = (d⁻¹ * (d * y * d⁻¹) * d) * (d⁻¹ * g⁻¹ * c) := by rw [hd]
      _ = y * (d⁻¹ * g⁻¹ * c) := by group
  have h2 := hy hm
  have : g = c * (d⁻¹ * g⁻¹ * c)⁻¹ * d⁻¹ := by group
  rw [this]
  exact N.mul_mem (N.mul_mem hcN (N.inv_mem h2)) (N.inv_mem hdN)

variable [Finite G]

theorem isStronglyEmbedded_of_cent {M : Subgroup G} (hM : M ≠ ⊤) {x v : G} (hxM : x ∈ M)
    (hx2 : orderOf x = 2) (hnc : ¬ IsConj x v)
    (hfus : ∀ t ∈ M, orderOf t = 2 → (∃ c ∈ M, c * x * c⁻¹ = t) ∨ (∃ c ∈ M, c * v * c⁻¹ = t))
    (hCx : centralizer ({x} : Set G) ≤ M) (hCv : centralizer ({v} : Set G) ≤ M) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine C3.Layer1.Bk.isStronglyEmbeddedOrder_of_involutions hM ⟨x, hxM, hx2⟩ ?_
  intro t htM ht2 g hg
  have ht2' : orderOf (g⁻¹ * t * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    simpa [MulAut.conj_apply] using this.trans ht2
  rcases hfus t htM ht2 with ⟨c, hcM, hc⟩ | ⟨c, hcM, hc⟩
  · rcases hfus _ hg ht2' with ⟨d, hdM, hd⟩ | ⟨d, hdM, hd⟩
    · exact mem_of_conj_conj' hCx hcM hdM hc hd
    · exfalso
      refine hnc (isConj_iff.2 ⟨d⁻¹ * g⁻¹ * c, ?_⟩)
      calc d⁻¹ * g⁻¹ * c * x * (d⁻¹ * g⁻¹ * c)⁻¹ = d⁻¹ * (g⁻¹ * (c * x * c⁻¹) * g) * d := by
            group
        _ = d⁻¹ * (g⁻¹ * t * g) * d := by rw [hc]
        _ = d⁻¹ * (d * v * d⁻¹) * d := by rw [hd]
        _ = v := by group
  · rcases hfus _ hg ht2' with ⟨d, hdM, hd⟩ | ⟨d, hdM, hd⟩
    · exfalso
      refine hnc ((isConj_iff.2 ⟨d⁻¹ * g⁻¹ * c, ?_⟩ : IsConj v x).symm)
      calc d⁻¹ * g⁻¹ * c * v * (d⁻¹ * g⁻¹ * c)⁻¹ = d⁻¹ * (g⁻¹ * (c * v * c⁻¹) * g) * d := by
            group
        _ = d⁻¹ * (g⁻¹ * t * g) * d := by rw [hc]
        _ = d⁻¹ * (d * x * d⁻¹) * d := by rw [hd]
        _ = x := by group
    · exact mem_of_conj_conj' hCv hcM hdM hc hd

end SE

section Lift

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem exists_conj_of_barMk_conj {s u : ↥M} (hs : orderOf s = 2) (hu : orderOf u = 2)
    (h : IsConj (barMk ↥M s) (barMk ↥M u)) : ∃ m : ↥M, m * u * m⁻¹ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨cb, hcb⟩ := isConj_iff.1 h
  obtain ⟨c, rfl⟩ := barMk_surjective (Y := ↥M) cb
  have hs'2 : orderOf (c * s * c⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c) s
    simpa [MulAut.conj_apply] using this.trans hs
  have hP : ∀ {t : ↥M}, orderOf t = 2 → IsPGroup 2 ↥(zpowers t) := fun {t} ht =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have hmem : u⁻¹ * (c * s * c⁻¹) ∈ pPrimeCore 2 ↥M := by
    rw [← ker_barMk, MonoidHom.mem_ker]
    have : barMk ↥M (c * s * c⁻¹) = barMk ↥M u := by
      rw [map_mul, map_mul, map_inv]
      exact hcb
    rw [map_mul, map_inv, this, inv_mul_cancel]
  obtain ⟨g, hg⟩ := C3.Layer1.Bk.exists_conj_of_coset (C := ⊤) (W := pPrimeCore 2 ↥M)
    (B₁ := zpowers u) (B₂ := zpowers (c * s * c⁻¹))
    (fun c' _ w hw => Subgroup.Normal.conj_mem inferInstance w hw c') (odd_card_pPrimeCore ↥M)
    (s := u) (u := c * s * c⁻¹) (Subgroup.mem_top u) (mem_zpowers u) (hP hu)
    (mem_zpowers _) (hP hs'2) hmem
  refine ⟨(g * c)⁻¹, ?_⟩
  rw [← hg]
  group

end Lift

section Card

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem card_centralizer_barMk {t : ↥M} (ht : orderOf t = 2) :
    ∃ r : ℕ, Odd r ∧ Nat.card ↥(centralizer ({t} : Set ↥M)) =
      r * Nat.card ↥(centralizer ({barMk ↥M t} : Set (Mb M))) := by
  have hsurj := barMkCentralizer_surjective ht
  have h1 := Subgroup.card_mul_index (barMkCentralizer ht).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top] at h1
  exact ⟨Nat.card (barMkCentralizer ht).ker, odd_card_ker_barMkCentralizer ht, h1.symm⟩

omit [Finite G] in
theorem card_centralizer_of_le {x : G} (hxM : x ∈ M) (hC : centralizer ({x} : Set G) ≤ M) :
    Nat.card ↥(centralizer ({x} : Set G)) =
      Nat.card ↥(centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) := by
  have h : centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M) = (centralizer ({x} : Set G)).subgroupOf M := by
    ext c
    rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [h]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv).symm

theorem not_isConj_of_two_adic {x v : G} (hxM : x ∈ M) (hvM : v ∈ M) (hx2 : orderOf x = 2)
    (hv2 : orderOf v = 2) (hCx : centralizer ({x} : Set G) ≤ M)
    (hCv : centralizer ({v} : Set G) ≤ M) {k : ℕ}
    (hk1 : 2 ^ k ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨v, hvM⟩ : ↥M)} : Set (Mb M))))
    (hk2 : ¬ 2 ^ k ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M)))) :
    ¬ IsConj x v := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hcard : Nat.card ↥(centralizer ({v} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
    have h := Stage1.Thm2.Recip.map_centralizer_singleton_conj x g
    rw [hg] at h
    rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [card_centralizer_of_le hvM hCv, card_centralizer_of_le hxM hCx] at hcard
  obtain ⟨rv, hrv, hv⟩ := card_centralizer_barMk (M := M)
    (show orderOf (⟨v, hvM⟩ : ↥M) = 2 from (Subgroup.orderOf_mk v hvM).trans hv2)
  obtain ⟨rx, hrx, hx⟩ := card_centralizer_barMk (M := M)
    (show orderOf (⟨x, hxM⟩ : ↥M) = 2 from (Subgroup.orderOf_mk x hxM).trans hx2)
  have h2k : 2 ^ k ∣ Nat.card ↥(centralizer ({(⟨v, hvM⟩ : ↥M)} : Set ↥M)) := by
    rw [hv]
    exact hk1.mul_left rv
  rw [hcard, hx] at h2k
  have hcop : Nat.Coprime (2 ^ k) rx := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hrx)
  exact hk2 (hcop.dvd_of_dvd_mul_left h2k)

end Card

end CFSG.GH74.GLS.Th2.P85.Alt

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.TwoThin

theorem b_thm2_p85_alt_of_cent (h : B_thm2_p85_alt_cent) :
    B_thm2_p85_alt := by
  intro G _ _ x y K T S M L hstruct halt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsetup := hstruct.toP85Setup
  have hG := hsetup.hG
  have hchoice := hsetup.choice
  have hKM := hsetup.KM
  have hQ := hsetup.hQ
  have hstd := hchoice.std
  have hMtop : M ≠ ⊤ := hchoice.maximal.1
  have hsimp : IsSimpleGroup G := (isKProperSimple_iff.1 hG.kproper).1
  have hQM : T ⊓ CxK x K ≤ M := hQ.le.trans inf_le_left
  have hxM : x ∈ M := hQM ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  obtain ⟨W, hWsyl, hWle⟩ : ∃ W : Subgroup G, IsSylowOf 2 W M ∧ T ⊓ M ≤ W := by
    have hTp : IsPGroup 2 ↥(T ⊓ M) := hstd.T_pGroup.to_le inf_le_left
    have hAp : IsPGroup 2 ↥((T ⊓ M).subgroupOf M) :=
      hTp.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ M ≤ M)).symm
    obtain ⟨Sy, hASy⟩ := hAp.exists_le_sylow
    refine ⟨(Sy : Subgroup ↥M).map M.subtype, ⟨Sy, rfl⟩, fun t ht => ?_⟩
    exact ⟨⟨t, ht.2⟩, hASy (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  obtain ⟨hCx2, hCvAll⟩ := h G x y K T S M L hstruct halt
  have hCx : centralizer ({x} : Set G) ≤ M := by
    by_cases hterm : IsTerminalPair 2 x K
    · rcases hchoice with hM1 | ⟨ρ, B, hM2⟩
      · have hgam := Th2.CaseI.gammaK_le_normalizer_of_standard hM1.standard hM1.sylowQ
        exact ((C3.Layer1.U1a.centralizer_le_gammaK (Q := T ⊓ CxK x K)
          ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩ hx2).trans hgam).trans hM1.le_M
      · exact absurd hterm hM2.nonterminal
    · exact hCx2 hterm
  have hxW : x ∈ W := hWle ⟨hstd.x_mem_T, hxM⟩
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    omega
  obtain ⟨v, hvW, hv2, hvc⟩ := Th2.L84Syl.exists_involution_mem_center hWsyl.isPGroup hxW hx1
  have hCv := hCvAll W hWsyl hWle v hvW hv2 hvc
  have hvM : v ∈ M := hWsyl.le hvW
  obtain ⟨hLtop, n, hn, ⟨eK⟩, ⟨eL⟩⟩ := halt
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    exact hn
  have hm : n + 4 = 9 ∨ n + 4 = 10 ∨ n + 4 = 11 := by omega
  let e : Mb M ≃* alternatingGroup (Fin (n + 4)) :=
    ((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv).symm.trans eL
  have hxb2 : orderOf (barMk ↥M ⟨x, hxM⟩) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hKC : imgM M K ≤ centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M)) := by
    intro w hw
    obtain ⟨m, hm', rfl⟩ := mem_imgM_iff.1 hw
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hstd.K_le_C hm'))
  have h5 : 5 ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M))) := by
    have h1 : Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ∣ Nat.card ↥(imgM M K) :=
      Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥(imgM M K)))
        (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(imgM M K)))
    have h2 : Nat.card ↥(imgM M K) ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M))) :=
      Subgroup.card_dvd_of_le hKC
    have h3 : Nat.card (alternatingGroup (Fin n)) =
        Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) := (Nat.card_congr eK.toEquiv).symm
    have h4 : 5 ∣ Nat.card (alternatingGroup (Fin n)) := by
      rcases hn' with rfl | rfl | rfl <;>
        (rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide)
    exact h4.trans ((h3 ▸ h1).trans h2)
  have hMM : imgM M M = ⊤ := by
    unfold imgM
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ barMk_surjective
  have hWb := (isSylowOf_imgM_of_le (le_refl M) hWsyl).card_eq
  rw [hMM, Subgroup.card_top] at hWb
  have hvb2 : orderOf (barMk ↥M ⟨v, hvM⟩) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk v hvM).trans hv2)
  have hvcb : ∀ w ∈ imgM M W, w * barMk ↥M ⟨v, hvM⟩ = barMk ↥M ⟨v, hvM⟩ * w := by
    intro w hw
    obtain ⟨m, hm', rfl⟩ := mem_imgM_iff.1 hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc _ hm').symm
  obtain ⟨-, hcls, k, hk1, hk2⟩ := Th2.AltInv.alt_facts hm e hxb2 h5 hWb hvb2 hvcb
  have hfus : ∀ t ∈ M, orderOf t = 2 →
      (∃ c ∈ M, c * x * c⁻¹ = t) ∨ (∃ c ∈ M, c * v * c⁻¹ = t) := by
    intro t htM ht2
    have ht2M : orderOf (⟨t, htM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk t htM).trans ht2
    have hx2M : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
    have hv2M : orderOf (⟨v, hvM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk v hvM).trans hv2
    rcases hcls _ (orderOf_barMk ht2M) with h | h
    · left
      obtain ⟨m, hmx⟩ := exists_conj_of_barMk_conj ht2M hx2M h
      exact ⟨m, m.2, congrArg Subtype.val hmx⟩
    · right
      obtain ⟨m, hmv⟩ := exists_conj_of_barMk_conj ht2M hv2M h
      exact ⟨m, m.2, congrArg Subtype.val hmv⟩
  have hnc : ¬ IsConj x v := not_isConj_of_two_adic hxM hvM hx2 hv2 hCx hCv hk1 hk2
  have hSE := isStronglyEmbedded_of_cent hMtop hxM hx2 hnc hfus hCx hCv
  have hB := CFSG.BenderSuzuki.bender_suzuki M hSE
  have hsol := C3.Layer1.Bk.isSolvable_centralizer_of_isBenderGroup hB hx2
  have hKsol : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hstd.K_le_C)
      (Subgroup.inclusion_injective hstd.K_le_C)
  have hq : Group.IsSolvable (↥K ⧸ pPrimeCore 2 ↥K) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  have hqs := TwoThin.isQuasisimple_hat hstd.comp
  have : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := CFSG.LocalCores.isQuasisimple_nontrivial hqs
  have : Group.IsPerfect (↥K ⧸ pPrimeCore 2 ↥K) := hqs.1
  exact Group.IsPerfect.not_isSolvable _ hq

end CFSG.GH74.GLS
