module

public import CFSG.GH74.Generic.BProg.B3.Lemma212Aux
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.GH74.GLS
open scoped commutatorElement

namespace PiAux

variable {G : Type} [Group G]

theorem exists_mul_comm_of_odd [Finite G] {Λ O : Subgroup G} (hOΛ : O ≤ Λ)
    (hodd : Odd (Nat.card O)) {c : G} (hc2 : c * c = 1) {y : G} (hy : y ∈ Λ)
    (hn : y⁻¹ * (c⁻¹ * y * c) ∈ O) :
    ∃ m ∈ O, y * m ∈ Λ ∧ c * (y * m) = (y * m) * c := by
  set n := y⁻¹ * (c⁻¹ * y * c) with hndef
  have hci : c⁻¹ = c := (eq_inv_of_mul_eq_one_left hc2).symm
  have hk : Odd (orderOf n) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard O hn)
  set m := n ^ ((orderOf n + 1) / 2) with hmdef
  have hmO : m ∈ O := pow_mem hn _
  have hmm : m * m = n := by
    rw [hmdef, ← pow_two, ← pow_mul]
    have : (orderOf n + 1) / 2 * 2 = orderOf n + 1 :=
      Nat.div_mul_cancel (even_iff_two_dvd.mp hk.add_one)
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hcn : c⁻¹ * n * c = n⁻¹ := by
    rw [hndef]
    calc c⁻¹ * (y⁻¹ * (c⁻¹ * y * c)) * c = c⁻¹ * y⁻¹ * c⁻¹ * y * (c * c) := by group
      _ = c⁻¹ * y⁻¹ * c⁻¹ * y := by rw [hc2, mul_one]
      _ = (y⁻¹ * (c⁻¹ * y * c))⁻¹ := by simp only [mul_inv_rev, inv_inv, hci, mul_assoc]
  have hcm : c⁻¹ * m * c = m⁻¹ := by
    have h := map_pow (MulAut.conj c⁻¹) n ((orderOf n + 1) / 2)
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [hmdef, h, hcn, inv_pow]
  have hcy : c⁻¹ * y * c = y * n := by rw [hndef]; group
  refine ⟨m, hmO, mul_mem hy (hOΛ hmO), ?_⟩
  have hfix : c⁻¹ * (y * m) * c = y * m := by
    calc c⁻¹ * (y * m) * c = (c⁻¹ * y * c) * (c⁻¹ * m * c) := by group
      _ = y * (m * m) * m⁻¹ := by rw [hcy, hcm, hmm]
      _ = y * m := by group
  calc c * (y * m) = c * (c⁻¹ * (y * m) * c) := by rw [hfix]
    _ = (y * m) * c := by group

variable [Finite G]

theorem pPrimeCoreOf_le_of_isPCompIn {H J : Subgroup G} (hJ : IsPCompIn 2 H J) :
    pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJH, K', -, hsub, -⟩ := hJ
  have h1 := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal (X := ↥H) 2 hsub
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hJH]
  exact Subgroup.map_mono h1

theorem conj_mem_pPrimeCoreOf {Λ : Subgroup G} {g n : G} (hg : g ∈ Λ)
    (hn : n ∈ pPrimeCoreOf 2 Λ) : g * n * g⁻¹ ∈ pPrimeCoreOf 2 Λ :=
  (mem_normalizer_iff.mp (TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hg)) n).mp hn

@[expose] def commCoreSub (Λ : Subgroup G) (c : G) : Subgroup G where
  carrier := {y | y ∈ Λ ∧ y⁻¹ * (c⁻¹ * y * c) ∈ pPrimeCoreOf 2 Λ}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (a * b)⁻¹ * (c⁻¹ * (a * b) * c) =
        (b⁻¹ * (a⁻¹ * (c⁻¹ * a * c)) * b⁻¹⁻¹) * (b⁻¹ * (c⁻¹ * b * c)) := by group
    rw [e]
    exact mul_mem (conj_mem_pPrimeCoreOf (inv_mem hb) ha') hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : a⁻¹⁻¹ * (c⁻¹ * a⁻¹ * c) = a * (a⁻¹ * (c⁻¹ * a * c))⁻¹ * a⁻¹ := by group
    rw [e]
    exact conj_mem_pPrimeCoreOf ha (inv_mem ha')

end PiAux

open PiAux

theorem lemmaPi {X : Type} [Group X] [Finite X] (t c : X) (ht : orderOf t = 2)
    (hc : orderOf c = 2)
    (htL : t ∈ pLayerOf 2 (centralizer ({t} : Set X)))
    (hcL : c ∈ pLayerOf 2 (centralizer ({t} : Set X)))
    (hcZ : ∀ y ∈ pLayerOf 2 (centralizer ({t} : Set X)),
      y⁻¹ * (c⁻¹ * y * c) ∈ pPrimeCoreOf 2 (pLayerOf 2 (centralizer ({t} : Set X)))) :
    t ∈ pLayerOf 2 (centralizer ({c} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer ({t} : Set X) with hY
  set Λ := pLayerOf 2 Y with hΛ
  have hΛY : Λ ≤ Y := TwoThin.pLayerOf_le 2 Y
  have hOΛ : pPrimeCoreOf 2 Λ ≤ Λ := TwoThin.pPrimeCoreOf_le Λ
  have hOodd : Odd (Nat.card (pPrimeCoreOf 2 Λ)) := TwoThin.card_pPrimeCoreOf_odd Λ
  have hc2 : c * c = 1 := by rw [← pow_two, ← hc, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp (hΛY hcL)
  set Q := Λ ⊓ centralizer ({c} : Set X) with hQ
  have hQΛ : Q ≤ Λ := inf_le_left
  have htQ : t ∈ Q := ⟨htL, mem_centralizer_singleton_iff.mpr hct.symm⟩
  have : (pPrimeCore 2 ↥Λ).Normal := pPrimeCore_normal
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Λ) with hπ
  set φ : ↥Q →* ↥Λ ⧸ pPrimeCore 2 ↥Λ := π.comp (Subgroup.inclusion hQΛ) with hφ
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥Λ) z
    obtain ⟨m, hmO, hym, hcomm⟩ := exists_mul_comm_of_odd hOΛ hOodd hc2 y.2 (hcZ y y.2)
    have hq : (y : X) * m ∈ Q := ⟨hym, mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    refine ⟨⟨_, hq⟩, ?_⟩
    show π ⟨(y : X) * m, hym⟩ = π y
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hm' : (⟨m⁻¹, hOΛ (inv_mem hmO)⟩ : ↥Λ) ∈ pPrimeCore 2 ↥Λ :=
      (Stage2.Signalizer.L52Two.I1.mem_pPrimeCoreOf_iff _).1 (inv_mem hmO)
    convert hm' using 1
    ext
    simp
  have hodd : Odd (Nat.card φ.ker) := by
    have hk : φ.ker = (pPrimeCore 2 ↥Λ).comap (Subgroup.inclusion hQΛ) := by
      rw [hφ, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rw [hk]
    exact Odd.of_dvd_nat (TwoThin.odd_card_pPrimeCore ↥Λ)
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hQΛ))
  have hΛall : ∀ z : ↥Λ, z ∈ ComponentClassification.TwoLayer.subgroup ↥Λ := by
    intro z
    have h1 : (z : X) ∈ pLayerOf 2 Λ := by
      rw [CFSG.GH74.Generic.BProg.B3.Lemma212Aux.pLayerOf_pLayerOf]
      exact z.2
    rw [TwoThin.pLayerOf_two_eq_map] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    rwa [show w = z from Subtype.ext hwz] at hw
  have hπodd : Odd (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact TwoThin.odd_card_pPrimeCore _
  have himg := ComponentClassification.TwoLayerTransport.image_of_odd_kernel π
    (QuotientGroup.mk'_surjective _) hπodd
  set t' : ↥Q := ⟨t, htQ⟩ with ht'
  have hφt : φ t' ∈ ComponentClassification.TwoLayer.subgroup (↥Λ ⧸ pPrimeCore 2 ↥Λ) := by
    rw [← himg]
    exact ⟨_, hΛall _, rfl⟩
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  have htQL := CFSG.GH74.Generic.BProg.B3.Lemma212Aux.mem_twoLayer_of_map_mem φ hsurj hodd ht'2 hφt
  have htLQ : t ∈ pLayerOf 2 Q := by
    rw [TwoThin.pLayerOf_two_eq_map]
    exact ⟨t', htQL, rfl⟩
  have hzt := CFSG.GH74.Generic.BProg.centralizer_zpowers_eq t
  set M := centralizer ({c} : Set X) ⊓ centralizer ((zpowers t : Subgroup X) : Set X) with hM
  have hQM : Q ≤ M := fun y hy => ⟨hy.2, by rw [hzt]; exact hΛY hy.1⟩
  have hnormal : (Q.subgroupOf M).Normal := by
    refine (normal_subgroupOf_iff hQM).mpr fun h k hh hk => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hkY : k ∈ Y := by rw [hY, ← hzt]; exact hk.2
      exact (mem_normalizer_iff.mp
        (CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer.mem_normalizer_pLayerOf_of_mem_normalizer
          (le_normalizer hkY)) h).mp hh.1
    · have hkc : k ∈ centralizer ({c} : Set X) := (Subgroup.mem_inf.mp hk).1
      have hhc : h ∈ centralizer ({c} : Set X) := (Subgroup.mem_inf.mp hh).2
      exact mul_mem (mul_mem hkc hhc) (inv_mem hkc)
  have h1 := CFSG.GH74.Generic.BProg.pLayerOf_le_of_normal 2 hQM
  have htc : t ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr hct.symm
  have h2 := Stage2.Signalizer.L52Two.I1.pLayerOf_inf_centralizer_le
    (H := centralizer ({c} : Set X)) (U := zpowers t) (zpowers_le.mpr htc)
    (CFSG.GH74.Generic.BProg.isPGroup_two_zpowers ⟨1, by rw [pow_one, ← ht, pow_orderOf_eq_one]⟩)
  exact h2 (h1 htLQ)

theorem lemmaPi' {X : Type} [Group X] [Finite X] (t c : X) (K : Subgroup X)
    (hK : IsPCompIn 2 (centralizer ({t} : Set X)) K) (hcK : c ∈ K)
    (hcZ : c ∈ (Open.fusionZStar ↥K).map K.subtype) :
    ∀ y ∈ pLayerOf 2 (centralizer ({t} : Set X)),
      y⁻¹ * (c⁻¹ * y * c) ∈ pPrimeCoreOf 2 (pLayerOf 2 (centralizer ({t} : Set X))) := by
  set Y := centralizer ({t} : Set X) with hY
  set Λ := pLayerOf 2 Y with hΛ
  have hKΛ : IsPCompIn 2 Λ K :=
    CFSG.GH74.Generic.BProg.B3.Lemma212Aux.isPCompIn_of_le hK (le_sSup hK) (TwoThin.pLayerOf_le 2 Y)
  have hOK : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 Λ := pPrimeCoreOf_le_of_isPCompIn hKΛ
  suffices h : Λ ≤ commCoreSub Λ c from fun y hy => (h hy).2
  refine sSup_le fun L hL => ?_
  intro y hy
  refine ⟨le_sSup hL hy, hOK ?_⟩
  by_cases hLK : L = K
  · subst hLK
    obtain ⟨c', hc', rfl⟩ := hcZ
    have hcen := (Subgroup.mem_center_iff.mp hc'
      (QuotientGroup.mk' (Open.fusionOddCore ↥L) (⟨y, hy⟩ : ↥L))).symm
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hcen
    have hmem : (⟨y, hy⟩ : ↥L)⁻¹ * (c'⁻¹ * ⟨y, hy⟩ * c') ∈ pPrimeCore 2 ↥L := by
      rw [← fusionOddCore_eq_pPrimeCore]
      convert hcen using 1
      group
    exact (Stage2.Signalizer.L52Two.I1.mem_pPrimeCoreOf_iff (G := X)
      (L.mul_mem (L.inv_mem hy) (L.mul_mem (L.mul_mem (L.inv_mem c'.2) hy) c'.2))).2 hmem
  · have hsec := Stage1.Thm2.Recip.le_cSec_of_ne hL hK hLK (L.inv_mem hy)
    obtain ⟨-, -, hcomm⟩ := hsec
    have h := (pPrimeCoreOf 2 K).inv_mem (hcomm c⁻¹ (K.inv_mem hcK))
    convert h using 1
    simp only [commutatorElement_def]
    group

end CFSG.ComponentClassification.GSThmB
