module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Aut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Z

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem hasNormalPComplement_of_mulEquiv' {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) (h : HasNormalPComplement 2 A) : HasNormalPComplement 2 B := by
  obtain ⟨N, hN, hcop, hq⟩ := h
  have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
  refine ⟨N.map e.toMonoidHom, hN', ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcop
  · exact hq.of_equiv (QuotientGroup.congr N (N.map e.toMonoidHom) e rfl)

theorem hasNormalPComplement_map' {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    {X : Subgroup A} (h : HasNormalPComplement 2 X) : HasNormalPComplement 2 (X.map f) := by
  obtain ⟨N, hN, hNc, hNp⟩ := h
  set g : X →* X.map f := f.subgroupMap X with hg
  have hgs : Function.Surjective g := f.subgroupMap_surjective X
  have hNf : (N.map g).Normal := hN.map g hgs
  refine ⟨N.map g, hNf, Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (H := N) g) hNc, ?_⟩
  have hle : N ≤ (N.map g).comap g := Subgroup.le_comap_map g N
  let φ : X ⧸ N →* (X.map f) ⧸ N.map g := QuotientGroup.map N (N.map g) g hle
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := hgs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact hNp.of_surjective φ hφ

theorem zpow_apply_eq_of_apply_eq {Y : Type*} [Group Y] {φ : MulAut Y} {x : Y} (hx : φ x = x)
    (k : ℤ) : (φ ^ k) x = x := by
  have hmem : φ ∈ MulAction.stabilizer (MulAut Y) x := hx
  exact zpow_mem hmem k

theorem exists_lift_of_fixed {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (g : normalizer (L : Set G)) (hg : IsPGroup 2 (zpowers g)) {x : L ⧸ pPrimeCore 2 L}
    (hx : oddBarAction L g x = x) :
    ∃ l : L, (g : G) * l = l * g ∧ (l : L ⧸ pPrimeCore 2 L) = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective x
  set α : ↥(zpowers g) →* MulAut L := L.normalizerMonoidHom.comp (zpowers g).subtype with hα
  have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) :=
    (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := L))
  have hfix : ∀ c : ↥(zpowers g),
      oddBarAut L (α c) (l₀ : L ⧸ pPrimeCore 2 L) = (l₀ : L ⧸ pPrimeCore 2 L) := by
    rintro ⟨c, k, rfl⟩
    have h1 : oddBarAut L (α ⟨g ^ k, k, rfl⟩) = (oddBarAction L g) ^ k := by
      show oddBarAction L (g ^ k) = _
      rw [map_zpow]
    rw [h1]
    exact zpow_apply_eq_of_apply_eq hx k
  obtain ⟨c, hc, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hg α
    (pPrimeCore 2 L) hcop l₀).2 (fun a y hy => by
      have hy' : ((y : L) : L ⧸ pPrimeCore 2 L) = (l₀ : L ⧸ pPrimeCore 2 L) :=
        (QuotientGroup.eq.mpr hy).symm
      have h2 : ((α a y : L) : L ⧸ pPrimeCore 2 L) = (l₀ : L ⧸ pPrimeCore 2 L) := by
        rw [← oddBarAut_apply_mk, hy', hfix a]
      exact QuotientGroup.eq.mp h2.symm)
  refine ⟨c, ?_, (QuotientGroup.eq.mpr hc).symm⟩
  have h3 := hcfix ⟨g, mem_zpowers g⟩
  have h4 : (g : G) * c * (g : G)⁻¹ = c := congrArg Subtype.val h3
  calc (g : G) * c = (g : G) * c * (g : G)⁻¹ * g := by group
    _ = c * g := by rw [h4]

end Eight

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem not_conj_b_bz (hNN : CF81NoNilp)
    (hY : (∃ c : H, c⁻¹ * d.b * c = d.b * d.z) → HasNormalPComplement 2
      ↥(centralizer ({h.a} : Set H) ⊓ centralizer ({d.b * d.z} : Set H))) (c : H) :
    c⁻¹ * d.b * c ≠ d.b * d.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  have hY' := hY ⟨c, hc⟩
  have ha2 : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
  set t := c * h.a * c⁻¹ with ht
  have hbz : c * (d.b * d.z) * c⁻¹ = d.b := by rw [← hc]; group
  have habz : h.a * (d.b * d.z) = d.b * d.z * h.a := by
    rw [← mul_assoc, d.a_comm_b, mul_assoc, ← d.z_comm_a, mul_assoc]
  have htb : t * d.b = d.b * t := by
    calc t * d.b = c * h.a * c⁻¹ * (c * (d.b * d.z) * c⁻¹) := by rw [hbz]
      _ = c * (h.a * (d.b * d.z)) * c⁻¹ := by group
      _ = c * (d.b * d.z * h.a) * c⁻¹ := by rw [habz]
      _ = c * (d.b * d.z) * c⁻¹ * t := by rw [ht]; group
      _ = d.b * t := by rw [hbz]
  have hcomm : ∀ k : ℤ, t * d.b ^ k = d.b ^ k * t := fun k =>
    (Commute.zpow_right (show Commute t d.b from htb) k).eq
  have htW : t ∈ normalizer (h.B : Set H) := by
    rw [d.B_eq, mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [hcomm k, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k
    · intro hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
      have hyk : y = d.b ^ k := by
        calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
          _ = t⁻¹ * d.b ^ k * t := by rw [hk]
          _ = d.b ^ k := by rw [mul_assoc, ← hcomm k, inv_mul_cancel_left]
      rw [hyk]
      exact zpow_mem (mem_zpowers _) k
  have htK : t ∈ normalizer (h.K : Set H) := by
    rw [← H₁.kloc.V_eq_K]
    exact mem_normalizer_layerIn htW
  set tt : ↥(normalizer (h.K : Set H)) := ⟨t, htK⟩ with htt
  set α := Eight.oddBarAction h.K tt with hα
  have htt2 : tt * tt = 1 := Subtype.ext (by
    show c * h.a * c⁻¹ * (c * h.a * c⁻¹) = 1
    rw [show c * h.a * c⁻¹ * (c * h.a * c⁻¹) = c * (h.a * h.a) * c⁻¹ by group, ha2]
    group)
  have hα2 : α * α = 1 := by rw [hα, ← map_mul, htt2, map_one]
  have httP : IsPGroup 2 (zpowers tt) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    refine orderOf_eq_prime (by rw [pow_two]; exact htt2) fun h1 => ?_
    have h2 : t = 1 := congrArg Subtype.val h1
    apply a_ne_one' (h := h)
    calc h.a = c⁻¹ * t * c := by rw [ht]; group
      _ = 1 := by rw [h2]; group
  set X : Subgroup H := centralizer ({t} : Set H) ⊓ h.K with hX
  have hXY : conjugate X c ≤ centralizer ({h.a} : Set H) ⊓ centralizer ({d.b * d.z} : Set H) := by
    intro w hw
    rw [mem_conjugate_iff] at hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
    have hw1' := mem_centralizer_singleton_iff.mp hw1
    have hwb : c * w * c⁻¹ * d.b = d.b * (c * w * c⁻¹) := d.comm_b_of_mem_M3 (mem_sup_left hw2)
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · have h1 : c * (w * h.a) * c⁻¹ = c * (h.a * w) * c⁻¹ := by
        calc c * (w * h.a) * c⁻¹ = c * w * c⁻¹ * t := by rw [ht]; group
          _ = t * (c * w * c⁻¹) := hw1'
          _ = c * (h.a * w) * c⁻¹ := by rw [ht]; group
      simpa using h1
    · have h1 : c * (w * (d.b * d.z)) * c⁻¹ = c * (d.b * d.z * w) * c⁻¹ := by
        calc c * (w * (d.b * d.z)) * c⁻¹ = c * w * c⁻¹ * (c * (d.b * d.z) * c⁻¹) := by group
          _ = c * w * c⁻¹ * d.b := by rw [hbz]
          _ = d.b * (c * w * c⁻¹) := hwb
          _ = c * (d.b * d.z) * c⁻¹ * (c * w * c⁻¹) := by rw [hbz]
          _ = c * (d.b * d.z * w) * c⁻¹ := by group
      simpa using h1
  have hconj : HasNormalPComplement 2 ↥(conjugate X c) := hasNormalPComplement_of_le 2 hXY hY'
  have hXn : HasNormalPComplement 2 ↥X := by
    have e : ↥X ≃* ↥(conjugate X c) :=
      X.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective
    exact Eight.hasNormalPComplement_of_mulEquiv' e.symm hconj
  have hCK : HasNormalPComplement 2 ↥((centralizer ({t} : Set H)).subgroupOf h.K) := by
    apply hasNormalPComplement_of_map_subtype 2 h.K
    rw [subgroupOf_map_subtype]
    exact hXn
  have hfix : fixSub α ≤ ((centralizer ({t} : Set H)).subgroupOf h.K).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥h.K)) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Eight.exists_lift_of_fixed tt httP hx
    refine ⟨l, mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr hl.symm), rfl⟩
  have hfixN : HasNormalPComplement 2 ↥(fixSub α) :=
    hasNormalPComplement_of_le 2 hfix (Eight.hasNormalPComplement_map' _ hCK)
  obtain ⟨-, p, f, hp, hp2, hf, hsoc, -⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.case8
  exact hNN _ p f hp hp2 hf hsoc α hα2 hfixN

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
