module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8

section Core

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_map_hom {K H : Type} [Group K] [Group H] {p : ℕ} {A : Subgroup K}
    (hA : IsElemAbelian p A) (f : K →* H) : IsElemAbelian p (A.map f) := by
  have hcomm : ∀ y ∈ A.map f, ∀ z ∈ A.map f, y * z = z * y := by
    intro y hy z hz
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    show f y' * f z' = f z' * f y'
    rw [← map_mul, ← map_mul, isElemAbelian_commute hA hy' hz']
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  rw [← map_pow, hA.2 y' hy', map_one]

theorem isElemAbelian_subgroupOf' {p : ℕ} {L F : Subgroup G} (hF : IsElemAbelian p F) :
    IsElemAbelian p (F.subgroupOf L) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (?_)⟩
  · exact isElemAbelian_commute hF (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · exact hF.2 _ (Subgroup.mem_subgroupOf.1 hx)

@[expose] noncomputable def piL (p : ℕ) (L : Subgroup G) : ↥L →* PSimple p L :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))

theorem card_le_center_mul_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    {A W : Subgroup ↥L} (hA : IsElemAbelian p A) (hW : IsPGroup 2 W) (hW1 : W ≠ ⊥)
    (hWN : ¬ W ≤ GLAPPrimeCore p ↥L) (hAW : A ≤ Subgroup.normalizer (W : Set ↥L)) :
    Nat.card A ≤
      Nat.card (Subgroup.center (PQuot p L)) * p ^ GLATwoLocalRank p (PSimple p L) := by
  have hZp : IsPGroup p (Subgroup.center (PQuot p L)) := I2611.isPGroup_center_pQuot' hp L
  have hcop2 : Nat.Coprime (2 : ℕ) p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hWc : ∀ w ∈ W, piL p L w = 1 → w ∈ GLAPPrimeCore p ↥L := by
    intro w hw hφ
    obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
    have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hcZ : (QuotientGroup.mk w : PQuot p L) ∈ Subgroup.center (PQuot p L) :=
      (QuotientGroup.eq_one_iff _).1 hφ
    obtain ⟨j, hj⟩ := hZp ⟨_, hcZ⟩
    have hj' : (QuotientGroup.mk w : PQuot p L) ^ p ^ j = 1 := congrArg Subtype.val hj
    have hk'' : (QuotientGroup.mk w : PQuot p L) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have h1 := orderOf_dvd_of_pow_eq_one hk''
    have h2 := orderOf_dvd_of_pow_eq_one hj'
    have hcop : Nat.Coprime (2 ^ k) (p ^ j) := Nat.Coprime.pow k j hcop2
    have h3 : orderOf (QuotientGroup.mk w : PQuot p L) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3)
  have hS : W.map (piL p L) ≠ ⊥ := by
    intro hbot
    apply hWN
    intro w hw
    have hmem : piL p L w ∈ W.map (piL p L) := Subgroup.mem_map_of_mem _ hw
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hWc w hw hmem
  have hEN : A.map (piL p L) ≤
      Subgroup.normalizer ((W.map (piL p L) : Subgroup (PSimple p L)) : Set (PSimple p L)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hAa := Subgroup.mem_normalizer_iff.1 (hAW ha)
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨a * w * a⁻¹, (hAa w).1 hw, ?_⟩
      simp only [map_mul, map_inv]
    · intro hh
      obtain ⟨w', hw', hweq⟩ := Subgroup.mem_map.1 hh
      have hinv := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hAW ha)) w'
      refine Subgroup.mem_map.2 ⟨a⁻¹ * w' * a, ?_, ?_⟩
      · have := (hinv).1 hw'
        simpa using this
      · have hh' : h = (piL p L a)⁻¹ * piL p L w' * piL p L a := by
          rw [hweq]
          group
        rw [hh']
        simp only [map_mul, map_inv]
  let ψ : ↥A →* PSimple p L := (piL p L).comp A.subtype
  have hψr : ψ.range = A.map (piL p L) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hlag := Subgroup.card_ker_mul_card_range ψ
  have hrange : Nat.card ψ.range ≤ p ^ GLATwoLocalRank p (PSimple p L) := by
    rw [hψr]
    exact card_le_pow_glaTwoLocalRank hp (isElemAbelian_map_hom hA (piL p L)) hS
      (IsPGroup.map hW (piL p L)) hEN
  have hker : Nat.card ψ.ker ≤ Nat.card (Subgroup.center (PQuot p L)) := by
    have hθ : ∀ k : ψ.ker, QuotientGroup.mk (k.1.1 : ↥L) ∈ Subgroup.center (PQuot p L) := by
      intro k
      have hk : piL p L k.1.1 = 1 := MonoidHom.mem_ker.1 k.2
      exact (QuotientGroup.eq_one_iff _).1 hk
    let θ : ψ.ker → Subgroup.center (PQuot p L) := fun k => ⟨QuotientGroup.mk (k.1.1 : ↥L), hθ k⟩
    have hinj : Function.Injective θ := by
      intro k k' hkk
      have h1 : (QuotientGroup.mk (k.1.1 : ↥L) : PQuot p L) = QuotientGroup.mk (k'.1.1 : ↥L) :=
        congrArg Subtype.val hkk
      have hN : (k.1.1 : ↥L)⁻¹ * k'.1.1 ∈ GLAPPrimeCore p ↥L := (QuotientGroup.eq).1 h1
      have he : (k.1.1 : ↥L)⁻¹ * k'.1.1 ∈ A :=
        A.mul_mem (A.inv_mem k.1.2) k'.1.2
      have he1 : ((k.1.1 : ↥L)⁻¹ * k'.1.1) ^ p = 1 := hA.2 _ he
      have hcopN : Nat.Coprime (orderOf ((k.1.1 : ↥L)⁻¹ * k'.1.1)) p := by
        have hmem : (((k.1.1 : ↥L)⁻¹ * k'.1.1 : ↥L) : G) ∈ GLAPPrimeCoreOf p L :=
          Subgroup.mem_map.2 ⟨_, hN, rfl⟩
        have := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hmem
        rwa [Subgroup.orderOf_coe] at this
      have hd : orderOf ((k.1.1 : ↥L)⁻¹ * k'.1.1) ∣ p := orderOf_dvd_of_pow_eq_one he1
      have h3 : orderOf ((k.1.1 : ↥L)⁻¹ * k'.1.1) = 1 := Nat.Coprime.eq_one_of_dvd hcopN hd
      have h4 : (k.1.1 : ↥L) = k'.1.1 := inv_mul_eq_one.1 (orderOf_eq_one_iff.1 h3)
      exact Subtype.ext (Subtype.ext h4)
    exact Nat.card_le_card_of_injective θ hinj
  calc Nat.card A = Nat.card ψ.ker * Nat.card ψ.range := hlag.symm
    _ ≤ Nat.card (Subgroup.center (PQuot p L)) * p ^ GLATwoLocalRank p (PSimple p L) :=
      Nat.mul_le_mul hker hrange

theorem card_le_mul_card_inf {p : ℕ} {L E : Subgroup G} {x : G} (hxp : orderOf x = p)
    (hxL : ∀ l ∈ L, x * l = l * x) (hE : E ≤ L ⊔ Subgroup.zpowers x) :
    Nat.card E ≤ p * Nat.card (L ⊓ E : Subgroup G) := by
  have hxc : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => (hxL h hh).symm)
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hxc)
  have hLN : L ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hzN
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hE.trans hLN
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := L) (B := Subgroup.zpowers x) hzN
  rw [Nat.card_zpowers, hxp] at h1
  have hpos : 0 < Nat.card (L ⊓ Subgroup.zpowers x : Subgroup G) := Nat.card_pos
  have hLx : Nat.card (L ⊔ Subgroup.zpowers x : Subgroup G) ≤ p * Nat.card L := by
    have : Nat.card (L ⊔ Subgroup.zpowers x : Subgroup G) ≤
        Nat.card (L ⊔ Subgroup.zpowers x : Subgroup G) * Nat.card (L ⊓ Subgroup.zpowers x : Subgroup G) :=
      Nat.le_mul_of_pos_right _ hpos
    rw [h1] at this
    rw [mul_comm p]
    exact this
  have h2 := card_sup_mul_card_inf_of_le_normalizer (A := L) (B := E) hEN
  have hLE : Nat.card (L ⊔ E : Subgroup G) ≤ p * Nat.card L :=
    (Subgroup.card_le_of_le (sup_le (le_sup_left) hE : L ⊔ E ≤ L ⊔ Subgroup.zpowers x)).trans hLx
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have key : Nat.card L * Nat.card E ≤ Nat.card L * (p * Nat.card (L ⊓ E : Subgroup G)) := by
    rw [← h2]
    calc Nat.card (L ⊔ E : Subgroup G) * Nat.card (L ⊓ E : Subgroup G)
        ≤ (p * Nat.card L) * Nat.card (L ⊓ E : Subgroup G) := Nat.mul_le_mul_right _ hLE
      _ = Nat.card L * (p * Nat.card (L ⊓ E : Subgroup G)) := by ring
  exact Nat.le_of_mul_le_mul_left key hLpos

end Core

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
