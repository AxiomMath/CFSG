module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

@[expose] noncomputable def pairOrder {G : Type} [Group G] (p q : G) : ℕ :=
  Nat.card ↥(centralizer ({p} : Set G) ⊓ centralizer ({q} : Set G))

section PairOrder

variable {G : Type} [Group G]

theorem pairOrder_comm (p q : G) : pairOrder p q = pairOrder q p := by
  rw [pairOrder, pairOrder, inf_comm]

theorem pairOrder_conj (g p q : G) : pairOrder (g * p * g⁻¹) (g * q * g⁻¹) = pairOrder p q := by
  have hconj : ∀ (x w : G), x * (g * w * g⁻¹) = (g * w * g⁻¹) * x →
      g⁻¹ * x * g * w = w * (g⁻¹ * x * g) := by
    intro x w hx
    calc g⁻¹ * x * g * w = g⁻¹ * (x * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * x) * g := by rw [hx]
      _ = w * (g⁻¹ * x * g) := by group
  have hconj' : ∀ (y w : G), y * w = w * y →
      g * y * g⁻¹ * (g * w * g⁻¹) = (g * w * g⁻¹) * (g * y * g⁻¹) := by
    intro y w hy
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hy]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  rw [pairOrder, pairOrder]
  refine Nat.card_congr ⟨fun x => ⟨g⁻¹ * x * g, ?_⟩, fun y => ⟨g * y * g⁻¹, ?_⟩, ?_, ?_⟩
  · obtain ⟨hxa, hxb⟩ := mem_inf.1 x.2
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2
      (hconj x p (mem_centralizer_singleton_iff.1 hxa)),
      mem_centralizer_singleton_iff.2 (hconj x q (mem_centralizer_singleton_iff.1 hxb))⟩
  · obtain ⟨hya, hyb⟩ := mem_inf.1 y.2
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2
      (hconj' y p (mem_centralizer_singleton_iff.1 hya)),
      mem_centralizer_singleton_iff.2 (hconj' y q (mem_centralizer_singleton_iff.1 hyb))⟩
  · intro x; ext; simp [mul_assoc]
  · intro y; ext; simp [mul_assoc]

theorem pairOrder_mul_right {p q : G} (hpq : p * q = q * p) :
    pairOrder p (p * q) = pairOrder p q := by
  rw [pairOrder, pairOrder]
  have h : centralizer ({p} : Set G) ⊓ centralizer ({p * q} : Set G) =
      centralizer ({p} : Set G) ⊓ centralizer ({q} : Set G) := by
    apply le_antisymm
    · intro g hg
      rw [mem_inf] at hg ⊢
      obtain ⟨hgp, hgpq⟩ := hg
      refine ⟨hgp, ?_⟩
      rw [mem_centralizer_singleton_iff] at hgp hgpq ⊢
      refine mul_left_cancel (a := p) ?_
      calc p * (g * q) = (p * g) * q := by simp only [mul_assoc]
        _ = (g * p) * q := by rw [← hgp]
        _ = g * (p * q) := by simp only [mul_assoc]
        _ = (p * q) * g := hgpq
        _ = p * (q * g) := by simp only [mul_assoc]
    · intro g hg
      rw [mem_inf] at hg ⊢
      obtain ⟨hgp, hgq⟩ := hg
      refine ⟨hgp, ?_⟩
      rw [mem_centralizer_singleton_iff] at hgp hgq ⊢
      calc g * (p * q) = (g * p) * q := by simp only [mul_assoc]
        _ = (p * g) * q := by rw [hgp]
        _ = p * (g * q) := by simp only [mul_assoc]
        _ = p * (q * g) := by rw [hgq]
        _ = (p * q) * g := by simp only [mul_assoc]
  rw [h]

theorem pairOrder_mul_left {p q : G} (hpq : p * q = q * p) :
    pairOrder q (p * q) = pairOrder p q := by
  rw [pairOrder_comm q (p * q), hpq, pairOrder_comm (q * p) q,
    pairOrder_mul_right (p := q) (q := p) hpq.symm, pairOrder_comm]

end PairOrder

@[expose] def N10 (k : ℕ) : ℕ := 2 * ((10 - 2 * k).factorial * 2 ^ k * k.factorial)

theorem N10_one : N10 1 = 161280 := by
  norm_num [N10, Nat.factorial]

theorem N10_four : N10 4 = 1536 := by
  norm_num [N10, Nat.factorial]

theorem N10_five : N10 5 = 7680 := by
  norm_num [N10, Nat.factorial]

theorem N10_one_ne_four : N10 1 ≠ N10 4 := by
  rw [N10_one, N10_four]; norm_num

theorem N10_one_ne_five : N10 1 ≠ N10 5 := by
  rw [N10_one, N10_five]; norm_num

theorem N10_four_ne_five : N10 4 ≠ N10 5 := by
  rw [N10_four, N10_five]; norm_num

theorem two_mul_card_centralizer_perm_ten {σ : Perm (Fin 10)} (h2 : σ * σ = 1) :
    2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 10)))) = N10 (Multiset.card σ.cycleType) := by
  rw [nat_card_centralizer_of_mul_self h2, Fintype.card_fin]
  unfold N10
  ring

section Data

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem CentData.card_inf_centralizer (hC : CentData z ι) (σ : Perm (Fin 10)) :
    Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({ι σ} : Set G)) =
      2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 10)))) := by
  let f : Bool × ↥(centralizer ({σ} : Set (Perm (Fin 10)))) →
      ↥(centralizer ({z} : Set G) ⊓ centralizer ({ι σ} : Set G)) :=
    fun bs => ⟨(cond bs.1 z 1) * ι (bs.2 : Perm (Fin 10)), by
      refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
      · have hz : (cond bs.1 z 1) * z = z * (cond bs.1 z 1) := by
          cases bs.1 <;> simp
        have his : (ι (bs.2 : Perm (Fin 10))) * z = z * (ι (bs.2 : Perm (Fin 10))) :=
          (hC.comm _).symm
        rw [mul_assoc, his, ← mul_assoc, hz, mul_assoc]
      · have hzσ : z * ι σ = ι σ * z := hC.comm σ
        have hι : ι (bs.2 : Perm (Fin 10)) * ι σ = ι σ * ι (bs.2 : Perm (Fin 10)) := by
          rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 bs.2.2]
        have hc : (cond bs.1 z 1) * ι σ = ι σ * (cond bs.1 z 1) := by
          cases bs.1 <;> simp [hzσ]
        rw [mul_assoc, hι, ← mul_assoc, hc, mul_assoc]⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨b, s⟩ ⟨b', s'⟩ h
    simp only [f, Subtype.mk.injEq] at h
    cases b <;> cases b'
    · simp only [cond_false, one_mul] at h
      exact Prod.ext rfl (Subtype.ext (hC.inj h))
    · exfalso
      simp only [cond_false, cond_true, one_mul] at h
      refine hC.ne_z (s * (s')⁻¹) ?_
      have hz : z = ι (s : Perm (Fin 10)) * (ι (s' : Perm (Fin 10)))⁻¹ := by
        rw [h]; group
      rw [hz]
      simp only [map_mul, Subgroup.coe_inv, map_inv]
    · exfalso
      simp only [cond_false, cond_true, one_mul] at h
      refine hC.ne_z (s' * s⁻¹) ?_
      have hz : z = ι (s' : Perm (Fin 10)) * (ι (s : Perm (Fin 10)))⁻¹ := by
        rw [← h]; group
      rw [hz]
      simp only [map_mul, Subgroup.coe_inv, map_inv]
    · simp only [cond_true] at h
      exact Prod.ext rfl (Subtype.ext (hC.inj (mul_left_cancel h)))
  have hf_surj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨hgz, hgισ⟩ := mem_inf.1 hg
    obtain ⟨σ', hσ'⟩ := hC.cases g hgz
    have hcomm : (σ' : Perm (Fin 10)) * σ = σ * σ' := by
      apply hC.inj
      rw [map_mul, map_mul]
      rcases hσ' with h | h
      · rw [h] at hgισ
        exact mem_centralizer_singleton_iff.1 hgισ
      · have hthis : (z * ι σ') * ι σ = ι σ * (z * ι σ') := by
          rw [h] at hgισ; exact mem_centralizer_singleton_iff.1 hgισ
        have key : z * (ι σ' * ι σ) = z * (ι σ * ι σ') := by
          calc z * (ι σ' * ι σ) = (z * ι σ') * ι σ := by simp only [mul_assoc]
            _ = ι σ * (z * ι σ') := hthis
            _ = (ι σ * z) * ι σ' := by simp only [mul_assoc]
            _ = (z * ι σ) * ι σ' := by rw [← hC.comm σ]
            _ = z * (ι σ * ι σ') := by simp only [mul_assoc]
        exact mul_left_cancel key
    rcases hσ' with h | h
    · refine ⟨(false, ⟨σ', mem_centralizer_singleton_iff.2 hcomm⟩), ?_⟩
      apply Subtype.ext
      simp only [f, cond_false, one_mul]
      exact h.symm
    · refine ⟨(true, ⟨σ', mem_centralizer_singleton_iff.2 hcomm⟩), ?_⟩
      apply Subtype.ext
      simp only [f, cond_true]
      exact h.symm
  let e := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]

theorem CentData.card_inf_centralizer_mul (hC : CentData z ι) (σ : Perm (Fin 10)) :
    Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({z * ι σ} : Set G)) =
      2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 10)))) := by
  calc Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({z * ι σ} : Set G))
      = pairOrder z (z * ι σ) := rfl
    _ = pairOrder z (ι σ) := pairOrder_mul_right (p := z) (q := ι σ) (hC.comm σ)
    _ = Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({ι σ} : Set G)) := rfl
    _ = 2 * Nat.card ↥(centralizer ({σ} : Set (Perm (Fin 10)))) :=
        CentData.card_inf_centralizer hC σ

theorem card_inf_centralizer_eq_card_centralizer {d : G} (f : ↥(centralizer ({d} : Set G))) :
    Nat.card ↥(centralizer ({d} : Set G) ⊓ centralizer ({(f : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))) := by
  let g : ↥(centralizer ({d} : Set G) ⊓ centralizer ({(f : G)} : Set G)) →
      ↥(Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))) :=
    fun x => ⟨⟨x, (mem_inf.1 x.2).1⟩, by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2)⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      exact Subtype.ext (congrArg
        (fun z : ↥(Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))) =>
          (((z : ↥(centralizer ({d} : Set G)))) : G)) h)
    · intro a
      refine ⟨⟨a.1, mem_inf.2 ⟨a.1.2, ?_⟩⟩, ?_⟩
      · exact mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 a.2))
      · apply Subtype.ext
        rfl
  exact Nat.card_congr (Equiv.ofBijective g hg)

theorem card_ker_restrict_centralizer [Finite G] {d : G}
    {π : ↥(centralizer ({d} : Set G)) →* Perm (Fin 10)} (hS : SymSec d π)
    (hd1 : d ≠ 1) (f : ↥(centralizer ({d} : Set G))) :
    Nat.card ↥((π.comp
        (Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))).subtype).ker) = 2 := by
  let A : Subgroup ↥(centralizer ({d} : Set G)) :=
    Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))
  let φ : A →* Perm (Fin 10) := π.comp A.subtype
  change Nat.card ↥(φ.ker) = 2
  have hselfA : selfC d ∈ A :=
    Subgroup.center_le_centralizer ({f} : Set ↥(centralizer ({d} : Set G))) (selfC_mem_center d)
  have hπself : π (selfC d) = 1 := (hS.ker (selfC d)).2 (Or.inr rfl)
  let k2 : ↥(φ.ker) := ⟨⟨selfC d, hselfA⟩, by
    show φ ⟨selfC d, hselfA⟩ = 1
    exact hπself⟩
  have hk2ne : k2 ≠ (1 : ↥(φ.ker)) := by
    intro h
    have h2 : (⟨selfC d, hselfA⟩ : A) = 1 := congrArg (fun x : ↥(φ.ker) => (x.1 : A)) h
    have h3 : selfC d = (1 : ↥(centralizer ({d} : Set G))) :=
      congrArg (fun x : A => (x.1 : ↥(centralizer ({d} : Set G)))) h2
    have h4 : (selfC d : G) = 1 :=
      congrArg (fun x : ↥(centralizer ({d} : Set G)) => (x : G)) h3
    exact hd1 h4
  rw [Nat.card_eq_two_iff' (1 : ↥(φ.ker))]
  refine ⟨k2, hk2ne, ?_⟩
  intro y hy
  have hy1 : π (y.1.1) = 1 := y.2
  rcases (hS.ker (y.1.1)).1 hy1 with h | h
  · exfalso; exact hy (Subtype.ext (Subtype.ext (Subtype.ext h)))
  · exact Subtype.ext (Subtype.ext (Subtype.ext h))

theorem range_restrict_centralizer [Finite G] {d : G}
    {π : ↥(centralizer ({d} : Set G)) →* Perm (Fin 10)} (hS : SymSec d π)
    {κ : ↥(centralizer ({d} : Set G)) →* ℤˣ} (hκ : κ (selfC d) = -1)
    (f : ↥(centralizer ({d} : Set G))) :
    (π.comp (Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))).subtype).range =
      Subgroup.centralizer ({π f} : Set (Perm (Fin 10))) := by
  apply le_antisymm
  · rintro s ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change π (a : ↥(centralizer ({d} : Set G))) * π f =
      π f * π (a : ↥(centralizer ({d} : Set G)))
    have ha : a.1 * f = f * a.1 := mem_centralizer_singleton_iff.1 a.2
    rw [← map_mul, ← map_mul, ha]
  · intro s hs
    rw [mem_centralizer_singleton_iff] at hs
    obtain ⟨g, hg⟩ := hS.surj s
    have hker' : π ((g * f * g⁻¹) * f⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, hs]
      group
    have hgcomm : g * f * g⁻¹ = f := by
      rcases (hS.ker ((g * f * g⁻¹) * f⁻¹)).1 hker' with h | h
      · have h1 : (g * f * g⁻¹) * f⁻¹ = 1 := Subtype.ext h
        calc g * f * g⁻¹ = (g * f * g⁻¹) * (f⁻¹ * f) := by group
          _ = ((g * f * g⁻¹) * f⁻¹) * f := by group
          _ = 1 * f := by rw [h1]
          _ = f := by group
      · exfalso
        have hself : (g * f * g⁻¹) * f⁻¹ = selfC d := Subtype.ext h
        have hL : κ ((g * f * g⁻¹) * f⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [mul_comm (κ g) (κ f)]
          group
        have hone : (1 : ℤˣ) = -1 := by
          calc (1 : ℤˣ) = κ ((g * f * g⁻¹) * f⁻¹) := hL.symm
            _ = κ (selfC d) := by rw [hself]
            _ = -1 := hκ
        have hone_ne : (1 : ℤˣ) ≠ -1 := by
          intro hh
          have : (1 : ℤ) = -1 := congrArg (fun u : ℤˣ => (u : ℤ)) hh
          norm_num at this
        exact hone_ne hone
    refine ⟨⟨g, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      calc g * f = (g * f * g⁻¹) * g := by group
        _ = f * g := by rw [hgcomm]
    · show π g = s
      exact hg

theorem SymSec.card_inf_centralizer [Finite G] {d : G}
    {π : ↥(centralizer ({d} : Set G)) →* Perm (Fin 10)} (hS : SymSec d π)
    {κ : ↥(centralizer ({d} : Set G)) →* ℤˣ} (hκ : κ (selfC d) = -1) (hd2 : d * d = 1)
    (hd1 : d ≠ 1) (f : ↥(centralizer ({d} : Set G))) :
    Nat.card ↥(centralizer ({d} : Set G) ⊓ centralizer ({(f : G)} : Set G)) =
      2 * Nat.card ↥(centralizer ({π f} : Set (Perm (Fin 10)))) := by
  let φ : ↥(Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))) →* Perm (Fin 10) :=
    π.comp (Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))).subtype
  calc Nat.card ↥(centralizer ({d} : Set G) ⊓ centralizer ({(f : G)} : Set G))
      = Nat.card ↥(Subgroup.centralizer ({f} : Set ↥(centralizer ({d} : Set G)))) :=
        card_inf_centralizer_eq_card_centralizer f
    _ = Nat.card ↥(φ.ker) * Nat.card ↥(φ.range) := (card_ker_mul_card_range φ).symm
    _ = 2 * Nat.card ↥(Subgroup.centralizer ({π f} : Set (Perm (Fin 10)))) := by
        rw [card_ker_restrict_centralizer hS hd1 f, range_restrict_centralizer hS hκ f]

end Data

end CFSG.OddStandard.AltStdSec.SwapPattern
