module

public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalCores CFSG.GroupTheory

variable {H : Type*} [Group H]

theorem eq_top_of_quotient_isPGroup [Finite H] {p : ℕ} [Fact p.Prime] [Group.IsPerfect H]
    (N : Subgroup H) [N.Normal] (hN : IsPGroup p (H ⧸ N)) : N = ⊤ := by
  by_contra hne
  have : Nontrivial (H ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
    exact hne
  have : Group.IsSolvable (H ⧸ N) := by
    have : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
    infer_instance
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) this

theorem involution_component_centralizes_two_core [Finite H] {t : H} (ht : orderOf t = 2)
    (L : Subgroup (Subgroup.centralizer ({t} : Set H))) (hL : IsComponent L) :
    ⁅L.map (Subgroup.centralizer ({t} : Set H)).subtype, CFSG.pCore 2 H⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  have hQp : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hQC : ⁅L, (CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))⁆ = ⊥ := by
    have hp2 : IsPGroup 2 ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))) :=
      hQp.comap_of_injective _ (Subgroup.centralizer ({t} : Set H)).subtype_injective
    have hsolv : Group.IsSolvable
        ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))) := by
      have : Group.IsNilpotent
          ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))) := hp2.isNilpotent
      infer_instance
    have hnorm : ((CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H))).Normal :=
      Subgroup.normal_subgroupOf
    exact (component_solvable_centralizer hsolv hnorm.isSubnormal).1 L hL
  have hodd : ∀ x ∈ L, ¬ 2 ∣ orderOf x → ∀ q ∈ CFSG.pCore 2 H,
      (x : H) * q * (x : H)⁻¹ = q := by
    intro x hxL hx q hq
    let A := Subgroup.zpowers (x : H)
    let B := Subgroup.zpowers t
    let α : A →* MulAut (CFSG.pCore 2 H) := MulAut.conjNormal.comp A.subtype
    let β : B →* MulAut (CFSG.pCore 2 H) := MulAut.conjNormal.comp B.subtype
    have hxt : (x : H) * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 x.2
    have hcomm : ∀ a b, α a * β b = β b * α a := by
      rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
      change MulAut.conjNormal (((x : H) ^ i)) * MulAut.conjNormal (t ^ j) =
        MulAut.conjNormal (t ^ j) * MulAut.conjNormal ((x : H) ^ i)
      rw [← map_mul, ← map_mul, ((Commute.zpow_zpow (hxt : Commute (x : H) t)) i j).eq]
    have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
      rintro ⟨a, i, rfl⟩ r hr
      have hrt : (r : H) ∈ Subgroup.centralizer ({t} : Set H) := by
        have := congrArg Subtype.val (hr ⟨t, Subgroup.mem_zpowers t⟩)
        rw [Subgroup.mem_centralizer_singleton_iff]
        change t * r * t⁻¹ = r at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have hcx : (x : H) * r = r * x := by
        have hmem : (⟨r, hrt⟩ : Subgroup.centralizer ({t} : Set H)) ∈
            (CFSG.pCore 2 H).subgroupOf (Subgroup.centralizer ({t} : Set H)) := r.2
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hQC hxL _ hmem
        exact (congrArg Subtype.val this).symm
      apply Subtype.ext
      change (x : H) ^ i * r * ((x : H) ^ i)⁻¹ = r
      rw [((Commute.zpow_left (hcx : Commute (x : H) r)) i).eq, mul_inv_cancel_right]
    have hA : ¬ 2 ∣ Nat.card A := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe]
      exact hx
    have hB : IsPGroup 2 B := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, ht, pow_one]⟩
    have h := thompson_A_times_B hQp hA hB α β hcomm hfix ⟨x, Subgroup.mem_zpowers _⟩
    have := congrArg (fun φ : MulAut (CFSG.pCore 2 H) => ((φ ⟨q, hq⟩ : CFSG.pCore 2 H) : H)) h
    simpa [α, MulAut.conjNormal_apply] using this
  let N : Subgroup L := ((Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)).comap
    (Subgroup.centralizer ({t} : Set H)).subtype).subgroupOf L
  have hNn : N.Normal := by
    have h1 : (Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)).Normal :=
      Subgroup.normal_centralizer
    have h2 : ((Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)).comap
        (Subgroup.centralizer ({t} : Set H)).subtype).Normal := h1.comap _
    exact Subgroup.normal_subgroupOf
  have hNmem : ∀ x : L, (∀ q ∈ CFSG.pCore 2 H,
      ((x : Subgroup.centralizer ({t} : Set H)) : H) * q *
        ((x : Subgroup.centralizer ({t} : Set H)) : H)⁻¹ = q) → x ∈ N := by
    intro x hx
    change ((x : Subgroup.centralizer ({t} : Set H)) : H) ∈
      Subgroup.centralizer ((CFSG.pCore 2 H : Subgroup H) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := hx q hq
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hquot : IsPGroup 2 (L ⧸ N) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hNmem
    have hord : orderOf (x ^ (2 ^ e)) = m := by
      rw [orderOf_pow' x (pow_ne_zero _ two_ne_zero), he, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (pow_pos two_pos e)]
    have hoddm : ¬ 2 ∣ orderOf (((x ^ (2 ^ e) : L) : Subgroup.centralizer ({t} : Set H))) := by
      rw [Subgroup.orderOf_coe, hord]
      exact hm.not_two_dvd_nat
    exact hodd _ (x ^ (2 ^ e)).2 hoddm
  have : Group.IsPerfect L := hL.1.1
  have htop := eq_top_of_quotient_isPGroup N hquot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨y, hy, rfl⟩
  have hyN : (⟨y, hy⟩ : L) ∈ N := htop ▸ Subgroup.mem_top _
  exact hyN

end CFSG.LocalAnalysis.ComponentInitial
