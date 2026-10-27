module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34CaseTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Quotient

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

namespace CaseTwo

variable {a t z : G} (c : CaseTwo S A₁ A₂ a t z)
include c

theorem conj_involution {v : G} (hvv : v * v = 1) : v⁻¹ * t * v = twist t v * t := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hvv
  have htt := c.t_mul_self
  rw [hvinv, twist]
  calc v * t * v = v * t * v * (t * t) := by rw [htt, mul_one]
    _ = v * (t * v * t) * t := by group

theorem t_mem_conj {g : G} (hg : EscapeChoice A₁ A₂ a t g) : t ∈ rightConjugate A₁ g :=
  hg.conj_eq ▸ mem_rightConjugate_conj c.mem

theorem t_mem_conj_sylow {g : G} (hg : EscapeChoice A₁ A₂ a t g) :
    t ∈ rightConjugate (S : Subgroup G) g :=
  Subgroup.map_mono c.hyp.le_one (c.t_mem_conj hg)

theorem not_mem_conj {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) (hvv : v * v = 1) {g : G}
    (hg : EscapeChoice A₁ A₂ a t g) : v ∉ rightConjugate (overlapClosure A₁ A₂) g := by
  intro hvH
  have hvz : Commute v z := c.commute_one_two hv c.inf_mem.2
  let X := commutingPairSubgroup v z hvv c.mul_self hvz
  have hv1 : v ≠ 1 := fun h1 => hvA (h1 ▸ A₂.one_mem)
  have hvz' : v ≠ z := fun h1 => hvA (h1 ▸ c.inf_mem.2)
  refine c.hyp.choice_not_le c.not_le₁₂ c.not_le₂₁ hg (X := X) ?_ ?_ ?_
  · intro y hy
    rcases mem_commutingPairSubgroup.mp hy with rfl | rfl | rfl | rfl
    · exact Or.inl A₁.one_mem
    · exact Or.inl hv
    · exact Or.inl c.inf_mem.1
    · exact Or.inl (A₁.mul_mem hv c.inf_mem.1)
  · rw [commutingPairSubgroup_card hv1 c.ne_one hvz']
    norm_num
  · have hzH := hg.centralizer_le c.z_mem_centralizer
    intro y hy
    rcases mem_commutingPairSubgroup.mp hy with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hvH
    · exact hzH
    · exact Subgroup.mul_mem _ hvH hzH

theorem twist_not_mem_normalizer {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) (hvv : v * v = 1)
    {g : G} (hg : EscapeChoice A₁ A₂ a t g) (hxT : twist t v ∈ rightConjugate (S : Subgroup G) g) :
    twist t v ∉ Subgroup.normalizer (rightConjugate A₁ g : Set G) := by
  intro hxN
  apply c.not_mem_conj hv hvA hvv hg
  refine c.hyp.choice_mem_of_conj hg c.mem c.t_ne_one ?_ (Or.inl ?_)
  · rw [c.conj_involution hvv]
    exact Subgroup.mul_mem _ hxT (c.t_mem_conj_sylow hg)
  · rw [c.conj_involution hvv]
    exact Subgroup.mul_mem _ hxN (Subgroup.le_normalizer (c.t_mem_conj hg))

theorem twist_not_sq {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) (hvv : v * v = 1) {r : G}
    (hr : r ∈ Subgroup.centralizer ({t} : Set G)) : r * r ≠ twist t v := by
  intro hrr
  have hxx : twist t v * twist t v = 1 := c.twist_mul_self hv (by rw [hvv]; exact A₂.one_mem)
  have hr4 : r ^ (2 ^ 2) = 1 := by
    rw [show (2 ^ 2 : ℕ) = 2 * 2 by norm_num, pow_mul, sq r, hrr, sq, hxx]
  have hpr : IsPGroup 2 (Subgroup.zpowers r) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hr4)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨g, hg, hVT⟩ := c.rechoice _ hpr (Subgroup.zpowers_le.mpr hr)
  have hrT : r ∈ rightConjugate (S : Subgroup G) g := hVT (Subgroup.mem_zpowers r)
  have h₁ := rightConjugate_mul_self_of_mem_pairStabilizer (c.mem_pairStabilizer hrT)
  rw [hrr] at h₁
  apply c.twist_not_mem_normalizer hv hvA hvv hg (hrr ▸ Subgroup.mul_mem _ hrT hrT)
  exact (rightConjugate_eq_self_iff _ _).mp h₁

theorem card_inf_eq_two {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) (hvv : v * v = 1) :
    Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2 := by
  have h := c.hyp
  have htt := c.t_mul_self
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set x := twist t v with hxdef
  have hxx : x * x = 1 := c.twist_mul_self hv (by rw [hvv]; exact A₂.one_mem)
  have hxt : Commute t x := c.twist_commute hv
  have hxz : Commute x z := (c.commute_z_twist hv).symm
  obtain ⟨hpV, hVC⟩ := c.pair_le (c.twist_mem_sylow hv) (c.twist_mem_centralizer hv)
  obtain ⟨g, hg, hVT⟩ := c.rechoice _ hpV hVC
  have hxT : x ∈ rightConjugate (S : Subgroup G) g :=
    hVT (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hzT : z ∈ rightConjugate (S : Subgroup G) g :=
    hVT (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hB := h.conj g
  have hB12 : ¬ (rightConjugate A₁ g) ≤ (rightConjugate A₂ g) := by
    rw [rightConjugate_le_rightConjugate_iff]; exact c.not_le₁₂
  have hB21 : ¬ (rightConjugate A₂ g) ≤ (rightConjugate A₁ g) := by
    rw [rightConjugate_le_rightConjugate_iff]; exact c.not_le₂₁
  have hxs : rightConjugate (rightConjugate A₁ g) x = (rightConjugate A₂ g) := by
    rcases c.mem_pairStabilizer hxT with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact absurd ((rightConjugate_eq_self_iff _ _).mp h₁)
        (c.twist_not_mem_normalizer hv hvA hvv hg hxT)
    · exact h₁
  have hzs := c.z_swap hg hzT
  have hxzN : x * z ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hxs, hzs.2]
  have htB : t ∈ (rightConjugate A₁ g) := c.t_mem_conj hg
  have htT : t ∈ rightConjugate (S : Subgroup G) g := c.t_mem_conj_sylow hg
  set y₀ := t * (x * z) with hy₀
  have hy₀T : y₀ ∈ rightConjugate (S : Subgroup G) g :=
    Subgroup.mul_mem _ htT (Subgroup.mul_mem _ hxT hzT)
  have hy₀N : y₀ ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer htB) hxzN
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hvv
  have hvx : v⁻¹ * x * v = x := by
    rw [hvinv, hxdef, twist]
    have h1 : t * v * t * v = v * (t * v * t) :=
      (c.commute_one_two hv (c.conj_mem_two hv)).eq.symm
    calc v * (v * (t * v * t)) * v = (v * v) * (t * v * t * v) := by group
      _ = v * (t * v * t) := by rw [hvv, one_mul, h1]
  have hvz : v⁻¹ * z * v = z := by
    rw [hvinv, (c.commute_one_two hv c.inf_mem.2).eq, mul_assoc, hvv, mul_one]
  have hconj_mul : ∀ p q : G, v⁻¹ * (p * q) * v = (v⁻¹ * p * v) * (v⁻¹ * q * v) := fun p q =>
    by group
  have hvy₀ : v⁻¹ * y₀ * v = t * z := by
    rw [hy₀, hconj_mul, hconj_mul, c.conj_involution hvv, hvx, hvz]
    calc x * t * (x * z) = t * (x * x) * z := by rw [← hxt.eq]; group
      _ = t * z := by rw [hxx, mul_one]
  have hxz1 : x * z ≠ 1 := by
    intro h1
    apply c.twist_ne_z hv hvA
    calc x = x * z * z := by rw [mul_assoc, c.mul_self, mul_one]
      _ = z := by rw [h1, one_mul]
  have hy₀B₁ : y₀ ∉ (rightConjugate A₁ g) := by
    intro hy₀B
    have hxzB : x * z ∈ (rightConjugate A₁ g) := by
      have := (rightConjugate A₁ g).mul_mem ((rightConjugate A₁ g).inv_mem htB) hy₀B
      rwa [hy₀, inv_mul_cancel_left] at this
    have hxzxz : x * z * (x * z) = 1 := by
      rw [mul_assoc, hxz.symm.left_comm, ← mul_assoc, hxx, one_mul, c.mul_self]
    have htxz : Commute t (x * z) := hxt.mul_right c.commute
    have htne : t ≠ x * z := by
      intro hteq
      apply c.rightConjugate_ne (g := 1)
      rw [rightConjugate_one, rightConjugate_one, ← c.swap.1, hteq]
      refine ((rightConjugate_eq_self_iff _ _).mpr ?_).symm
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (mem_normalizer_one_of_mem_union h.comm (Or.inl hv))
          (mem_normalizer_one_of_mem_union h.comm (Or.inr (c.conj_mem_two hv))))
        (mem_normalizer_one_of_mem_union h.comm (Or.inl c.inf_mem.1))
    let X := commutingPairSubgroup t (x * z) htt hxzxz htxz
    have hXU : (X : Set G) ⊆ (rightConjugate A₁ g : Set G) ∪ (rightConjugate A₂ g) := by
      intro y hy
      rcases mem_commutingPairSubgroup.mp hy with rfl | rfl | rfl | rfl
      · exact Or.inl (rightConjugate A₁ g).one_mem
      · exact Or.inl htB
      · exact Or.inl hxzB
      · exact Or.inl hy₀B
    have hX := hB.fixesOnly_of_card hB12 hB21 hXU
      (by rw [commutingPairSubgroup_card c.t_ne_one hxz1 htne]; norm_num)
    rw [overlapClosure_conj] at hX
    apply c.not_mem_conj hv hvA hvv hg
    refine hX v fun y hy => ?_
    have hCH := hg.centralizer_le
    rcases mem_commutingPairSubgroup.mp hy with rfl | rfl | rfl | rfl
    · rw [mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [c.conj_involution hvv]
      exact hCH (Subgroup.mul_mem _ (c.twist_mem_centralizer hv) htC)
    · rw [hconj_mul, hvx, hvz]
      exact hCH (Subgroup.mul_mem _ (c.twist_mem_centralizer hv) c.z_mem_centralizer)
    · rw [← hy₀, hvy₀]
      exact hCH (Subgroup.mul_mem _ htC c.z_mem_centralizer)
  have hy₀B₂ : y₀ ∉ (rightConjugate A₂ g) := by
    intro hy₀B
    apply hy₀B₁
    have hzy : z⁻¹ * y₀ * z = y₀ := by
      have hzc : Commute z y₀ :=
        (c.commute.symm).mul_right (hxz.symm.mul_right (Commute.refl z))
      rw [mul_assoc, ← hzc.eq, inv_mul_cancel_left]
    rw [← hzs.2, ← hzy]
    exact mem_rightConjugate_conj hy₀B
  have hnf : ∀ b ∈ A₁, ∀ k : G, k⁻¹ * b * k ≠ t * z := by
    intro b hb k hk
    have hbB : g⁻¹ * b * g ∈ (rightConjugate A₁ g : Set G) ∪ (rightConjugate A₂ g) :=
      Or.inl (mem_rightConjugate_conj hb)
    have hm : (g⁻¹ * k * v⁻¹)⁻¹ * (g⁻¹ * b * g) * (g⁻¹ * k * v⁻¹) = y₀ := by
      calc (g⁻¹ * k * v⁻¹)⁻¹ * (g⁻¹ * b * g) * (g⁻¹ * k * v⁻¹)
          = v * (k⁻¹ * b * k) * v⁻¹ := by group
        _ = v * (v⁻¹ * y₀ * v) * v⁻¹ := by rw [hk, hvy₀]
        _ = y₀ := by group
    have hmem := hB.conj_mem_of_mem_normalizer hbB (by rw [hm, coe_conjSylow]; exact hy₀T)
      (Or.inl (by rw [hm]; exact hy₀N))
    rw [hm] at hmem
    rcases hmem with h1 | h1
    · exact hy₀B₁ h1
    · exact hy₀B₂ h1
  have hlt : Nat.card (A₁ ⊓ A₂ : Subgroup G) < 4 := by
    by_contra hcon
    obtain ⟨w, -, hw⟩ := exists_conj_eq_mul_of_card c.isPGroup_inf c.commute_inf htt
      c.normalizes c.inf_mem c.ne_one c.conj_z c.fix' (not_lt.mp hcon)
    apply hnf a c.mem (g * w)
    rw [← hw, ← hg.conj_eq]
    group
  have hle := card_le_two_of_lt_four c.isPGroup_inf hlt
  have hge : 2 ≤ Nat.card (A₁ ⊓ A₂ : Subgroup G) := by
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr
      (fun hbot => c.ne_one (by rw [← Subgroup.mem_bot, ← hbot]; exact c.inf_mem))
    omega
  omega

theorem not_dihedral (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) {v : G} (hv : v ∈ A₁)
    (hvA : v ∉ A₂) (hvv : v * v = 1) :
    ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) := by
  intro hd
  obtain ⟨g, hg⟩ := c.choice
  exact hD ⟨⟨a, c.mem, g, hg.conj_eq ▸ c.sylow, hg.conj_eq ▸ c.swap.1⟩, hd,
    c.card_inf_eq_two hv hvA hvv⟩

theorem not_dihedral_two (hnd : ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁)) :
    ¬ (IsDihedralTwoGroup A₂ ∨ IsSemidihedralTwoGroup A₂) := fun hd =>
  hnd (dihedral_of_mulEquiv
    ((rightConjugateEquiv A₁ t).trans (MulEquiv.subgroupCongr c.swap.1)).symm hd)

theorem card_two : Nat.card A₂ = Nat.card A₁ := by
  rw [← c.swap.1, rightConjugate_card]

end CaseTwo

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
