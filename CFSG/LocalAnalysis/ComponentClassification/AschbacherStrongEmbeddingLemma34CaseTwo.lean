module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Choice

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

@[expose] def twist (t v : G) : G := v * (t * v * t)

structure CaseTwo (S : Sylow 2 G) (A₁ A₂ : Subgroup G) (a t z : G) : Prop where
  hyp : Hyp S A₁ A₂
  not_le₁₂ : ¬ A₁ ≤ A₂
  not_le₂₁ : ¬ A₂ ≤ A₁
  mem : a ∈ A₁
  orderOf_eq : orderOf a = 2
  sylow : t ∈ (S : Subgroup G)
  choice : ∃ g : G, EscapeChoice A₁ A₂ a t g
  rechoice : EscapeRechoice S A₁ A₂ a t
  inf_mem : z ∈ A₁ ⊓ A₂
  ne_one : z ≠ 1
  mul_self : z * z = 1
  commute : Commute t z
  fix : ∀ p ∈ A₁ ⊓ A₂, Commute t p → p = 1 ∨ p = z

namespace CaseTwo

variable {a t z : G} (c : CaseTwo S A₁ A₂ a t z)
include c

theorem a_ne_one : a ≠ 1 := (orderOf_eq_prime_iff.mp c.orderOf_eq).2

theorem t_mul_self : t * t = 1 := by
  obtain ⟨g, hg⟩ := c.choice
  have haa : a * a = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp c.orderOf_eq).1
  rw [← hg.conj_eq]
  calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
    _ = 1 := by rw [haa]; group

theorem t_ne_one : t ≠ 1 := by
  obtain ⟨g, hg⟩ := c.choice
  intro h1
  apply c.a_ne_one
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [hg.conj_eq, h1]; group

theorem swap : rightConjugate A₁ t = A₂ ∧ rightConjugate A₂ t = A₁ := by
  obtain ⟨g, hg⟩ := c.choice
  exact c.hyp.escape_swap c.not_le₁₂ c.not_le₂₁ hg c.mem c.a_ne_one c.sylow

theorem conj_mem_two {v : G} (hv : v ∈ A₁) : t * v * t ∈ A₂ :=
  conj_mem_two_of_swap c.t_mul_self c.swap.1 hv

theorem conj_mem_one {v : G} (hv : v ∈ A₂) : t * v * t ∈ A₁ :=
  conj_mem_two_of_swap c.t_mul_self c.swap.2 hv

theorem commute_one_two {b d : G} (hb : b ∈ A₁) (hd : d ∈ A₂) : Commute b d :=
  commute_of_comm c.hyp.comm hb hd

theorem z_mem_centralizer : z ∈ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr c.commute.eq.symm

theorem z_mem_sylow : z ∈ (S : Subgroup G) := c.hyp.le_one c.inf_mem.1

theorem conj_z : t * z * t = z := by
  rw [c.commute.eq, mul_assoc, c.t_mul_self, mul_one]

theorem fix' : ∀ p ∈ A₁ ⊓ A₂, t * p * t = p → p = 1 ∨ p = z := by
  intro p hp hpt
  refine c.fix p hp ?_
  change t * p = p * t
  calc t * p = t * p * t * t := by rw [mul_assoc (t * p), c.t_mul_self, mul_one]
    _ = p * t := by rw [hpt]

theorem normalizes : ∀ p ∈ A₁ ⊓ A₂, t * p * t ∈ A₁ ⊓ A₂ := fun _ hp =>
  ⟨c.conj_mem_one hp.2, c.conj_mem_two hp.1⟩

theorem commute_inf : ∀ x ∈ A₁ ⊓ A₂, ∀ y ∈ A₁ ⊓ A₂, Commute x y := fun _ hx _ hy =>
  c.commute_one_two hx.1 hy.2

theorem isPGroup_inf : IsPGroup 2 (A₁ ⊓ A₂ : Subgroup G) :=
  S.isPGroup'.to_le (inf_le_left.trans c.hyp.le_one)

theorem twist_commute {v : G} (hv : v ∈ A₁) : Commute t (twist t v) := by
  have h1 : v * (t * v * t) = t * v * t * v := (c.commute_one_two hv (c.conj_mem_two hv)).eq
  change t * (v * (t * v * t)) = v * (t * v * t) * t
  calc t * (v * (t * v * t)) = t * v * t * v * t := by group
    _ = v * (t * v * t) * t := by rw [← h1]

theorem twist_mem_centralizer {v : G} (hv : v ∈ A₁) :
    twist t v ∈ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (c.twist_commute hv).eq.symm

theorem twist_mem_sylow {v : G} (hv : v ∈ A₁) : twist t v ∈ (S : Subgroup G) :=
  Subgroup.mul_mem _ (c.hyp.le_one hv) (c.hyp.le_two (c.conj_mem_two hv))

theorem twist_mul {b d : G} (hb : b ∈ A₁) (hd : d ∈ A₁) :
    twist t (b * d) = twist t b * twist t d := by
  have htt := c.t_mul_self
  have hdb : d * (t * b * t) = t * b * t * d := (c.commute_one_two hd (c.conj_mem_two hb)).eq
  change b * d * (t * (b * d) * t) = b * (t * b * t) * (d * (t * d * t))
  calc b * d * (t * (b * d) * t) = b * (d * (t * b * t)) * (t * d * t) := by
        rw [show t * (b * d) * t = t * b * (t * t) * d * t by rw [htt, mul_one]; group]
        group
    _ = b * (t * b * t * d) * (t * d * t) := by rw [hdb]
    _ = b * (t * b * t) * (d * (t * d * t)) := by group

theorem twist_mul_self_eq {v : G} (hv : v ∈ A₁) :
    twist t v * twist t v = v * v * (t * (v * v) * t) := by
  rw [← c.twist_mul hv hv]
  rfl

theorem commute_z_twist {v : G} (hv : v ∈ A₁) : Commute z (twist t v) :=
  ((c.commute_one_two hv c.inf_mem.2).symm).mul_right
    (c.commute_one_two c.inf_mem.1 (c.conj_mem_two hv))

theorem twist_mul_self_mem {v : G} (hv : v ∈ A₁) (hv2 : v * v ∈ A₂) :
    twist t v * twist t v ∈ A₁ ⊓ A₂ := by
  rw [c.twist_mul_self_eq hv]
  have hvv : v * v ∈ A₁ ⊓ A₂ := ⟨A₁.mul_mem hv hv, hv2⟩
  exact (A₁ ⊓ A₂).mul_mem hvv (c.normalizes _ hvv)

theorem twist_not_mem {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) : twist t v ∉ A₂ := by
  intro hx
  apply hvA
  have := A₂.mul_mem hx (A₂.inv_mem (c.conj_mem_two hv))
  rwa [twist, mul_inv_cancel_right] at this

theorem twist_ne_one {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) : twist t v ≠ 1 := fun h1 =>
  c.twist_not_mem hv hvA (h1 ▸ A₂.one_mem)

theorem twist_ne_z {v : G} (hv : v ∈ A₁) (hvA : v ∉ A₂) : twist t v ≠ z := fun h1 =>
  c.twist_not_mem hv hvA (h1 ▸ c.inf_mem.2)

theorem pair_le {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxC : x ∈ Subgroup.centralizer ({t} : Set G)) :
    IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer ({t} : Set G) := by
  refine ⟨S.isPGroup'.to_le (sup_le (Subgroup.zpowers_le.mpr hxS)
    (Subgroup.zpowers_le.mpr c.z_mem_sylow)), sup_le (Subgroup.zpowers_le.mpr hxC)
    (Subgroup.zpowers_le.mpr c.z_mem_centralizer)⟩

theorem z_swap {g : G} (hg : EscapeChoice A₁ A₂ a t g)
    (hzT : z ∈ rightConjugate (S : Subgroup G) g) :
    rightConjugate (rightConjugate A₁ g) z = rightConjugate A₂ g ∧
      rightConjugate (rightConjugate A₂ g) z = rightConjugate A₁ g :=
  c.hyp.choice_swap c.not_le₁₂ c.not_le₂₁ hg (Or.inl c.inf_mem.1) c.ne_one hzT

theorem rightConjugate_ne {g : G} : rightConjugate A₁ g ≠ rightConjugate A₂ g := fun heq =>
  c.not_le₁₂ ((rightConjugate_le_rightConjugate_iff g).mp (le_of_eq heq))

theorem mem_pairStabilizer {g y : G} (hyT : y ∈ rightConjugate (S : Subgroup G) g) :
    y ∈ pairStabilizer (rightConjugate A₁ g) (rightConjugate A₂ g) := by
  have hB := c.hyp.conj g
  have hB12 : ¬ rightConjugate A₁ g ≤ rightConjugate A₂ g := by
    rw [rightConjugate_le_rightConjugate_iff]; exact c.not_le₁₂
  have hB21 : ¬ rightConjugate A₂ g ≤ rightConjugate A₁ g := by
    rw [rightConjugate_le_rightConjugate_iff]; exact c.not_le₂₁
  exact hB.sylow_le_pairStabilizer hB12 hB21 (by rw [coe_conjSylow]; exact hyT)

theorem twist_mul_self {v : G} (hv : v ∈ A₁) (hv2 : v * v ∈ A₂) :
    twist t v * twist t v = 1 := by
  have hxx := c.twist_mul_self_mem hv hv2
  have hxt : Commute t (twist t v * twist t v) :=
    (c.twist_commute hv).mul_right (c.twist_commute hv)
  rcases c.fix _ hxx hxt with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨hpV, hVC⟩ := c.pair_le (c.twist_mem_sylow hv) (c.twist_mem_centralizer hv)
    obtain ⟨g, hg, hVT⟩ := c.rechoice _ hpV hVC
    have hxT : twist t v ∈ rightConjugate (S : Subgroup G) g :=
      hVT (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hzT : z ∈ rightConjugate (S : Subgroup G) g :=
      hVT (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have h₁ := rightConjugate_mul_self_of_mem_pairStabilizer (c.mem_pairStabilizer hxT)
    rw [h1, (c.z_swap hg hzT).1] at h₁
    exact c.rightConjugate_ne h₁.symm

theorem conj_mul_eq {v w : G} (hv : v ∈ A₁) (hvv : v * v = z) (hw : w ∈ A₁ ⊓ A₂)
    (htw : t * w * t = w * z) :
    (v * w)⁻¹ * t * (v * w) = twist t v * t := by
  obtain ⟨u, hu⟩ : ∃ u, t * v * t = u := ⟨_, rfl⟩
  have huA : u ∈ A₂ := hu ▸ c.conj_mem_two hv
  have hwv : Commute w v := (c.commute_one_two hv hw.2).symm
  have hwu : Commute w u := c.commute_one_two hw.1 huA
  have hzu : Commute z u := c.commute_one_two c.inf_mem.1 huA
  have hwz : Commute w z := c.commute_one_two hw.1 c.inf_mem.2
  have htt := c.t_mul_self
  have htv : t * v = u * t := by rw [← hu, mul_assoc (t * v), htt, mul_one]
  have htw' : t * w = w * z * t := by
    rw [← htw, mul_assoc (t * w), htt, mul_one]
  have key : t * (v * w) = v * w * (twist t v * t) := by
    rw [twist, hu]
    calc t * (v * w) = t * v * w := by rw [mul_assoc]
      _ = u * (t * w) := by rw [htv, mul_assoc]
      _ = u * (w * (z * t)) := by rw [htw', mul_assoc]
      _ = w * (u * (z * t)) := hwu.symm.left_comm _
      _ = w * (z * (u * t)) := by rw [hzu.symm.left_comm]
      _ = z * (w * (u * t)) := hwz.left_comm _
      _ = v * v * (w * (u * t)) := by rw [hvv]
      _ = v * (w * (v * (u * t))) := by rw [mul_assoc, hwv.symm.left_comm]
      _ = v * w * (v * u * t) := by simp only [mul_assoc]
  rw [mul_assoc, key, inv_mul_cancel_left]

theorem exists_involution : ∃ v ∈ A₁, v ∉ A₂ ∧ v * v = 1 := by
  by_contra hcon
  have hall : ∀ v ∈ A₁, v * v = 1 → v ∈ A₂ := fun v hv hvv => by
    by_contra hvA
    exact hcon ⟨v, hv, hvA, hvv⟩
  have h := c.hyp
  obtain ⟨E, hEA, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) A₁
  have hEI : E ≤ A₁ ⊓ A₂ := fun e he =>
    ⟨hEA he, hall e (hEA he) (by rw [← sq]; exact hEel.2 e he)⟩
  have hrI : 2 ≤ CFSG.Open.pRank 2 (A₁ ⊓ A₂ : Subgroup G) :=
    h.rank_one.trans (CFSG.SectionRank.le_pRank (by norm_num) hEI hEel hEcard)
  have hI4 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 4 :=
    card_eq_four_of_fixed_two c.isPGroup_inf c.commute_inf c.t_mul_self c.normalizes
      c.inf_mem c.ne_one c.conj_z c.fix' hrI
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A₁ := Nat.pow_le_pow_right (by norm_num) h.rank_one
  have hEeq : E = A₁ ⊓ A₂ := Subgroup.eq_of_le_of_card_ge hEI (by omega)
  have hIsq : ∀ p ∈ A₁ ⊓ A₂, p * p = 1 := fun p hp => by
    rw [← sq]; exact hEel.2 p (hEeq ▸ hp)
  obtain ⟨v, hv, hvA, hv2⟩ := exists_mem_sq_mem_of_not_le
    (S.isPGroup'.to_le h.le_one) c.not_le₁₂
  have hvvI : v * v ∈ A₁ ⊓ A₂ := ⟨A₁.mul_mem hv hv, hv2⟩
  have hvvz : v * v = z := by
    have hx := c.twist_mul_self hv hv2
    rw [c.twist_mul_self_eq hv] at hx
    have hinv : t * (v * v) * t = v * v := by
      have h1 := eq_inv_of_mul_eq_one_right hx
      rwa [inv_eq_of_mul_eq_one_left (hIsq _ hvvI)] at h1
    rcases c.fix' _ hvvI hinv with h1 | h1
    · exact absurd (hall v hv h1) hvA
    · exact h1
  obtain ⟨w, hwI, hwt⟩ := exists_conj_eq_mul_of_card c.isPGroup_inf c.commute_inf c.t_mul_self
    c.normalizes c.inf_mem c.ne_one c.conj_z c.fix' (by omega)
  have hww := hIsq w hwI
  have htw : t * w * t = w * z := by
    have htt := c.t_mul_self
    have : t * w = w * (t * z) := by
      rw [← hwt]
      group
    rw [this, mul_assoc, c.conj_z]
  have hwvA : v * w ∈ A₁ := A₁.mul_mem hv hwI.1
  have hwv : Commute w v := (c.commute_one_two hv hwI.2).symm
  have hvw2 : v * w * (v * w) = z := by
    rw [mul_assoc, hwv.left_comm, ← mul_assoc, hvvz, hww, mul_one]
  have htww : twist t w = z := by
    change w * (t * w * t) = z
    rw [htw, ← mul_assoc, hww, one_mul]
  obtain ⟨hpV, hVC⟩ := c.pair_le (c.twist_mem_sylow hv) (c.twist_mem_centralizer hv)
  obtain ⟨g, hg, hVT⟩ := c.rechoice _ hpV hVC
  have hxT : twist t v ∈ rightConjugate (S : Subgroup G) g :=
    hVT (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hzT : z ∈ rightConjugate (S : Subgroup G) g :=
    hVT (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨v₀, hv₀, hv₀z, hxN, hx₀T⟩ : ∃ v₀ ∈ A₁, v₀ * v₀ = z ∧
      twist t v₀ ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G) ∧
      twist t v₀ ∈ rightConjugate (S : Subgroup G) g := by
    rcases c.mem_pairStabilizer hxT with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
    · exact ⟨v, hv, hvvz, (rightConjugate_eq_self_iff _ _).mp h₁, hxT⟩
    · refine ⟨v * w, hwvA, hvw2, ?_, ?_⟩
      · rw [c.twist_mul hv hwI.1, htww, ← rightConjugate_eq_self_iff, ← rightConjugate_mul,
          h₁, (c.z_swap hg hzT).2]
      · rw [c.twist_mul hv hwI.1, htww]
        exact Subgroup.mul_mem _ hxT hzT
  have htB : t ∈ rightConjugate A₁ g := hg.conj_eq ▸ mem_rightConjugate_conj c.mem
  have htT : t ∈ rightConjugate (S : Subgroup G) g :=
    Subgroup.map_mono h.le_one htB
  have hmem : v₀ * w ∈ rightConjugate (overlapClosure A₁ A₂) g := by
    refine h.choice_mem_of_conj hg c.mem c.t_ne_one ?_ (Or.inl ?_)
    · rw [c.conj_mul_eq hv₀ hv₀z hwI htw]
      exact Subgroup.mul_mem _ hx₀T htT
    · rw [c.conj_mul_eq hv₀ hv₀z hwI htw]
      exact Subgroup.mul_mem _ hxN (Subgroup.le_normalizer htB)
  have hv₀w2 : (v₀ * w) * (v₀ * w) = z := by
    have hwv₀ : Commute w v₀ := (c.commute_one_two hv₀ hwI.2).symm
    rw [mul_assoc, hwv₀.left_comm, ← mul_assoc, hv₀z, hww, mul_one]
  have hord : orderOf (v₀ * w) = 2 ^ (1 + 1) := by
    apply orderOf_eq_prime_pow
    · rw [pow_one, sq, hv₀w2]
      exact c.ne_one
    · have h4 : (v₀ * w) ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq (v₀ * w), hv₀w2, sq, c.mul_self]
      norm_num
      exact h4
  refine h.choice_not_le c.not_le₁₂ c.not_le₂₁ hg (X := Subgroup.zpowers (v₀ * w))
    (fun y hy => Or.inl ((Subgroup.zpowers_le.mpr (A₁.mul_mem hv₀ hwI.1)) hy)) ?_
    (Subgroup.zpowers_le.mpr hmem)
  rw [Nat.card_zpowers, hord]
  norm_num

end CaseTwo

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
