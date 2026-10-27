module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Action
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm

public section

namespace GL83.PiGen

open Equiv Equiv.Perm GL83.CompFam

variable {X : Type*} [Group X] {K A : Subgroup X}

theorem isElemAbelian_range {p : ℕ} {G' : Type*} [Group G'] (hA : CFSG.Open.IsElemAbelian p A)
    (f : A →* G') : CFSG.Open.IsElemAbelian p f.range := by
  have := hA.1
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    refine Subtype.ext ?_
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, mul_comm' a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]

theorem le_centGenI_of_perm {p : ℕ} [Group.IsPerfect K]
    (hA : A ≤ Subgroup.normalizer (K : Set X)) (hodd : Odd (Nat.card (Subgroup.center K)))
    {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hgen : alternatingGroup (Fin n) ≤
      Subgroup.closure (Y2 p (permHom hA hn hn6 e).range)) :
    K ≤ centGenI p A K := by
  classical
  set π := permHom hA hn hn6 e with hπ
  set R := π.range with hR
  let 𝒴 : Set (K ⧸ Subgroup.center K) := {y | (e y : Perm (Fin n)) ∈ Y2 p R}
  let T : Set (alternatingGroup (Fin n)) := {z | (z : Perm (Fin n)) ∈ Y2 p R}
  have hTcl : Subgroup.closure T = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    have h1 : (Subgroup.closure T).map (alternatingGroup (Fin n)).subtype =
        Subgroup.closure (Y2 p R) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hy
        exact ⟨⟨y, hy.1⟩, hy, rfl⟩
    have h2 : (z : Perm (Fin n)) ∈ (Subgroup.closure T).map (alternatingGroup (Fin n)).subtype := by
      rw [h1]
      exact hgen z.2
    obtain ⟨t, ht, hzt⟩ := h2
    have : t = z := Subtype.ext hzt
    rwa [this] at ht
  have h𝒴 : Subgroup.closure 𝒴 = ⊤ := by
    have h1 : (Subgroup.closure 𝒴).map e.toMonoidHom = Subgroup.closure T := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        refine ⟨e.symm z, ?_, by simp⟩
        show (e (e.symm z) : Perm (Fin n)) ∈ Y2 p R
        rw [MulEquiv.apply_symm_apply]
        exact hz
    rw [hTcl] at h1
    have h2 : (Subgroup.closure 𝒴).map e.toMonoidHom = (⊤ : Subgroup _).map e.toMonoidHom := by
      rw [h1]
      ext z
      simp only [Subgroup.mem_top, Subgroup.mem_map, true_iff]
      exact ⟨e.symm z, trivial, by simp⟩
    exact Subgroup.map_injective e.injective h2
  have h2 : ∀ y ∈ 𝒴, ∃ j : ℕ, y ^ (2 ^ j) = 1 := by
    intro y hy
    obtain ⟨-, ⟨j, hj⟩, -⟩ := hy
    refine ⟨j, e.injective ?_⟩
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using hj)
  refine le_centGenI_of_closure Group.IsPerfect.commutator_eq_top hodd 𝒴 h𝒴 h2 ?_
  intro y hy
  obtain ⟨-, -, E, hER, hEi, hcomm⟩ := hy
  let E' : Subgroup A := E.comap π
  refine ⟨E'.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 : Nat.card E' * E'.index = Nat.card A := Subgroup.card_mul_index E'
    have h2 : E'.index = E.relIndex R := Subgroup.index_comap E π
    have h3 : E.relIndex R * Nat.card E = Nat.card R := by
      have := Subgroup.relIndex_mul_card (H := E) (K := R)
      rwa [inf_eq_left.2 hER] at this
    have h4 : E.relIndex R ≤ p := by
      have hpos : 0 < Nat.card E := Nat.card_pos
      by_contra hlt
      have : p * Nat.card E < E.relIndex R * Nat.card E :=
        Nat.mul_lt_mul_of_pos_right (not_le.1 hlt) hpos
      omega
    rw [Subgroup.card_map_of_injective A.subtype_injective, ← h1, h2]
    calc Nat.card E' * E.relIndex R ≤ Nat.card E' * p := Nat.mul_le_mul_left _ h4
      _ = p * Nat.card E' := mul_comm _ _
  · intro g hg x hx
    obtain ⟨a, haE, rfl⟩ := hg
    obtain ⟨y₁, hy₁, hspec⟩ := permHom_spec hA hn hn6 e a x
    have hπa : π a ∈ E := haE
    have hc := hcomm (π a) hπa
    have h1 : (e (QuotientGroup.mk y₁) : Perm (Fin n)) = (e y : Perm (Fin n)) := by
      rw [← hspec, hx]
      calc π a * (e y : Perm (Fin n)) * (π a)⁻¹ = (e y : Perm (Fin n)) * π a * (π a)⁻¹ := by
            rw [← hc]
        _ = (e y : Perm (Fin n)) := by group
    have h2 : (QuotientGroup.mk y₁ : K ⧸ Subgroup.center K) = y :=
      e.injective (Subtype.ext h1)
    have h3 : x⁻¹ * y₁ ∈ Subgroup.center K :=
      QuotientGroup.eq.1 (hx.trans h2.symm)
    refine ⟨x⁻¹ * y₁, h3, ?_⟩
    show (a : X) * x * (a : X)⁻¹ = (x : X) * ((x⁻¹ * y₁ : K) : X)
    rw [← hy₁]
    simp

theorem le_centGenI_of_orbits {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) [Group.IsPerfect K]
    (hA : A ≤ Subgroup.normalizer (K : Set X)) (hApg : IsPGroup p A)
    (hodd : Odd (Nat.card (Subgroup.center K))) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (hnp : n % p = 2)
    (horb : ∀ ω : Fin n, Nat.card (MulAction.orbit (permHom hA hn hn6 e).range ω) ≤ p) :
    K ≤ centGenI p A K := by
  refine le_centGenI_of_perm hA hodd hn hn6 e ?_
  have hR : IsPGroup p (permHom hA hn hn6 e).range :=
    hApg.of_surjective (permHom hA hn hn6 e).rangeRestrict
      (permHom hA hn hn6 e).rangeRestrict_surjective
  exact alternatingGroup_le_closure_Y2 hp3 hR (by simpa using hn) (by simpa using hnp) horb

end GL83.PiGen
