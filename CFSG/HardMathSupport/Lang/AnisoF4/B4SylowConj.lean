module

public import CFSG.HardMathSupport.Lang.AnisoE6.PlaneConjGen

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Lang.AnisoE6
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_conj_plane_le_of_factorization {G : Type*} [Group G] [Finite G] {P : ℕ}
    [hP : Fact P.Prime] (hT : SylowTorus G P 2) (X : Subgroup G)
    (hv : (Nat.card G).factorization P ≤ (Nat.card X).factorization P) {e : G} (he : e ∈ X)
    (heo : orderOf e = P) {E₀ : Subgroup G} (hE₀ : IsElemAbelian P E₀)
    (hE₀c : Nat.card E₀ = P ^ 2) :
    ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ X ∧
      e ∈ E₀.map (MulAut.conj g).toMonoidHom := by
  classical
  have hzp : IsPGroup P (Subgroup.zpowers (⟨e, he⟩ : X)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    rw [pow_one]
    exact heo
  obtain ⟨Sx, hSx⟩ := hzp.exists_le_sylow
  set Q : Subgroup G := (Sx : Subgroup X).map X.subtype with hQ
  have hXG : (Nat.card X).factorization P ≤ (Nat.card G).factorization P := by
    exact (Nat.factorization_le_iff_dvd (Nat.card_pos (α := X)).ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card X) P
  have hQc : Nat.card Q = P ^ (Nat.card G).factorization P := by
    rw [hQ, Subgroup.card_map_of_injective X.subtype_injective, Sylow.card_eq_multiplicity,
      le_antisymm hXG hv]
  set SQ : Sylow P G := Sylow.ofCard Q hQc with hSQ
  have hSQQ : (SQ : Subgroup G) = Q := Sylow.coe_ofCard Q hQc
  have hpg : IsPGroup P E₀ := IsPGroup.of_card (n := 2) hE₀c
  obtain ⟨S₀, hS₀⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ SQ
  set F' : Subgroup G := E₀.map (MulAut.conj g).toMonoidHom with hF'
  have hF'S : F' ≤ SQ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x ∈ (S₀ : Subgroup G) := hS₀ hx
    have h2 : g * x * g⁻¹ ∈ ((g • S₀ : Sylow P G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx0, by simp [MulAut.smul_def]⟩
    rw [hg] at h2
    exact h2
  have hSab : ∀ a ∈ (SQ : Subgroup G), ∀ b ∈ (SQ : Subgroup G), a * b = b * a :=
    fun a ha b hb => mul_comm_of_sylowTorus hT SQ.isPGroup' ha hb
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ (SQ : Subgroup G) ∧ x ^ P = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hSab a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩ : IsElemAbelian P Ω :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hSab a a.2.1 b b.2.1), fun x hx => hx.2⟩
  have hF'Ω : F' ≤ Ω := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hF'S ⟨x, hx, rfl⟩, ?_⟩
    rw [← map_pow, hE₀.2 x hx, map_one]
  have hcardF' : Nat.card F' = P ^ 2 := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have hΩc : Nat.card Ω ≤ Nat.card F' := by
    rw [hcardF']
    exact hT.rank_le hP.out hΩ
  have hEq : F' = Ω := Subgroup.eq_of_le_of_card_ge hF'Ω hΩc
  have heQ : e ∈ Q := ⟨⟨e, he⟩, hSx (Subgroup.mem_zpowers _), rfl⟩
  have hep : e ^ P = 1 := heo ▸ pow_orderOf_eq_one e
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    have : x ∈ (SQ : Subgroup G) := hF'S hx
    rw [hSQQ] at this
    obtain ⟨y, -, rfl⟩ := this
    exact y.2
  · rw [← hF', hEq]
    exact ⟨by rw [hSQQ]; exact heQ, hep⟩

end CFSG.HardMathSupport.Lang.AnisoF4
