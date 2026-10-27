module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem isPGroup_of_isElemAbelian' {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem exists_conj_eq_of_sylowTorus {G : Type*} [Group G] [Finite G] {p m : ℕ} [hp : Fact p.Prime]
    (h : SylowTorus G p m) {E E' : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ m)
    (hE' : IsElemAbelian p E') (hEc' : Nat.card E' = p ^ m) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom = E' := by
  classical
  have hpg : ∀ {Q : Subgroup G}, IsElemAbelian p Q → IsPGroup p Q := fun {Q} hQ =>
    isPGroup_of_isElemAbelian' hQ
  obtain ⟨S, hS⟩ := (hpg hE).exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := (hpg hE').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S₀
  have hSab : ∀ a ∈ (S₀ : Subgroup G), ∀ b ∈ (S₀ : Subgroup G), a * b = b * a :=
    fun a ha b hb => mul_comm_of_sylowTorus h S₀.isPGroup' ha hb
  set F' : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hF'
  have hF'S : F' ≤ S₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x ∈ (S : Subgroup G) := hS hx
    have h2 : g * x * g⁻¹ ∈ ((g • S : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx0, by simp [MulAut.smul_def]⟩
    rw [hg] at h2
    exact h2
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ (S₀ : Subgroup G) ∧ x ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hSab a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩ : IsElemAbelian p Ω :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hSab a a.2.1 b b.2.1), fun x hx => hx.2⟩
  have hE'Ω : E' ≤ Ω := fun x hx => ⟨hS₀ hx, hE'.2 x hx⟩
  have hF'Ω : F' ≤ Ω := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hF'S ⟨x, hx, rfl⟩, ?_⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hΩc : Nat.card Ω ≤ Nat.card E' := by
    rw [hEc']
    exact h.rank_le hp.out hΩ
  have hEq : E' = Ω := Subgroup.eq_of_le_of_card_ge hE'Ω hΩc
  have hF'le : F' ≤ E' := hEq ▸ hF'Ω
  have hcardF' : Nat.card F' = Nat.card E' := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc, hEc']
  exact ⟨g, (Subgroup.eq_of_le_of_card_ge hF'le hcardF'.ge)⟩

theorem exists_plane_containing_of_sylowTorus {G : Type*} [Group G] {p m : ℕ} [hp : Fact p.Prime]
    (h : SylowTorus G p m) {e : G} (he : orderOf e = p) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ m ∧ e ∈ E := by
  obtain ⟨T, E, hT, hconj, hET, hTE, hEel, hEc⟩ := h.exists_torus
  have hP : IsPGroup p (Subgroup.zpowers e) := by
    have : IsPGroup p (Subgroup.zpowers e) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, he, pow_one]
    exact this
  obtain ⟨g, hg⟩ := hconj _ hP
  have heT : e ∈ T.map (MulAut.conj g).toMonoidHom := hg (Subgroup.mem_zpowers e)
  obtain ⟨t, ht, hte⟩ := heT
  have hep : e ^ p = 1 := he ▸ pow_orderOf_eq_one e
  have htp : t ^ p = 1 := by
    have h1 : (MulAut.conj g).toMonoidHom (t ^ p) = 1 := by
      rw [map_pow]
      exact hte ▸ hep
    exact (MulAut.conj g).injective (by simpa using h1)
  have htE : t ∈ E := hTE t ht htp
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, ?_, ⟨t, htE, hte⟩⟩
  · refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hxa, ← hyb]
      have hxy : x * y = y * x := congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
        _ = g * (y * x) * g⁻¹ := by rw [hxy]
        _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEel.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEc]

end CFSG.HardMathSupport.Lang.AnisoE6
