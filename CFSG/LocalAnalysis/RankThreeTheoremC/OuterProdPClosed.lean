module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.AutL2Facts

private theorem mem_sylow_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hS : (S : Subgroup G).Normal) {x : G} {k : ℕ} (hx : x ^ p ^ k = 1) :
    x ∈ (S : Subgroup G) := by
  have hz : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨T, hT⟩ := hz.exists_le_sylow
  rw [← S.is_maximal' T.isPGroup' (S.isPGroup'.le_sylow_of_normal T)]
  exact hT (Subgroup.mem_zpowers x)

private theorem exists_pow_eq_one_of_mem {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (hH : IsPGroup p H) {x : G} (hx : x ∈ H) : ∃ k : ℕ, x ^ p ^ k = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

variable {L : Type*} [Group L]

private theorem simpleCentreless_of_simple [IsSimpleGroup L] (hLnab : ∃ a b : L, a * b ≠ b * a) :
    SimpleCentreless L := by
  obtain ⟨a, b, hab⟩ := hLnab
  refine ⟨fun N _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N, fun z hz => ?_, ⟨a, ?_⟩⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · have hz' : z ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g => (hz g).symm
      rwa [h, Subgroup.mem_bot] at hz'
    · have ha : a ∈ Subgroup.center L := h ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  · rintro rfl
    exact hab (by rw [one_mul, mul_one])

variable [Finite L]

private theorem inner_le_presSub : inner (L × L) ≤ presSub L := by
  rintro _ ⟨g, rfl⟩
  exact ⟨fun s => by simp [MulAut.conj_apply], fun t => by simp [MulAut.conj_apply]⟩

private theorem mem_presSub_or_swaps (hS : SimpleCentreless L) (φ : MulAut (L × L)) :
    φ ∈ presSub L ∨ ((∀ s, (φ (s, 1)).1 = 1) ∧ ∀ t, (φ (1, t)).2 = 1) := by
  rcases hS.fst_or φ with h | h
  · exact Or.inl ⟨h, hS.snd_of_fst h⟩
  · exact Or.inr ⟨h, hS.snd_of_swap h⟩

private theorem mul_mem_presSub_of_swaps {φ ψ : MulAut (L × L)}
    (hφ : (∀ s, (φ (s, 1)).1 = 1) ∧ ∀ t, (φ (1, t)).2 = 1)
    (hψ : (∀ s, (ψ (s, 1)).1 = 1) ∧ ∀ t, (ψ (1, t)).2 = 1) : φ * ψ ∈ presSub L := by
  refine ⟨fun s => ?_, fun t => ?_⟩
  · rw [MulAut.mul_apply, show ψ (s, 1) = (1, (ψ (s, 1)).2) from Prod.ext (hψ.1 s) rfl]
    exact hφ.2 _
  · rw [MulAut.mul_apply, show ψ (1, t) = ((ψ (1, t)).1, 1) from Prod.ext rfl (hψ.2 t)]
    exact hφ.1 _

private theorem swaps_mul_of_mem_presSub {φ ψ : MulAut (L × L)} (hφ : φ ∈ presSub L)
    (hψ : (∀ s, (ψ (s, 1)).1 = 1) ∧ ∀ t, (ψ (1, t)).2 = 1) :
    (∀ s, ((φ * ψ) (s, 1)).1 = 1) ∧ ∀ t, ((φ * ψ) (1, t)).2 = 1 := by
  refine ⟨fun s => ?_, fun t => ?_⟩
  · rw [MulAut.mul_apply, show ψ (s, 1) = (1, (ψ (s, 1)).2) from Prod.ext (hψ.1 s) rfl]
    exact hφ.2 _
  · rw [MulAut.mul_apply, show ψ (1, t) = ((ψ (1, t)).1, 1) from Prod.ext rfl (hψ.2 t)]
    exact hφ.1 _

private theorem swaps_pow_odd {φ : MulAut (L × L)}
    (hφ : (∀ s, (φ (s, 1)).1 = 1) ∧ ∀ t, (φ (1, t)).2 = 1) (k : ℕ) :
    (∀ s, ((φ ^ (2 * k + 1)) (s, 1)).1 = 1) ∧ ∀ t, ((φ ^ (2 * k + 1)) (1, t)).2 = 1 := by
  rw [pow_succ, pow_mul]
  refine swaps_mul_of_mem_presSub (pow_mem ?_ k) hφ
  rw [sq]
  exact mul_mem_presSub_of_swaps hφ hφ

private theorem not_swaps_of_mem_presSub (hS : SimpleCentreless L) {φ : MulAut (L × L)}
    (hφ : φ ∈ presSub L) (hsw : (∀ s, (φ (s, 1)).1 = 1) ∧ ∀ t, (φ (1, t)).2 = 1) : False := by
  obtain ⟨s, hs⟩ := hS.nontriv
  have h1 : φ (s, 1) = φ 1 := by
    rw [map_one]
    exact Prod.ext (hsw.1 s) (hφ.1 s)
  exact hs (by simpa using congrArg Prod.fst (φ.injective h1))

private theorem mem_presSub_of_pow_mem_inner (hS : SimpleCentreless L) {φ : MulAut (L × L)}
    {n : ℕ} (hn : Odd n) (h : φ ^ n ∈ inner (L × L)) : φ ∈ presSub L := by
  rcases mem_presSub_or_swaps hS φ with hφ | hφ
  · exact hφ
  · obtain ⟨k, rfl⟩ := hn
    exact (not_swaps_of_mem_presSub hS (inner_le_presSub h) (swaps_pow_odd hφ k)).elim

private theorem mem_inner_of_fstHom_sndHom (φ : presSub L) (h1 : fstHom φ ∈ inner L)
    (h2 : sndHom φ ∈ inner L) : (φ : MulAut (L × L)) ∈ inner (L × L) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(a, b), MulEquiv.ext fun x => ?_⟩
  obtain ⟨s, t⟩ := x
  rw [presSub_apply, ← ha, ← hb]
  simp [MulAut.conj_apply]

private theorem fstHom_sndHom_mem_inner {φ : presSub L}
    (h : (φ : MulAut (L × L)) ∈ inner (L × L)) : fstHom φ ∈ inner L ∧ sndHom φ ∈ inner L := by
  obtain ⟨g, hg⟩ := h
  refine ⟨⟨g.1, MulEquiv.ext fun s => ?_⟩, ⟨g.2, MulEquiv.ext fun t => ?_⟩⟩
  · rw [fstHom_apply, ← hg]
    simp [MulAut.conj_apply]
  · rw [sndHom_apply, ← hg]
    simp [MulAut.conj_apply]

theorem sylow_normal_outer_prod_of_simple {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    (hLnab : ∃ a b : L, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : ∀ S : Sylow p (CFSG.ComponentClassification.OuterAutomorphisms.Outer L),
      (S : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer L)).Normal) :
    ∀ S : Sylow p (CFSG.ComponentClassification.OuterAutomorphisms.Outer (L × L)),
      (S : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer (L × L))).Normal := by
  have hS := simpleCentreless_of_simple hLnab
  have hodd : ∀ k : ℕ, Odd (p ^ k) := fun k => (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p (Outer L)))
  have hS₀ := h S₀
  let T : Subgroup (MulAut L) := (S₀ : Subgroup (Outer L)).comap (QuotientGroup.mk' (inner L))
  let R : Subgroup (Outer (L × L)) := (T.comap fstHom ⊓ T.comap sndHom).map
    ((QuotientGroup.mk' (inner (L × L))).comp (presSub L).subtype)
  have hRp : IsPGroup p R := by
    rintro ⟨_, φ, ⟨h1, h2⟩, rfl⟩
    have h1' : QuotientGroup.mk' (inner L) (fstHom φ) ∈ (S₀ : Subgroup (Outer L)) := h1
    have h2' : QuotientGroup.mk' (inner L) (sndHom φ) ∈ (S₀ : Subgroup (Outer L)) := h2
    obtain ⟨k₁, hk₁⟩ := exists_pow_eq_one_of_mem S₀.isPGroup' h1'
    obtain ⟨k₂, hk₂⟩ := exists_pow_eq_one_of_mem S₀.isPGroup' h2'
    have hin := mem_inner_of_fstHom_sndHom (φ ^ p ^ (k₁ + k₂))
      ((QuotientGroup.eq_one_iff _).mp (by rw [map_pow, QuotientGroup.mk_pow, pow_add, pow_mul,
        ← QuotientGroup.mk'_apply, hk₁, one_pow]))
      ((QuotientGroup.eq_one_iff _).mp (by rw [map_pow, QuotientGroup.mk_pow, pow_add, pow_mul',
        ← QuotientGroup.mk'_apply, hk₂, one_pow]))
    refine ⟨k₁ + k₂, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hin
  have hRmax : ∀ (x : Outer (L × L)) (k : ℕ), x ^ p ^ k = 1 → x ∈ R := by
    intro x k hx
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (L × L)) x
    have hαk : α ^ p ^ k ∈ inner (L × L) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hx
    have hα : α ∈ presSub L := mem_presSub_of_pow_mem_inner hS (hodd k) hαk
    have hin := fstHom_sndHom_mem_inner (φ := ⟨α, hα⟩ ^ p ^ k) hαk
    refine ⟨⟨α, hα⟩, ⟨?_, ?_⟩, rfl⟩
    · refine mem_sylow_of_pow_eq_one S₀ hS₀ (k := k) ?_
      rw [← map_pow, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hin.1
    · refine mem_sylow_of_pow_eq_one S₀ hS₀ (k := k) ?_
      rw [← map_pow, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hin.2
  intro S
  have hSR : (S : Subgroup (Outer (L × L))) ≤ R := fun x hx => by
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem S.isPGroup' hx
    exact hRmax x k hk
  rw [← S.is_maximal' hRp hSR]
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hRp hx
  exact hRmax _ k (by rw [conj_pow, hk, mul_one, mul_inv_cancel])

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
