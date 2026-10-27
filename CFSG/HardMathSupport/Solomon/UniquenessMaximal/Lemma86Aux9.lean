module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux8
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux3
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

namespace LinPkg

variable {Q N : Subgroup G} (P : LinPkg Q N)

theorem mem_normalizer_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {J : Subgroup X}
    {g : X} (hg : g ∈ Subgroup.normalizer (J : Set X)) :
    f g ∈ Subgroup.normalizer ((J.map f : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg y).1 hy, by simp⟩
  · rintro ⟨y', hy', hz⟩
    refine ⟨g⁻¹ * y' * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y').1 hy'
      simpa using this
    · have : z = (f g)⁻¹ * (f g * z * (f g)⁻¹) * f g := by group
      rw [this, ← hz]
      simp

theorem rB_mem_normalizer_of_simple (i11 : Input11_3) (hK : CFSG.Open.IsKGroup ↥N) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) {B : Subgroup G} (hBN : B ≤ N)
    (hBmax : GLAIsBmax p (B.subgroupOf N)) {Lt : Subgroup (MulAut P.V)}
    (hsn : IsSubnormal Lt P.ρ.range) (hsimple : IsSimpleGroup ↥Lt)
    (hnab : ∃ a b : ↥Lt, a * b ≠ b * a) (hpL : p ∣ Nat.card Lt) (b : B) :
    P.rB hBN b ∈ Subgroup.normalizer (Lt : Set (MulAut P.V)) := by
  have hLX : Lt ≤ P.ρ.range := isSubnormal_le' hsn
  have hcomp := glaPComponent_of_simple hp hLX hsn hsimple hnab hpL
  rw [MonoidHom.range_eq_map] at hcomp
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥N) ⊓ P.ρ.ker)) := by
    rw [top_inf_eq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (P.not_dvd_card_ker hp hp2 hQ2)
  obtain ⟨J, hJ, hJmap⟩ := exists_glaPComponent_map_eq hp P.ρ hker hcomp
  let g : ↥J →* MulAut P.V := P.ρ.comp J.subtype
  have hgL : ∀ j : J, g j ∈ Lt := fun j => hJmap ▸ ⟨j, j.2, rfl⟩
  let f : ↥J →* ↥Lt := g.codRestrict Lt hgL
  have hf : Function.Surjective f := by
    intro l
    have : (l : MulAut P.V) ∈ J.map P.ρ := hJmap ▸ l.2
    obtain ⟨j, hj, hjl⟩ := this
    exact ⟨⟨j, hj⟩, Subtype.ext hjl⟩
  have hkerf : ¬ p ∣ Nat.card f.ker := by
    let k : ↥f.ker →* ↥P.ρ.ker :=
      MonoidHom.codRestrict (J.subtype.comp f.ker.subtype) P.ρ.ker (fun x => by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        exact this)
    have hkinj : Function.Injective k := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥P.ρ.ker => ((x : ↥N) : ↥N)) hab
    have hk2 : IsPGroup 2 ↥f.ker := (P.isPGroup_ker hQ2).of_injective k hkinj
    obtain ⟨a, ha⟩ := hk2.exists_card_eq
    rw [ha]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hcenter := center_quotient_eq_bot hp hf hsimple hnab hpL hkerf
  have hnorm : (B.subgroupOf N) ≤ Subgroup.normalizer (J : Set ↥N) := by
    by_contra h
    exact i11 ↥N hK p hp hp2 (B.subgroupOf N) hBmax J hJ h hcenter
  have h1 := hnorm (Subgroup.mem_subgroupOf.2 b.2 : (⟨b, hBN b.2⟩ : ↥N) ∈ B.subgroupOf N)
  have h2 := mem_normalizer_map P.ρ h1
  rw [hJmap] at h2
  exact h2

end LinPkg

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
