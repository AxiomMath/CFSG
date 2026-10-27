module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabPrime
  CFSG.QuasithinUnique
open scoped commutatorElement

theorem mem_of_mem_normalizer {V : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]
    (S : Sylow p V) {J : Subgroup V} (hSJ : (S : Subgroup V) ≤ J)
    (hJ : Subgroup.normalizer (S : Set V) ≤ J) {g : V}
    (hg : g ∈ Subgroup.normalizer (J : Set V)) : g ∈ J := by
  set Nj : Subgroup V := Subgroup.normalizer (J : Set V) with hNj
  have hSN : (S : Subgroup V) ≤ Nj := hSJ.trans Subgroup.le_normalizer
  set P : Sylow p ↥Nj := S.subtype hSN with hP
  have : (J.subgroupOf Nj).Normal := Subgroup.normal_in_normalizer
  have hPcoe : (P : Subgroup ↥Nj) = (S : Subgroup V).subgroupOf Nj := S.coe_subtype hSN
  have hPJ : (P : Subgroup ↥Nj) ≤ J.subgroupOf Nj := by
    intro x hx
    rw [hPcoe] at hx
    exact hSJ (Subgroup.mem_subgroupOf.1 hx)
  have hfr := Sylow.normalizer_sup_eq_top' P hPJ
  have hmem : (⟨g, hg⟩ : ↥Nj) ∈ Subgroup.normalizer (P : Set ↥Nj) ⊔ J.subgroupOf Nj := by
    rw [hfr]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have haS : (a : V) ∈ Subgroup.normalizer (S : Set V) := by
    have h1 : a ∈ Subgroup.normalizer (((S : Subgroup V).subgroupOf Nj : Subgroup ↥Nj) :
        Set ↥Nj) := by
      rw [← hPcoe]
      exact ha
    rw [← Subgroup.subgroupOf_normalizer_eq hSN] at h1
    exact h1
  have hgab : g = (a : V) * (b : V) := congrArg Subtype.val hab.symm
  rw [hgab]
  exact J.mul_mem (hJ haS) (Subgroup.mem_subgroupOf.1 hb)

theorem perfectCyclicSylow_quotImage {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}
    [Fact p.Prime] (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    (h : PerfectCyclicSylow p J) {V : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hVJ : V ≤ quotImage L J) (hV : ⁅V, V⁆ = V) {A : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hAV : A ≤ V) (hA : IsPGroup p A) : IsCyclic A := by
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hker : π.ker ≤ Subgroup.center ↥L := by rw [hπ, QuotientGroup.ker_mk']
  obtain ⟨W, hW, hWle, hWmap⟩ := exists_perfect_map_eq π hker hV
    (by rw [MonoidHom.range_eq_top_of_surjective π (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hWJ : W.map L.subtype ≤ J := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 : π w ∈ V := hWle hw
    obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 (hVJ h1)
    have hz : l⁻¹ * w ∈ Subgroup.center ↥L := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, QuotientGroup.mk'_apply, hl]
      simp [hπ])
    have e1 : (w : Y) = (l : Y) * ((l⁻¹ * w : ↥L) : Y) := by simp
    show (w : Y) ∈ J
    rw [e1]
    exact J.mul_mem hlJ (hZ _ hz)
  have hWperf : ⁅W.map L.subtype, W.map L.subtype⁆ = W.map L.subtype := by
    rw [← Subgroup.map_commutator, hW]
  refine isCyclic_of_le_map π (B := W) (fun A₁ hA₁ hA₁p => ?_) (hWmap ▸ hAV) hA
  have hc : IsCyclic (A₁.map L.subtype) :=
    h _ hWJ hWperf _ (Subgroup.map_mono hA₁) (hA₁p.map _)
  exact isCyclic_of_injective
    (Subgroup.equivMapOfInjective A₁ L.subtype L.subtype_injective).toMonoidHom
    (MulEquiv.injective _)

section Map

variable {V W : Type*} [Group V] [Group W] (f : V →* W)

theorem borelLike_map {J S T : Subgroup V} (hS2 : IsPGroup 2 S) (hSJ : S ≤ J) (hTJ : T ≤ J)
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTodd : ∀ t ∈ T, ∃ m : ℕ, Odd m ∧ t ^ m = 1) (hTS : T ≤ Subgroup.normalizer (S : Set V))
    (hgen : J ≤ T ⊔ S ⊔ perfectJoin J) :
    IsPGroup 2 (S.map f) ∧ S.map f ≤ J.map f ∧ T.map f ≤ J.map f ∧
      (∀ a ∈ T.map f, ∀ b ∈ T.map f, a * b = b * a) ∧
      (∀ t ∈ T.map f, ∃ m : ℕ, Odd m ∧ t ^ m = 1) ∧
      T.map f ≤ Subgroup.normalizer ((S.map f : Subgroup W) : Set W) ∧
      J.map f ≤ T.map f ⊔ S.map f ⊔ perfectJoin (J.map f) := by
  refine ⟨hS2.map f, Subgroup.map_mono hSJ, Subgroup.map_mono hTJ, ?_, ?_,
    (Subgroup.map_mono hTS).trans (Subgroup.le_normalizer_map f), ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hTc a ha b hb]
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨m, hm, htm⟩ := hTodd t ht
    exact ⟨m, hm, by rw [← map_pow, htm, map_one]⟩
  · refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le_sup_left (le_perfectJoin (Subgroup.map_mono (perfectJoin_le J)) ?_) _
    rw [← Subgroup.map_commutator, perfectJoin_perfect]

theorem isCyclic_of_le_perfectJoin_map (hf : Function.Injective f) {J : Subgroup V} {p : ℕ}
    (hcyc : ∀ U : Subgroup V, U ≤ J → ⁅U, U⁆ = U → ∀ A : Subgroup V, A ≤ U → IsPGroup p A →
      IsCyclic A) {A : Subgroup W} (hA : A ≤ perfectJoin (J.map f)) (hAp : IsPGroup p A) :
    IsCyclic A := by
  set Q := perfectJoin (J.map f) with hQ
  have hQJ : Q ≤ J.map f := perfectJoin_le _
  set Q₀ := Q.comap f with hQ₀
  have hQ₀J : Q₀ ≤ J := by
    intro x hx
    obtain ⟨j, hj, hjx⟩ := hQJ hx
    exact (hf hjx) ▸ hj
  have hmapQ : Q₀.map f = Q := Subgroup.map_comap_eq_self (by
    exact hQJ.trans (Subgroup.map_le_range f J))
  have hperf : ⁅Q₀, Q₀⁆ = Q₀ := by
    apply Subgroup.map_injective hf
    rw [Subgroup.map_commutator, hmapQ, hQ, perfectJoin_perfect]
  have hAQ : A ≤ Q₀.map f := hmapQ ▸ hA
  set A₀ := A.comap f with hA₀
  have hA₀Q : A₀ ≤ Q₀ := fun x hx => hA hx
  have hA₀p : IsPGroup p A₀ := hAp.comap_of_injective f hf
  have hc : IsCyclic A₀ := hcyc Q₀ hQ₀J hperf A₀ hA₀Q hA₀p
  have hA₀map : A₀.map f = A := Subgroup.map_comap_eq_self (hA.trans (hQJ.trans
    (Subgroup.map_le_range f J)))
  rw [← hA₀map]
  exact isCyclic_of_injective (Subgroup.equivMapOfInjective A₀ f hf).symm.toMonoidHom
    (MulEquiv.injective _)

end Map

end CFSG.AGLEmbedding.ParabAutIrr
