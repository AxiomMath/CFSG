module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Count

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G}

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

@[expose] def Acts (ι : Elem2 6 →* G) (n : G) (g : Equiv.Perm V6) : Prop :=
  ∀ v : V6, n * coordElt ι v * n⁻¹ = coordElt ι (g v)

theorem acts_one : Acts ι 1 1 := by
  intro v
  simp

theorem Acts.mul {n m : G} {g h : Equiv.Perm V6} (hn : Acts ι n g) (hm : Acts ι m h) :
    Acts ι (n * m) (g * h) := by
  intro v
  have h1 : (n * m) * coordElt ι v * (n * m)⁻¹ = n * (m * coordElt ι v * m⁻¹) * n⁻¹ := by
    group
  rw [h1, hm v, hn (h v), Equiv.Perm.mul_apply]

theorem Acts.inv {n : G} {g : Equiv.Perm V6} (hn : Acts ι n g) : Acts ι n⁻¹ g⁻¹ := by
  intro v
  have h := hn (g⁻¹ v)
  have h2 : g (g⁻¹ v) = v := by simp
  rw [h2] at h
  rw [← h]
  group

theorem Acts.unique (hι : Function.Injective ι) {n : G} {g g' : Equiv.Perm V6}
    (h : Acts ι n g) (h' : Acts ι n g') : g = g' := by
  apply Equiv.ext
  intro v
  apply coordElt_injective hι
  rw [← h v, ← h' v]

theorem Acts.mem_normalizer {n : G} {g : Equiv.Perm V6} (h : Acts ι n g) :
    n ∈ normalizer (ι.range : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← show coordElt ι (Multiplicative.toAdd a) = ι a from rfl, h (Multiplicative.toAdd a)]
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (g (Multiplicative.toAdd a)), rfl⟩
  · intro hx
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx
    refine MonoidHom.mem_range.mpr
      ⟨Multiplicative.ofAdd (g⁻¹ (Multiplicative.toAdd b)), ?_⟩
    have hspec := h (g⁻¹ (Multiplicative.toAdd b))
    have hg : g (g⁻¹ (Multiplicative.toAdd b)) = Multiplicative.toAdd b := by simp
    rw [hg] at hspec
    rw [show coordElt ι (Multiplicative.toAdd b) = ι b from rfl] at hspec
    have hspec' : n * coordElt ι (g⁻¹ (Multiplicative.toAdd b)) = ι b * n :=
      mul_inv_eq_iff_eq_mul.mp hspec
    have hb' : n * x = ι b * n := mul_inv_eq_iff_eq_mul.mp hb.symm
    exact mul_left_cancel (hspec'.trans hb'.symm)

theorem exists_acts (hι : Function.Injective ι) {n : G} (hn : n ∈ normalizer (ι.range : Set G)) :
    ∃ g : Equiv.Perm V6, Acts ι n g := by
  obtain ⟨g, -, hg⟩ := exists_perm_of_mem_normalizer hι hn
  exact ⟨g, hg⟩

theorem Acts.isAddPerm (hι : Function.Injective ι) {n : G} {g : Equiv.Perm V6}
    (h : Acts ι n g) : IsAddPerm g := by
  intro x y
  have h1 : coordElt ι (g (x + y)) = coordElt ι (g x + g y) := by
    rw [← h (x + y), coordElt_add, coordElt_add, ← h x, ← h y]
    group
  exact Multiplicative.ofAdd.injective (hι h1)

theorem acts_one_of_mem_range {n : G} (hn : n ∈ ι.range) : Acts ι n 1 := by
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hn
  intro v
  simp only [Equiv.Perm.coe_one, id_eq]
  have hcomm : ι a * coordElt ι v = coordElt ι v * ι a := by
    rw [coordElt, ← map_mul, ← map_mul]
    congr 1
    exact mul_comm _ _
  rw [hcomm]
  group

theorem Acts.mem_range_of_one (hC : centralizer (ι.range : Set G) ≤ ι.range) {n : G}
    (h : Acts ι n 1) : n ∈ ι.range := by
  apply hC
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  have hspec := h (Multiplicative.toAdd a)
  simp only [Equiv.Perm.coe_one, id_eq] at hspec
  have hc : n * ι a = ι a * n := by
    simpa [coordElt] using (mul_inv_eq_iff_eq_mul.mp hspec)
  exact hc.symm

@[expose] def actImage (ι : Elem2 6 →* G) (P : Subgroup G) : Subgroup (Equiv.Perm V6) where
  carrier := {g | ∃ n ∈ P, Acts ι n g}
  mul_mem' := by
    rintro g h ⟨n, hn, hng⟩ ⟨m, hm, hmh⟩
    exact ⟨n * m, mul_mem hn hm, hng.mul hmh⟩
  one_mem' := ⟨1, one_mem _, acts_one⟩
  inv_mem' := by
    rintro g ⟨n, hn, hng⟩
    exact ⟨n⁻¹, inv_mem hn, hng.inv⟩

theorem actImage_normalizer : actImage ι (normalizer (ι.range : Set G)) = inducedGroup ι := by
  ext g
  constructor
  · rintro ⟨n, hn, hg⟩
    exact ⟨n, hn, hg⟩
  · rintro ⟨n, hn, hg⟩
    exact ⟨n, hn, hg⟩

theorem actImage_mono {P Q : Subgroup G} (h : P ≤ Q) : actImage ι P ≤ actImage ι Q := by
  rintro g ⟨n, hn, hng⟩
  exact ⟨n, h hn, hng⟩

theorem card_eq_card_inf_mul_card_actImage [Finite G] (hι : Function.Injective ι)
    (hC : centralizer (ι.range : Set G) ≤ ι.range) {P : Subgroup G}
    (hP : P ≤ normalizer (ι.range : Set G)) :
    Nat.card P = Nat.card ↥(P ⊓ ι.range) * Nat.card ↥(actImage ι P) := by
  classical
  let φ : P →* Equiv.Perm V6 :=
    { toFun := fun (p : P) => Classical.choose (exists_acts hι (hP p.2))
      map_one' := by
        apply Acts.unique hι
        · exact Classical.choose_spec (exists_acts hι (hP (1 : P).2))
        · simpa using acts_one
      map_mul' := fun (p q : P) => by
        apply Acts.unique hι
        · exact Classical.choose_spec (exists_acts hι (hP (p * q).2))
        · simpa only [Subgroup.coe_mul] using
            (Classical.choose_spec (exists_acts hι (hP p.2))).mul
              (Classical.choose_spec (exists_acts hι (hP q.2))) }
  have hrange : φ.range = actImage ι P := by
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, Classical.choose_spec (exists_acts hι (hP p.2))⟩
    · rintro ⟨n, hn, hgn⟩
      exact ⟨⟨n, hn⟩, Acts.unique hι (Classical.choose_spec (exists_acts hι (hP hn))) hgn⟩
  have hker : φ.ker = (ι.range).subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hp
      have hspec : Acts ι (p : G) (φ p) := Classical.choose_spec (exists_acts hι (hP p.2))
      rw [hp] at hspec
      exact Acts.mem_range_of_one hC hspec
    · intro hp
      exact Acts.unique hι (Classical.choose_spec (exists_acts hι (hP p.2)))
        (acts_one_of_mem_range hp)
  let eker : ↥((ι.range).subgroupOf P) ≃ ↥(P ⊓ ι.range) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl }
  have hker_card : Nat.card φ.ker = Nat.card ↥(P ⊓ ι.range) := by
    rw [hker]
    exact Nat.card_congr eker
  have hiso := Subgroup.card_ker_mul_card_range φ
  rw [hker_card, hrange] at hiso
  rw [← hiso]

end CFSG.EvenSporadicStandard.HNRecog.Harada
