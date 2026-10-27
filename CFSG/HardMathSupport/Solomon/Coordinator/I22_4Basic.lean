module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {Ω : Type*} [Group Ω]

@[expose] def i224Cj (g : Ω) (H : Subgroup Ω) : Subgroup Ω := H.map (MulAut.conj g).toMonoidHom

theorem mem_i224Cj {g x : Ω} {H : Subgroup Ω} : x ∈ i224Cj g H ↔ g⁻¹ * x * g ∈ H := by
  unfold i224Cj
  rw [Subgroup.mem_map_equiv]
  rfl

theorem i224Cj_mul (g h : Ω) (H : Subgroup Ω) : i224Cj (g * h) H = i224Cj g (i224Cj h H) := by
  ext x
  rw [mem_i224Cj, mem_i224Cj, mem_i224Cj]
  have : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [this]

theorem i224Cj_of_mem_normalizer {g : Ω} {H : Subgroup Ω} (hg : g ∈ Subgroup.normalizer (H : Set Ω)) :
    i224Cj g H = H := by
  ext x
  rw [mem_i224Cj]
  have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (H : Set Ω)).inv_mem hg) x)
  simpa using this.symm

theorem mem_normalizer_of_i224Cj_eq {g g' : Ω} {H : Subgroup Ω} (h : i224Cj g H = i224Cj g' H) :
    g⁻¹ * g' ∈ Subgroup.normalizer (H : Set Ω) := by
  have key : ∀ y : Ω, y ∈ H ↔ (g⁻¹ * g')⁻¹ * y * (g⁻¹ * g') ∈ H := by
    intro y
    have h1 : g * y * g⁻¹ ∈ i224Cj g H ↔ g * y * g⁻¹ ∈ i224Cj g' H := by rw [h]
    rw [mem_i224Cj, mem_i224Cj] at h1
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g'⁻¹ * (g * y * g⁻¹) * g' = (g⁻¹ * g')⁻¹ * y * (g⁻¹ * g') := by group
    rw [e1, e2] at h1
    exact h1
  have hinv : (g⁻¹ * g')⁻¹ ∈ Subgroup.normalizer (H : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simpa using key y
  simpa using (Subgroup.normalizer (H : Set Ω)).inv_mem hinv

theorem i224_perfect {L : Subgroup Ω} (hL : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 := Subgroup.map_commutator (f := L.subtype) (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h1
  have h2 : ⁅(⊤ : Subgroup ↥L), ⊤⁆ = ⊤ := hL.1
  rw [h2, Subgroup.map_top, Subgroup.range_subtype] at h1
  exact h1.symm

theorem i224_gen {L : Subgroup Ω} (hL : CFSG.Open.IsQuasisimple ↥L) {a : Ω}
    (ha : a ∈ Subgroup.normalizer (L : Set Ω)) (hne : ∃ l ∈ L, a * l * a⁻¹ ≠ l) :
    L ≤ Subgroup.closure {t : Ω | ∃ l ∈ L, t = a * l * a⁻¹ * l⁻¹} := by
  set S : Set Ω := {t : Ω | ∃ l ∈ L, t = a * l * a⁻¹ * l⁻¹} with hS
  set T : Subgroup Ω := Subgroup.closure S with hT
  have hal : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl => (Subgroup.mem_normalizer_iff.1 ha l).1 hl
  have hSL : S ⊆ L := by
    rintro _ ⟨l, hl, rfl⟩
    exact L.mul_mem (hal l hl) (L.inv_mem hl)
  have hTL : T ≤ L := (Subgroup.closure_le L).2 hSL
  have hid : ∀ l m : Ω, a * (l * m) * a⁻¹ * (l * m)⁻¹ =
      (a * l * a⁻¹ * l⁻¹) * (l * (a * m * a⁻¹ * m⁻¹) * l⁻¹) := fun l m => by group
  have hconj : ∀ m ∈ L, ∀ t ∈ T, m * t * m⁻¹ ∈ T := by
    intro m hm t ht
    have hle : S ≤ (T.comap (MulAut.conj m).toMonoidHom : Subgroup Ω) := by
      rintro _ ⟨l, hl, rfl⟩
      show m * (a * l * a⁻¹ * l⁻¹) * m⁻¹ ∈ T
      have h1 := hid m l
      have h2 : m * (a * l * a⁻¹ * l⁻¹) * m⁻¹ =
          (a * m * a⁻¹ * m⁻¹)⁻¹ * (a * (m * l) * a⁻¹ * (m * l)⁻¹) := by
        rw [h1]; group
      rw [h2]
      exact T.mul_mem (T.inv_mem (Subgroup.subset_closure ⟨m, hm, rfl⟩))
        (Subgroup.subset_closure ⟨m * l, L.mul_mem hm hl, rfl⟩)
    exact (Subgroup.closure_le _ |>.2 hle) ht
  have hnormal : (T.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTL]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro t
    exact ⟨fun ht => hconj m hm t ht, fun ht => by
      have := hconj m⁻¹ (L.inv_mem hm) _ ht
      simpa [mul_assoc] using this⟩
  have hq : CFSG.IsQuasisimple ↥L :=
    ⟨⟨hL.1⟩, hL.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hnormal with htop | hcen
  · exact Subgroup.subgroupOf_eq_top.mp htop
  · exfalso
    have hcenl : ∀ l ∈ L, ∀ m ∈ L, m * (a * l * a⁻¹ * l⁻¹) = (a * l * a⁻¹ * l⁻¹) * m := by
      intro l hl m hm
      have : (⟨a * l * a⁻¹ * l⁻¹, hTL (Subgroup.subset_closure ⟨l, hl, rfl⟩)⟩ : ↥L) ∈
          Subgroup.center ↥L := hcen (Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨l, hl, rfl⟩))
      have h := Subgroup.mem_center_iff.1 this ⟨m, hm⟩
      exact congrArg Subtype.val h
    let φ : ↥L →* Ω :=
      { toFun := fun l => a * l * a⁻¹ * (l : Ω)⁻¹
        map_one' := by simp
        map_mul' := fun l m => by
          have h1 := hid (l : Ω) (m : Ω)
          have h2 := hcenl m m.2 l l.2
          have h3 : (l : Ω) * (a * m * a⁻¹ * (m : Ω)⁻¹) * (l : Ω)⁻¹ = a * m * a⁻¹ * (m : Ω)⁻¹ := by
            rw [h2]; group
          show a * ((l * m : ↥L) : Ω) * a⁻¹ * ((l * m : ↥L) : Ω)⁻¹ = _
          rw [Subgroup.coe_mul, h1, h3] }
    have hcomm : ∀ x y : ↥L, Commute (φ x) (φ y) := by
      intro x y
      exact (hcenl x x.2 (a * y * a⁻¹ * (y : Ω)⁻¹) (hTL (Subgroup.subset_closure ⟨y, y.2, rfl⟩))).symm
    have hle : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ φ.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (hcomm x y)
    have hall : ∀ l : ↥L, φ l = 1 := by
      intro l
      have h2 : ⁅(⊤ : Subgroup ↥L), ⊤⁆ = ⊤ := hL.1
      rw [h2] at hle
      exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top l))
    obtain ⟨l, hl, hl'⟩ := hne
    apply hl'
    have := hall ⟨l, hl⟩
    have h4 : a * l * a⁻¹ * l⁻¹ = 1 := this
    calc a * l * a⁻¹ = (a * l * a⁻¹ * l⁻¹) * l := by group
      _ = l := by rw [h4, one_mul]

theorem i224_exists_compl {p : ℕ} [Fact p.Prime] {B A : Subgroup Ω}
    (hB : CFSG.Open.IsElemAbelian p B) (hAB : A ≤ B) :
    ∃ C : Subgroup Ω, C ≤ B ∧ A ⊓ C = ⊥ ∧ A ⊔ C = B := by
  have : CFSG.IsElementaryAbelian p ↥B :=
    { toIsMulCommutative := hB.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hB.2 x x.2) }
  obtain ⟨C', hC'⟩ := CFSG.IsElementaryAbelian.exists_isCompl p ↥B (A.subgroupOf B)
  refine ⟨C'.map B.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [eq_bot_iff]
    intro x ⟨hxA, hxC⟩
    obtain ⟨c, hc, rfl⟩ := hxC
    have h1 : c ∈ A.subgroupOf B ⊓ C' := ⟨Subgroup.mem_subgroupOf.2 hxA, hc⟩
    rw [hC'.1.eq_bot] at h1
    have : c = 1 := h1
    rw [this]
    exact Subgroup.one_mem _
  · have h1 : (A.subgroupOf B) ⊔ C' = ⊤ := hC'.2.eq_top
    have h2 := congrArg (Subgroup.map B.subtype) h1
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAB, Subgroup.map_top,
      Subgroup.range_subtype] at h2
    exact h2

theorem i224_card_sup {P Q : Subgroup Ω} (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hd : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  let f : P × Q →* Ω := MonoidHom.noncommCoprod P.subtype Q.subtype fun x y => hc x x.2 y y.2
  have hrange : f.range = P ⊔ Q := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      exact (P ⊔ Q).mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right y.2)
    · intro x hx
      exact ⟨(⟨x, hx⟩, 1), by show x * 1 = x; simp⟩
    · intro x hx
      exact ⟨(1, ⟨x, hx⟩), by show 1 * x = x; simp⟩
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : Ω) * y = 1 := hxy
    have h1 : (x : Ω) = (y : Ω)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have h2 : (x : Ω) ∈ P ⊓ Q := ⟨x.2, by rw [h1]; exact Q.inv_mem y.2⟩
    rw [hd, Subgroup.mem_bot] at h2
    have hx1 : x = 1 := Subtype.ext h2
    have hy1 : (y : Ω) = 1 := by rw [h1] at h2; simpa using h2
    rw [Subgroup.mem_bot]
    exact Prod.ext hx1 (Subtype.ext hy1)
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [Nat.card_prod] at h1
  rw [← hrange, ← h1]

end CFSG.HardMathSupport.Solomon.Coordinator
