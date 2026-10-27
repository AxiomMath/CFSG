module

public import CFSG.LargeExtraspecial.S14C10FStar
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

variable {Y : Type} [Group Y] {M : Subgroup Y} {M0 : Subgroup M}

@[expose] def Ct0 (M0 : Subgroup M) (t : Y) : Subgroup Y :=
  M0.map M.subtype ⊓ centralizer ({t} : Set Y)

@[expose] def inclC (M0 : Subgroup M) (t0 : M0) : centralizer ({t0} : Set M0) →* Y :=
  M.subtype.comp (M0.subtype.comp (centralizer ({t0} : Set M0)).subtype)

variable {t0 : M0}

theorem inclC_injective : Function.Injective (inclC M0 t0) :=
  Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)

theorem inclC_mul (a b : centralizer ({t0} : Set M0)) :
    inclC M0 t0 (a * b) = inclC M0 t0 a * inclC M0 t0 b :=
  map_mul _ a b

theorem inclC_inv (a : centralizer ({t0} : Set M0)) : inclC M0 t0 a⁻¹ = (inclC M0 t0 a)⁻¹ :=
  map_inv _ a

theorem mem_Ct0 {t x : Y} : x ∈ Ct0 M0 t ↔ (∃ m ∈ M0, (m : Y) = x) ∧ x * t = t * x := by
  unfold Ct0
  rw [Subgroup.mem_inf, Subgroup.mem_map, mem_centralizer_singleton_iff]
  rfl

theorem range_inclC : (inclC M0 t0).range = Ct0 M0 ((t0 : M) : Y) := by
  ext x
  rw [mem_Ct0, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨(c : M0), (c : M0).2, rfl⟩,
      congrArg (fun y : M0 => ((y : M) : Y)) (mem_centralizer_singleton_iff.mp c.2)⟩
  · rintro ⟨⟨m, hm, rfl⟩, hxt⟩
    exact ⟨⟨⟨m, hm⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext (Subtype.ext hxt))⟩, rfl⟩

theorem inclC_mem_Ct0 (c : centralizer ({t0} : Set M0)) :
    inclC M0 t0 c ∈ Ct0 M0 ((t0 : M) : Y) :=
  range_inclC (t0 := t0) ▸ MonoidHom.mem_range.mpr ⟨c, rfl⟩

theorem Ct0_le (t : Y) : Ct0 M0 t ≤ M ⊓ centralizer ({t} : Set Y) := fun x hx => by
  obtain ⟨⟨m, -, rfl⟩, hxt⟩ := mem_Ct0.mp hx
  exact Subgroup.mem_inf.mpr ⟨m.2, mem_centralizer_singleton_iff.mpr hxt⟩

theorem inclC_mem (c : centralizer ({t0} : Set M0)) :
    inclC M0 t0 c ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y) :=
  Ct0_le _ (inclC_mem_Ct0 c)

theorem conj_mem_Ct0 (hn : M0.Normal) {t k h : Y} (hk : k ∈ M ⊓ centralizer ({t} : Set Y))
    (hh : h ∈ Ct0 M0 t) : k * h * k⁻¹ ∈ Ct0 M0 t := by
  rw [mem_Ct0] at hh ⊢
  obtain ⟨⟨m, hm, rfl⟩, hht⟩ := hh
  have hk1 : k ∈ M := (Subgroup.mem_inf.mp hk).1
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).2
  have h1 : (⟨k, hk1⟩ : M) * m * (⟨k, hk1⟩ : M)⁻¹ ∈ M0 := hn.conj_mem m hm _
  refine ⟨⟨_, h1, by simp only [Subgroup.coe_mul, Subgroup.coe_inv]⟩, ?_⟩
  exact ((Commute.mul_left (Commute.mul_left hkt hht) (Commute.inv_left hkt))).eq

theorem map_fstar_inclC [Finite Y] (hn : M0.Normal)
    (hp : IsPGroup 2 (timmesfeldFStar ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y))))
    (hle : (timmesfeldFStar ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y))).map
      (M ⊓ centralizer ({((t0 : M) : Y)} : Set Y)).subtype ≤ M0.map M.subtype) :
    (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) =
      (timmesfeldFStar ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y))).map
        (M ⊓ centralizer ({((t0 : M) : Y)} : Set Y)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle' : (timmesfeldFStar ↥(M ⊓ centralizer ({((t0 : M) : Y)} : Set Y))).map
      (M ⊓ centralizer ({((t0 : M) : Y)} : Set Y)).subtype ≤ Ct0 M0 ((t0 : M) : Y) :=
    fun x hx => by
      refine mem_Ct0.mpr ⟨Subgroup.mem_map.mp (hle hx), ?_⟩
      obtain ⟨y, -, rfl⟩ := hx
      exact mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
  have h1 := map_fstar_eq_of_le (Ct0_le _) (fun k hk h hh => conj_mem_Ct0 hn hk hh) hp hle'
  let e := (MonoidHom.ofInjective (inclC_injective (t0 := t0))).trans
    (MulEquiv.subgroupCongr (range_inclC (t0 := t0)))
  have he : (Ct0 M0 ((t0 : M) : Y)).subtype.comp e.toMonoidHom = inclC M0 t0 :=
    MonoidHom.ext fun _ => rfl
  rw [← he, ← map_map, Bridge.timmesfeldFStar_map e, h1]

theorem exists_conclusion_of_mainFor (ih : Bridge.MainFor M0) {w : ℕ} {N : Subgroup Y}
    (hnonab : ∃ a b : M0, a * b ≠ b * a) (ht2 : orderOf t0 = 2)
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hext : IsExtraspecialPGroup 2 N) (hcard : Nat.card N = 2 ^ (1 + 2 * w)) :
    ∃ (X : Type) (_ : Group X) (φ : centralizer ({t0} : Set M0) →* X),
      Function.Surjective φ ∧ φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)) ∧
        Bridge.TimmesfeldConclusion M0 w X := by
  have e := (Subgroup.equivMapOfInjective _ _ (inclC_injective (t0 := t0))).trans
    (MulEquiv.subgroupCongr hmap)
  have hext' := (Bridge.timmesfeldIsExtraspecial_congr e).mpr
    ((Bridge.timmesfeldIsExtraspecial_iff _).mpr hext)
  have hcard' := (Nat.card_congr e.toEquiv).trans hcard
  have := timmesfeldFStar_normal (centralizer ({t0} : Set M0))
  exact ⟨_, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
    QuotientGroup.ker_mk' _, ih hnonab t0 ht2 hext' w hcard' _
      ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩⟩

theorem map_comap_inclC {R : Subgroup Y} (hR : R ≤ Ct0 M0 ((t0 : M) : Y)) :
    (R.comap (inclC M0 t0)).map (inclC M0 t0) = R := by
  rw [map_comap_eq, range_inclC, inf_eq_right.mpr hR]

theorem comap_inclC_perfect {R : Subgroup Y} (hR : R ≤ Ct0 M0 ((t0 : M) : Y))
    (hRp : ⁅R, R⁆ = R) : ⁅R.comap (inclC M0 t0), R.comap (inclC M0 t0)⁆ = R.comap (inclC M0 t0) :=
  map_injective (inclC_injective (t0 := t0)) (by rw [map_commutator, map_comap_inclC hR, hRp])

theorem comap_inclC_normal {R : Subgroup Y}
    (hRn : ∀ k ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y), ∀ r ∈ R, k * r * k⁻¹ ∈ R) :
    (R.comap (inclC M0 t0)).Normal :=
  ⟨fun n hn c => by
    rw [mem_comap, inclC_mul, inclC_mul, inclC_inv]
    exact hRn _ (inclC_mem c) _ hn⟩

theorem fstar_le_comap_inclC {R N : Subgroup Y}
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hNR : N ≤ R) : timmesfeldFStar (centralizer ({t0} : Set M0)) ≤ R.comap (inclC M0 t0) :=
  fun x hx => hNR (by rw [← hmap]; exact mem_map_of_mem _ hx)

theorem mem_fstar_iff {N : Subgroup Y}
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (c : centralizer ({t0} : Set M0)) :
    c ∈ timmesfeldFStar (centralizer ({t0} : Set M0)) ↔ inclC M0 t0 c ∈ N := by
  rw [← hmap]
  exact (mem_map_iff_mem (inclC_injective (t0 := t0))).symm

theorem exists_noncomm_of_mem {a b : Y} (ha : a ∈ M0.map M.subtype) (hb : b ∈ M0.map M.subtype)
    (hab : a * b ≠ b * a) : ∃ x y : M0, x * y ≠ y * x := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  refine ⟨⟨a', ha'⟩, ⟨b', hb'⟩, fun h => hab ?_⟩
  have h' := congrArg (fun y : M0 => ((y : M) : Y)) h
  simpa only [Subgroup.coe_mul, Subgroup.coe_subtype] using h'

end CFSG.LargeExtraspecial.S14
