module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Moved

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Diag

variable {Y : Type} [Group Y]

theorem map_conj_one (K : Subgroup Y) : K.map (MulAut.conj (1 : Y)).toMonoidHom = K := by
  ext x
  simp

theorem conj_mem_map_conj {L : Subgroup Y} (u : Y) {l : Y} (hl : l ∈ L) :
    u * l * u⁻¹ ∈ L.map (MulAut.conj u).toMonoidHom :=
  ⟨l, hl, by simp [MulAut.conj_apply]⟩

theorem isComponentOf_map_conj {L : Subgroup Y} (hL : IsComponentOf L ⊤) (u : Y) :
    IsComponentOf (L.map (MulAut.conj u).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj u) L).mpr hL

theorem commute_of_mem_ne [Finite Y] {L L' : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hL' : IsComponentOf L' ⊤) (hne : L ≠ L') {a b : Y} (ha : a ∈ L) (hb : b ∈ L') :
    a * b = b * a := by
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne
  have hc : a * b * a⁻¹ * b⁻¹ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at hc
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

theorem map_conj_ne_of_not_mem_normalizer {L : Subgroup Y} {u : Y} (hu : u ^ 3 = 1)
    (hnot : u ∉ Subgroup.normalizer (L : Set Y)) :
    L ≠ L.map (MulAut.conj u).toMonoidHom ∧ L ≠ L.map (MulAut.conj (u ^ 2)).toMonoidHom ∧
      L.map (MulAut.conj u).toMonoidHom ≠ L.map (MulAut.conj (u ^ 2)).toMonoidHom := by
  have hu2 : u ^ 2 = u⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hu]
  have h01 : L ≠ L.map (MulAut.conj u).toMonoidHom := fun h =>
    hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  refine ⟨h01, fun h => hnot ?_, fun h => h01 ?_⟩
  · have h2 : u ^ 2 ∈ Subgroup.normalizer (L : Set Y) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    rw [hu2] at h2
    simpa using Subgroup.inv_mem _ h2
  · have e1 : (L.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom = L := by
      rw [← map_conj_mul, inv_mul_cancel, map_conj_one]
    have e2 : (L.map (MulAut.conj (u ^ 2)).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom =
        L.map (MulAut.conj u).toMonoidHom := by
      have hh : u⁻¹ * u ^ 2 = u := by rw [pow_two]; group
      rw [← map_conj_mul, hh]
    calc L = (L.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom := e1.symm
      _ = (L.map (MulAut.conj (u ^ 2)).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom := by
          rw [h]
      _ = L.map (MulAut.conj u).toMonoidHom := e2

@[expose] def conjDiag (L : Subgroup Y) (u : Y)
    (h01 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj u).toMonoidHom, a * b = b * a)
    (h02 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a)
    (h12 : ∀ a ∈ L.map (MulAut.conj u).toMonoidHom,
      ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a) : L →* Y where
  toFun l := (l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have ha1 := conj_mem_map_conj u a.2
    have hb1 := conj_mem_map_conj u b.2
    have ha2 := conj_mem_map_conj (u ^ 2) a.2
    simp only [Subgroup.coe_mul]
    have e1 : u * ((a : Y) * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    have e2 : u ^ 2 * ((a : Y) * b) * (u ^ 2)⁻¹ =
        (u ^ 2 * a * (u ^ 2)⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹) := by group
    rw [e1, e2]
    have c1 := h01 b b.2 _ ha1
    have c2 := h02 b b.2 _ ha2
    have c3 := h12 _ hb1 _ ha2
    calc (a : Y) * b * (u * a * u⁻¹ * (u * b * u⁻¹)) *
          (u ^ 2 * a * (u ^ 2)⁻¹ * (u ^ 2 * b * (u ^ 2)⁻¹))
        = a * (b * (u * a * u⁻¹)) * (u * b * u⁻¹) *
          (u ^ 2 * a * (u ^ 2)⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹) := by group
      _ = a * ((u * a * u⁻¹) * b) * (u * b * u⁻¹) *
          (u ^ 2 * a * (u ^ 2)⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹) := by rw [c1]
      _ = a * (u * a * u⁻¹) * b * ((u * b * u⁻¹) *
          (u ^ 2 * a * (u ^ 2)⁻¹)) * (u ^ 2 * b * (u ^ 2)⁻¹) := by group
      _ = a * (u * a * u⁻¹) * b * ((u ^ 2 * a * (u ^ 2)⁻¹) *
          (u * b * u⁻¹)) * (u ^ 2 * b * (u ^ 2)⁻¹) := by rw [c3]
      _ = a * (u * a * u⁻¹) * (b * (u ^ 2 * a * (u ^ 2)⁻¹)) *
          (u * b * u⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹) := by group
      _ = a * (u * a * u⁻¹) * ((u ^ 2 * a * (u ^ 2)⁻¹) * b) *
          (u * b * u⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹) := by rw [c2]
      _ = a * (u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹) *
          (b * (u * b * u⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹)) := by group

variable {L : Subgroup Y} {u : Y}
  {h01 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj u).toMonoidHom, a * b = b * a}
  {h02 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a}
  {h12 : ∀ a ∈ L.map (MulAut.conj u).toMonoidHom,
    ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a}

theorem conjDiag_apply (l : L) :
    conjDiag L u h01 h02 h12 l = (l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) :=
  rfl

theorem range_conjDiag_le_centralizer (hu : u ^ 3 = 1) :
    (conjDiag L u h01 h02 h12).range ≤ Subgroup.centralizer ({u} : Set Y) := by
  rintro _ ⟨l, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, conjDiag_apply]
  have c1 := h01 l l.2 _ (conj_mem_map_conj u l.2)
  have c2 := h02 l l.2 _ (conj_mem_map_conj (u ^ 2) l.2)
  symm
  have e3 : u * ((l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹)) =
      (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) * l * u := by
    have : u ^ 3 = u * u ^ 2 := by rw [pow_succ']
    calc u * ((l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹))
        = (u * l * u⁻¹) * (u * u * l * u⁻¹ * u⁻¹) * (u * u ^ 2 * l * (u * u ^ 2)⁻¹) * u := by
          rw [pow_two]; group
      _ = (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) * l * u := by
          rw [← this, hu, ← pow_two]; group
  rw [e3]
  calc (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) * (l : Y) * u
      = (u * l * u⁻¹) * ((u ^ 2 * l * (u ^ 2)⁻¹) * l) * u := by group
    _ = (u * l * u⁻¹) * (l * (u ^ 2 * l * (u ^ 2)⁻¹)) * u := by rw [c2]
    _ = ((u * l * u⁻¹) * l) * (u ^ 2 * l * (u ^ 2)⁻¹) * u := by group
    _ = (l * (u * l * u⁻¹)) * (u ^ 2 * l * (u ^ 2)⁻¹) * u := by rw [c1]

theorem commute_of_conjDiag_eq_one (h1 : ∀ l : L, conjDiag L u h01 h02 h12 l = 1) (a b : L) :
    a * b = b * a := by
  have hfa := h1 a
  rw [conjDiag_apply] at hfa
  have hainv : (a : Y) = ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))⁻¹ := by
    have : (a : Y) * ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) = 1 := by
      rw [← mul_assoc]; exact hfa
    exact eq_inv_of_mul_eq_one_left this
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have c1 := h01 b b.2 _ (conj_mem_map_conj u a.2)
  have c2 := h02 b b.2 _ (conj_mem_map_conj (u ^ 2) a.2)
  rw [hainv]
  have hc : (b : Y) * ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) =
      ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) * b := by
    calc (b : Y) * ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))
        = ((b : Y) * (u * a * u⁻¹)) * (u ^ 2 * a * (u ^ 2)⁻¹) := by simp only [mul_assoc]
      _ = ((u * a * u⁻¹) * b) * (u ^ 2 * a * (u ^ 2)⁻¹) := by rw [c1]
      _ = (u * a * u⁻¹) * ((b : Y) * (u ^ 2 * a * (u ^ 2)⁻¹)) := by simp only [mul_assoc]
      _ = (u * a * u⁻¹) * ((u ^ 2 * a * (u ^ 2)⁻¹) * b) := by rw [c2]
      _ = ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) * b := by simp only [mul_assoc]
  calc ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))⁻¹ * (b : Y)
      = ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))⁻¹ * (b *
        ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))) *
        ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))⁻¹ := by group
    _ = (b : Y) * ((u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹))⁻¹ := by rw [hc]; group

theorem mem_normalizer_of_no_perfect_centralizer [Finite Y] (hL : IsComponentOf L ⊤)
    (hu : u ^ 3 = 1)
    (hZ : ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ Subgroup.centralizer ({u} : Set Y) → D = ⊥) :
    u ∈ Subgroup.normalizer (L : Set Y) := by
  by_contra hnot
  obtain ⟨h01', h02', h12'⟩ := map_conj_ne_of_not_mem_normalizer hu hnot
  have hc₁ := isComponentOf_map_conj hL u
  have hc₂ := isComponentOf_map_conj hL (u ^ 2)
  have c01 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj u).toMonoidHom, a * b = b * a :=
    fun a ha b hb => commute_of_mem_ne hL hc₁ h01' ha hb
  have c02 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a :=
    fun a ha b hb => commute_of_mem_ne hL hc₂ h02' ha hb
  have c12 : ∀ a ∈ L.map (MulAut.conj u).toMonoidHom,
      ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a :=
    fun a ha b hb => commute_of_mem_ne hc₁ hc₂ h12' ha hb
  set f := conjDiag L u c01 c02 c12 with hf
  have hLperf : ⁅(⊤ : Subgroup L), ⊤⁆ = ⊤ := hL.2.2.1
  have hDperf : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hLperf]
  have hDbot := hZ f.range hDperf (range_conjDiag_le_centralizer (h01 := c01) (h02 := c02)
    (h12 := c12) hu)
  have : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  have hab := commute_of_conjDiag_eq_one (h01 := c01) (h02 := c02) (h12 := c12) (fun l => by
    have : f l ∈ f.range := ⟨l, rfl⟩
    rwa [hDbot, Subgroup.mem_bot] at this)
  have htop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hab a b]
    group
  rw [hLperf] at htop
  exact (top_ne_bot : (⊤ : Subgroup L) ≠ ⊥) htop

theorem not_mem_centralizer_of_no_perfect_centralizer (hL : IsComponentOf L ⊤)
    (hZ : ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ Subgroup.centralizer ({u} : Set Y) → D = ⊥) :
    u ∉ Subgroup.centralizer (L : Set Y) := by
  intro hu
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (⟨hL.2.2.1⟩ : Group.IsPerfect ↥L)
  have hle : L ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hu l hl
  have : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this (hZ _ hLperf hle)

end Diag

section Irreducible

variable {Y : Type} [Group Y]

theorem conj_mul_inv_mem_centralizer {L : Subgroup Y} {t w : Y}
    (ht : t ∈ Subgroup.centralizer (L : Set Y)) (hw : w ∈ Subgroup.normalizer (L : Set Y)) :
    t * w * t⁻¹ * w⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  have hN : Subgroup.normalizer (L : Set Y) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have h1 : w * t⁻¹ * w⁻¹ ∈ Subgroup.centralizer (L : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp (hN hw) t⁻¹).mp (Subgroup.inv_mem _ ht)
  have h2 := Subgroup.mul_mem _ ht h1
  simpa [mul_assoc] using h2

theorem inf_centralizer_eq_bot_of_irreducible {A : Subgroup Y} {t : Y}
    (htA : t ∈ Subgroup.normalizer (A : Set Y))
    (hirr : ∀ F : Subgroup Y, F ≤ A → t ∈ Subgroup.normalizer (F : Set Y) → F = ⊥ ∨ F = A)
    (hnt : ∃ x ∈ A, t * x * t⁻¹ ≠ x) : A ⊓ Subgroup.centralizer ({t} : Set Y) = ⊥ := by
  have htF : t ∈ Subgroup.normalizer
      ((A ⊓ Subgroup.centralizer ({t} : Set Y) : Subgroup Y) : Set Y) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨htA, Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
  rcases hirr _ inf_le_left htF with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx, hne⟩ := hnt
    have hxF : x ∈ A ⊓ Subgroup.centralizer ({t} : Set Y) := by rw [h]; exact hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxF.2
    exact hne (by rw [← hxt]; group)

theorem exists_conj_mul_inv_eq [Finite Y] {A : Subgroup Y} (hA : IsMulCommutative A) {t : Y}
    (htA : t ∈ Subgroup.normalizer (A : Set Y))
    (hC : A ⊓ Subgroup.centralizer ({t} : Set Y) = ⊥) {a : Y} (ha : a ∈ A) :
    ∃ x ∈ A, t * x * t⁻¹ * x⁻¹ = a := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hA) ⟨x, hx⟩ ⟨y, hy⟩)
  have htx : ∀ x ∈ A, t * x * t⁻¹ ∈ A := fun x hx => (Subgroup.mem_normalizer_iff.mp htA x).mp hx
  let φ : A →* A :=
    { toFun := fun x => ⟨(t * x * t⁻¹) * (x : Y)⁻¹, A.mul_mem (htx x x.2) (A.inv_mem x.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul]
        have c := hcomm _ (A.inv_mem x.2) _ (A.mul_mem (htx y y.2) (A.inv_mem y.2))
        calc t * (x * y) * t⁻¹ * ((x : Y) * y)⁻¹
            = t * x * t⁻¹ * ((t * y * t⁻¹ * (y : Y)⁻¹) * (x : Y)⁻¹) := by group
          _ = t * x * t⁻¹ * ((x : Y)⁻¹ * (t * y * t⁻¹ * (y : Y)⁻¹)) := by rw [c]
          _ = t * x * t⁻¹ * (x : Y)⁻¹ * (t * y * t⁻¹ * (y : Y)⁻¹) := by group }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (t * x * t⁻¹) * (x : Y)⁻¹ = 1 := congrArg Subtype.val hx
    have hxF : (x : Y) ∈ A ⊓ Subgroup.centralizer ({t} : Set Y) := by
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have : t * x * t⁻¹ = x := mul_inv_eq_one.mp h1
      calc (x : Y) * t = t * x * t⁻¹ * t := by rw [this]
        _ = t * x := by group
    rw [hC, Subgroup.mem_bot] at hxF
    exact Subtype.ext hxF
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨a, ha⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem le_centralizer_of_irreducible [Finite Y] {A L : Subgroup Y} (hA : IsMulCommutative A)
    {t : Y} (htA : t ∈ Subgroup.normalizer (A : Set Y))
    (hirr : ∀ F : Subgroup Y, F ≤ A → t ∈ Subgroup.normalizer (F : Set Y) → F = ⊥ ∨ F = A)
    (hnt : ∃ x ∈ A, t * x * t⁻¹ ≠ x) (hAL : A ≤ Subgroup.normalizer (L : Set Y))
    (htL : t ∈ Subgroup.centralizer (L : Set Y)) :
    A ≤ Subgroup.centralizer (L : Set Y) := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ :=
    exists_conj_mul_inv_eq hA htA (inf_centralizer_eq_bot_of_irreducible htA hirr hnt) ha
  exact conj_mul_inv_mem_centralizer htL (hAL hx)

end Irreducible

end CFSG.AGLEmbedding
