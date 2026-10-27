module

public import CFSG.LargeExtraspecial.O62Sylow
public import CFSG.LargeExtraspecial.O62Span
public import CFSG.LargeExtraspecial.O62Transport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Code Check

theorem exists_coded_of_mem_sylowT
    {minus : Bool} {x : V₀ ≃ₗ[ZMod 2] V₀}
    (hx : x ∈ sylowT minus) : ∃ c ∈ (sylowWords minus).map wordC, Coded x c := by
  obtain ⟨w, hw, rfl⟩ := mem_sylowT.mp hx
  exact ⟨wordC w, List.mem_map_of_mem hw, coded_wordProd w⟩

theorem isInv_of_coded {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hx : Coded x c) (h2 : x ^ 2 = 1)
    (h1 : x ≠ 1) : isInv c = true := by
  have hsq : Coded (x * x) (mul c c) := hx.mul hx
  rw [← pow_two, h2] at hsq
  have e1 : mul c c = one := (hsq.eq_iff coded_one).mp rfl
  have e2 : c ≠ one := fun h => h1 ((hx.eq_iff coded_one).mpr h)
  simp [isInv, e1, e2]

theorem comm_of_coded {x y : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hx : Coded x a) (hy : Coded y b)
    (h : x * y = y * x) : comm a b = true := by
  have e := ((hx.mul hy).eq_iff (hy.mul hx)).mp h
  simp [Check.comm, e]

theorem not_mem_spanC_of_coded {xs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded xs cs) {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hx : Coded x c)
    (hn : x ∉ spanG xs) : c ∉ spanC cs :=
  fun hc => hn ((mem_iff_of_forall₂ (forall₂_spanG h) hx).mpr hc)

theorem mem_filter_comm {l s : List ℕ} {x y : ℕ} (hy : y ∈ l) (hc : comm x y = true)
    (hs : y ∉ s) : y ∈ l.filter (fun z => comm x z && !s.contains z) := by
  rw [List.mem_filter]
  refine ⟨hy, ?_⟩
  simp [hc, hs]

theorem card_le_of_elemAbelian_model
    {minus : Bool} {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hP : P ≤ O₀ minus) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1) :
    Nat.card P ≤ 2 ^ 4 := by
  have := finite_linearEquiv (V := V₀)
  have hP2 : IsPGroup 2 P := fun x => ⟨1, Subtype.ext (by simpa using h2 x x.2)⟩
  obtain ⟨g, -, hg⟩ := exists_conj_mem_sylowT hP hP2
  set φ := (MulAut.conj g⁻¹).toMonoidHom with hφ
  set P₁ := P.map φ with hP₁
  have hT : ∀ y ∈ P₁, y ∈ sylowT minus := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [hφ, MulAut.conj_apply] using hg x hx
  have hab₁ : ∀ y ∈ P₁, ∀ y' ∈ P₁, y * y' = y' * y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul, hab x hx x' hx']
  have h2₁ : ∀ y ∈ P₁, y ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h2 x hx, map_one]
  have hcard : Nat.card P₁ = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  by_contra hlt
  rw [not_le, ← hcard] at hlt
  norm_num at hlt
  obtain ⟨x₁, hx₁, hn₁⟩ := exists_mem_not_mem_spanG (P := P₁) [] (by simp; omega)
  obtain ⟨x₂, hx₂, hn₂⟩ := exists_mem_not_mem_spanG (P := P₁) [x₁] (by simp; omega)
  obtain ⟨x₃, hx₃, hn₃⟩ := exists_mem_not_mem_spanG (P := P₁) [x₂, x₁] (by simp; omega)
  obtain ⟨x₄, hx₄, hn₄⟩ := exists_mem_not_mem_spanG (P := P₁) [x₃, x₂, x₁] (by simp; omega)
  obtain ⟨x₅, hx₅, hn₅⟩ := exists_mem_not_mem_spanG (P := P₁) [x₄, x₃, x₂, x₁]
    (by simp; omega)
  obtain ⟨c₁, hm₁, hc₁⟩ := exists_coded_of_mem_sylowT (hT x₁ hx₁)
  obtain ⟨c₂, hm₂, hc₂⟩ := exists_coded_of_mem_sylowT (hT x₂ hx₂)
  obtain ⟨c₃, hm₃, hc₃⟩ := exists_coded_of_mem_sylowT (hT x₃ hx₃)
  obtain ⟨c₄, hm₄, hc₄⟩ := exists_coded_of_mem_sylowT (hT x₄ hx₄)
  obtain ⟨c₅, hm₅, hc₅⟩ := exists_coded_of_mem_sylowT (hT x₅ hx₅)
  have hne : ∀ {x : V₀ ≃ₗ[ZMod 2] V₀} {xs : List (V₀ ≃ₗ[ZMod 2] V₀)}, x ∉ spanG xs → x ≠ 1 :=
    fun hn h => hn (h ▸ one_mem_spanG _)
  have hcs : ∀ {x c}, x ∈ P₁ → c ∈ (sylowWords minus).map wordC → Coded x c →
      ∀ {xs : List (V₀ ≃ₗ[ZMod 2] V₀)}, x ∉ spanG xs →
        c ∈ ((sylowWords minus).map wordC).filter isInv :=
    fun hx hm hc _ hn => List.mem_filter.mpr ⟨hm, isInv_of_coded hc (h2₁ _ hx) (hne hn)⟩
  have F₁ : List.Forall₂ Coded [x₁] [c₁] := .cons hc₁ .nil
  have F₂ : List.Forall₂ Coded [x₂, x₁] [c₂, c₁] := .cons hc₂ F₁
  have F₃ : List.Forall₂ Coded [x₃, x₂, x₁] [c₃, c₂, c₁] := .cons hc₃ F₂
  have F₄ : List.Forall₂ Coded [x₄, x₃, x₂, x₁] [c₄, c₃, c₂, c₁] := .cons hc₄ F₃
  have n₂₁ := not_mem_spanC_of_coded F₁ hc₂ hn₂
  have n₃₂ := not_mem_spanC_of_coded F₂ hc₃ hn₃
  have n₃₁ := not_mem_spanC_of_coded F₁ hc₃ fun h => hn₃ (mem_spanG_cons_of_mem h)
  have n₄₃ := not_mem_spanC_of_coded F₃ hc₄ hn₄
  have n₄₂ := not_mem_spanC_of_coded F₂ hc₄ fun h => hn₄ (mem_spanG_cons_of_mem h)
  have n₄₁ := not_mem_spanC_of_coded F₁ hc₄ fun h =>
    hn₄ (mem_spanG_cons_of_mem (mem_spanG_cons_of_mem h))
  have n₅₄ := not_mem_spanC_of_coded F₄ hc₅ hn₅
  have n₅₃ := not_mem_spanC_of_coded F₃ hc₅ fun h => hn₅ (mem_spanG_cons_of_mem h)
  have n₅₂ := not_mem_spanC_of_coded F₂ hc₅ fun h =>
    hn₅ (mem_spanG_cons_of_mem (mem_spanG_cons_of_mem h))
  have n₅₁ := not_mem_spanC_of_coded F₁ hc₅ fun h =>
    hn₅ (mem_spanG_cons_of_mem (mem_spanG_cons_of_mem (mem_spanG_cons_of_mem h)))
  rw [spanC_cons] at n₃₂ n₄₂ n₅₂
  rw [spanC_cons, spanC_cons] at n₄₃ n₅₃
  rw [spanC_cons, spanC_cons, spanC_cons] at n₅₄
  have k : ∀ {x y : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ}, x ∈ P₁ → y ∈ P₁ → Coded x a → Coded y b →
      comm a b = true := fun hx hy ha hb => comm_of_coded ha hb (hab₁ _ hx _ hy)
  have h := checkRank_eq_true minus
  unfold checkRank at h
  have h1 := List.all_eq_true.mp h c₁ (hcs hx₁ hm₁ hc₁ hn₁)
  have h2' := List.all_eq_true.mp h1 c₂
    (mem_filter_comm (hcs hx₂ hm₂ hc₂ hn₂) (k hx₁ hx₂ hc₁ hc₂) n₂₁)
  have h3 := List.all_eq_true.mp h2' c₃
    (mem_filter_comm (mem_filter_comm (hcs hx₃ hm₃ hc₃ hn₃) (k hx₁ hx₃ hc₁ hc₃) n₃₁)
      (k hx₂ hx₃ hc₂ hc₃) n₃₂)
  have h4 := List.all_eq_true.mp h3 c₄
    (mem_filter_comm (mem_filter_comm (mem_filter_comm (hcs hx₄ hm₄ hc₄ hn₄)
      (k hx₁ hx₄ hc₁ hc₄) n₄₁) (k hx₂ hx₄ hc₂ hc₄) n₄₂) (k hx₃ hx₄ hc₃ hc₄) n₄₃)
  have h5 := mem_filter_comm (mem_filter_comm (mem_filter_comm (mem_filter_comm
    (hcs hx₅ hm₅ hc₅ hn₅) (k hx₁ hx₅ hc₁ hc₅) n₅₁) (k hx₂ hx₅ hc₂ hc₅) n₅₂)
    (k hx₃ hx₅ hc₃ hc₅) n₅₃) (k hx₄ hx₅ hc₄ hc₅) n₅₄
  rw [List.isEmpty_iff] at h4
  rw [h4] at h5
  exact List.not_mem_nil h5

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_le_of_elemAbelian
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1) :
    Nat.card P ≤ 2 ^ 4 := by
  obtain ⟨L, hL⟩ := exists_linearEquiv_model hV hQ
  obtain ⟨minus, hL'⟩ : ∃ minus, ∀ v, qModel minus (L v) = Q v := by
    rcases hL with hL | hL
    · exact ⟨false, fun v => by rw [qModel_false]; exact hL v⟩
    · exact ⟨true, fun v => by rw [qModel_true]; exact hL v⟩
  rw [← card_map_conjL L P]
  refine card_le_of_elemAbelian_model (map_conjL_le_orthogonalGroup hL' hP) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h2 x hx, map_one]

end CFSG.LargeExtraspecial.O62
