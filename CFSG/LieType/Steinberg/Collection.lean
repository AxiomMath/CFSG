module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

variable {G : Type*} [Group G]

section Conj

theorem map_conj_mul (g h : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp

theorem mem_normalizer_iff_map_conj {g : G} {H : Subgroup G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem map_conj_of_mem {g : G} {H : Subgroup G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H :=
  mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hg)

theorem map_conj_inv_of_map_conj {g : G} {H K : Subgroup G}
    (h : H.map (MulAut.conj g).toMonoidHom = K) : K.map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [← h, ← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem map_conj_le_iff {g : G} {H K : Subgroup G} :
    H.map (MulAut.conj g).toMonoidHom ≤ K ↔ ∀ x ∈ H, g * x * g⁻¹ ∈ K :=
  ⟨fun h x hx => h ⟨x, hx, rfl⟩, fun h => Subgroup.map_le_iff_le_comap.2 fun x hx => h x hx⟩

theorem conj_mem_map_conj {g x : G} {H : Subgroup G} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem le_normalizer_of_map_conj_le {A M : Subgroup G}
    (h : ∀ x ∈ A, M.map (MulAut.conj x).toMonoidHom ≤ M) :
    A ≤ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  exact fun x hx m hm => h x hx ⟨m, hm, rfl⟩

theorem le_normalizer_iSup {κ : Sort*} {A : Subgroup G} {B : κ → Subgroup G}
    (h : ∀ k, A ≤ Subgroup.normalizer (B k : Set G)) :
    A ≤ Subgroup.normalizer ((⨆ k, B k : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun x hx => ?_
  rw [Subgroup.map_iSup]
  exact iSup_mono fun k => (mem_normalizer_iff_map_conj.1 (h k hx)).le

theorem le_normalizer_sup {A B C : Subgroup G} (hB : A ≤ Subgroup.normalizer (B : Set G))
    (hC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun x hx => ?_
  rw [Subgroup.map_sup, mem_normalizer_iff_map_conj.1 (hB hx),
    mem_normalizer_iff_map_conj.1 (hC hx)]

variable {N : Type*} [Group N]

theorem map_map_conj (f : G →* N) (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g).toMonoidHom).map f =
      (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end Conj

section InjOn

variable {N : Type*} [Group N] {f : G →* N}

theorem injOn_of_eq_one {M : Subgroup G} (h : ∀ g ∈ M, f g = 1 → g = 1) :
    Set.InjOn f (M : Set G) := by
  intro x hx y hy hxy
  exact mul_inv_eq_one.1 (h _ (M.mul_mem hx (M.inv_mem hy)) (by simp [hxy]))

theorem mem_of_injOn {M Q : Subgroup G} (hM : Set.InjOn f (M : Set G)) (hQ : Q ≤ M) {x : G}
    (hx : x ∈ M) (h : f x ∈ Q.map f) : x ∈ Q := by
  obtain ⟨q, hq, hqx⟩ := h
  rwa [← hM (hQ hq) hx hqx]

theorem le_of_injOn {M P Q : Subgroup G} (hM : Set.InjOn f (M : Set G)) (hP : P ≤ M)
    (hQ : Q ≤ M) (h : P.map f ≤ Q.map f) : P ≤ Q :=
  fun _ hp => mem_of_injOn hM hQ (hP hp) (h ⟨_, hp, rfl⟩)

theorem eq_of_injOn {M P Q : Subgroup G} (hM : Set.InjOn f (M : Set G)) (hP : P ≤ M)
    (hQ : Q ≤ M) (h : P.map f = Q.map f) : P = Q :=
  le_antisymm (le_of_injOn hM hP hQ h.le) (le_of_injOn hM hQ hP h.ge)

end InjOn

section Collection

variable {V : Type*}

theorem iSup_mem_cons (A : V → Subgroup G) (a : V) (L : List V) :
    ⨆ b ∈ a :: L, A b = A a ⊔ ⨆ b ∈ L, A b := by
  simp only [List.mem_cons, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]

private theorem iSup_cons_le {A : V → Subgroup G} {h : V → ℤ} {a : V} {L : List V} {m : ℤ}
    (ha : h a ≤ m) :
    ⨆ c ∈ a :: L, ⨆ (_ : m < h c), A c ≤ ⨆ c ∈ L, ⨆ (_ : m < h c), A c := by
  rw [iSup_mem_cons]
  exact sup_le (iSup_le fun hlt => absurd hlt (not_lt.2 ha)) le_rfl

theorem exists_prod_eq_of_commutator_mem (A : V → Subgroup G) (h : V → ℤ) :
    ∀ {L : List V}, L.Nodup → L.Pairwise (fun a b => h a ≤ h b) →
      (∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ A a, ∀ y ∈ A b,
        ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), A c) →
      ∀ g ∈ ⨆ v ∈ L, A v, ∃ f : V → G, (∀ v ∈ L, f v ∈ A v) ∧ g = (L.map f).prod
  | [], _, _, _, g, hg => ⟨1, by simp, by simpa using hg⟩
  | a :: L, hnd, hs, hc, g, hg => by
    classical
    obtain ⟨haL, hnd⟩ := List.nodup_cons.1 hnd
    obtain ⟨hah, hs⟩ := List.pairwise_cons.1 hs
    have hc' : ∀ b ∈ L, ∀ c ∈ L, b ≠ c → ∀ x ∈ A b, ∀ y ∈ A c,
        ⁅x, y⁆ ∈ ⨆ d ∈ L, ⨆ (_ : min (h b) (h c) < h d), A d := fun b hb c hc'' hbc x hx y hy =>
      iSup_cons_le (le_min (hah b hb) (hah c hc''))
        (hc b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc'') hbc x hx y hy)
    have hnorm : A a ≤ Subgroup.normalizer ((⨆ b ∈ L, A b : Subgroup G) : Set G) := by
      refine le_normalizer_of_map_conj_le fun x hx => ?_
      simp only [Subgroup.map_iSup]
      refine iSup₂_le fun b hb => map_conj_le_iff.2 fun y hy => ?_
      have hab : a ≠ b := fun hab => haL (hab ▸ hb)
      have hxy := iSup_cons_le (le_of_eq (min_eq_left (hah b hb)).symm)
        (hc a (List.mem_cons_self) b (List.mem_cons_of_mem a hb) hab x hx y hy)
      have hle : ⨆ c ∈ L, ⨆ (_ : min (h a) (h b) < h c), A c ≤ ⨆ c ∈ L, A c :=
        iSup₂_mono fun d _ => iSup_le fun _ => le_rfl
      have hxy' : ⁅x, y⁆ ∈ ⨆ b ∈ L, A b := hle hxy
      have hy' : y ∈ ⨆ b ∈ L, A b := (le_iSup₂ (f := fun b (_ : b ∈ L) => A b) b hb) hy
      have := Subgroup.mul_mem _ hxy' hy'
      rwa [commutatorElement_def, inv_mul_cancel_right] at this
    rw [iSup_mem_cons, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
      Set.mem_mul] at hg
    obtain ⟨x, hx, m, hm, rfl⟩ := hg
    obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem A h hnd hs hc' m hm
    have hfL : ∀ v ∈ L, Function.update f a x v = f v := fun v hv =>
      Function.update_of_ne (by rintro rfl; exact haL hv) _ _
    refine ⟨Function.update f a x, fun v hv => ?_, ?_⟩
    · rcases List.mem_cons.1 hv with rfl | hv
      · simpa using hx
      · rw [hfL v hv]
        exact hf v hv
    · rw [List.map_cons, List.prod_cons, Function.update_self, List.map_congr_left hfL]

end Collection

end CFSG.LieType.Steinberg
