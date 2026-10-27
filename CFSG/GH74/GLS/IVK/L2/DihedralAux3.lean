module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.IVK.DihedralAux

open DihedralGroup

private theorem two_mul_eq_zero_iff'' {k : ℕ} [NeZero k] (i : ZMod k) (h : i + i = 0) :
    i = 0 ∨ i = ((k / 2 : ℕ) : ZMod k) := by
  have hneg : -i = i := neg_eq_of_add_eq_zero_right h
  rcases (ZMod.neg_eq_self_iff i).mp hneg with h0 | h1
  · left; exact h0
  · right
    have hk2 : k % 2 = 0 := by
      have := ZMod.val_lt i
      omega
    rw [← ZMod.natCast_zmod_val i]
    congr 1
    omega

private theorem pow_mem_iff_even'' {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2) {ρ : G}
    (hρ : ρ ∉ H) (k : ℕ) : ρ ^ k ∈ H ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hH, ih, Nat.even_add_one]
    simp [hρ]

theorem subset_of_comm_sr {N : ℕ} [NeZero N] (E : Subgroup (DihedralGroup N))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {j : ZMod N} (hj : sr j ∈ E) :
    ∀ x ∈ E, x * x = 1 →
      x = r 0 ∨ x = r ((N / 2 : ℕ) : ZMod N) ∨ x = sr j ∨ x = sr (j + ((N / 2 : ℕ) : ZMod N)) := by
  intro x hx hsq
  have hc := hcomm x hx (sr j) hj
  rcases x with i | m
  · rw [r_mul_sr, sr_mul_r] at hc
    have h2 : i + i = 0 := by
      have := sr.inj hc
      linear_combination (-1 : ZMod N) * this
    rcases two_mul_eq_zero_iff'' i h2 with h | h
    · left; rw [h]
    · right; left; rw [h]
  · rw [sr_mul_sr, sr_mul_sr] at hc
    have h2 : (m - j) + (m - j) = 0 := by
      have := r.inj hc
      linear_combination (-1 : ZMod N) * this
    rcases two_mul_eq_zero_iff'' (m - j) h2 with h | h
    · right; right; left
      have : m = j := by linear_combination h
      rw [this]
    · right; right; right
      have : m = j + ((N / 2 : ℕ) : ZMod N) := by linear_combination h
      rw [this]

theorem exists_sr_mem_of_card_four {N : ℕ} [NeZero N] (E : Subgroup (DihedralGroup N))
    (hsq : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 4) : ∃ j, sr j ∈ E := by
  by_contra hno
  push Not at hno
  have hsub : (E : Set (DihedralGroup N)) ⊆
      (({r 0, r ((N / 2 : ℕ) : ZMod N)} : Finset (DihedralGroup N)) : Set (DihedralGroup N)) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases x with i | m
    · have h := hsq _ hx
      rw [r_mul_r, one_def] at h
      have h2 : i + i = 0 := r.inj h
      rcases two_mul_eq_zero_iff'' i h2 with h | h
      · left; rw [h]
      · right; rw [h]
    · exact absurd hx (hno m)
  have hle : Nat.card E ≤ 2 := by
    have h1 : (E : Set (DihedralGroup N)).ncard ≤
        (({r 0, r ((N / 2 : ℕ) : ZMod N)} : Finset (DihedralGroup N)) :
          Set (DihedralGroup N)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : Nat.card E = (E : Set (DihedralGroup N)).ncard := Nat.card_coe_set_eq _
    have h3 : ({r 0, r ((N / 2 : ℕ) : ZMod N)} : Finset (DihedralGroup N)).card ≤ 2 :=
      Finset.card_le_two
    omega
  omega

theorem mem_iff_of_card_four {N : ℕ} [NeZero N] (E : Subgroup (DihedralGroup N))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 4) {j : ZMod N} (hj : sr j ∈ E) (x : DihedralGroup N) :
    x ∈ E ↔ x = r 0 ∨ x = r ((N / 2 : ℕ) : ZMod N) ∨ x = sr j ∨
      x = sr (j + ((N / 2 : ℕ) : ZMod N)) := by
  classical
  constructor
  · intro hx
    exact subset_of_comm_sr E hcomm hj x hx (hsq x hx)
  · intro hx
    by_contra hxE
    have hsub : (E : Set (DihedralGroup N)) ⊆
        (({r 0, r ((N / 2 : ℕ) : ZMod N), sr j, sr (j + ((N / 2 : ℕ) : ZMod N))} :
          Finset (DihedralGroup N)) : Set (DihedralGroup N)) := by
      intro y hy
      have := subset_of_comm_sr E hcomm hj y hy (hsq y hy)
      simpa using this
    have hxS : x ∈ (({r 0, r ((N / 2 : ℕ) : ZMod N), sr j, sr (j + ((N / 2 : ℕ) : ZMod N))} :
          Finset (DihedralGroup N))) := by
      simpa using hx
    have hsub' : (E : Set (DihedralGroup N)) ⊆
        ((({r 0, r ((N / 2 : ℕ) : ZMod N), sr j, sr (j + ((N / 2 : ℕ) : ZMod N))} :
          Finset (DihedralGroup N)).erase x : Finset (DihedralGroup N)) : Set (DihedralGroup N)) := by
      intro y hy
      have hyS := hsub hy
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      refine ⟨hyS, ?_⟩
      rintro rfl
      exact hxE hy
    have hle : Nat.card E ≤ 3 := by
      have h1 : (E : Set (DihedralGroup N)).ncard ≤
          ((({r 0, r ((N / 2 : ℕ) : ZMod N), sr j, sr (j + ((N / 2 : ℕ) : ZMod N))} :
            Finset (DihedralGroup N)).erase x : Finset (DihedralGroup N)) :
              Set (DihedralGroup N)).ncard := Set.ncard_le_ncard hsub' (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, Finset.card_erase_of_mem hxS] at h1
      have h2 : Nat.card E = (E : Set (DihedralGroup N)).ncard := Nat.card_coe_set_eq _
      have h4 : ({r 0, r ((N / 2 : ℕ) : ZMod N), sr j, sr (j + ((N / 2 : ℕ) : ZMod N))} :
          Finset (DihedralGroup N)).card ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine (Nat.succ_le_succ (Finset.card_insert_le _ _)).trans ?_
        refine (Nat.succ_le_succ (Nat.succ_le_succ (Finset.card_insert_le _ _))).trans ?_
        simp
      omega
    omega

theorem dihedral_conj_four {N : ℕ} [NeZero N] (H : Subgroup (DihedralGroup N)) (hH : H.index = 2)
    (U₁ U₂ : Subgroup (DihedralGroup N)) (h₁ : U₁ ≤ H) (h₂ : U₂ ≤ H)
    (hc₁ : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y = y * x) (hs₁ : ∀ x ∈ U₁, x * x = 1)
    (hcard₁ : Nat.card U₁ = 4)
    (hc₂ : ∀ x ∈ U₂, ∀ y ∈ U₂, x * y = y * x) (hs₂ : ∀ x ∈ U₂, x * x = 1)
    (hcard₂ : Nat.card U₂ = 4) :
    ∃ g : DihedralGroup N, ∀ x ∈ U₁, g * x * g⁻¹ ∈ U₂ := by
  obtain ⟨j₁, hj₁⟩ := exists_sr_mem_of_card_four U₁ hs₁ hcard₁
  obtain ⟨j₂, hj₂⟩ := exists_sr_mem_of_card_four U₂ hs₂ hcard₂
  have hrot : ∀ a : ZMod N, (r 1 : DihedralGroup N) ∈ H → (r a : DihedralGroup N) ∈ H := by
    intro a hρ
    have : (r a : DihedralGroup N) = (r 1) ^ a.val := by rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [this]
    exact H.pow_mem hρ _
  have hρ : (r 1 : DihedralGroup N) ∉ H := by
    intro hρ
    have htop : H = ⊤ := by
      rw [eq_top_iff]
      rintro (a | b) -
      · exact hrot a hρ
      · have : (sr b : DihedralGroup N) = sr j₁ * r (b - j₁) := by
          rw [sr_mul_r]; congr 1; ring
        rw [this]
        exact H.mul_mem (h₁ hj₁) (hrot _ hρ)
    rw [htop, Subgroup.index_top] at hH
    omega
  have hmem : (r (j₂ - j₁) : DihedralGroup N) ∈ H := by
    have := H.mul_mem (h₁ hj₁) (h₂ hj₂)
    rwa [sr_mul_sr] at this
  have heven : Even (j₂ - j₁).val := by
    rw [← pow_mem_iff_even'' H hH hρ, r_one_pow, ZMod.natCast_zmod_val]
    exact hmem
  obtain ⟨c, hc⟩ := heven
  have ha : j₂ - j₁ = (c : ZMod N) + c := by
    rw [← ZMod.natCast_zmod_val (j₂ - j₁), hc]; push_cast; ring
  have hz : (r ((N / 2 : ℕ) : ZMod N) : DihedralGroup N) ∈ U₂ :=
    (mem_iff_of_card_four U₂ hc₂ hs₂ hcard₂ hj₂ _).mpr (Or.inr (Or.inl rfl))
  have hrconj : ∀ i : ZMod N, r (-(c : ZMod N)) * r i * (r (-(c : ZMod N)))⁻¹ = (r i : DihedralGroup N) := by
    intro i
    rw [inv_r, r_mul_r, r_mul_r]; congr 1; ring
  have hsconj : ∀ k : ZMod N, r (-(c : ZMod N)) * sr k * (r (-(c : ZMod N)))⁻¹ =
      (sr (k + c + c) : DihedralGroup N) := by
    intro k
    rw [inv_r, r_mul_sr, sr_mul_r]; congr 1; ring
  refine ⟨r (-(c : ZMod N)), ?_⟩
  intro x hx
  rcases (mem_iff_of_card_four U₁ hc₁ hs₁ hcard₁ hj₁ x).mp hx with rfl | rfl | rfl | rfl
  · rw [hrconj]
    rw [← one_def]
    exact U₂.one_mem
  · rw [hrconj]
    exact hz
  · rw [hsconj]
    have : j₁ + c + c = j₂ := by linear_combination (-1 : ZMod N) * ha
    rw [this]
    exact hj₂
  · rw [hsconj]
    have : j₁ + ((N / 2 : ℕ) : ZMod N) + c + c = j₂ + ((N / 2 : ℕ) : ZMod N) := by
      linear_combination (-1 : ZMod N) * ha
    rw [this]
    exact (mem_iff_of_card_four U₂ hc₂ hs₂ hcard₂ hj₂ _).mpr (Or.inr (Or.inr (Or.inr rfl)))

theorem exists_conj_of_four_subgroups {G : Type*} [Group G] (D H : Subgroup G) (hHD : H ≤ D)
    {N : ℕ} [NeZero N] (φ : ↥D ≃* DihedralGroup N) (hH : (H.subgroupOf D).index = 2)
    (U₁ U₂ : Subgroup G) (h₁ : U₁ ≤ H) (h₂ : U₂ ≤ H)
    (hc₁ : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y = y * x) (hs₁ : ∀ x ∈ U₁, x * x = 1)
    (hcard₁ : Nat.card U₁ = 4)
    (hc₂ : ∀ x ∈ U₂, ∀ y ∈ U₂, x * y = y * x) (hs₂ : ∀ x ∈ U₂, x * x = 1)
    (hcard₂ : Nat.card U₂ = 4) :
    ∃ g ∈ D, U₁.map (MulAut.conj g).toMonoidHom = U₂ := by
  let H' : Subgroup (DihedralGroup N) := (H.subgroupOf D).map φ.toMonoidHom
  have hH' : H'.index = 2 := by
    rw [show H' = (H.subgroupOf D).map (φ : ↥D →* DihedralGroup N) from rfl,
      Subgroup.index_map_equiv _ φ, hH]
  let V₁ : Subgroup (DihedralGroup N) := (U₁.subgroupOf D).map φ.toMonoidHom
  let V₂ : Subgroup (DihedralGroup N) := (U₂.subgroupOf D).map φ.toMonoidHom
  have hmemV : ∀ (U : Subgroup G) (hU : U ≤ D) (y : DihedralGroup N),
      y ∈ (U.subgroupOf D).map φ.toMonoidHom ↔ ∃ u : ↥D, (u : G) ∈ U ∧ φ u = y := by
    intro U hU y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hcardV : ∀ (U : Subgroup G) (hU : U ≤ D),
      Nat.card ((U.subgroupOf D).map φ.toMonoidHom) = Nat.card U := by
    intro U hU
    rw [Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  have hV₁ : V₁ ≤ H' := Subgroup.map_mono (fun x hx => h₁ hx)
  have hV₂ : V₂ ≤ H' := Subgroup.map_mono (fun x hx => h₂ hx)
  have hcommV : ∀ (U : Subgroup G) (hU : U ≤ D), (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) →
      ∀ x ∈ (U.subgroupOf D).map φ.toMonoidHom, ∀ y ∈ (U.subgroupOf D).map φ.toMonoidHom,
        x * y = y * x := by
    intro U hU hc x hx y hy
    obtain ⟨a, ha, rfl⟩ := (hmemV U hU x).mp hx
    obtain ⟨b, hb, rfl⟩ := (hmemV U hU y).mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ ha _ hb)
  have hsqV : ∀ (U : Subgroup G) (hU : U ≤ D), (∀ x ∈ U, x * x = 1) →
      ∀ x ∈ (U.subgroupOf D).map φ.toMonoidHom, x * x = 1 := by
    intro U hU hs x hx
    obtain ⟨a, ha, rfl⟩ := (hmemV U hU x).mp hx
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hs _ ha)
    rw [this, map_one]
  obtain ⟨g', hg'⟩ := dihedral_conj_four H' hH' V₁ V₂ hV₁ hV₂
    (hcommV U₁ (h₁.trans hHD) hc₁) (hsqV U₁ (h₁.trans hHD) hs₁)
    ((hcardV U₁ (h₁.trans hHD)).trans hcard₁)
    (hcommV U₂ (h₂.trans hHD) hc₂) (hsqV U₂ (h₂.trans hHD) hs₂)
    ((hcardV U₂ (h₂.trans hHD)).trans hcard₂)
  set g : ↥D := φ.symm g' with hg
  refine ⟨(g : G), g.2, ?_⟩
  have hle : U₁.map (MulAut.conj (g : G)).toMonoidHom ≤ U₂ := by
    rintro _ ⟨u, hu, rfl⟩
    have huD : u ∈ D := hHD (h₁ hu)
    have := hg' (φ ⟨u, huD⟩) ((hmemV U₁ (h₁.trans hHD) _).mpr ⟨⟨u, huD⟩, hu, rfl⟩)
    obtain ⟨w, hw, hwe⟩ := (hmemV U₂ (h₂.trans hHD) _).mp this
    have hw' : w = g * ⟨u, huD⟩ * g⁻¹ := by
      apply φ.injective
      rw [hwe, map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply]
    have : (w : G) = (g : G) * u * (g : G)⁻¹ := by rw [hw']; rfl
    show (g : G) * u * (g : G)⁻¹ ∈ U₂
    rw [← this]
    exact hw
  have hfin : Finite ↥U₂ := Nat.finite_of_card_ne_zero (by omega)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective, hcard₁, hcard₂]

end CFSG.GH74.GLS.IVK.DihedralAux
