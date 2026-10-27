module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4c

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X]

theorem conjugate_conjugate_mul (H : Subgroup X) (g k : X) :
    conjugate (conjugate H g) k = conjugate H (g * k) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  rw [show g * (k * x * k⁻¹) * g⁻¹ = g * k * x * (g * k)⁻¹ by group]

theorem conjugate_one' (H : Subgroup X) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem conjugate_le_of_mem_normalizer' {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : conjugate H g ≤ H := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have := (mem_normalizer_iff.mp (inv_mem hg) _).mp hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem conjugate_inf (H K : Subgroup X) (g : X) :
    conjugate (H ⊓ K) g = conjugate H g ⊓ conjugate K g := by
  ext x
  rw [mem_inf, mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff, mem_inf]

theorem conjugate_sq_eq_one {E : Subgroup X} (hE : ∀ x ∈ E, x * x = 1) (g : X) :
    ∀ x ∈ conjugate E g, x * x = 1 := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h1 := hE _ hx
  calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

theorem le_normalizer_of_commute {A B : Subgroup X} (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    B ≤ normalizer (A : Set X) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rwa [← hAB x hx y hy, mul_inv_cancel_right]
  · intro hx
    have h1 := hAB _ hx y hy
    have h2 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
        _ = y * x * y⁻¹ := by group
    rw [h2]
    exact hx

theorem exists_mul_of_mem_sup {A B : Subgroup X} (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    {x : X} (hx : x ∈ A ⊔ B) : ∃ y ∈ A, ∃ w ∈ B, x = y * w := by
  have hx' : x ∈ ((A ⊔ B : Subgroup X) : Set X) := hx
  rw [coe_mul_of_right_le_normalizer_left A B (le_normalizer_of_commute hAB)] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := hx'
  exact ⟨y, hy, w, hw, rfl⟩

theorem sup_sq_eq_one {A B : Subgroup X} (hA : ∀ x ∈ A, x * x = 1) (hB : ∀ x ∈ B, x * x = 1)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : ∀ x ∈ A ⊔ B, x * x = 1 := by
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := exists_mul_of_mem_sup hAB hx
  calc y * w * (y * w) = y * (w * y) * w := by group
    _ = y * (y * w) * w := by rw [hAB y hy w hw]
    _ = (y * y) * (w * w) := by group
    _ = 1 := by rw [hA y hy, hB w hw, one_mul]

theorem card_sup_of_commute {A B : Subgroup X} (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hdisj : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B :=
  CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer A B
    (le_normalizer_of_commute hAB) (disjoint_iff.mpr hdisj)

@[expose] def Je (H : Subgroup X) : Subgroup X :=
  ⨆ (E : Subgroup X) (_ : E ≤ H ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 64), E

theorem le_Je {H E : Subgroup X} (hEH : E ≤ H) (hE : ∀ x ∈ E, x * x = 1)
    (h64 : Nat.card E = 64) : E ≤ Je H :=
  le_iSup₂_of_le E ⟨hEH, hE, h64⟩ le_rfl

theorem Je_le (H : Subgroup X) : Je H ≤ H :=
  iSup₂_le fun _ h => h.1

theorem Je_le_of {H K : Subgroup X}
    (hK : ∀ E : Subgroup X, E ≤ H → (∀ x ∈ E, x * x = 1) → Nat.card E = 64 → E ≤ K) :
    Je H ≤ K :=
  iSup₂_le fun E h => hK E h.1 h.2.1 h.2.2

variable [Finite X]

theorem conjugate_Je_eq {H : Subgroup X} {g : X} (hg : conjugate (Je H) g ≤ H) :
    conjugate (Je H) g = Je H := by
  refine eq_of_le_of_card_ge ?_ (card_conjugate _ _).ge
  change (Je H).map (MulAut.conj g⁻¹).toMonoidHom ≤ Je H
  rw [map_le_iff_le_comap]
  refine Je_le_of fun E hEH hE h64 => ?_
  rw [← map_le_iff_le_comap]
  have hle : conjugate E g ≤ conjugate (Je H) g := map_mono (le_Je hEH hE h64)
  exact le_Je (hle.trans hg) (conjugate_sq_eq_one hE g) ((card_conjugate E g).trans h64)

theorem normalizer_le_normalizer_Je (H : Subgroup X) :
    normalizer (H : Set X) ≤ normalizer (Je H : Set X) := by
  intro g hg
  have h1 : conjugate (Je H) g ≤ H :=
    (map_mono (Je_le H)).trans (conjugate_le_of_mem_normalizer' hg)
  exact mem_normalizer_of_conjugate_eq (conjugate_Je_eq h1)

theorem exists_normalizer_conj_of_weaklyClosed {S₁ F : Subgroup X}
    (hS₁ : ∃ R : Sylow 2 X, (R : Subgroup X) = S₁) (hFS : F ≤ S₁)
    (hWC : ∀ g : X, conjugate F g ≤ S₁ → conjugate F g = F) {w g : X}
    (hw : F ≤ centralizer ({w} : Set X)) (hwg : F ≤ centralizer ({g⁻¹ * w * g} : Set X)) :
    ∃ n ∈ normalizer (F : Set X), n⁻¹ * w * n = g⁻¹ * w * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hS₁
  set t := g⁻¹ * w * g with ht
  set C := centralizer ({t} : Set X) with hC
  have hF2 : IsPGroup 2 F := (hR ▸ R.isPGroup' : IsPGroup 2 S₁).to_le hFS
  have hFgC : conjugate F g ≤ C := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    rw [hC, mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (hw hx)
    calc x * t = g⁻¹ * ((g * x * g⁻¹) * w) * g := by rw [ht]; group
      _ = g⁻¹ * (w * (g * x * g⁻¹)) * g := by rw [h1]
      _ = t * x := by rw [ht]; group
  obtain ⟨V₁, hV₁⟩ := (hF2.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨V₂, hV₂⟩ := ((hF2.map (MulAut.conj g⁻¹).toMonoidHom :
    IsPGroup 2 (conjugate F g)).comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) V₂ V₁
  have hmap : (V₂ : Subgroup ↥C).map (MulAut.conj c).toMonoidHom = (V₁ : Subgroup ↥C) := by
    rw [← hc]
    rfl
  set n₀ := g * (c : X)⁻¹ with hn₀
  have hFn₀ : ∀ x ∈ conjugate F n₀, ∃ hx : x ∈ C, (⟨x, hx⟩ : ↥C) ∈ V₁ := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have hy : (c : X)⁻¹ * x * c ∈ conjugate F g := by
      rw [mem_conjugate_iff]
      rwa [show g * ((c : X)⁻¹ * x * c) * g⁻¹ = n₀ * x * n₀⁻¹ by rw [hn₀]; group]
    have hyC := hFgC hy
    have hyV : (⟨_, hyC⟩ : ↥C) ∈ V₂ := hV₂ (show (⟨_, hyC⟩ : ↥C) ∈ (conjugate F g).comap
      C.subtype from hy)
    have h1 := hmap ▸ mem_map_of_mem (MulAut.conj c).toMonoidHom hyV
    have hxC : x ∈ C := by
      have := mul_mem (mul_mem c.2 hyC) (inv_mem c.2)
      rwa [show (c : X) * ((c : X)⁻¹ * x * c) * (c : X)⁻¹ = x by group] at this
    refine ⟨hxC, ?_⟩
    have heq : (MulAut.conj c).toMonoidHom (⟨_, hyC⟩ : ↥C) = ⟨x, hxC⟩ := by
      apply Subtype.ext
      change (c : X) * ((c : X)⁻¹ * x * c) * (c : X)⁻¹ = x
      group
    rw [heq] at h1
    exact h1
  obtain ⟨R₁, hR₁⟩ := ((V₁.isPGroup'.map C.subtype : IsPGroup 2 ((V₁ : Subgroup ↥C).map
    C.subtype))).exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq X R R₁
  have hmapR : (R : Subgroup X).map (MulAut.conj y).toMonoidHom = (R₁ : Subgroup X) := by
    rw [← hy]
    rfl
  have hmemR : ∀ x : X, y * x * y⁻¹ ∈ (R₁ : Subgroup X) → x ∈ S₁ := by
    intro x hx
    rw [← hmapR] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    have hrx' : y * r * y⁻¹ = y * x * y⁻¹ := hrx
    have : r = x := by
      have := congrArg (fun v => y⁻¹ * v * y) hrx'
      simpa [mul_assoc] using this
    rw [← hR, ← this]
    exact hr
  have hV₁R : ∀ x (hx : x ∈ C), (⟨x, hx⟩ : ↥C) ∈ V₁ → x ∈ (R₁ : Subgroup X) :=
    fun x hx hxV => hR₁ ⟨⟨x, hx⟩, hxV, rfl⟩
  have hFy : conjugate F y = F := by
    refine hWC y fun x hx => ?_
    rw [mem_conjugate_iff] at hx
    apply hmemR
    have hxC : y * x * y⁻¹ ∈ C := hwg hx
    exact hV₁R _ hxC (hV₁ (show (⟨_, hxC⟩ : ↥C) ∈ F.comap C.subtype from hx))
  have hFny : conjugate F (n₀ * y) = F := by
    refine hWC (n₀ * y) fun x hx => ?_
    rw [mem_conjugate_iff] at hx
    apply hmemR
    have h1 : y * x * y⁻¹ ∈ conjugate F n₀ := by
      rw [mem_conjugate_iff]
      rwa [show n₀ * (y * x * y⁻¹) * n₀⁻¹ = n₀ * y * x * (n₀ * y)⁻¹ by group]
    obtain ⟨hxC, hxV⟩ := hFn₀ _ h1
    exact hV₁R _ hxC hxV
  have hFn : conjugate F n₀ = F := by
    have h1 : conjugate F n₀ = conjugate (conjugate F (n₀ * y)) y⁻¹ := by
      rw [conjugate_conjugate_mul, mul_inv_cancel_right]
    have h2 : conjugate F y⁻¹ = F := by
      conv_rhs => rw [← conjugate_one' F, ← mul_inv_cancel y, ← conjugate_conjugate_mul, hFy]
    rw [h1, hFny, h2]
  refine ⟨n₀, mem_normalizer_of_conjugate_eq hFn, ?_⟩
  have hct : (c : X) * t = t * c := mem_centralizer_singleton_iff.mp c.2
  calc n₀⁻¹ * w * n₀ = (c : X) * t * (c : X)⁻¹ := by rw [hn₀, ht]; group
    _ = t := by rw [hct, mul_inv_cancel_right]

omit [Finite X] in
@[expose] noncomputable def rhoE (J : Subgroup X) (x : X) : MulAut (↥J ⧸ pPrimeCore 2 ↥J) :=
  Function.extend (fun n : ↥(normalizer (J : Set X)) => (n : X))
    (fun n => Eight.oddBarAction J n) 1 x

omit [Finite X]

theorem rhoE_of_mem {J : Subgroup X} {x : X} (hx : x ∈ normalizer (J : Set X)) :
    rhoE J x = Eight.oddBarAction J ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply _ _ (⟨x, hx⟩ : ↥(normalizer (J : Set X)))

theorem rhoE_mul {J : Subgroup X} {x y : X} (hx : x ∈ normalizer (J : Set X))
    (hy : y ∈ normalizer (J : Set X)) : rhoE J (x * y) = rhoE J x * rhoE J y := by
  rw [rhoE_of_mem hx, rhoE_of_mem hy, rhoE_of_mem (mul_mem hx hy), ← map_mul]
  rfl

theorem rhoE_inv {J : Subgroup X} {x : X} (hx : x ∈ normalizer (J : Set X)) :
    rhoE J x⁻¹ = (rhoE J x)⁻¹ := by
  rw [rhoE_of_mem hx, rhoE_of_mem (inv_mem hx), ← map_inv]
  rfl

theorem rhoE_one (J : Subgroup X) : rhoE J 1 = 1 := by
  rw [rhoE_of_mem (one_mem _)]
  exact map_one _

theorem rhoE_eq_one_iff {J : Subgroup X} {x : X} (hx : x ∈ normalizer (J : Set X)) :
    rhoE J x = 1 ↔ x ∈ coreActionKernel J := by
  rw [rhoE_of_mem hx, ← MonoidHom.mem_ker]
  exact Eight.mem_ker_oddBarAction

theorem rhoE_mem_rhoImg {J W : Subgroup X} (hWN : W ≤ normalizer (J : Set X)) {x : X}
    (hx : x ∈ W) : rhoE J x ∈ rhoImg J W := by
  rw [rhoE_of_mem (hWN hx)]
  exact mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem exists_of_mem_rhoImg {J W : Subgroup X} {σ : MulAut (↥J ⧸ pPrimeCore 2 ↥J)}
    (hσ : σ ∈ rhoImg J W) : ∃ x ∈ W, x ∈ normalizer (J : Set X) ∧ rhoE J x = σ := by
  obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hσ
  exact ⟨x, mem_subgroupOf.mp hx, hxN, rhoE_of_mem hxN⟩

theorem rhoE_of_mem_J {J : Subgroup X} {d : X} (hd : d ∈ J) :
    rhoE J d = MulAut.conj (((⟨d, hd⟩ : ↥J)) : ↥J ⧸ pPrimeCore 2 ↥J) := by
  rw [rhoE_of_mem (le_normalizer hd)]
  exact rho_of_mem hd

theorem card_eq_card_rhoImg_mul {J W : Subgroup X} (hWN : W ≤ normalizer (J : Set X)) :
    Nat.card W = Nat.card (rhoImg J W) * Nat.card ↥(W ⊓ coreActionKernel J) := by
  set f : ↥W →* MulAut (↥J ⧸ pPrimeCore 2 ↥J) :=
    (Eight.oddBarAction J).comp (inclusion hWN) with hf
  have hrange : f.range = rhoImg J W := by
    rw [hf, MonoidHom.range_comp]
    congr 1
    ext x
    rw [MonoidHom.mem_range, mem_subgroupOf]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(W ⊓ coreActionKernel J) := by
    have h1 : f.ker = (W ⊓ coreActionKernel J).subgroupOf W := by
      ext w
      rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
      constructor
      · intro h
        exact ⟨w.2, Eight.mem_ker_oddBarAction.mp h⟩
      · rintro ⟨-, h⟩
        exact Eight.mem_ker_oddBarAction.mpr h
    rw [h1]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  rw [← h1, mul_comm]

abbrev S1 (S : Subgroup X) (u : X) : Subgroup X := S ⊔ zpowers u

theorem mem_S1 {S : Subgroup X} {u : X} (hu : u ∈ normalizer (S : Set X)) (huu : u * u ∈ S)
    {x : X} : x ∈ S1 S u ↔ x ∈ S ∨ x * u⁻¹ ∈ S := by
  have hN : zpowers u ≤ normalizer (S : Set X) := (zpowers_le).mpr hu
  have hsq : ∀ m : ℤ, u ^ (2 * m) ∈ S := fun m => by
    rw [zpow_mul, zpow_two]
    exact zpow_mem huu m
  constructor
  · intro hx
    have hx' : x ∈ ((S ⊔ zpowers u : Subgroup X) : Set X) := hx
    rw [coe_mul_of_right_le_normalizer_left S (zpowers u) hN] at hx'
    obtain ⟨s, hs, v, hv, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    change s ∈ S at hs
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exact Or.inl (mul_mem hs (hsq m))
    · right
      change s * u ^ (2 * m + 1) * u⁻¹ ∈ S
      rw [show s * u ^ (2 * m + 1) * u⁻¹ = s * u ^ (2 * m) by rw [zpow_add_one]; group]
      exact mul_mem hs (hsq m)
  · rintro (h | h)
    · exact mem_sup_left h
    · have := mul_mem_sup h (mem_zpowers u)
      rwa [inv_mul_cancel_right] at this

theorem isPGroup_S1 {S : Subgroup X} {u : X} (hS : IsPGroup 2 S)
    (hu : u ∈ normalizer (S : Set X)) (huu : u * u ∈ S) : IsPGroup 2 (S1 S u) := by
  rintro ⟨x, hx⟩
  rcases (mem_S1 hu huu).mp hx with h | h
  · obtain ⟨k, hk⟩ := hS ⟨x, h⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  · have hxx : x * x ∈ S := by
      have h1 : x * x = (x * u⁻¹) * (u * (x * u⁻¹) * u⁻¹) * (u * u) := by group
      rw [h1]
      exact mul_mem (mul_mem h ((mem_normalizer_iff.mp hu _).mp h)) huu
    obtain ⟨k, hk⟩ := hS ⟨x * x, hxx⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (x * x) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, pow_two]
    exact hk'

theorem le_S1 (S : Subgroup X) (u : X) : S ≤ S1 S u := le_sup_left

theorem mem_S1_self (S : Subgroup X) (u : X) : u ∈ S1 S u := mem_sup_right (mem_zpowers u)

end Seven

end CFSG.ComponentClassification.GSThmB
