module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup

@[expose] def NoQ8Fix (K : Type) [Group K] (H : Subgroup K) : Prop :=
  ∀ ψ : QuaternionGroup 2 →* MulAut K, Function.Injective ψ → ¬ ∀ a, ∀ h ∈ H, ψ a h = h

theorem noQ8Fix_of_dichotomy {K : Type} [Group K] {H : Subgroup K} (T : Set (MulAut K))
    (hT : ∀ α ∈ T, ∀ β ∈ T, α * β = β * α)
    (h : ∀ α : MulAut K, (∀ j ∈ H, α j = j) → α ∈ T ∨ α * α = 1) : NoQ8Fix K H := by
  intro ψ hψ hfix
  have hsq : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ψ q ∈ T := fun q hq => by
    rcases h (ψ q) (hfix q) with h1 | h1
    · exact h1
    · exact absurd (hψ (by rw [map_mul, h1, map_one])) hq
  have := hT _ (hsq (a 1) (by decide)) _ (hsq (xa 0) (by decide))
  rw [← map_mul, ← map_mul] at this
  exact absurd (hψ this) (by decide)

theorem NoQ8Fix.map {K K' : Type} [Group K] [Group K'] {H : Subgroup K} (h : NoQ8Fix K H)
    (e : K ≃* K') : NoQ8Fix K' (H.map e.toMonoidHom) := by
  intro ψ hψ hfix
  refine h ((MulAut.congr e).symm.toMonoidHom.comp ψ)
    ((MulAut.congr e).symm.injective.comp hψ) fun q x hx => ?_
  show e.symm (ψ q (e x)) = x
  rw [hfix q (e x) ⟨x, hx, rfl⟩, e.symm_apply_apply]

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.false_of_noQ8Fix (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (H : Subgroup ↥N)
    (hHt : H.map N.subtype ≤ Subgroup.centralizer ({t} : Set G))
    [Group.IsPerfect ↥(H.map N.subtype)]
    (hmax : ∀ M : Subgroup G, M ≤ N → M ≤ Subgroup.centralizer ({t} : Set G) → ⁅M, M⁆ = M →
      M ≤ H.map N.subtype)
    (hodd : NoOddNormal (H.map N.subtype)) (hA : NoQ8Fix ↥N H) : False := by
  have hRH := TightDatum.le_centralizer_of_maxPerfect hD (Subgroup.map_subtype_le H) hHt hmax hodd
  obtain ⟨φ, hφi, hφR, -⟩ := datum_exists_q8 hD
  let ψ : QuaternionGroup 2 →* MulAut ↥N := MulAut.conjNormal.comp φ
  have hψ : ∀ q (n : ↥N), ((ψ q n : ↥N) : G) = φ q * n * (φ q)⁻¹ := fun _ _ => rfl
  refine hA ψ ?_ fun q h hh => Subtype.ext ?_
  · rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : φ q ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have := congrArg Subtype.val (DFunLike.congr_fun hq ⟨n, hn⟩)
      rw [hψ] at this
      calc n * φ q = φ q * n * (φ q)⁻¹ * φ q := by rw [this]; rfl
        _ = φ q * n := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact hφi (h1.trans (map_one φ).symm)
  · rw [hψ]
    have := Subgroup.mem_centralizer_iff.mp (hRH (hφR q)) (h : G) ⟨h, hh, rfl⟩
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite G] in
theorem NoOddNormal.map {P : Type} [Group P] {H₀ : Subgroup P} (h : NoOddNormal H₀)
    (ι : P →* G) (hι : Function.Injective ι) : NoOddNormal (H₀.map ι) := by
  intro M hMH hMn hMo
  have hMr : M ≤ ι.range := hMH.trans (Subgroup.map_le_range ι H₀)
  have h0 : M.comap ι = ⊥ := by
    refine h (M.comap ι) (fun x hx => ?_) ⟨fun x hx g => ?_⟩ ?_
    · obtain ⟨y, hy, hyx⟩ := hMH hx
      rwa [← hι hyx]
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hx ⊢
      have hg : ι g ∈ H₀.map ι := ⟨g, g.2, rfl⟩
      have := hMn.conj_mem ⟨ι x, hMH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨ι g, hg⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    · have : Nat.card (M.comap ι) = Nat.card M := by
        rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hMr]
      rwa [this]
  rw [← Subgroup.map_comap_eq_self hMr, h0, Subgroup.map_bot]

theorem TightDatum.false_of_model (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {P : Type} [Group P] (e : ↥N ≃* P)
    (htN : t ∈ N) {u : P} (hu : e ⟨t, htN⟩ = u) (H₀ : Subgroup P) [Group.IsPerfect H₀]
    (hH₀ : H₀ ≤ Subgroup.centralizer ({u} : Set P))
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer ({u} : Set P) → ⁅M, M⁆ = M → M ≤ H₀)
    (hodd : NoOddNormal H₀) (hA : NoQ8Fix P H₀) : False := by
  set ι : P →* G := N.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hιu : ι u = t := by
    rw [hιdef, MonoidHom.comp_apply, ← hu]
    simp
  have hmap : (H₀.map e.symm.toMonoidHom).map N.subtype = H₀.map ι := by
    rw [Subgroup.map_map]
  have hιr : ι.range = N := by
    rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcent : ∀ x : P, Commute x u → Commute (ι x) t := fun x hx => by
    rw [← hιu]
    exact hx.map ι
  have : Group.IsPerfect ↥((H₀.map e.symm.toMonoidHom).map N.subtype) := by
    rw [hmap, ← Subgroup.range_subtype H₀, ← MonoidHom.range_comp]
    exact Group.IsPerfect.range _
  refine TightDatum.false_of_noQ8Fix hD hC (H₀.map e.symm.toMonoidHom) ?_ ?_ ?_ (hA.map e.symm)
  · rw [hmap]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hcent x (Subgroup.mem_centralizer_singleton_iff.mp (hH₀ hx))).eq
  · intro M hMN hMt hMp
    have hMr : M ≤ ι.range := hιr ▸ hMN
    have hM0 : ⁅M.comap ι, M.comap ι⁆ = M.comap ι := Subgroup.map_injective hι (by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hMr, hMp])
    have hM0t : M.comap ι ≤ Subgroup.centralizer ({u} : Set P) := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hMt hx)
      rw [← hιu, ← map_mul, ← map_mul] at h1
      exact hι h1
    rw [hmap, ← Subgroup.map_comap_eq_self hMr]
    exact Subgroup.map_mono (hmax _ hM0t hM0)
  · rw [hmap]
    exact hodd.map ι hι

end CFSG.ClassicalInvolution.Q3.TA3
