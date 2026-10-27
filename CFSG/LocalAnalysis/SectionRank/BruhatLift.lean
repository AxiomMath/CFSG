module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools

public section

namespace CFSG.SectionRank

section Bruhat

variable {G E W : Type*} [Group G] [Group E] [Group W] {ι : Type*}

theorem exists_lift_subgroup_of_bruhat' (π : E →* G) (B : Subgroup G) (Bh : Subgroup E)
    (hBmap : Bh.map π = B) (hBinj : ∀ b ∈ Bh, π b = 1 → b = 1) (ν : W → E) (hν1 : ν 1 = 1)
    (s : ι → W) (hs2 : ∀ i, s i * s i = 1) (Inc : ι → W → Prop)
    (hInc : ∀ i w, Inc i w ∨ Inc i (s i * w))
    (hνmul : ∀ i w, Inc i w → ν (s i * w) = ν (s i) * ν w)
    (hνinv : ∀ i, ν (s i) * ν (s i) = 1)
    (hgen : Subgroup.closure ((B : Set G) ∪ Set.range fun i => π (ν (s i))) = ⊤)
    (hdisj : ∀ w, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ * π (ν w) * b₂ = 1 → w = 1)
    (hcell : ∀ i w, Inc i w → ∀ b ∈ Bh, ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh,
      ν (s i) * b * ν w = b₁ * ν (s i * w) * b₂)
    (hrank : ∀ i, ∀ b ∈ Bh, ν (s i) * b * ν (s i) ∈ Bh ∨
      ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh, ν (s i) * b * ν (s i) = b₁ * ν (s i) * b₂) :
    ∃ J : Subgroup E, J.map π = ⊤ ∧ ∀ j ∈ J, π j = 1 → j = 1 := by
  set X : Set E := {e | ∃ w : W, ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh, e = b₁ * ν w * b₂} with hX
  have hXB : ∀ b ∈ Bh, ∀ e ∈ X, b * e ∈ X := by
    rintro b hb _ ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨w, b * b₁, Bh.mul_mem hb hb₁, b₂, hb₂, by group⟩
  have hXs : ∀ i, ∀ e ∈ X, ν (s i) * e ∈ X := by
    rintro i _ ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩
    rcases hInc i w with hlt | hgt
    · obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := hcell i w hlt b₁ hb₁
      exact ⟨s i * w, c₁, hc₁, c₂ * b₂, Bh.mul_mem hc₂ hb₂, by
        rw [← mul_assoc, ← mul_assoc, hc]; group⟩
    ·
      set v := s i * w with hv
      have hw : s i * v = w := by rw [hv, ← mul_assoc, hs2, one_mul]
      have hνw : ν w = ν (s i) * ν v := by rw [← hw]; exact hνmul i v hgt
      rcases hrank i b₁ hb₁ with hB | ⟨c₁, hc₁, c₂, hc₂, hc⟩
      · exact ⟨v, ν (s i) * b₁ * ν (s i), hB, b₂, hb₂, by rw [hνw]; group⟩
      · obtain ⟨d₁, hd₁, d₂, hd₂, hd⟩ := hcell i v hgt c₂ hc₂
        refine ⟨w, c₁ * d₁, Bh.mul_mem hc₁ hd₁, d₂ * b₂, Bh.mul_mem hd₂ hb₂, ?_⟩
        calc ν (s i) * (b₁ * ν w * b₂) = (ν (s i) * b₁ * ν (s i)) * ν v * b₂ := by
              rw [hνw]; group
          _ = c₁ * (ν (s i) * c₂ * ν v) * b₂ := by rw [hc]; group
          _ = c₁ * (d₁ * ν (s i * v) * d₂) * b₂ := by rw [hd]
          _ = c₁ * d₁ * ν w * (d₂ * b₂) := by rw [hw]; group
  set J : Subgroup E := Subgroup.closure ((Bh : Set E) ∪ Set.range fun i => ν (s i)) with hJ
  have hJX : ∀ j ∈ J, j ∈ X := by
    intro j hj
    induction hj using Subgroup.closure_induction_left with
    | one => exact ⟨1, 1, Bh.one_mem, 1, Bh.one_mem, by rw [hν1]; group⟩
    | mul_left x hx y _ ih =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact hXB x hx y ih
      · exact hXs i y ih
    | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | ⟨i, rfl⟩
      · exact hXB x⁻¹ (Bh.inv_mem hx) y ih
      · have hinv : (ν (s i))⁻¹ = ν (s i) := inv_eq_of_mul_eq_one_right (hνinv i)
        rw [hinv]
        exact hXs i y ih
  refine ⟨J, ?_, fun j hj hj1 => ?_⟩
  · rw [hJ, MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, hBmap,
      ← Set.range_comp]
    exact hgen
  · obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := hJX j hj
    have hπ : π b₁ * π (ν w) * π b₂ = 1 := by rw [← map_mul, ← map_mul]; exact hj1
    have hw1 : w = 1 := hdisj w (π b₁) (hBmap ▸ Subgroup.mem_map_of_mem π hb₁) (π b₂)
      (hBmap ▸ Subgroup.mem_map_of_mem π hb₂) hπ
    subst hw1
    rw [hν1, mul_one] at hj1 ⊢
    exact hBinj _ (Bh.mul_mem hb₁ hb₂) hj1

theorem exists_lift_subgroup_of_bruhat (π : E →* G) (B : Subgroup G) (Bh : Subgroup E)
    (hBmap : Bh.map π = B) (hBinj : ∀ b ∈ Bh, π b = 1 → b = 1) (ν : W → E) (hν1 : ν 1 = 1)
    (s : ι → W) (hs2 : ∀ i, s i * s i = 1) (ℓ : W → ℕ)
    (hℓ : ∀ i w, ℓ (s i * w) = ℓ w + 1 ∨ ℓ w = ℓ (s i * w) + 1)
    (hνmul : ∀ i w, ℓ (s i * w) = ℓ w + 1 → ν (s i * w) = ν (s i) * ν w)
    (hνinv : ∀ i, ν (s i) * ν (s i) = 1)
    (hgen : Subgroup.closure ((B : Set G) ∪ Set.range fun i => π (ν (s i))) = ⊤)
    (hdisj : ∀ w, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ * π (ν w) * b₂ = 1 → w = 1)
    (hcell : ∀ i w, ℓ (s i * w) = ℓ w + 1 → ∀ b ∈ Bh, ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh,
      ν (s i) * b * ν w = b₁ * ν (s i * w) * b₂)
    (hrank : ∀ i, ∀ b ∈ Bh, ν (s i) * b * ν (s i) ∈ Bh ∨
      ∃ b₁ ∈ Bh, ∃ b₂ ∈ Bh, ν (s i) * b * ν (s i) = b₁ * ν (s i) * b₂) :
    ∃ J : Subgroup E, J.map π = ⊤ ∧ ∀ j ∈ J, π j = 1 → j = 1 := by
  refine exists_lift_subgroup_of_bruhat' π B Bh hBmap hBinj ν hν1 s hs2
    (fun i w => ℓ (s i * w) = ℓ w + 1) (fun i w => ?_) hνmul hνinv hgen hdisj hcell hrank
  rcases hℓ i w with h | h
  · exact Or.inl h
  · right
    rw [← mul_assoc, hs2, one_mul]
    exact h

theorem exists_section_of_lift_subgroup (π : E →* G) {J : Subgroup E} (hJ : J.map π = ⊤)
    (hinj : ∀ j ∈ J, π j = 1 → j = 1) : ∃ σ : G →* E, ∀ x, π (σ x) = x := by
  let ρ : J →* G := π.comp J.subtype
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro j hj
    exact Subtype.ext (hinj j j.2 hj)
  have hρsurj : Function.Surjective ρ := by
    intro x
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 (hJ ▸ Subgroup.mem_top x)
    exact ⟨⟨j, hj⟩, rfl⟩
  let e : J ≃* G := MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  exact ⟨J.subtype.comp e.symm.toMonoidHom, fun x => e.apply_symm_apply x⟩

end Bruhat

section Dihedral

variable {E : Type*} [Group E]

theorem card_closure_pair_le [Finite E] {a b : E} (ha : a * a = 1) (hb : b * b = 1) {m : ℕ}
    (hm : 0 < m) (hab : (a * b) ^ m = 1) :
    Nat.card (Subgroup.closure ({a, b} : Set E)) ≤ 2 * m := by
  classical
  set r := a * b with hr
  set P : Finset E := (Finset.range m).image (fun k => r ^ k) with hP
  set S : Finset E := P ∪ (Finset.range m).image (fun k => r ^ k * a) with hS
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hpow : ∀ n : ℕ, r ^ n ∈ P := by
    intro n
    refine Finset.mem_image.2 ⟨n % m, Finset.mem_range.2 (Nat.mod_lt _ hm), ?_⟩
    conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hab, one_pow, mul_one]
  have hinvpow : ∀ k : ℕ, (r ^ k)⁻¹ ∈ P := by
    intro k
    have : (r ^ k)⁻¹ = r ^ (m * k - k) := by
      rw [eq_comm, ← mul_inv_eq_one, inv_inv, ← pow_add,
        Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hm), pow_mul, hab, one_pow]
    rw [this]
    exact hpow _
  have hara : a * r * a⁻¹ = r⁻¹ := by
    rw [hr, hainv, mul_inv_rev, hainv, hbinv, ← mul_assoc, ha, one_mul]
  have hconj : ∀ k : ℕ, a * r ^ k * a = (r ^ k)⁻¹ := by
    intro k
    calc a * r ^ k * a = a * r ^ k * a⁻¹ := by rw [hainv]
      _ = (a * r * a⁻¹) ^ k := conj_pow.symm
      _ = (r ^ k)⁻¹ := by rw [hara, inv_pow]
  have hmemP : ∀ x ∈ P, x ∈ S := fun x hx => Finset.mem_union_left _ hx
  have hmemPa : ∀ x ∈ P, x * a ∈ S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, hj, rfl⟩)
  have hSa : ∀ x ∈ S, a * x ∈ S := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h <;> obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
    · have e : a * r ^ k = (r ^ k)⁻¹ * a := by rw [← hconj k, mul_assoc, ha, mul_one]
      rw [e]
      exact hmemPa _ (hinvpow k)
    · rw [← mul_assoc, hconj k]
      exact hmemP _ (hinvpow k)
  have hSr : ∀ x ∈ S, r * x ∈ S := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h <;> obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
    · rw [← pow_succ']
      exact hmemP _ (hpow _)
    · rw [← mul_assoc, ← pow_succ']
      exact hmemPa _ (hpow _)
  have hbr : b = a * r := by rw [hr, ← mul_assoc, ha, one_mul]
  have hSb : ∀ x ∈ S, b * x ∈ S := fun x hx => by
    rw [hbr, mul_assoc]
    exact hSa _ (hSr _ hx)
  have hle : (Subgroup.closure ({a, b} : Set E) : Set E) ⊆ S := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact hmemP _ (Finset.mem_image.2 ⟨0, Finset.mem_range.2 hm, pow_zero r⟩)
    | mul_left x hx y _ ih =>
      rcases hx with rfl | rfl
      · exact hSa _ ih
      · exact hSb _ ih
    | inv_mul_cancel x hx y _ ih =>
      rcases hx with rfl | rfl
      · rw [hainv]; exact hSa _ ih
      · rw [hbinv]; exact hSb _ ih
  calc Nat.card (Subgroup.closure ({a, b} : Set E))
      ≤ S.card := by
        rw [← Nat.card_eq_finsetCard]
        exact Nat.card_mono (Finset.finite_toSet S) hle
    _ ≤ m + m := (Finset.card_union_le _ _).trans (add_le_add
        (Finset.card_image_le.trans (by simp)) (Finset.card_image_le.trans (by simp)))
    _ = 2 * m := by ring

end Dihedral

section Torus

variable {E G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}

noncomputable def invLift (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (n : E) {t : G} (ht : π n * t * (π n)⁻¹ = t⁻¹) : E :=
  (OddCover.existsUnique_inverted_lift hπ hC hodd n ht).choose

theorem invLift_spec (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (n : E) {t : G} (ht : π n * t * (π n)⁻¹ = t⁻¹) :
    π (invLift hπ hC hodd n ht) = t ∧
      n * invLift hπ hC hodd n ht * n⁻¹ = (invLift hπ hC hodd n ht)⁻¹ :=
  (OddCover.existsUnique_inverted_lift hπ hC hodd n ht).choose_spec.1

theorem eq_invLift (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (n : E) {t : G} (ht : π n * t * (π n)⁻¹ = t⁻¹) {y : E}
    (hy : π y = t) (hyn : n * y * n⁻¹ = y⁻¹) : y = invLift hπ hC hodd n ht :=
  (OddCover.existsUnique_inverted_lift hπ hC hodd n ht).choose_spec.2 y ⟨hy, hyn⟩

omit [Finite E] in
theorem commute_of_map_mem_cyclic (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    {T : Subgroup G} [IsCyclic T] {x y : E} (hx : π x ∈ T) (hy : π y ∈ T) : Commute x y := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  obtain ⟨e, he⟩ := hπ (g : G)
  have hpow : ∀ {z : E}, π z ∈ T → ∃ k : ℤ, ∃ c ∈ π.ker, z = e ^ k * c := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨π z, hz⟩)
    have hk' : (g : G) ^ k = π z := by simpa using congrArg Subtype.val hk
    refine ⟨k, (e ^ k)⁻¹ * z, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, he, hk', inv_mul_cancel]
  obtain ⟨k, c₁, hc₁, rfl⟩ := hpow hx
  obtain ⟨l, c₂, hc₂, rfl⟩ := hpow hy
  have h1 : ∀ w : E, Commute c₁ w := fun w => (Subgroup.mem_center_iff.1 (hC hc₁) w).symm
  have h2 : ∀ w : E, Commute c₂ w := fun w => (Subgroup.mem_center_iff.1 (hC hc₂) w).symm
  have h3 : Commute (e ^ k) (e ^ l) := Commute.zpow_zpow_self e k l
  calc e ^ k * c₁ * (e ^ l * c₂) = e ^ k * e ^ l * (c₁ * c₂) := by
        rw [mul_assoc, ← mul_assoc c₁, (h1 _).eq]; group
    _ = e ^ l * e ^ k * (c₂ * c₁) := by rw [h3.eq, (h1 c₂).eq]
    _ = e ^ l * c₂ * (e ^ k * c₁) := by
        rw [show e ^ l * c₂ * (e ^ k * c₁) = e ^ l * (c₂ * e ^ k) * c₁ by group,
          (h2 (e ^ k)).eq]
        group

variable (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
  (hodd : Odd (Nat.card π.ker))
include hπ hC hodd

theorem invLift_mul (n : E) {T : Subgroup G} [IsCyclic T]
    (hT : ∀ t ∈ T, π n * t * (π n)⁻¹ = t⁻¹) {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) :
    invLift hπ hC hodd n (hT (t * t') (T.mul_mem ht ht')) =
      invLift hπ hC hodd n (hT t ht) * invLift hπ hC hodd n (hT t' ht') := by
  obtain ⟨h1, h1n⟩ := invLift_spec hπ hC hodd n (hT t ht)
  obtain ⟨h2, h2n⟩ := invLift_spec hπ hC hodd n (hT t' ht')
  set a := invLift hπ hC hodd n (hT t ht)
  set b := invLift hπ hC hodd n (hT t' ht')
  have hab : Commute a b := commute_of_map_mem_cyclic hπ hC (h1 ▸ ht) (h2 ▸ ht')
  refine (eq_invLift hπ hC hodd n _ (by rw [map_mul, h1, h2]) ?_).symm
  calc n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
    _ = a⁻¹ * b⁻¹ := by rw [h1n, h2n]
    _ = (a * b)⁻¹ := by rw [mul_inv_rev, hab.inv_inv.eq]

noncomputable def invLiftHom (n : E) (T : Subgroup G) [IsCyclic T]
    (hT : ∀ t ∈ T, π n * t * (π n)⁻¹ = t⁻¹) : T →* E where
  toFun t := invLift hπ hC hodd n (hT t t.2)
  map_one' := by
    refine (eq_invLift hπ hC hodd n (hT 1 T.one_mem) (map_one π) (by group)).symm
  map_mul' t t' := invLift_mul hπ hC hodd n hT t.2 t'.2

theorem invLiftHom_spec (n : E) (T : Subgroup G) [IsCyclic T]
    (hT : ∀ t ∈ T, π n * t * (π n)⁻¹ = t⁻¹) (t : T) :
    π (invLiftHom hπ hC hodd n T hT t) = t ∧
      n * invLiftHom hπ hC hodd n T hT t * n⁻¹ = (invLiftHom hπ hC hodd n T hT t)⁻¹ :=
  invLift_spec hπ hC hodd n (hT t t.2)

theorem mem_range_invLiftHom (n : E) (T : Subgroup G) [IsCyclic T]
    (hT : ∀ t ∈ T, π n * t * (π n)⁻¹ = t⁻¹) {x : E} (hx : π x ∈ T)
    (hxn : n * x * n⁻¹ = x⁻¹) : x ∈ (invLiftHom hπ hC hodd n T hT).range :=
  ⟨⟨π x, hx⟩, (eq_invLift hπ hC hodd n (hT _ hx) rfl hxn).symm⟩

omit hπ hC in
theorem eq_one_of_mem_ker_of_eq_inv {c : E} (hc : c ∈ π.ker) (h : c = c⁻¹) : c = 1 := by
  have h2 : c ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel c
  exact OddCover.eq_one_of_sq_eq_one_of_odd h2 (OddCover.odd_orderOf_of_mem hodd hc)

omit hπ in
theorem conj_eq_mul_of_inverted {n x y : E} (hn : n * n = 1)
    (hδ : n * x * n⁻¹ * (x * y)⁻¹ ∈ π.ker) (hy : n * y * n⁻¹ = y⁻¹) :
    n * x * n⁻¹ = x * y := by
  set δ := n * x * n⁻¹ * (x * y)⁻¹ with hδdef
  have hcen : ∀ w, Commute δ w := fun w => (Subgroup.mem_center_iff.1 (hC hδ) w).symm
  have h1 : n * x * n⁻¹ = δ * (x * y) := by rw [hδdef]; group
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn
  have h2 : x = n * (n * x * n⁻¹) * n⁻¹ := by
    rw [hninv, ← mul_assoc, ← mul_assoc, hn, one_mul, mul_assoc, hn, mul_one]
  have h3 : n * (δ * (x * y)) * n⁻¹ = δ * (n * x * n⁻¹) * (n * y * n⁻¹) := by
    calc n * (δ * (x * y)) * n⁻¹ = (n * δ) * (x * y) * n⁻¹ := by group
      _ = (δ * n) * (x * y) * n⁻¹ := by rw [(hcen n).eq]
      _ = δ * (n * x * n⁻¹) * (n * y * n⁻¹) := by group
  rw [h1, h3, h1, hy] at h2
  have h4 : δ * δ = 1 := by
    have h5 : x = δ * δ * x := by
      calc x = δ * (δ * (x * y)) * y⁻¹ := h2
        _ = δ * δ * x := by group
    exact mul_right_cancel (h5.symm.trans (one_mul x).symm)
  rw [h1, eq_one_of_mem_ker_of_eq_inv hodd hδ (eq_inv_of_mul_eq_one_left h4), one_mul]

theorem commute_invLift_of_cross {T₁ T₂ : Subgroup G} [IsCyclic T₁]
    (hcomm : ∀ x ∈ T₁, ∀ y ∈ T₂, Commute x y) {n₁ : E}
    (hinv₁ : ∀ t ∈ T₁, π n₁ * t * (π n₁)⁻¹ = t⁻¹)
    (hcross₁ : ∀ t ∈ T₂, t⁻¹ * (π n₁ * t * (π n₁)⁻¹) ∈ T₁) (t : T₁) {b : E} (hb : π b ∈ T₂) :
    Commute (invLiftHom hπ hC hodd n₁ T₁ hinv₁ t) b := by
  set j₁ := invLiftHom hπ hC hodd n₁ T₁ hinv₁
  set a := j₁ t
  have ha : π a = t := (invLiftHom_spec hπ hC hodd n₁ T₁ hinv₁ t).1
  have han : n₁ * a * n₁⁻¹ = a⁻¹ := (invLiftHom_spec hπ hC hodd n₁ T₁ hinv₁ t).2
  set β : T₁ := ⟨_, hcross₁ (π b) hb⟩
  set y := j₁ β
  have hyπ : π y = β := (invLiftHom_spec hπ hC hodd n₁ T₁ hinv₁ β).1
  have hay : Commute a y := commute_of_map_mem_cyclic hπ hC (ha ▸ t.2) (hyπ ▸ β.2)
  set c := a * b * a⁻¹ * b⁻¹ with hcdef
  have hcker : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, ha,
      (hcomm _ t.2 _ hb).eq]
    group
  have hcen : ∀ w, Commute c w := fun w => (Subgroup.mem_center_iff.1 (hC hcker) w).symm
  set δ := n₁ * b * n₁⁻¹ * (b * y)⁻¹ with hδdef
  have hδker : δ ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [hδdef, map_mul, map_inv, hyπ]
    rw [show (β : G) = (π b)⁻¹ * (π n₁ * π b * (π n₁)⁻¹) from rfl]
    group
  have hδcen : ∀ w, Commute δ w := fun w => (Subgroup.mem_center_iff.1 (hC hδker) w).symm
  have hb' : n₁ * b * n₁⁻¹ = δ * (b * y) := by rw [hδdef]; group
  have hconj : n₁ * c * n₁⁻¹ = c⁻¹ := by
    calc n₁ * c * n₁⁻¹ = (n₁ * a * n₁⁻¹) * (n₁ * b * n₁⁻¹) * (n₁ * a * n₁⁻¹)⁻¹ *
          (n₁ * b * n₁⁻¹)⁻¹ := by rw [hcdef]; group
      _ = a⁻¹ * (δ * (b * y)) * a * (δ * (b * y))⁻¹ := by rw [han, hb', inv_inv]
      _ = δ * (a⁻¹ * (b * y) * a * (b * y)⁻¹) * δ⁻¹ := by
          rw [show a⁻¹ * (δ * (b * y)) = δ * (a⁻¹ * (b * y)) by
            rw [← mul_assoc, ← (hδcen a⁻¹).eq, mul_assoc]]
          group
      _ = a⁻¹ * (b * y) * a * (b * y)⁻¹ := by rw [(hδcen _).eq]; group
      _ = a⁻¹ * b * a * b⁻¹ := by
          rw [show a⁻¹ * (b * y) * a * (b * y)⁻¹ = a⁻¹ * b * (y * a) * y⁻¹ * b⁻¹ by group,
            ← hay.eq]
          group
      _ = c⁻¹ := by
          have : a⁻¹ * b * a * b⁻¹ = a⁻¹ * c⁻¹ * a := by rw [hcdef]; group
          rw [this, ← (hcen a⁻¹).inv_left.eq]; group
  have hcc : c = c⁻¹ := by
    rw [← hconj, ← (hcen n₁).eq]; group
  have hc1 := eq_one_of_mem_ker_of_eq_inv hodd hcker hcc
  show a * b = b * a
  have : a * b * a⁻¹ * b⁻¹ = 1 := hc1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

theorem exists_torus_lift {T₁ T₂ : Subgroup G} [IsCyclic T₁] [IsCyclic T₂]
    (hcomm : ∀ x ∈ T₁, ∀ y ∈ T₂, Commute x y) (hdisj : T₁ ⊓ T₂ = ⊥)
    {n₁ n₂ : E} (hn₁ : n₁ * n₁ = 1) (hn₂ : n₂ * n₂ = 1)
    (hinv₁ : ∀ t ∈ T₁, π n₁ * t * (π n₁)⁻¹ = t⁻¹) (hinv₂ : ∀ t ∈ T₂, π n₂ * t * (π n₂)⁻¹ = t⁻¹)
    (hcross₁ : ∀ t ∈ T₂, t⁻¹ * (π n₁ * t * (π n₁)⁻¹) ∈ T₁)
    (hcross₂ : ∀ t ∈ T₁, t⁻¹ * (π n₂ * t * (π n₂)⁻¹) ∈ T₂) :
    ∃ Th : Subgroup E, Th.map π = T₁ ⊔ T₂ ∧ (∀ x ∈ Th, π x = 1 → x = 1) ∧
      (∀ x ∈ Th, n₁ * x * n₁⁻¹ ∈ Th) ∧ (∀ x ∈ Th, n₂ * x * n₂⁻¹ ∈ Th) ∧
      (∀ x, π x ∈ T₁ → n₁ * x * n₁⁻¹ = x⁻¹ → x ∈ Th) ∧
      (∀ x, π x ∈ T₂ → n₂ * x * n₂⁻¹ = x⁻¹ → x ∈ Th) := by
  set j₁ := invLiftHom hπ hC hodd n₁ T₁ hinv₁
  set j₂ := invLiftHom hπ hC hodd n₂ T₂ hinv₂
  have hj₁ : ∀ t, π (j₁ t) = t := fun t => (invLiftHom_spec hπ hC hodd n₁ T₁ hinv₁ t).1
  have hj₂ : ∀ u, π (j₂ u) = u := fun u => (invLiftHom_spec hπ hC hodd n₂ T₂ hinv₂ u).1
  have hj₁n : ∀ t, n₁ * j₁ t * n₁⁻¹ = (j₁ t)⁻¹ := fun t =>
    (invLiftHom_spec hπ hC hodd n₁ T₁ hinv₁ t).2
  have hj₂n : ∀ u, n₂ * j₂ u * n₂⁻¹ = (j₂ u)⁻¹ := fun u =>
    (invLiftHom_spec hπ hC hodd n₂ T₂ hinv₂ u).2
  have hcomm' : ∀ x ∈ T₂, ∀ y ∈ T₁, Commute x y := fun x hx y hy => (hcomm y hy x hx).symm
  have hc12 : ∀ t u, Commute (j₁ t) (j₂ u) := fun t u =>
    commute_invLift_of_cross hπ hC hodd hcomm hinv₁ hcross₁ t (by rw [hj₂]; exact u.2)
  set ψ := MonoidHom.noncommCoprod j₁ j₂ hc12
  refine ⟨ψ.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [MonoidHom.map_range]
    refine le_antisymm ?_ (sup_le (fun t ht => ⟨(⟨t, ht⟩, 1), ?_⟩) (fun u hu => ⟨(1, ⟨u, hu⟩), ?_⟩))
    · rintro _ ⟨⟨t, u⟩, rfl⟩
      simp only [MonoidHom.comp_apply, ψ, MonoidHom.noncommCoprod_apply, map_mul, hj₁, hj₂]
      exact mul_mem (Subgroup.mem_sup_left t.2) (Subgroup.mem_sup_right u.2)
    · simp [ψ, hj₁]
    · simp [ψ, hj₂]
  ·
    rintro _ ⟨⟨t, u⟩, rfl⟩ h1
    simp only [ψ, MonoidHom.noncommCoprod_apply, map_mul, hj₁, hj₂] at h1 ⊢
    have ht : (t : G) = (u : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have htu : (t : G) ∈ T₁ ⊓ T₂ := ⟨t.2, ht ▸ T₂.inv_mem u.2⟩
    rw [hdisj, Subgroup.mem_bot] at htu
    have hu : (u : G) = 1 := by rw [← inv_eq_one, ← ht, htu]
    have ht1 : t = 1 := Subtype.ext htu
    have hu1 : u = 1 := Subtype.ext hu
    rw [ht1, hu1, map_one, map_one, mul_one]
  ·
    rintro _ ⟨⟨t, u⟩, rfl⟩
    simp only [ψ, MonoidHom.noncommCoprod_apply]
    set β : T₁ := ⟨_, hcross₁ (u : G) u.2⟩
    have hu : n₁ * j₂ u * n₁⁻¹ = j₂ u * j₁ β := by
      refine conj_eq_mul_of_inverted hC hodd hn₁ ?_ (hj₁n β)
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hj₁, hj₂]
      rw [show (β : G) = (u : G)⁻¹ * (π n₁ * u * (π n₁)⁻¹) from rfl]
      group
    refine ⟨(t⁻¹ * β, u), ?_⟩
    simp only [MonoidHom.noncommCoprod_apply, map_mul, map_inv]
    calc (j₁ t)⁻¹ * j₁ β * j₂ u = (j₁ t)⁻¹ * (j₂ u * j₁ β) := by
          rw [mul_assoc, (hc12 β u).eq]
      _ = (n₁ * j₁ t * n₁⁻¹) * (n₁ * j₂ u * n₁⁻¹) := by rw [hj₁n, hu]
      _ = n₁ * (j₁ t * j₂ u) * n₁⁻¹ := by group
  ·
    rintro _ ⟨⟨t, u⟩, rfl⟩
    simp only [ψ, MonoidHom.noncommCoprod_apply]
    set β : T₂ := ⟨_, hcross₂ (t : G) t.2⟩
    have hc21 : ∀ u t, Commute (j₂ u) (j₁ t) := fun u t => (hc12 t u).symm
    have ht : n₂ * j₁ t * n₂⁻¹ = j₁ t * j₂ β := by
      refine conj_eq_mul_of_inverted hC hodd hn₂ ?_ (hj₂n β)
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hj₁, hj₂]
      rw [show (β : G) = (t : G)⁻¹ * (π n₂ * t * (π n₂)⁻¹) from rfl]
      group
    refine ⟨(t, β * u⁻¹), ?_⟩
    simp only [MonoidHom.noncommCoprod_apply, map_mul, map_inv]
    calc j₁ t * (j₂ β * (j₂ u)⁻¹) = (n₂ * j₁ t * n₂⁻¹) * (n₂ * j₂ u * n₂⁻¹) := by
          rw [ht, hj₂n]; group
      _ = n₂ * (j₁ t * j₂ u) * n₂⁻¹ := by group
  ·
    intro x hx hxn
    refine ⟨(⟨π x, hx⟩, 1), ?_⟩
    simp only [ψ, MonoidHom.noncommCoprod_apply, map_one, mul_one]
    exact (eq_invLift hπ hC hodd n₁ (hinv₁ _ hx) rfl hxn).symm
  ·
    intro x hx hxn
    refine ⟨(1, ⟨π x, hx⟩), ?_⟩
    simp only [ψ, MonoidHom.noncommCoprod_apply, map_one, one_mul]
    exact (eq_invLift hπ hC hodd n₂ (hinv₂ _ hx) rfl hxn).symm

end Torus


end CFSG.SectionRank
