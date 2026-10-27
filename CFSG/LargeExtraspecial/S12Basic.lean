module

public import CFSG.LargeExtraspecial.S3Qa
public import CFSG.LargeExtraspecial.S3Two
public import CFSG.LargeExtraspecial.OrthoF2Timmesfeld12

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

instance s12_instFiniteLinearEquiv : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  Finite.of_injective (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => (e : S.Qt → S.Qt))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

omit [Finite G] in
theorem s12_Qa_mul (h g : G) : S.Qa (h * g) = (S.Qa g).map (MulAut.conj h).toMonoidHom := by
  rw [S.Qa_eq_map, S.Qa_eq_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem s12_map_conj_M {h : G} (hh : h ∈ S.M) : S.M.map (MulAut.conj h).toMonoidHom = S.M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact S.M.mul_mem (S.M.mul_mem hh hy) (S.M.inv_mem hh)
  · intro hx
    refine ⟨h⁻¹ * x * h, S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hh) hx) hh, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem s12_L0_mul {h : G} (hh : h ∈ S.M) (g : G) :
    S.L0 (h * g) = (S.L0 g).map (MulAut.conj h).toMonoidHom := by
  rw [L0, L0, S.s12_Qa_mul, Subgroup.map_inf _ _ _ (MulAut.conj h).injective, S.s12_map_conj_M hh]

theorem s12_mem_Lbar {g : G} {t : S.O} :
    t ∈ S.Lbar g ↔ ∃ y, ∃ hy : y ∈ S.L0 g, S.ρ ⟨y, S.L0_le_M g hy⟩ = t := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, S.L0_le_M g hy⟩, hy, rfl⟩

theorem s12_Lbar_mul (h : S.M) (g : G) :
    S.Lbar ((h : G) * g) = (S.Lbar g).map (MulAut.conj (S.ρ h)).toMonoidHom := by
  ext t
  rw [S.s12_mem_Lbar]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [S.s12_L0_mul h.2] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨S.ρ ⟨y', S.L0_le_M g hy'⟩, S.s12_mem_Lbar.mpr ⟨y', hy', rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul, ← map_inv]
    congr 1
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨y', hy', rfl⟩ := S.s12_mem_Lbar.mp ht'
    have hy : (h : G) * y' * (h : G)⁻¹ ∈ S.L0 ((h : G) * g) := by
      rw [S.s12_L0_mul h.2]
      exact ⟨y', hy', rfl⟩
    refine ⟨_, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul, ← map_inv]
    congr 1

theorem s12_Lbar_eq_of_conj_eq {g g' : G} (h : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) :
    S.Lbar g = S.Lbar g' := by
  simp only [Lbar, L0, S.Qa_eq_of_conj_eq h]

omit [Finite G] in
theorem s12_Qa_le_centralizer (g : G) : S.Qa g ≤ centralizer ({g * S.z * g⁻¹} : Set G) :=
  (S.conjBy g).QG_le_M

omit [Finite G] in
theorem s12_commute_of_mem_L0 {g y : G} (hy : y ∈ S.L0 g) :
    y * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * y :=
  mem_centralizer_singleton_iff.mp (S.s12_Qa_le_centralizer g (S.L0_le_Qa g hy))

theorem s12_Lbar_apply_cl_a {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp ht
  rw [S.ρ_cl _ haQ]
  congr 1
  change y * (g * S.z * g⁻¹) * y⁻¹ = g * S.z * g⁻¹
  rw [S.s12_commute_of_mem_L0 hy]
  group

omit [Finite G] in
theorem s12_commutator_L0_mem {g x y : G} (hxQ : x ∈ S.QG)
    (hxa : x * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * x) (hy : y ∈ S.L0 g) :
    y * x * y⁻¹ * x⁻¹ ∈ S.QG ⊓ S.Qa g := by
  refine ⟨S.commutator_mem_QG (S.L0_le_M g hy) hxQ, ?_⟩
  have hxM : x ∈ (S.conjBy g).M := mem_centralizer_singleton_iff.mpr hxa
  have h1 : x * y⁻¹ * x⁻¹ ∈ (S.conjBy g).QG :=
    (S.conjBy g).conj_mem_QG hxM ((S.conjBy g).QG.inv_mem (S.L0_le_Qa g hy))
  have h2 : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
  rw [h2]
  exact (S.conjBy g).QG.mul_mem (S.L0_le_Qa g hy) h1

theorem s12_Lbar_apply_sub_mem {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {v : S.Qt} (hv : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp ht
  obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
  have hxa : (g * S.z * g⁻¹) * x = x * (g * S.z * g⁻¹) := (S.polar_cl_eq_zero_iff haQ hxQ).mp hv
  rw [← S.cl_commutator (S.L0_le_M g hy) hxQ]
  exact S.cl_mem_clSub (S.s12_commutator_L0_mem hxQ hxa.symm hy)
    (S.commutator_mem_QG (S.L0_le_M g hy) hxQ)

omit [Finite G] in
theorem s12_exists_not_commute_of_extraspecial {P : Subgroup G} (h : IsExtraspecialPGroup 2 P) :
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  have hbot : commutator P = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact Subtype.ext (hc _ y.2 _ x.2)
  have h2 := h.2.2.2
  rw [← h.2.1, hbot, card_bot] at h2
  exact absurd h2 (by norm_num)

theorem s12_exists_L0_commutator_eq {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 2 ≤ S.width) :
    ∃ y₁ ∈ S.L0 g, ∃ y₂ ∈ S.L0 g, y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = g * S.z * g⁻¹ := by
  obtain ⟨Q₀, hQ₀, -, -, -, -, -, hext⟩ := S.exists_L0_eq haQ hne
  obtain ⟨x, hx, y, hy, hxy⟩ := s12_exists_not_commute_of_extraspecial (hext hn)
  refine ⟨x, hQ₀ hx, y, hQ₀ hy, ?_⟩
  rcases (S.conjBy g).commutator_eq_one_or_z (S.L0_le_Qa g (hQ₀ hx))
    (S.L0_le_Qa g (hQ₀ hy)) with h | h
  · exact absurd (by
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [h, one_mul]) hxy
  · exact h

omit [Finite G] in
theorem s12_commutator_mul_mul_of_commute {H : Type*} [Group H] {u v c d : H}
    (hcu : Commute c u) (hcv : Commute c v) (hdu : Commute d u) (hdv : Commute d v)
    (hcd : Commute c d) :
    (c * u) * (d * v) * (c * u)⁻¹ * (d * v)⁻¹ = u * v * u⁻¹ * v⁻¹ := by
  have h1 : Commute c (u * d * v * u⁻¹) := by
    apply_rules [Commute.mul_right, Commute.inv_right]
  have h2 : Commute d (v * u⁻¹ * v⁻¹) := by
    apply_rules [Commute.mul_right, Commute.inv_right]
  calc (c * u) * (d * v) * (c * u)⁻¹ * (d * v)⁻¹
      = c * (u * d * v * u⁻¹) * c⁻¹ * (v⁻¹ * d⁻¹) := by group
    _ = (u * d * v * u⁻¹) * (v⁻¹ * d⁻¹) := by rw [h1.eq]; group
    _ = u * (d * (v * u⁻¹ * v⁻¹)) * d⁻¹ := by group
    _ = u * v * u⁻¹ * v⁻¹ := by rw [h2.eq]; group

theorem s12_commute_a_of_fixed {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 2 ≤ S.width) {x : G} (hxQ : x ∈ S.QG)
    (hfix : ∀ t ∈ S.Lbar g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x) :
    x * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * x := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := S.s12_exists_L0_commutator_eq haQ hne hn
  have hxz : Commute x S.z := S.z_comm (S.mem_M_of_mem_QG hxQ)
  have hconj : ∀ y ∈ S.L0 g, ∃ c, (c = 1 ∨ c = S.z) ∧ x * y * x⁻¹ = c * y := by
    intro y hy
    have h1 := hfix _ (S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩)
    rw [S.ρ_cl _ hxQ] at h1
    change S.cl (y * x * y⁻¹) = S.cl x at h1
    rcases (S.cl_eq_cl_iff hxQ (S.conj_mem_QG (S.L0_le_M g hy) hxQ)).mp h1.symm with h2 | h2
    · refine ⟨1, Or.inl rfl, ?_⟩
      calc x * y * x⁻¹ = x * (y * x * y⁻¹)⁻¹ * y := by group
        _ = 1 * y := by rw [h2]; group
    · refine ⟨S.z, Or.inr rfl, ?_⟩
      calc x * y * x⁻¹ = x * (y * x * y⁻¹)⁻¹ * y := by group
        _ = x * S.z⁻¹ * x⁻¹ * y := by rw [h2]; group
        _ = S.z⁻¹ * y := by rw [hxz.inv_right.eq]; group
        _ = S.z * y := by rw [S.z_inv]
  have hcomm : ∀ c, (c = 1 ∨ c = S.z) → ∀ y ∈ S.L0 g, Commute c y := by
    rintro c (rfl | rfl) y hy
    · exact Commute.one_left y
    · exact (S.z_comm (S.L0_le_M g hy)).symm
  obtain ⟨c₁, hc₁, e₁⟩ := hconj y₁ hy₁
  obtain ⟨c₂, hc₂, e₂⟩ := hconj y₂ hy₂
  have hc₁₂ : Commute c₁ c₂ := by
    rcases hc₁ with rfl | rfl
    · exact Commute.one_left _
    · rcases hc₂ with rfl | rfl
      · exact Commute.one_right _
      · exact Commute.refl _
  have key : x * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x⁻¹ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by
    have e : x * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x⁻¹ =
        (x * y₁ * x⁻¹) * (x * y₂ * x⁻¹) * (x * y₁ * x⁻¹)⁻¹ * (x * y₂ * x⁻¹)⁻¹ := by group
    rw [e, e₁, e₂]
    exact s12_commutator_mul_mul_of_commute (hcomm c₁ hc₁ y₁ hy₁) (hcomm c₁ hc₁ y₂ hy₂)
      (hcomm c₂ hc₂ y₁ hy₁) (hcomm c₂ hc₂ y₂ hy₂) hc₁₂
  rw [hy] at key
  calc x * (g * S.z * g⁻¹) = x * (g * S.z * g⁻¹) * x⁻¹ * x := by group
    _ = (g * S.z * g⁻¹) * x := by rw [key]

omit [Finite G] in
theorem s12_card_le_two_of_forall_eq {H : Type*} [Group H] [Finite H] (K : Subgroup H)
    (h : ∀ x ∈ K, ∀ y ∈ K, x ≠ 1 → y ≠ 1 → x = y) : Nat.card K ≤ 2 := by
  by_cases hb : ∃ x ∈ K, x ≠ 1
  · obtain ⟨x, hx, hx1⟩ := hb
    have hsub : (K : Set H) ⊆ {1, x} := by
      intro y hy
      by_cases hy1 : y = 1
      · simp [hy1]
      · simp [h y hy x hx hy1 hx1]
    calc Nat.card K = (K : Set H).ncard := (Nat.card_coe_set_eq _)
      _ ≤ ({1, x} : Set H).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({x} : Set H).ncard + 1 := Set.ncard_insert_le 1 {x}
      _ = 2 := by rw [Set.ncard_singleton]
  · push Not at hb
    have : K = ⊥ := (Subgroup.eq_bot_iff_forall K).mpr hb
    subst this
    simp

omit [Finite G] in
theorem s12_conj_z_ne_one (g : G) : g * S.z * g⁻¹ ≠ 1 := by
  intro h'
  apply S.z_ne_one
  calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
    _ = 1 := by rw [h']; group

omit [Finite G] in
theorem s12_mul_conj_z (h g : G) : h * g * S.z * (h * g)⁻¹ = h * (g * S.z * g⁻¹) * h⁻¹ := by group

theorem s12_Lbar_mul_eq_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (h : S.M) (hfix : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)) :
    S.Lbar ((h : G) * g) = S.Lbar g := by
  rw [S.ρ_cl h haQ] at hfix
  rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG h.2 haQ)).mp hfix.symm with h1 | h1
  · exact S.s12_Lbar_eq_of_conj_eq ((S.s12_mul_conj_z _ _).trans h1)
  · obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z haQ (S.s12_conj_z_ne_one g) hne
    have hug : u * g * S.z * (u * g)⁻¹ = (h : G) * g * S.z * ((h : G) * g)⁻¹ := by
      rw [S.s12_mul_conj_z, S.s12_mul_conj_z, h1, hu]
    rw [← S.s12_Lbar_eq_of_conj_eq hug]
    have hρu : S.ρ ⟨u, S.QG_le_M huQ⟩ = 1 := (S.ρ_eq_one_iff _).mpr huQ
    have e := S.s12_Lbar_mul ⟨u, S.QG_le_M huQ⟩ g
    rw [hρu] at e
    rw [e]
    ext t
    simp

omit [Finite G] in
theorem s12_cl_ne_zero_of_conj {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.cl (g * S.z * g⁻¹) ≠ 0 := by
  rw [Ne, S.cl_eq_zero_iff haQ]
  rintro (h | h)
  · exact S.s12_conj_z_ne_one g h
  · exact hne h

omit [Finite G] in
theorem s12_conj_z_sq (g : G) : (g * S.z * g⁻¹) ^ 2 = 1 := by
  rw [pow_two, show g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ by group, S.z_mul_z]
  group

omit [Finite G] in
theorem s12_conj_z_of_mem_M {h : G} (hh : h ∈ S.M) : h * S.z * h⁻¹ = S.z := by
  rw [S.z_comm hh]
  group

theorem s12_not_mem_Qa_of_Lbar_eq {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hbQ : g' * S.z * g'⁻¹ ∈ S.QG) (hbne : g' * S.z * g'⁻¹ ≠ S.z)
    (hL : S.Lbar g = S.Lbar g') (hab : S.cl (g * S.z * g⁻¹) ≠ S.cl (g' * S.z * g'⁻¹)) :
    g * S.z * g⁻¹ ∉ S.Qa g' := by
  intro haQb
  have hfix : ∀ y ∈ S.L0 g', S.cl (y * (g * S.z * g⁻¹) * y⁻¹) = S.cl (g * S.z * g⁻¹) := by
    intro y hy
    have ht : S.ρ ⟨y, S.L0_le_M g' hy⟩ ∈ S.Lbar g := hL ▸ S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩
    have e := S.ρ_cl ⟨y, S.L0_le_M g' hy⟩ haQ
    rw [S.s12_Lbar_apply_cl_a haQ ht] at e
    exact e.symm
  rcases S.mem_of_cl_fixed_by_L0 hbQ hbne ⟨haQ, haQb⟩ hfix with h | h | h | h
  · exact S.s12_conj_z_ne_one g h
  · exact hab (by rw [h])
  · exact hne h
  · apply hab
    rw [h, S.cl_mul S.z_mem_QG hbQ, S.cl_z, zero_add]

omit [Finite G] in
theorem s12_conj_L0_eq_or {g y w : G} (hy : y ∈ S.L0 g) (hw : w ∈ S.Qa g) :
    y * w * y⁻¹ = w ∨ y * w * y⁻¹ = (g * S.z * g⁻¹) * w := by
  rcases (S.conjBy g).commutator_eq_one_or_z (S.L0_le_Qa g hy) hw with h | h
  · left
    calc y * w * y⁻¹ = y * w * y⁻¹ * w⁻¹ * w := by group
      _ = w := by rw [h, one_mul]
  · right
    calc y * w * y⁻¹ = y * w * y⁻¹ * w⁻¹ * w := by group
      _ = (g * S.z * g⁻¹) * w := by rw [h]; rfl

theorem s12_cl_eq_zero_of_mem_inf_inf {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hbQ : g' * S.z * g'⁻¹ ∈ S.QG) (hbne : g' * S.z * g'⁻¹ ≠ S.z)
    (hL : S.Lbar g = S.Lbar g') (hab : S.cl (g * S.z * g⁻¹) ≠ S.cl (g' * S.z * g'⁻¹))
    (haQb : g * S.z * g⁻¹ ∉ S.Qa g') {w : G} (hw : w ∈ S.QG ⊓ S.Qa g ⊓ S.Qa g') :
    S.cl w = 0 := by
  obtain ⟨⟨hwQ, hwa⟩, hwb⟩ := hw
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hb0 := S.s12_cl_ne_zero_of_conj hbQ hbne
  have hfix : ∀ y ∈ S.L0 g, S.cl (y * w * y⁻¹) = S.cl w := by
    intro y hy
    have ht : S.ρ ⟨y, S.L0_le_M g hy⟩ ∈ S.Lbar g' := hL ▸ S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy'⟩ := S.s12_mem_Lbar.mp ht
    have he : S.cl (y * w * y⁻¹) = S.cl (y' * w * y'⁻¹) := by
      have e1 := S.ρ_cl ⟨y, S.L0_le_M g hy⟩ hwQ
      have e2 := S.ρ_cl ⟨y', S.L0_le_M g' hy'⟩ hwQ
      rw [hyy'] at e2
      exact e1.symm.trans e2
    rcases S.s12_conj_L0_eq_or hy hwa with h1 | h1
    · rw [h1]
    · exfalso
      rw [h1, S.cl_mul haQ hwQ] at he
      rcases S.s12_conj_L0_eq_or hy' hwb with h2 | h2
      · rw [h2] at he
        exact ha0 (by simpa using he)
      · rw [h2, S.cl_mul hbQ hwQ] at he
        exact hab (add_right_cancel he)
  rcases S.mem_of_cl_fixed_by_L0 haQ hne ⟨hwQ, hwa⟩ hfix with h | h | h | h
  · rw [h, S.cl_one]
  · exact absurd (h ▸ hwb) haQb
  · rw [h, S.cl_z]
  · exfalso
    apply haQb
    have hzb : S.z ∈ S.Qa g' := S.z_mem_Qa_of_mem_QG rfl hbQ hbne
    have e : g * S.z * g⁻¹ = S.z⁻¹ * w := by rw [h]; group
    rw [e]
    exact (S.Qa g').mul_mem ((S.Qa g').inv_mem hzb) hwb

theorem s12_Lbar_fix_of_commute {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hL : S.Lbar g = S.Lbar g')
    (hW : ∀ w ∈ S.QG ⊓ S.Qa g ⊓ S.Qa g', S.cl w = 0) {x : G} (hxQ : x ∈ S.QG)
    (hxa : x * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * x)
    (hxb : x * (g' * S.z * g'⁻¹) = (g' * S.z * g'⁻¹) * x) {t : S.O} (ht : t ∈ S.Lbar g) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x := by
  have ht' : t ∈ S.Lbar g' := hL ▸ ht
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp ht
  obtain ⟨y', hy', hyy'⟩ := S.s12_mem_Lbar.mp ht'
  have hc := S.s12_commutator_L0_mem hxQ hxa hy
  have hc' := S.s12_commutator_L0_mem hxQ hxb hy'
  have he : S.cl (y * x * y⁻¹ * x⁻¹) = S.cl (y' * x * y'⁻¹ * x⁻¹) := by
    rw [S.cl_commutator (S.L0_le_M g hy) hxQ, S.cl_commutator (S.L0_le_M g' hy') hxQ, hyy']
  have hc'a : y' * x * y'⁻¹ * x⁻¹ ∈ S.Qa g := by
    rcases (S.cl_eq_cl_iff hc.1 hc'.1).mp he with h | h
    · rw [h]
      exact hc.2
    · rw [h]
      exact (S.Qa g).mul_mem hc.2 (S.z_mem_Qa_of_mem_QG rfl haQ hne)
  have h0 := hW _ ⟨⟨hc'.1, hc'a⟩, hc'.2⟩
  rw [← he, S.cl_commutator (S.L0_le_M g hy) hxQ, sub_eq_zero] at h0
  exact h0

theorem s12_fix_of_mem_normalizer_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) (h : S.M)
    (hN : S.ρ h ∈ normalizer (S.Lbar g : Set S.O)) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  by_contra hb
  set g' := (h : G) * g with hg'
  have hbQ : g' * S.z * g'⁻¹ ∈ S.QG := by
    rw [hg', S.s12_mul_conj_z]
    exact S.conj_mem_QG h.2 haQ
  have hbne : g' * S.z * g'⁻¹ ≠ S.z := by
    rw [hg', S.s12_mul_conj_z]
    intro h'
    apply hne
    calc g * S.z * g⁻¹ = (h : G)⁻¹ * ((h : G) * (g * S.z * g⁻¹) * (h : G)⁻¹) * h := by group
      _ = (h : G)⁻¹ * S.z * (h : G)⁻¹⁻¹ := by rw [h']; group
      _ = S.z := S.s12_conj_z_of_mem_M (S.M.inv_mem h.2)
  have hbcl : S.cl (g' * S.z * g'⁻¹) = ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹)) := by
    rw [S.ρ_cl h haQ, hg', S.s12_mul_conj_z]
  have hL : S.Lbar g = S.Lbar g' := by
    rw [hg', S.s12_Lbar_mul h g]
    exact ((mem_normalizer_iff_map_conj_eq).mp hN).symm
  have hab : S.cl (g * S.z * g⁻¹) ≠ S.cl (g' * S.z * g'⁻¹) := by
    rw [hbcl]
    exact fun e => hb e.symm
  have haQb := S.s12_not_mem_Qa_of_Lbar_eq haQ hne hbQ hbne hL hab
  have hW := fun w hw => S.s12_cl_eq_zero_of_mem_inf_inf haQ hne hbQ hbne hL hab haQb (w := w) hw
  have hfixb : ∀ t ∈ S.Lbar g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g' * S.z * g'⁻¹)) =
      S.cl (g' * S.z * g'⁻¹) := fun t ht => S.s12_Lbar_apply_cl_a hbQ (hL ▸ ht)
  have hcomm := S.s12_commute_a_of_fixed haQ hne (by omega) hbQ hfixb
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hb0 := S.s12_cl_ne_zero_of_conj hbQ hbne
  have hqa : S.q (S.cl (g * S.z * g⁻¹)) = 0 := (S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)
  have hqb : S.q (S.cl (g' * S.z * g'⁻¹)) = 0 := (S.q_cl_eq_zero_iff hbQ).mpr (S.s12_conj_z_sq g')
  have hpol : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl (g' * S.z * g'⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff haQ hbQ).mpr hcomm.symm
  have hli : LinearIndependent (ZMod 2) ![S.cl (g * S.z * g⁻¹), S.cl (g' * S.z * g'⁻¹)] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨ha0, hb0, hab⟩
  have hfixperp : ∀ t ∈ S.Lbar g, ∀ v, polar S.q (S.cl (g * S.z * g⁻¹)) v = 0 →
      polar S.q (S.cl (g' * S.z * g'⁻¹)) v = 0 → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro t ht v hva hvb
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
    have hxa := (S.polar_cl_eq_zero_iff haQ hxQ).mp hva
    have hxb := (S.polar_cl_eq_zero_iff hbQ hxQ).mp hvb
    exact S.s12_Lbar_fix_of_commute haQ hne hL hW hxQ hxa.symm hxb.symm ht
  have hall : ∀ t ∈ S.Lbar g, t ≠ 1 → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      CFSG.ClassicalGroups.Orthogonal.eichler S.q (S.cl (g * S.z * g⁻¹))
        (S.cl (g' * S.z * g'⁻¹)) := by
    intro t ht ht1
    have ht1' : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun e => ht1 (Subtype.ext e)
    obtain ⟨-, hc, -, -⟩ := timmesfeld_12_2 S.q_nondegenerate t.2 ht1' hli hqa hqb hpol
      (hfixperp t ht)
    rcases eq_one_or_eq_eichler_of_totallySingular S.q_nondegenerate hli hqa hqb hpol t.2
      hc.le (hfixperp t ht) with e | e
    · exact absurd e ht1'
    · exact e
  have hcard := s12_card_le_two_of_forall_eq (S.Lbar g) fun x hx y hy hx1 hy1 =>
    Subtype.ext ((hall x hx hx1).trans (hall y hy hy1).symm)
  have hge := S.card_Lbar_ge haQ hne
  have h4 : 2 ^ 2 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem timmesfeld_12_4_1 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (h : S.M) :
    S.ρ h ∈ normalizer (S.Lbar g : Set S.O) ↔
      ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  refine ⟨S.s12_fix_of_mem_normalizer_Lbar haQ hne hn h, fun hfix => ?_⟩
  rw [mem_normalizer_iff_map_conj_eq]
  have e := S.s12_Lbar_mul h g
  rw [S.s12_Lbar_mul_eq_of_fix haQ hne h hfix] at e
  exact e.symm

omit [Finite G] in
theorem s12_conj_pow_eq {h x c : G} (hc : h * c * h⁻¹ = c) (hx : h * x * h⁻¹ = c * x) :
    ∀ k : ℕ, h ^ k * x * (h ^ k)⁻¹ = c ^ k * x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hck : h * c ^ k * h⁻¹ = c ^ k := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hc]
    calc h ^ (k + 1) * x * (h ^ (k + 1))⁻¹ = h * (h ^ k * x * (h ^ k)⁻¹) * h⁻¹ := by group
      _ = h * c ^ k * h⁻¹ * (h * x * h⁻¹) := by rw [ih]; group
      _ = c ^ (k + 1) * x := by rw [hck, hx, pow_succ, mul_assoc]

omit [Finite G] in
theorem s12_eq_one_of_conj_odd {h x c : G} (hc : h * c * h⁻¹ = c) (hx : h * x * h⁻¹ = c * x)
    (hc2 : c ^ 2 = 1) {m : ℕ} (hm : h ^ m = 1) (hmo : Odd m) : c = 1 := by
  have e := s12_conj_pow_eq hc hx m
  rw [hm, inv_one, one_mul, mul_one] at e
  have hcm : c ^ m = 1 := by
    have := congrArg (· * x⁻¹) e
    simpa using this.symm
  obtain ⟨j, rfl⟩ := hmo
  rw [pow_succ, pow_mul, hc2, one_pow, one_mul] at hcm
  exact hcm

end Setting

end CFSG.LargeExtraspecial
