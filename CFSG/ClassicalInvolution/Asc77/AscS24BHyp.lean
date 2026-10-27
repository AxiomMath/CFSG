module

public import CFSG.ClassicalInvolution.Asc77.AscS24BHJ
public import CFSG.ClassicalInvolution.Asc77.AscS24Hyp51
public import CFSG.ClassicalInvolution.Asc77.AscT7K9

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_normalizer_of_conj_le {L : Subgroup G} {n : G}
    (h : ∀ y ∈ L, n * y * n⁻¹ ∈ L) : n ∈ Subgroup.normalizer (L : Set G) := by
  have hle : conjSub n L ≤ L := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have e : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    rw [e]
    exact h _ hx
  have hcard : Nat.card ↥(conjSub n L) = Nat.card ↥L := by
    have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
    rw [show conjSub n L = L.map (MulAut.conj n).toMonoidHom from rfl,
      Subgroup.card_map_of_injective hinj]
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

theorem mem_normalizer_closure {X : Set G} {n : G}
    (h : ∀ x ∈ X, n * x * n⁻¹ ∈ Subgroup.closure X) :
    n ∈ Subgroup.normalizer ((Subgroup.closure X : Subgroup G) : Set G) := by
  have hle : Subgroup.closure X ≤ (Subgroup.closure X).comap (MulAut.conj n).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    exact h x hx
  exact mem_normalizer_of_conj_le fun y hy => hle hy

omit [Finite G] in
theorem mem_closure₁ {x y w : G} : x ∈ Subgroup.closure ({x, y, w} : Set G) :=
  Subgroup.subset_closure (by simp)

omit [Finite G] in
theorem mem_closure₂ {x y w : G} : y ∈ Subgroup.closure ({x, y, w} : Set G) :=
  Subgroup.subset_closure (by simp)

omit [Finite G] in
theorem mem_closure₃ {x y w : G} : w ∈ Subgroup.closure ({x, y, w} : Set G) :=
  Subgroup.subset_closure (by simp)

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

theorem x₃_mul : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
  have hc : z * H.C.D.x₃⁻¹ = H.C.D.x₃⁻¹ * z :=
    Thompson.commutes_of_mem_WSet H.C.D.c.hp H.C.D.c.hq H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
      (W.inv_mem H.C.D.x₃_mem)
  rw [hc]; group

theorem B_le {L : Subgroup G} (h1 : H.C.D.F.j * H.a ∈ L) (h2 : H.C.D.F.j ∈ L) (h3 : z ∈ L) :
    H.B ≤ L := by
  rw [B, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h <;> rw [h]
  exacts [h1, h2, h3]

theorem closure_le_B {x y w : G} (hx : x ∈ H.B) (hy : y ∈ H.B) (hw : w ∈ H.B) :
    Subgroup.closure ({x, y, w} : Set G) ≤ H.B := by
  rw [Subgroup.closure_le]
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h <;> rw [h]
  exacts [hx, hy, hw]

theorem B_eq_zja : H.B = Subgroup.closure ({z, H.C.D.F.j, H.a} : Set G) := by
  refine le_antisymm (H.B_le (Subgroup.mul_mem _ mem_closure₂ mem_closure₃) mem_closure₂
    mem_closure₁) (H.closure_le_B H.z_mem_B H.j_mem_B H.a_mem_B)

theorem B_eq_zjza : H.B = Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G) := by
  have ha : H.a ∈ Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G) := by
    have h := Subgroup.mul_mem _
      (Subgroup.inv_mem _ (mem_closure₁ : z ∈ Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G)))
      (mem_closure₃ : z * H.a ∈ Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G))
    rwa [inv_mul_cancel_left] at h
  refine le_antisymm (H.B_le (Subgroup.mul_mem _ mem_closure₂ ha) mem_closure₂ mem_closure₁)
    (H.closure_le_B H.z_mem_B H.j_mem_B (H.B.mul_mem H.z_mem_B H.a_mem_B))

theorem B_eq_jzja : H.B = Subgroup.closure ({H.C.D.F.j, z, H.C.D.F.j * H.a} : Set G) :=
  le_antisymm (H.B_le mem_closure₃ mem_closure₁ mem_closure₂)
    (H.closure_le_B H.j_mem_B H.z_mem_B H.ja_mem_B)

theorem hyp51At_z [IsSimpleGroup G] : Hyp51At H.B z := by
  have hxy : H.C.D.x₁⁻¹ * H.C.D.x₂ = H.C.D.F.j := H.C.j_eq.symm
  refine S24.hyp51At_of_twin_vertex_z' H.C.hs.stand H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hzK
    H.C.hzK' H.B_isElemAbelian H.z_mem_B (K.inv_mem H.C.x₁_mem_K) H.C.x₂_mem_K'
    (by rw [hxy]; exact H.j_mem_B) (by rw [hxy]; exact H.C.hjJ.ne_one)
    (by rw [hxy]; exact H.C.z_ne_j.symm) H.a_mem_B H.ha1 H.a_ne_z
    (H.K_tq H.a H.ha2 H.haR).2 H.a_mem_B H.ha1 H.a_ne_z (H.K'_tq H.a H.ha2 H.haR').2

theorem hyp51At_j [IsSimpleGroup G] : Hyp51At H.B H.C.D.F.j := by
  refine S24.hyp51At_of_twin_vertex_z' H.C.hs.stand H.C.D.F.ρ₃.hK H.Js_mem H.C.hjJ H.hjJs
    H.B_isElemAbelian H.j_mem_B H.C.x₃_mem_J (H.Ts_syl.1 H.zx₃_mem_Ts)
    (by rw [H.x₃_mul]; exact H.z_mem_B) (by rw [H.x₃_mul]; exact H.C.hzK.ne_one)
    (by rw [H.x₃_mul]; exact H.C.z_ne_j) H.a_mem_B H.ha1 H.a_ne_j
    (H.J_tq H.a H.ha2 H.hTa).2 H.a_mem_B H.ha1 H.a_ne_j (H.Js_tq H.a H.ha2 H.Ts_le).2

theorem hyp51At_a [IsSimpleGroup G] : Hyp51At H.B H.a :=
  T7K.hyp51At_of_twin_inner (T7K.twinSmallInner_K p) (g2d4VertexExcl_proved (p := p) (f := f))
    H.C.hs.stand H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hs.hne H.C.hzK H.C.hzK'
    (H.K_tq H.a H.ha2 H.haR) (H.K'_tq H.a H.ha2 H.haR') H.B_isElemAbelian H.z_mem_B H.j_mem_B
    H.a_mem_B H.B_eq_zja H.ha1 H.a_ne_z.symm H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq
    (H.j_mem_exact H.a H.ha2 H.haR H.haR')

theorem za_ne_one : z * H.a ≠ 1 := fun h =>
  H.a_ne_z (by
    have e : H.a = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact inv_eq_of_mul_eq_one_right H.C.hzK.sq)

theorem ja_ne_one : H.C.D.F.j * H.a ≠ 1 := fun h =>
  H.a_ne_j (by
    have e : H.a = H.C.D.F.j⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e]
    exact inv_eq_of_mul_eq_one_right H.C.hjJ.sq)

theorem hyp51At_za [IsSimpleGroup G] : Hyp51At H.B (z * H.a) :=
  T7K.hyp51At_of_twin_inner (T7K.twinSmallInner_K p) (g2d4VertexExcl_proved (p := p) (f := f))
    H.C.hs.stand H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hs.hne H.C.hzK H.C.hzK'
    (H.K_tq (z * H.a) H.za_sq H.R_le_za) (H.K'_tq (z * H.a) H.za_sq H.R'_le_za)
    H.B_isElemAbelian H.z_mem_B H.j_mem_B (H.B.mul_mem H.z_mem_B H.a_mem_B) H.B_eq_zjza
    H.za_ne_one (fun h => H.ha1 (left_eq_mul.mp h)) H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq
    (H.j_mem_exact (z * H.a) H.za_sq H.R_le_za H.R'_le_za)

theorem hyp51At_ja [IsSimpleGroup G] : Hyp51At H.B (H.C.D.F.j * H.a) :=
  T7K.hyp51At_of_twin_inner (T7K.twinSmallInner_K p) (g2d4VertexExcl_proved (p := p) (f := f))
    H.C.hs.stand H.C.D.F.ρ₃.hK H.Js_mem H.Js_ne H.C.hjJ H.hjJs
    (H.J_tq _ H.ja_sq H.T_le_ja) (H.Js_tq _ H.ja_sq H.Ts_le_ja) H.B_isElemAbelian H.j_mem_B
    H.z_mem_B H.ja_mem_B H.B_eq_jzja H.ja_ne_one (fun h => H.ha1 (left_eq_mul.mp h))
    H.C.hzK.ne_one H.C.z_ne_j H.C.hzK.sq H.z_mem_exact

theorem r_mem_normalizer_B : H.C.D.F.ρ.r ∈ Subgroup.normalizer (H.B : Set G) := by
  have hrz : H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹ = z := by
    rw [(e189_commute_of_mem H.C.hzK H.C.r_mem_K).symm]; group
  have hra : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
  have hrj := H.C.r_conj_j
  refine mem_normalizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h <;> rw [h]
  · have e : H.C.D.F.ρ.r * (H.C.D.F.j * H.a) * H.C.D.F.ρ.r⁻¹ =
        (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹) := by
      group
    rw [e, hrj, hra]
    exact H.B.mul_mem (H.B.mul_mem H.j_mem_B H.z_mem_B) H.a_mem_B
  · rw [hrj]
    exact H.B.mul_mem H.j_mem_B H.z_mem_B
  · rw [hrz]
    exact H.z_mem_B

theorem hyp51 [IsSimpleGroup G] : Hyp51 H.B := by
  refine hyp51_of_orbitReps H.B_isElemAbelian H.B_card
    (R := {z, H.C.D.F.j, H.a, z * H.a, H.C.D.F.j * H.a}) ?_ ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h <;> rw [h]
    exacts [H.hyp51At_z, H.hyp51At_j, H.hyp51At_a, H.hyp51At_za, H.hyp51At_ja]
  · intro c hc hc1
    have hrN := H.r_mem_normalizer_B
    have hrj := H.C.r_conj_j
    have hra : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
    rcases T7K.mem_cases_of_commuting_involutions H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.comm_jz
        H.comm_j H.comm_z hc with h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j, by simp, H.C.D.F.ρ.r, hrN, by rw [h, hrj]⟩
    · exact ⟨H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j * H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · refine ⟨H.C.D.F.j * H.a, by simp, H.C.D.F.ρ.r, hrN, ?_⟩
      have e : H.C.D.F.ρ.r * (H.C.D.F.j * H.a) * H.C.D.F.ρ.r⁻¹ =
          (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹) := by
        group
      rw [h, e, hrj, hra]

end HCtx

end S24B

end CFSG.ClassicalInvolution.Asc77
