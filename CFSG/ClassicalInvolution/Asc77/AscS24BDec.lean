module

public import CFSG.ClassicalInvolution.Asc77.AscS24BSwap

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem good_mul {K K' : Subgroup G} {S : Sylow 2 G} {W : Subgroup G} {w₁ w₂ : G}
    (h₁ : w₁ ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub w₁ K = K ∧ conjSub w₁ K' = K')
    (h₂ : w₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub w₂ K = K ∧ conjSub w₂ K' = K') :
    w₁ * w₂ ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub (w₁ * w₂) K = K ∧
      conjSub (w₁ * w₂) K' = K' :=
  ⟨Subgroup.mul_mem _ h₁.1 h₂.1, by rw [conjSub_mul, h₂.2.1, h₁.2.1],
    by rw [conjSub_mul, h₂.2.2, h₁.2.2]⟩

omit [Finite G] in
theorem imgQ_comm_iff {W : Subgroup G} (ρ σ : Thompson.Rep Ω W) :
    T7D.imgQ ρ * T7D.imgQ σ = T7D.imgQ σ * T7D.imgQ ρ ↔ ρ.img * σ.img = σ.img * ρ.img :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem conjSub_K'_of_K {y : G} (h : conjSub y K = K) : conjSub y K' = K' := by
  have hst := C.hs.stand
  have h1 := twinSet_conj hst.hyp.conjInvariant C.hs.hK' y
  rw [h, C.hs.twinSet_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd ((conjSub_inj y).mp (h1.trans h.symm)) C.hs.hne
  · exact h1

include C in
theorem mem_normalizer_K'_of_mem_K {x : G} (hx : x ∈ K) :
    x ∈ Subgroup.normalizer (K' : Set G) :=
  C.hs.stand.hyp.le_normalizer_of_twin C.hs.stand.mem C.hs.hK'.1 C.hs.hne.symm C.hzK C.hzK' hx

include C in
theorem mem_normalizer_K_of_mem_K' {x : G} (hx : x ∈ K') :
    x ∈ Subgroup.normalizer (K : Set G) :=
  C.hs.stand.hyp.le_normalizer_of_twin C.hs.hK'.1 C.hs.stand.mem C.hs.hne C.hzK' C.hzK hx

theorem piG_r_sq : Thompson.piG W C.D.F.ρ.r * Thompson.piG W C.D.F.ρ.r = 1 := by
  rw [← Thompson.piG_mul C.D.F.ρ.r_mem_normalizer C.D.F.ρ.r_mem_normalizer, C.r_mul_self]
  exact Thompson.piG_of_mem_sup (Subgroup.mem_sup_left C.hd.hzW)

theorem piG_t_sq : Thompson.piG W C.D.F.ρ'.r * Thompson.piG W C.D.F.ρ'.r = 1 := by
  rw [← Thompson.piG_mul C.D.F.ρ'.r_mem_normalizer C.D.F.ρ'.r_mem_normalizer, C.t_mul_self]
  exact Thompson.piG_of_mem_sup (Subgroup.mem_sup_left C.hd.hzW)

theorem fix_J_of {y w : G} (hy : y ∈ Subgroup.normalizer (W : Set G))
    (hw : w ∈ Subgroup.normalizer (W : Set G))
    (h : Thompson.piG W y * C.D.F.ρ₃.img * (Thompson.piG W y)⁻¹ =
      Thompson.piG W w * C.D.F.ρ₃.img * (Thompson.piG W w)⁻¹) :
    conjSub (w⁻¹ * y) C.D.F.ρ₃.K = C.D.F.ρ₃.K := by
  have hn : w⁻¹ * y ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) hy
  refine (T7D.conj_stable C.D.c hn C.D.F.ρ₃ ?_).1
  rw [Thompson.piG_mul (Subgroup.inv_mem _ hw) hy, Thompson.piG_inv hw]
  calc (Thompson.piG W w)⁻¹ * Thompson.piG W y * C.D.F.ρ₃.img *
        ((Thompson.piG W w)⁻¹ * Thompson.piG W y)⁻¹
      = (Thompson.piG W w)⁻¹ * (Thompson.piG W y * C.D.F.ρ₃.img * (Thompson.piG W y)⁻¹) *
          Thompson.piG W w := by group
    _ = C.D.F.ρ₃.img := by rw [h]; group

theorem good_r : C.D.F.ρ.r ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub C.D.F.ρ.r K = K ∧
    conjSub C.D.F.ρ.r K' = K' :=
  ⟨⟨C.hd.hR.2.2 C.r_mem_R, Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr⟩,
    conjSub_eq_self_of_mem C.r_mem_K,
    mem_normalizer_iff_conjSub_eq.mp (C.mem_normalizer_K'_of_mem_K C.r_mem_K)⟩

theorem good_t : C.D.F.ρ'.r ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub C.D.F.ρ'.r K = K ∧
    conjSub C.D.F.ρ'.r K' = K' :=
  ⟨⟨C.hd.hR'.2.2 C.t_mem_R', Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr⟩,
    mem_normalizer_iff_conjSub_eq.mp (C.mem_normalizer_K_of_mem_K' C.t_mem_K'),
    conjSub_eq_self_of_mem C.t_mem_K'⟩

theorem exists_fix_J {y : G} (hy : y ∈ (S : Subgroup G)) (hK : conjSub y K = K)
    (hK' : conjSub y K' = K') :
    ∃ w : G, (w ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub w K = K ∧ conjSub w K' = K') ∧
      conjSub (w⁻¹ * y) C.D.F.ρ₃.K = C.D.F.ρ₃.K := by
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := C.le_normalizer_W hy
  set q := Thompson.piG W y with hq
  have hr : q * C.D.F.ρ.img * q⁻¹ = C.D.F.ρ.img :=
    C.img_conj_eq_of_fix hyN C.D.F.ρ (by rw [C.hK]; exact hK)
  have ht : q * C.D.F.ρ'.img * q⁻¹ = C.D.F.ρ'.img :=
    C.img_conj_eq_of_fix hyN C.D.F.ρ' (by rw [C.hK']; exact hK')
  set σ := T7D.conjRep C.D.c.hΩ hyN C.D.F.ρ₃ with hσdef
  have hσ : σ.img = q * C.D.F.ρ₃.img * q⁻¹ := T7D.conjRep_img _ _ _
  have hrs : C.D.F.ρ.img * C.D.F.ρ₃.img ≠ C.D.F.ρ₃.img * C.D.F.ρ.img :=
    fun h => C.D.hac ((imgQ_comm_iff _ _).mpr h)
  have hts : C.D.F.ρ'.img * C.D.F.ρ₃.img ≠ C.D.F.ρ₃.img * C.D.F.ρ'.img :=
    C.D.c.noncomm C.D.F.ρ' C.D.F.ρ₃ C.D.F.hne₂ C.D.F.hn₂
  have key : ∀ x : NQuot (W ⊔ OCW W), q * x * q⁻¹ = x →
      x * C.D.F.ρ₃.img ≠ C.D.F.ρ₃.img * x → σ.img * x ≠ x * σ.img := by
    intro x hx hne h
    apply hne
    rw [hσ] at h
    have e : q * (x * C.D.F.ρ₃.img) * q⁻¹ = q * (C.D.F.ρ₃.img * x) * q⁻¹ := by
      calc q * (x * C.D.F.ρ₃.img) * q⁻¹ = (q * x * q⁻¹) * (q * C.D.F.ρ₃.img * q⁻¹) := by group
        _ = x * (q * C.D.F.ρ₃.img * q⁻¹) := by rw [hx]
        _ = (q * C.D.F.ρ₃.img * q⁻¹) * x := h.symm
        _ = (q * C.D.F.ρ₃.img * q⁻¹) * (q * x * q⁻¹) := by rw [hx]
        _ = q * (C.D.F.ρ₃.img * x) * q⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hσr := key _ hr (fun h => hrs h)
  have hσt := key _ ht (fun h => hts h)
  set a := C.D.φ (T7D.imgQ C.D.F.ρ)
  set b := C.D.φ (T7D.imgQ C.D.F.ρ')
  set c := C.D.φ (T7D.imgQ C.D.F.ρ₃)
  set c' := C.D.φ (T7D.imgQ σ)
  have hab : a ≠ b := fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : a * b = b * a := by rw [← map_mul, ← map_mul, C.D.hcomm]
  have hac : a * c ≠ c * a := by
    intro h; apply C.D.hac; apply C.D.φ.injective; rw [map_mul, map_mul]; exact h
  have hc'a : c' * a ≠ a * c' := by
    intro h; apply hσr; rw [← imgQ_comm_iff]; apply C.D.φ.injective
    rw [map_mul, map_mul]; exact h
  have hc'b : c' * b ≠ b * c' := by
    intro h; apply hσt; rw [← imgQ_comm_iff]; apply C.D.φ.injective
    rw [map_mul, map_mul]; exact h
  have hval : ∀ X : ↥(muGroup Ω W), c' = C.D.φ X → σ.img = (X : NQuot (W ⊔ OCW W)) :=
    fun X h => congrArg Subtype.val (C.D.φ.injective h)
  have hrr := C.piG_r_sq
  have htt := C.piG_t_sq
  have hrinv : (Thompson.piG W C.D.F.ρ.r)⁻¹ = Thompson.piG W C.D.F.ρ.r :=
    inv_eq_of_mul_eq_one_right hrr
  have htinv : (Thompson.piG W C.D.F.ρ'.r)⁻¹ = Thompson.piG W C.D.F.ρ'.r :=
    inv_eq_of_mul_eq_one_right htt
  rcases S4.swap_word a (C.φ_imgQ_mem _) b (C.φ_imgQ_mem _) c (C.φ_imgQ_mem _) hab hcomm hac c'
      (C.φ_imgQ_mem _) with h | h | h | h | h | h
  · exact absurd (by rw [h]) hc'a
  · exact absurd (by rw [h, hcomm]) hc'a
  · refine ⟨1, ⟨Subgroup.one_mem _, by simp [conjSub_one], by simp [conjSub_one]⟩, ?_⟩
    refine C.fix_J_of hyN (Subgroup.one_mem _) ?_
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ₃) h, Thompson.piG_of_mem_sup (Subgroup.one_mem _)]
    simp [T7D.imgQ]
  · refine ⟨C.D.F.ρ.r, C.good_r, C.fix_J_of hyN C.D.F.ρ.r_mem_normalizer ?_⟩
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ₃ * T7D.imgQ C.D.F.ρ)
      (by rw [h, map_mul, map_mul]), hrinv]
    rfl
  · refine ⟨C.D.F.ρ'.r, C.good_t, C.fix_J_of hyN C.D.F.ρ'.r_mem_normalizer ?_⟩
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ₃ * T7D.imgQ C.D.F.ρ')
      (by rw [h, map_mul, map_mul]), htinv]
    rfl
  · refine ⟨C.D.F.ρ.r * C.D.F.ρ'.r, good_mul C.good_r C.good_t,
      C.fix_J_of hyN (Subgroup.mul_mem _ C.D.F.ρ.r_mem_normalizer C.D.F.ρ'.r_mem_normalizer) ?_⟩
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ₃ *
        T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ) (by rw [h, map_mul, map_mul, map_mul, map_mul]),
      Thompson.piG_mul C.D.F.ρ.r_mem_normalizer C.D.F.ρ'.r_mem_normalizer, mul_inv_rev, hrinv,
      htinv]
    change C.D.F.ρ.img * C.D.F.ρ'.img * C.D.F.ρ₃.img * C.D.F.ρ'.img * C.D.F.ρ.img = _
    unfold Thompson.Rep.img
    group

include C in
theorem exists_decomp {y : G} (hy : y ∈ (S : Subgroup G)) :
    ∃ x ∈ (S : Subgroup G) ⊓ MGrp Ω W, ∃ t ∈ (S : Subgroup G), TrivMu Ω W t ∧ y = x * t := by
  obtain ⟨x₀, hx₀P, hx₀K⟩ : ∃ x₀ ∈ (S : Subgroup G) ⊓ MGrp Ω W, conjSub (x₀⁻¹ * y) K = K := by
    rcases C.conjSub_K_mem hy with h | h
    · exact ⟨1, Subgroup.one_mem _, by rw [inv_one, one_mul, h]⟩
    · obtain ⟨x₀, hx₀P, hx₀⟩ := C.exists_swap
      refine ⟨x₀, hx₀P, ?_⟩
      rw [conjSub_mul, h, ← hx₀, conjSub_inv_conjSub]
  set y₁ := x₀⁻¹ * y with hy₁
  have hy₁S : y₁ ∈ (S : Subgroup G) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₀P.1) hy
  have hy₁K' : conjSub y₁ K' = K' := C.conjSub_K'_of_K hx₀K
  obtain ⟨w, hw, hwJ⟩ := C.exists_fix_J hy₁S hx₀K hy₁K'
  refine ⟨x₀ * w, Subgroup.mul_mem _ hx₀P hw.1, w⁻¹ * y₁,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hw.1.1) hy₁S, ?_, by rw [hy₁]; group⟩
  have hwK : conjSub w⁻¹ K = K := by
    conv_lhs => rw [← hw.2.1]
    exact conjSub_inv_conjSub w K
  have hwK' : conjSub w⁻¹ K' = K' := by
    conv_lhs => rw [← hw.2.2]
    exact conjSub_inv_conjSub w K'
  have htN : w⁻¹ * y₁ ∈ Subgroup.normalizer (W : Set G) :=
    C.le_normalizer_W (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw.1.1) hy₁S)
  refine C.trivMu_of_fix htN ?_ ?_ hwJ
  · rw [C.hK, conjSub_mul, hx₀K, hwK]
  · rw [C.hK', conjSub_mul, hy₁K', hwK']

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
