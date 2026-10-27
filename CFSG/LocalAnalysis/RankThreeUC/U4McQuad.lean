module

public import CFSG.LocalAnalysis.RankThreeUC.U4McPlane

public section

namespace CFSG.LocalAnalysis.RankThreeUC.U4Mc

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.RankThreeUC (sesqPerp mem_sesqPerp_iff qd_finrank_sesqPerp_add
  qd_sesqPerp_sesqPerp qdImage qd_sub_mulVec_mem qd_image_fix qd_mem_sesqPerp_image_iff qdEnd
  mem_qdEnd qd_natCard_qdEnd qdAdj qdAdj_herm qdAdj_qdAdj qdAdj_smul qdAdjE qdAdj_toLin
  qd_conjTr_sub_one card_fix_sq_of_semilinear_involution su4_quadratic_card_le)

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem eq_of_herm_eq (hσ : ∀ c, σ (σ c) = c) {y y' : Fin 4 → F}
    (h : ∀ x, herm σ x y = herm σ x y') : y = y' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_herm σ fun x => herm_eq_zero_comm σ hσ ?_
  rw [herm_sub_right, h x, sub_self]

@[expose] def rankOne (σ : F ≃+* F) (u : Fin 4 → F) : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
  LinearMap.smulRight (hermL σ u) u

theorem rankOne_apply (u x : Fin 4 → F) : rankOne σ u x = herm σ u x • u := rfl

theorem qdAdj_rankOne (hσ : ∀ c, σ (σ c) = c) (u : Fin 4 → F) :
    qdAdj σ (rankOne σ u) = rankOne σ u := by
  refine LinearMap.ext fun y => eq_of_herm_eq hσ fun x => ?_
  rw [← qdAdj_herm, rankOne_apply, rankOne_apply, herm_smul_left, herm_smul_right,
    herm_conj σ hσ u x, mul_comm]

theorem su4_quadratic_structure [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (B : Subgroup (GL (Fin 4) F)) (hBU : B ≤ SUid σ 4) (hinv : ∀ b ∈ B, b * b = 1)
    (hquad : ∀ b ∈ B, ∀ b' ∈ B,
      ((b : Matrix (Fin 4) (Fin 4) F) - 1) * ((b' : Matrix (Fin 4) (Fin 4) F) - 1) = 0)
    (hB : B ≠ ⊥)
    (hcard : Nat.card F ^ 4 ≤
      Nat.card B * Nat.card {x : Fin 4 → F // ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x}) :
    Nat.card B = Nat.card F ^ 2 ∧ IsTI σ (qdImage B) ∧ Module.finrank F (qdImage B) = 2 ∧
      (∀ x, x ∈ qdImage B ↔ ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x) ∧
      ∀ u ∈ qdImage B, ∃ b ∈ B, ∀ x,
        (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x + herm σ u x • u := by
  set I : Submodule F (Fin 4 → F) := qdImage B with hIdef
  set C : Submodule F (Fin 4 → F) := sesqPerp σ I with hCdef
  have hC : C = sesqPerp σ I := rfl
  have hI : I = sesqPerp σ C := (qd_sesqPerp_sesqPerp hσ.invol I).symm
  have hfix : ∀ x, x ∈ C ↔ ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x :=
    fun x => qd_mem_sesqPerp_image_iff hσ hBU hinv x
  have hIC : I ≤ C := by
    intro w hw
    rw [hfix]
    intro b hb
    have h0 := qd_image_fix hquad hw b hb
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h0
    exact sub_eq_zero.mp h0
  have hsum : Module.finrank F C + Module.finrank F I = 4 := qd_finrank_sesqPerp_add σ I
  have hle : Module.finrank F I ≤ Module.finrank F C := Submodule.finrank_mono hIC
  have hEcard : Nat.card ↥(qdEnd C I) =
      Nat.card F ^ (Module.finrank F I * Module.finrank F I) := by
    rw [qd_natCard_qdEnd C I, show 4 - Module.finrank F C = Module.finrank F I by omega]
  have hEfin : Finite ↥(qdEnd C I) := by
    apply Nat.finite_of_card_ne_zero
    rw [hEcard]
    exact pow_ne_zero _ (Nat.card_pos (α := F)).ne'
  let s : ↥(qdEnd C I) ≃+ ↥(qdEnd C I) := qdAdjE σ hσ.invol hC hI
  have hs : ∀ (c : F) (x : ↥(qdEnd C I)), s (c • x) = σ c • s x :=
    fun c x => Subtype.ext (qdAdj_smul σ c x.1)
  have hss : ∀ x, s (s x) = x := fun x => Subtype.ext (qdAdj_qdAdj σ hσ.invol x.1)
  have hdesc := card_fix_sq_of_semilinear_involution (K := F) (C := ↥(qdEnd C I))
    σ.toRingHom hσ.invol hσ.exists_ne s hs hss
  have hmem : ∀ b ∈ B, Matrix.toLin' ((b : Matrix (Fin 4) (Fin 4) F) - 1) ∈ qdEnd C I := by
    intro b hb
    rw [mem_qdEnd]
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, (hfix x).mp hx b hb,
        sub_self]
    · rw [Matrix.toLin'_apply]
      exact qd_sub_mulVec_mem hb x
  let f : ↥B → {x : ↥(qdEnd C I) // s x = x} := fun b =>
    ⟨⟨Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1), hmem b.1 b.2⟩, by
      apply Subtype.ext
      show qdAdj σ (Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1)) =
        Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1)
      rw [qdAdj_toLin, qd_conjTr_sub_one (hBU b.2) (hinv b.1 b.2)]⟩
  have hf : Function.Injective f := by
    intro b b' h
    have h1 : Matrix.toLin' ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1) =
        Matrix.toLin' ((b'.1 : Matrix (Fin 4) (Fin 4) F) - 1) :=
      congrArg (fun z : {x : ↥(qdEnd C I) // s x = x} => z.1.1) h
    have h2 : ((b.1 : Matrix (Fin 4) (Fin 4) F) - 1) =
        ((b'.1 : Matrix (Fin 4) (Fin 4) F) - 1) :=
      (LinearEquiv.injective Matrix.toLin') h1
    exact Subtype.ext (Units.ext (sub_left_inj.mp h2))
  have hcardB : Nat.card ↥B ≤ Nat.card {x : ↥(qdEnd C I) // s x = x} :=
    Nat.card_le_card_of_injective f hf
  have hfixcard : Nat.card {x : Fin 4 → F // ∀ b ∈ B, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x} =
      Nat.card F ^ Module.finrank F C := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => (hfix x).symm)]
    exact Module.natCard_eq_pow_finrank (K := F) (V := C)
  rw [hfixcard] at hcard
  set r := Module.finrank F I with hr
  set X := Nat.card {x : ↥(qdEnd C I) // s x = x} with hX
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hX2 : X ^ 2 = Nat.card F ^ (r * r) := hdesc.trans hEcard
  have hc : Module.finrank F C = 4 - r := by omega
  have hr2 : r = 2 := by
    have hr4 : r ≤ 2 := by omega
    have h8 : (Nat.card F ^ 4) ^ 2 ≤ (X * Nat.card F ^ (4 - r)) ^ 2 := by
      rw [← hc]
      exact Nat.pow_le_pow_left (hcard.trans (Nat.mul_le_mul_right _ hcardB)) 2
    rw [mul_pow, hX2, ← pow_mul, ← pow_mul, ← pow_add] at h8
    have h8' : 4 * 2 ≤ r * r + (4 - r) * 2 := (Nat.pow_le_pow_iff_right hq).mp h8
    interval_cases r
    ·
      exfalso
      have hX1 : X ≤ 1 := by
        have : X ^ 2 = 1 := by rw [hX2]; simp
        nlinarith
      apply hB
      rw [eq_bot_iff]
      intro b hb
      have hle1 : Nat.card ↥B ≤ 1 := hcardB.trans hX1
      have h1 : (⟨b, hb⟩ : ↥B) = 1 := Finite.card_le_one_iff_subsingleton.mp hle1 |>.elim _ _
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    · omega
    · rfl
  have hIC' : I = C := Submodule.eq_of_le_of_finrank_eq hIC (by omega)
  have hXq : X = Nat.card F ^ 2 := by
    rw [hr2] at hX2
    have : X ^ 2 = (Nat.card F ^ 2) ^ 2 := by rw [hX2, ← pow_mul]
    exact (Nat.pow_left_injective two_ne_zero) this
  have hBcard : Nat.card ↥B = Nat.card F ^ 2 := by
    refine le_antisymm (hcardB.trans hXq.le) ?_
    rw [hc, hr2] at hcard
    have hpos : 0 < Nat.card F ^ 2 := pow_pos (by omega) 2
    have : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card ↥B * Nat.card F ^ 2 := by
      rw [← pow_add]
      exact hcard
    exact Nat.le_of_mul_le_mul_right this hpos
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [← hX, hXq, hBcard])
  refine ⟨hBcard, ?_, hr2, ?_, ?_⟩
  · intro w hw w' hw'
    have hw'C : w' ∈ C := hIC hw'
    exact mem_sesqPerp_iff.mp hw'C w hw
  · intro x
    rw [hIC']
    exact hfix x
  · intro u hu
    have hR : rankOne σ u ∈ qdEnd C I := by
      rw [mem_qdEnd]
      refine ⟨fun x hx => ?_, fun x => I.smul_mem _ hu⟩
      rw [rankOne_apply, mem_sesqPerp_iff.mp hx u hu, zero_smul]
    obtain ⟨b, hb⟩ := hbij.2 ⟨⟨rankOne σ u, hR⟩, Subtype.ext (qdAdj_rankOne hσ.invol u)⟩
    refine ⟨b.1, b.2, fun x => ?_⟩
    have h1 := congrArg (fun z : {x : ↥(qdEnd C I) // s x = x} => z.1.1 x) hb
    simp only [f, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, rankOne_apply] at h1
    rw [← h1]
    abel

theorem commutant_transvections [Finite F] (h2 : (2 : F) = 0)
    {W : Submodule F (Fin 4 → F)} (hW : IsTI σ W) (hW2 : Module.finrank F W = 2)
    {a : AddAut (Fin 4 → F)} (ha2 : ∀ x, a (a x) = x) {θ : F →+* F}
    (hθ : ∀ (c : F) (x : Fin 4 → F), a (c • x) = θ c • a x)
    (hcomm : ∀ u ∈ W, ∀ x, a (x + herm σ u x • u) = a x + herm σ u (a x) • u) :
    (∀ c, θ c = c) ∧ (∀ w ∈ W, a w = w) ∧ ∀ x, a x - x ∈ W := by
  have heig : ∀ u ∈ W, ∃ l : F, a u = l • u := by
    intro u hu
    by_cases hu0 : u = 0
    · exact ⟨0, by rw [hu0, map_zero, smul_zero]⟩
    obtain ⟨x, hx⟩ := exists_herm_eq_one σ hu0
    refine ⟨herm σ u (a x), ?_⟩
    have h := hcomm u hu x
    rw [hx, map_add, one_smul] at h
    exact add_left_cancel h
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁0, hspan, hind⟩ := exists_pair_of_finrank_eq_two hW2
  obtain ⟨l₁, hl₁⟩ := heig u₁ hu₁
  obtain ⟨l₂, hl₂⟩ := heig u₂ hu₂
  have hkey : ∀ c : F, θ c * l₁ = c * l₂ ∧ True := by
    intro c
    obtain ⟨μ, hμ⟩ := heig (c • u₁ + u₂) (W.add_mem (W.smul_mem c hu₁) hu₂)
    rw [map_add, hθ, hl₁, hl₂, smul_smul, smul_add, smul_smul] at hμ
    have h0 : (θ c * l₁ - μ * c) • u₁ + (l₂ - μ) • u₂ = 0 := by
      rw [sub_smul, sub_smul, ← sub_eq_zero.mpr hμ]
      abel
    obtain ⟨h1, h2'⟩ := hind _ _ h0
    refine ⟨?_, trivial⟩
    rw [sub_eq_zero] at h1 h2'
    rw [h1, h2', mul_comm]
  have hl₁₂ : l₁ = l₂ := by
    have h := (hkey 1).1
    rwa [map_one, one_mul, one_mul] at h
  have hl0 : l₁ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hl₁
    apply hu₁0
    rw [← ha2 u₁, hl₁, map_zero]
  have hθid : ∀ c, θ c = c := by
    intro c
    have h := (hkey c).1
    rw [← hl₁₂] at h
    exact mul_right_cancel₀ hl0 h
  have hW' : ∀ w ∈ W, a w = l₁ • w := by
    intro w hw
    obtain ⟨α, β, rfl⟩ := hspan w hw
    rw [map_add, hθ, hθ, hl₁, hl₂, hθid, hθid, ← hl₁₂, smul_smul, smul_smul, smul_add,
      smul_smul, smul_smul, mul_comm α, mul_comm β]
  have hl1 : l₁ = 1 := by
    have h := ha2 u₁
    rw [hl₁, hθ, hl₁, smul_smul, hθid] at h
    have h' : (l₁ * l₁ - 1) • u₁ = 0 := by rw [sub_smul, h, one_smul, sub_self]
    have hsq : l₁ * l₁ - 1 = 0 := (smul_eq_zero.mp h').resolve_right hu₁0
    have : (l₁ - 1) * (l₁ - 1) = 0 := by linear_combination hsq - l₁ * h2 + h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  have hWfix : ∀ w ∈ W, a w = w := fun w hw => by rw [hW' w hw, hl1, one_smul]
  refine ⟨hθid, hWfix, fun x => hW.mem_of_herm_eq_zero hW2 fun u hu => ?_⟩
  have h := hcomm u hu x
  rw [map_add, hθ, hθid, hWfix u hu] at h
  have h' : (herm σ u x - herm σ u (a x)) • u = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel h)
  rcases smul_eq_zero.mp h' with h0 | h0
  · rw [herm_sub_right]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h0).symm
  · rw [h0, herm_zero_left]

theorem card_sq_le_of_two_planes [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (D : Subgroup (GL (Fin 4) F)) (hDU : D ≤ SUid σ 4) {W₁ W₂ : Submodule F (Fin 4 → F)}
    (hW₁2 : Module.finrank F W₁ = 2) (hW₂2 : Module.finrank F W₂ = 2) (hne : W₁ ≠ W₂)
    (hD : ∀ d ∈ D, (∀ w ∈ W₁, (d : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w) ∧
      (∀ w ∈ W₂, (d : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w) ∧
      ∀ x, (d : Matrix (Fin 4) (Fin 4) F) *ᵥ x - x ∈ W₁) :
    Nat.card D ^ 2 ≤ Nat.card F := by
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hquad : ∀ d ∈ D, ∀ d' ∈ D,
      ((d : Matrix (Fin 4) (Fin 4) F) - 1) * ((d' : Matrix (Fin 4) (Fin 4) F) - 1) = 0 := by
    intro d hd d' hd'
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    have hy : ((d' : Matrix (Fin 4) (Fin 4) F) - 1) *ᵥ Pi.single j 1 ∈ W₁ := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hD d' hd').2.2 _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, (hD d hd).1 _ hy, sub_self]
  have hinv : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    have h := hquad d hd d hd
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    have e : (d : Matrix (Fin 4) (Fin 4) F) * d =
        ((d : Matrix (Fin 4) (Fin 4) F) - 1) * ((d : Matrix (Fin 4) (Fin 4) F) - 1) +
          (2 : F) • (d : Matrix (Fin 4) (Fin 4) F) - 1 := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, one_mul, two_smul]
      abel
    rw [e, h, h2F, zero_smul, add_zero, zero_sub]
    have h1 : (-1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [neg_eq_iff_add_eq_zero, ← two_smul F (1 : Matrix (Fin 4) (Fin 4) F), h2F, zero_smul]
    exact h1
  obtain ⟨r, -, hfix, hsq⟩ := su4_quadratic_card_le σ hσ D hDU hinv hquad
  have hlt : W₁ < W₁ ⊔ W₂ := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have hle : W₂ ≤ W₁ := by rw [h]; exact le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hW₁2, hW₂2])).symm
  have h3 : 3 ≤ Module.finrank F ↥(W₁ ⊔ W₂) := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hinj : Nat.card ↥(W₁ ⊔ W₂) ≤
      Nat.card {x : Fin 4 → F // ∀ b ∈ D, (b : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x} := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, fun d hd => ?_⟩) ?_
    · obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp x.2
      rw [← hyz, Matrix.mulVec_add, (hD d hd).1 y hy, (hD d hd).2.1 z hz]
    · intro x y h
      exact Subtype.ext (Subtype.mk.inj h)
  rw [hfix, Module.natCard_eq_pow_finrank (K := F) (V := ↥(W₁ ⊔ W₂))] at hinj
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h4r : 3 ≤ 4 - r :=
    (Nat.pow_le_pow_iff_right hq).mp ((Nat.pow_le_pow_right (by omega) h3).trans hinj)
  have hr1 : r ≤ 1 := by omega
  calc Nat.card D ^ 2 ≤ Nat.card F ^ (r ^ 2) := hsq
    _ ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right (by omega) (by interval_cases r <;> norm_num)
    _ = Nat.card F := pow_one _

end CFSG.LocalAnalysis.RankThreeUC.U4Mc
