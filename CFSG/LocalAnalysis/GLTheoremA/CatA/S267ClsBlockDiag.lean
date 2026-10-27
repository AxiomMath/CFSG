module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAssembleDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCasesScal
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
import CFSG.GroupTheory.PLayer.CenterQuotientAction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (conjOn coe_conjOn)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}
variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_block_diag (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) [Finite K]
    {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} (hHβ : H ≤ isomGL β)
    (φ : ↥H →* Ω)
    (hφS : φ.range = S) (hφk : φ.ker ≤ (StatedScalars ι K).subgroupOf H)
    {B₁ : Subgroup Ω} (hB₁B : B₁ ≤ B) (θ : ↥B₁ →* GL ι K) (hθβ : ∀ x, θ x ∈ isomGL β)
    (hθN : ∀ x, θ x ∈ Subgroup.normalizer (H : Set (GL ι K)))
    (hθφ : ∀ x (k : ↥H), φ (conjOn (hθN x) k) = (x : Ω) * φ k * (x : Ω)⁻¹)
    {b : Ω} {A : GL ι K} {σ : K ≃+* K}
    (hsplit : B₁ = B ∨ (b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
      Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ))
    {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (hIH : blkI β U W ≤ H) (hIq : CFSG.Open.IsQuasisimple ↥(blkI β U W))
    (hpI : p ∣ Nat.card ↥(blkI β U W)) {D : Subgroup Ω} (hDB : D ≤ B₁)
    (hD : ∀ x : ↥B₁, (x : Ω) ∈ D ↔ ∃ c : K, ∀ u ∈ U, glEquiv (θ x) u = c • u)
    (hθU : ∀ x : ↥B₁, ∀ u ∈ U, glEquiv (θ x) u ∈ U)
    (hθW : ∀ x : ↥B₁, ∀ w ∈ W, glEquiv (θ x) w ∈ W)
    (hCpres : ∀ g ∈ H, (∀ x : ↥B₁, (x : Ω) ∈ D → g * θ x = θ x * g) →
      (∀ u ∈ U, glEquiv g u ∈ U) ∧ ∀ w ∈ W, glEquiv g w ∈ W)
    (hSchur : ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
      ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u)
    (hfield : (b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ) →
      (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) ∧ (∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) ∧
      ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ w ∈ W, glEquiv y w ∈ W) →
        ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j)
    (hDc : p ^ 2 ≤ Nat.card D) (hDBc : p ^ 2 * Nat.card D ≤ Nat.card B)
    (hE : Nat.card D = p ^ 2 →
      (∃ x : ↥B₁, (x : Ω) ∉ D ∧
        GLAPLayer p (blkI β U W ⊓ Subgroup.centralizer {θ x}) ≠ ⊥) ∨
      ((b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ) ∧
        GLAPLayer p (blkI β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥))
    {z : GL ι K} (hzH : z ∈ H) (hz2 : z ^ 2 = 1) {ε₁ ε₂ : K} (hε : ε₁ ≠ ε₂)
    (hzU : ∀ u ∈ U, glEquiv z u = ε₁ • u) (hzW : ∀ w ∈ W, glEquiv z w = ε₂ • w)
    (hU0 : U ≠ ⊥) (hW0 : W ≠ ⊥) : S267ConcA p S B := by
  classical
  set I : Subgroup ↥H := (blkI β U W).subgroupOf H with hIdef
  have hmemI : ∀ j : ↥H, j ∈ I ↔ (j : GL ι K) ∈ blkI β U W := fun j => Subgroup.mem_subgroupOf
  let eI : ↥I ≃* ↥(blkI β U W) := Subgroup.subgroupOfEquivOfLe hIH
  have hIq' : CFSG.Open.IsQuasisimple ↥I := CFSG.Open.IsQuasisimple.of_mulEquiv eI hIq
  have hpI' : p ∣ Nat.card ↥I := by rw [Nat.card_congr eI.toEquiv]; exact hpI
  have hker : φ.ker ≤ Subgroup.center ↥H :=
    hφk.trans (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center H)
  have hjU : ∀ j ∈ blkI β U W, ∀ u ∈ U, glEquiv j u ∈ U := fun j hj =>
    (blkI_le_blkSub β U W hj).2.1
  have hjW : ∀ j ∈ blkI β U W, ∀ w ∈ W, glEquiv j w = w := fun j hj =>
    (blkI_le_blkSub β U W hj).2.2
  have hIker : ¬ p ∣ Nat.card ↥(I ⊓ φ.ker) := by
    have hbot : I ⊓ φ.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨hgI, hgk⟩
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hφk hgk)
      have hc' : Matrix.GeneralLinearGroup.scalar ι c = (g : GL ι K) := hc
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      have h1 := hjW _ ((hmemI g).mp hgI) w hw
      rw [← hc', glEquiv_scalar_apply] at h1
      have hc1 : (c : K) = 1 := by
        have h2 : ((c : K) - 1) • w = 0 := by rw [sub_smul, h1, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)
      have hg1 : (g : GL ι K) = 1 := by
        rw [← hc', show c = 1 from Units.ext hc1, map_one]
      exact Subgroup.mem_bot.mpr (Subtype.ext hg1)
    rw [hbot, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hθI : ∀ (x : ↥B₁) (j : GL ι K), j ∈ blkI β U W →
      θ x * j * (θ x)⁻¹ ∈ blkI β U W := fun x j hj =>
    conj_mem_blkI (hθβ x) (hθU x) (hθW x) hj
  obtain ⟨lift, hlift, hlift₁, hshape⟩ : ∃ lift : ↥B → MulAut ↥H,
      (∀ (x : ↥B) (h : ↥H), φ (lift x h) = (x : Ω) * φ h * (x : Ω)⁻¹) ∧
      (∀ (x : ↥B) (hx : (x : Ω) ∈ B₁), lift x = conjOn (hθN ⟨x, hx⟩)) ∧
      (∀ x : ↥B, (x : Ω) ∉ B₁ → (b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ) ∧
        ∃ y : ↥B₁, ∃ k : ℕ, 0 < k ∧ k < p ∧ (x : Ω) = y * b ^ k ∧
          ∀ h : ↥H, ((lift x h : ↥H) : GL ι K) =
            θ y * (ModelGen.semiConj A σ ^ k) h * (θ y)⁻¹) := by
    rcases hsplit with hBB | hF
    · refine ⟨fun x => conjOn (hθN ⟨x, by rw [hBB]; exact x.2⟩), fun x h => ?_,
        fun x hx => rfl, fun x hx => absurd (by rw [hBB]; exact x.2) hx⟩
      exact hθφ _ h
    · have hF' := hF
      obtain ⟨hbB, hbN, hBb, hbout, hact, hform⟩ := hF
      choose y hy k hk hxk using fun x : ↥B =>
        exists_mul_pow_of_mem_sup hp hB hB₁B hbB (hBb ▸ x.2 : (x : Ω) ∈ B₁ ⊔ Subgroup.zpowers b)
      refine ⟨fun x => if hx : (x : Ω) ∈ B₁ then conjOn (hθN ⟨x, hx⟩)
          else conjOn (hθN ⟨y x, hy x⟩) * semiAut A σ (semiConj_mem_of_fieldAct hact) ^ k x,
        fun x h => ?_, fun x hx => ?_, fun x hx => ⟨hF', ⟨y x, hy x⟩, k x, ?_, hk x, hxk x,
          fun h => ?_⟩⟩
      · dsimp only
        by_cases hx : (x : Ω) ∈ B₁
        · rw [dif_pos hx]
          exact hθφ _ h
        · rw [dif_neg hx, MulAut.mul_apply, hθφ, map_semiAut_pow hact, hxk x]
          simp only [Subgroup.coe_mk]
          group
      · simp only [dif_pos hx]
      · rcases Nat.eq_zero_or_pos (k x) with h0 | h0
        · exact absurd (by rw [hxk x, h0, pow_zero, mul_one]; exact hy x) hx
        · exact h0
      · dsimp only
        rw [dif_neg hx, MulAut.mul_apply, coe_conjOn, coe_semiAut_pow_apply]
  set X : Subgroup ↥H := ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ D} => lift x.1)
    with hXdef
  have hmemX : ∀ g : ↥H, g ∈ X ↔
      ∀ x : ↥B₁, (x : Ω) ∈ D → (g : GL ι K) * θ x = θ x * g := by
    intro g
    rw [hXdef, ModelGen.mem_fixFam]
    constructor
    · intro h x hx
      have h1 := h ⟨⟨x, hB₁B x.2⟩, hx⟩
      rw [hlift₁ _ x.2] at h1
      have h2 := congrArg Subtype.val h1
      rw [coe_conjOn] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro h x
      rw [hlift₁ _ (hDB x.2)]
      apply Subtype.ext
      rw [coe_conjOn, ← h ⟨x.1, hDB x.2⟩ x.2, mul_inv_cancel_right]
  have hIX : I ≤ X := by
    intro j hj
    rw [hmemX]
    intro x hx
    obtain ⟨c, hc⟩ := (hD x).mp hx
    exact (comm_of_scalar_of_block hUW hc (hθW x) (hjU _ ((hmemI j).mp hj))
      (hjW _ ((hmemI j).mp hj))).symm
  have hXN : X ≤ Subgroup.normalizer (I : Set ↥H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro j
    obtain ⟨hgU, hgW⟩ := hCpres g g.2 ((hmemX g).mp hg)
    obtain ⟨hgU', hgW'⟩ := hCpres (g⁻¹ : ↥H) (g⁻¹).2 ((hmemX g⁻¹).mp (X.inv_mem hg))
    constructor
    · intro hj
      rw [hmemI] at hj ⊢
      simpa using conj_mem_blkI (hHβ g.2) hgU hgW hj
    · intro hj
      rw [hmemI] at hj ⊢
      have h1 := conj_mem_blkI (hHβ (g⁻¹).2) hgU' hgW' hj
      have e : ((g⁻¹ : ↥H) : GL ι K) * ((g * j * g⁻¹ : ↥H) : GL ι K) *
          ((g⁻¹ : ↥H) : GL ι K)⁻¹ = (j : GL ι K) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e] at h1
      exact h1
  have hInorm : (I.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIX).mpr hXN
  have hI : GLAPComponent p X I :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hIq' hpI' hIX hInorm
  have hlI : ∀ (x : ↥B) (j : ↥H), j ∈ I → lift x j ∈ I := by
    intro x j hj
    rw [hmemI] at hj ⊢
    by_cases hx : (x : Ω) ∈ B₁
    · rw [hlift₁ x hx, coe_conjOn]
      exact hθI ⟨x, hx⟩ j hj
    · obtain ⟨hF, y, k, -, -, -, hlx⟩ := hshape x hx
      obtain ⟨haU, haW, -⟩ := hfield hF
      rw [hlx]
      exact hθI y _ (semiConj_pow_mem_blkI hF.2.2.2.2.2 haU haW k hj)
  have hIB : ∀ x : ↥B, I.map (lift x).toMonoidHom = I := by
    intro x
    have hle : I.map (lift x).toMonoidHom ≤ I := by
      rintro _ ⟨j, hj, rfl⟩
      exact hlI x j hj
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (lift x).injective])
  have hID : ∀ x : ↥B, (∀ j ∈ I, lift x j = j) → (x : Ω) ∈ D := by
    intro x hfixI
    by_cases hx : (x : Ω) ∈ B₁
    · have hcomm : ∀ j ∈ blkI β U W, θ ⟨x, hx⟩ * j = j * θ ⟨x, hx⟩ := by
        intro j hj
        have h1 := hfixI ⟨j, hIH hj⟩ ((hmemI _).mpr hj)
        rw [hlift₁ x hx] at h1
        have h2 := congrArg Subtype.val h1
        rw [coe_conjOn] at h2
        exact mul_inv_eq_iff_eq_mul.mp h2
      obtain ⟨c, hc⟩ := hSchur _ (hθU ⟨x, hx⟩) hcomm
      exact (hD ⟨x, hx⟩).mpr ⟨c, hc⟩
    · exfalso
      obtain ⟨hF, y, k, hk0, hkp, -, hlx⟩ := hshape x hx
      obtain ⟨-, -, hno⟩ := hfield hF
      refine hno _ (hθU y) (hθW y) k hk0 hkp fun j hj => ?_
      have h1 := hfixI ⟨j, hIH hj⟩ ((hmemI _).mpr hj)
      have h2 := congrArg Subtype.val h1
      rw [hlx] at h2
      exact h2
  set zH : ↥H := ⟨z, hzH⟩ with hzHdef
  have hzθ : ∀ x : ↥B₁, θ x * z = z * θ x := fun x =>
    comm_of_two_scalars hUW hzU hzW (hθU x) (hθW x)
  have hzD : ∀ x : ↥B, (x : Ω) ∈ D → lift x zH = zH := by
    intro x hx
    rw [hlift₁ x (hDB hx)]
    apply Subtype.ext
    rw [coe_conjOn, hzHdef, hzθ, mul_inv_cancel_right]
  have hzI : ∀ j ∈ I, j * zH = zH * j := by
    intro j hj
    rw [hmemI] at hj
    apply Subtype.ext
    exact comm_of_two_scalars hUW hzU hzW (hjU _ hj) (fun w hw => by rw [hjW _ hj w hw]; exact hw)
  have hz1 : φ zH ≠ 1 := by
    intro h
    have hk : zH ∈ φ.ker := h
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hφk hk)
    have hc' : Matrix.GeneralLinearGroup.scalar ι c = z := hc
    have hz : ∀ v, glEquiv z v = (c : K) • v := by
      intro v
      rw [← hc', glEquiv_scalar_apply]
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have e1 : ε₁ = c := smul_left_injective K hu0 ((hzU u hu).symm.trans (hz u))
    have e2 : ε₂ = c := smul_left_injective K hw0 ((hzW w hw).symm.trans (hz w))
    exact hε (e1.trans e2.symm)
  have hz2' : zH ^ 2 = 1 := Subtype.ext (by simpa [hzHdef] using hz2)
  have hDB' : D ≤ B := hDB.trans hB₁B
  have key : ∀ E : Subgroup Ω, E ≤ B → D ≤ E → (Nat.card D = p ^ 2 → Nat.card E = p ^ 3) →
      (Nat.card D = p ^ 2 → GLAPLayer p
        (I ⊓ ModelGen.fixFam fun x : {x : ↥B // (x : Ω) ∈ E} => lift x.1) ≠ ⊥) →
      S267ConcA p S B := fun E hEB hDE hEc hIE =>
    concA_of_lift_diag hp hB hBC φ hφS hker lift hlift hDB' hEB hDE hDc hDBc hEc hIker hI hIq'
      hpI' hIB hID hIE hz1 hz2' hzI hzD
  have hlayer : ∀ Y : Subgroup (GL ι K), Y ≤ H → GLAPLayer p Y ≠ ⊥ →
      GLAPLayer p (Y.subgroupOf H) ≠ ⊥ := by
    intro Y hYH hY hbot
    apply hY
    have h1 := CFSG.glaPLayer_map_eq_of_injective hp H.subtype H.subtype_injective (Y.subgroupOf H)
    rw [hbot, Subgroup.map_bot, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYH] at h1
    exact h1.symm
  by_cases hD2 : Nat.card D = p ^ 2
  · rcases hE hD2 with ⟨x₀, hx₀D, hlay⟩ | ⟨hF, hlay⟩
    ·
      have hEB₁ : D ⊔ Subgroup.zpowers (x₀ : Ω) ≤ B₁ :=
        sup_le hDB (Subgroup.zpowers_le.mpr x₀.2)
      refine key (D ⊔ Subgroup.zpowers (x₀ : Ω)) (hEB₁.trans hB₁B) le_sup_left
        (fun _ => ?_) (fun _ => ?_)
      · rw [card_sup_zpowers_of_not_mem hp hB hDB' (hB₁B x₀.2) hx₀D, hD2]
        ring
      · have hEq : I ⊓ ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ D ⊔
            Subgroup.zpowers (x₀ : Ω)} => lift x.1) =
            (blkI β U W ⊓ Subgroup.centralizer {θ x₀}).subgroupOf H := by
          ext h
          rw [Subgroup.mem_inf, ModelGen.mem_fixFam, Subgroup.mem_subgroupOf,
            Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
          constructor
          · rintro ⟨hj, hfix⟩
            refine ⟨hj, ?_⟩
            have h1 := hfix ⟨⟨x₀, hB₁B x₀.2⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
            rw [hlift₁ _ x₀.2] at h1
            have h2 := congrArg Subtype.val h1
            rw [coe_conjOn] at h2
            exact (mul_inv_eq_iff_eq_mul.mp h2).symm
          · rintro ⟨hj, hc⟩
            refine ⟨hj, fun x => ?_⟩
            let T : Subgroup Ω := ((Subgroup.centralizer {(h : GL ι K)}).comap θ).map B₁.subtype
            have hDT : D ≤ T := by
              intro d hd
              refine ⟨⟨d, hDB hd⟩, ?_, rfl⟩
              rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
              exact ((hmemX h).mp (hIX hj) ⟨d, hDB hd⟩ hd).symm
            have hx₀T : (x₀ : Ω) ∈ T := by
              refine ⟨x₀, ?_, rfl⟩
              rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
              exact hc.symm
            obtain ⟨y, hy, hyx⟩ := sup_le hDT (Subgroup.zpowers_le.mpr hx₀T) x.2
            have hxB₁ : (x.1 : Ω) ∈ B₁ := hyx ▸ y.2
            rw [hlift₁ _ hxB₁]
            have hy' : (⟨x.1, hxB₁⟩ : ↥B₁) = y := Subtype.ext hyx.symm
            apply Subtype.ext
            rw [coe_conjOn, hy']
            rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hy
            rw [hy, mul_inv_cancel_right]
        rw [hEq]
        exact hlayer _ (inf_le_left.trans hIH) hlay
    ·
      obtain ⟨hbB, hbN, hBb, hbout, hact, hform⟩ := hF
      have hbD : b ∉ D := fun h => hbN (hDB h)
      refine key (D ⊔ Subgroup.zpowers b) (sup_le hDB' (Subgroup.zpowers_le.mpr hbB))
        le_sup_left (fun _ => ?_) (fun _ => ?_)
      · rw [card_sup_zpowers_of_not_mem hp hB hDB' hbB hbD, hD2]
        ring
      · have hp1 : 1 < p := hp.one_lt
        have hbout' : Subgroup.zpowers b ⊓ B₁ = ⊥ := hbout
        have hEq : I ⊓ ModelGen.fixFam (fun x : {x : ↥B // (x : Ω) ∈ D ⊔
            Subgroup.zpowers b} => lift x.1) =
            (blkI β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}).subgroupOf H := by
          ext h
          rw [Subgroup.mem_inf, ModelGen.mem_fixFam, Subgroup.mem_subgroupOf,
            Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          have hcen : (h : GL ι K) ∈ centGL {(ModelGen.semiMap A σ).toAddMonoidHom} ↔
              ModelGen.semiConj A σ h = h := by
            rw [mem_centGL]
            constructor
            · intro hc
              apply glEquiv.injective
              refine LinearEquiv.ext fun v => ?_
              obtain ⟨v', rfl⟩ := (ModelGen.semiMap A σ).surjective v
              rw [ModelGen.glEquiv_semiConj_apply]
              exact (hc _ rfl v').symm
            · intro hc s hs v
              rw [Set.mem_singleton_iff] at hs
              subst hs
              have := ModelGen.glEquiv_semiConj_apply A σ (h : GL ι K) v
              rw [hc] at this
              exact this
          have hθ1 : ∀ y : ↥B₁, (y : Ω) = 1 → θ y = 1 := fun y hy => by
            rw [show y = 1 from Subtype.ext hy, map_one]
          constructor
          · rintro ⟨hj, hfixall⟩
            refine ⟨hj, hcen.mpr ?_⟩
            have h1 := hfixall ⟨⟨b, hbB⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
            obtain ⟨-, y, k, hk0, hkp, hbk, hlx⟩ := hshape ⟨b, hbB⟩ hbN
            obtain ⟨hy1, hk1⟩ := eq_of_mul_pow_eq hp hB le_rfl hbB hbN hbout' y.2
              B₁.one_mem hkp hp1
              (show (y : Ω) * b ^ k = 1 * b ^ 1 by rw [one_mul, pow_one]; exact hbk.symm)
            have h2 := congrArg Subtype.val h1
            rw [hlx, hθ1 y hy1, hk1, pow_one] at h2
            simpa using h2
          · rintro ⟨hj, hc⟩
            have hsc : ModelGen.semiConj A σ h = h := hcen.mp hc
            have hsck : ∀ n : ℕ, (ModelGen.semiConj A σ ^ n) h = h := by
              intro n
              induction n with
              | zero => rfl
              | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hsc]
            refine ⟨hj, fun x => ?_⟩
            obtain ⟨d, hd, j, hjp, hxd⟩ := exists_mul_pow_of_mem_sup hp hB hDB' hbB x.2
            have hcommD : ∀ y : ↥B₁, (y : Ω) ∈ D → θ y * h = h * θ y := fun y hy =>
              (((hmemX h).mp (hIX hj)) y hy).symm
            by_cases hx : ((x.1 : ↥B) : Ω) ∈ B₁
            · obtain ⟨hxd', -⟩ := eq_of_mul_pow_eq hp hB le_rfl hbB hbN hbout' hx
                (hDB hd) hp.pos hjp (by simpa using hxd)
              rw [hlift₁ _ hx]
              apply Subtype.ext
              rw [coe_conjOn, hcommD ⟨_, hx⟩ (hxd' ▸ hd), mul_inv_cancel_right]
            · obtain ⟨-, y, k, -, hkp, hyk, hlx⟩ := hshape x.1 hx
              obtain ⟨hyd, -⟩ := eq_of_mul_pow_eq hp hB le_rfl hbB hbN hbout' y.2 (hDB hd)
                hkp hjp (hyk.symm.trans hxd)
              apply Subtype.ext
              rw [hlx, hsck, hcommD y (hyd ▸ hd), mul_inv_cancel_right]
        rw [hEq]
        exact hlayer _ (inf_le_left.trans hIH) hlay
  · exact key D hDB' le_rfl (fun h => absurd h hD2) (fun h => absurd h hD2)

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
