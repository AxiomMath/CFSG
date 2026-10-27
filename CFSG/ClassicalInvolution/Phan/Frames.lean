module

public import CFSG.ClassicalInvolution.Phan.Frames.BlockStab
public import CFSG.ClassicalInvolution.Phan.Parabolic.Defs
public import CFSG.ClassicalInvolution.Phan.TitsChamber
public import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem Module Matrix

variable {K : Type} [Field K] {σ : K ≃+* K}

variable (σ) in
@[expose] def frameSystem (n : ℕ) : ChamberSystem (Fin n) (Frame σ (n + 1)) where
  adj i c d := ∀ k : Fin (n + 1), k ≠ i.castSucc → k ≠ i.succ → c.line k = d.line k
  equivalence _ :=
    ⟨fun _ _ _ _ => rfl, fun h k h₁ h₂ => (h k h₁ h₂).symm,
      fun h h' k h₁ h₂ => (h k h₁ h₂).trans (h' k h₁ h₂)⟩

section System

variable {n : ℕ}

theorem frameSystem_adj {i : Fin n} {c d : Frame σ (n + 1)} :
    (frameSystem σ n).adj i c d ↔
      ∀ k : Fin (n + 1), k ≠ i.castSucc → k ≠ i.succ → c.line k = d.line k :=
  Iff.rfl

theorem castSucc_ne_succ (j : Fin n) : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ).ne

theorem adj_sup_eq (hσ : IsUnitaryInvolution σ) {i : Fin n} {c d : Frame σ (n + 1)}
    (h : (frameSystem σ n).adj i c d) :
    c.line i.castSucc ⊔ c.line i.succ = d.line i.castSucc ⊔ d.line i.succ := by
  rw [← Frame.spanAt_pair, ← Frame.spanAt_pair]
  refine c.spanAt_eq_of_agree hσ fun k hk => h k ?_ ?_
  · exact fun h' => hk (by simp [h'])
  · exact fun h' => hk (by simp [h'])

theorem line_mem_nsPts_of_adj (hσ : IsUnitaryInvolution σ) {i : Fin n} {c d : Frame σ (n + 1)}
    (h : (frameSystem σ n).adj i c d) :
    d.line i.castSucc ∈ nsPts σ (c.line i.castSucc ⊔ c.line i.succ) :=
  ⟨by rw [adj_sup_eq hσ h]; exact le_sup_left, d.finrank_line _, d.nondeg_line _⟩

theorem exists_adj_line_eq (hσ : IsUnitaryInvolution σ) (c : Frame σ (n + 1)) (i : Fin n)
    {x : Submodule K (Fin (n + 1) → K)} (hx : x ∈ nsPts σ (c.line i.castSucc ⊔ c.line i.succ)) :
    ∃ d : Frame σ (n + 1), (frameSystem σ n).adj i c d ∧ d.line i.castSucc = x := by
  have hP2 : finrank K ↥(c.line i.castSucc ⊔ c.line i.succ) = 2 := by
    rw [← Frame.spanAt_pair, c.finrank_spanAt, Finset.card_pair (castSucc_ne_succ i)]
  have hPnd : Nondeg σ (c.line i.castSucc ⊔ c.line i.succ) := by
    rw [← Frame.spanAt_pair]
    exact c.nondeg_spanAt hσ _
  obtain ⟨y, hy, hxy, -⟩ := exists_orth_complement_in_plane hσ hP2 hPnd hx
  refine ⟨c.replace hσ i.castSucc i.succ (castSucc_ne_succ i) x y hx hy hxy, ?_,
    Frame.replaceLine_left c _ _⟩
  intro k hk1 hk2
  exact (Frame.replaceLine_of_ne c hk1 hk2 _ _).symm

theorem frameSystem_adj_smul {i : Fin n} {c d : Frame σ (n + 1)} (g : SUid σ (n + 1))
    (h : (frameSystem σ n).adj i c d) : (frameSystem σ n).adj i (g • c) (g • d) :=
  fun k h₁ h₂ => by
    rw [Frame.smul_line, Frame.smul_line, h k h₁ h₂]

theorem frameSystem_adj_smul_iff {i : Fin n} {c d : Frame σ (n + 1)} (g : SUid σ (n + 1)) :
    (frameSystem σ n).adj i (g • c) (g • d) ↔ (frameSystem σ n).adj i c d :=
  ⟨fun h => by
    simpa using frameSystem_adj_smul g⁻¹ h, frameSystem_adj_smul g⟩

theorem frameSystem_isMorphism_smul (g : SUid σ (n + 1)) :
    IsMorphism (frameSystem σ n) (frameSystem σ n) (g • · : Frame σ (n + 1) → Frame σ (n + 1)) :=
  fun _ _ _ h => frameSystem_adj_smul g h

variable (σ n) in
@[expose] noncomputable def frameAut : SUid σ (n + 1) →* (frameSystem σ n).typeAut :=
  (MulAction.toPermHom (SUid σ (n + 1)) (Frame σ (n + 1))).codRestrict (frameSystem σ n).typeAut
    fun g _ _ _ => frameSystem_adj_smul_iff g

theorem frameAut_apply (g : SUid σ (n + 1)) (c : Frame σ (n + 1)) :
    ((frameAut σ n g : (frameSystem σ n).typeAut) : Equiv.Perm (Frame σ (n + 1))) c = g • c :=
  rfl

theorem exists_frameAut_apply_stdFrame (hσ : IsUnitaryInvolution σ) (c : Frame σ (n + 1)) :
    ∃ g : SUid σ (n + 1),
      ((frameAut σ n g : (frameSystem σ n).typeAut) : Equiv.Perm (Frame σ (n + 1)))
        (stdFrame σ (n + 1)) = c :=
  exists_smul_stdFrame hσ c

@[expose] def stabResidue (σ : K ≃+* K) (n : ℕ) (J : Set (Fin n)) : Subgroup (SUid σ (n + 1)) where
  carrier := {g | g • stdFrame σ (n + 1) ∈ (frameSystem σ n).residue J (stdFrame σ (n + 1))}
  one_mem' := by
    show (1 : SUid σ (n + 1)) • stdFrame σ (n + 1) ∈
      (frameSystem σ n).residue J (stdFrame σ (n + 1))
    rw [one_smul]
    exact self_mem_residue _ _
  mul_mem' {g h} hg hh := by
    have h1 : g • h • stdFrame σ (n + 1) ∈
        (frameSystem σ n).residue J (g • stdFrame σ (n + 1)) :=
      (frameSystem_isMorphism_smul g).mapsTo_residue J _ hh
    have h2 : (frameSystem σ n).residue J (g • stdFrame σ (n + 1)) =
        (frameSystem σ n).residue J (stdFrame σ (n + 1)) := residue_eq_of_mem hg
    show (g * h) • stdFrame σ (n + 1) ∈ (frameSystem σ n).residue J (stdFrame σ (n + 1))
    rw [mul_smul]
    rwa [h2] at h1
  inv_mem' {g} hg := by
    have h1 : g⁻¹ • g • stdFrame σ (n + 1) ∈
        (frameSystem σ n).residue J (g⁻¹ • stdFrame σ (n + 1)) :=
      (frameSystem_isMorphism_smul g⁻¹).mapsTo_residue J _ hg
    rw [inv_smul_smul] at h1
    exact mem_residue_symm h1

theorem mem_stabResidue {J : Set (Fin n)} {g : SUid σ (n + 1)} :
    g ∈ stabResidue σ n J ↔
      g • stdFrame σ (n + 1) ∈ (frameSystem σ n).residue J (stdFrame σ (n + 1)) :=
  Iff.rfl

theorem stabResidue_mono {J J' : Set (Fin n)} (h : J ⊆ J') :
    stabResidue σ n J ≤ stabResidue σ n J' :=
  fun _ hg => mem_stabResidue.2 (residue_mono h _ (mem_stabResidue.1 hg))

theorem torus_le_stabResidue (J : Set (Fin n)) :
    torus σ (n + 1) ≤ stabResidue σ n J := fun g hg => by
  rw [mem_stabResidue, (smul_stdFrame_eq_iff g).2 hg]
  exact self_mem_residue _ _

theorem exists_mem_torus_smul_eq {m : ℕ} (x : SUid σ m) (b : Fin m) (Bk : Set (Fin m))
    (hb : b ∈ Bk)
    (hx : ∀ k, k ∉ Bk → x • (Pi.single k 1 : Fin m → K) ∈ K ∙ (Pi.single k 1 : Fin m → K)) :
    ∃ t ∈ torus σ m, ∀ k, k ∉ Bk → x • (Pi.single k 1 : Fin m → K) =
      t • (Pi.single k 1 : Fin m → K) := by
  have h1 : ∀ k, ∃ u : normOne σ, k ∉ Bk → x • (Pi.single k 1 : Fin m → K) =
      ((u : normOne σ) : Kˣ).val • (Pi.single k 1 : Fin m → K) := by
    intro k
    by_cases hk : k ∈ Bk
    · exact ⟨1, fun h => absurd hk h⟩
    · obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp (hx k hk)
      have hnorm : σ u * u = 1 := by
        have := herm_smul_smul σ x (Pi.single k 1) (Pi.single k 1)
        rw [← hu, herm_smul_left, herm_smul_right, herm_single_left] at this
        simpa using this
      have hu0 : u ≠ 0 := fun h => by
        rw [h, map_zero, zero_mul] at hnorm
        exact zero_ne_one hnorm
      exact ⟨⟨Units.mk0 u hu0, hnorm⟩, fun _ => hu.symm⟩
  choose d₀ hd₀ using h1
  set δ : normOne σ := ∏ k, d₀ k with hδ
  set d : Fin m → normOne σ := d₀ * Pi.mulSingle b δ⁻¹ with hd
  have hdet : d ∈ detKer σ m := by
    rw [mem_detKer]
    simp only [hd, Pi.mul_apply, Finset.prod_mul_distrib]
    rw [← hδ]
    have : ∏ k, (Pi.mulSingle b δ⁻¹ : Fin m → normOne σ) k = δ⁻¹ := by
      simp only [Pi.mulSingle_apply]
      rw [Finset.prod_ite_eq']
      simp
    rw [this, mul_inv_cancel]
  refine ⟨diagSU σ d hdet, diagSU_mem_torus d hdet, fun k hk => ?_⟩
  rw [smul_single_diagSU, hd₀ k hk]
  have hkb : k ≠ b := fun h => hk (h ▸ hb)
  simp [hd, hkb]

theorem stabilizer_stdFrame {m : ℕ} :
    MulAction.stabilizer (SUid σ m) (stdFrame σ m) = torus σ m :=
  Subgroup.ext fun g => smul_stdFrame_eq_iff g

noncomputable def frameEquivQuotient (hσ : IsUnitaryInvolution σ) :
    SUid σ (n + 1) ⧸ torus σ (n + 1) ≃ Frame σ (n + 1) :=
  (Subgroup.quotientEquivOfEq stabilizer_stdFrame.symm).trans
    (Equiv.ofBijective (MulAction.ofQuotientStabilizer (SUid σ (n + 1)) (stdFrame σ (n + 1)))
      (show Function.Bijective _ from
        ⟨MulAction.injective_ofQuotientStabilizer _ _, fun c => by
          obtain ⟨g, rfl⟩ := exists_smul_stdFrame hσ c
          exact ⟨(g : SUid σ (n + 1) ⧸ _), MulAction.ofQuotientStabilizer_mk _ _ _⟩⟩))

theorem frameEquivQuotient_mk (hσ : IsUnitaryInvolution σ) (g : SUid σ (n + 1)) :
    frameEquivQuotient hσ (g : SUid σ (n + 1) ⧸ torus σ (n + 1)) = g • stdFrame σ (n + 1) := by
  have h : (Subgroup.quotientEquivOfEq (stabilizer_stdFrame (σ := σ) (m := n + 1)).symm)
      (g : SUid σ (n + 1) ⧸ torus σ (n + 1)) =
      (g : SUid σ (n + 1) ⧸ MulAction.stabilizer (SUid σ (n + 1)) (stdFrame σ (n + 1))) :=
    Subgroup.quotientEquivOfEq_mk _ _
  unfold frameEquivQuotient
  rw [Equiv.trans_apply, h, Equiv.ofBijective_apply]
  exact MulAction.ofQuotientStabilizer_mk _ _ _

end System

section Panels

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem adj_blockEmb2_smul_stdFrame (i : Fin n) (A : Su K p f 2) :
    (frameSystem (unitaryInvolution K p f) n).adj i (stdFrame _ (n + 1))
      (blockEmb2 K p f n i A • stdFrame _ (n + 1)) := by
  intro k h₁ h₂
  have hk : ¬ ((i : ℕ) ≤ k.val ∧ k.val < (i : ℕ) + 2) := by
    rintro ⟨ha, hb⟩
    have h1' : k.val ≠ i.val := fun h => h₁ (Fin.ext (by simpa using h))
    have h2' : k.val ≠ i.val + 1 := fun h => h₂ (Fin.ext (by simpa using h))
    omega
  rw [Frame.smul_line, stdFrame_line, smul_span_singleton]
  exact congrArg (fun v => K ∙ v) (blockEmb_smul_single_of_not_mem (by omega) A hk).symm

theorem blockEmb2_le_stabResidue {J : Set (Fin n)} {i : Fin n} (hi : i ∈ J) :
    (blockEmb2 K p f n i).range ≤ stabResidue (unitaryInvolution K p f) n J := by
  rintro _ ⟨A, rfl⟩
  rw [mem_stabResidue]
  refine residue_mono (Set.singleton_subset_iff.2 hi) _ ?_
  rw [mem_residue_singleton]
  exact adj_blockEmb2_smul_stdFrame i A

theorem adj_smul_stdFrame_iff (i : Fin n) (x : Su K p f (n + 1)) :
    (frameSystem (unitaryInvolution K p f) n).adj i (x • stdFrame _ (n + 1)) (stdFrame _ (n + 1)) ↔
      x ∈ torus (unitaryInvolution K p f) (n + 1) ⊔ (blockEmb2 K p f n i).range := by
  constructor
  · intro h
    have hx : ∀ k, k ∉ ({i.castSucc, i.succ} : Set (Fin (n + 1))) →
        x • (Pi.single k 1 : Fin (n + 1) → K) ∈ K ∙ (Pi.single k 1 : Fin (n + 1) → K) := by
      intro k hk
      have hk1 : k ≠ i.castSucc := fun h' => hk (Or.inl h')
      have hk2 : k ≠ i.succ := fun h' => hk (Or.inr h')
      have := h k hk1 hk2
      rw [Frame.smul_line, stdFrame_line, smul_span_singleton] at this
      exact this ▸ Submodule.mem_span_singleton_self _
    obtain ⟨t, ht, hxt⟩ := exists_mem_torus_smul_eq x i.castSucc {i.castSucc, i.succ}
      (Or.inl rfl) hx
    have hu : t⁻¹ * x ∈ (blockEmb2 K p f n i).range := by
      refine (mem_range_blockEmb_iff (by omega) _).2 fun l hl => ?_
      have hl1 : l ≠ i.castSucc := fun h' => hl ⟨by simp [h'], by simp [h']⟩
      have hl2 : l ≠ i.succ := fun h' => hl ⟨by simp [h'], by simp [h']⟩
      have hl' : l ∉ ({i.castSucc, i.succ} : Set (Fin (n + 1))) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hl1, hl2⟩
      rw [mul_smul, hxt l hl', inv_smul_smul]
    have : x = t * (t⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ht hu
  · intro hx
    have h1 : x ∈ (stabResidue (unitaryInvolution K p f) n {i}) := by
      have : torus (unitaryInvolution K p f) (n + 1) ⊔ (blockEmb2 K p f n i).range ≤
          stabResidue (unitaryInvolution K p f) n {i} :=
        sup_le (torus_le_stabResidue _) (blockEmb2_le_stabResidue rfl)
      exact this hx
    rw [mem_stabResidue, mem_residue_singleton] at h1
    exact adj_symm h1

theorem adj_smul_stdFrame_smul_iff (i : Fin n) (g h : Su K p f (n + 1)) :
    (frameSystem (unitaryInvolution K p f) n).adj i (g • stdFrame _ (n + 1))
        (h • stdFrame _ (n + 1)) ↔
      g⁻¹ * h ∈ torus (unitaryInvolution K p f) (n + 1) ⊔ (blockEmb2 K p f n i).range := by
  rw [← adj_smul_stdFrame_iff, ← frameSystem_adj_smul_iff g⁻¹, mul_smul, inv_smul_smul]
  exact ⟨adj_symm, adj_symm⟩

end Panels

section Parabolic

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem parabolic_le_stabResidue (J : Set (Fin n)) :
    parabolic K p f n J ≤ stabResidue (unitaryInvolution K p f) n J :=
  sup_le (torus_le_stabResidue J) (iSup₂_le fun _ hj => blockEmb2_le_stabResidue hj)

theorem mem_parabolic_of_isGallery (hK : Nat.card K = (p ^ f) ^ 2) (J : Set (Fin n)) :
    ∀ (γ : List (Fin n × Frame (unitaryInvolution K p f) (n + 1))) (x₀ : Su K p f (n + 1)),
      x₀ ∈ parabolic K p f n J →
      (frameSystem (unitaryInvolution K p f) n).IsGallery
        (x₀ • stdFrame (unitaryInvolution K p f) (n + 1)) γ →
      (∀ i ∈ galleryType γ, i ∈ J) →
      ∀ x : Su K p f (n + 1), x • stdFrame (unitaryInvolution K p f) (n + 1) =
        galleryEnd (x₀ • stdFrame (unitaryInvolution K p f) (n + 1)) γ →
          x ∈ parabolic K p f n J := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  intro γ
  induction γ with
  | nil =>
    intro x₀ hx₀ _ _ x hx
    have h1 : (x₀⁻¹ * x) • stdFrame (unitaryInvolution K p f) (n + 1) =
        stdFrame (unitaryInvolution K p f) (n + 1) := by
      rw [mul_smul, hx]
      simp
    have h2 := (smul_stdFrame_eq_iff _).1 h1
    have := (parabolic K p f n J).mul_mem hx₀ (torus_le_parabolic J h2)
    simpa using this
  | cons q γ ih =>
    intro x₀ hx₀ hγ hJ x hx
    obtain ⟨hq1, hq2⟩ := hγ
    obtain ⟨x₁, hx₁⟩ := exists_smul_stdFrame hσ q.2
    have hqi : q.1 ∈ J := hJ q.1 (by simp)
    have hadj : (frameSystem (unitaryInvolution K p f) n).adj q.1
        (stdFrame (unitaryInvolution K p f) (n + 1))
        ((x₀⁻¹ * x₁) • stdFrame (unitaryInvolution K p f) (n + 1)) := by
      have h1 := frameSystem_adj_smul x₀⁻¹ hq1
      rw [← hx₁, inv_smul_smul, ← mul_smul] at h1
      exact h1
    have hmem := (adj_smul_stdFrame_iff q.1 (x₀⁻¹ * x₁)).1 (adj_symm hadj)
    have hmem' : x₀⁻¹ * x₁ ∈ parabolic K p f n J :=
      sup_le (torus_le_parabolic J) (range_blockEmb2_le_parabolic hqi) hmem
    have hx₁P : x₁ ∈ parabolic K p f n J := by
      have := (parabolic K p f n J).mul_mem hx₀ hmem'
      rwa [mul_inv_cancel_left] at this
    refine ih x₁ hx₁P (by rw [hx₁]; exact hq2) (fun i hi => hJ i (by simp [hi])) x ?_
    rw [galleryEnd_cons, ← hx₁] at hx
    exact hx

theorem mem_parabolic_iff (hK : Nat.card K = (p ^ f) ^ 2) (J : Set (Fin n))
    (x : Su K p f (n + 1)) :
    x ∈ parabolic K p f n J ↔
      x • stdFrame (unitaryInvolution K p f) (n + 1) ∈
        (frameSystem (unitaryInvolution K p f) n).residue J
          (stdFrame (unitaryInvolution K p f) (n + 1)) := by
  refine ⟨fun h => parabolic_le_stabResidue J h, fun h => ?_⟩
  obtain ⟨γ, hγ, hJ, hend⟩ := h
  have := mem_parabolic_of_isGallery hK J γ 1 (one_mem _) (by rwa [one_smul]) hJ x
    (by rw [one_smul]; exact hend.symm)
  exact this

theorem parabolic_eq_stabResidue (hK : Nat.card K = (p ^ f) ^ 2) (J : Set (Fin n)) :
    parabolic K p f n J = stabResidue (unitaryInvolution K p f) n J :=
  le_antisymm (parabolic_le_stabResidue J) fun x hx => (mem_parabolic_iff hK J x).2 hx

theorem frames_universal_completion (hK : Nat.card K = (p ^ f) ^ 2)
    (hconn : (frameSystem (unitaryInvolution K p f) n).Connected)
    (hS : (frameSystem (unitaryInvolution K p f) n).SimplyTwoConnected)
    {Y : Type*} [Group Y] (φ : ∀ J : Set (Fin n), J.encard ≤ 2 → parabolic K p f n J →* Y)
    (hφ : ∀ (J J' : Set (Fin n)) (hJ : J.encard ≤ 2) (hJ' : J'.encard ≤ 2), J' ⊆ J →
      ∀ (g : Su K p f (n + 1)) (hgJ' : g ∈ parabolic K p f n J') (hgJ : g ∈ parabolic K p f n J),
        φ J' hJ' ⟨g, hgJ'⟩ = φ J hJ ⟨g, hgJ⟩) :
    ∃! ψ : Su K p f (n + 1) →* Y, ∀ (J : Set (Fin n)) (hJ : J.encard ≤ 2)
      (g : parabolic K p f n J), ψ g = φ J hJ g :=
  tits_chamber_universal_completion (frameSystem (unitaryInvolution K p f) n) hconn hS
    (frameAut (unitaryInvolution K p f) n) (stdFrame (unitaryInvolution K p f) (n + 1))
    (fun c => exists_frameAut_apply_stdFrame (isUnitaryInvolution_unitaryInvolution hK) c)
    (parabolic K p f n) (fun J _ g => mem_parabolic_iff hK J g) φ hφ

end Parabolic

end CFSG.ClassicalInvolution.Phan
