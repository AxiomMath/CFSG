module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.ThetaComm

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def qRes (d : X) : Subgroup X :=
  inSubgroup perfectResidual (Subgroup.centralizer ({d} : Set X))

omit [Finite X] in
theorem qRes_le (d : X) : qRes d ≤ Subgroup.centralizer ({d} : Set X) :=
  Subgroup.map_subtype_le _

theorem qRes_commutator (d : X) : ⁅qRes d, qRes d⁆ = qRes d := by
  have : Group.IsPerfect ↥(perfectResidual ↥(Subgroup.centralizer ({d} : Set X))) :=
    CFSG.Wreathed.PrimewisePerfectLift.perfectResidual_isPerfect
  have h := Subgroup.commutator_eq_self
    (H := perfectResidual ↥(Subgroup.centralizer ({d} : Set X)))
  unfold qRes inSubgroup
  rw [← Subgroup.map_commutator, h]

omit [Finite X] in
theorem map_qRes (σ : MulAut X) {d : X} (hσ : σ d = d) :
    (qRes d).map σ.toMonoidHom = qRes d := by
  unfold qRes
  rw [map_inSubgroup_perfectResidual σ, map_centralizer_singleton, hσ]

omit [Finite X] in
theorem fixes_of_perfect (σ : MulAut X) (Q : Subgroup X) (hQ : ⁅Q, Q⁆ = Q)
    (hσQ : ∀ q ∈ Q, σ q ∈ Q)
    (hz : ∀ q ∈ Q, ∀ y ∈ Q, (σ q * q⁻¹) * y = y * (σ q * q⁻¹)) :
    ∀ q ∈ Q, σ q = q := by
  have hcomm : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, σ ⁅q₁, q₂⁆ = ⁅q₁, q₂⁆ := by
    intro q₁ hq₁ q₂ hq₂
    set z₁ := σ q₁ * q₁⁻¹ with hz₁
    set z₂ := σ q₂ * q₂⁻¹ with hz₂
    have e₁ : σ q₁ = z₁ * q₁ := by rw [hz₁]; group
    have e₂ : σ q₂ = z₂ * q₂ := by rw [hz₂]; group
    have z₁q₁ : z₁ * q₁ = q₁ * z₁ := hz q₁ hq₁ q₁ hq₁
    have z₁q₂ : z₁ * q₂ = q₂ * z₁ := hz q₁ hq₁ q₂ hq₂
    have z₂q₁ : z₂ * q₁ = q₁ * z₂ := hz q₂ hq₂ q₁ hq₁
    have z₂q₂ : z₂ * q₂ = q₂ * z₂ := hz q₂ hq₂ q₂ hq₂
    have z₁z₂ : z₁ * z₂ = z₂ * z₁ := hz q₁ hq₁ z₂ (by
      rw [hz₂]; exact Subgroup.mul_mem _ (hσQ q₂ hq₂) (Subgroup.inv_mem _ hq₂))
    have c₁ : Commute z₁ q₁ := z₁q₁
    have c₂ : Commute z₁ q₂ := z₁q₂
    have c₃ : Commute z₂ q₁ := z₂q₁
    have c₄ : Commute z₂ q₂ := z₂q₂
    have c₅ : Commute z₁ z₂ := z₁z₂
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, e₁, e₂]
    have h1 : z₁ * q₁ * (z₂ * q₂) * (z₁ * q₁)⁻¹ * (z₂ * q₂)⁻¹ =
        z₁ * (q₁ * z₂ * q₂ * q₁⁻¹) * z₁⁻¹ * q₂⁻¹ * z₂⁻¹ := by group
    rw [h1, ← c₃.eq, show z₂ * q₁ * q₂ * q₁⁻¹ = z₂ * (q₁ * q₂ * q₁⁻¹) by group]
    have h2 : z₁ * (z₂ * (q₁ * q₂ * q₁⁻¹)) * z₁⁻¹ * q₂⁻¹ * z₂⁻¹ =
        (z₁ * z₂) * (q₁ * q₂ * q₁⁻¹) * z₁⁻¹ * q₂⁻¹ * z₂⁻¹ := by group
    rw [h2, c₅.eq]
    have h3 : z₂ * z₁ * (q₁ * q₂ * q₁⁻¹) * z₁⁻¹ * q₂⁻¹ * z₂⁻¹ =
        z₂ * (z₁ * q₁ * q₂ * q₁⁻¹ * z₁⁻¹) * q₂⁻¹ * z₂⁻¹ := by group
    rw [h3]
    have h4 : z₁ * q₁ * q₂ * q₁⁻¹ * z₁⁻¹ = q₁ * q₂ * q₁⁻¹ := by
      have := c₁.eq
      calc z₁ * q₁ * q₂ * q₁⁻¹ * z₁⁻¹ = (z₁ * q₁) * q₂ * q₁⁻¹ * z₁⁻¹ := by group
        _ = (q₁ * z₁) * q₂ * q₁⁻¹ * z₁⁻¹ := by rw [this]
        _ = q₁ * (z₁ * q₂) * q₁⁻¹ * z₁⁻¹ := by group
        _ = q₁ * (q₂ * z₁) * q₁⁻¹ * z₁⁻¹ := by rw [c₂.eq]
        _ = q₁ * q₂ * (z₁ * q₁⁻¹) * z₁⁻¹ := by group
        _ = q₁ * q₂ * (q₁⁻¹ * z₁) * z₁⁻¹ := by rw [c₁.inv_right.eq]
        _ = q₁ * q₂ * q₁⁻¹ := by group
    rw [h4]
    have h5 : z₂ * (q₁ * q₂ * q₁⁻¹) * q₂⁻¹ * z₂⁻¹ = q₁ * q₂ * q₁⁻¹ * q₂⁻¹ := by
      calc z₂ * (q₁ * q₂ * q₁⁻¹) * q₂⁻¹ * z₂⁻¹ = (z₂ * q₁) * q₂ * q₁⁻¹ * q₂⁻¹ * z₂⁻¹ := by group
        _ = (q₁ * z₂) * q₂ * q₁⁻¹ * q₂⁻¹ * z₂⁻¹ := by rw [c₃.eq]
        _ = q₁ * (z₂ * q₂) * q₁⁻¹ * q₂⁻¹ * z₂⁻¹ := by group
        _ = q₁ * (q₂ * z₂) * q₁⁻¹ * q₂⁻¹ * z₂⁻¹ := by rw [c₄.eq]
        _ = q₁ * q₂ * (z₂ * q₁⁻¹) * q₂⁻¹ * z₂⁻¹ := by group
        _ = q₁ * q₂ * (q₁⁻¹ * z₂) * q₂⁻¹ * z₂⁻¹ := by rw [c₃.inv_right.eq]
        _ = q₁ * q₂ * q₁⁻¹ * (z₂ * q₂⁻¹) * z₂⁻¹ := by group
        _ = q₁ * q₂ * q₁⁻¹ * (q₂⁻¹ * z₂) * z₂⁻¹ := by rw [c₄.inv_right.eq]
        _ = q₁ * q₂ * q₁⁻¹ * q₂⁻¹ := by group
    rw [h5]
  have hle : Q ≤ (σ.toMonoidHom.eqLocus (MonoidHom.id X)) := by
    conv_lhs => rw [← hQ]
    rw [Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    exact hcomm q₁ hq₁ q₂ hq₂
  intro q hq
  exact hle hq

theorem fixes_qRes (hZ : Subgroup.center X = ⊥) {Y : Subgroup (MulAut X)}
    (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) {d : X} {b : Y}
    (hb : (b : MulAut X) = MulAut.conj d)
    (H1 : ∀ x ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set X)) ⊓
        qRes d, ∀ y ∈ qRes d, x * y = y * x)
    {n : Y} (hn : n ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y))) :
    ∀ q ∈ qRes d, (n : MulAut X) q = q := by
  set σ : MulAut X := (n : MulAut X) with hσdef
  have hσd : σ d = d := fixes_of_mem_theta hZ hb hn
  have hσQ : ∀ q ∈ qRes d, σ q ∈ qRes d := by
    intro q hq
    rw [← map_qRes σ hσd]
    exact ⟨q, hq, rfl⟩
  have hz : ∀ q ∈ qRes d, ∀ y ∈ qRes d, (σ q * q⁻¹) * y = y * (σ q * q⁻¹) := by
    intro q hq y hy
    have hmem : σ q * q⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({d} : Set X)) ⊓ qRes d := by
      refine ⟨mem_theta_of_mem_theta hZ hY hb hn (qRes_le d hq), ?_⟩
      exact Subgroup.mul_mem _ (hσQ q hq) (Subgroup.inv_mem _ hq)
    exact H1 _ hmem y hy
  exact fixes_of_perfect σ (qRes d) (qRes_commutator d) hσQ hz

theorem thetaJ_eq_bot_of_local (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (H1 : ∀ b ∈ D, b ≠ 1 → ∀ x ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b, ∀ y ∈ qRes b, x * y = y * x)
    (H2 : ∀ b ∈ D, b ≠ 1 → D ≤ Subgroup.zpowers b ⊔ qRes b) {Y : Subgroup (MulAut X)}
    (hY : (MulAut.conj : X →* MulAut X).range ≤ Y) :
    thetaJ 3 ((D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y) = ⊥ := by
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
  obtain ⟨b₀, hb₀, hbb₀⟩ := Subgroup.mem_subgroupOf.mp hb
  have hb₀1 : b₀ ≠ 1 := by
    rintro rfl
    apply hb1
    apply Subtype.ext
    rw [← hbb₀]
    simp
  rw [Subgroup.commutator_le]
  intro q hq' d hd
  obtain ⟨d₀, hd₀, hdd₀⟩ := Subgroup.mem_subgroupOf.mp hd
  have hqb : (q : MulAut X) b₀ = b₀ := fixes_of_mem_theta hZ hbb₀.symm hq'
  have hqr : ∀ r ∈ qRes b₀, (q : MulAut X) r = r :=
    fixes_qRes hZ hY hbb₀.symm (H1 b₀ hb₀ hb₀1) hq'
  have hqd : (q : MulAut X) d₀ = d₀ := by
    have hle : Subgroup.zpowers b₀ ⊔ qRes b₀ ≤
        (q : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact hqb
      · intro r hr
        exact hqr r hr
    exact hle (H2 b₀ hb₀ hb₀1 hd₀)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hdd₀]
  have h1 := mulAut_mul_conj_mul_inv (q : MulAut X) d₀
  rw [hqd] at h1
  calc (q : MulAut X) * MulAut.conj d₀ =
      (q : MulAut X) * MulAut.conj d₀ * (q : MulAut X)⁻¹ * (q : MulAut X) := by group
    _ = MulAut.conj d₀ * (q : MulAut X) := by rw [h1]

theorem alphaVanishes_of_local (hZ : Subgroup.center X = ⊥) {D : Subgroup X}
    (H1 : ∀ b ∈ D, b ≠ 1 → ∀ x ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b, ∀ y ∈ qRes b, x * y = y * x)
    (H2 : ∀ b ∈ D, b ≠ 1 → D ≤ Subgroup.zpowers b ⊔ qRes b)
    (H3 : (⊤ : Subgroup X) ≤ Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b}) :
    AlphaVanishes X D := by
  intro Y hY
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  have hJ : thetaJ 3 B = ⊥ := thetaJ_eq_bot_of_local hZ H1 H2 hY
  have hT : thetaT 3 B = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have htfix : ∀ x : X, (∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b) → (t : MulAut X) x = x := by
      rintro x ⟨b₀, hb₀, hb₀1, hx⟩
      have hbY : MulAut.conj b₀ ∈ Y := hY ⟨b₀, rfl⟩
      set b : Y := ⟨MulAut.conj b₀, hbY⟩
      have hbB : b ∈ B := Subgroup.mem_subgroupOf.mpr ⟨b₀, hb₀, rfl⟩
      have hb1 : b ≠ 1 := by
        intro h1
        apply hb₀1
        apply hinj
        rw [map_one]
        exact congrArg Subtype.val h1
      have htb : t ∈
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)) := by
        have h1 := Subgroup.mem_iInf.mp ht b
        have h2 := Subgroup.mem_iInf.mp h1 hbB
        exact Subgroup.mem_iInf.mp h2 hb1
      exact fixes_qRes hZ hY (b := b) (d := b₀) rfl (H1 b₀ hb₀ hb₀1) htb x hx
    have hle : Subgroup.closure {x : X | ∃ b ∈ D, b ≠ 1 ∧ x ∈ qRes b} ≤
        (t : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact htfix x hx
    apply Subtype.ext
    ext x
    exact hle (H3 (Subgroup.mem_top x))
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
