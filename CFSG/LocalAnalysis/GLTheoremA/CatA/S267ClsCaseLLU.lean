module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsBlockDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLUMain
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open scoped IsMulCommutative

section Count

private theorem card_comap_eq_mul {G N : Type*} [Group G] [Finite G] [Group N] (f : G →* N)
    (E : Subgroup N) : Nat.card (E.comap f) = Nat.card f.ker * Nat.card ↥(f.range ⊓ E) := by
  let g : ↥(E.comap f) →* N := f.comp (E.comap f).subtype
  have hk : g.ker = f.ker.subgroupOf (E.comap f) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, g, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype]
  have hr : g.range = f.range ⊓ E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
  have hle : f.ker ≤ E.comap f := Subgroup.ker_le_comap f E
  have h := Subgroup.card_ker_mul_card_range g
  rw [hk, hr, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  exact h.symm

theorem card_inf_le_of_index {G₀ : Type*} [CommGroup G₀] [Finite G₀] {p : ℕ} (hp : p.Prime)
    {Sc A' G H₀ : Subgroup G₀} (hH₀ : H₀.index = p) (hf : Sc ⊓ H₀ ≤ G)
    (hG : Nat.card G = p ^ 2) :
    Nat.card ↥(Sc ⊓ A') ≤ p ^ 3 ∧ ((∃ g ∈ G, g ∉ A') → Nat.card ↥(Sc ⊓ A') ≤ p ^ 2) := by
  have hrel : H₀.relIndex (Sc ⊓ A') ≤ p := by
    have h := Subgroup.relIndex_dvd_index_of_normal H₀ (Sc ⊓ A')
    rw [hH₀] at h
    exact Nat.le_of_dvd hp.pos h
  have hmul := Subgroup.relIndex_mul_card H₀ (Sc ⊓ A')
  have hsub : H₀ ⊓ (Sc ⊓ A') ≤ A' ⊓ G := fun x hx => ⟨hx.2.2, hf ⟨hx.2.1, hx.1⟩⟩
  have hc1 : Nat.card ↥(H₀ ⊓ (Sc ⊓ A')) ≤ Nat.card ↥(A' ⊓ G) := Subgroup.card_le_of_le hsub
  have hdvd : Nat.card ↥(A' ⊓ G) ∣ p ^ 2 := hG ▸ Subgroup.card_dvd_of_le inf_le_right
  have hle2 : Nat.card ↥(A' ⊓ G) ≤ p ^ 2 := Nat.le_of_dvd (pow_pos hp.pos 2) hdvd
  refine ⟨?_, fun ⟨g, hgG, hgA⟩ => ?_⟩
  · calc Nat.card ↥(Sc ⊓ A') = H₀.relIndex (Sc ⊓ A') * Nat.card ↥(H₀ ⊓ (Sc ⊓ A')) := hmul.symm
      _ ≤ p * p ^ 2 := Nat.mul_le_mul hrel (hc1.trans hle2)
      _ = p ^ 3 := by ring
  · obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have hk2' : k = 2 := by omega
      have heq : A' ⊓ G = G :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hG, hkc, hk2'])
      have hgAG : g ∈ A' ⊓ G := by rw [heq]; exact hgG
      exact hgA hgAG.1
    have hlep : Nat.card ↥(A' ⊓ G) ≤ p := by
      rw [hkc]
      exact (Nat.pow_le_pow_right hp.pos hk1).trans (pow_one p).le
    calc Nat.card ↥(Sc ⊓ A') = H₀.relIndex (Sc ⊓ A') * Nat.card ↥(H₀ ⊓ (Sc ⊓ A')) := hmul.symm
      _ ≤ p * p := Nat.mul_le_mul hrel (hc1.trans hlep)
      _ = p ^ 2 := by ring

end Count

section Scalar

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
variable {p : ℕ} {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]

theorem mem_of_scalarOn_of_mem (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)
    [DecidableEq (Hyperplane ↥Aε p)] {I : Finset (Hyperplane ↥Aε p)} {H₀ : Hyperplane ↥Aε p}
    (hH₀I : H₀ ∉ I) (hH₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥) {a : ↥Aε}
    (ha : (a : GL ι K) ∈ scalarOnGL (wtU Aε I)) (haH₀ : a ∈ H₀.1) {H : Hyperplane ↥Aε p}
    (hHI : H ∉ I) (hH : weightSpace (glRep Aε) H.1 ≠ ⊥) : a ∈ H.1 := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH₀
  have h1 : glRep Aε a v = v := apply_eq_of_mem_weightSpace (glRep Aε) haH₀ hv
  rw [glRep_apply_eq_glEquiv, hc v (weightSpace_le_ker_projI hp hA hpK hH₀I hv)] at h1
  have hc1 : c = 1 := by
    have h2 : (c - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  by_contra haH
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
  apply hw0
  refine eq_zero_of_mem_weightSpace_of_fixed (glRep Aε) hp hA hpK haH hw ?_
  rw [glRep_apply_eq_glEquiv, hc w (weightSpace_le_ker_projI hp hA hpK hHI hw), hc1, one_smul]

end Scalar

private theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    {g : G} (hg : ∀ k ∈ H, g * k * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hg h, fun hh => ?_⟩
  let f : H → H := fun k => ⟨g * k * g⁻¹, hg k k.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hh⟩
  have h1 := congrArg Subtype.val hk
  simp only [f, mul_left_inj, mul_right_inj] at h1
  exact h1 ▸ k.2

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_caseL_lu {n : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] {τ : K →+* K}
    (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B) (h4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0)
    {H : Subgroup (GL (Fin n) K)} {β : (Fin n → K) →ₗ[K] (Fin n → K) →ₛₗ[τ] K}
    (hHβ : H ≤ isomGL β) (hβ : β = 0 ∨ β.SeparatingLeft)
    (hdetH : ∀ g ∈ isomGL β, (g : Matrix (Fin n) (Fin n) K).det = 1 → g ∈ H)
    (hsc : ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL β)
    {Qbig : Prop} (hQ : Qbig)
    (hblk : ∀ U W : Submodule K (Fin n → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ Qbig)) →
      blkI β U W ≤ H ∧ CFSG.Open.IsQuasisimple ↥(blkI β U W) ∧
      (∀ x ∈ blkSub β U W, orderOf x = p → p ∣ Nat.card ↥(blkI β U W)) ∧
      (∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
        (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j))
    (hD1 : ∀ (Aε : Subgroup (GL (Fin n) K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
      Aε ≤ isomGL β → IsMaxElem β (glRep Aε) p ∅ →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧
        Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL β) →
      ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
        Module.finrank K (weightSpace (glRep Aε) H'.1) = 1)
    (φ : ↥H →* Ω) (hφS : φ.range = S) (hφk : φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H)
    {B₁ : Subgroup Ω} (θ : ↥B₁ →* GL (Fin n) K) (hB₁B : B₁ ≤ B)
    (hB₀B₁ : B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁)
    (hθβ : θ.range ≤ isomGL β) (hθel : IsElemAbelian p θ.range)
    (hθZ : θ.range ⊓ StatedScalars (Fin n) K = ⊥)
    (hθ1 : ∀ x : ↥B₁, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω))
    (hθact : ∀ (x : ↥B₁) (k : ↥H), ∃ k' : ↥H,
      (k' : GL (Fin n) K) = θ x * k * (θ x)⁻¹ ∧ φ k' = x * φ k * x⁻¹)
    (hθc : p ^ (n - 2) ≤ Nat.card θ.range)
    (hsplit : B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
      Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
        ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ ∧
        ∀ x : ↥B₁, ModelGen.semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) :
    S267ConcA p S B := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c₀, hc₀1, hc₀p, hc₀β⟩ := hsc
  have hc₀1' : (c₀ : K) ≠ 1 := fun h => hc₀1 (Units.ext h)
  have hζc : ∀ g : GL (Fin n) K, Matrix.GeneralLinearGroup.scalar (Fin n) c₀ * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin n) c₀ := fun g => scalarGL_mul_comm c₀ g
  have hζp : Matrix.GeneralLinearGroup.scalar (Fin n) c₀ ^ p = 1 := by
    rw [← map_pow, hc₀p, map_one]
  have hZel : IsElemAbelian p (Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar (Fin n) c₀)) := by
    rw [Subgroup.zpowers_eq_closure]
    exact IsElemAbelian.closure_of_commute
      (fun a ha b hb => by rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])
      (fun a ha => by rw [Set.mem_singleton_iff.mp ha]; exact hζp)
  have hZcomm : ∀ a ∈ Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar (Fin n) c₀),
      ∀ g : GL (Fin n) K, a * g = g * a := by
    intro a ha g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hζc g) k).eq
  have hAel : IsElemAbelian p (θ.range ⊔ Subgroup.zpowers
      (Matrix.GeneralLinearGroup.scalar (Fin n) c₀)) :=
    hθel.sup_of_commute hZel fun a _ b hb => (hZcomm b hb a).symm
  have hAX : θ.range ⊔ Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar (Fin n) c₀) ≤
      isomGL β ⊓ centGL ∅ :=
    le_inf (sup_le hθβ (Subgroup.zpowers_le.mpr hc₀β)) fun g _ => by
      rw [mem_centGL]
      intro s hs
      exact absurd hs (Set.notMem_empty s)
  obtain ⟨Aε, hAAε, hAε, hAεX, hmax⟩ := exists_maximal_elemAbelian hAel hAX
  haveI : IsMulCommutative ↥Aε := hAε.1
  have hA : ∀ a : ↥Aε, a ^ p = 1 := fun a => Subtype.ext (by simpa using hAε.2 a a.2)
  have hAεβ : Aε ≤ isomGL β := hAεX.trans inf_le_left
  have hmaxE : IsMaxElem β (glRep Aε) p ∅ :=
    isMaxElem_of_maximal β ∅ Aε hAε hAεβ (hAεX.trans inf_le_right)
      fun A' h1 h2 h3 h4 => hmax A' h1 h2 (le_inf h3 h4)
  have h𝒮 : ∀ s ∈ (∅ : Set ((Fin n → K) →+ (Fin n → K))), ∀ a v,
      s (glRep Aε a v) = glRep Aε a (s v) := fun s hs => absurd hs (Set.notMem_empty s)
  have h𝒮W : ∀ s ∈ (∅ : Set ((Fin n → K) →+ (Fin n → K))), ∀ i,
      ∀ v ∈ weightFamily (p := p) (glRep Aε) i, s v ∈ weightFamily (p := p) (glRep Aε) i :=
    fun s hs => absurd hs (Set.notMem_empty s)
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  have hζAε : Matrix.GeneralLinearGroup.scalar (Fin n) c₀ ∈ Aε :=
    hAAε (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  set ζ : ↥Aε := ⟨_, hζAε⟩ with hζdef
  have hζv : ∀ v, glRep Aε ζ v = (c₀ : K) • v := fun v => by
    rw [glRep_apply_eq_glEquiv]
    exact glEquiv_scalar_apply c₀ v
  have hfix0 : fixedSpace (glRep Aε) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : glRep Aε ζ v = v := hv ζ (Subgroup.mem_top _)
    rw [hζv] at h1
    have h2 : ((c₀ : K) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc₀1'))
  have hlines := hD1 Aε hA hAεβ hmaxE ⟨c₀, hc₀1, hc₀p, hc₀β⟩
  set T : Finset (Hyperplane ↥Aε p) :=
    Finset.univ.filter fun H' => weightSpace (glRep Aε) H'.1 ≠ ⊥ with hTdef
  have hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥ := fun H' => by
    simp [hTdef]
  have hsum1 : ∀ J ⊆ T, ∑ H' ∈ J, Module.finrank K (weightSpace (glRep Aε) H'.1) = J.card :=
    fun J hJT => by
      rw [Finset.sum_congr rfl fun H' hH' => hlines H' ((hT H').mp (hJT hH')), Finset.sum_const,
        smul_eq_mul, mul_one]
  have hTn : T.card = n := by
    have h1 := finrank_eq_fixedSpace_add_sum_support (glRep Aε) hp hA hpK T hT
    rw [hfix0, finrank_bot, zero_add, Module.finrank_fin_fun, hsum1 T le_rfl] at h1
    exact h1.symm
  have hAεc : Nat.card ↥Aε = p ^ n := by
    rw [card_eq_pow_support β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT,
      hTn]
  have hζH : ∀ H' ∈ T, ζ ∉ H'.1 := by
    intro H' hH' hζ
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hT H').mp hH')
    have h1 := apply_eq_of_mem_weightSpace (glRep Aε) hζ hv
    rw [hζv] at h1
    have h2 : ((c₀ : K) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact hv0 ((smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc₀1'))
  have hLAε : θ.range ≤ Aε := le_sup_left.trans hAAε
  let θε : ↥B₁ →* ↥Aε := θ.codRestrict Aε fun x => hLAε ⟨x, rfl⟩
  have hθcomp : θ = Aε.subtype.comp θε := MonoidHom.ext fun _ => rfl
  have hLc : Nat.card θε.range = Nat.card θ.range := by
    rw [hθcomp, MonoidHom.range_comp, Subgroup.card_map_of_injective Aε.subtype_injective]
  have hZsc : ∀ a ∈ Subgroup.zpowers ζ, ∃ c : Kˣ,
      (a : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨c₀ ^ k, by rw [map_zpow, Subgroup.coe_zpow]⟩
  have hZc : ∀ a ∈ Subgroup.zpowers ζ, ∀ g : GL (Fin n) K, (a : GL (Fin n) K) * g = g * a := by
    intro a ha g
    obtain ⟨c, hc⟩ := hZsc a ha
    rw [hc]
    exact scalarGL_mul_comm c g
  have hLZ : θε.range ⊓ Subgroup.zpowers ζ = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨x, hx⟩, ha⟩
    obtain ⟨c, hc⟩ := hZsc a ha
    have h1 : (a : GL (Fin n) K) ∈ θ.range ⊓ StatedScalars (Fin n) K :=
      ⟨⟨x, by rw [← hx]; rfl⟩, ⟨c, hc.symm⟩⟩
    rw [hθZ, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hζ1 : ζ ≠ 1 := fun h => hc₀1 (scalarGL_injective (by
    rw [map_one]
    exact congrArg Subtype.val h))
  have hZcard : Nat.card ↥(Subgroup.zpowers ζ) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hA ζ) hζ1]
  have hA'c : Nat.card ↥(θε.range ⊔ Subgroup.zpowers ζ) = Nat.card θε.range * p := by
    rw [CFSG.CGT.T75P.card_sup_of_commute (fun a _ b _ => mul_comm a b) hLZ, hZcard]
  have hidx : Nat.card ↥Aε ≤ p * Nat.card ↥(θε.range ⊔ Subgroup.zpowers ζ) := by
    rw [hAεc, hA'c, hLc]
    calc p ^ n = p * (p ^ (n - 2) * p) := by
          rw [← pow_succ, ← pow_succ']
          congr 1
          omega
      _ ≤ p * (Nat.card θ.range * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hθc)
  obtain ⟨Ha, hHa, Hb, hHb, hab, ⟨y, hyA, hya, hyb, hyo⟩, hAtop, hthird⟩ :=
    exists_caseL_pair hp hA hpK hAεβ hmaxE h𝒮 h𝒮W T hT (by omega) hidx
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ)) hζH
  set I : Finset (Hyperplane ↥Aε p) := {Ha, Hb} with hIdef
  have hIT : I ⊆ T := by
    intro H' hH'
    rcases Finset.mem_insert.mp hH' with rfl | hH'
    · exact hHa
    · rw [Finset.mem_singleton.mp hH']
      exact hHb
  have hIc : I.card = 2 := Finset.card_pair hab
  have hUWd : ∀ J ⊆ T, Module.finrank K (wtW Aε J) = J.card ∧
      Module.finrank K (wtU Aε J) = n - J.card := by
    intro J hJT
    have hW : Module.finrank K (wtW Aε J) = J.card := by
      rw [finrank_range_projI (glRep Aε) hp hA hpK J, hsum1 J hJT]
    have h1 : Module.finrank K (wtU Aε J) + Module.finrank K (wtW Aε J) = n :=
      (Submodule.finrank_add_eq_of_isCompl
        (isCompl_ker_range_projI (glRep Aε) hp hA hpK J)).trans (Module.finrank_fin_fun K)
    rw [hW] at h1
    exact ⟨hW, by omega⟩
  obtain ⟨hWd, hUd⟩ := hUWd I hIT
  rw [hIc] at hWd hUd
  have hUW : IsCompl (wtU Aε I) (wtW Aε I) := isCompl_ker_range_projI (glRep Aε) hp hA hpK I
  have hU0 : wtU Aε I ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hUd
    omega
  have hW0 : wtW Aε I ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hWd
    omega
  have hyI : ∀ H' ∈ I, y ∉ H'.1 := by
    intro H' hH'
    rcases Finset.mem_insert.mp hH' with rfl | hH'
    · exact hya
    · rw [Finset.mem_singleton.mp hH']
      exact hyb
  have hyO : ∀ H' : Hyperplane ↥Aε p, H' ∉ I → weightSpace (glRep Aε) H'.1 ≠ ⊥ → y ∈ H'.1 := by
    intro H' hH' hne
    exact hyo H' ((hT H').mpr hne) (fun h => hH' (h ▸ Finset.mem_insert_self _ _))
      (fun h => hH' (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have hyU : ∀ u ∈ wtU Aε I, glEquiv (y : GL (Fin n) K) u = u := fun u hu => by
    rw [← glRep_apply_eq_glEquiv]
    exact (apply_eq_self_iff_projI (glRep Aε) hp hA hpK hyI hyO u).mpr hu
  have hyW' : ∀ w ∈ wtW Aε I, glEquiv (y : GL (Fin n) K) w = w → w = 0 := by
    rintro _ ⟨v, rfl⟩ hfix
    rw [← glRep_apply_eq_glEquiv, apply_eq_self_iff_projI (glRep Aε) hp hA hpK hyI hyO,
      projI_projI (glRep Aε) hp hA hpK] at hfix
    exact hfix
  have hpres : ∀ a : ↥Aε, (∀ u ∈ wtU Aε I, glEquiv (a : GL (Fin n) K) u ∈ wtU Aε I) ∧
      ∀ w ∈ wtW Aε I, glEquiv (a : GL (Fin n) K) w ∈ wtW Aε I := by
    intro a
    have h := preserves_wtU_wtW hp hA hpK I _ (glRep_preserves_weightFamily a)
    simpa only [LinearMap.toAddMonoidHom_coe, glRep_apply_eq_glEquiv] using h
  have hblkJ : ∀ J : Finset (Hyperplane ↥Aε p),
      (3 ≤ Module.finrank K (wtU Aε J) ∨ (Module.finrank K (wtU Aε J) = 2 ∧ Qbig)) →
      blkI β (wtU Aε J) (wtW Aε J) ≤ H ∧
      CFSG.Open.IsQuasisimple ↥(blkI β (wtU Aε J) (wtW Aε J)) ∧
      (∀ x ∈ blkSub β (wtU Aε J) (wtW Aε J), orderOf x = p →
        p ∣ Nat.card ↥(blkI β (wtU Aε J) (wtW Aε J))) ∧
      (∀ y : GL (Fin n) K, (∀ u ∈ wtU Aε J, glEquiv y u ∈ wtU Aε J) →
        (∀ j ∈ blkI β (wtU Aε J) (wtW Aε J), y * j = j * y) →
        ∃ c : K, ∀ u ∈ wtU Aε J, glEquiv y u = c • u) ∧
      (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
        (∀ u ∈ wtU Aε J, ModelGen.semiMap A σ u ∈ wtU Aε J) →
        ∀ y : GL (Fin n) K, (∀ u ∈ wtU Aε J, glEquiv y u ∈ wtU Aε J) → ∀ k : ℕ, 0 < k →
          k < p → ¬ ∀ j ∈ blkI β (wtU Aε J) (wtW Aε J),
            y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j) := fun J hJ =>
    hblk _ _ (isCompl_ker_range_projI (glRep Aε) hp hA hpK J)
      (orth_ker_range_projI β (glRep Aε) hρ J)
      (hβ.imp id fun hsep => nondeg_ker_projI β (glRep Aε) hρ hp hA hpK hsep J) hJ
  obtain ⟨hIH, hIq, hdvd, hSchur, hF5b⟩ := hblkJ I (Or.inl (by rw [hUd]; omega))
  obtain ⟨Hm, hHmT, hHmI⟩ : ∃ Hm ∈ T, Hm ∉ I := by
    by_contra hcon
    push Not at hcon
    have h1 := Finset.card_le_card (show T ⊆ I from hcon)
    omega
  have hJT : insert Hm I ⊆ T := Finset.insert_subset hHmT hIT
  have hJc : (insert Hm I).card = 3 := by rw [Finset.card_insert_of_notMem hHmI, hIc]
  obtain ⟨Hm', hHm'T, hHm'J⟩ : ∃ Hm' ∈ T, Hm' ∉ insert Hm I := by
    by_contra hcon
    push Not at hcon
    have h1 := Finset.card_le_card (show T ⊆ insert Hm I from hcon)
    omega
  have hHm'I : Hm' ∉ I := fun h => hHm'J (Finset.mem_insert_of_mem h)
  have hHm'm : Hm' ≠ Hm := fun h => hHm'J (h ▸ Finset.mem_insert_self _ _)
  have hsupp : ∀ H' ∈ T, ∃ x : ↥Aε, (∀ H'' ∈ ({H'} : Finset (Hyperplane ↥Aε p)), x ∉ H''.1) ∧
      ∀ H'' : Hyperplane ↥Aε p, H'' ∉ ({H'} : Finset (Hyperplane ↥Aε p)) →
        weightSpace (glRep Aε) H''.1 ≠ ⊥ → x ∈ H''.1 := fun H' hH' =>
    exists_supported_element β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W {H'}
      (fun H'' hH'' => by rw [Finset.mem_singleton.mp hH'']; exact (hT H').mp hH')
  obtain ⟨xm, hxm1, hxm2⟩ := hsupp Hm hHmT
  have hpI : p ∣ Nat.card ↥(blkI β (wtU Aε I) (wtW Aε I)) := by
    obtain ⟨h1, h2⟩ := supported_mem_blkSub hp hA hpK hAεβ I hHmI hxm1 hxm2
    exact hdvd _ h1 h2
  obtain ⟨hUJd', hUJd⟩ := hUWd _ hJT
  rw [hJc] at hUJd' hUJd
  obtain ⟨-, hJq, hJdvd, -, -⟩ := hblkJ (insert Hm I) (by
    rcases (by omega : 3 ≤ n - 3 ∨ n - 3 = 2) with h | h
    · exact Or.inl (hUJd ▸ h)
    · exact Or.inr ⟨hUJd.trans h, hQ⟩)
  obtain ⟨xm', hxm'1, hxm'2⟩ := hsupp Hm' hHm'T
  have hpJ : p ∣ Nat.card ↥(blkI β (wtU Aε (insert Hm I)) (wtW Aε (insert Hm I))) := by
    obtain ⟨h1, h2⟩ := supported_mem_blkSub hp hA hpK hAεβ (insert Hm I) hHm'J hxm'1 hxm'2
    exact hJdvd _ h1 h2
  have hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ H := by
    refine hdetH _ (involGL_mem_isomGL hA hp hpK hAεβ I) ?_
    rw [det_involGL hA hp hpK, hsum1 I hIT, hIc]
    norm_num
  have hz2 : glEquiv.symm (invol (glRep Aε) hp hA hpK I) ^ 2 = 1 := by
    apply glEquiv.injective
    refine LinearEquiv.ext fun v => ?_
    rw [map_pow, map_one, pow_two, LinearEquiv.mul_apply, glEquiv_involGL, invol_invol]
    rfl
  have hε : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)
  set Sc : Subgroup ↥Aε := (scalarOnGL (wtU Aε I)).comap Aε.subtype with hScdef
  set D : Subgroup Ω := (Sc.comap θε).map B₁.subtype with hDdef
  have hDB : D ≤ B₁ := Subgroup.map_subtype_le _
  have hD : ∀ x : ↥B₁, (x : Ω) ∈ D ↔ ∃ c : K, ∀ u ∈ wtU Aε I, glEquiv (θ x) u = c • u := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx'⟩
      rw [show x' = x from Subtype.ext hxx'] at hx'
      exact hx'
    · intro h
      exact ⟨x, h, rfl⟩
  have hZSc : ∀ a ∈ Subgroup.zpowers ζ, a ∈ Sc := by
    intro a ha
    obtain ⟨c, hc⟩ := hZsc a ha
    refine ⟨(c : K), fun u _ => ?_⟩
    show glEquiv (a : GL (Fin n) K) u = (c : K) • u
    rw [hc, glEquiv_scalar_apply]
  have hySc : y ∈ Sc := ⟨1, fun u hu => by rw [one_smul]; exact hyU u hu⟩
  obtain ⟨l, ⟨xy, hxy⟩, a₀, ha₀, hyla⟩ := Subgroup.mem_sup.mp hyA
  have hlSc : θε xy ∈ Sc := by
    have : θε xy = y * a₀⁻¹ := by rw [hxy, ← hyla]; group
    rw [this]
    exact Sc.mul_mem hySc (Sc.inv_mem (hZSc a₀ ha₀))
  have hxyD : (xy : Ω) ∈ D := ⟨xy, hlSc, rfl⟩
  have hyθ : (y : GL (Fin n) K) = θ xy * a₀ := by
    rw [← hyla, ← hxy]
    rfl
  have hCpres : ∀ g ∈ H, (∀ x : ↥B₁, (x : Ω) ∈ D → g * θ x = θ x * g) →
      (∀ u ∈ wtU Aε I, glEquiv g u ∈ wtU Aε I) ∧ ∀ w ∈ wtW Aε I, glEquiv g w ∈ wtW Aε I := by
    intro g _ hg
    have h1 : g * θ xy = θ xy * g := hg xy hxyD
    have hgy : g * (y : GL (Fin n) K) = y * g := by
      rw [hyθ, ← mul_assoc, h1, mul_assoc, ← hZc a₀ ha₀ g, mul_assoc]
    have h := preserves_of_comm_supported (glRep Aε) hp hA hpK hyI hyO
      (glEquiv g : (Fin n → K) →ₗ[K] (Fin n → K)) fun v => by
        simp only [glRep_apply_eq_glEquiv, LinearEquiv.coe_coe]
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hgy]
    exact ⟨fun u hu => h.1 u hu, fun w hw => h.2 w hw⟩
  have hfieldU : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      (∀ x : ↥B₁, ModelGen.semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) →
      (∀ u ∈ wtU Aε I, ModelGen.semiMap A σ u ∈ wtU Aε I) ∧
        ∀ w ∈ wtW Aε I, ModelGen.semiMap A σ w ∈ wtW Aε I := by
    intro A σ hAσ
    have ha₀Z : (a₀ : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) :=
      Subgroup.mem_center_iff.mpr fun g => (hZc a₀ ha₀ g).symm
    have hsa₀ : ModelGen.semiConj A σ (a₀ : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := (ModelGen.semiConj A σ).surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha₀Z g']
    have hs := hAσ xy
    rw [CFSG.Open.StatedAPI.statedScalars_eq_center] at hs
    have hZ' : ModelGen.semiConj A σ (a₀ : GL (Fin n) K) * (a₀ : GL (Fin n) K)⁻¹ ∈
        Subgroup.center (GL (Fin n) K) := Subgroup.mul_mem _ hsa₀ (Subgroup.inv_mem _ ha₀Z)
    have hmem : ModelGen.semiConj A σ (y : GL (Fin n) K) * (y : GL (Fin n) K)⁻¹ ∈
        Subgroup.center (GL (Fin n) K) := by
      have e : ModelGen.semiConj A σ (y : GL (Fin n) K) * (y : GL (Fin n) K)⁻¹ =
          (ModelGen.semiConj A σ (θ xy) * (θ xy)⁻¹) *
            (ModelGen.semiConj A σ (a₀ : GL (Fin n) K) * (a₀ : GL (Fin n) K)⁻¹) := by
        have hc1 := (Subgroup.mem_center_iff.mp hZ' (θ xy)⁻¹).symm
        rw [hyθ, map_mul]
        calc ModelGen.semiConj A σ (θ xy) * ModelGen.semiConj A σ (a₀ : GL (Fin n) K) *
              (θ xy * (a₀ : GL (Fin n) K))⁻¹ =
            ModelGen.semiConj A σ (θ xy) * ((ModelGen.semiConj A σ (a₀ : GL (Fin n) K) *
              (a₀ : GL (Fin n) K)⁻¹) * (θ xy)⁻¹) := by group
          _ = _ := by rw [hc1]; group
      rw [e]
      exact Subgroup.mul_mem _ hs hZ'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hconj : ModelGen.semiConj A σ (y : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c * y := by
      rw [hc]
      group
    exact semiMap_preserves_of_semiConj A σ hconj hUW hyU (hpres y).2 hyW'
      (by rw [hWd, hUd]; omega)
  obtain ⟨b, A, σ, hsplit', hscal⟩ : ∃ (b : Ω) (A : GL (Fin n) K) (σ : K ≃+* K),
      (B₁ = B ∨ (b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧ Subgroup.zpowers b ⊓ B₁ = ⊥ ∧
        ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ)) ∧
      ((b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧ Subgroup.zpowers b ⊓ B₁ = ⊥ ∧
        ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ) →
        ∀ x : ↥B₁, ModelGen.semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hact, hform, hfix⟩
    · exact ⟨1, 1, RingEquiv.refl K, Or.inl hBB, fun h => absurd (one_mem B₁) h.2.1⟩
    · exact ⟨b, A, σ, Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform⟩, fun _ => hfix⟩
  have hfield : (b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧ Subgroup.zpowers b ⊓ B₁ = ⊥ ∧
        ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ) →
      (∀ u ∈ wtU Aε I, ModelGen.semiMap A σ u ∈ wtU Aε I) ∧
        (∀ w ∈ wtW Aε I, ModelGen.semiMap A σ w ∈ wtW Aε I) ∧
        ∀ y' : GL (Fin n) K, (∀ u ∈ wtU Aε I, glEquiv y' u ∈ wtU Aε I) →
          (∀ w ∈ wtW Aε I, glEquiv y' w ∈ wtW Aε I) → ∀ k : ℕ, 0 < k → k < p →
            ¬ ∀ j ∈ blkI β (wtU Aε I) (wtW Aε I),
              y' * (ModelGen.semiConj A σ ^ k) j * y'⁻¹ = j := by
    intro hF
    obtain ⟨hU', hW'⟩ := hfieldU A σ (hscal hF)
    exact ⟨hU', hW', fun y' hy'U _ k hk0 hkp => hF5b A σ hF.2.2.2.2.1.1 hU' y' hy'U k hk0 hkp⟩
  obtain ⟨x', hx'A, hx'm, hx'o⟩ := hthird Hm hHmT
    (fun h => hHmI (h ▸ Finset.mem_insert_self _ _))
    (fun h => hHmI (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨l', ⟨x₁, hx₁⟩, a₁, ha₁, hx'la⟩ := Subgroup.mem_sup.mp hx'A
  have hHm'a : Hm' ≠ Ha := fun h => hHm'I (h ▸ Finset.mem_insert_self _ _)
  have hHm'b : Hm' ≠ Hb := fun h =>
    hHm'I (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hx₁D : (x₁ : Ω) ∉ D := by
    rintro ⟨x'', hx'', hxx⟩
    have hx₁Sc : θε x₁ ∈ Sc := by
      rw [show x'' = x₁ from Subtype.ext hxx] at hx''
      exact Subgroup.mem_comap.mp hx''
    rw [hx₁] at hx₁Sc
    have hx'Sc : x' ∈ Sc := hx'la ▸ Sc.mul_mem hx₁Sc (hZSc a₁ ha₁)
    exact hx'm (mem_of_scalarOn_of_mem hp hA hpK hHm'I ((hT Hm').mp hHm'T) hx'Sc
      (hx'o Hm' hHm'T hHm'm hHm'a hHm'b) hHmI ((hT Hm).mp hHmT))
  have hlay := glaPLayer_ne_bot_of_subBlock_supp hp hA hpK hAεβ I hHmI hx'm
    (fun H'' hH'' hne => hx'o H'' ((hT H'').mpr hne)
      (fun h => hH'' (h ▸ Finset.mem_insert_self _ _))
      (fun h => hH'' (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      (fun h => hH'' (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))))) hJq hpJ
  have hcent : Subgroup.centralizer {θ x₁} = Subgroup.centralizer {(x' : GL (Fin n) K)} := by
    have hx' : (x' : GL (Fin n) K) = θ x₁ * a₁ := by
      rw [← hx'la, ← hx₁]
      rfl
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hx']
    constructor
    · intro h
      rw [← mul_assoc, h, mul_assoc, ← hZc a₁ ha₁ g, mul_assoc]
    · intro h
      apply mul_right_cancel (b := (a₁ : GL (Fin n) K))
      calc g * θ x₁ * a₁ = g * (θ x₁ * a₁) := mul_assoc _ _ _
        _ = θ x₁ * a₁ * g := h
        _ = θ x₁ * g * a₁ := by rw [mul_assoc, hZc a₁ ha₁ g, ← mul_assoc]
  have hE : Nat.card D = p ^ 2 →
      (∃ x : ↥B₁, (x : Ω) ∉ D ∧
        GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓ Subgroup.centralizer {θ x}) ≠ ⊥) ∨
      ((b ∈ B ∧ b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ) ∧
        GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓
          centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥) :=
    fun _ => Or.inl ⟨x₁, hx₁D, by rw [hcent]; exact hlay⟩
  have hB₀ : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← ModelGen.inf_centMod_eq_inf_centralizer hSn hcore]
    exact hBC
  have hker : Nat.card θε.ker = p := by
    have hk : θε.ker = (Subgroup.centralizer (S : Set Ω)).subgroupOf B₁ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hθ1]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have heq : Subgroup.centralizer (S : Set Ω) ⊓ B₁ = B ⊓ Subgroup.centralizer (S : Set Ω) :=
      le_antisymm (fun x hx => ⟨hB₁B hx.2, hx.1⟩) (fun x hx => ⟨hx.2, hB₀B₁ hx⟩)
    rw [hk, ← Subgroup.card_map_of_injective B₁.subtype_injective,
      Subgroup.subgroupOf_map_subtype, heq, hB₀]
  have hB₁c : Nat.card ↥B₁ = p * Nat.card θε.range := by
    rw [← Subgroup.card_ker_mul_card_range θε, hker]
  have hDc' : Nat.card ↥D = p * Nat.card ↥(θε.range ⊓ Sc) := by
    rw [hDdef, Subgroup.card_map_of_injective B₁.subtype_injective, card_comap_eq_mul, hker]
  have hLSc : p * Nat.card ↥(θε.range ⊓ Sc) ≤ Nat.card ↥(Sc ⊓ (θε.range ⊔ Subgroup.zpowers ζ)) := by
    have hinf : (θε.range ⊓ Sc) ⊓ Subgroup.zpowers ζ = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans hLZ.le)
    have h1 := CFSG.CGT.T75P.card_sup_of_commute (fun a _ b _ => mul_comm a b) hinf
    rw [hZcard] at h1
    rw [mul_comm, ← h1]
    exact Subgroup.card_le_of_le (sup_le (le_inf inf_le_right (inf_le_left.trans le_sup_left))
      (le_inf hZSc le_sup_right))
  have hG : Nat.card ↥(⨅ H' ∈ T \ I, H'.1) = p ^ 2 := by
    rw [card_biInf_sdiff β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT hIT,
      hIc]
  have hf : Sc ⊓ Hm.1 ≤ ⨅ H' ∈ T \ I, H'.1 := by
    rintro a ⟨haSc, haHm⟩
    rw [Subgroup.mem_iInf]
    intro H'
    rw [Subgroup.mem_iInf]
    intro hH'
    obtain ⟨hH'T, hH'I⟩ := Finset.mem_sdiff.mp hH'
    exact mem_of_scalarOn_of_mem hp hA hpK hHmI ((hT Hm).mp hHmT) haSc haHm hH'I
      ((hT H').mp hH'T)
  obtain ⟨hcard3, hcard2⟩ := card_inf_le_of_index hp Hm.2 hf hG
    (A' := θε.range ⊔ Subgroup.zpowers ζ)
  have hDle : Nat.card ↥D ≤ Nat.card ↥(Sc ⊓ (θε.range ⊔ Subgroup.zpowers ζ)) := by
    rw [hDc']
    exact hLSc
  have hDc : p ^ 2 ≤ Nat.card D := by
    rw [hDc']
    have hl1 : θε xy ≠ 1 := by
      intro h1
      rw [← hxy, h1, one_mul] at hyla
      obtain ⟨c, hc⟩ := hZsc a₀ ha₀
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have h2 := hyU v hv
      rw [← hyla, hc, glEquiv_scalar_apply] at h2
      have hc1 : c = 1 := Units.ext (by
        have h3 : ((c : K) - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0))
      apply hya
      have hy1 : y = 1 := Subtype.ext (by rw [← hyla, hc, hc1, map_one]; rfl)
      rw [hy1]
      exact Ha.1.one_mem
    have hlp : Nat.card ↥(Subgroup.zpowers (θε xy)) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hA _) hl1]
    have hle : Subgroup.zpowers (θε xy) ≤ θε.range ⊓ Sc :=
      Subgroup.zpowers_le.mpr ⟨⟨xy, rfl⟩, hlSc⟩
    calc p ^ 2 = p * p := by ring
      _ ≤ p * Nat.card ↥(θε.range ⊓ Sc) :=
        Nat.mul_le_mul_left _ (hlp ▸ Subgroup.card_le_of_le hle)
  have hDBc : p ^ 2 * Nat.card D ≤ Nat.card B := by
    rcases hAtop with htop | ⟨g, hgG, hgA⟩
    · have hB₁n : Nat.card ↥B₁ = p ^ n := by
        rw [hB₁c, ← hAεc, ← Subgroup.card_top (G := ↥Aε), ← htop, hA'c, mul_comm]
      calc p ^ 2 * Nat.card ↥D ≤ p ^ 2 * p ^ 3 := Nat.mul_le_mul_left _ (hDle.trans hcard3)
        _ = p ^ 5 := by ring
        _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
        _ = Nat.card ↥B₁ := hB₁n.symm
        _ ≤ Nat.card ↥B := Subgroup.card_le_of_le hB₁B
    · calc p ^ 2 * Nat.card ↥D ≤ p ^ 2 * p ^ 2 :=
          Nat.mul_le_mul_left _ (hDle.trans (hcard2 ⟨g, hgG, hgA⟩))
        _ = p ^ 4 := by ring
        _ ≤ Nat.card ↥B := h4
  have hθN : ∀ x : ↥B₁, θ x ∈ Subgroup.normalizer (H : Set (GL (Fin n) K)) := fun x =>
    mem_normalizer_of_conj_mem fun k hk => by
      obtain ⟨k', hk', -⟩ := hθact x ⟨k, hk⟩
      rw [← hk']
      exact k'.2
  have hθφ : ∀ (x : ↥B₁) (k : ↥H),
      φ (ModelGen.conjOn (hθN x) k) = (x : Ω) * φ k * (x : Ω)⁻¹ := by
    intro x k
    obtain ⟨k', hk', hφk'⟩ := hθact x k
    have hkk : ModelGen.conjOn (hθN x) k = k' := Subtype.ext (by rw [ModelGen.coe_conjOn, hk'])
    rw [hkk, hφk']
    rfl
  exact concA_of_block_diag hp hB hBC hHβ φ hφS hφk hB₁B θ (fun x => hθβ ⟨x, rfl⟩) hθN hθφ
    hsplit' hUW hIH hIq hpI hDB hD (fun x => (hpres (θε x)).1) (fun x => (hpres (θε x)).2)
    hCpres hSchur hfield hDc hDBc hE hzH hz2 hε (involGL_apply_wtU hA hp hpK I)
    (involGL_apply_wtW hA hp hpK I) hU0 hW0

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
