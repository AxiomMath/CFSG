module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsMax
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open scoped IsMulCommutative

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}
variable {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω}
variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

@[expose] def fieldSet (Dat : ClsInner p S B H β) : Set ((ι → K) →+ (ι → K)) :=
  {s | FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
    s = (ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}

abbrev liftGroup (Dat : ClsInner p S B H β) : Subgroup (GL ι K) := Dat.θ.range.map H.subtype

theorem semiConj_eq_of_comm {A : GL ι K} {σ : K ≃+* K} {g : GL ι K}
    (hg : ∀ v, glEquiv g (ModelGen.semiMap A σ v) = ModelGen.semiMap A σ (glEquiv g v)) :
    ModelGen.semiConj A σ g = g := by
  apply glEquiv.injective
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨v', rfl⟩ := (ModelGen.semiMap A σ).surjective v
  rw [ModelGen.glEquiv_semiConj_apply, hg]

theorem liftGroup_le_centGL (Dat : ClsInner p S B H β) :
    liftGroup Dat ≤ centGL (fieldSet Dat) := by
  rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
  rw [mem_centGL]
  rintro s ⟨hF, rfl⟩ v
  have := ModelGen.glEquiv_semiConj_apply Dat.A Dat.σ ((Dat.θ x : ↥H) : GL ι K) v
  rwa [hF.2.2.2.2.2.2 x] at this

theorem isElemAbelian_liftGroup (Dat : ClsInner p S B H β) : IsElemAbelian p (liftGroup Dat) :=
  CFSG.SectionRank.isElemAbelian_map Dat.elem H.subtype

theorem exists_maximal_engine [Finite K] (Dat : ClsInner p S B H β) (hHβ : H ≤ isomGL β) :
    ∃ Aε : Subgroup (GL ι K), liftGroup Dat ≤ Aε ∧ IsElemAbelian p Aε ∧ Aε ≤ isomGL β ∧
      Aε ≤ centGL (fieldSet Dat) ∧
      ∀ A' : Subgroup (GL ι K), Aε ≤ A' → IsElemAbelian p A' → A' ≤ isomGL β →
        A' ≤ centGL (fieldSet Dat) → A' ≤ Aε := by
  have hle : liftGroup Dat ≤ isomGL β ⊓ centGL (fieldSet Dat) :=
    le_inf ((Subgroup.map_le_range _ _).trans (by rw [Subgroup.range_subtype]; exact hHβ))
      (liftGroup_le_centGL Dat)
  obtain ⟨Aε, h1, h2, h3, h4⟩ := exists_maximal_elemAbelian (isElemAbelian_liftGroup Dat) hle
  exact ⟨Aε, h1, h2, h3.trans inf_le_left, h3.trans inf_le_right,
    fun A' hA' hel hβ' h𝒮' => h4 A' hA' hel (le_inf hβ' h𝒮')⟩

theorem inf_eq_liftGroup [Finite Ω] (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (h4 : p ^ 4 ≤ Nat.card B)
    [Finite K] (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β)
    (hHβ : H ≤ isomGL β) {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
    (hle : liftGroup Dat ≤ Aε) (hAε : IsElemAbelian p Aε) (hAεβ : Aε ≤ isomGL β)
    (hAε𝒮 : Aε ≤ centGL (fieldSet Dat))
    (hmax : ∀ A' : Subgroup (GL ι K), Aε ≤ A' → IsElemAbelian p A' → A' ≤ isomGL β →
      A' ≤ centGL (fieldSet Dat) → A' ≤ Aε)
    (hA : ∀ a : ↥Aε, a ^ p = 1) [DecidableEq (Hyperplane ↥Aε p)]
    (hInv : ∀ H₁ H₂ H₃ : Hyperplane ↥Aε p, H₁ ≠ H₂ → H₁ ≠ H₃ → H₂ ≠ H₃ →
      weightSpace (glRep Aε) H₁.1 ≠ ⊥ → weightSpace (glRep Aε) H₂.1 ≠ ⊥ →
      weightSpace (glRep Aε) H₃.1 ≠ ⊥ →
      glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁, H₂}) ∈ H ∨
        glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁, H₃}) ∈ H ∨
        glEquiv.symm (invol (glRep Aε) hp hA hpK {H₂, H₃}) ∈ H) :
    Aε ⊓ H = liftGroup Dat := by
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  set ρ := glRep Aε with hρdef
  have hρ : IsIsomRep β ρ := isIsomRep_glRep hAεβ
  have hmaxE : IsMaxElem β ρ p (fieldSet Dat) :=
    isMaxElem_of_maximal β (fieldSet Dat) Aε hAε hAεβ hAε𝒮 hmax
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (ρ a v) = ρ a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      s v ∈ weightFamily (p := p) ρ i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear ρ (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
    rw [← ModelGen.inf_centMod_eq_inf_centralizer hSn hcore]
    exact hBC
  have hθcard := ModelGen.card_range_mul_card_inf Dat.θ Dat.θ_eq_one
  obtain ⟨b', hb'B, hb'out, hBcard, hb'comm⟩ : ∃ b' ∈ B,
      Subgroup.zpowers b' ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
      Nat.card B = p * Nat.card Dat.θ.range * Nat.card (Subgroup.zpowers b') ∧
      ∀ e : ↥H, (e : GL ι K) ∈ centGL (fieldSet Dat) → b' * Dat.φ e = Dat.φ e * b' := by
    rcases Dat.split with hBB | hF
    · refine ⟨1, B.one_mem, by simp, ?_, fun e _ => by simp⟩
      have h1 : innerPart S B ⊓ Subgroup.centralizer (S : Set Ω) =
          B ⊓ Subgroup.centralizer (S : Set Ω) := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤
          S ⊔ Subgroup.centralizer (S : Set Ω))]
      rw [h1, hBC'] at hθcard
      have hB1 : Nat.card ↥(innerPart S B) = Nat.card B := by rw [hBB]
      rw [← hB1, ← hθcard, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]
      ring
    · have hF' := hF
      obtain ⟨hbB, hbN, hBb, hbout, hact, hform, hfix⟩ := hF
      refine ⟨Dat.b, hbB, hbout, card_eq_of_inner_split hB hBC' hbB hBb hbout hθcard,
        fun e he => ?_⟩
      obtain ⟨k', hk', hφk'⟩ := hact.2.2 e
      have hse : ModelGen.semiConj Dat.A Dat.σ e = e :=
        semiConj_eq_of_comm fun v => (mem_centGL.mp he) _ ⟨hF', rfl⟩ v
      have hke : k' = e := Subtype.ext (hk'.trans hse)
      rw [hke] at hφk'
      calc Dat.b * Dat.φ e = Dat.b * Dat.φ e * Dat.b⁻¹ * Dat.b := by group
        _ = Dat.φ e * Dat.b := by rw [← hφk']
  have hkerp : Nat.Coprime (Nat.card Dat.φ.ker) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr Dat.not_dvd).symm
  have hcardL : Nat.card ↥(liftGroup Dat) = Nat.card Dat.θ.range :=
    Subgroup.card_map_of_injective H.subtype_injective
  set T : Finset (Hyperplane ↥Aε p) :=
    Finset.univ.filter fun H' => weightSpace ρ H'.1 ≠ ⊥ with hTdef
  have hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace ρ H'.1 ≠ ⊥ := fun H' => by
    simp [hTdef]
  have hcardA : Nat.card ↥Aε = p ^ T.card :=
    card_eq_pow_support β ρ hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT
  have hρW : ∀ (a : ↥Aε) i, ∀ v ∈ weightFamily (p := p) ρ i,
      (ρ a).toAddMonoidHom v ∈ weightFamily (p := p) ρ i := fun a i v hv =>
    preserves_weightFamily_of_semilinear ρ (RingHom.id K) (ρ a).toAddMonoidHom
      (fun c v => map_smul (ρ a) c v)
      (fun a' v => by
        show ρ a (ρ a' v) = ρ a' (ρ a v)
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) i hv
  by_cases h3 : 3 ≤ T.card
  · obtain ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, h12, h13, h23⟩ :=
      Finset.two_lt_card_iff.mp (lt_of_lt_of_le (by norm_num) h3)
    have hpair : ∀ Ha Hb Hc : Hyperplane ↥Aε p, Ha ≠ Hc → Hb ≠ Hc → Ha ∈ T → Hc ∈ T →
        glEquiv.symm (invol ρ hp hA hpK {Ha, Hb}) ∈ H → Aε ⊓ H = liftGroup Dat := by
      intro Ha Hb Hc hac hbc ha hc hzH
      set z : GL ι K := glEquiv.symm (invol ρ hp hA hpK {Ha, Hb}) with hzdef
      have hgz : glEquiv z = invol ρ hp hA hpK {Ha, Hb} := MulEquiv.apply_symm_apply _ _
      set zH : ↥H := ⟨z, hzH⟩ with hzHdef
      have hEel : IsElemAbelian p (Aε.subgroupOf H) :=
        ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hAε.comm x.2 y.2))⟩⟩,
          fun x hx => Subtype.ext (hAε.2 _ hx)⟩
      have hAE : Dat.θ.range ≤ Aε.subgroupOf H := fun y hy => hle ⟨y, hy, rfl⟩
      have hzz : z * z = 1 := by
        apply glEquiv.injective
        rw [map_mul, hgz, map_one]
        exact LinearEquiv.ext fun v => invol_invol ρ hp hA hpK {Ha, Hb} v
      have hz2 : zH ^ 2 = 1 := Subtype.ext (by simpa [pow_two, hzHdef] using hzz)
      have hz1 : Dat.φ zH ≠ 1 := by
        intro h
        have hk : zH ∈ Dat.φ.ker := h
        rw [Dat.ker_eq, Subgroup.mem_subgroupOf] at hk
        obtain ⟨c, hc'⟩ := hk
        have hc'' : Matrix.GeneralLinearGroup.scalar ι c = z := hc'
        refine invol_ne_smul ρ hp hA hpK h2 (Finset.mem_insert_self Ha {Hb})
          (fun h => ?_) ((hT Ha).mp ha) ((hT Hc).mp hc) (c : K) fun v => ?_
        · rcases Finset.mem_insert.mp h with h | h
          · exact hac h.symm
          · exact hbc (Finset.mem_singleton.mp h).symm
        · rw [← hgz, ← hc'', glEquiv_apply]
          simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_mulVec, Matrix.one_mulVec]
      have hzE : ∀ e ∈ Aε.subgroupOf H, e * zH = zH * e := by
        intro e he
        apply Subtype.ext
        apply glEquiv.injective
        refine LinearEquiv.ext fun v => ?_
        simp only [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, hzHdef, hgz]
        have := invol_comm ρ hp hA hpK {Ha, Hb} (ρ ⟨_, he⟩).toAddMonoidHom
          (hρW ⟨_, he⟩) v
        simp only [LinearMap.toAddMonoidHom_coe, hρdef, glRep_apply_eq_glEquiv] at this
        exact this.symm
      have hzc : (z : GL ι K) ∈ centGL (fieldSet Dat) := by
        rw [mem_centGL]
        intro s hs v
        rw [hgz]
        exact (invol_comm ρ hp hA hpK {Ha, Hb} s (h𝒮W s hs) v)
      have hEA := eq_of_le_of_involution hp hSn hcore hZ hB hrank hBC Dat.φ Dat.range_eq hkerp
        hAE hEel hb'B (fun e he => hb'comm e (hAε𝒮 he)) hb'out hBcard hz2 hz1 hzE
        (hb'comm zH hzc)
      have h1 := congrArg (Subgroup.map H.subtype) hEA
      rwa [Subgroup.subgroupOf_map_subtype] at h1
    rcases hInv H₁ H₂ H₃ h12 h13 h23 ((hT H₁).mp hH₁) ((hT H₂).mp hH₂) ((hT H₃).mp hH₃) with
      h | h | h
    · exact hpair H₁ H₂ H₃ h13 h23 hH₁ hH₃ h
    · exact hpair H₁ H₃ H₂ h12 h23.symm hH₁ hH₂ h
    · exact hpair H₂ H₃ H₁ h12.symm h13.symm hH₂ hH₁ h
  ·
    have hb'p : Nat.card (Subgroup.zpowers b') ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hB.2 b' hb'B))
    have hAp : p ^ 2 ≤ Nat.card Dat.θ.range := by
      have h1 : p ^ 4 ≤ p ^ 2 * Nat.card Dat.θ.range := by
        calc p ^ 4 ≤ Nat.card B := h4
          _ = p * Nat.card Dat.θ.range * Nat.card (Subgroup.zpowers b') := hBcard
          _ ≤ p * Nat.card Dat.θ.range * p := Nat.mul_le_mul_left _ hb'p
          _ = p ^ 2 * Nat.card Dat.θ.range := by ring
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      have : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card Dat.θ.range := by
        calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_left this hp2
    have hAεcard : Nat.card ↥Aε ≤ Nat.card ↥(liftGroup Dat) := by
      rw [hcardA, hcardL]
      exact (Nat.pow_le_pow_right hp.pos (by omega)).trans hAp
    have heq : liftGroup Dat = Aε := Subgroup.eq_of_le_of_card_ge hle hAεcard
    rw [← heq, inf_eq_left]
    exact (Subgroup.map_le_range _ _).trans (by rw [Subgroup.range_subtype])

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
