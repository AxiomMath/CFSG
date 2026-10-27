module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AFive
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (VecAut projEquiv)

theorem exists_lieIndex_A {n : ℕ} (hn : 5 ≤ n) {X : Type} [Group X] (h : catalogIs X (isLnA n 2)) :
    ∃ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid),
      r + 1 = n ∧ q.card = 2 ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating m hm => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r qq =>
        have h1' : r + 1 = n ∧ qq.card = 2 := h1
        exact ⟨r, qq, hv, h1'.1, h1'.2, ⟨e⟩⟩
      | _ => simp [onLie, isLnEps] at h1
  · omega
  · omega
  · omega
  · omega



theorem center_eq_bot_of_psl_two
    {S : Type} [Group S] [Finite S]
    (hq : CFSG.Open.IsQuasisimple S) {n p f : ℕ} [Fact p.Prime] (hn : 5 ≤ n) (hf : 0 < f)
    (hpf : p ^ f = 2)
    (e : S ⧸ Subgroup.center S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) :
    Subgroup.center S = ⊥ := by
  obtain ⟨-, ⟨M⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl_generic p f n hf
    (by omega) (Or.inr (Or.inr hn))
  have hE : CFSG.Open.griessPSLExceptional n (p ^ f) = (1, 1) :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.griessPSLExceptional_eq_one (by omega) (by omega)
      (by omega) (by omega) (by omega)
  rw [hE, hpf] at M
  have hg : Nat.gcd n (2 - 1) = 1 := by simp
  rw [hg] at M
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))) := by
    have : Subsingleton (Multiplicative (ZMod 1 × ZMod 1 × ZMod 1)) := by
      change Subsingleton (ZMod 1 × ZMod 1 × ZMod 1)
      infer_instance
    exact M.toEquiv.subsingleton
  exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff S).2.2.1.2 hq) e hsub


open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer in
theorem exists_theta
    {n : ℕ} (hn : 5 ≤ n) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥S) (hS : catalogIs (PSimple 3 S) (isLnA n 2)) :
    Subgroup.center ↥S = ⊥ ∧ Nonempty (↥S ≃* VecAut n) ∧
      CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner ↥S := by
  obtain ⟨r, q, hv, hrn, hq2, ⟨e⟩⟩ := exists_lieIndex_A hn hS
  subst hrn
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : Group.IsPerfect ↥S := ⟨hq.1⟩
  let K := GaloisField q.p q.exponent
  have hpf : q.p ^ q.exponent = 2 := by
    have := hq2
    rwa [TauCeti.PrimePower.card_def] at this
  have hKcard : Nat.card K = 2 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne']
    exact hpf
  let Φ' := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv
  let Φ'' := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    (r + 1) K
  have hnab : ∃ a b : PSimple 3 S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_noncomm_projectiveSL
      (K := K) (n := r + 1) (by omega)
    let Ψ : PSimple 3 S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (r + 1) K :=
      e.trans (Φ'.trans Φ'')
    exact ⟨Ψ.symm a, Ψ.symm b, fun h => hab (Ψ.symm.injective (by simpa using h))⟩
  have hOne : GLAPPrimeCore 3 ↥S ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PSimple 3 S) := by
      have h1 : Subsingleton (↥S ⧸ GLAPPrimeCore 3 ↥S) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact (QuotientGroup.mk'_surjective (Subgroup.center (↥S ⧸ GLAPPrimeCore 3 ↥S))).subsingleton
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subsingleton.elim _ _)
  have hOZ : GLAPPrimeCore 3 ↥S ≤ Subgroup.center ↥S :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hOne
  let ΦS : (↥S ⧸ Subgroup.center ↥S) ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group :=
    (pSimpleEquivCenterQuot 3 hOZ).trans e
  have hZ : Subgroup.center ↥S = ⊥ :=
    center_eq_bot_of_psl_two hq (n := r + 1) (p := q.p) (f := q.exponent) (by omega)
      q.exponent_pos hpf (ΦS.trans Φ')
  have hSe : ↥S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group :=
    (QuotientGroup.quotientBot (G := ↥S)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans ΦS)
  refine ⟨hZ, ?_, CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeA_two
    hv hq2 hSe⟩
  obtain ⟨σ⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.exists_ringEquiv_zmod2 K hKcard
  exact ⟨hSe.trans (Φ'.trans (Φ''.trans (projEquiv (r + 1) σ)))⟩


open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer in
theorem exists_action {n : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω} [S.Normal]
    (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hZ : Subgroup.center ↥S = ⊥) (θ : ↥S ≃* VecAut n)
    (hin : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AutThreePowInner ↥S) :
    ∃ (Θ : VecAut n →* Ω) (φ : ↥B →* VecAut n), Function.Injective Θ ∧ Θ.range = S ∧
      (∀ (b : ↥B) (g : VecAut n), (b : Ω) * Θ g * (b : Ω)⁻¹ = Θ (φ b * g * (φ b)⁻¹)) ∧
      (∀ b : ↥B, φ b = 1 ↔ ∀ s ∈ S, (b : Ω) * s = s * (b : Ω)) := by
  let Θ : VecAut n →* Ω := S.subtype.comp θ.symm.toMonoidHom
  have hΘinj : Function.Injective Θ := Subtype.val_injective.comp θ.symm.injective
  have hρinj := conj_injective_of_center_eq_bot hZ
  let ρ : ↥S →* MulAut ↥S := MulAut.conj
  let ρB : ↥B →* MulAut ↥S := (MulAut.conjNormal : Ω →* MulAut ↥S).comp B.subtype
  have hrange : ∀ b : ↥B, ρB b ∈ ρ.range := by
    intro b
    have hb3 : b ^ 3 = (1 : ↥B) := Subtype.ext (by simpa using hB3 b b.2)
    have h3 : (ρB b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
    obtain ⟨a, ha⟩ := hin (ρB b) 1 (fun x => by
      rw [pow_one, iterate_apply_eq_pow, h3]
      rfl)
    refine ⟨a, MulEquiv.ext fun x => ?_⟩
    show MulAut.conj a x = ρB b x
    rw [MulAut.conj_apply]
    exact (ha x).symm
  let φ' : ↥B →* ↥S := ((MonoidHom.ofInjective hρinj).symm.toMonoidHom).comp
    (ρB.codRestrict ρ.range hrange)
  have hφ' : ∀ b : ↥B, ρ (φ' b) = ρB b := by
    intro b
    have := (MonoidHom.ofInjective hρinj).apply_symm_apply ⟨ρB b, hrange b⟩
    exact congrArg Subtype.val this
  refine ⟨Θ, θ.toMonoidHom.comp φ', hΘinj, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact (θ.symm g).2
    · intro hy
      exact ⟨θ ⟨y, hy⟩, by simp [Θ]⟩
  · intro b g
    have h1 : ((ρB b) (θ.symm g) : Ω) = (b : Ω) * (θ.symm g : Ω) * (b : Ω)⁻¹ := by
      simp [ρB, MulAut.conjNormal_apply]
    have h2 : (ρB b) (θ.symm g) = φ' b * θ.symm g * (φ' b)⁻¹ := by
      rw [← hφ' b, MulAut.conj_apply]
    show (b : Ω) * (θ.symm g : Ω) * (b : Ω)⁻¹ = ((θ.symm (θ (φ' b) * g * (θ (φ' b))⁻¹) : ↥S) : Ω)
    rw [← h1, h2]
    simp
  · intro b
    have hρB : ρB b = 1 ↔ ∀ s ∈ S, (b : Ω) * s = s * (b : Ω) := by
      constructor
      · intro h s hs
        have := congrArg (fun f : MulAut ↥S => (f ⟨s, hs⟩ : Ω)) h
        simp only [ρB, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply,
          Subgroup.coe_subtype] at this
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      · intro h
        ext s
        simp only [ρB, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply,
          Subgroup.coe_subtype]
        rw [h s s.2, mul_inv_cancel_right]
    show θ (φ' b) = 1 ↔ _
    rw [← hρB, ← hφ' b, ← map_one ρ, hρinj.eq_iff, ← map_one θ, θ.injective.eq_iff]

theorem card_comap_eq {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H) (Z : Subgroup H)
    (hZ : Z ≤ φ.range) : Nat.card (Z.comap φ) = Nat.card φ.ker * Nat.card Z := by
  let ψ : ↥(Z.comap φ) →* H := φ.comp (Z.comap φ).subtype
  have h := Subgroup.card_ker_mul_card_range ψ
  have hr : ψ.range = Z := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hZ
  have hk : ψ.ker = φ.ker.subgroupOf (Z.comap φ) := (MonoidHom.comap_ker φ (Z.comap φ).subtype).symm
  have hle : φ.ker ≤ Z.comap φ := fun g hg => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]; exact Z.one_mem
  rw [hr, hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  exact h.symm

theorem layer_eq_of_normal_quasisimple {G : Type} [Group G] {H N : Subgroup G} (hNH : N ≤ H)
    (hnorm : (N.subgroupOf H).Normal) (hq : CFSG.Open.IsQuasisimple ↥N) (hcomm : ⁅H, H⁆ ≤ N) :
    CFSG.Open.IsComponentOf N H ∧ GLALayer H = N := by
  have hcomp : CFSG.Open.IsComponentOf N H :=
    ⟨hNH, CFSG.Open.IsSubnormal.step hNH hnorm (CFSG.Open.IsSubnormal.refl H), hq⟩
  refine ⟨hcomp, ?_⟩
  have hall : ∀ K : Subgroup G, CFSG.Open.IsComponentOf K H → K = N := by
    intro K hK
    have hKN : K ≤ N :=
      (CFSG.Fischer.Classification.Recognition.IsQuasisimple.le_commutator hK.2.2).trans
        ((Subgroup.commutator_mono hK.1 hK.1).trans hcomm)
    have hsub : CFSG.Open.IsSubnormal K N := by
      have := CFSG.Fischer.Classification.Recognition.IsSubnormal.inf_normal hK.2.1 hNH hnorm
      rwa [inf_eq_left.mpr hKN] at this
    exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      ⟨hKN, hsub, hK.2.2⟩ hq
  unfold GLALayer
  show sSup {K | CFSG.Open.IsComponentOf K H} = N
  apply le_antisymm
  · exact sSup_le fun K hK => (hall K hK).le
  · exact le_sSup hcomp

theorem catalogIs_isLnA_of_vecAut {k : ℕ} (hk : 5 ≤ k) {X : Type} [Group X]
    (e : X ≃* VecAut k) : catalogIs X (isLnA k 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, one_pos⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSL (r + 1) 2 1 := by
    refine ⟨Nat.prime_two, le_rfl, ?_, ?_, ?_⟩
    · omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  have hdup : ¬ (TauCeti.LieTypeIndex.A r q).IsDuplicateRepresentative := by
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | h) <;> first | omega | exact absurd h (by simp)
  have hv : (TauCeti.LieTypeIndex.A r q).Valid :=
    CFSG.ClassicalModels.linearCatalog_index_valid (r + 1) 2 1 hadm hdup
  refine ⟨.lie ⟨.A r q, hv⟩, Or.inl ⟨rfl, by simp [q, TauCeti.PrimePower.card_def]⟩, ?_⟩
  have hKcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card _ _ one_ne_zero]; norm_num
  obtain ⟨σ⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.exists_ringEquiv_zmod2
    (GaloisField 2 1) hKcard
  let Φ' := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv
  let Φ'' := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    (r + 1) (GaloisField 2 1)
  exact ⟨e.trans ((projEquiv (r + 1) σ).symm.trans (Φ''.symm.trans Φ'.symm))⟩


theorem pSimple_equiv {Ω : Type} [Group Ω] [Finite Ω] {K : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : Subgroup.center ↥K = ⊥) (h3 : 3 ∣ Nat.card ↥K) :
    Nonempty (PSimple 3 K ≃* ↥K) := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro htop
    have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
      CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
    rw [htop, Subgroup.card_top] at hc
    exact (by norm_num : (3 : ℕ) ≠ 1) (Nat.Coprime.eq_one_of_dvd hc h3)
  have hOZ := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hOne
  exact ⟨(pSimpleEquivCenterQuot 3 hOZ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem card_ker_eq_three {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω} {m : ℕ}
    (φ : ↥B →* VecAut m) (hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x)
    (hBel : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1) : Nat.card φ.ker = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordx : orderOf x = 3 := orderOf_eq_prime (hBel.2 x hxB) hx1
  have : φ.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hxB)).toEquiv,
    Nat.card_zpowers, hordx]

theorem isElemAbelian_range {Ω : Type} [Group Ω] {B : Subgroup Ω} {m : ℕ}
    (φ : ↥B →* VecAut m) (hBel : IsElemAbelian 3 B) : IsElemAbelian 3 φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨b₁, h₁⟩ := a.2
    obtain ⟨b₂, h₂⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h₁, ← h₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val (hBel.1.is_comm.comm b₁ b₂))
  · rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have : b ^ 3 = (1 : ↥B) := Subtype.ext (by simpa using hBel.2 b b.2)
    rw [this, map_one]



end CFSG.LocalAnalysis.GLTheoremA.S172A

end
