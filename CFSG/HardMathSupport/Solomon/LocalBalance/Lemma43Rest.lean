module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43One
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

open scoped commutatorElement Pointwise

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def Input14_20_7 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K →
    GLAPPrimeCore 5 ↥K = ⊥ → ∀ x : Y, x ∈ Subgroup.normalizer (K : Set Y) →
      ¬ K ≤ Subgroup.centralizer ({x} : Set Y) → K ≤ Subgroup.centralizer ({x ^ 5} : Set Y) →
        ∀ J : Subgroup Y, GLAPComponent 5 (K ⊓ Subgroup.centralizer ({x} : Set Y)) J →
          ¬ IsFiTwentyTwo (↥J ⧸ GLAPPrimeCore 5 ↥J)

namespace Lemma43Rest

variable {G : Type} [Group G] [Finite G]

theorem glaPComponent_of_isSubnormal {p : ℕ} (hp : p.Prime) {X H K : Subgroup G}
    (hHX : IsSubnormal H X) (hK : GLAPComponent p H K) : GLAPComponent p X K := by
  obtain ⟨hKH, hsn, hcomp, hmin⟩ := hK
  have hHXle : H ≤ X := isSubnormal_le' hHX
  have hKX : K ≤ X := hKH.trans hHXle
  have hsnX : IsSubnormal K X := isSubnormal_trans' hsn hHX
  refine ⟨hKX, hsnX, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := X) p hsnX
    rwa [barX_self] at this
  · have e : ↥(barX p X K) ≃* ↥(barX p H K) :=
      (quotEquivBarX hp hKX hsnX).symm.trans (quotEquivBarX hp hKH hsn)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcomp.2.2
  · intro J hJ hJsn heq
    have hJK : J ≤ K := hJ.le
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJK.trans hKH) hHXle
    have hcoreK : K ⊓ GLAPPrimeCoreOf p X ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnX]
      exact glaPPrimeCoreOf_le_of_isSubnormal p hsn
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H K
    refine le_antisymm (barX_mono p hJK) ?_
    refine barX_le_of_forall (hJK.trans hKH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := X) (le_of_eq heq.symm) hk (hKX hk)
    exact ⟨j, hj, hcoreK ⟨K.mul_mem (K.inv_mem (hJK hj)) hk, hjk⟩⟩

theorem b0_isPGroup_bar_of_le_oPrimePOf {J K : Subgroup G} (hJK : J ≤ K)
    (h : J ≤ oPrimePOf 5 K) : IsPGroup 5 (barOf 5 J) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  intro z
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨y, hy, hyj⟩ := h j.2
  have hy' : (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) y) ∈
      CFSG.pCore 5 (↥K ⧸ GLAPPrimeCore 5 ↥K) := hy
  have hy'' : (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) y) ∈
      CFSG.Open.pCore 5 (↥K ⧸ GLAPPrimeCore 5 ↥K) := by
    exact hy'
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K ⧸ GLAPPrimeCore 5 ↥K) 5)
    ⟨_, hy''⟩
  refine ⟨k, ?_⟩
  have hk' : (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) y) ^ 5 ^ k = 1 := congrArg Subtype.val hk
  have hyk : y ^ 5 ^ k ∈ GLAPPrimeCore 5 ↥K := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hk'
  have hmem : ((j ^ 5 ^ k : ↥J) : G) ∈ GLAPPrimeCoreOf 5 K ⊓ J := by
    refine ⟨⟨y ^ 5 ^ k, hyk, ?_⟩, (j ^ 5 ^ k).2⟩
    simp [← hyj]
  have h2 := gLAPPrimeCoreOf_inf_le hp K J hmem
  rw [inf_eq_right.2 hJK] at h2
  obtain ⟨c, hc, hcj⟩ := h2
  have : c = j ^ 5 ^ k := Subtype.ext hcj
  rw [this] at hc
  exact (QuotientGroup.eq_one_iff _).2 hc

theorem glaPComponent_eq_of_le {X K₁ K₂ J : Subgroup G} (h₁ : GLAPComponent 5 X K₁)
    (h₂ : GLAPComponent 5 X K₂) (hJ₁ : J ≤ K₁) (hJ₂ : J ≤ K₂)
    (hJ : ¬ IsPGroup 5 (barOf 5 J)) : K₁ = K₂ := by
  by_contra hne
  have hp : Nat.Prime 5 := by norm_num
  exact hJ (b0_isPGroup_bar_of_le_oPrimePOf hJ₁
    (le_inf hJ₁ hJ₂ |>.trans (inf_le_oPrimePOf_of_ne hp h₁ h₂ hne)))

omit [Finite G] in
theorem b0_exists_mul_of_le_sup {p : ℕ} {J K : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf p K) :
    ∀ k ∈ K, ∃ j ∈ J, ∃ q ∈ GLAPPrimeCoreOf p K, j * q = k := by
  intro k hk
  have hmem : (⟨k, hk⟩ : ↥K) ∈ J.subgroupOf K ⊔ GLAPPrimeCore p ↥K := by
    have h1 : (J.subgroupOf K ⊔ GLAPPrimeCore p ↥K).map K.subtype = J ⊔ GLAPPrimeCoreOf p K := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJK]
      rfl
    have h2 : k ∈ (J.subgroupOf K ⊔ GLAPPrimeCore p ↥K).map K.subtype := by
      rw [h1]; exact hcov hk
    obtain ⟨y, hy, hyk⟩ := h2
    have : y = ⟨k, hk⟩ := Subtype.ext hyk
    rwa [this] at hy
  obtain ⟨j, hj, q, hq, hjq⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  exact ⟨j, (Subgroup.mem_subgroupOf).1 hj, q, ⟨q, hq, rfl⟩, congrArg Subtype.val hjq⟩

theorem barOf_equiv_of_cover {J K : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 5 K) : Nonempty (barOf 5 J ≃* barOf 5 K) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  set g : ↥J →* ↥K := Subgroup.inclusion hJK with hg
  set f : ↥J →* barOf 5 K := (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K)).comp g with hf
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨j, hj, q, ⟨q', hq', rfl⟩, hjq⟩ := b0_exists_mul_of_le_sup hJK hcov k k.2
    refine ⟨⟨j, hj⟩, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) (g ⟨j, hj⟩) = QuotientGroup.mk' _ k
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (g ⟨j, hj⟩)⁻¹ * k = q' := by
      apply Subtype.ext
      have : (j : G) * q'.1 = k := hjq
      simp only [hg, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← this]; simp
    rw [this]; exact hq'
  have hker : f.ker = GLAPPrimeCore 5 ↥J := by
    have hP0 : GLAPPrimeCore 5 (barOf 5 K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    refine le_antisymm ?_ ?_
    ·
      have hker' : f.ker = (GLAPPrimeCore 5 ↥K).comap g := by
        ext x
        simp [hf, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
      refine le_sSup ⟨MonoidHom.normal_ker f, ?_⟩
      have hle : (f.ker).map g ≤ GLAPPrimeCore 5 ↥K := by
        rw [hker']; exact Subgroup.map_comap_le _ _
      have h1 : Nat.card (f.ker.map g) = Nat.card f.ker :=
        Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJK)
      have h2 := Subgroup.card_dvd_of_le hle
      rw [h1] at h2
      exact (coprime_card_gLAPPrimeCore_aux 5 ↥K).coprime_dvd_right h2
    ·
      have hnorm : ((GLAPPrimeCore 5 ↥J).map f).Normal :=
        Subgroup.Normal.map inferInstance f hsurj
      have hcop : Nat.Coprime 5 (Nat.card ((GLAPPrimeCore 5 ↥J).map f)) :=
        (coprime_card_gLAPPrimeCore_aux 5 ↥J).coprime_dvd_right (Subgroup.card_map_dvd _ f)
      have hle : (GLAPPrimeCore 5 ↥J).map f ≤ GLAPPrimeCore 5 (barOf 5 K) :=
        le_sSup ⟨hnorm, hcop⟩
      rw [hP0] at hle
      intro x hx
      have : f x ∈ (GLAPPrimeCore 5 ↥J).map f := ⟨x, hx, rfl⟩
      have h3 := hle this
      exact (MonoidHom.mem_ker).2 (Subgroup.mem_bot.1 h3)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

omit [Finite G] in
theorem b0_le_normalizer_core {p : ℕ} {X M : Subgroup G} (h : M ≤ Subgroup.normalizer (X : Set G)) :
    M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  intro g hg
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (h hg)
  rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, h1]

theorem b0_core_le_of_cover {J K : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 5 K) : GLAPPrimeCoreOf 5 J ≤ GLAPPrimeCoreOf 5 K := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  set g : ↥J →* ↥K := Subgroup.inclusion hJK with hg
  set f : ↥J →* barOf 5 K := (QuotientGroup.mk' (GLAPPrimeCore 5 ↥K)).comp g with hf
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨j, hj, q, ⟨q', hq', rfl⟩, hjq⟩ := b0_exists_mul_of_le_sup hJK hcov k k.2
    refine ⟨⟨j, hj⟩, ?_⟩
    show QuotientGroup.mk' (GLAPPrimeCore 5 ↥K) (g ⟨j, hj⟩) = QuotientGroup.mk' _ k
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (g ⟨j, hj⟩)⁻¹ * k = q' := by
      apply Subtype.ext
      have : (j : G) * q'.1 = k := hjq
      simp only [hg, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← this]; simp
    rw [this]; exact hq'
  have hP0 : GLAPPrimeCore 5 (barOf 5 K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hnorm : ((GLAPPrimeCore 5 ↥J).map f).Normal :=
    Subgroup.Normal.map inferInstance f hsurj
  have hcop : Nat.Coprime 5 (Nat.card ((GLAPPrimeCore 5 ↥J).map f)) :=
    (coprime_card_gLAPPrimeCore_aux 5 ↥J).coprime_dvd_right (Subgroup.card_map_dvd _ f)
  have hle : (GLAPPrimeCore 5 ↥J).map f ≤ GLAPPrimeCore 5 (barOf 5 K) :=
    le_sSup ⟨hnorm, hcop⟩
  rw [hP0] at hle
  rintro _ ⟨x, hx, rfl⟩
  have : f x ∈ (GLAPPrimeCore 5 ↥J).map f := ⟨x, hx, rfl⟩
  have h3 := hle this
  have h4 : g x ∈ GLAPPrimeCore 5 ↥K := by
    have := Subgroup.mem_bot.1 h3
    exact (QuotientGroup.eq_one_iff _).1 this
  exact ⟨g x, h4, rfl⟩

omit [Finite G] in
theorem b0_subnormal_simple {S : Type*} [Group S] [IsSimpleGroup S] {H : Subgroup S}
    (h : IsSubnormal H ⊤) : H = ⊥ ∨ H = ⊤ := by
  by_cases hne : H = ⊤
  · exact Or.inr hne
  · left
    obtain ⟨M, hHM, -, hMne, hn, -⟩ := isSubnormal_exists_normal h hne
    have h1 : ⊤ ≤ Subgroup.normalizer (M : Set S) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hn
    have hMn : M.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h1)
    rcases Subgroup.Normal.eq_bot_or_eq_top (G := S) M with h2 | h2
    · exact le_bot_iff.1 (h2 ▸ hHM)
    · exact absurd h2 hMne

omit [Finite G] in
theorem b0_commutator_mul_central {Q : Type*} [Group Q] {g h c : Q}
    (hc : c ∈ Subgroup.center Q) : ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have hc' : ∀ x : Q, c * x = x * c := fun x => (Subgroup.mem_center_iff.1 hc x).symm
  have : c * h * c⁻¹ = h := by rw [mul_inv_eq_iff_eq_mul]; exact hc' h
  rw [commutatorElement_def, commutatorElement_def]
  calc g * c * h * (g * c)⁻¹ * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [this]

omit [Finite G] in
theorem b0_eq_top_of_isComponentOf {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {E : Subgroup Q} (hE : IsComponentOf E ⊤) : E = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hQ
  have hEsn := hE.2.1
  have hEq := hE.2.2
  have hbar : IsSubnormal (E.map (QuotientGroup.mk' (Subgroup.center Q))) ⊤ := by
    have := isSubnormal_map' (QuotientGroup.mk' (Subgroup.center Q)) hEsn
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  rcases @b0_subnormal_simple _ _ hsimple _ hbar with h | h
  · exfalso
    have hEc : E ≤ Subgroup.center Q := by
      intro e he
      have : QuotientGroup.mk' (Subgroup.center Q) e ∈
          E.map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨e, he, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff _).1 this
    obtain ⟨hEperf, hEsimple⟩ := hEq
    have hcomm : ∀ x y : E, x * y = y * x := fun x y =>
      Subtype.ext (((Subgroup.mem_center_iff.1 (hEc x.2)) y).symm)
    have hbot : commutator E = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      simp [commutatorElement_def, hcomm a b]
    rw [hbot] at hEperf
    obtain ⟨a, b, hab⟩ := @exists_pair_ne _ hEsimple.toNontrivial
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : x = 1 := by
      have : x ∈ (⊤ : Subgroup E) := Subgroup.mem_top x
      rw [← hEperf] at this
      exact Subgroup.mem_bot.1 this
    have hy : y = 1 := by
      have : y ∈ (⊤ : Subgroup E) := Subgroup.mem_top y
      rw [← hEperf] at this
      exact Subgroup.mem_bot.1 this
    exact hab (by rw [hx, hy])
  ·
    have hcov : ∀ a : Q, ∃ e ∈ E, e⁻¹ * a ∈ Subgroup.center Q := by
      intro a
      have : QuotientGroup.mk' (Subgroup.center Q) a ∈
          E.map (QuotientGroup.mk' (Subgroup.center Q)) := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨e, he, hea⟩ := this
      exact ⟨e, he, QuotientGroup.eq.1 hea⟩
    have hle : commutator Q ≤ E := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨e₁, he₁, hc₁⟩ := hcov a
      obtain ⟨e₂, he₂, hc₂⟩ := hcov b
      have ha : a = e₁ * (e₁⁻¹ * a) := by group
      have hb : b = e₂ * (e₂⁻¹ * b) := by group
      rw [ha, hb]
      have h1 : ⁅e₁ * (e₁⁻¹ * a), e₂ * (e₂⁻¹ * b)⁆ = ⁅e₁, e₂ * (e₂⁻¹ * b)⁆ :=
        b0_commutator_mul_central hc₁
      have h2 : ⁅e₁, e₂ * (e₂⁻¹ * b)⁆ = ⁅e₁, e₂⁆ := by
        calc ⁅e₁, e₂ * (e₂⁻¹ * b)⁆ = ⁅e₂ * (e₂⁻¹ * b), e₁⁆⁻¹ := (commutatorElement_inv _ _).symm
          _ = ⁅e₂, e₁⁆⁻¹ := by rw [b0_commutator_mul_central hc₂]
          _ = ⁅e₁, e₂⁆ := commutatorElement_inv e₂ e₁
      rw [h1, h2]
      exact Subgroup.commutator_mem_commutator he₁ he₂ |> fun _ => by
        simpa [commutatorElement_def] using E.mul_mem (E.mul_mem (E.mul_mem he₁ he₂) (E.inv_mem he₁)) (E.inv_mem he₂)
    rw [hperf] at hle
    exact top_le_iff.1 hle

theorem b0_isQuasisimple_bar {X K : Subgroup G} (hK : GLAPComponent 5 X K) :
    CFSG.Open.IsQuasisimple (barOf 5 K) := by
  have hp : Nat.Prime 5 := by norm_num
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivBarX hp hK.1 hK.2.1).symm hK.2.2.1.2.2

theorem cover_of_trivial_action {X K J A : Subgroup G} (hK : GLAPComponent 5 X K)
    (hAp : IsPGroup 5 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hJ : GLAPComponent 5 (K ⊓ Subgroup.centralizer (A : Set G)) J)
    (htriv : ∀ x ∈ A, ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 5 K) :
    K ≤ J ⊔ GLAPPrimeCoreOf 5 K := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  set P := GLAPPrimeCoreOf 5 K with hPdef
  set Z := K ⊓ Subgroup.centralizer (A : Set G) with hZ
  have hZK : Z ≤ K := inf_le_left
  have hPK : P ≤ K := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 5 K
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := b0_le_normalizer_core hAK
  have hlift : ∀ k ∈ K, ∃ z ∈ Z, z⁻¹ * k ∈ P := by
    intro k hk
    have hkP : k ∈ Subgroup.normalizer (P : Set G) := le_normalizer_glaPPrimeCoreOf 5 K hk
    obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 5) (U := A) (V := P) hAp
      (not_dvd_card_glaPPrimeCoreOf hp K) hAP hkP (fun u hu => by
        have := P.inv_mem (htriv u hu k hk)
        have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
        rwa [e] at this)
    refine ⟨k * v, ⟨K.mul_mem hk (hPK hv), ?_⟩, by simpa using P.inv_mem hv⟩
    show k * v ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (mul_inv_eq_iff_eq_mul.1 (hfix u hu))
  have hcov : K ≤ Z ⊔ P := by
    intro k hk
    obtain ⟨z, hz, hzk⟩ := hlift k hk
    have : k = z * (z⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hz hzk
  obtain ⟨e⟩ := barOf_equiv_of_cover hZK hcov
  have hZQ : CFSG.Open.IsQuasisimple (barOf 5 Z) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
      (b0_isQuasisimple_bar hK)
  have hJtop : barX 5 Z J = ⊤ := b0_eq_top_of_isComponentOf hZQ hJ.2.2.1
  have hcoreZ : GLAPPrimeCoreOf 5 Z ≤ P := b0_core_le_of_cover hZK hcov
  intro k hk
  obtain ⟨z, hz, hzk⟩ := hlift k hk
  have hle : barX 5 Z Z ≤ barX 5 Z J := by rw [hJtop]; exact le_top
  obtain ⟨j, hj, hjz⟩ := exists_of_barX_le hle hz hz
  have hc : j⁻¹ * z ∈ P := hcoreZ hjz
  have : k = j * ((j⁻¹ * z) * (z⁻¹ * k)) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hj (P.mul_mem hc hzk)

omit [Finite G] in
theorem b1_isQuasisimple_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hn : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  refine ⟨?_, ?_⟩
  · rcases Subgroup.Normal.eq_bot_or_eq_top (G := Q) (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      apply hab
      have : ⁅a, b⁆ ∈ commutator Q := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  · have hc : Subgroup.center Q = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (G := Q) (Subgroup.center Q) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hn
        apply hab
        have : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.1 this b).symm
    have e : Q ⧸ Subgroup.center Q ≃* Q ⧸ (⊥ : Subgroup Q) :=
      QuotientGroup.congr _ _ (MulEquiv.refl Q) (by rw [hc]; simp)
    exact (e.trans (QuotientGroup.quotientBot (G := Q))).isSimpleGroup_congr.2 hs

theorem exists_J_structure {L A : Subgroup G} (hAp : IsPGroup 5 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAtriv : A ≤ centralizerQuot L (GLAPPrimeCoreOf 5 L))
    (hsimple : IsSimpleGroup (barOf 5 L)) (hnab : ∃ a b : barOf 5 L, a * b ≠ b * a) :
    ∃ J : Subgroup G, GLAPComponent 5 (L ⊓ Subgroup.centralizer (A : Set G)) J ∧
      GLAPLayer 5 (L ⊓ Subgroup.centralizer (A : Set G)) = J ∧
      Nonempty (barOf 5 J ≃* barOf 5 L) ∧
      (∀ F : Subgroup G, IsPGroup 5 F → F ≤ L ⊓ Subgroup.centralizer (A : Set G) → F ≤ J) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  set P := GLAPPrimeCoreOf 5 L with hPdef
  set Y := L ⊓ Subgroup.centralizer (A : Set G) with hYdef
  have hYL : Y ≤ L := inf_le_left
  have hPL : P ≤ L := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 5 L
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := b0_le_normalizer_core hAN
  have hlift : ∀ l ∈ L, ∃ y ∈ Y, y⁻¹ * l ∈ P := by
    intro l hl
    have hlP : l ∈ Subgroup.normalizer (P : Set G) := le_normalizer_glaPPrimeCoreOf 5 L hl
    obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 5) (U := A) (V := P) hAp
      (not_dvd_card_glaPPrimeCoreOf hp L) hAP hlP (fun u hu => by
        have := P.inv_mem ((hAtriv hu).2.2 l hl)
        have e : (l * u * l⁻¹ * u⁻¹)⁻¹ = u * l * u⁻¹ * l⁻¹ := by group
        rwa [e] at this)
    refine ⟨l * v, ⟨L.mul_mem hl (hPL hv), ?_⟩, by simpa using P.inv_mem hv⟩
    show l * v ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (mul_inv_eq_iff_eq_mul.1 (hfix u hu))
  have hcov : L ≤ Y ⊔ P := by
    intro l hl
    obtain ⟨z, hz, hzl⟩ := hlift l hl
    have : l = z * (z⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hz hzl
  obtain ⟨e⟩ := barOf_equiv_of_cover hYL hcov
  have hLq : CFSG.Open.IsQuasisimple (barOf 5 L) := b1_isQuasisimple_of_simple hsimple hnab
  have hYq : CFSG.Open.IsQuasisimple (barOf 5 Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hLq
  have hTop : IsComponentOf (⊤ : Subgroup (barOf 5 Y)) ⊤ :=
    ⟨le_top, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        Subgroup.topEquiv.symm hYq⟩
  obtain ⟨J, hJ, hJtop⟩ := exists_glaPComponent_barX_eq (p := 5) Y hTop
  have huniq : ∀ J₂ : Subgroup G, GLAPComponent 5 Y J₂ → J₂ = J := by
    intro J₂ hJ₂
    exact glaPComponent_unique hJ₂ hJ
      ((b0_eq_top_of_isComponentOf hYq hJ₂.2.2.1).trans hJtop.symm)
  have hcovJ : Y ≤ J ⊔ GLAPPrimeCoreOf 5 Y := by
    intro y hy
    have hle : barX 5 Y Y ≤ barX 5 Y J := by rw [hJtop]; exact le_top
    obtain ⟨j, hj, hjy⟩ := exists_of_barX_le hle hy hy
    have : y = j * (j⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hj hjy
  have hlayer : GLAPLayer 5 Y = J := by
    unfold GLAPLayer
    exact le_antisymm (sSup_le fun K hK => (huniq K hK).le) (le_sSup hJ)
  have hequiv : Nonempty (barOf 5 J ≃* barOf 5 L) := by
    obtain ⟨e1⟩ := barOf_equiv_of_cover hJ.1 hcovJ
    exact ⟨e1.trans e⟩
  refine ⟨J, hJ, hlayer, hequiv, ?_⟩
  have hYpre : Y ≤ preimBarX 5 Y J := by
    intro y hy
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore 5 ↥Y) ⟨y, hy⟩ ∈ barX 5 Y J
    rw [hJtop]; exact Subgroup.mem_top _
  have hYN : Y ≤ Subgroup.normalizer (J : Set G) :=
    hYpre.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX 5 hJ.1)).1
      (glaPComponent_normal_preimBarX hJ))
  have hJYn : (J.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ.1).2 hYN
  intro F hF hFY f hf
  have hfY : f ∈ Y := hFY hf
  have hle : barX 5 Y Y ≤ barX 5 Y J := by rw [hJtop]; exact le_top
  obtain ⟨j, hj, hjf⟩ := exists_of_barX_le hle hfY hfY
  obtain ⟨c', hc', hc'e⟩ := hjf
  obtain ⟨a, ha⟩ := hF ⟨f, hf⟩
  have hfa : f ^ 5 ^ a = 1 := congrArg Subtype.val ha
  have hjY : j ∈ Y := hJ.1 hj
  set fY : ↥Y := ⟨f, hfY⟩ with hfYdef
  have h1 : fY = ⟨j, hjY⟩ * c' := by
    apply Subtype.ext
    have h2 : (c' : G) = j⁻¹ * f := hc'e
    show f = j * (c' : G)
    rw [h2]; group
  have hmk : (QuotientGroup.mk fY : ↥Y ⧸ J.subgroupOf Y) = QuotientGroup.mk c' := by
    rw [h1, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (⟨j, hjY⟩ : ↥Y) : ↥Y ⧸ J.subgroupOf Y) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((Subgroup.mem_subgroupOf).2 hj)
    rw [this, one_mul]
  have hd1 : orderOf (QuotientGroup.mk fY : ↥Y ⧸ J.subgroupOf Y) ∣ 5 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : fY ^ 5 ^ a = 1 := Subtype.ext (by simpa [hfYdef] using hfa)
    rw [this, QuotientGroup.mk_one]
  have hd2 : orderOf (QuotientGroup.mk fY : ↥Y ⧸ J.subgroupOf Y) ∣
      Nat.card (GLAPPrimeCore 5 ↥Y) := by
    rw [hmk]
    exact (orderOf_map_dvd (QuotientGroup.mk' (J.subgroupOf Y)) c').trans
      (Subgroup.orderOf_dvd_natCard (GLAPPrimeCore 5 ↥Y) hc')
  have hcop : Nat.Coprime (5 ^ a) (Nat.card (GLAPPrimeCore 5 ↥Y)) :=
    (coprime_card_gLAPPrimeCore_aux 5 ↥Y).pow_left a
  have hone := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have hmk1 : (QuotientGroup.mk fY : ↥Y ⧸ J.subgroupOf Y) = 1 := orderOf_eq_one_iff.1 hone
  have := (QuotientGroup.eq_one_iff _).1 hmk1
  exact (Subgroup.mem_subgroupOf).1 this

omit [Finite G] in
theorem b2_isKGroup_of_injective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (hB : CFSG.Open.IsKGroup B) : CFSG.Open.IsKGroup A :=
  hB.of_injective f hf

omit [Finite G] in
theorem b2_isKGroup_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hA : CFSG.Open.IsKGroup A) : CFSG.Open.IsKGroup B :=
  hA.of_surjective f hf

theorem E1 (h1420 : Input14_20_7) {X K : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hK : GLAPComponent 5 X K) {x : G} (hxX : x ∈ X)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hx5 : x ^ 5 = 1) {K' : Subgroup G}
    (hK' : GLAPComponent 5 (K ⊓ Subgroup.centralizer ({x} : Set G)) K')
    (hfi : IsFiTwentyTwo (barOf 5 K')) :
    ⁅K, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 5 K := by
  by_contra hcon
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  let π : ↥X →* (↥X ⧸ GLAPPrimeCore 5 ↥X) := QuotientGroup.mk' _
  set Khat := barX 5 X K with hKhat
  set xhat : ↥X ⧸ GLAPPrimeCore 5 ↥X := π ⟨x, hxX⟩ with hxhat
  have hKq : CFSG.Open.IsQuasisimple ↥Khat := hK.2.2.1.2.2
  have hKsn : IsSubnormal Khat ⊤ := hK.2.2.1.2.1
  have hKg : CFSG.Open.IsKGroup ↥Khat :=
    b2_isKGroup_of_injective Khat.subtype Khat.subtype_injective
      (b2_isKGroup_of_surjective π (QuotientGroup.mk'_surjective _) hX)
  have hcore : GLAPPrimeCore 5 ↥Khat = ⊥ := by
    set V : Subgroup (↥X ⧸ GLAPPrimeCore 5 ↥X) := GLAPPrimeCoreOf 5 Khat with hV
    have hVK : V ≤ Khat := Subgroup.map_subtype_le _
    have hVn : (V.subgroupOf Khat).Normal := by
      have : V.subgroupOf Khat = GLAPPrimeCore 5 ↥Khat :=
        Subgroup.comap_map_eq_self_of_injective Khat.subtype_injective _
      rw [this]; infer_instance
    have hVsn : IsSubnormal V ⊤ :=
      isSubnormal_trans' (IsSubnormal.step hVK hVn (IsSubnormal.refl _)) hKsn
    have hVc : Nat.Coprime 5 (Nat.card V) := by
      have : Nat.card V = Nat.card (GLAPPrimeCore 5 ↥Khat) :=
        Subgroup.card_map_of_injective Khat.subtype_injective
      rw [this]; exact coprime_card_gLAPPrimeCore_aux 5 ↥Khat
    have hVbot : V = ⊥ :=
      eq_bot_of_isSubnormal_of_coprime hp (glaPPrimeCore_quotient_eq_bot hp) hVsn hVc
    exact (Subgroup.map_eq_bot_iff_of_injective _ Khat.subtype_injective).1 hVbot
  have hxN : xhat ∈ Subgroup.normalizer (Khat : Set (↥X ⧸ GLAPPrimeCore 5 ↥X)) := by
    have h1 : xhat ∈ barX 5 X (Subgroup.zpowers x) :=
      ⟨⟨x, hxX⟩, (Subgroup.mem_subgroupOf).2 (Subgroup.mem_zpowers x), rfl⟩
    exact barX_le_normalizer (Subgroup.zpowers_le.2 hxK) h1
  have hxhat5 : xhat ^ 5 = 1 := by
    rw [hxhat, ← map_pow]
    have : (⟨x, hxX⟩ : ↥X) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
    rw [this, map_one]
  have hx5' : Khat ≤ Subgroup.centralizer ({xhat ^ 5} : Set (↥X ⧸ GLAPPrimeCore 5 ↥X)) := by
    intro q _
    rw [hxhat5, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]; simp
  have hnc : ¬ Khat ≤ Subgroup.centralizer ({xhat} : Set (↥X ⧸ GLAPPrimeCore 5 ↥X)) := by
    intro hle
    apply hcon
    have hxT : x ∈ centralizerQuot K (GLAPPrimeCoreOf 5 K) := by
      refine ⟨hxK, b0_le_normalizer_core (Subgroup.zpowers_le.2 hxK) (Subgroup.mem_zpowers x),
        fun k hk => ?_⟩
      have hkX : k ∈ X := hK.1 hk
      have hmem : π ⟨k, hkX⟩ ∈ Khat := ⟨⟨k, hkX⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
      have hc := (Subgroup.mem_centralizer_iff.1 (hle hmem)) xhat rfl
      have hX1 : k * x * k⁻¹ * x⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem (X.mul_mem hkX hxX) (X.inv_mem hkX)) (X.inv_mem hxX)
      have h1 : π ⟨k * x * k⁻¹ * x⁻¹, hX1⟩ = 1 := by
        have e : (⟨k * x * k⁻¹ * x⁻¹, hX1⟩ : ↥X) = ⟨k, hkX⟩ * ⟨x, hxX⟩ * ⟨k, hkX⟩⁻¹ * ⟨x, hxX⟩⁻¹ :=
          rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
        change π ⟨k, hkX⟩ * xhat * (π ⟨k, hkX⟩)⁻¹ * xhat⁻¹ = 1
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact hc.symm
      have h2 : k * x * k⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 5 X :=
        ⟨⟨_, hX1⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
      have h3 : k * x * k⁻¹ * x⁻¹ ∈ K := by
        have := K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 hxK k⁻¹).1 (K.inv_mem hk))
        simpa [mul_assoc] using this
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1]
      exact ⟨h3, h2⟩
    have hz : Subgroup.zpowers x ≤ centralizerQuot K (GLAPPrimeCoreOf 5 K) :=
      Subgroup.zpowers_le.2 hxT
    refine Subgroup.commutator_le.2 fun k hk g hg => ?_
    have := (hz hg).2.2 k hk
    rw [commutatorElement_def]
    exact this
  set W := K ⊓ Subgroup.centralizer ({x} : Set G) with hW
  have hWX : W ≤ X := inf_le_left.trans hK.1
  set WX : Subgroup ↥X := W.subgroupOf X with hWXdef
  have hWXmap : WX.map X.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWX
  have hker0 : ∀ B : Subgroup ↥X, Nat.Coprime 5 (Nat.card ↥(B ⊓ X.subtype.ker)) := by
    intro B
    rw [Subgroup.ker_subtype, inf_bot_eq]
    simp
  have hK'W : GLAPComponent 5 (WX.map X.subtype) K' := by rw [hWXmap]; exact hK'
  obtain ⟨K'', hK''WX, hK''map⟩ := exists_glaPComponent_map_eq hp X.subtype (hker0 WX) hK'W
  subst hK''map
  have hker1 : ∀ B : Subgroup ↥X, Nat.Coprime 5 (Nat.card ↥(B ⊓ π.ker)) := by
    intro B
    have hk : π.ker = GLAPPrimeCore 5 ↥X := QuotientGroup.ker_mk' _
    have hd := Subgroup.card_dvd_of_le (inf_le_right : B ⊓ π.ker ≤ π.ker)
    rw [hk] at hd ⊢
    exact (coprime_card_gLAPPrimeCore_aux 5 ↥X).coprime_dvd_right hd
  have hJ1 := glaPComponent_map hp π (hker1 WX) hK''WX
  have hd5 : IsPGroup 5 ↥(Subgroup.zpowers x) := by
    rintro ⟨g, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx5, one_zpow]
  have himg : WX.map π = Khat ⊓ Subgroup.centralizer ({xhat} : Set (↥X ⧸ GLAPPrimeCore 5 ↥X)) :=
    barX_inf_centralizer hp hxX hK.1 hxK hd5
  rw [himg] at hJ1
  have hfi2 : IsFiTwentyTwo (barOf 5 (K''.map π)) := by
    obtain ⟨e⟩ := hfi
    exact ⟨((lcEquiv hp π K'' (hker1 K'')).symm.trans
      (lcEquiv hp X.subtype K'' (hker0 K''))).trans e⟩
  exact h1420 (↥X ⧸ GLAPPrimeCore 5 ↥X) Khat hKq hKg hcore xhat hxN hnc hx5' (K''.map π) hJ1 hfi2

omit [Finite G] in
theorem b3_centralizer_sup (D E : Subgroup G) :
    Subgroup.centralizer ((D ⊔ E : Subgroup G) : Set G) =
      Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (E : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_sup_left : D ≤ D ⊔ E)))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (le_sup_right : E ≤ D ⊔ E)))
  · rw [← Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]; exact inf_le_left
    · rw [Subgroup.le_centralizer_iff]; exact inf_le_right

omit [Finite G] in
theorem b3_centralizer_zpowers (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite G] in
theorem b3_ne_bot_of_not_pGroup {J : Subgroup G} (hJnp : ¬ IsPGroup 5 (barOf 5 J)) : J ≠ ⊥ := by
  intro h
  apply hJnp
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have : x = 1 := by
    apply Subtype.ext
    have hx : (x : G) ∈ (⊥ : Subgroup G) := h ▸ x.2
    simpa using Subgroup.mem_bot.1 hx
  exact ⟨0, by simp [this]⟩

theorem b3_collapse (h183 : Input18_3_4) {X E J : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hEX : E ≤ X) (hE : IsElemAbelian 5 E)
    (hnormE : ∀ K : Subgroup G, GLAPComponent 5 X K → E ≤ Subgroup.normalizer (K : Set G))
    (hJ : GLAPComponent 5 (X ⊓ Subgroup.centralizer (E : Set G)) J) (hJne : J ≠ ⊥) :
    ∃ K : Subgroup G, GLAPComponent 5 X K ∧ J ≤ K ∧
      K = ⨆ g ∈ GLAPLayer 5 X, GLBConj g J := by
  have hp : Nat.Prime 5 := by norm_num
  obtain ⟨𝒞, h𝒞comp, h𝒞sup, h𝒞E, h𝒞tr⟩ := h183 G X hX 5 hp E hEX hE J hJ
  have hJle : J ≤ ⨆ g ∈ GLAPLayer 5 X, GLBConj g J := by
    refine le_iSup₂_of_le (1 : G) (one_mem _) ?_
    rw [gLBConj_one]
  have hne : ∃ K₀, K₀ ∈ 𝒞 := by
    by_contra hcon
    push Not at hcon
    have h1 : (⨆ L ∈ 𝒞, L) = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun L hL => (hcon L hL).elim)
    rw [h𝒞sup, ← le_bot_iff] at h1
    exact hJne (le_bot_iff.1 (hJle.trans h1))
  obtain ⟨K₀, hK₀⟩ := hne
  have hall : ∀ L ∈ 𝒞, L = K₀ := by
    intro L hL
    obtain ⟨e, he, heq⟩ := h𝒞tr K₀ hK₀ L hL
    have := mem_normalizer_iff_gLBConj_eq.1 (hnormE K₀ (h𝒞comp K₀ hK₀) he)
    rw [← heq, this]
  have hsup : (⨆ L ∈ 𝒞, L) = K₀ :=
    le_antisymm (iSup₂_le fun L hL => (hall L hL).le) (le_iSup₂_of_le K₀ hK₀ le_rfl)
  refine ⟨K₀, h𝒞comp K₀ hK₀, ?_, ?_⟩
  · rw [← hsup, h𝒞sup]; exact hJle
  · rw [← h𝒞sup, hsup]

theorem tprop (h183 : Input18_3_4) (h1420 : Input14_20_7) {A J : Subgroup G}
    (hAel : IsElemAbelian 5 A)
    (hX : ∀ D : Subgroup G, D ≤ A → D ≠ ⊥ → CFSG.Open.IsKGroup ↥(Subgroup.centralizer (D : Set G)))
    (hnorm : ∀ D : Subgroup G, D ≤ A → D ≠ ⊥ → ∀ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer (D : Set G)) K → A ≤ Subgroup.normalizer (K : Set G))
    (hJ : GLAPComponent 5 (Subgroup.centralizer (A : Set G)) J)
    (hJfi : IsFiTwentyTwo (barOf 5 J)) (hJnp : ¬ IsPGroup 5 (barOf 5 J)) :
    ∀ D : Subgroup G, D ≤ A → D ≠ ⊥ → ∃ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer (D : Set G)) K ∧ J ≤ K ∧
      K ≤ J ⊔ GLAPPrimeCoreOf 5 K ∧
      K = ⨆ g ∈ GLAPLayer 5 (Subgroup.centralizer (D : Set G)), GLBConj g J := by
  have hp : Nat.Prime 5 := by norm_num
  have hJne : J ≠ ⊥ := b3_ne_bot_of_not_pGroup hJnp
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => elemAbelian_comm hAel ha hb
  have hAp : IsPGroup 5 A := GL83.isPGroup_of_isElemAbelian hAel
  have key : ∀ n : ℕ, ∀ D : Subgroup G, D ≤ A → D ≠ ⊥ → Nat.card A - Nat.card D = n →
      ∃ K : Subgroup G, GLAPComponent 5 (Subgroup.centralizer (D : Set G)) K ∧ J ≤ K ∧
        K ≤ J ⊔ GLAPPrimeCoreOf 5 K ∧
        K = ⨆ g ∈ GLAPLayer 5 (Subgroup.centralizer (D : Set G)), GLBConj g J := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro D hDA hD0 hn
      set X := Subgroup.centralizer (D : Set G) with hXdef
      have hAX : A ≤ X := by
        intro a ha
        rw [hXdef, Subgroup.mem_centralizer_iff]
        intro d hd
        exact (hAcomm d (hDA hd) a ha)
      have hCAX : Subgroup.centralizer (A : Set G) ≤ X := Subgroup.centralizer_le hDA
      have hJ' : GLAPComponent 5 (X ⊓ Subgroup.centralizer (A : Set G)) J := by
        rw [inf_eq_right.2 hCAX]; exact hJ
      obtain ⟨K₀, hK₀, hJK₀, hK₀eq⟩ := b3_collapse h183 (hX D hDA hD0) hAX hAel
        (hnorm D hDA hD0) hJ' hJne
      have hAK₀ : A ≤ Subgroup.normalizer (K₀ : Set G) := hnorm D hDA hD0 K₀ hK₀
      have htriv : ∀ x ∈ A, ⁅K₀, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 5 K₀ := by
        intro x hxA
        by_cases hxD : x ∈ D
        · refine Subgroup.commutator_le.2 fun k hk g hg => ?_
          have hgD : g ∈ D := (Subgroup.zpowers_le.2 hxD) hg
          have hkc : k ∈ Subgroup.centralizer (D : Set G) := hK₀.1 hk
          have : k * g = g * k := ((Subgroup.mem_centralizer_iff.1 hkc) g hgD).symm
          rw [commutatorElement_def, this]
          simp
        · set D' := D ⊔ Subgroup.zpowers x with hD'def
          have hD'A : D' ≤ A := sup_le hDA (Subgroup.zpowers_le.2 hxA)
          have hD'ne : D' ≠ ⊥ := fun h => hD0 (le_bot_iff.1 (h ▸ le_sup_left))
          have hlt : D < D' := by
            refine lt_of_le_of_ne le_sup_left fun h => hxD ?_
            rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
          have hcard := card_lt_of_lt' hlt
          have hcardA : Nat.card D' ≤ Nat.card A := Subgroup.card_le_of_le hD'A
          obtain ⟨K', hK', hJK', hK'cov, -⟩ := ih (Nat.card A - Nat.card D') (by omega) D' hD'A hD'ne rfl
          have hxX : x ∈ X := hAX hxA
          have hzX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.2 hxX
          have hCD' : Subgroup.centralizer (D' : Set G) = X ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
            rw [hD'def, b3_centralizer_sup]
          have hK'' : GLAPComponent 5 (X ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) K' := by
            rw [← hCD']; exact hK'
          obtain ⟨K₂, hK₂, hK'K₂, -⟩ := b3_collapse h183 (hX D hDA hD0) hzX
            (isElemAbelian_mono hAel (Subgroup.zpowers_le.2 hxA))
            (fun K hK => (Subgroup.zpowers_le.2 hxA).trans (hnorm D hDA hD0 K hK)) hK''
            (fun h => hJne (le_bot_iff.1 (h ▸ hJK')))
          have hJK₂ : J ≤ K₂ := hJK'.trans hK'K₂
          have hK₂eq : K₂ = K₀ := glaPComponent_eq_of_le hK₂ hK₀ hJK₂ hJK₀ hJnp
          have hK'sub : K' ≤ K₀ ⊓ Subgroup.centralizer ({x} : Set G) := by
            refine le_inf (hK'K₂.trans hK₂eq.le) ?_
            have h1 : K' ≤ X ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) := hK''.1
            exact h1.trans (inf_le_right.trans (b3_centralizer_zpowers x).le)
          have hK'comp : GLAPComponent 5 (K₀ ⊓ Subgroup.centralizer ({x} : Set G)) K' := by
            refine glaPComponent_of_le hp hK' hK'sub ?_
            rw [hCD']
            exact inf_le_inf hK₀.1 (b3_centralizer_zpowers x).ge
          have hfi' : IsFiTwentyTwo (barOf 5 K') := by
            obtain ⟨e⟩ := barOf_equiv_of_cover hJK' hK'cov
            obtain ⟨f⟩ := hJfi
            exact ⟨e.symm.trans f⟩
          exact E1 h1420 (hX D hDA hD0) hK₀ hxX (hAK₀ hxA) (hAel.2 x hxA) hK'comp hfi'
      refine ⟨K₀, hK₀, hJK₀, ?_, hK₀eq⟩
      refine cover_of_trivial_action hK₀ hAp hAK₀
        (glaPComponent_of_le hp hJ (le_inf hJK₀ hJ.1) inf_le_right) ?_
      intro x hx k hk
      have := htriv x hx (Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers x))
      simpa [commutatorElement_def] using this
  intro D hDA hD0
  exact key _ D hDA hD0 rfl

omit [Finite G] in
theorem b5_mem_sup_mul {P S : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G)) :
    ∀ x ∈ P ⊔ S, ∃ p ∈ P, ∃ s ∈ S, p * s = x := by
  intro x hx
  set H := P ⊔ S with hH
  have hHN : H ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hSP
  have hn : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHN
  have hmem : (⟨x, hx⟩ : ↥H) ∈ P.subgroupOf H ⊔ S.subgroupOf H := by
    have h1 : (P.subgroupOf H ⊔ S.subgroupOf H).map H.subtype = H := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
        Subgroup.map_subgroupOf_eq_of_le le_sup_right]
    have h2 : x ∈ (P.subgroupOf H ⊔ S.subgroupOf H).map H.subtype := by rw [h1]; exact hx
    obtain ⟨y, hy, hyx⟩ := h2
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  obtain ⟨y, hy, z, hz, hyz⟩ := (@Subgroup.mem_sup_of_normal_left _ _ _ _ hn _).1 hmem
  exact ⟨y, (Subgroup.mem_subgroupOf).1 hy, z, (Subgroup.mem_subgroupOf).1 hz,
    congrArg Subtype.val hyz⟩

theorem b5_not_dvd_card_sup {P S : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hS : IsPGroup 2 S) (hP : ¬ 5 ∣ Nat.card P) : ¬ 5 ∣ Nat.card ↥(P ⊔ S) := by
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := P ⊔ S with hH
  have hHN : H ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hSP
  have hn : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHN
  have hQ2 : IsPGroup 2 (↥H ⧸ P.subgroupOf H) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨p, hp, s, hs, hps⟩ := b5_mem_sup_mul hSP h h.2
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hsH : s ∈ H := Subgroup.mem_sup_right hs
    have hmk : (QuotientGroup.mk h : ↥H ⧸ P.subgroupOf H) =
        QuotientGroup.mk (⟨s, hsH⟩ : ↥H) := by
      rw [QuotientGroup.eq]
      refine (Subgroup.mem_subgroupOf).2 ?_
      have h1 : (h : G) = p * s := hps.symm
      have h2 := (Subgroup.mem_normalizer_iff.1 (hSP (S.inv_mem hs)) p).1 hp
      simpa [h1, mul_assoc] using P.inv_mem h2
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨s, hsH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hsk)
    rw [this, QuotientGroup.mk_one]
  obtain ⟨m, hm⟩ := hQ2.exists_card_eq
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf H)
  have hcardP : Nat.card (P.subgroupOf H) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  intro hd
  rw [hcard, hm, hcardP] at hd
  rcases (Nat.Prime.dvd_mul hp5).1 hd with h | h
  · have := hp5.dvd_of_dvd_pow h
    omega
  · exact hP h

theorem b5_exists_R {P S B : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hP : ¬ 5 ∣ Nat.card P) (hB5 : IsPGroup 5 B)
    (hBW : B ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G)) :
    ∃ R : Subgroup G, R ≤ P ⊔ S ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ B ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card R = 2 ^ (Nat.card ↥(P ⊔ S)).factorization 2 := by
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  set W := P ⊔ S with hW
  have hW5 := b5_not_dvd_card_sup hSP hS hP
  obtain ⟨R₀, hR₀⟩ := exists_sylow_normalized (r := 2) (p := 5) hBW hB5 hW5
  have hcard : Nat.card ((R₀ : Subgroup W).map W.subtype) = 2 ^ (Nat.card W).factorization 2 := by
    rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact Sylow.card_eq_multiplicity R₀
  refine ⟨(R₀ : Subgroup W).map W.subtype, Subgroup.map_subtype_le _, ?_, ?_, hR₀, hcard⟩
  · exact R₀.isPGroup'.map W.subtype
  · intro hbot
    have h1 : Nat.card ((R₀ : Subgroup W).map W.subtype) = 1 := by rw [hbot]; simp
    rw [hcard] at h1
    have h2 : 2 ∣ Nat.card S := by
      obtain ⟨m, hm⟩ := hS.exists_card_eq
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hS1 (Subgroup.card_eq_one.1 (by rw [hm]; simp))
      rw [hm]; exact dvd_pow_self 2 hm0
    have h3 : 2 ∣ Nat.card W := h2.trans (Subgroup.card_dvd_of_le le_sup_right)
    have h4 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h3
    have h5 : 2 ^ (Nat.card W).factorization 2 ≠ 1 := by
      intro h
      have := Nat.one_lt_two_pow h4.ne'
      omega
    exact h5 h1

theorem b5_frattini {K P R : Subgroup G} (hRP : R ≤ Subgroup.normalizer (P : Set G))
    (hRK : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ * r⁻¹ ∈ P)
    (hcard : Nat.card R = 2 ^ (Nat.card ↥(P ⊔ R)).factorization 2) :
    ∀ k ∈ K, ∃ q ∈ P, q⁻¹ * k ∈ Subgroup.normalizer (R : Set G) := by
  intro k hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := P ⊔ R with hH
  have hRH : R ≤ H := le_sup_right
  set R' : Subgroup G := R.map (MulAut.conj k).toMonoidHom with hR'
  have hR'H : R' ≤ H := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : k * r * k⁻¹ * r⁻¹ ∈ P := hRK k hk r hr
    have : (MulAut.conj k).toMonoidHom r = (k * r * k⁻¹ * r⁻¹) * r := by
      simp [MulAut.conj_apply]
    rw [this]
    exact H.mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hr)
  have hR'card : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hc1 : Nat.card (R.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hc2 : Nat.card (R'.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hcard, ← hR'card]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'H).toEquiv
  let SR : Sylow 2 ↥H := Sylow.ofCard (R.subgroupOf H) hc1
  let SR' : Sylow 2 ↥H := Sylow.ofCard (R'.subgroupOf H) hc2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H SR SR'
  have h1 : ((SR' : Subgroup ↥H)) = (SR : Subgroup ↥H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl
  have h2 : R'.subgroupOf H = (R.subgroupOf H).map (MulAut.conj g).toMonoidHom := h1
  have h3 : R' = R.map (MulAut.conj (g : G)).toMonoidHom := by
    have := congrArg (Subgroup.map H.subtype) h2
    rw [Subgroup.map_subgroupOf_eq_of_le hR'H, Subgroup.map_map] at this
    rw [this]
    have hcomp : H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype := by
      ext x; simp
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRH]
  obtain ⟨p, hp, s, hs, hps⟩ := b5_mem_sup_mul hRP (g : G) g.2
  have hcc : ∀ a b : G, (R.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      R.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map]
    congr 1
    ext x; simp [MulAut.conj_apply, mul_assoc]
  have hsR : R.map (MulAut.conj s).toMonoidHom = R := by
    have := mem_normalizer_iff_gLBConj_eq.1
      ((Subgroup.le_normalizer : R ≤ Subgroup.normalizer (R : Set G)) (R.inv_mem hs))
    simpa [GLBConj] using this
  have h4 : R.map (MulAut.conj k).toMonoidHom = R.map (MulAut.conj p).toMonoidHom := by
    have h5 : R.map (MulAut.conj (g : G)).toMonoidHom = R.map (MulAut.conj p).toMonoidHom := by
      rw [← hps, ← hcc s p, hsR]
    rw [← h5]; exact h3
  refine ⟨p, hp, ?_⟩
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold GLBConj
  have hconj1 : R.map (MulAut.conj (1 : G)).toMonoidHom = R := by
    have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext; simp
    rw [this, Subgroup.map_id]
  have h6 : (R.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom = R := by
    rw [hcc, inv_mul_cancel, hconj1]
  rw [h4, hcc] at h6
  have : ((p⁻¹ * k)⁻¹) = k⁻¹ * p := by group
  rw [this]; exact h6

theorem b5_le_normalizer_of_cover {Z J : Subgroup G} (hJ : GLAPComponent 5 Z J)
    (hcov : Z ≤ J ⊔ GLAPPrimeCoreOf 5 Z) : Z ≤ Subgroup.normalizer (J : Set G) := by
  have hYpre : Z ≤ preimBarX 5 Z J := by
    intro z hz
    obtain ⟨j, hj, q, ⟨q', hq', rfl⟩, hjq⟩ := b0_exists_mul_of_le_sup hJ.1 hcov z hz
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore 5 ↥Z) ⟨z, hz⟩ ∈ barX 5 Z J
    refine ⟨⟨j, hJ.1 hj⟩, (Subgroup.mem_subgroupOf).2 hj, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨j, hJ.1 hj⟩ : ↥Z)⁻¹ * ⟨z, hz⟩ = q' := by
      apply Subtype.ext
      have h1 : (j : G) * (q' : G) = z := hjq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1]; group
    rw [this]; exact hq'
  exact hYpre.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX 5 hJ.1)).1
    (glaPComponent_normal_preimBarX hJ))

omit [Finite G] in
theorem b5_trivial_of_cover {J K A : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 5 K) (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ∀ g ∈ A, ∀ k ∈ K, k * g * k⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 5 K := by
  intro g hg k hk
  obtain ⟨j, hj, q, hq, rfl⟩ := b0_exists_mul_of_le_sup hJK hcov k hk
  have hgP : g ∈ Subgroup.normalizer (GLAPPrimeCoreOf 5 K : Set G) :=
    b0_le_normalizer_core hAK hg
  have hjP : j ∈ Subgroup.normalizer (GLAPPrimeCoreOf 5 K : Set G) :=
    le_normalizer_glaPPrimeCoreOf 5 K (hJK hj)
  have hcomm : g * j = j * g := (Subgroup.mem_centralizer_iff.1 (hJA hj)) g hg
  have hc' : j⁻¹ * g⁻¹ = g⁻¹ * j⁻¹ := by
    have := congrArg (fun x => x⁻¹) hcomm
    simpa [mul_inv_rev] using this
  have h1 : g * q⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 5 K :=
    (Subgroup.mem_normalizer_iff.1 hgP q⁻¹).1 ((GLAPPrimeCoreOf 5 K).inv_mem hq)
  have h2 : q * g * q⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 5 K := by
    have := (GLAPPrimeCoreOf 5 K).mul_mem hq h1
    simpa [mul_assoc] using this
  have h3 : j * (q * g * q⁻¹ * g⁻¹) * j⁻¹ ∈ GLAPPrimeCoreOf 5 K :=
    (Subgroup.mem_normalizer_iff.1 hjP _).1 h2
  have e : (j * q) * g * (j * q)⁻¹ * g⁻¹ = j * (q * g * q⁻¹ * g⁻¹) * j⁻¹ := by
    calc (j * q) * g * (j * q)⁻¹ * g⁻¹ = j * (q * g * q⁻¹) * (j⁻¹ * g⁻¹) := by group
      _ = j * (q * g * q⁻¹) * (g⁻¹ * j⁻¹) := by rw [hc']
      _ = j * (q * g * q⁻¹ * g⁻¹) * j⁻¹ := by group
  rw [e]; exact h3

omit [Finite G] in
theorem b5_mem_triv_conj {K P : Subgroup G} {s t : G} (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) (ht : t ∈ centralizerQuot K P) :
    s * t * s⁻¹ ∈ centralizerQuot K P := by
  obtain ⟨htK, htP, htr⟩ := ht
  refine ⟨(Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem hsK htK) ((Subgroup.normalizer (K : Set G)).inv_mem hsK),
    (Subgroup.normalizer (P : Set G)).mul_mem
      ((Subgroup.normalizer (P : Set G)).mul_mem hsP htP) ((Subgroup.normalizer (P : Set G)).inv_mem hsP),
    fun k hk => ?_⟩
  have hk' : s⁻¹ * k * s ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (K : Set G)).inv_mem hsK) k).1 hk
    simpa using this
  have h1 := htr _ hk'
  have h2 := (Subgroup.mem_normalizer_iff.1 hsP _).1 h1
  have e : k * (s * t * s⁻¹) * k⁻¹ * (s * t * s⁻¹)⁻¹ =
      s * ((s⁻¹ * k * s) * t * (s⁻¹ * k * s)⁻¹ * t⁻¹) * s⁻¹ := by group
  rw [e]; exact h2

omit [Finite G] in
theorem b5_lift {K P N A : Subgroup G} (hAp : IsPGroup 5 A)
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hP5 : ¬ 5 ∣ Nat.card P)
    (hAN : A ≤ N) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hAtriv : ∀ g ∈ A, ∀ k ∈ K, k * g * k⁻¹ * g⁻¹ ∈ P)
    (hcov : ∀ k ∈ K, ∃ n ∈ N ⊓ K, ∃ q ∈ P, k = n * q) :
    ∀ k ∈ K, ∃ u ∈ N ⊓ K ⊓ Subgroup.centralizer (A : Set G), ∃ p ∈ P, k = u * p := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  intro k hk
  obtain ⟨n, hn, q, hq, rfl⟩ := hcov k hk
  set V := N ⊓ K ⊓ P with hV
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_inf (mem_normalizer_inf (Subgroup.le_normalizer (hAN hg)) (hAK hg)) (hAP hg)
  have hnV : n ∈ Subgroup.normalizer (V : Set G) :=
    mem_normalizer_inf (mem_normalizer_inf (Subgroup.le_normalizer hn.1)
      (Subgroup.le_normalizer hn.2)) (hKP hn.2)
  have hVp : ¬ 5 ∣ Nat.card V := fun h => hP5 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hx : ∀ u ∈ A, u * n * u⁻¹ * n⁻¹ ∈ V := by
    intro u hu
    have h1 : u * n * u⁻¹ * n⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem (hAN hu) hn.1) (N.inv_mem (hAN hu))) (N.inv_mem hn.1)
    have h2 : u * n * u⁻¹ * n⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAK hu) n).1 hn.2) (K.inv_mem hn.2)
    have h3 : u * n * u⁻¹ * n⁻¹ ∈ P := by
      have := P.inv_mem (hAtriv u hu n hn.2)
      have e : (n * u * n⁻¹ * u⁻¹)⁻¹ = u * n * u⁻¹ * n⁻¹ := by group
      rwa [e] at this
    exact ⟨⟨h1, h2⟩, h3⟩
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 5) (U := A) (V := V) hAp hVp hAV hnV hx
  refine ⟨n * v, ⟨⟨N.mul_mem hn.1 hv.1.1, K.mul_mem hn.2 hv.1.2⟩, ?_⟩, v⁻¹ * q,
    P.mul_mem (P.inv_mem hv.2) hq, by group⟩
  show n * v ∈ Subgroup.centralizer (A : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact mul_inv_eq_iff_eq_mul.1 (hfix u hu)

theorem b5_sim {J K : Subgroup G} (hJK : J ≤ K) (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 5 K)
    (hsimple : IsSimpleGroup (barOf 5 J)) {W : Subgroup G} (hPW : GLAPPrimeCoreOf 5 K ≤ W)
    (hWK : W ≤ K) (hKW : K ≤ Subgroup.normalizer (W : Set G)) :
    W = GLAPPrimeCoreOf 5 K ∨ W = K := by
  have hOJ : GLAPPrimeCoreOf 5 J ≤ GLAPPrimeCoreOf 5 K := b0_core_le_of_cover hJK hcov
  by_cases hJW : J ≤ W
  · right
    refine le_antisymm hWK fun k hk => ?_
    obtain ⟨j, hj, q, hq, rfl⟩ := b0_exists_mul_of_le_sup hJK hcov k hk
    exact W.mul_mem (hJW hj) (hPW hq)
  · left
    set M₁ : Subgroup ↥J := (J ⊓ W).subgroupOf J with hM₁
    have hM₁n : M₁.Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun j hj => ?_
      exact mem_normalizer_inf (Subgroup.le_normalizer hj) (hKW (hJK hj))
    have hM₁O : M₁ ≤ GLAPPrimeCore 5 ↥J := by
      set π : ↥J →* barOf 5 J := QuotientGroup.mk' (GLAPPrimeCore 5 ↥J) with hπ
      have hmn : (M₁.map π).Normal := Subgroup.Normal.map hM₁n π (QuotientGroup.mk'_surjective _)
      rcases Subgroup.Normal.eq_bot_or_eq_top (G := barOf 5 J) (M₁.map π) with h | h
      · intro m hm
        have : π m ∈ M₁.map π := ⟨m, hm, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff _).1 this
      · exfalso
        apply hJW
        intro j hj
        have : π ⟨j, hj⟩ ∈ M₁.map π := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨m, hm, hmj⟩ := this
        have hmj' : (m : ↥J)⁻¹ * ⟨j, hj⟩ ∈ GLAPPrimeCore 5 ↥J := by
          rw [← QuotientGroup.eq]; exact hmj
        have hmW : (m : G) ∈ W := ((Subgroup.mem_subgroupOf).1 hm).2
        have hoW : ((m : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J) ∈ GLAPPrimeCore 5 ↥J := hmj'
        have hoO : (((m : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J) : G) ∈ GLAPPrimeCoreOf 5 J := ⟨_, hoW, rfl⟩
        have hjeq : j = (m : G) * (((m : ↥J)⁻¹ * ⟨j, hj⟩ : ↥J) : G) := by simp
        rw [hjeq]
        exact W.mul_mem hmW (hPW (hOJ hoO))
    refine le_antisymm (fun w hw => ?_) hPW
    obtain ⟨j, hj, q, hq, hjq⟩ := b0_exists_mul_of_le_sup hJK hcov w (hWK hw)
    have hjW : j ∈ W := by
      have : j = w * q⁻¹ := by rw [← hjq]; group
      rw [this]; exact W.mul_mem hw (W.inv_mem (hPW hq))
    have hjM : (⟨j, hj⟩ : ↥J) ∈ M₁ := (Subgroup.mem_subgroupOf).2 ⟨hj, hjW⟩
    have hjO : j ∈ GLAPPrimeCoreOf 5 J := ⟨⟨j, hj⟩, hM₁O hjM, rfl⟩
    rw [← hjq]
    exact (GLAPPrimeCoreOf 5 K).mul_mem (hOJ hjO) hq

omit [Finite G] in
theorem b5_mem_normalizer_sup {g : G} {X Y : Subgroup G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hX hY ⊢
  unfold GLBConj at hX hY ⊢
  rw [Subgroup.map_sup, hX, hY]

theorem b5_card_R_eq {P S R : Subgroup G} (hRW : R ≤ P ⊔ S)
    (hcard : Nat.card R = 2 ^ (Nat.card ↥(P ⊔ S)).factorization 2) :
    Nat.card R = 2 ^ (Nat.card ↥(P ⊔ R)).factorization 2 := by
  have hH' : P ⊔ R ≤ P ⊔ S := sup_le le_sup_left hRW
  have h1 : Nat.card ↥(P ⊔ R) ∣ Nat.card ↥(P ⊔ S) := Subgroup.card_dvd_of_le hH'
  have h2 : Nat.card R ∣ Nat.card ↥(P ⊔ R) := Subgroup.card_dvd_of_le le_sup_right
  have hf1 : (Nat.card ↥(P ⊔ R)).factorization 2 ≤ (Nat.card ↥(P ⊔ S)).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 h1 2
  have hf2 : (Nat.card ↥(P ⊔ S)).factorization 2 ≤ (Nat.card ↥(P ⊔ R)).factorization 2 := by
    rw [hcard] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
  rw [hcard, le_antisymm hf1 hf2]

theorem iii_core (hchar : IsCharTwoType G) (hKp : CFSG.Open.IsKProper G) (h116 : Input11_6)
    {A B J F : Subgroup G}
    (hBel : IsElemAbelian 5 B)
    (hBU : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G))
    (hBsc : IsSCp 5 ⊤ B) (hAB : A ≤ B) (hA25 : 25 ≤ Nat.card A)
    (hcentne : ∀ a : G, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≠ ⊤)
    (hrank : ∀ a ∈ B, a ≠ 1 → GLATwoLocalRank 5 ↥(Subgroup.centralizer ({a} : Set G)) ≤
      CFSG.Open.pRank 5 (B.subgroupOf (Subgroup.centralizer ({a} : Set G))))
    (hJ : GLAPComponent 5 (Subgroup.centralizer (A : Set G)) J)
    (hJsimple : IsSimpleGroup (barOf 5 J)) (hFJ : F ≤ J) (hFB : F ≤ B) (hF1 : F ≠ ⊥)
    (hK : ∀ a ∈ A, a ≠ 1 → ∃ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer ({a} : Set G)) K ∧
      B ≤ Subgroup.normalizer (K : Set G) ∧ J ≤ K ∧ K ≤ J ⊔ GLAPPrimeCoreOf 5 K) :
    ∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ J ≤ N ⊓ J ⊔ GLAPPrimeCoreOf 5 J := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hB5 : IsPGroup 5 B := GL83.isPGroup_of_isElemAbelian hBel
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => elemAbelian_comm hBel ha hb
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h] at hA25
    simp at hA25
  have hBne : B ≠ ⊥ := fun h => hAne (le_bot_iff.1 (h ▸ hAB))
  obtain ⟨d, hdA, hd1⟩ : ∃ d ∈ A, d ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAne
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨U, hU0, hU2, hBU'⟩ := hBU
  let 𝒮 : Set (Subgroup G) :=
    {T' | IsPGroup 2 T' ∧ B ≤ Subgroup.normalizer (T' : Set G) ∧ U ≤ T'}
  obtain ⟨T, hTS, hTmax⟩ := (Set.toFinite 𝒮).exists_maximalFor id 𝒮 ⟨U, hU2, hBU', le_rfl⟩
  obtain ⟨hT2, hBT, hUT⟩ := hTS
  have hTne : T ≠ ⊥ := fun h => hU0 (le_bot_iff.1 (h ▸ hUT))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax ⟨h2, hN, hUT.trans hle⟩ hle) hle
  obtain ⟨A₀, hA₀B, hA₀i, hne⟩ :=
    (GL83.I_33_1_proved G hchar 5 hp hp2 B T hBne hBel hT2 hBT (Or.inl ⟨hTne, hmax⟩)).1 d
      (hAB hdA) hd1
  obtain ⟨a, haA, haA₀, ha1⟩ : ∃ a ∈ A, a ∈ A₀ ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A₀ ⊓ A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact hcon x hx.2 hx.1
    have h1 : (A₀ ⊓ A).relIndex A = Nat.card A := by rw [hbot, Subgroup.relIndex_bot_left]
    have h2 : (A₀ ⊓ A).relIndex A = A₀.relIndex A := Subgroup.inf_relIndex_right _ _
    have h3 : A₀.relIndex A ≤ A₀.relIndex B :=
      Subgroup.relIndex_le_of_le_right hAB (by change (A₀.subgroupOf B).index ≠ 0; rw [hA₀i]; norm_num)
    have h4 : A₀.relIndex B = 5 := hA₀i
    omega
  set X : Subgroup G := T ⊓ Subgroup.centralizer (A₀ : Set G) with hXdef
  have hBC : B ≤ Subgroup.centralizer (A₀ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hBcomm b hb x (hA₀B hx) |>.symm
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun b hb =>
    mem_normalizer_inf (hBT hb) (Subgroup.le_normalizer (hBC hb))
  have hdd : Subgroup.zpowers d ≤ B := Subgroup.zpowers_le.2 (hAB hdA)
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (X : Set G) := hdd.trans hBX
  have hBd : B ≤ Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    have h : Commute d b := hBcomm d (hAB hdA) b hb
    exact (Commute.zpow_left h n).eq
  have hBdn : B ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    hBd.trans (Subgroup.centralizer_le_normalizer _)
  have hX2 : IsPGroup 2 X := hT2.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers d)) (Nat.card X) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hBel.2 d (hAB hdA)) hd1]
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hsolv : Group.IsSolvable X := by
    have := IsPGroup.isNilpotent hX2
    infer_instance
  have hdouble : ⁅⁅X, Subgroup.zpowers d⁆, Subgroup.zpowers d⁆ = ⁅X, Subgroup.zpowers d⁆ :=
    GL83.commutator_double_eq_self (Subgroup.zpowers d) X hdN hcop hsolv
  set S : Subgroup G := ⁅X, Subgroup.zpowers d⁆ with hSdef
  have hSne : S ≠ ⊥ := by rwa [hSdef, Subgroup.commutator_comm]
  have hSX : S ≤ X := GL83.commutator_le_of_le_normalizer hdN
  have hBS : B ≤ Subgroup.normalizer (S : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer B X (Subgroup.zpowers d) hBX
      hBdn
  have hS2 : IsPGroup 2 S := hT2.to_le (hSX.trans inf_le_left)
  have hSCa : S ≤ Subgroup.centralizer ({a} : Set G) :=
    hSX.trans (inf_le_right.trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA₀)))
  obtain ⟨K, hKc, hBK, hJK, hKcov⟩ := hK a haA ha1
  set P := GLAPPrimeCoreOf 5 K with hPdef
  have hPK : P ≤ K := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 5 K
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := le_normalizer_glaPPrimeCoreOf 5 K
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := b0_le_normalizer_core hBK
  have hP5 : ¬ 5 ∣ Nat.card P := not_dvd_card_glaPPrimeCoreOf hp K
  have hBCa : B ≤ Subgroup.centralizer ({a} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hBcomm a (hAB haA) b hb
  have hSK : S ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_input11_6 h116 hKp hp hp2 (hcentne a ha1) hBCa hSCa hBsc
      (hrank a (hAB haA) ha1) hS2 hBS hKc
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAB.trans hBK
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := b0_le_normalizer_core hAK
  have hAtriv : ∀ g ∈ A, ∀ k ∈ K, k * g * k⁻¹ * g⁻¹ ∈ P :=
    b5_trivial_of_cover hJK hKcov hJ.1 hAK
  have hATr : A ≤ centralizerQuot K P := fun g hg => ⟨hAK hg, hAP hg, hAtriv g hg⟩
  have hPTr : P ≤ centralizerQuot K P := by
    intro p hp'
    refine ⟨Subgroup.le_normalizer (hPK hp'), Subgroup.le_normalizer hp', fun k hk => ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hKP hk) p).1 hp'
    exact P.mul_mem h1 (P.inv_mem hp')
  have hSTr : S ≤ centralizerQuot K P := by
    calc S = ⁅S, Subgroup.zpowers d⁆ := hdouble.symm
      _ ≤ centralizerQuot K P := by
        refine Subgroup.commutator_le.2 fun s hs t ht => ?_
        have htT : t ∈ centralizerQuot K P := hATr ((Subgroup.zpowers_le.2 hdA) ht)
        have h1 := b5_mem_triv_conj (hSK hs) (b0_le_normalizer_core hSK hs) htT
        rw [commutatorElement_def]
        exact (centralizerQuot K P).mul_mem h1 ((centralizerQuot K P).inv_mem htT)
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := fun s hs => b0_le_normalizer_core hSK hs
  have hBW : B ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G) := fun b hb =>
    b5_mem_normalizer_sup (hBP hb) (hBS hb)
  obtain ⟨R, hRW, hR2, hR1, hBR, hRcard⟩ := b5_exists_R hSP hS2 hSne hP5 hB5 hBW
  have hWTr : P ⊔ S ≤ centralizerQuot K P := sup_le hPTr hSTr
  have hRTr : R ≤ centralizerQuot K P := hRW.trans hWTr
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := fun r hr => (hRTr hr).2.1
  have hRtriv : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ * r⁻¹ ∈ P := fun k hk r hr => (hRTr hr).2.2 k hk
  have hfr := b5_frattini hRP hRtriv (b5_card_R_eq hRW hRcard)
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hNdef
  have hN : IsTwoLocal N := ⟨R, hR1, hR2, rfl⟩
  have hBN : B ≤ N := hBR
  have hcov1 : ∀ k ∈ K, ∃ n ∈ N ⊓ K, ∃ q ∈ P, k = n * q := by
    intro k hk
    obtain ⟨q, hq, hqk⟩ := hfr k hk
    have hnK : q⁻¹ * k ∈ K := K.mul_mem (K.inv_mem (hPK hq)) hk
    refine ⟨q⁻¹ * k, ⟨hqk, hnK⟩, (q⁻¹ * k)⁻¹ * q * (q⁻¹ * k), ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.1 (hKP (K.inv_mem hnK)) q).1 hq
    simpa using this
  have hU := b5_lift (hB5.to_le hAB) hKP hP5 (hAB.trans hBN) hAK hAP hAtriv hcov1
  set Z' := K ⊓ Subgroup.centralizer (A : Set G) with hZ'
  have hJZ' : J ≤ Z' := le_inf hJK hJ.1
  have hJZ : GLAPComponent 5 Z' J := glaPComponent_of_le hp hJ hJZ' inf_le_right
  have hcovZ : Z' ≤ J ⊔ GLAPPrimeCoreOf 5 Z' := by
    intro z hz
    obtain ⟨j, hj, q, hq, hjq⟩ := b0_exists_mul_of_le_sup hJK hKcov z hz.1
    have hqZ : q ∈ Z' := by
      have : q = j⁻¹ * z := by rw [← hjq]; group
      rw [this]; exact Z'.mul_mem (Z'.inv_mem (hJZ' hj)) hz
    have hqO : q ∈ GLAPPrimeCoreOf 5 Z' := by
      have := gLAPPrimeCoreOf_inf_le hp K Z' ⟨hq, hqZ⟩
      rwa [inf_eq_right.2 (inf_le_left : Z' ≤ K)] at this
    rw [← hjq]; exact Subgroup.mul_mem_sup hj hqO
  have hJnorm : Z' ≤ Subgroup.normalizer (J : Set G) := b5_le_normalizer_of_cover hJZ hcovZ
  set I₁ := N ⊓ J with hI₁
  have hFN : F ≤ N := hFB.trans hBN
  have hFI : F ≤ I₁ := le_inf hFN hFJ
  have hI₁K : I₁ ≤ K := inf_le_right.trans hJK
  set W := P ⊔ I₁ with hW
  have hI₁P : I₁ ≤ Subgroup.normalizer (P : Set G) := fun i hi => hKP (hI₁K hi)
  have hWK : W ≤ K := sup_le hPK hI₁K
  have hPW : P ≤ W := le_sup_left
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := by
    intro k hk
    obtain ⟨u, hu, p', hp', rfl⟩ := hU k hk
    have huN : u ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hu.1.1
    have huZ : u ∈ Z' := ⟨hu.1.2, hu.2⟩
    have huJ : u ∈ Subgroup.normalizer (J : Set G) := hJnorm huZ
    have huI : u ∈ Subgroup.normalizer (I₁ : Set G) := mem_normalizer_inf huN huJ
    have huP : u ∈ Subgroup.normalizer (P : Set G) := hKP hu.1.2
    have huW : u ∈ Subgroup.normalizer (W : Set G) := b5_mem_normalizer_sup huP huI
    exact (Subgroup.normalizer (W : Set G)).mul_mem huW (Subgroup.le_normalizer (hPW hp'))
  have hFnP : ¬ F ≤ P := by
    intro hFP
    apply hF1
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    have h1 : orderOf f ∣ 5 := orderOf_dvd_of_pow_eq_one (hBel.2 f (hFB hf))
    have h2 : orderOf f ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P (hFP hf)
    have hcop' : Nat.Coprime 5 (Nat.card P) := (Nat.Prime.coprime_iff_not_dvd hp).2 hP5
    have := Nat.eq_one_of_dvd_coprimes hcop' h1 h2
    exact orderOf_eq_one_iff.1 this
  have hWK' : W = K := by
    rcases b5_sim hJK hKcov hJsimple hPW hWK hKW with h | h
    · exact absurd ((hFI.trans (le_sup_right : I₁ ≤ W)).trans h.le) hFnP
    · exact h
  refine ⟨N, hN, hBN, fun j hj => ?_⟩
  have hjW : j ∈ W := hWK' ▸ hJK hj
  obtain ⟨p', hp', i, hi, hpi⟩ := b5_mem_sup_mul hI₁P j hjW
  have hiJ : i ∈ J := hi.2
  have h1 : i⁻¹ * j ∈ P := by
    have e : i⁻¹ * j = i⁻¹ * p' * i := by rw [← hpi]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 (hKP (K.inv_mem (hI₁K hi))) p').1 hp'
    simpa using this
  have h2 : i⁻¹ * j ∈ J := J.mul_mem (J.inv_mem hiJ) hj
  have h3 : i⁻¹ * j ∈ GLAPPrimeCoreOf 5 J := by
    have := gLAPPrimeCoreOf_inf_le hp K J ⟨h1, h2⟩
    rwa [inf_eq_right.2 hJK] at this
  have e2 : j = i * (i⁻¹ * j) := by group
  rw [e2]
  exact Subgroup.mul_mem_sup hi h3

omit [Finite G] in
theorem b4_le_core_of_barX_eq_bot {p : ℕ} {C S : Subgroup G} (hSC : S ≤ C)
    (h : barX p C S = ⊥) : S ≤ GLAPPrimeCoreOf p C := by
  intro s hs
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨s, hSC hs⟩ ∈ barX p C S :=
    ⟨⟨s, hSC hs⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact ⟨⟨s, hSC hs⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩

omit [Finite G] in
theorem b4_isPGroup_barX {p r : ℕ} {C X : Subgroup G} (hXC : X ≤ C) (hX : IsPGroup r X) :
    IsPGroup r (barX p C X) :=
  (hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXC).symm).map _

theorem iv_core (hchar : IsCharTwoType G) {A B J F N : Subgroup G}
    (hBel : IsElemAbelian 5 B) (hAB : A ≤ B) (hA : A ≠ ⊥)
    (hN : IsTwoLocal N) (hBN : B ≤ N)
    (hJ : J ≤ Subgroup.centralizer (A : Set G)) (hFJ : F ≤ J) (hFB : F ≤ B) (hF1 : F ≠ ⊥)
    (hJN : J ≤ N ⊓ J ⊔ GLAPPrimeCoreOf 5 J)
    (hK : ∀ d ∈ A, d ≠ 1 → ∃ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer ({d} : Set G)) K ∧ J ≤ K ∧
      K ≤ J ⊔ GLAPPrimeCoreOf 5 K) :
    ∃ D : Subgroup G, D ≤ A ∧ (D.subgroupOf A).index = 5 ∧
      Even (Nat.card ↥(⁅B, GLADelta 5 D⁆ : Subgroup G)) := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  set I := N ⊓ J with hI
  have hIJ : I ≤ J := inf_le_right
  have hIN : I ≤ N := inf_le_left
  have hFN : F ≤ N := hFB.trans hBN
  have hFCA : F ≤ Subgroup.centralizer (A : Set G) := hFJ.trans hJ
  have hFp : IsPGroup 5 F := GL83.isPGroup_of_isElemAbelian (isElemAbelian_mono hBel hFB)
  have hnot : ¬ IsPGroup 2 F := by
    intro h2
    apply hF1
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    exact GL83.eq_one_of_pow_prime_of_pGroup_two hp hp2 h2 hf (hBel.2 f (hFB hf))
  have hA5 : IsElemAbelian 5 A := isElemAbelian_mono hBel hAB
  obtain ⟨D, hDA, hDidx, hne⟩ := GL83.I_33_3_proved G hchar 5 hp hp2 N A F hN hA hA5
    (hAB.trans hBN) (le_inf hFN hFCA) hnot
  refine ⟨D, hDA, hDidx, ?_⟩
  set X := pCoreOf 2 N ⊓ Subgroup.centralizer (D : Set G) with hXdef
  have hO2 : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hX2 : IsPGroup 2 X := hO2.to_le inf_le_left
  have hFD : F ≤ Subgroup.centralizer (D : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hAB (hDA hd)) (hFB hf)
  have hID : I ≤ Subgroup.centralizer (D : Set G) :=
    (hIJ.trans hJ).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDA))
  have hFX : F ≤ Subgroup.normalizer (X : Set G) := fun f hf =>
    mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N (hFN hf))
      (Subgroup.le_normalizer (hFD hf))
  have hIX : I ≤ Subgroup.normalizer (X : Set G) := fun i hi =>
    mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N (hIN hi))
      (Subgroup.le_normalizer (hID hi))
  have hcop : Nat.Coprime (Nat.card F) (Nat.card X) := by
    obtain ⟨a, ha⟩ := hFp.exists_card_eq
    obtain ⟨b, hb⟩ := hX2.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hsolv : Group.IsSolvable X := by
    have := IsPGroup.isNilpotent hX2
    infer_instance
  have hdouble : ⁅⁅X, F⁆, F⁆ = ⁅X, F⁆ := GL83.commutator_double_eq_self F X hFX hcop hsolv
  set S := ⁅I, X⁆ with hS
  have hFI : F ≤ I := le_inf hFN hFJ
  have hXO : X ≤ pCoreOf 2 N := inf_le_left
  have hSO : S ≤ pCoreOf 2 N := by
    refine Subgroup.commutator_le.2 fun i hi x hx => ?_
    have hxO : x ∈ pCoreOf 2 N := hXO hx
    have hnorm : pCoreOf 2 N ≤ _ := le_rfl
    have h1 : i * x * i⁻¹ ∈ pCoreOf 2 N := by
      have := (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N (hIN hi)) x).1 hxO
      exact this
    rw [commutatorElement_def]
    exact (pCoreOf 2 N).mul_mem h1 ((pCoreOf 2 N).inv_mem hxO)
  have hSΔ : S ≤ GLADelta 5 D := by
    refine le_iInf₂ fun d hd => le_iInf fun hd1 => ?_
    obtain ⟨K, hKc, hJK, hKcov⟩ := hK d (hDA hd) hd1
    set Cd := Subgroup.centralizer ({d} : Set G) with hCd
    have hXCd : X ≤ Cd := by
      intro y hy
      have h2 : y ∈ Subgroup.centralizer (D : Set G) := hy.2
      rw [Subgroup.mem_centralizer_iff] at h2 ⊢
      intro h hh
      exact h2 h (by rw [Set.mem_singleton_iff.1 hh]; exact hd)
    have hICd : I ≤ Cd := (hIJ.trans hJK).trans hKc.1
    have hIK : I ≤ K := hIJ.trans hJK
    have hOJ : GLAPPrimeCoreOf 5 J ≤ GLAPPrimeCoreOf 5 K := b0_core_le_of_cover hJK hKcov
    have hKI : K ≤ I ⊔ GLAPPrimeCoreOf 5 K := by
      refine hKcov.trans (sup_le ?_ le_sup_right)
      exact hJN.trans (sup_le le_sup_left (hOJ.trans le_sup_right))
    have hP : GLAPPrimeCoreOf 5 K ≤ GLAPPrimeCoreOf 5 Cd :=
      glaPPrimeCoreOf_le_of_isSubnormal 5 hKc.2.1
    have hle : barX 5 Cd K ≤ barX 5 Cd I := by
      refine barX_le_of_forall hICd fun k hk => ?_
      obtain ⟨i, hi, q, hq, hiq⟩ := b0_exists_mul_of_le_sup hIK hKI k hk
      refine ⟨i, hi, ?_⟩
      have : i⁻¹ * k = q := by rw [← hiq]; group
      rw [this]; exact hP hq
    have hKbar : IsComponentOf (barX 5 Cd K) ⊤ := hKc.2.2.1
    have hnormbar : barX 5 Cd K ≤ Subgroup.normalizer (barX 5 Cd X : Set _) :=
      hle.trans (barX_le_normalizer hIX)
    have hX2' : IsPGroup 2 (barX 5 Cd X) := b4_isPGroup_barX hXCd hX2
    have hcommb := commutator_eq_bot_of_normalizes hKbar hX2' hnormbar
    have hbot : barX 5 Cd ⁅I, X⁆ = ⊥ := by
      rw [barX_commutator 5 hICd hXCd]
      exact le_bot_iff.1 (hcommb ▸ Subgroup.commutator_mono (barX_mono 5 hIK) le_rfl)
    exact b4_le_core_of_barX_eq_bot (commutator_le_of_le' hICd hXCd) hbot
  have hT : ⁅X, F⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm] at hne
  have hTS : ⁅X, F⁆ ≤ S := by
    rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mono hFI le_rfl
  have hBS_ne : ⁅B, S⁆ ≠ ⊥ := by
    intro hbot
    apply hT
    have h1 : ⁅⁅X, F⁆, F⁆ ≤ ⁅S, B⁆ := Subgroup.commutator_mono hTS hFB
    rw [Subgroup.commutator_comm S B, hbot, hdouble] at h1
    exact le_bot_iff.1 h1
  have hBS2 : IsPGroup 2 ↥(⁅B, S⁆ : Subgroup G) := by
    refine hO2.to_le ?_
    refine Subgroup.commutator_le.2 fun b hb s hs => ?_
    have hsO : s ∈ pCoreOf 2 N := hSO hs
    have h1 : b * s * b⁻¹ ∈ pCoreOf 2 N :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N (hBN hb)) s).1 hsO
    rw [commutatorElement_def]
    exact (pCoreOf 2 N).mul_mem h1 ((pCoreOf 2 N).inv_mem hsO)
  have hBSΔ : ⁅B, S⁆ ≤ ⁅B, GLADelta 5 D⁆ := Subgroup.commutator_mono le_rfl hSΔ
  obtain ⟨k, hk⟩ := hBS2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hBS_ne
    exact Subgroup.card_eq_one.1 (by rw [hk]; simp)
  have hdvd : 2 ∣ Nat.card ↥(⁅B, GLADelta 5 D⁆ : Subgroup G) := by
    have h2 : 2 ∣ Nat.card ↥(⁅B, S⁆ : Subgroup G) := by rw [hk]; exact dvd_pow_self 2 hk0
    exact h2.trans (Subgroup.card_dvd_of_le hBSΔ)
  exact even_iff_two_dvd.2 hdvd

omit [Finite G] in
theorem b6_centralizer_ne_top (hS : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {D : Subgroup G} (hD : D ≠ ⊥) : Subgroup.centralizer (D : Set G) ≠ ⊤ := by
  intro htop
  have hc : D ≤ Subgroup.center G := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer (D : Set G) := by rw [htop]; exact Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.1 this) d hd).symm
  rcases Subgroup.Normal.eq_bot_or_eq_top (G := G) (Subgroup.center G) with h | h
  · exact hD (le_bot_iff.1 (h ▸ hc))
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

end Lemma43Rest

open Lemma43Rest in
theorem lemma43_of_inputs (hF : Fi22Facts) (h112 : Input11_2) (h23 : Lemma23)
    (h116 : Input11_6) (h183 : Input18_3_4) (h1420 : Input14_20_7) : Lemma43 := by
  intro G _ _ m p hS hp5 B hB b hb hb1 L hL hM
  subst hp5
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hi := lemma43_i_of_facts hF h112 h23 hS hB hb hL hM
  have hBel : IsElemAbelian 5 B := hB.1.1
  have hB5 : IsPGroup 5 B := GL83.isPGroup_of_isElemAbelian hBel
  have hBcomm : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc => elemAbelian_comm hBel ha hc
  have hrank0 : ∀ X : Subgroup G, GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B := fun X =>
    (glaTwoLocalRank_subgroup_le hp X).trans (hS.rank_eq.le.trans (hS.le_pRank' hB))
  have hnormB : ∀ D : Subgroup G, D ≤ B → ∀ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer (D : Set G)) K → B ≤ Subgroup.normalizer (K : Set G) := by
    intro D hDB K hK
    by_contra hn
    have hBC : B ≤ Subgroup.centralizer (D : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact hBcomm d (hDB hd) x hx
    have := (h112 G m 5 hS _ B K hBel hBC (hrank0 _) hK hn).1
    omega
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := by
    have := hnormB (Subgroup.zpowers b) (Subgroup.zpowers_le.2 hb) L (by
      rw [b3_centralizer_zpowers]; exact hL)
    exact this
  set A := cBarB 5 B L with hAdef
  have hAB : A ≤ B := inf_le_left
  have hAel : IsElemAbelian 5 A := isElemAbelian_mono hBel hAB
  have hAp : IsPGroup 5 A := GL83.isPGroup_of_isElemAbelian hAel
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hAB.trans hBN
  have hAtriv : A ≤ centralizerQuot L (GLAPPrimeCoreOf 5 L) := inf_le_right
  have hbA : b ∈ A := by
    refine ⟨hb, hBN hb, b0_le_normalizer_core (Subgroup.zpowers_le.2 (hBN hb))
      (Subgroup.mem_zpowers b), fun x hx => ?_⟩
    have h1 : b * x = x * b := (Subgroup.mem_centralizer_iff.1 (hL.1 hx)) b rfl
    have e : x * b * x⁻¹ * b⁻¹ = 1 := by rw [← h1]; group
    rw [e]; exact (GLAPPrimeCoreOf 5 L).one_mem
  have hFcard : Nat.card ↥(B ⊓ L) = 25 := by
    have := hi.2.2.1.2
    simpa using this
  have hcardB : Nat.card B = 5 ^ m := hS.card_eq hB
  have hA25 : 25 ≤ Nat.card A := by
    have h1 := card_sup_eq_mul_of_commute (A := A) (F := B ⊓ L)
      (fun a ha f hf => hBcomm a (hAB ha) f hf.1) hi.2.1
    rw [hi.1, hcardB, hFcard] at h1
    have h2 : 5 ^ 4 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hS.four_le
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h] at hA25
    simp at hA25
  obtain ⟨hZ, hv, hord, hInn⟩ := hF (barOf 5 L) hM
  have hLq : CFSG.Open.IsQuasisimple (barOf 5 L) := b0_isQuasisimple_bar hL
  have hsimple : IsSimpleGroup (barOf 5 L) := by
    have e : barOf 5 L ⧸ Subgroup.center (barOf 5 L) ≃* barOf 5 L ⧸ (⊥ : Subgroup (barOf 5 L)) :=
      QuotientGroup.congr _ _ (MulEquiv.refl _) (by rw [hZ]; simp)
    exact (e.trans (QuotientGroup.quotientBot)).isSimpleGroup_congr.1 hLq.2
  have hnab : ∃ a c : barOf 5 L, a * c ≠ c * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : barOf 5 L)
    apply hx
    have : x ∈ Subgroup.center (barOf 5 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hcon g x)
    rw [hZ] at this
    exact Subgroup.mem_bot.1 this
  obtain ⟨J, hJcomp, hJlayer, ⟨eJL⟩, hJF⟩ := exists_J_structure hAp hAN hAtriv hsimple hnab
  rw [hJlayer]
  have hCAb : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbA)
  have hJsn : IsSubnormal (L ⊓ Subgroup.centralizer (A : Set G)) (Subgroup.centralizer (A : Set G)) := by
    have := isSubnormal_inf hL.2.1 (Subgroup.centralizer (A : Set G))
    rwa [inf_eq_right.2 hCAb] at this
  have hJC : GLAPComponent 5 (Subgroup.centralizer (A : Set G)) J :=
    glaPComponent_of_isSubnormal hp hJsn hJcomp
  have hJfi : IsFiTwentyTwo (barOf 5 J) := by
    obtain ⟨f⟩ := hM
    exact ⟨eJL.trans f⟩
  have hJsimple : IsSimpleGroup (barOf 5 J) := eJL.isSimpleGroup_congr.2 hsimple
  have hJnp : ¬ IsPGroup 5 (barOf 5 J) := by
    intro h5
    have h5' : IsPGroup 5 (barOf 5 L) := h5.of_injective eJL.symm.toMonoidHom eJL.symm.injective
    obtain ⟨k, hk⟩ := h5'.exists_card_eq
    have hk2 : k = 2 := by
      have := hv
      rw [hk, Nat.Prime.factorization_pow hp] at this
      simpa using this
    subst hk2
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
    obtain ⟨a, c, hac⟩ := hnab
    exact hac (mul_comm a c)
  have hFp : IsPGroup 5 (B ⊓ L : Subgroup G) :=
    GL83.isPGroup_of_isElemAbelian (isElemAbelian_mono hBel inf_le_left)
  have hFA : B ⊓ L ≤ L ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_inf inf_le_right fun f hf => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hBcomm a (hAB ha) f hf.1
  have hFJ : B ⊓ L ≤ J := hJF _ hFp hFA
  have hF1 : (B ⊓ L : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h] at hFcard
    simp at hFcard
  have hcent : ∀ D : Subgroup G, D ≠ ⊥ → Subgroup.centralizer (D : Set G) ≠ ⊤ := fun D hD =>
    b6_centralizer_ne_top hS.simple hS.nonabelian hD
  have hX : ∀ D : Subgroup G, D ≤ A → D ≠ ⊥ →
      CFSG.Open.IsKGroup ↥(Subgroup.centralizer (D : Set G)) :=
    fun D _ hD => isKGroup_of_isKProper hS.kProper (hcent D hD)
  have hnorm : ∀ D : Subgroup G, D ≤ A → D ≠ ⊥ → ∀ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer (D : Set G)) K → A ≤ Subgroup.normalizer (K : Set G) :=
    fun D hDA _ K hK => hAB.trans (hnormB D (hDA.trans hAB) K hK)
  have hT := tprop h183 h1420 hAel hX hnorm hJC hJfi hJnp
  have hzne : ∀ a : G, a ≠ 1 → Subgroup.zpowers a ≠ ⊥ := by
    intro a ha1 h
    apply ha1
    have := Subgroup.mem_zpowers a
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have hKa : ∀ a ∈ A, a ≠ 1 → ∃ K : Subgroup G,
      GLAPComponent 5 (Subgroup.centralizer ({a} : Set G)) K ∧
      B ≤ Subgroup.normalizer (K : Set G) ∧ J ≤ K ∧ K ≤ J ⊔ GLAPPrimeCoreOf 5 K ∧
      K = ⨆ g ∈ GLAPLayer 5 (Subgroup.centralizer ({a} : Set G)), GLBConj g J := by
    intro a ha ha1
    obtain ⟨K, hK, hJK, hcov, hKeq⟩ := hT (Subgroup.zpowers a) (Subgroup.zpowers_le.2 ha)
      (hzne a ha1)
    have hBK := hnormB _ ((Subgroup.zpowers_le.2 ha).trans hAB) K hK
    rw [b3_centralizer_zpowers] at hK hKeq
    exact ⟨K, hK, hBK, hJK, hcov, hKeq⟩
  have hrank : ∀ a ∈ B, a ≠ 1 → GLATwoLocalRank 5 ↥(Subgroup.centralizer ({a} : Set G)) ≤
      CFSG.Open.pRank 5 (B.subgroupOf (Subgroup.centralizer ({a} : Set G))) := by
    intro a ha _
    have hBC : B ≤ Subgroup.centralizer ({a} : Set G) := le_centralizer_of_mem hBel ha
    have hE := CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hBel
      (Subgroup.centralizer ({a} : Set G))
    have hcard : Nat.card ↥(B.subgroupOf (Subgroup.centralizer ({a} : Set G))) = 5 ^ m := by
      rw [← hS.card_eq hB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
    rw [pRank_eq_of_card hp hE hcard]
    exact (glaTwoLocalRank_subgroup_le hp _).trans hS.rank_eq.le
  have hcentne : ∀ a : G, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
    intro a ha1
    have := hcent (Subgroup.zpowers a) (hzne a ha1)
    rwa [b3_centralizer_zpowers] at this
  obtain ⟨N, hN2, hBN', hJN⟩ := iii_core hS.charTwo hS.kProper h116 hBel hB.1.2.2
    (h23 G m 5 hS B hB) hAB hA25 hcentne hrank hJC hJsimple hFJ inf_le_left hF1
    (fun a ha ha1 => by
      obtain ⟨K, h1, h2, h3, h4, -⟩ := hKa a ha ha1
      exact ⟨K, h1, h2, h3, h4⟩)
  refine ⟨hi, ?_, ⟨N, hN2, hBN', hJN⟩, ?_⟩
  · intro a ha ha1
    obtain ⟨K, hKc, -, -, hcov, hKeq⟩ := hKa a ha ha1
    rw [← hKeq]; exact ⟨hKc, hcov⟩
  · exact iv_core hS.charTwo hBel hAB hAne hN2 hBN' hJC.1 hFJ inf_le_left hF1 hJN
      (fun a ha ha1 => by
        obtain ⟨K, h1, -, h3, h4, -⟩ := hKa a ha ha1
        exact ⟨K, h1, h3, h4⟩)


end CFSG.HardMathSupport.Solomon.LocalBalance
