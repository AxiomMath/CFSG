module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13e
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13f
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Ii
public import CFSG.LocalAnalysis.GLTheoremB.Input27_9_3Proof
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Four

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped MatrixGroups

open Sec13e (Input22_3 Input7_1Aut)

namespace Lemma1311

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCore_quot_eq_bot (p : ℕ) [Fact p.Prime] (X : Type) [Group X] [Finite X] :
    GLAPPrimeCore p (X ⧸ GLAPPrimeCore p X) = ⊥ := by
  refine (CFSG.pPrimeCore_eq_bot_iff).2 ?_
  intro K hK hcop
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
  have hPn : (K.comap (QuotientGroup.mk' (GLAPPrimeCore p X))).Normal :=
    Subgroup.Normal.comap hK _
  have hcard : Nat.card (K.comap (QuotientGroup.mk' (GLAPPrimeCore p X))) =
      Nat.card (GLAPPrimeCore p X) * Nat.card K := by
    have h1 := QuotientGroup.card_preimage_mk (GLAPPrimeCore p X)
      (K : Set (X ⧸ GLAPPrimeCore p X))
    have h2 : Nat.card ↥(K.comap (QuotientGroup.mk' (GLAPPrimeCore p X))) =
        (QuotientGroup.mk ⁻¹' (K : Set (X ⧸ GLAPPrimeCore p X))).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [h2, ← Nat.card_coe_set_eq, h1]
    rfl
  have hPcop : Nat.Coprime p (Nat.card (K.comap (QuotientGroup.mk' (GLAPPrimeCore p X)))) := by
    rw [hcard]
    exact Nat.Coprime.mul_right CFSG.pPrimeCore_coprime_card hcop
  have hle : K.comap (QuotientGroup.mk' (GLAPPrimeCore p X)) ≤ GLAPPrimeCore p X :=
    le_sSup ⟨hPn, hPcop⟩
  have hx : x ∈ GLAPPrimeCore p X := hle hk
  exact (QuotientGroup.eq_one_iff x).2 hx

theorem glaPPrimeCoreOf_top_eq_bot {p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
  have hiso := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)
  rw [hY] at hiso
  have h1 : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hm : (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y) x ∈
        (GLAPPrimeCore p ↥(⊤ : Subgroup Y)).map
          (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hiso, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).injective (hm.trans (map_one _).symm)
  unfold GLAPPrimeCoreOf
  rw [h1, Subgroup.map_bot]

theorem glaPPrimeCore_sub_eq_bot {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) {S : Subgroup Y} (hS : IsSubnormal S ⊤) :
    GLAPPrimeCore p ↥S = ⊥ := by
  have h1 : GLAPPrimeCoreOf p S ≤ GLAPPrimeCoreOf p (⊤ : Subgroup Y) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hS
  rw [glaPPrimeCoreOf_top_eq_bot hY] at h1
  rw [eq_bot_iff]
  intro x hx
  have hm : (x : Y) ∈ GLAPPrimeCoreOf p S := Subgroup.mem_map_of_mem S.subtype hx
  have := h1 hm
  rw [Subgroup.mem_bot] at this ⊢
  exact Subtype.ext this

theorem eq_bot_of_subnormal_pPrime {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) {S : Subgroup Y} (hS : IsSubnormal S ⊤)
    (hcop : Nat.Coprime p (Nat.card ↥S)) : S = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hself : (⊤ : Subgroup ↥S) ≤ GLAPPrimeCore p ↥S := by
    refine le_sSup ⟨Subgroup.normal_top, ?_⟩
    simpa using hcop
  have hS_le : S ≤ GLAPPrimeCoreOf p S := by
    unfold GLAPPrimeCoreOf
    intro s hs
    exact ⟨⟨s, hs⟩, hself (Subgroup.mem_top _), rfl⟩
  have h2 : GLAPPrimeCoreOf p S ≤ GLAPPrimeCoreOf p (⊤ : Subgroup Y) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hS
  rw [glaPPrimeCoreOf_top_eq_bot hY] at h2
  exact le_bot_iff.1 (hS_le.trans h2)

theorem glaPComponent_of_normal {p : ℕ} (hp : p.Prime) {T N K : Subgroup G} (hNT : N ≤ T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hK : GLAPComponent p N K) :
    GLAPComponent p T K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNnorm : (N.subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hTN g.2) (n : G)).1 hn
    simpa using this
  have hNsn : IsSubnormal N T := IsSubnormal.step hNT hNnorm (IsSubnormal.refl T)
  have hBn : (barX p T N).Normal := by
    unfold barX
    exact Subgroup.Normal.map hNnorm _ (QuotientGroup.mk'_surjective _)
  have hKN : K ≤ N := hK.1
  have hKT : K ≤ T := hKN.trans hNT
  have hKsn : IsSubnormal K T := isSubnormal_trans' hK.2.1 hNsn
  have hbar := Prop115b.barX_glaPComponent_of_le hp hNT hK
  have hSB : barX p T K ≤ barX p T N := hbar.1
  have hSsn : IsSubnormal (barX p T K) (barX p T N) := hbar.2.1
  have hBtop : IsSubnormal (barX p T N) (⊤ : Subgroup (↥T ⧸ GLAPPrimeCore p ↥T)) :=
    isSubnormal_of_normal hBn
  have hSsnTop : IsSubnormal (barX p T K) (⊤ : Subgroup (↥T ⧸ GLAPPrimeCore p ↥T)) :=
    isSubnormal_trans' hSsn hBtop
  have hcompS : IsComponentOf (barX p T K) ⊤ := by
    refine ⟨le_top, hSsnTop, ?_⟩
    have hbc : IsComponentOf (barX p (barX p T N) (barX p T K)) ⊤ := hbar.2.2.1
    have e1 : (↥(barX p T K) ⧸ GLAPPrimeCore p ↥(barX p T K)) ≃* ↥(barX p (barX p T N) (barX p T K)) :=
      quotEquivBarX hp hSB hSsn
    have hO : GLAPPrimeCore p ↥(barX p T K) = ⊥ :=
      glaPPrimeCore_sub_eq_bot hp (glaPPrimeCore_quot_eq_bot p ↥T) hSsnTop
    have e2 : (↥(barX p T K) ⧸ GLAPPrimeCore p ↥(barX p T K)) ≃* ↥(barX p T K) :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (e1.symm.trans e2) hbc.2.2
  refine ⟨hKT, hKsn, hcompS, ?_⟩
  intro J hJK hJT heq
  have hJN : J ≤ N := hJK.le.trans hKN
  have hJNsn : IsSubnormal J N := by
    have h := isSubnormal_inf hJT N
    rwa [inf_eq_left.2 hJN, inf_eq_right.2 hNT] at h
  exact hK.2.2.2 J hJK hJNsn (barX_eq_of_barX_eq hp hNT hJN hKN heq)

section Gen

variable {p : ℕ}

theorem barX_mono' (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem mem_barX' (p : ℕ) {X S : Subgroup G} {y : ↥X ⧸ GLAPPrimeCore p ↥X} :
    y ∈ barX p X S ↔ ∃ x : ↥X, (x : G) ∈ S ∧ QuotientGroup.mk' (GLAPPrimeCore p ↥X) x = y := by
  unfold barX
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩

abbrev SummandP (p : ℕ) (M D L : Subgroup G) : Prop :=
  GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
    Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))

theorem Iof_eq_iSup_summand (p : ℕ) (M D : Subgroup G) :
    Iof p M D = ⨆ x : {L0 : Subgroup G // SummandP p M D L0}, x.1 := by
  unfold Iof
  exact le_antisymm (iSup₂_le fun L0 h => le_iSup_of_le ⟨L0, h⟩ le_rfl)
    (iSup_le fun x => le_iSup₂_of_le x.1 x.2 le_rfl)

theorem summand_conj_pComp (hp : p.Prime) {M D : Subgroup G} {g : G} (hg : g ∈ M)
    (x : {L0 : Subgroup G // SummandP p M D L0}) :
    GLAPComponent p (Istar p M D) (GLBConj g x.1) := by
  have hxc : GLAPComponent p M x.1 := x.2.1
  have hxI : x.1 ≤ Iof p M D := by
    rw [Iof_eq_iSup_summand]
    exact le_iSup (fun x : {L0 : Subgroup G // SummandP p M D L0} => x.1) x
  have hle : GLBConj g x.1 ≤ Istar p M D :=
    le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g (Iof p M D)) g hg
      (gLBConj_mono g hxI)
  have hgc : GLAPComponent p M (GLBConj g x.1) := glaPComponent_conj_mem hxc hg
  exact glaPComponent_of_le hp hgc hle (istar_le_M p M D)

theorem istar_le_iSup_pComp (hp : p.Prime) (M D : Subgroup G) :
    Istar p M D ≤ ⨆ (y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}), y.1 := by
  refine iSup₂_le fun g hg => ?_
  have h2 : GLBConj g (Iof p M D) ≤ ⨆ (y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}), y.1 := by
    rw [Iof_eq_iSup_summand]
    refine (gLBConj_iSup_eq g _).le.trans (iSup_le fun x => ?_)
    exact le_iSup_of_le ⟨GLBConj g x.1, summand_conj_pComp hp hg x⟩ le_rfl
  exact h2

theorem barX_istar_le_iSup_pComp (hp : p.Prime) (M D : Subgroup G) :
    barX p M (Istar p M D) ≤
      ⨆ (y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}), barX p M y.1 := by
  have hX : ∀ y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}, y.1 ≤ M :=
    fun y => y.2.1.trans (istar_le_M p M D)
  have h0 : barX p M (Istar p M D) ≤
      barX p M (⨆ (y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}), y.1) :=
    barX_mono' p (X := M) (istar_le_iSup_pComp hp M D)
  have h1 : barX p M (⨆ (y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}), y.1) ≤
      ⨆ (y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}), barX p M y.1 :=
    barX_iSup_le_iSup (p := p) (C := M) (fun y : {L : Subgroup G // GLAPComponent p (Istar p M D) L} => y.1) hX
  exact h0.trans h1

theorem isComponent_barX_of_pComp (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) : IsComponentOf (barX p M L) ⊤ := by
  have hLN : L ≤ Istar p M D := hL.1
  have hLM : L ≤ M := hLN.trans (istar_le_M p M D)
  have hsnL : IsSubnormal L M := isSubnormal_trans' hL.2.1 (istar_isSubnormal p M D)
  have e : ↥(barX p M L) ≃* ↥(barX p (Istar p M D) L) :=
    (quotEquivBarX hp hLM hsnL).symm.trans (quotEquivBarX hp hLN hL.2.1)
  refine ⟨le_top, ?_, ?_⟩
  · have := isSubnormal_barX p (C := M) hsnL
    rwa [barX_self] at this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
      hL.2.2.1.2.2

noncomputable def barXIso (hp : p.Prime) {M L : Subgroup G} (hLM : L ≤ M) (hsn : IsSubnormal L M) :
    ↥(barX p M L) ≃* barOf p L :=
  (quotEquivBarX hp hLM hsn).symm

theorem isSubnormal_pComp_of_istar (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) : IsSubnormal L M :=
  isSubnormal_trans' hL.2.1 (istar_isSubnormal p M D)

end Gen

section Orbit1311

variable {X : Type} [Group X] [Finite X]

@[expose] def jSet1311 (L B K₁ : Subgroup X) : Set X :=
  {b : X | b ∈ B ∧ b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set X) ∨ b ∉ Subgroup.normalizer (K₁ : Set X))}

@[expose] def orbitSet1311 (B K₁ : Subgroup X) : Set (Subgroup X) :=
  {K | ∃ b ∈ B, GLBConj b K₁ = K}

@[expose] def orbitProd1311 (B K₁ : Subgroup X) : Subgroup X :=
  ⨆ K ∈ orbitSet1311 B K₁, K

theorem mem_orbitSet1311_self (B K₁ : Subgroup X) (hB : (1 : X) ∈ B) :
    K₁ ∈ orbitSet1311 B K₁ :=
  ⟨1, hB, gLBConj_one K₁⟩

theorem isComponentOf_orbit1311 {B K₁ K : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤)
    (hK : K ∈ orbitSet1311 B K₁) : IsComponentOf K ⊤ := by
  obtain ⟨b, -, rfl⟩ := hK
  exact isComponentOf_gLBConj hK₁ b

theorem le_orbitProd1311 {B K₁ K : Subgroup X} (hK : K ∈ orbitSet1311 B K₁) :
    K ≤ orbitProd1311 B K₁ :=
  le_iSup₂_of_le (f := fun K (_ : K ∈ orbitSet1311 B K₁) => K) K hK le_rfl

theorem orbitProd1311_le {B K₁ Y : Subgroup X} (h : ∀ K ∈ orbitSet1311 B K₁, K ≤ Y) :
    orbitProd1311 B K₁ ≤ Y :=
  iSup₂_le fun K hK => h K hK

theorem isComponentOf_orbitProd1311 {B K₁ K : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤)
    (hK : K ∈ orbitSet1311 B K₁) : IsComponentOf K (orbitProd1311 B K₁) := by
  have h := isComponentOf_orbit1311 hK₁ hK
  have hKle : K ≤ orbitProd1311 B K₁ := le_orbitProd1311 hK
  exact ⟨hKle, isSubnormal_of_le_of_le h.2.1 hKle le_top, h.2.2⟩

theorem gLBConj_orbitProd1311_le {B K₁ : Subgroup X} {b : X} (hb : b ∈ B) :
    GLBConj b (orbitProd1311 B K₁) ≤ orbitProd1311 B K₁ := by
  unfold orbitProd1311
  rw [gLBConj_iSup_eq]
  refine iSup_le fun K => ?_
  rw [gLBConj_iSup_eq]
  refine iSup_le fun hK => ?_
  obtain ⟨b₀, hb₀, rfl⟩ := hK
  rw [gLBConj_gLBConj]
  exact le_iSup₂_of_le (f := fun K (_ : K ∈ orbitSet1311 B K₁) => K) (GLBConj (b₀ * b) K₁)
    ⟨b₀ * b, B.mul_mem hb₀ hb, rfl⟩ le_rfl

theorem le_normalizer_orbitProd1311 {B K₁ : Subgroup X} :
    B ≤ Subgroup.normalizer ((orbitProd1311 B K₁ : Subgroup X) : Set X) := by
  intro b hb
  have h1 : GLBConj b (orbitProd1311 B K₁) ≤ orbitProd1311 B K₁ := gLBConj_orbitProd1311_le hb
  have h2 : GLBConj b⁻¹ (orbitProd1311 B K₁) ≤ orbitProd1311 B K₁ :=
    gLBConj_orbitProd1311_le (B.inv_mem hb)
  have h3 : orbitProd1311 B K₁ ≤ GLBConj b (orbitProd1311 B K₁) := by
    have := gLBConj_mono b h2
    rwa [gLBConj_gLBConj_inv] at this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (mem_gLBConj.1 (h3 hh))
  · intro hh
    exact h1 (mem_gLBConj.2 hh)

theorem orbit_commute1311 {B K₁ : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤) :
    ∀ K ∈ orbitSet1311 B K₁, ∀ K' ∈ orbitSet1311 B K₁, K ≠ K' → ⁅K, K'⁆ = ⊥ :=
  fun K hK K' hK' hne => Sec13e.commute_of_isComponentOf (isComponentOf_orbit1311 hK₁ hK)
    (isComponentOf_orbit1311 hK₁ hK') hne

theorem le_normalizer_orbitProd_of_comp1311 {B K₁ K : Subgroup X}
    (h : K ∈ orbitSet1311 B K₁ ∨ ∀ K'' ∈ orbitSet1311 B K₁, ⁅K, K''⁆ = ⊥) :
    K ≤ Subgroup.normalizer ((orbitProd1311 B K₁ : Subgroup X) : Set X) := by
  rcases h with hK | hcomm
  · exact (le_orbitProd1311 hK).trans Subgroup.le_normalizer
  · have hQC : orbitProd1311 B K₁ ≤ Subgroup.centralizer (K : Set X) := by
      refine orbitProd1311_le fun K'' hK'' => ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hKC : K ≤ Subgroup.centralizer (K'' : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm K'' hK'')
      exact ((Subgroup.mem_centralizer_iff.1 (hKC hk)) x hx).symm
    have hKC : K ≤ Subgroup.centralizer ((orbitProd1311 B K₁ : Subgroup X) : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact ((Subgroup.mem_centralizer_iff.1 (hQC hq)) k hk).symm
    exact hKC.trans (Subgroup.centralizer_le_normalizer _)

end Orbit1311

section Orbit1311b

variable {X : Type} [Group X] [Finite X]

@[expose] def conjRestr1311 (K : Subgroup X) (b : X)
    (hb : b ∈ Subgroup.normalizer (K : Set X)) : MulAut ↥K where
  toFun x := ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb x).1 x.2⟩
  invFun x := ⟨b⁻¹ * x * b, (Subgroup.mem_normalizer_iff.1 hb (b⁻¹ * x * b)).2 (by
    simpa [mul_assoc] using x.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

theorem jSet_nonempty1311 {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hI71 : Input7_1Aut) {B K₁ : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤)
    (hZ : Subgroup.center ↥K₁ = ⊥)
    (hT : IsAltType (p + 2) ↥K₁ ∨ (3 < p ∧ ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧
      IsOmegaTwo ε (n + 1) ↥K₁ ∧ HasFixedPointFreeOrder ε n p ∧
        CFSG.Open.pRank p (⊤ : Subgroup ↥K₁) = 1))
    (hB : IsElemAbelian p B) (hcard : p ^ 2 ≤ Nat.card ↥B) :
    ∃ b : X, b ∈ B ∧ b ≠ 1 ∧
      (b ∈ Subgroup.centralizer ((orbitProd1311 B K₁ : Subgroup X) : Set X) ∨
        b ∉ Subgroup.normalizer (K₁ : Set X)) := by
  by_cases hA : ∃ b ∈ B, b ∉ Subgroup.normalizer (K₁ : Set X)
  · obtain ⟨b, hbB, hbN⟩ := hA
    refine ⟨b, hbB, ?_, Or.inr hbN⟩
    rintro rfl
    exact hbN (Subgroup.one_mem _)
  · have hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (K₁ : Set X) := by
      intro b hb
      by_contra h
      exact hA ⟨b, hb, h⟩
    have hgl : ∀ b ∈ B, GLBConj b K₁ = K₁ := fun b hb => gLBConj_eq_of_mem_normalizer (hN b hb)
    have horb : orbitProd1311 B K₁ = K₁ := by
      have hS : orbitSet1311 B K₁ = {K₁} := by
        ext K
        constructor
        · rintro ⟨b, hb, rfl⟩
          rw [Set.mem_singleton_iff, hgl b hb]
        · intro hK
          rw [Set.mem_singleton_iff] at hK
          subst hK
          exact mem_orbitSet1311_self B _ B.one_mem
      unfold orbitProd1311
      rw [hS]
      simp
    by_cases hC : ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (K₁ : Set X)
    · obtain ⟨b, hbB, hb1, hbC⟩ := hC
      exact ⟨b, hbB, hb1, Or.inl (by rw [horb]; exact hbC)⟩
    · exfalso
      have hC' : ∀ b ∈ B, b ≠ 1 → b ∉ Subgroup.centralizer (K₁ : Set X) :=
        fun b hb hb1 hc => hC ⟨b, hb, hb1, hc⟩
      let ψ : ↥B →* MulAut ↥K₁ :=
        { toFun := fun b => conjRestr1311 K₁ (b : X) (hN b.1 b.2)
          map_one' := by
            ext x
            simp [conjRestr1311]
          map_mul' := fun a b => by
            ext x
            simp [conjRestr1311, mul_assoc] }
      have hinj : Function.Injective ψ := by
        rw [injective_iff_map_eq_one]
        intro b hb
        apply Subtype.ext
        by_contra hne
        have key : ∀ h ∈ K₁, (b : X) * h * (b : X)⁻¹ = h := by
          intro h hh
          have := congrArg (fun φ : MulAut ↥K₁ => ((φ ⟨h, hh⟩ : ↥K₁) : X)) hb
          simpa [ψ, conjRestr1311] using this
        have hcent : (b : X) ∈ Subgroup.centralizer (K₁ : Set X) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          exact (mul_inv_eq_iff_eq_mul.1 (key h hh)).symm
        exact hC' (b : X) b.2 hne hcent
      have hcardψ : Nat.card ↥(ψ.range) = Nat.card ↥B :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hE : IsElemAbelian p ψ.range := by
        apply isElemAbelian_of_comm_pow
        · rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
          rw [← map_mul, ← map_mul]
          congr 1
          exact hB.1.is_comm.comm a c
        · rintro _ ⟨a, rfl⟩
          have ha : a ^ p = 1 := Subtype.ext (hB.2 a.1 a.2)
          rw [← map_pow, ha, map_one]
      have hle := hI71 p hp hp3 ↥K₁ hK₁.2.2 hZ hT ψ.range hE
      rw [hcardψ] at hle
      nlinarith [hp.two_le]

theorem comp_le_layers1311 {p : ℕ} (hI22 : Input22_3) (hI71 : Input7_1Aut) (hp : p.Prime)
    (hp3 : 3 ≤ p) {B K₁ : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤)
    (hZ : Subgroup.center ↥K₁ = ⊥)
    (hT : IsAltType (p + 2) ↥K₁ ∨ (3 < p ∧ ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧
      IsOmegaTwo ε (n + 1) ↥K₁ ∧ HasFixedPointFreeOrder ε n p ∧
        CFSG.Open.pRank p (⊤ : Subgroup ↥K₁) = 1))
    (hB : IsElemAbelian p B) (hcard : p ^ 2 ≤ Nat.card ↥B) (hpK : p ∣ Nat.card ↥K₁) :
    K₁ ≤ ⨆ (b : X) (_ : b ∈ B ∧ b ≠ 1 ∧
        (b ∈ Subgroup.centralizer ((orbitProd1311 B K₁ : Subgroup X) : Set X) ∨
          b ∉ Subgroup.normalizer (K₁ : Set X))),
      GLAPLayer p (orbitProd1311 B K₁ ⊓ Subgroup.centralizer ({b} : Set X)) := by
  have hK₁mem : K₁ ∈ orbitSet1311 B K₁ := mem_orbitSet1311_self B K₁ B.one_mem
  have hle : K₁ ≤ orbitProd1311 B K₁ := le_orbitProd1311 hK₁mem
  have hdvd : p ∣ Nat.card ↥(orbitProd1311 B K₁) := hpK.trans (Subgroup.card_dvd_of_le hle)
  have hL := hI22 X p hp (orbitProd1311 B K₁) B K₁ (orbitSet1311 B K₁) hK₁mem
    (fun K hK => isComponentOf_orbitProd1311 hK₁ hK) rfl (orbit_commute1311 hK₁)
    (by
      rintro K ⟨b₀, hb₀, rfl⟩ K' ⟨b₁, hb₁, rfl⟩
      refine ⟨b₀⁻¹ * b₁, B.mul_mem (B.inv_mem hb₀) hb₁, ?_⟩
      rw [gLBConj_gLBConj, mul_inv_cancel_left])
    hB le_normalizer_orbitProd1311 hdvd
  have hne := jSet_nonempty1311 hp hp3 hI71 hK₁ hZ hT hB hcard
  have hsup := hL.2 hne hcard
  rw [hsup] at hle
  exact hle

end Orbit1311b

@[expose] def Input22_5Layer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → GLAPPrimeCore p X = ⊥ →
    ∀ (K B : Subgroup X), IsComponentOf K ⊤ → IsElemAbelian p B →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) < CFSG.Open.pRank p B →
      ∀ b ∈ jSet1311 (orbitProd1311 B K) B K,
        ∀ Y : Subgroup X,
          GLAPComponent p (orbitProd1311 B K ⊓ Subgroup.centralizer ({b} : Set X)) Y →
            ∃ φ : ↥K →* barOf p Y, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥K


section OrbitG

variable {p : ℕ}

theorem barX_pComp_le_normalizer_orbit (hp : p.Prime) {M D L0 L : Subgroup G}
    (hL0 : GLAPComponent p (Istar p M D) L0) (hL : GLAPComponent p (Istar p M D) L) :
    barX p M L ≤
      Subgroup.normalizer ((orbitProd1311 (barX p M D) (barX p M L0) : Subgroup _) : Set _) := by
  refine le_normalizer_orbitProd_of_comp1311 ?_
  by_cases hc : barX p M L ∈ orbitSet1311 (barX p M D) (barX p M L0)
  · exact Or.inl hc
  · right
    intro K'' hK''
    have h1 : IsComponentOf (barX p M L) ⊤ := isComponent_barX_of_pComp hp hL
    have h2 : IsComponentOf K'' ⊤ :=
      isComponentOf_orbit1311 (isComponent_barX_of_pComp hp hL0) hK''
    have hne : barX p M L ≠ K'' := fun h => hc (by rw [h]; exact hK'')
    exact Sec13e.commute_of_isComponentOf h1 h2 hne

theorem barX_istar_le_normalizer_orbit (hp : p.Prime) {M D L0 : Subgroup G}
    (hL0 : GLAPComponent p (Istar p M D) L0) :
    barX p M (Istar p M D) ≤
      Subgroup.normalizer ((orbitProd1311 (barX p M D) (barX p M L0) : Subgroup _) : Set _) :=
  (barX_istar_le_iSup_pComp hp M D).trans
    (iSup_le fun y => barX_pComp_le_normalizer_orbit hp hL0 y.2)

theorem orbitProd_le_barX_istar (hp : p.Prime) {M D L0 : Subgroup G} (hD : D ≤ M)
    (hL0 : GLAPComponent p (Istar p M D) L0) :
    orbitProd1311 (barX p M D) (barX p M L0) ≤ barX p M (Istar p M D) := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨c, hc, rfl⟩ := hK
  obtain ⟨x, hxD, rfl⟩ := (mem_barX' p).1 hc
  have hxM : (x : G) ∈ M := x.2
  have e : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥M) x) (barX p M L0) =
      barX p M (GLBConj (x : G) L0) := by
    rw [barX_gLBConj_eq p hxM L0]
  have hle : GLBConj (x : G) L0 ≤ Istar p M D :=
    (gLBConj_mono _ hL0.1).trans (istar_conj_eq p hxM).le
  rw [e]
  exact barX_mono' p (X := M) hle

end OrbitG

section OrbitIso

variable {p : ℕ}

noncomputable def barOfIsoBarX (hp : p.Prime) {M K : Subgroup G} (hKM : K ≤ M) :
    barOf p K ≃* barOf p (barX p M K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let A : Subgroup ↥M := K.subgroupOf M
  let e : ↥K ≃* ↥A := (Subgroup.subgroupOfEquivOfLe hKM).symm
  have hker : Nat.Coprime p (Nat.card ↥(A ⊓ (QuotientGroup.mk' (GLAPPrimeCore p ↥M)).ker)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  exact (QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso p e)).trans
    (lcEquiv hp (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) A hker)

end OrbitIso

section Lift

variable {p : ℕ}

@[expose] def KGof (p : ℕ) (M : Subgroup G) (Q : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Subgroup G :=
  (Q.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).map M.subtype

theorem mem_KGof (p : ℕ) {M : Subgroup G} {Q : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)} {h : G} :
    h ∈ KGof p M Q ↔ ∃ hM : h ∈ M, QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨h, hM⟩ ∈ Q := by
  unfold KGof
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hM, hQ⟩
    exact ⟨⟨h, hM⟩, hQ, rfl⟩

theorem conj_mem_LO (p : ℕ) {M D : Subgroup G} {Q : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)} {g : G}
    (hgM : g ∈ M) (hgI : g ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G))
    (hgQ : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ ∈ Subgroup.normalizer (Q : Set _))
    (h : G) :
    h ∈ Istar p M D ⊓ KGof p M Q ↔ g * h * g⁻¹ ∈ Istar p M D ⊓ KGof p M Q := by
  have hI := Subgroup.mem_normalizer_iff.1 hgI h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hI]
  refine and_congr_right fun _ => ?_
  by_cases hhM : h ∈ M
  · have hghM : g * h * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hhM) (M.inv_mem hgM)
    rw [mem_KGof, mem_KGof]
    have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g * h * g⁻¹, hghM⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨h, hhM⟩ *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩)⁻¹ := by
      simp only [← map_mul, ← map_inv]
      rfl
    constructor
    · rintro ⟨hM0, hQ⟩
      refine ⟨hghM, ?_⟩
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 hgQ _).1 hQ
    · rintro ⟨hM0, hQ⟩
      refine ⟨hhM, ?_⟩
      rw [e] at hQ
      exact (Subgroup.mem_normalizer_iff.1 hgQ _).2 hQ
  · have hL : h ∉ KGof p M Q := fun hc => hhM (by
      obtain ⟨hM', -⟩ := (mem_KGof p).1 hc
      exact hM')
    have hR : g * h * g⁻¹ ∉ KGof p M Q := fun hc => hhM (by
      obtain ⟨hM', -⟩ := (mem_KGof p).1 hc
      have := M.mul_mem (M.mul_mem (M.inv_mem hgM) hM') hgM
      simpa [mul_assoc] using this)
    exact iff_of_false hL hR

theorem normalizes_centralizer_singleton {d h : G} (hdh : d * h = h * d) (x : G) :
    x ∈ Subgroup.centralizer ({d} : Set G) ↔ h * x * h⁻¹ ∈ Subgroup.centralizer ({d} : Set G) := by
  have hdh' : h⁻¹ * d = d * h⁻¹ := by
    calc h⁻¹ * d = h⁻¹ * d * (h * h⁻¹) := by simp
      _ = h⁻¹ * (d * h) * h⁻¹ := by simp [mul_assoc]
      _ = h⁻¹ * (h * d) * h⁻¹ := by rw [hdh]
      _ = d * h⁻¹ := by simp [mul_assoc]
  have e1 : d * (h * x * h⁻¹) = h * (d * x) * h⁻¹ := by
    calc d * (h * x * h⁻¹) = (d * h) * x * h⁻¹ := by simp [mul_assoc]
      _ = (h * d) * x * h⁻¹ := by rw [hdh]
      _ = h * (d * x) * h⁻¹ := by simp [mul_assoc]
  have e2 : (h * x * h⁻¹) * d = h * (x * d) * h⁻¹ := by
    calc (h * x * h⁻¹) * d = h * x * (h⁻¹ * d) := by simp [mul_assoc]
      _ = h * x * (d * h⁻¹) := by rw [hdh']
      _ = h * (x * d) * h⁻¹ := by simp [mul_assoc]
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, e1, e2]
  constructor
  · intro e
    rw [e]
  · intro e
    have := congrArg (fun z => h⁻¹ * z * h) e
    simpa [mul_assoc] using this

theorem lift_pComp (hp : p.Prime) {M D L0 : Subgroup G} (hD : D ≤ M)
    (hDel : IsElemAbelian p D) (hL0 : GLAPComponent p (Istar p M D) L0) {d : G} (hdD : d ∈ D)
    {Y : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hY : GLAPComponent p (orbitProd1311 (barX p M D) (barX p M L0) ⊓
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hD hdD⟩} :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))) Y) :
    ∃ K : Subgroup G, GLAPComponent p (Istar p M D ⊓ Cg d) K ∧ barX p M K = Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdM : d ∈ M := hD hdD
  have hbB : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ ∈ barX p M D :=
    (mem_barX' p).2 ⟨⟨d, hdM⟩, hdD, rfl⟩
  have hbN : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ ∈
      Subgroup.normalizer ((orbitProd1311 (barX p M D) (barX p M L0) : Subgroup _) : Set _) :=
    le_normalizer_orbitProd1311 (K₁ := barX p M L0) hbB
  have hQI : orbitProd1311 (barX p M D) (barX p M L0) ≤ barX p M (Istar p M D) :=
    orbitProd_le_barX_istar hp hD hL0
  have hIN := barX_istar_le_normalizer_orbit hp (M := M) (D := D) hL0
  have hdI : d ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_iff.2
    intro y
    have := mem_gLBConj (g := d) (y := y) (H := Istar p M D)
    rw [istar_conj_eq p hdM] at this
    exact this
  have hLOM : Istar p M D ⊓ KGof p M (orbitProd1311 (barX p M D) (barX p M L0)) ≤ M :=
    inf_le_left.trans (istar_le_M p M D)
  have hLOQ : barX p M (Istar p M D ⊓ KGof p M (orbitProd1311 (barX p M D) (barX p M L0))) =
      orbitProd1311 (barX p M D) (barX p M L0) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hxLO, rfl⟩ := (mem_barX' p).1 hy
      obtain ⟨-, hxK⟩ := hxLO
      obtain ⟨hM0, hQx⟩ := (mem_KGof p).1 hxK
      exact hQx
    · intro y hy
      obtain ⟨x, hxI, rfl⟩ := (mem_barX' p).1 (hQI hy)
      exact (mem_barX' p).2 ⟨x, ⟨hxI, (mem_KGof p).2 ⟨x.2, hy⟩⟩, rfl⟩
  have hdL : d ∈ Subgroup.normalizer
      ((Istar p M D ⊓ KGof p M (orbitProd1311 (barX p M D) (barX p M L0)) : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_iff.2
    intro h
    exact conj_mem_LO p hdM hdI hbN h
  have hd : IsPGroup p (Subgroup.zpowers d) :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.isPGroup_zpowers_of_pow_eq_one' (hDel.2 d hdD)
  have hK' : GLAPComponent p (barX p M (Istar p M D ⊓ KGof p M (orbitProd1311 (barX p M D) (barX p M L0))) ⊓
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))) Y := by
    rw [hLOQ]
    exact hY
  obtain ⟨K, hK, hKY⟩ := exists_glaPComponent_lift hp hdM hLOM hdL hd hK'
  have hNT : (Istar p M D ⊓ KGof p M (orbitProd1311 (barX p M D) (barX p M L0))) ⊓ Cg d ≤
      Istar p M D ⊓ Cg d :=
    inf_le_inf_right _ inf_le_left
  have hTN : Istar p M D ⊓ Cg d ≤ Subgroup.normalizer
      (((Istar p M D ⊓ KGof p M (orbitProd1311 (barX p M D) (barX p M L0))) ⊓ Cg d : Subgroup G) :
        Set G) := by
    intro h hh
    obtain ⟨hhI, hhC⟩ := hh
    have hhM : h ∈ M := istar_le_M p M D hhI
    have hhN : h ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G) := by
      apply Subgroup.mem_normalizer_iff.2
      intro y
      have := mem_gLBConj (g := h) (y := y) (H := Istar p M D)
      rw [istar_conj_eq p hhM] at this
      exact this
    have hhQ : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨h, hhM⟩ ∈
        Subgroup.normalizer ((orbitProd1311 (barX p M D) (barX p M L0) : Subgroup _) : Set _) :=
      hIN ((mem_barX' p).2 ⟨⟨h, hhM⟩, hhI, rfl⟩)
    have hdh : d * h = h * d := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hhC
      exact this.symm
    apply Subgroup.mem_normalizer_iff.2
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, normalizes_centralizer_singleton hdh x]
    have hL := conj_mem_LO p hhM hhN hhQ x
    exact ⟨fun ⟨a, b⟩ => ⟨hL.1 a, b⟩, fun ⟨a, b⟩ => ⟨hL.2 a, b⟩⟩
  exact ⟨K, glaPComponent_of_normal hp hNT hTN hK, hKY⟩

end Lift

section Types

variable {p : ℕ}

theorem pRank_top_le_of_iso (hp : p.Prime) {L : Subgroup G} {K : Type} [Group K] [Finite K]
    (e : K ≃* barOf p L) : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hndvd : ¬ p ∣ Nat.card ↥(GLAPPrimeCore p ↥L) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  rw [CFSG.SectionRank.pRank_quotient_eq (GLAPPrimeCore p ↥L) hndvd]
  have h := CFSG.SectionRank.pRank_le_map hp.one_lt L.subtype Subtype.val_injective (⊤ : Subgroup ↥L)
  rwa [show (⊤ : Subgroup ↥L).map L.subtype = L by ext x; simp] at h

theorem pRank_top_eq_one (hp : p.Prime) {L : Subgroup G} {K : Type} [Group K] [Finite K]
    (e : K ≃* barOf p L) (hpK : p ∣ Nat.card K) (hr : CFSG.Open.pRank p L = 1) :
    CFSG.Open.pRank p (⊤ : Subgroup K) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · exact (pRank_top_le_of_iso hp e).trans hr.le
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
    have hgp : g ^ p = 1 := by
      rw [← hg]
      exact pow_orderOf_eq_one g
    have hE : IsElemAbelian p (Subgroup.zpowers g) := by
      apply isElemAbelian_of_comm_pow
      · intro x hx y hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((Commute.refl g).zpow_zpow i j).eq
      · intro x hx
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgp, one_zpow]
    have hcard : Nat.card (Subgroup.zpowers g) = p ^ 1 := by
      rw [pow_one, Nat.card_zpowers, hg]
    exact CFSG.SectionRank.le_pRank hp.one_lt le_top hE hcard

theorem p_dvd_card_alt (hp : p.Prime) (hp3 : 3 ≤ p) :
    p ∣ Nat.card (alternatingGroup (Fin (p + 2))) := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin (p + 2))
  have hperm : Nat.card (Equiv.Perm (Fin (p + 2))) = (p + 2).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hdvd : p ∣ 2 * Nat.card (alternatingGroup (Fin (p + 2))) := by
    rw [h2, hperm]
    exact (Nat.dvd_factorial hp.pos (by omega))
  have hcop : Nat.Coprime p 2 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
    omega
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem glaPPrimeCore_eq_bot_of_simple (hp : p.Prime) {K : Subgroup G} (hK : IsComponentOf K ⊤)
    (hZ : Subgroup.center ↥K = ⊥) (hpK : p ∣ Nat.card ↥K) : GLAPPrimeCore p ↥K = ⊥ := by
  have hsimple : IsSimpleGroup ↥K := by
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
    have e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact e.symm.isSimpleGroup
  unfold GLAPPrimeCore
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro R hR hcop
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal R) with h | h
  · exact h
  · exfalso
    have : Nat.card ↥R = Nat.card ↥K := by
      rw [h, Subgroup.card_top]
    rw [this] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpK


@[expose] def InputOmegaDvd1311 : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (ε : Bool) (n : ℕ) (X : Type) [Group X] [Finite X], 1 ≤ n →
    IsOmegaTwo ε (n + 1) X → HasFixedPointFreeOrder ε n p → p ∣ Nat.card X

theorem pComp_eq_of_single (hp : p.Prime) {M D L1 L : Subgroup G} (hIL : Istar p M D = L1)
    (hL1 : GLAPComponent p (Istar p M D) L1) (hL : GLAPComponent p (Istar p M D) L) : L = L1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [hIL] at hL hL1
  have hL1c : IsComponentOf (⊤ : Subgroup (↥L1 ⧸ GLAPPrimeCore p ↥L1)) ⊤ := by
    have h : IsComponentOf (barX p L1 L1) ⊤ := hL1.2.2.1
    rwa [barX_self] at h
  have hKc : IsComponentOf (barX p L1 L) ⊤ := hL.2.2.1
  obtain ⟨i, hi⟩ := layer_mem hKc (ι := Unit) (F := fun _ => ⊤) (fun _ => hL1c)
    (by rw [iSup_const]; exact le_top)
  refine glaPComponent_unique hL hL1 ?_
  rw [barX_self]
  exact hi.symm

theorem pComp_type (hp : p.Prime) {M D L : Subgroup G} (h139 : Prop139a p M D ∨ Prop139b p M D)
    (hL : GLAPComponent p (Istar p M D) L) :
    IsAltType (p + 2) (barOf p L) ∨ (3 < p ∧ ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧
      IsOmegaTwo ε (n + 1) (barOf p L) ∧ HasFixedPointFreeOrder ε n p ∧
        CFSG.Open.pRank p L = 1) := by
  rcases h139 with ⟨hp3, hIoS, L1, hL1, hIL1, hr1, htyp⟩ | ⟨rfl, hall⟩
  · have hIL : Istar p M D = L1 := hIoS.symm.trans hIL1
    have hL1' : GLAPComponent p (Istar p M D) L1 := hIoS ▸ hL1
    have hLL1 : L = L1 := pComp_eq_of_single hp hIL hL1' hL
    rw [hLL1]
    rcases htyp with h | ⟨ε, n, hn, hΩ, hfp⟩
    · exact Or.inl h
    · exact Or.inr ⟨hp3, ε, n, hn, hΩ, hfp, hr1⟩
  · exact Or.inl (hall L hL)

end Types

section Gen2

variable {p : ℕ}

theorem comp_data (hp : p.Prime) (hp3 : 3 ≤ p) (hOm : InputOmegaDvd1311)
    {M D L : Subgroup G} (h139 : Prop139a p M D ∨ Prop139b p M D)
    (hL : GLAPComponent p (Istar p M D) L) :
    IsComponentOf (barX p M L) ⊤ ∧ Subgroup.center ↥(barX p M L) = ⊥ ∧
    (IsAltType (p + 2) ↥(barX p M L) ∨ (3 < p ∧ ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧
      IsOmegaTwo ε (n + 1) ↥(barX p M L) ∧ HasFixedPointFreeOrder ε n p ∧
        CFSG.Open.pRank p (⊤ : Subgroup ↥(barX p M L)) = 1)) ∧
    p ∣ Nat.card ↥(barX p M L) ∧ IsPiGroup p ↥(barX p M L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK1 : IsComponentOf (barX p M L) ⊤ := isComponent_barX_of_pComp hp hL
  have hLM : L ≤ M := hL.1.trans (istar_le_M p M D)
  have hsn : IsSubnormal L M := isSubnormal_pComp_of_istar hp hL
  have e : ↥(barX p M L) ≃* barOf p L := barXIso hp hLM hsn
  rcases pComp_type hp h139 hL with halt | ⟨hp3', ε, n, hn, hΩ, hfp, hr⟩
  · obtain ⟨f⟩ := halt
    let e' : ↥(barX p M L) ≃* alternatingGroup (Fin (p + 2)) := e.trans f
    have hcen : Subgroup.center ↥(barX p M L) = ⊥ :=
      CFSG.LocalAnalysis.GLTheoremB.center_eq_bot_of_mulEquiv_alt (by omega) e'
    have hdvd : p ∣ Nat.card ↥(barX p M L) := by
      rw [Nat.card_congr e'.toEquiv]
      exact p_dvd_card_alt hp hp3
    have e0 : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* ↥(barX p M L) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have hpi : IsPiGroup p ↥(barX p M L) := by
      refine ⟨hK1.2.2, glaPPrimeCore_eq_bot_of_simple hp hK1 hcen hdvd, Or.inl ⟨1, ⟨?_⟩⟩⟩
      have h1 : 1 * p + 2 = p + 2 := by omega
      exact e0.trans (e'.trans (Equiv.altCongrHom (finCongr h1.symm)))
    exact ⟨hK1, hcen, Or.inl ⟨e'⟩, hdvd, hpi⟩
  · have hΩ' : IsOmegaTwo ε (n + 1) ↥(barX p M L) := IsOmegaTwo.of_mulEquiv e.symm hΩ
    have hcen : Subgroup.center ↥(barX p M L) = ⊥ :=
      Prop95I1920.center_eq_bot_of_omega Prop95I1920.omegaFourComponentCentre_holds hK1 hn ε hΩ'
    have hdvd : p ∣ Nat.card ↥(barX p M L) := hOm p hp ε n _ hn hΩ' hfp
    have hr1 : CFSG.Open.pRank p (⊤ : Subgroup ↥(barX p M L)) = 1 :=
      pRank_top_eq_one hp e hdvd hr
    have e0 : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* ↥(barX p M L) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have hpi : IsPiGroup p ↥(barX p M L) := by
      refine ⟨hK1.2.2, glaPPrimeCore_eq_bot_of_simple hp hK1 hcen hdvd,
        Or.inr (Or.inl ⟨n, ε, hn, IsOmegaTwo.of_mulEquiv e0.symm hΩ', hfp⟩)⟩
    exact ⟨hK1, hcen, Or.inr ⟨hp3', ε, n, hn, hΩ', hfp, hr1⟩, hdvd, hpi⟩

theorem iso_of_hom {K : Type} [Group K] [Finite K] {Y : Type} [Group Y] (hZ : Subgroup.center K = ⊥)
    (φ : K →* Y) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K) : Nonempty (K ≃* Y) := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have : a ∈ φ.ker := ha
    have h1 : a ∈ Subgroup.center K := hker this
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hφ⟩⟩

end Gen2

section Clause

variable {p : ℕ}

theorem pComp_le_R (hp : p.Prime) {M D L0 : Subgroup G} (hD : D ≤ M) (hDel : IsElemAbelian p D)
    (hL0 : GLAPComponent p (Istar p M D) L0) {d : G} (hdD : d ∈ D)
    {Y : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hY : GLAPComponent p (orbitProd1311 (barX p M D) (barX p M L0) ⊓
      Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hD hdD⟩} :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))) Y)
    (hPi : IsPiGroup p ↥(barX p M L0))
    (φ : ↥(barX p M L0) ≃* barOf p Y) :
    Y ≤ barX p M (piLayer p (Istar p M D ⊓ Cg d)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, hKY⟩ := lift_pComp hp hD hDel hL0 hdD hY
  have hKM : K ≤ M := (hK.1.trans inf_le_left).trans (istar_le_M p M D)
  have e2 := barOfIsoBarX hp hKM
  rw [hKY] at e2
  have hPiK : IsPiGroup p (barOf p K) := IsPiGroup.of_mulEquiv (φ.trans e2.symm) hPi
  have hKP : K ≤ piLayer p (Istar p M D ⊓ Cg d) := Sec13f.le_piLayer hK hPiK
  rw [← hKY]
  exact barX_mono' p (X := M) hKP

theorem layer_le_R (hp : p.Prime) (hp3 : 3 ≤ p) (hI225 : Input22_5Layer) (hI71 : Input7_1Aut)
    {M D L0 : Subgroup G} (hD : D ≤ M) (hDel : IsElemAbelian p D)
    (hL0 : GLAPComponent p (Istar p M D) L0)
    (hK₁ : IsComponentOf (barX p M L0) ⊤) (hZ : Subgroup.center ↥(barX p M L0) = ⊥)
    (hT : IsAltType (p + 2) ↥(barX p M L0) ∨ (3 < p ∧ ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧
      IsOmegaTwo ε (n + 1) ↥(barX p M L0) ∧ HasFixedPointFreeOrder ε n p ∧
        CFSG.Open.pRank p (⊤ : Subgroup ↥(barX p M L0)) = 1))
    (hPi : IsPiGroup p ↥(barX p M L0))
    (hlt : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(barX p M L0))) < CFSG.Open.pRank p (barX p M D))
    (hB : IsElemAbelian p (barX p M D))
    {b : ↥M ⧸ GLAPPrimeCore p ↥M}
    (hbB : b ∈ barX p M D) (hb1 : b ≠ 1)
    (hbJ : b ∈ jSet1311 (orbitProd1311 (barX p M D) (barX p M L0)) (barX p M D) (barX p M L0)) :
    GLAPLayer p (orbitProd1311 (barX p M D) (barX p M L0) ⊓ Subgroup.centralizer ({b} : Set _)) ≤
      ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), barX p M (piLayer p (Istar p M D ⊓ Cg d)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxD, rfl⟩ := (mem_barX' p).1 hbB
  have hd1 : (x : G) ≠ 1 := by
    intro h
    apply hb1
    have hx : x = 1 := Subtype.ext h
    rw [hx, map_one]
  refine sSup_le fun Y hY => ?_
  obtain ⟨φ0, hsurj, hker⟩ := hI225 (↥M ⧸ GLAPPrimeCore p ↥M) p hp
    (glaPPrimeCore_quot_eq_bot p ↥M) (barX p M L0) (barX p M D) hK₁ hB hlt _ hbJ Y hY
  obtain ⟨φ⟩ := iso_of_hom hZ φ0 hsurj hker
  exact (pComp_le_R hp hD hDel hL0 hxD hY hPi φ).trans
    (le_iSup_of_le (x : G) (le_iSup_of_le hxD (le_iSup_of_le hd1 le_rfl)))

end Clause

section Gen3

variable {p : ℕ}

theorem istar_barX_le_R (hp : p.Prime) (hp3 : 3 ≤ p) (hI22 : Input22_3) (hI71 : Input7_1Aut)
    (hI225 : Input22_5Layer) (hOm : InputOmegaDvd1311) {M D : Subgroup G}
    (h139 : Prop139a p M D ∨ Prop139b p M D) (hDM : D ≤ M) (hDel : IsElemAbelian p D)
    (hDcard : Nat.card ↥D = p ^ 2) :
    barX p M (Istar p M D) ≤
      ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), barX p M (piLayer p (Istar p M D ⊓ Cg d)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine (barX_istar_le_iSup_pComp hp M D).trans (iSup_le fun y => ?_)
  obtain ⟨hK₁, hcen, hT, hpK, hPi⟩ := comp_data hp hp3 hOm h139 y.2
  have hPD : IsPGroup p ↥D := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hDel.2 (g : G) g.2)⟩
  have hB : IsElemAbelian p (barX p M D) := isElemAbelian_barX hDel
  have hBcard : Nat.card ↥(barX p M D) = p ^ 2 := by
    rw [card_barX_of_isPGroup hp hPD hDM, hDcard]
  have hpB : 2 ≤ CFSG.Open.pRank p (barX p M D) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB hBcard
  have hpE : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(barX p M y.1))) ≤ 1 := by
    apply CFSG.SectionRank.pRank_le hp.one_lt (k := 1)
    intro E _ hE
    have := hI71 p hp hp3 ↥(barX p M y.1) hK₁.2.2 hcen hT E hE
    rw [pow_one]
    exact this
  have hlt : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(barX p M y.1))) <
      CFSG.Open.pRank p (barX p M D) := lt_of_le_of_lt hpE (by omega)
  have hcomp := comp_le_layers1311 hI22 hI71 hp hp3 hK₁ hcen hT hB hBcard.ge hpK
  refine hcomp.trans (iSup_le fun b => iSup_le fun hb => ?_)
  exact layer_le_R hp hp3 hI225 hI71 hDM hDel y.2 hK₁ hcen hT hPi hlt hB hb.1 hb.2.1 hb

theorem lemma1311_gen_of_inputs (hp : p.Prime) (hp3 : 3 ≤ p) (hI22 : Input22_3) (hI71 : Input7_1Aut)
    (hI225 : Input22_5Layer) (hOm : InputOmegaDvd1311) {M D : Subgroup G}
    (h139 : Prop139a p M D ∨ Prop139b p M D) (hDM : D ≤ M) (hDel : IsElemAbelian p D)
    (hDcard : Nat.card ↥D = p ^ 2) :
    barX p M (Istar p M D) =
      ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), barX p M (piLayer p (Istar p M D ⊓ Cg d)) := by
  refine le_antisymm (istar_barX_le_R hp hp3 hI22 hI71 hI225 hOm h139 hDM hDel hDcard) ?_
  refine iSup_le fun d => iSup_le fun _ => iSup_le fun _ => ?_
  exact barX_mono' p (X := M) ((Sec13f.piLayer_le p _).trans inf_le_left)

end Gen3

section Final

variable {p : ℕ}

theorem pComp_piLayer_summand (hp : p.Prime) {H J : Subgroup G}
    (hJ : GLAPComponent p (piLayer p H) J) :
    ∃ S : Subgroup G, GLAPComponent p H S ∧ IsPiGroup p (↥S ⧸ GLAPPrimeCore p ↥S) ∧ J = S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXH : piLayer p H ≤ H := Sec13f.piLayer_le p H
  have hsum : ∀ i : Sec13f.PiSummand p H, GLAPComponent p (piLayer p H) i.1 := fun i =>
    glaPComponent_of_le hp i.2.1 (Sec13f.le_piLayer i.2.1 i.2.2) hXH
  have hJS : J ≤ ⨆ i : Sec13f.PiSummand p H, i.1 := by
    rw [← Sec13f.piLayer_eq_iSup_subtype]
    exact hJ.1
  have hle : barX p (piLayer p H) J ≤
      ⨆ i : Sec13f.PiSummand p H, barX p (piLayer p H) i.1 :=
    (barX_mono' p (X := piLayer p H) hJS).trans
      (barX_iSup_le_iSup (p := p) (C := piLayer p H) (fun i : Sec13f.PiSummand p H => i.1)
        (fun i => Sec13f.le_piLayer i.2.1 i.2.2))
  obtain ⟨i, hi⟩ := layer_mem hJ.2.2.1 (fun i => (hsum i).2.2.1) hle
  exact ⟨i.1, i.2.1, i.2.2, glaPComponent_unique hJ (hsum i) hi.symm⟩

theorem barOf_iso_of_pComp (hp : p.Prime) {M D K L : Subgroup G}
    (h139 : Prop139a p M D ∨ Prop139b p M D) (hK : GLAPComponent p (Istar p M D) K)
    (hL : GLAPComponent p (Istar p M D) L) : Nonempty (barOf p K ≃* barOf p L) := by
  rcases h139 with ⟨-, hIoS, L1, hL1, hIL1, -, -⟩ | ⟨-, hall⟩
  · have hIL : Istar p M D = L1 := hIoS.symm.trans hIL1
    have hL1' : GLAPComponent p (Istar p M D) L1 := hIoS ▸ hL1
    have hKL : K = L := (pComp_eq_of_single hp hIL hL1' hK).trans
      (pComp_eq_of_single hp hIL hL1' hL).symm
    rw [hKL]
    exact ⟨MulEquiv.refl _⟩
  · obtain ⟨eK⟩ := hall K hK
    obtain ⟨eL⟩ := hall L hL
    exact ⟨eK.trans eL.symm⟩

@[expose] def Gap1311Iso : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) (h139 : Prop139a p M D ∨ Prop139b p M D) (d : G),
    d ∈ D → d ≠ 1 → ¬ Istar p M D ≤ Subgroup.centralizer ({d} : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) J →
      ∃ K : Subgroup G, GLAPComponent p (Istar p M D) K ∧ Nonempty (barOf p J ≃* barOf p K)

theorem lemma1311_iso_of_gap (hGap : Gap1311Iso) {G : Type} [Group G] [Finite G] {m p : ℕ}
    {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (h139 : Prop139a p M D ∨ Prop139b p M D) :
    ∀ d ∈ D, d ≠ 1 → ∀ J : Subgroup G, GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) J →
      ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → Nonempty (barOf p J ≃* barOf p L) := by
  intro d hd hd1 J hJ L hL
  have hp : p.Prime := (show p.Prime ∧ _ from h.standing.beta).1
  by_cases hdC : Istar p M D ≤ Subgroup.centralizer ({d} : Set G)
  · have hH : Istar p M D ⊓ Cg d = Istar p M D := inf_eq_left.2 hdC
    rw [hH] at hJ
    obtain ⟨S, hS, -, rfl⟩ := pComp_piLayer_summand hp hJ
    exact barOf_iso_of_pComp hp h139 hS hL
  · obtain ⟨K, hK, hiso⟩ := hGap h h139 d hd hd1 hdC J hJ
    obtain ⟨eKL⟩ := barOf_iso_of_pComp hp h139 hK hL
    obtain ⟨eJ⟩ := hiso
    exact ⟨eJ.trans eKL⟩

end Final

end Lemma1311

theorem lemma1311_of_inputs (hI22 : Sec13e.Input22_3) (hI71 : Sec13e.Input7_1Aut)
    (hI225 : Lemma1311.Input22_5Layer) (hOm : Lemma1311.InputOmegaDvd1311)
    (hGap : Lemma1311.Gap1311Iso) : Lemma1311Statement := by
  intro G _ _ m p B M E A D T h h139
  have hp : p.Prime := (show p.Prime ∧ _ from h.standing.beta).1
  have hp3 : 3 ≤ p := by
    rcases h139 with ⟨h3, -⟩ | ⟨h3, -⟩
    · omega
    · omega
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := h.hD.1.trans hAM
  have hDel : IsElemAbelian p D := h.hD.2.1
  have hDcard : Nat.card ↥D = p ^ 2 := h.hD.2.2
  exact ⟨Lemma1311.lemma1311_gen_of_inputs hp hp3 hI22 hI71 hI225 hOm h139 hDM hDel hDcard,
    Lemma1311.lemma1311_iso_of_gap hGap h h139⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
