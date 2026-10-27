module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoSubgroup
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace Lemma55Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

@[expose] def IsLThreeEpsOrON (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 ≠ 0 ∧
      Nonempty (Y ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 ≠ 0 ∧ q ≠ 8 ∧
      Nonempty (Y ≃* StatedProj (StatedSU 3 q K))) ∨
    Nonempty (Y ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group)

@[expose] def Input23_26 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L E : Subgroup X) (𝒦 : Set (Subgroup X)),
    (∀ K ∈ 𝒦, IsComponentOf K ⊤ ∧ IsLThreeEpsOrON (↥K ⧸ Subgroup.center ↥K)) →
    L = ⨆ K ∈ 𝒦, K → IsElemAbelian 3 E → Nat.card E = 27 →
    E ≤ Subgroup.normalizer (L : Set X) →
      L = ⨆ (e : X) (_ : e ∈ E) (_ : e ≠ 1), GLAPLayer 3 (L ⊓ Subgroup.centralizer ({e} : Set X))

@[expose] def Input14_5Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → ∀ P : Subgroup X, P ≠ ⊥ → IsPGroup p P →
      ⁅GLAPLayer p (Subgroup.normalizer (P : Set X)),
        GLAPPrimeCoreOf p (Subgroup.normalizer (P : Set X))⁆ = ⊥

@[expose] def Input14_5Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ P : Subgroup X, P ≠ ⊥ → IsPGroup 3 P →
      ⁅GLAPLayer 3 (Subgroup.normalizer (P : Set X)),
        GLAPPrimeCoreOf 3 (Subgroup.normalizer (P : Set X))⁆ = ⊥

theorem input14_5Three_of_two (h : Input14_5Two) : Input14_5Three :=
  fun X _ _ hK hcore P hP hPp => h X hK 3 Nat.prime_three (by decide) hcore P hP hPp

@[expose] def InputUpsilonType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, GLAIsBmax 3 B → IsSCp 3 ⊤ B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L →
        IsExtremalType (↥L ⧸ oPrimeP 3 ↥L) ∨ IsHatON (barOf 3 L)

@[expose] def InputFieldAutTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Ab : Subgroup (MulAut Y)), IsPGroup 3 Ab →
    (∀ α ∈ Ab, IsFieldAutThree α) → (∃ α ∈ Ab, α ≠ 1) →
      ∃ T : Subgroup Y, T ≠ ⊥ ∧ IsPGroup 2 T ∧ ∀ α ∈ Ab, T.map α.toMonoidHom = T

section PerfectCentralizer

variable {G : Type*} [Group G]

theorem comm_aux {a b u v : G} (hau : Commute a u) (hav : Commute a v) (hab : Commute a b)
    (hbu : Commute b u) (hbv : Commute b v) :
    a⁻¹ * u * (b⁻¹ * v) * (a⁻¹ * u)⁻¹ * (b⁻¹ * v)⁻¹ = u * v * u⁻¹ * v⁻¹ := by
  have hX : Commute a⁻¹ (u * b⁻¹ * v * u⁻¹) :=
    ((((hau.inv_left).mul_right (hab.inv_left.inv_right)).mul_right hav.inv_left).mul_right
      hau.inv_left.inv_right)
  have hY : Commute b⁻¹ (v * u⁻¹ * v⁻¹) :=
    ((hbv.inv_left).mul_right hbu.inv_left.inv_right).mul_right hbv.inv_left.inv_right
  have e1 : a⁻¹ * u * (b⁻¹ * v) * (a⁻¹ * u)⁻¹ * (b⁻¹ * v)⁻¹
      = a⁻¹ * (u * b⁻¹ * v * u⁻¹) * a * (v⁻¹ * b) := by group
  have e2 : a⁻¹ * (u * b⁻¹ * v * u⁻¹) * a = u * b⁻¹ * v * u⁻¹ := by
    rw [hX.eq]; group
  have e3 : u * b⁻¹ * v * u⁻¹ * (v⁻¹ * b) = u * (b⁻¹ * (v * u⁻¹ * v⁻¹) * b) := by group
  have e4 : b⁻¹ * (v * u⁻¹ * v⁻¹) * b = v * u⁻¹ * v⁻¹ := by
    have := hY.eq
    calc b⁻¹ * (v * u⁻¹ * v⁻¹) * b = (v * u⁻¹ * v⁻¹) * b⁻¹ * b := by rw [← this]
      _ = v * u⁻¹ * v⁻¹ := by group
  rw [e1, e2, e3, e4]; group

theorem le_centralizer_of_perfect {W O : Subgroup G} {r : G} (hW : ⁅W, W⁆ = W)
    (hO : O ≤ Subgroup.centralizer (W : Set G)) (hrW : ∀ u ∈ W, r * u * r⁻¹ ∈ W)
    (hr : ∀ u ∈ W, u * r * u⁻¹ * r⁻¹ ∈ O) :
    W ≤ Subgroup.centralizer ({r} : Set G) := by
  have hOc : ∀ o ∈ O, ∀ w ∈ W, Commute o w := fun o ho w hw =>
    (show Commute w o from ((Subgroup.mem_centralizer_iff.1 (hO ho)) w hw)).symm
  rw [← hW]
  refine Subgroup.commutator_le.2 fun u hu v hv => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  set a := u * r * u⁻¹ * r⁻¹ with ha
  set b := v * r * v⁻¹ * r⁻¹ with hb
  have haO : a ∈ O := hr u hu
  have hbO : b ∈ O := hr v hv
  have haW : a ∈ W := by
    have h1 := hrW u hu
    have : a = u * (r * u * r⁻¹)⁻¹ := by rw [ha]; group
    rw [this]; exact W.mul_mem hu (W.inv_mem h1)
  have hbW : b ∈ W := by
    have h1 := hrW v hv
    have : b = v * (r * v * r⁻¹)⁻¹ := by rw [hb]; group
    rw [this]; exact W.mul_mem hv (W.inv_mem h1)
  have hru : r * u * r⁻¹ = a⁻¹ * u := by rw [ha]; group
  have hrv : r * v * r⁻¹ = b⁻¹ * v := by rw [hb]; group
  have key : r * ⁅u, v⁆ * r⁻¹ = ⁅u, v⁆ := by
    have e : r * ⁅u, v⁆ * r⁻¹ = (r * u * r⁻¹) * (r * v * r⁻¹) * (r * u * r⁻¹)⁻¹ * (r * v * r⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e, hru, hrv, commutatorElement_def]
    exact comm_aux (hOc a haO u hu) (hOc a haO v hv) (hOc a haO b hbW)
      (hOc b hbO u hu) (hOc b hbO v hv)
  calc ⁅u, v⁆ * r = (r * ⁅u, v⁆ * r⁻¹) * r := by rw [key]
    _ = r * ⁅u, v⁆ := by group

end PerfectCentralizer

theorem t1_glaPComponent_of_isSubnormal {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H M K : Subgroup G}
    (hK : GLAPComponent p H K) (hHM : H ≤ M) (hsnM : IsSubnormal K M) :
    GLAPComponent p M K := by
  obtain ⟨hKH, hsnH, hcomp, hmin⟩ := hK
  have hKM : K ≤ M := hKH.trans hHM
  refine ⟨hKM, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p H K) ≃* ↥(barX p M K) :=
      (quotEquivBarX hp hKH hsnH).symm.trans (quotEquivBarX hp hKM hsnM)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J hJ hJsn heq
    have hJL : J ≤ K := hJ.le
    have hcoreL : K ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal p hsnH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJL.trans hKH) hHM
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H K
    refine le_antisymm (barX_mono p hJL) ?_
    refine barX_le_of_forall (hJL.trans hKH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hKM hk)
    exact ⟨j, hj, hcoreL ⟨K.mul_mem (K.inv_mem (hJL hj)) hk, hjk⟩⟩

theorem glaPLayer_le_of_isSubnormal {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Y N : Subgroup G} (h : IsSubnormal Y N) : GLAPLayer p Y ≤ GLAPLayer p N := by
  refine sSup_le fun J hJ => le_sSup ?_
  exact t1_glaPComponent_of_isSubnormal hp hJ (isSubnormal_le' h) (isSubnormal_trans' hJ.2.1 h)

section T2

variable {G : Type*} [Group G]

private theorem t2_mem_primeCoreOf_conj {p : ℕ} {N : Subgroup G} {n : G} (hn : n ∈ N) {o : G}
    (ho : o ∈ GLAPPrimeCoreOf p N) : n * o * n⁻¹ ∈ GLAPPrimeCoreOf p N := by
  obtain ⟨y, hy, rfl⟩ := ho
  have hnorm : (GLAPPrimeCore p ↥N).Normal := inferInstance
  exact ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, hnorm.conj_mem y hy ⟨n, hn⟩, by simp⟩

private def t2_commSub (p : ℕ) (N : Subgroup G) (r : G) : Subgroup G where
  carrier := {u | u ∈ N ∧ u * r * u⁻¹ * r⁻¹ ∈ GLAPPrimeCoreOf p N}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨mul_mem hu hv, ?_⟩
    have h1 : u * v * r * (u * v)⁻¹ * r⁻¹ =
        (u * (v * r * v⁻¹ * r⁻¹) * u⁻¹) * (u * r * u⁻¹ * r⁻¹) := by group
    rw [h1]
    exact mul_mem (t2_mem_primeCoreOf_conj hu hv') hu'
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨inv_mem hu, ?_⟩
    have h1 : u⁻¹ * r * u⁻¹⁻¹ * r⁻¹ = u⁻¹ * (u * r * u⁻¹ * r⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [h1]
    exact t2_mem_primeCoreOf_conj (inv_mem hu)
      (inv_mem hu')

theorem commutator_mem_core_of_mem_layer [Finite G] {p : ℕ} (hp : p.Prime) {N : Subgroup G} {r : G}
    (hr : r ∈ oPrimePOf p N) {u : G} (hu : u ∈ GLAPLayer p N) :
    u * r * u⁻¹ * r⁻¹ ∈ GLAPPrimeCoreOf p N := by
  have _ := Fact.mk hp
  have hle : GLAPLayer p N ≤ t2_commSub p N r := by
    refine sSup_le fun K hK => ?_
    intro k hk
    refine ⟨hK.1 hk, ?_⟩
    obtain ⟨r', hr', rfl⟩ := hr
    have hkN : k ∈ N := hK.1 hk
    have hcen : ⁅barX p N K, CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N)⁆ = ⊥ := by
      have : Group.IsNilpotent (CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N)) :=
        IsPGroup.isNilpotent CFSG.pCore_isPGroup
      exact CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal _ _
        hK.2.2.1
        (IsSubnormal.step le_top (by infer_instance) (IsSubnormal.refl _))
    have hkbar : QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨k, hkN⟩ ∈ barX p N K :=
      ⟨⟨k, hkN⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
    have hrbar : QuotientGroup.mk' (GLAPPrimeCore p ↥N) r' ∈
        CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N) := hr'
    have h1 := Subgroup.commutator_mem_commutator hkbar hrbar
    rw [hcen, Subgroup.mem_bot, commutatorElement_def] at h1
    have hxN : k * (N.subtype r') * k⁻¹ * (N.subtype r')⁻¹ ∈ N := by
      have := (⟨k, hkN⟩ * r' * ⟨k, hkN⟩⁻¹ * r'⁻¹ : ↥N).2
      simpa using this
    refine ⟨⟨_, hxN⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨k, hkN⟩ * r' * ⟨k, hkN⟩⁻¹ * r'⁻¹) = 1
    simpa using h1
  exact (hle hu).2

theorem layer_perfect [Finite G] (p : ℕ) (N : Subgroup G) :
    ⁅GLAPLayer p N, GLAPLayer p N⁆ = GLAPLayer p N := by
  refine le_antisymm (Subgroup.commutator_le_self _) (sSup_le fun K hK => ?_)
  calc K = ⁅K, K⁆ := (glaPComponent_perfect hK).symm
    _ ≤ ⁅GLAPLayer p N, GLAPLayer p N⁆ :=
      Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem mem_layer_conj [Finite G] (p : ℕ) {N : Subgroup G} {n : G} (hn : n ∈ N) {u : G}
    (hu : u ∈ GLAPLayer p N) : n * u * n⁻¹ ∈ GLAPLayer p N := by
  have hN : GLBConj n⁻¹ N = N :=
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (inv_mem hn))
  have hle : GLAPLayer p N ≤ (GLAPLayer p N).comap (MulAut.conj n).toMonoidHom := by
    refine sSup_le fun K hK => ?_
    intro k hk
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK n⁻¹
    rw [hN] at h1
    have h2 : (MulAut.conj n).toMonoidHom k ∈ GLBConj n⁻¹ K := by
      rw [mem_gLBConj]
      have : n⁻¹ * (n * k * n⁻¹) * n⁻¹⁻¹ = k := by group
      show n⁻¹ * (n * k * n⁻¹) * n⁻¹⁻¹ ∈ K
      rw [this]; exact hk
    exact le_sSup (show GLBConj n⁻¹ K ∈ {L | GLAPComponent p N L} from h1) h2
  simpa [MulAut.conj_apply] using hle hu

end T2

section T3Tools

variable {G : Type*} [Group G]

private theorem t3_pow_mem_abs {p : ℕ} {H : Type*} [Group H] {x : H} (hx : x ∈ oPrimeP p H) :
    ∃ n : ℕ, x ^ (p ^ n) ∈ GLAPPrimeCore p H := by
  have hpg : IsPGroup p (CFSG.pCore p (H ⧸ GLAPPrimeCore p H)) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hpg ⟨_, hx⟩
  refine ⟨k, (QuotientGroup.eq_one_iff _).1 ?_⟩
  have := congrArg Subtype.val hk
  simpa [map_pow] using this

private theorem t3_le_oPrimeP_abs {p : ℕ} {H : Type*} [Group H] (W : Subgroup H) (hW : W.Normal)
    (hpow : ∀ w ∈ W, ∃ n : ℕ, w ^ (p ^ n) ∈ GLAPPrimeCore p H) : W ≤ oPrimeP p H := by
  have hWn : (W.map (QuotientGroup.mk' (GLAPPrimeCore p H))).Normal :=
    hW.map _ (QuotientGroup.mk'_surjective _)
  have hWp : IsPGroup p (W.map (QuotientGroup.mk' (GLAPPrimeCore p H))) := by
    rintro ⟨_, w, hw, rfl⟩
    obtain ⟨n, hn⟩ := hpow w hw
    refine ⟨n, Subtype.ext ?_⟩
    have : QuotientGroup.mk' (GLAPPrimeCore p H) (w ^ (p ^ n)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hn
    simpa [map_pow] using this
  have hle : W.map (QuotientGroup.mk' (GLAPPrimeCore p H)) ≤
      CFSG.pCore p (H ⧸ GLAPPrimeCore p H) := le_sSup ⟨hWn, hWp⟩
  intro w hw
  exact hle ⟨w, hw, rfl⟩

private theorem t3_core_map_le (p : ℕ) {H H' : Type*} [Group H] [Group H'] (σ : H ≃* H') :
    (GLAPPrimeCore p H).map σ.toMonoidHom ≤ GLAPPrimeCore p H' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map _ σ.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective σ.injective]
  exact hN.2

private theorem t3_map_le {p : ℕ} {H H' : Type*} [Group H] [Group H'] (σ : H ≃* H') :
    (oPrimeP p H).map σ.toMonoidHom ≤ oPrimeP p H' := by
  refine t3_le_oPrimeP_abs _ (Subgroup.Normal.map inferInstance _ σ.surjective) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := t3_pow_mem_abs hx
  refine ⟨n, t3_core_map_le p σ ⟨_, hn, ?_⟩⟩
  simp [map_pow]

private theorem t3_le_oPrimePOf {p : ℕ} {H S : Subgroup G} (hSH : S ≤ H)
    (hS : (S.subgroupOf H).Normal)
    (hpow : ∀ s ∈ S, ∃ n : ℕ, s ^ (p ^ n) ∈ GLAPPrimeCoreOf p H) : S ≤ oPrimePOf p H := by
  intro s hs
  have hmem : (⟨s, hSH hs⟩ : ↥H) ∈ oPrimeP p ↥H := by
    refine t3_le_oPrimeP_abs (S.subgroupOf H) hS ?_ (Subgroup.mem_subgroupOf.2 hs)
    intro w hw
    obtain ⟨n, hn⟩ := hpow w (Subgroup.mem_subgroupOf.1 hw)
    obtain ⟨t, ht, hte⟩ := hn
    have : t = w ^ (p ^ n) := Subtype.ext (by simpa using hte)
    exact ⟨n, this ▸ ht⟩
  exact ⟨_, hmem, rfl⟩

private theorem t3_pow_mem {p : ℕ} {X : Subgroup G} {s : G} (hs : s ∈ oPrimePOf p X) :
    ∃ n : ℕ, s ^ (p ^ n) ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨n, hn⟩ := t3_pow_mem_abs ht
  exact ⟨n, t ^ (p ^ n), hn, by simp⟩

private theorem t3_oPrimePOf_normal (p : ℕ) (X : Subgroup G) :
    ((oPrimePOf p X).subgroupOf X).Normal := by
  have h : (oPrimePOf p X).subgroupOf X = oPrimeP p ↥X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [h]
  infer_instance

private theorem t3_core_normal (p : ℕ) (X : Subgroup G) :
    ((GLAPPrimeCoreOf p X).subgroupOf X).Normal := by
  have h : (GLAPPrimeCoreOf p X).subgroupOf X = GLAPPrimeCore p ↥X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [h]
  infer_instance

private theorem t3_conj {S X : Subgroup G} (hn : (S.subgroupOf X).Normal) {s t : G} (hs : s ∈ S)
    (hsX : s ∈ X) (htX : t ∈ X) : t * s * t⁻¹ ∈ S := by
  have := hn.conj_mem ⟨s, hsX⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨t, htX⟩
  exact Subgroup.mem_subgroupOf.1 this

private theorem t3_conj_mem {p : ℕ} {C N : Subgroup G}
    (hn : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) {n : G} (hnN : n ∈ N) {w : G}
    (hw : w ∈ oPrimePOf p C) : n * w * n⁻¹ ∈ oPrimePOf p C := by
  let σ : ↥C ≃* ↥C :=
    { toFun := fun c => ⟨n * c * n⁻¹, hn n hnN c c.2⟩
      invFun := fun c => ⟨n⁻¹ * c * n, by simpa using hn n⁻¹ (N.inv_mem hnN) c c.2⟩
      left_inv := fun c => Subtype.ext (by simp [mul_assoc])
      right_inv := fun c => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨x, hx, rfl⟩ := hw
  exact ⟨σ x, t3_map_le σ ⟨x, hx, rfl⟩, rfl⟩

private theorem t3_inf_le_core [Finite G] {p : ℕ} (hp : p.Prime) {Y H : Subgroup G}
    (hHY : H ≤ Y) : GLAPPrimeCoreOf p Y ⊓ H ≤ GLAPPrimeCoreOf p H := by
  set M : Subgroup G := GLAPPrimeCoreOf p Y ⊓ H with hM
  have hMH : M ≤ H := inf_le_right
  have hnorm : (M.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMH]
    intro m k hm hk
    exact ⟨t3_conj (t3_core_normal p Y) hm.1 (Subgroup.map_subtype_le _ hm.1) (hHY hk),
      H.mul_mem (H.mul_mem hk hm.2) (H.inv_mem hk)⟩
  have hcop : Nat.Coprime p (Nat.card (M.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv]
    refine Nat.Coprime.coprime_dvd_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_glaPPrimeCoreOf hp Y))
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : M.subgroupOf H ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hnorm, hcop⟩
  calc M = (M.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hMH).symm
    _ ≤ GLAPPrimeCoreOf p H := Subgroup.map_mono hle

end T3Tools

theorem oPrimePOf_le_self {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) : oPrimePOf p H ≤ H :=
  Subgroup.map_subtype_le _

section T3Main

variable {G : Type*} [Group G]

theorem oPrimePOf_le_of_normal [Finite G] {p : ℕ} (hp : p.Prime) {C N : Subgroup G} (hCN : C ≤ N)
    (hn : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) : oPrimePOf p C ≤ oPrimePOf p N := by
  have hCN' : (C.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hCN).2 fun h k hh hk => hn k hk h hh
  have hcore := glaPPrimeCoreOf_le_of_normal (p := p) hp hCN hCN'
  have hOC : oPrimePOf p C ≤ C := oPrimePOf_le_self C
  refine t3_le_oPrimePOf (hOC.trans hCN) ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff (hOC.trans hCN)]
    intro s k hs hk
    exact t3_conj_mem hn hk hs
  · intro s hs
    obtain ⟨n, hn⟩ := t3_pow_mem hs
    exact ⟨n, hcore hn⟩

theorem oPrimePOf_inf_le [Finite G] {p : ℕ} (hp : p.Prime) {Y H : Subgroup G} (hHY : H ≤ Y) :
    oPrimePOf p Y ⊓ H ≤ oPrimePOf p H := by
  refine t3_le_oPrimePOf inf_le_right ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro s k hs hk
    exact ⟨t3_conj (t3_oPrimePOf_normal p Y) hs.1 (oPrimePOf_le_self Y hs.1) (hHY hk),
      H.mul_mem (H.mul_mem hk hs.2) (H.inv_mem hk)⟩
  · intro s hs
    obtain ⟨n, hn⟩ := t3_pow_mem hs.1
    exact ⟨n, t3_inf_le_core hp hHY ⟨hn, H.pow_mem hs.2 _⟩⟩

theorem t3_map_oPrimePOf_le {G₂ : Type*} [Group G₂] [Finite G] {p : ℕ} (hp : p.Prime)
    (ψ : G →* G₂) (A : Subgroup G) (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (oPrimePOf p A).map ψ ≤ oPrimePOf p (A.map ψ) := by
  have hOA : oPrimePOf p A ≤ A := oPrimePOf_le_self A
  have hSH : (oPrimePOf p A).map ψ ≤ A.map ψ := Subgroup.map_mono hOA
  refine t3_le_oPrimePOf hSH ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff hSH]
    rintro _ _ ⟨w, hw, rfl⟩ ⟨a, ha, rfl⟩
    exact ⟨a * w * a⁻¹, t3_conj (t3_oPrimePOf_normal p A) hw (hOA hw) ha, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨n, hn⟩ := t3_pow_mem hw
    obtain ⟨t, ht, hte⟩ := hn
    have hmem : ψ.subgroupMap A t ∈ GLAPPrimeCore p ↥(A.map ψ) := by
      rw [← glaPPrimeCore_map_subgroupMap hp ψ A hker]
      exact ⟨t, ht, rfl⟩
    refine ⟨n, ψ.subgroupMap A t, hmem, ?_⟩
    rw [← map_pow, ← hte]
    rfl

theorem mk_mem_oPrimePOf_barX [Finite G] {p : ℕ} (hp : p.Prime) {C H : Subgroup G} (hHC : H ≤ C)
    {b : G} (hb : b ∈ oPrimePOf p H) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hHC (oPrimePOf_le_self H hb)⟩ ∈
      oPrimePOf p (barX p C H) := by
  have : Fact p.Prime := ⟨hp⟩
  set ψ := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hψ
  set X : Subgroup ↥C := H.subgroupOf C with hX
  have hker : Nat.Coprime p (Nat.card ↥(X ⊓ ψ.ker)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C))
    have : (X ⊓ ψ.ker : Subgroup ↥C) ≤ GLAPPrimeCore p ↥C := by
      rw [hψ, QuotientGroup.ker_mk']
      exact inf_le_right
    exact Subgroup.card_dvd_of_le this
  have h1 : (⟨b, hHC (oPrimePOf_le_self H hb)⟩ : ↥C) ∈ oPrimePOf p X := by
    obtain ⟨y, hy, rfl⟩ := hb
    let e : ↥X ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHC
    exact ⟨e.symm y, t3_map_le e.symm ⟨y, hy, rfl⟩, rfl⟩
  exact t3_map_oPrimePOf_le hp ψ X hker ⟨_, h1, rfl⟩

end T3Main

private theorem t4_isPGroup_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hcore : GLAPPrimeCore p Y = ⊥) : IsPGroup p ↥(Subgroup.center Y) := by
  intro z
  have hz0 : orderOf (z : Y) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0 p hp.ne_one
  have hzc : (z : Y) ∈ Subgroup.center Y := z.2
  set w : Y := (z : Y) ^ (p ^ e) with hw
  have hwc : w ∈ Subgroup.center Y := Subgroup.pow_mem _ hzc _
  have hord : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hem ▸ dvd_mul_right _ _), hem,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hS : Subgroup.zpowers w ≤ GLAPPrimeCore p Y := by
    have hle : Subgroup.zpowers w ≤ Subgroup.center Y := (Subgroup.zpowers_le).2 hwc
    refine le_sSup ⟨Subgroup.normal_of_le_center hle, ?_⟩
    rw [Nat.card_zpowers, hord]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hw1 : w = 1 := by
    have := hS (Subgroup.mem_zpowers w)
    rw [hcore] at this
    exact Subgroup.mem_bot.1 this
  have hm1 : m = 1 := by rw [← hord, hw1, orderOf_one]
  refine ⟨e, Subtype.ext ?_⟩
  simpa [hw] using hw1

private theorem t4_center_eq_pCore {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple Y) (hcore : GLAPPrimeCore p Y = ⊥) :
    Subgroup.center Y = CFSG.pCore p Y := by
  refine le_antisymm (le_sSup ⟨inferInstance, t4_isPGroup_center hp hcore⟩) ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperf, hsimple⟩ := hq
  have hnt : Nontrivial Y := (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  have : Group.IsPerfect Y := ⟨hperf⟩
  set φ := QuotientGroup.mk' (Subgroup.center Y) with hφ
  have hn : ((CFSG.pCore p Y).map φ).Normal :=
    (CFSG.pCore_normal (p := p) (G := Y)).map φ (QuotientGroup.mk'_surjective _)
  have := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore p Y).map φ) with h | h
  · rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have hpg : IsPGroup p ((CFSG.pCore p Y).map φ) := (CFSG.pCore_isPGroup).map φ
    rw [h] at hpg
    have hpg' : IsPGroup p (Y ⧸ Subgroup.center Y) := hpg.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent (Y ⧸ Subgroup.center Y) := hpg'.isNilpotent
    have hnil : Group.IsNilpotent Y :=
      Subgroup.isNilpotent_of_ker_le_center φ (by rw [hφ, QuotientGroup.ker_mk']) 
    exact Group.IsPerfect.not_isNilpotent Y hnil

private noncomputable def t4_quotOPrimeP (p : ℕ) (H : Type*) [Group H] :
    (H ⧸ oPrimeP p H) ≃*
      ((H ⧸ GLAPPrimeCore p H) ⧸ CFSG.pCore p (H ⧸ GLAPPrimeCore p H)) := by
  let φ : H →* ((H ⧸ GLAPPrimeCore p H) ⧸ CFSG.pCore p (H ⧸ GLAPPrimeCore p H)) :=
    (QuotientGroup.mk' (CFSG.pCore p (H ⧸ GLAPPrimeCore p H))).comp
      (QuotientGroup.mk' (GLAPPrimeCore p H))
  have hsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = oPrimeP p H := by
    ext x
    simp [φ, oPrimeP, MonoidHom.mem_ker]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

private noncomputable def t4_quotCenterEquiv {Y K : Type*} [Group Y] [Group K] (e : Y ≃* K) :
    (Y ⧸ Subgroup.center Y) ≃* (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

section Types

variable {G : Type*} [Group G] [Finite G]

theorem isLThreeEpsOrON_barX {C I : Subgroup G} (hI : GLAPComponent 3 C I)
    (h : IsExtremalType (↥I ⧸ oPrimeP 3 ↥I) ∨ IsHatON (barOf 3 I)) :
    IsLThreeEpsOrON (↥(barX 3 C I) ⧸ Subgroup.center ↥(barX 3 C I)) := by
  set e : barOf 3 I ≃* ↥(barX 3 C I) := quotEquivBarX Nat.prime_three hI.1 hI.2.1 with he
  have hY : CFSG.Open.IsQuasisimple (barOf 3 I) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hI.2.2.1.2.2
  have hbot : GLAPPrimeCore 3 (barOf 3 I) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot (Z := ↥I) Nat.prime_three
  have hZ : Subgroup.center (barOf 3 I) = CFSG.pCore 3 (barOf 3 I) :=
    t4_center_eq_pCore Nat.prime_three hY hbot
  let E1 : (↥(barX 3 C I) ⧸ Subgroup.center ↥(barX 3 C I)) ≃* (↥I ⧸ oPrimeP 3 ↥I) :=
    (t4_quotCenterEquiv e).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (t4_quotOPrimeP 3 ↥I).symm)
  rcases h with h | h
  · rcases h with ⟨F, iF, iFin, hc, ⟨f⟩⟩ | ⟨F, iF, iFin, q, hq, hq3, hq8, ⟨f⟩⟩
    · exact Or.inl ⟨F, iF, iFin, by omega, ⟨E1.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨F, iF, iFin, q, hq, by omega, hq8, ⟨E1.trans f⟩⟩)
  · obtain ⟨-, -, ⟨f⟩⟩ := h
    exact Or.inr (Or.inr ⟨(t4_quotCenterEquiv e).symm.trans f⟩)

end Types

section T5

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem t5_comm {B : Subgroup G} (hB : IsElemAbelian 3 B) {g y : G} (hg : g ∈ B)
    (hy : y ∈ B) : g * y * g⁻¹ = y := by
  have := congrArg Subtype.val (hB.1.is_comm.comm ⟨g, hg⟩ ⟨y, hy⟩)
  simp only [Subgroup.coe_mul] at this
  rw [this]; group

omit [Finite G] in
private theorem t5_mem_iff {g y : G} {H : Subgroup G} (h : GLBConj g H = H) :
    g * y * g⁻¹ ∈ H ↔ y ∈ H := by
  rw [← mem_gLBConj, h]

omit [Finite G] in
private theorem t5_conj_le_iff {g : G} {H K : Subgroup G} :
    GLBConj g H ≤ GLBConj g K ↔ H ≤ K := by
  refine ⟨fun h => ?_, gLBConj_mono g⟩
  have := gLBConj_mono g⁻¹ h
  rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this

omit [Finite G] in
private theorem t5_le_conj_inv (g : G) {F T : Subgroup G} (h : GLBConj g F ≤ T) :
    F ≤ GLBConj g⁻¹ T := fun y hy => by
  rw [mem_gLBConj, inv_inv]
  exact h (mem_gLBConj.2 (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]))

omit [Finite G] in
private theorem t5_conj_le_of_le_conj_inv (g : G) {F T : Subgroup G} (h : F ≤ GLBConj g⁻¹ T) :
    GLBConj g F ≤ T :=
  (gLBConj_mono g h).trans (by rw [gLBConj_gLBConj_inv])

omit [Finite G] in
private theorem t5_conj_sSup_le (g : G) (S : Set (Subgroup G)) (T : Subgroup G)
    (h : ∀ L ∈ S, GLBConj g L ≤ T) : GLBConj g (sSup S) ≤ T :=
  t5_conj_le_of_le_conj_inv g (sSup_le fun L hL => t5_le_conj_inv g (h L hL))

omit [Finite G] in
private theorem t5_conj_cent {B : Subgroup G} (hB : IsElemAbelian 3 B) {b g : G} (hb : b ∈ B)
    (hg : g ∈ B) : GLBConj g (Subgroup.centralizer ({b} : Set G)) =
      Subgroup.centralizer ({b} : Set G) :=
  gLBConj_centralizer_singleton_of_commute (by
    have := t5_comm hB hg hb
    calc g * b = g * b * g⁻¹ * g := by group
      _ = b * g := by rw [this])

omit [Finite G] in
private theorem t5_conj_core {B : Subgroup G} (hB : IsElemAbelian 3 B) {b g : G} (hb : b ∈ B)
    (hg : g ∈ B) : GLBConj g (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) =
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  rw [← glaPPrimeCoreOf_gLBConj, t5_conj_cent hB hb hg]

omit [Finite G] in
private theorem t5_conj_centB {B : Subgroup G} (hB : IsElemAbelian 3 B) {g : G} (hg : g ∈ B) :
    GLBConj g (Subgroup.centralizer (B : Set G)) = Subgroup.centralizer (B : Set G) := by
  refine gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := t5_comm hB hg hh
  calc h * g = g * h * g⁻¹ * g := by rw [this]
    _ = g * h := by group

omit [Finite G] in
private theorem t5_conj_coreB {B : Subgroup G} (hB : IsElemAbelian 3 B) {g : G} (hg : g ∈ B) :
    GLBConj g (GLAPPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) =
      GLAPPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) := by
  rw [← glaPPrimeCoreOf_gLBConj, t5_conj_centB hB hg]

omit [Finite G] in
private theorem t5_conj_delta {B D : Subgroup G} (hB : IsElemAbelian 3 B) (hD : D ≤ B) {g : G}
    (hg : g ∈ B) : GLBConj g (GLADelta 3 D) = GLADelta 3 D := by
  ext y
  rw [mem_gLBConj]
  unfold GLADelta
  simp only [Subgroup.mem_iInf]
  refine forall_congr' fun d => forall_congr' fun hd => forall_congr' fun _ => ?_
  exact t5_mem_iff (t5_conj_core hB (hD hd) hg)

omit [Finite G] in
private theorem t5_conj_comm (g : G) (X Y : Subgroup G) :
    GLBConj g ⁅X, Y⁆ = ⁅GLBConj g X, GLBConj g Y⁆ :=
  Subgroup.map_commutator X Y (MulAut.conj g⁻¹).toMonoidHom

private theorem t5_comp {B : Subgroup G} (hB : IsElemAbelian 3 B) {b g : G} (hb : b ∈ B)
    (hg : g ∈ B) {L : Subgroup G} (h : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L) :
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g L) := by
  have := glaPComponent_gLBConj g h
  rwa [t5_conj_cent hB hb hg] at this

omit [Finite G] in
private theorem t5_slob {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G} (hx : x ∈ B) {g : G}
    (hg : g ∈ B) {L : Subgroup G} (h : IsStronglyLocallyOneBalanced 3 B x L) :
    IsStronglyLocallyOneBalanced 3 B x (GLBConj g L) := by
  intro S hS hcop hBS
  have e : Subgroup.normalizer (GLBConj g L : Set G) ⊓ Subgroup.centralizer ({x} : Set G) =
      GLBConj g (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [gLBConj_inf, normalizer_gLBConj, t5_conj_cent hB hx hg]
  have hS' : GLBConj g⁻¹ S ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
    have := gLBConj_mono g⁻¹ (hS.trans e.le)
    rwa [gLBConj_inv_gLBConj] at this
  have hcard : Nat.card (GLBConj g⁻¹ S) = Nat.card S := by
    have hinj : Function.Injective (MulAut.conj g⁻¹⁻¹).toMonoidHom := (MulAut.conj g⁻¹⁻¹).injective
    exact Subgroup.card_map_of_injective hinj
  have hBS' : B ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (GLBConj g⁻¹ S : Set G) := by
    rintro b ⟨hbB, hbN⟩
    have hbN' : b ∈ Subgroup.normalizer (GLBConj g L : Set G) := by
      rw [normalizer_gLBConj, mem_gLBConj, t5_comm hB hg hbB]
      exact hbN
    have hbS := hBS ⟨hbB, hbN'⟩
    have hc := t5_comm hB (B.inv_mem hg) hbB
    rw [inv_inv] at hc
    rw [normalizer_gLBConj, mem_gLBConj, inv_inv, hc]
    exact hbS
  have key := h _ hS' (hcard ▸ hcop) hBS'
  have := gLBConj_mono g key
  rwa [t5_conj_comm, gLBConj_gLBConj_inv, ← glaPPrimeCoreOf_gLBConj] at this

private theorem t5_lambda_le {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G} (hx : x ∈ B)
    {g : G} (hg : g ∈ B) : GLBConj g (lambdaOf 3 B x) ≤ lambdaOf 3 B x := by
  unfold lambdaOf
  refine t5_conj_sSup_le g _ _ ?_
  rintro L ⟨hL, hnb⟩
  refine le_sSup ⟨t5_comp hB hx hg hL, fun hs => hnb ?_⟩
  have := t5_slob hB hx (B.inv_mem hg) hs
  rwa [gLBConj_inv_gLBConj] at this

omit [Finite G] in
private theorem t5_bClosure {B : Subgroup G} {g : G} (hg : g ∈ B) (L : Subgroup G) :
    bClosure B (GLBConj g L) = bClosure B L := by
  unfold bClosure
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (g * b) (B.mul_mem hg hb) le_rfl
  · refine iSup₂_le fun b hb => ?_
    refine le_iSup₂_of_le (g⁻¹ * b) (B.mul_mem (B.inv_mem hg) hb) ?_
    rw [gLBConj_gLBConj, show g * (g⁻¹ * b) = b by group]

private theorem t5_psiOf_le {B : Subgroup G} (hB : IsElemAbelian 3 B) {b : G} (hb : b ∈ B)
    {g : G} (hg : g ∈ B) : GLBConj g (psiOf 3 B b) ≤ psiOf 3 B b := by
  unfold psiOf
  refine t5_conj_sSup_le g _ _ ?_
  rintro L ⟨hL, hnb, hG⟩
  refine le_sSup ⟨t5_comp hB hb hg hL, fun hs => hnb ?_, ?_⟩
  · have := t5_slob hB hb (B.inv_mem hg) hs
    rwa [gLBConj_inv_gLBConj] at this
  · unfold IsInGOne at hG ⊢
    rwa [t5_bClosure hg]

private theorem t5_psiStar_le {B : Subgroup G} (hB : IsElemAbelian 3 B) {b : G} (hb : b ∈ B)
    {g : G} (hg : g ∈ B) : GLBConj g (psiStar 3 B b) ≤ psiStar 3 B b := by
  have hs : ∀ X Y : Subgroup G, GLBConj g (X ⊔ Y) = GLBConj g X ⊔ GLBConj g Y :=
    fun X Y => Subgroup.map_sup _ _ _
  unfold psiStar
  rw [hs, hs]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (t5_psiOf_le hB hb hg).trans (le_sup_left.trans le_sup_left)
  · exact (t5_conj_core hB hb hg).le.trans (le_sup_right.trans le_sup_left)
  · exact (t5_conj_coreB hB hg).le.trans le_sup_right

private theorem t5_psiStarGroup_le {B : Subgroup G} (hB : IsElemAbelian 3 B) {g : G}
    (hg : g ∈ B) : GLBConj g (psiStarGroup 3 B) ≤ psiStarGroup 3 B := by
  refine t5_conj_le_of_le_conj_inv g ?_
  unfold psiStarGroup
  refine iSup₂_le fun b hb => iSup_le fun hb1 => t5_le_conj_inv g ?_
  exact (t5_psiStar_le hB hb hg).trans
    (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)))

theorem isUpsilonComponent_gLBConj {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G} (hx : x ∈ B)
    {L : Subgroup G} (h : IsUpsilonComponent B x L) {g : G} (hg : g ∈ B) :
    IsUpsilonComponent B x (GLBConj g L) := by
  obtain ⟨hcomp, halt⟩ := h
  refine ⟨t5_comp hB hx hg hcomp, ?_⟩
  rcases halt with ⟨hΛ, hψ⟩ | ⟨D, hD, hnot⟩
  · refine Or.inl ⟨(gLBConj_mono g hΛ).trans (t5_lambda_le hB hx hg), fun hle => hψ ?_⟩
    have h1 := gLBConj_mono g⁻¹ hle
    rw [gLBConj_inv_gLBConj] at h1
    exact h1.trans (t5_psiStarGroup_le hB (B.inv_mem hg))
  · refine Or.inr ⟨D, hD, fun hle => hnot ?_⟩
    have hconj : GLBConj g ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({x} : Set G)⁆ =
        ⁅GLBConj g L, GLADelta 3 D ⊓ Subgroup.centralizer ({x} : Set G)⁆ := by
      rw [t5_conj_comm, gLBConj_inf, t5_conj_delta hB hD.1 hg, t5_conj_cent hB hx hg]
    rw [← hconj, glaPPrimeCoreOf_gLBConj] at hle
    exact t5_conj_le_iff.1 hle

end T5

section TwoGroupLift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem t6_normalizerMonoidHom_coe {L : Subgroup G} (γ : ↥(Subgroup.normalizer (L : Set G)))
    (x : ↥L) : ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * x * (γ : G)⁻¹ := rfl

omit [Finite G] in
private theorem t6_conj_mem_core {L : Subgroup G} (γ : ↥(Subgroup.normalizer (L : Set G))) {n : G}
    (hn : n ∈ GLAPPrimeCoreOf 3 L) : (γ : G) * n * (γ : G)⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
  obtain ⟨y, hy, rfl⟩ := hn
  have h := map_gLAPPrimeCore_le 3 (L.normalizerMonoidHom γ)
  refine ⟨L.normalizerMonoidHom γ y, h ⟨y, hy, rfl⟩, ?_⟩
  simp

private theorem t6_coprime_even {E Y : Subgroup G} (hE : IsPGroup 3 E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (hcop : ¬ 3 ∣ Nat.card Y) (heven : Even (Nat.card Y)) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ T ≤ Y ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTY, hT2, hTc, hET⟩ := exists_sylow_normalized_of_not_dvd (p := 3) (q := 2) Y E hE hEY hcop
  refine ⟨T, ?_, hTY, hT2, hET⟩
  intro h
  have h1 := hTc 1 (by simpa using even_iff_two_dvd.1 heven)
  rw [h, Subgroup.card_bot] at h1
  simp at h1

theorem exists_twoGroup_lift {L A : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (Tb : Subgroup (barOf 3 L)) (hTb : Tb ≠ ⊥)
    (hTb2 : IsPGroup 2 Tb)
    (hinv : ∀ a : ↥(Subgroup.normalizer (L : Set G)), (a : G) ∈ A →
      Tb.map (barAut 3 L a).toMonoidHom = Tb) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ T ≤ L ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G) := by
  set P' : Subgroup ↥L := Tb.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hP'
  set P : Subgroup G := P'.map L.subtype with hP
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨x, hx, rfl⟩ := hg
    have hxT : (QuotientGroup.mk x : barOf 3 L) ∈ Tb := hx
    refine ⟨L.normalizerMonoidHom ⟨a, hAL ha⟩ x, ?_, ?_⟩
    · show (QuotientGroup.mk (L.normalizerMonoidHom ⟨a, hAL ha⟩ x) : barOf 3 L) ∈ Tb
      rw [← barAut_mk]
      rw [← hinv ⟨a, hAL ha⟩ ha]
      exact ⟨_, hxT, rfl⟩
    · simp
  have hcardP' : Nat.card P' = Nat.card Tb * Nat.card (GLAPPrimeCore 3 ↥L) := by
    have hidx : P'.index = Tb.index :=
      Subgroup.index_comap_of_surjective Tb (QuotientGroup.mk'_surjective _)
    have h1 : P'.index * Nat.card P' = Nat.card ↥L := Subgroup.index_mul_card P'
    have h2 : Tb.index * Nat.card Tb = Nat.card (barOf 3 L) := Subgroup.index_mul_card Tb
    have h3 : Nat.card (barOf 3 L) * Nat.card (GLAPPrimeCore 3 ↥L) = Nat.card ↥L := by
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)).symm
    have hpos : 0 < Tb.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hidx] at h1
    rw [← h2] at h3
    rw [h1, ← h3]
    ring
  have hcardP : Nat.card P = Nat.card Tb * Nat.card (GLAPPrimeCore 3 ↥L) := by
    rw [hP, Subgroup.card_map_of_injective L.subtype_injective, hcardP']
  obtain ⟨k, hk⟩ := hTb2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hTb
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hk
  have hOc : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := by
    rw [← Nat.prime_three.coprime_iff_not_dvd]
    exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
      Nat.prime_three _
  have hTc : ¬ 3 ∣ Nat.card Tb := by
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have hPc : ¬ 3 ∣ Nat.card P := by
    rw [hcardP]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact hTc h
    · exact hOc h
  have hPeven : Even (Nat.card P) := by
    rw [even_iff_two_dvd, hcardP, hk]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hk0) _
  obtain ⟨T, hT0, hTP, hT2, hAT⟩ :=
    t6_coprime_even hA3 hAP hPc hPeven
  exact ⟨T, hT0, hTP.trans hPL, hT2, hAT⟩

theorem exists_twoGroup_of_field (hFT : InputFeitThompson) (iFA : InputFieldAutTwo) {b : G}
    {A L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hA3 : IsPGroup 3 (A ⊔ Subgroup.zpowers b : Subgroup G))
    (hAC : A ≤ Subgroup.centralizer ({b} : Set G))
    (hfield : ∀ a ∈ A, InducesFieldAut 3 L a) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      A ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (T : Set G) := by
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) := fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]
  have hLC : L ≤ Subgroup.centralizer ({b} : Set G) := hL.1
  have hbL : ∀ x ∈ L, x * b = b * x := fun x hx => (hLC hx b rfl).symm
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := fun a ha => (hfield a ha).1
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have : b * x * b⁻¹ = x := by rw [← hbL x hx]; group
    rw [this]; exact hx
  by_cases h1 : ∀ a (ha : a ∈ A), barAut 3 L ⟨a, hAN ha⟩ = 1
  ·
    have hAQ : A ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
      intro a ha
      refine ⟨hAN ha, ?_, fun x hx => ?_⟩
      · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
        have := t6_conj_mem_core ⟨a, hAN ha⟩ hn
        exact this
      · have hx' := congrArg (fun σ => σ (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥L))) (h1 a ha)
        simp only [barAut_mk, MulAut.one_apply] at hx'
        have hq := QuotientGroup.eq.1 hx'.symm
        refine ⟨_, hq, ?_⟩
        simp [mul_assoc]
    have hULL : GLAPPrimeCoreOf 3 L ≤ L := Subgroup.map_subtype_le _
    have hbQ : Subgroup.zpowers b ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
      rw [Subgroup.zpowers_le]
      refine ⟨hbN, ?_, fun x hx => ?_⟩
      · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
        have : b * n * b⁻¹ = n := by rw [← hbL n (hULL hn)]; group
        rw [this]; exact hn
      · have : x * b * x⁻¹ * b⁻¹ = 1 := by rw [hbL x hx]; group
        rw [this]; exact one_mem _
    have hSQ := sup_le hAQ hbQ
    have hAX : A ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({b} : Set G) :=
      sup_le hAC (Subgroup.zpowers_le.2 hbC)
    refine exists_twoGroup_normalized_of_centralizes hFT Nat.prime_three (by norm_num) hL hAX hA3 ?_
    refine (Subgroup.commutator_le.2 fun x hx g hg => ?_).trans
      (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1)
    rw [commutatorElement_def]
    exact (hSQ hg).2.2 x hx
  · push Not at h1
    obtain ⟨a₀, ha₀, hne⟩ := h1
    have hA3' : IsPGroup 3 A := hA3.of_injective (Subgroup.inclusion le_sup_left) (Subgroup.inclusion_injective _)
    have hmem : ∀ γ : ↥(Subgroup.normalizer (L : Set G)), (γ : G) ∈ A →
        barAut 3 L γ ∈ autBar 3 A L := fun γ hγ =>
      ⟨γ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hγ, γ.2⟩), rfl⟩
    have hAb3 : IsPGroup 3 (autBar 3 A L) := by
      intro g
      obtain ⟨γ, hγ, hg⟩ := g.2
      have hγA : (γ : G) ∈ A := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
      obtain ⟨k, hk⟩ := hA3' ⟨γ, hγA⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : γ ^ (3 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      show (g : MulAut (barOf 3 L)) ^ (3 ^ k) = 1
      rw [← hg, ← map_pow, h1, map_one]
    have hfAb : ∀ α ∈ autBar 3 A L, IsFieldAutThree α := by
      rintro α ⟨γ, hγ, rfl⟩
      have hγA : (γ : G) ∈ A := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
      obtain ⟨h, hh⟩ := hfield γ hγA
      exact hh
    obtain ⟨Tb, hTb, hTb2, hinvAb⟩ := iFA (barOf 3 L) (autBar 3 A L) hAb3 hfAb
      ⟨barAut 3 L ⟨a₀, hAN ha₀⟩, hmem _ ha₀, hne⟩
    obtain ⟨T, hT0, hTL, hT2, hAT⟩ := exists_twoGroup_lift hA3' hAN Tb hTb hTb2
      fun a ha => hinvAb _ (hmem a ha)
    have hbT : b ∈ Subgroup.normalizer (T : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have : b * x * b⁻¹ = x := by rw [← hbL x (hTL hx)]; group
      rw [this]; exact hx
    exact ⟨T, hT0, hT2, sup_le hAT (Subgroup.zpowers_le.2 hbT)⟩

end TwoGroupLift

section TwoGroup

variable {G : Type} [Group G] [Finite G]

theorem isBZeroMax_of_twoGroup {m : ℕ} (hS : GLStanding G m 3) {B : Subgroup G}
    (hB : IsElemAbelian 3 B) (hrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {A : Subgroup G} (hA : IsEkIn 3 3 B A)
    (hT : ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      A ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (T : Set G))
    (hcore : ∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G))) :
    IsBZeroMax 3 B := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAB, hAe, hAcard⟩ := hA
  obtain ⟨T₀, hT₀ne, hT₀2, hAT₀⟩ := hT
  set B' : Subgroup G := A ⊔ Subgroup.zpowers b with hB'def
  have hAB' : A ≤ B' := le_sup_left
  have hbB' : b ∈ B' := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hB'B : B' ≤ B := sup_le hAB (Subgroup.zpowers_le.2 hb)
  have hB'e : IsElemAbelian 3 B' := isElemAbelian_mono hB hB'B
  have hB'ne : B' ≠ ⊥ := fun h => hb1 (Subgroup.mem_bot.1 (h ▸ hbB'))
  let S0 : Set (Subgroup G) :=
    {T' | IsPGroup 2 T' ∧ B' ≤ Subgroup.normalizer (T' : Set G) ∧ T₀ ≤ T'}
  obtain ⟨T, hTS, hTmax⟩ := (Set.toFinite S0).exists_maximalFor id S0 ⟨T₀, hT₀2, hAT₀, le_rfl⟩
  obtain ⟨hT2, hB'T, hT₀T⟩ := hTS
  have hTne : T ≠ ⊥ := fun h => hT₀ne (le_bot_iff.1 (h ▸ hT₀T))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B' ≤ Subgroup.normalizer (T' : Set G) →
      T ≤ T' → T' = T := fun T' h2 hN hle =>
    le_antisymm (hTmax ⟨h2, hN, hT₀T.trans hle⟩ hle) hle
  obtain ⟨A₁, hA₁B', hA₁i, hne⟩ :=
    (GL83.I_33_1_proved G hS.charTwo 3 hp3 (by norm_num) B' T hB'ne hB'e hT2 hB'T
      (Or.inl ⟨hTne, hmax⟩)).1 b hbB' hb1
  have hDcard : 3 ^ 2 ∣ Nat.card (A ⊓ A₁ : Subgroup G) := by
    have hsub : (A ⊓ A₁).subgroupOf A = A₁.subgroupOf A := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    have h1 : Nat.card A = Nat.card ((A ⊓ A₁).subgroupOf A) * ((A ⊓ A₁).subgroupOf A).index :=
      (Subgroup.card_mul_index _).symm
    have h2 : Nat.card ((A ⊓ A₁).subgroupOf A) = Nat.card (A ⊓ A₁ : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h3 : (A₁.subgroupOf A).index ≤ 3 := by
      have := Subgroup.relIndex_le_of_le_right (H := A₁) hAB' (by
        unfold Subgroup.relIndex; rw [hA₁i]; norm_num)
      unfold Subgroup.relIndex at this
      rwa [hA₁i] at this
    rw [h2, hsub, hAcard] at h1
    set d := (A₁.subgroupOf A).index with hd
    have h1' : Nat.card (A ⊓ A₁ : Subgroup G) * d = 27 := h1.symm.trans (by norm_num)
    have hdd : d ∣ 27 := Dvd.intro_left _ h1'
    have hd0 : d ≠ 0 := by
      rintro h; rw [h] at hdd; omega
    interval_cases d <;> omega
  obtain ⟨E, hEDle, hEe, hEcard⟩ := exists_le_isElemAbelian_card (p := 3)
    (isElemAbelian_mono hAe (inf_le_left : A ⊓ A₁ ≤ A)) hDcard
  have hEA : E ≤ A := hEDle.trans inf_le_left
  have hEA₁ : E ≤ A₁ := hEDle.trans inf_le_right
  have hEB : E ≤ B := hEA.trans hAB
  have hE0 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    omega
  set X : Subgroup G := T ⊓ Subgroup.centralizer (E : Set G) with hXdef
  have hbT : b ∈ Subgroup.normalizer (T : Set G) := hB'T hbB'
  have hbX : b ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_inf_centralizer hbT fun a ha => elemAbelian_comm hB (hEB ha) hb
  have hbdn : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    Subgroup.le_normalizer
  have hPX : Subgroup.zpowers b ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.2 hbX
  have hX2 : IsPGroup 2 X := hT2.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers b)) (Nat.card X) := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hb) hb1]
    obtain ⟨j, hj⟩ := hX2.exists_card_eq
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hsolv : Group.IsSolvable X := by
    have := IsPGroup.isNilpotent hX2
    infer_instance
  have hdouble : ⁅⁅X, Subgroup.zpowers b⁆, Subgroup.zpowers b⁆ = ⁅X, Subgroup.zpowers b⁆ :=
    GL83.commutator_double_eq_self (Subgroup.zpowers b) X hPX hcop hsolv
  set S : Subgroup G := ⁅X, Subgroup.zpowers b⁆ with hSdef
  have hSne : S ≠ ⊥ := by
    intro h
    apply hne
    have h' : ⁅Subgroup.zpowers b, X⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h
    refine eq_bot_iff.2 ((Subgroup.commutator_mono le_rfl ?_).trans h'.le)
    exact inf_le_inf_left _ (Subgroup.centralizer_le fun x hx => hEA₁ hx)
  have hSle : S ≤ X := GL83.commutator_le_of_le_normalizer hPX
  have hS2 : IsPGroup 2 S := hT2.to_le (hSle.trans inf_le_left)
  have hSN : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ X _ hPX hbdn
  have hSC : ∀ e ∈ E, S ≤ Subgroup.centralizer ({e} : Set G) := fun e he =>
    hSle.trans (inf_le_right.trans (Subgroup.centralizer_le fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]; exact he))
  have hSΔ : S ≤ GLADelta 3 E := by
    refine le_iInf fun e => le_iInf fun he => le_iInf fun he1 => ?_
    calc S = ⁅S, Subgroup.zpowers b⁆ := hdouble.symm
      _ ≤ _ := by
        rw [Subgroup.commutator_le]
        intro s hs y hy
        have hyo : y ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set G)) :=
          Subgroup.zpowers_le.2 (hcore e (hEA he) he1) hy
        rw [commutatorElement_def]
        exact comm_mem_gLAPPrimeCoreOf_of_mem_oPrimePOf hp3 (by norm_num) hS2 (hSC e he) hyo
          (hSN hy) hs
  have hSeven : 2 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hSne (Subgroup.card_eq_one.1 (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hSB : S ≤ ⁅GLADelta 3 E, B⁆ := by
    calc S = ⁅S, Subgroup.zpowers b⁆ := hdouble.symm
      _ ≤ ⁅GLADelta 3 E, B⁆ := Subgroup.commutator_mono hSΔ (Subgroup.zpowers_le.2 hb)
  have hΔeven : 2 ∣ Nat.card (GLADelta 3 E) := hSeven.trans (Subgroup.card_dvd_of_le hSΔ)
  have hWcop : Nat.Coprime 3 (Nat.card (GLADelta 3 E)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp3 hE0
  have hconj : ∀ e ∈ B, ∀ w ∈ GLADelta 3 E, e * w * e⁻¹ ∈ GLADelta 3 E := by
    intro e he w hw
    simp only [GLADelta, Subgroup.mem_iInf] at hw ⊢
    intro d hd hd1
    have hec : e ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact elemAbelian_comm hB (hEB hd) he
    exact mem_gLAPPrimeCoreOf_conj (hw d hd hd1) hec
  have hBΔ : B ≤ Subgroup.normalizer (GLADelta 3 E : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun n hn => hconj e he n hn
  obtain ⟨Q, -, hQ2, hQc, hBQ⟩ := exists_sylow_normalized_of_not_dvd (q := 2) (GLADelta 3 E) B
    (GL83.isPGroup_of_isElemAbelian hB) hBΔ (hp3.coprime_iff_not_dvd.1 hWcop)
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := hQc 1 (by simpa using hΔeven)
    rw [h, Subgroup.card_bot] at h1
    simp at h1
  have hloc : IsTwoLocal (Subgroup.normalizer (Q : Set G)) := ⟨Q, hQ1, hQ2, rfl⟩
  obtain ⟨j, hj⟩ := exists_card_eq_pow (GL83.isPGroup_of_isElemAbelian hB)
  have h1 : j ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.SectionRank.le_pRank hp3.one_lt hBQ hB hj
  have h2 : CFSG.Open.pRank 3 (Subgroup.normalizer (Q : Set G)) ≤ GLATwoLocalRank 3 G :=
    le_csSup ⟨CFSG.Open.pRank 3 (⊤ : Subgroup G), by
      rintro i ⟨H, -, rfl⟩
      exact CFSG.SectionRank.pRank_mono hp3.one_lt le_top⟩ ⟨_, hloc, rfl⟩
  have h3 : CFSG.Open.pRank 3 B ≤ j := by
    unfold CFSG.Open.pRank
    refine csSup_le' ?_
    rintro i ⟨E', hE'B, -, hE'c⟩
    have := Subgroup.card_dvd_of_le hE'B
    rw [hE'c, hj] at this
    exact (Nat.pow_dvd_pow_iff_le_right hp3.one_lt).1 this
  have hjeq : j = GLATwoLocalRank 3 G := le_antisymm (h1.trans h2) (hrank.trans h3)
  have hBmax : GLAIsBmax 3 B := ⟨hB, hj.trans (by rw [hjeq]), Q, hQ1, hQ2, hBQ⟩
  refine ⟨hBmax, E, hEB, ⟨hEe, hEcard⟩, fun h => absurd h (by norm_num), fun _ => ?_⟩
  exact even_iff_two_dvd.2 (hSeven.trans (Subgroup.card_dvd_of_le hSB))

end TwoGroup

section Aux

variable {G : Type*} [Group G]

theorem card_barX_of_isPGroup' [Finite G] {p : ℕ} (hp : p.Prime) {C E : Subgroup G}
    (hE : IsPGroup p E) (hEC : E ≤ C) : Nat.card (barX p C E) = Nat.card E := by
  set f := (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (E.subgroupOf C).subtype with hf
  have hfi := injective_barX_comp hp hE hEC
  have hrange : f.range = barX p C E := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv]

theorem barX_sSup (p : ℕ) {C : Subgroup G} {S : Set (Subgroup G)} (hS : ∀ K ∈ S, K ≤ C) :
    barX p C (sSup S) = ⨆ K ∈ S, barX p C K := by
  unfold barX
  have hmap : ((sSup S).subgroupOf C) = ⨆ K ∈ S, K.subgroupOf C := by
    set T : Subgroup ↥C := ⨆ K ∈ S, K.subgroupOf C with hT
    have h1 : T.map C.subtype = sSup S := by
      rw [hT, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
      apply le_antisymm
      · refine iSup₂_le fun K hK => ?_
        rw [Subgroup.map_subgroupOf_eq_of_le (hS K hK)]
        exact le_sSup hK
      · refine sSup_le fun K hK => ?_
        refine le_trans ?_ (le_iSup₂ K hK)
        rw [Subgroup.map_subgroupOf_eq_of_le (hS K hK)]
    have h2 : (T.map C.subtype).subgroupOf C = T :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective T
    rw [← h1, h2]
  rw [hmap, Subgroup.map_iSup]
  simp only [Subgroup.map_iSup]

theorem inf_gLAPPrimeCoreOf_le [Finite G] {p : ℕ} (hp : p.Prime) {H C : Subgroup G} (hHC : H ≤ C) :
    H ⊓ GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p H := by
  set K : Subgroup G := H ⊓ GLAPPrimeCoreOf p C with hK
  have hnorm : (K.subgroupOf H).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnH, hnO⟩ := hn
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem h.2 hnH) (H.inv_mem h.2)
      simpa using this
    · have := mem_gLAPPrimeCoreOf_conj hnO (hHC h.2)
      simpa using this
  have hcop : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ≤ H)).toEquiv]
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_right : K ≤ _)) ?_
    rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective C.subtype_injective]
    exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp _
  have hle : K.subgroupOf H ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx), rfl⟩

end Aux

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_upsilonOf {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G} (hx : x ∈ B) :
    B ≤ Subgroup.normalizer (upsilonOf B x : Set G) := by
  have hconj : ∀ g ∈ B, GLBConj g (upsilonOf B x) ≤ upsilonOf B x := by
    intro g hg
    refine t5_conj_sSup_le g _ _ fun L hL => ?_
    exact le_sSup (isUpsilonComponent_gLBConj hB hx hL hg)
  intro g hg
  have h1 := hconj g hg
  have h2 := gLBConj_mono g (hconj g⁻¹ (B.inv_mem hg))
  rw [gLBConj_gLBConj_inv] at h2
  exact mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h1 h2)

end Normalizer

section Heart

variable {Q : Type} [Group Q] [Finite Q]

theorem layer_le_centralizer_of_mem_oPrimeP (i14 : Input14_5Three) (hQ : CFSG.Open.IsKGroup Q)
    (hcore : GLAPPrimeCore 3 Q = ⊥) {Y : Subgroup Q} {e r : Q}
    (he : IsPGroup 3 (Subgroup.zpowers e : Subgroup Q)) (he1 : e ≠ 1)
    (hY : IsSubnormal Y (Subgroup.centralizer ({e} : Set Q)))
    (hr : r ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set Q))) :
    GLAPLayer 3 Y ≤ Subgroup.centralizer ({r} : Set Q) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set P : Subgroup Q := Subgroup.zpowers e with hP
  set N : Subgroup Q := Subgroup.normalizer (P : Set Q) with hN
  set C : Subgroup Q := Subgroup.centralizer ({e} : Set Q) with hC
  have hCP : C = Subgroup.centralizer (P : Set Q) := by
    rw [hC, hP, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCN : C ≤ N := by
    rw [hCP]; exact Subgroup.centralizer_le_normalizer (P : Set Q)
  have hn : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    rw [hCP, Subgroup.mem_centralizer_iff] at hc ⊢
    intro p hp
    have h1 : n⁻¹ * p * n⁻¹⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (N.inv_mem hn) p).1 hp
    have h2 := hc _ h1
    simp only [inv_inv] at h1 h2
    calc p * (n * c * n⁻¹) = n * ((n⁻¹ * p * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * p * n)) * n⁻¹ := by rw [h2]
      _ = n * c * n⁻¹ * p := by group
  have hCN' : IsSubnormal C N := by
    refine IsSubnormal.step hCN ?_ (IsSubnormal.refl N)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN]
    intro n hn'
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; exact hn n hn' z hz
    · intro hz
      have := hn n⁻¹ (N.inv_mem hn') _ hz
      simpa [mul_assoc] using this
  have hYN : IsSubnormal Y N := isSubnormal_trans' hY hCN'
  have hPne : P ≠ ⊥ := by
    intro h
    apply he1
    have : e ∈ P := Subgroup.mem_zpowers e
    rw [h] at this
    exact (Subgroup.mem_bot.1 this)
  have hO := i14 Q hQ hcore P hPne he
  have hOW : GLAPPrimeCoreOf 3 N ≤ Subgroup.centralizer (GLAPLayer 3 N : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hO
  have hrN : r ∈ oPrimePOf 3 N := oPrimePOf_le_of_normal hp3 hCN hn hr
  have hrN' : r ∈ N := oPrimePOf_le_self N hrN
  have hWr : GLAPLayer 3 N ≤ Subgroup.centralizer ({r} : Set Q) :=
    le_centralizer_of_perfect (layer_perfect 3 N) hOW
      (fun u hu => mem_layer_conj 3 hrN' hu)
      (fun u hu => commutator_mem_core_of_mem_layer hp3 hrN hu)
  exact (glaPLayer_le_of_isSubnormal hp3 hYN).trans hWr

theorem heart (i23 : Input23_26) (i14 : Input14_5Three) (hQ : CFSG.Open.IsKGroup Q)
    (hcore : GLAPPrimeCore 3 Q = ⊥) {L E : Subgroup Q} {𝒦 : Set (Subgroup Q)}
    (h𝒦 : ∀ K ∈ 𝒦, IsComponentOf K ⊤ ∧ IsLThreeEpsOrON (↥K ⧸ Subgroup.center ↥K))
    (hL : L = ⨆ K ∈ 𝒦, K) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 27)
    (hEL : E ≤ Subgroup.normalizer (L : Set Q)) {r : Q}
    (hr : ∀ e ∈ E, e ≠ 1 → r ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set Q))) :
    L ≤ Subgroup.centralizer ({r} : Set Q) := by
  have hL23 := i23 Q L E 𝒦 h𝒦 hL hE hEc hEL
  have hsn : IsSubnormal L ⊤ := by
    rw [hL]; exact isSubnormal_iSup_components 𝒦 (fun K hK => (h𝒦 K hK).1)
  have hE3 : IsPGroup 3 E := GL83.isPGroup_of_isElemAbelian hE
  calc L = _ := hL23
    _ ≤ _ := by
      refine iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_
      have hsnC : IsSubnormal (L ⊓ Subgroup.centralizer ({e} : Set Q))
          (Subgroup.centralizer ({e} : Set Q)) := by
        have := isSubnormal_inf hsn (Subgroup.centralizer ({e} : Set Q))
        rwa [top_inf_eq] at this
      exact layer_le_centralizer_of_mem_oPrimeP i14 hQ hcore
        (hE3.to_le (Subgroup.zpowers_le.2 he)) he1 hsnC (hr e he he1)

end Heart

section PartII

variable {G : Type} [Group G] [Finite G]

theorem part_ii_elt (iUps : InputUpsilonType) (i23 : Input23_26) (i14 : Input14_5Three)
    {m : ℕ} (hS : GLStanding G m 3) (hC4 : GLCaseFour G 3)
    {B : Subgroup G} (hB0 : IsBZeroMax 3 B) {A : Subgroup G} (hA : IsEkIn 3 3 B A)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) {g : G} (hg : g ∈ B)
    (hcore : ∀ a ∈ A, a ≠ 1 → g ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G))) :
    ∀ u ∈ upsilonOf B x, u * g * u⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 (upsilonOf B x) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hBe : IsElemAbelian 3 B := hB0.1.1
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hS hx1
  have hBC : B ≤ C := le_centralizer_of_mem hBe hx
  have hAB : A ≤ B := hA.1
  have hAC : A ≤ C := hAB.trans hBC
  have hQcore : GLAPPrimeCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp3
  have hQK : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore 3 ↥C) :=
    isKGroup_quotient' (isKGroup_of_isKProper hS.kProper hCtop) _
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB0
  have hSC : IsSCp 3 ⊤ B := lemma23_proved G m 3 hS B hB1
  set U : Subgroup G := upsilonOf B x with hU
  set S : Set (Subgroup G) := {I | IsUpsilonComponent B x I} with hSdef
  have hSC' : ∀ I ∈ S, I ≤ C := fun I hI => hI.1.1
  have hUC : U ≤ C := sSup_le hSC'
  have hgC : g ∈ C := hBC hg
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAB.trans (normalizer_upsilonOf hBe hx)
  have hgN : g ∈ Subgroup.normalizer (U : Set G) := normalizer_upsilonOf hBe hx hg
  set 𝒦 : Set (Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)) := (fun I => barX 3 C I) '' S with h𝒦def
  have hL : barX 3 C U = ⨆ K ∈ 𝒦, K := by
    rw [hU, upsilonOf, barX_sSup 3 hSC', h𝒦def, iSup_image]
  have h𝒦 : ∀ K ∈ 𝒦, IsComponentOf K ⊤ ∧
      IsLThreeEpsOrON (↥K ⧸ Subgroup.center ↥K) := by
    rintro _ ⟨I, hI, rfl⟩
    exact ⟨hI.1.2.2.1, isLThreeEpsOrON_barX hI.1
      (iUps G m hS hC4 B hB0.1 hSC x hx hx1 I hI)⟩
  have hA3 : IsPGroup 3 A := GL83.isPGroup_of_isElemAbelian hA.2.1
  have hEc : Nat.card (barX 3 C A) = 27 := by
    rw [card_barX_of_isPGroup' hp3 hA3 hAC, hA.2.2]; norm_num
  have hEL : barX 3 C A ≤ Subgroup.normalizer (barX 3 C U : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    barX_le_normalizer hAN
  set r : ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨g, hgC⟩ with hr
  have hrE : ∀ e ∈ barX 3 C A, e ≠ 1 →
      r ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))) := by
    intro e he he1
    obtain ⟨a', ha', rfl⟩ := he
    have haA : (a' : G) ∈ A := (Subgroup.mem_subgroupOf).1 ha'
    have haC : (a' : G) ∈ C := a'.2
    have ha1 : (a' : G) ≠ 1 := by
      intro h
      apply he1
      have : a' = 1 := Subtype.ext h
      rw [this, map_one]
    have hcomm : ∀ y ∈ B, y * (a' : G) = (a' : G) * y := fun y hy =>
      elemAbelian_comm hBe hy (hAB haA)
    set H : Subgroup G := C ⊓ Subgroup.centralizer ({(a' : G)} : Set G) with hH
    have hgH : g ∈ H := ⟨hgC, Subgroup.mem_centralizer_singleton_iff.2 (hcomm g hg)⟩
    have h1 : g ∈ oPrimePOf 3 H :=
      oPrimePOf_inf_le hp3 (inf_le_right : H ≤ Subgroup.centralizer ({(a' : G)} : Set G))
        ⟨hcore _ haA ha1, hgH⟩
    have h2 := mk_mem_oPrimePOf_barX hp3 (inf_le_left : H ≤ C) h1
    have h3 : barX 3 C H = Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) a'} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
      have := barX_inf_centralizer hp3 (M := C) (L := C) (d := (a' : G)) haC le_rfl
        (Subgroup.le_normalizer haC) ((hA3.to_le (Subgroup.zpowers_le.2 haA)))
      rw [barX_self, top_inf_eq] at this
      exact this
    rw [← h3]
    exact h2
  have hheart : barX 3 C U ≤ Subgroup.centralizer ({r} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    heart i23 i14 hQK hQcore h𝒦 hL (isElemAbelian_barX hA.2.1) hEc hEL hrE
  intro u hu
  have huC : u ∈ C := hUC hu
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨u, huC⟩ ∈ barX 3 C U :=
    ⟨⟨u, huC⟩, (Subgroup.mem_subgroupOf).2 hu, rfl⟩
  have hcm := Subgroup.mem_centralizer_singleton_iff.1 (hheart hmem)
  have hcore1 : u * g * u⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 C := by
    have h1 : (⟨u, huC⟩ : ↥C) * ⟨g, hgC⟩ * (⟨u, huC⟩ : ↥C)⁻¹ * (⟨g, hgC⟩ : ↥C)⁻¹ ∈
        GLAPPrimeCore 3 ↥C := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)
        ((⟨u, huC⟩ : ↥C) * ⟨g, hgC⟩ * (⟨u, huC⟩ : ↥C)⁻¹ * (⟨g, hgC⟩ : ↥C)⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hcm]
      simp only [mul_assoc, mul_inv_cancel_left]
      exact mul_inv_cancel _
    exact ⟨_, h1, rfl⟩
  have hUmem : u * g * u⁻¹ * g⁻¹ ∈ U := by
    have h1 : g * u⁻¹ * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hgN u⁻¹).1 (U.inv_mem hu)
    have := U.mul_mem hu h1
    simpa [mul_assoc] using this
  exact inf_gLAPPrimeCoreOf_le hp3 hUC ⟨hUmem, hcore1⟩

theorem part_ii (iUps : InputUpsilonType) (i23 : Input23_26) (i14 : Input14_5Three)
    {m : ℕ} (hS : GLStanding G m 3) (hC4 : GLCaseFour G 3)
    {B : Subgroup G} (hB0 : IsBZeroMax 3 B) {A : Subgroup G} (hA : IsEkIn 3 3 B A)
    {b : G} (hb : b ∈ B)
    (hcore : ∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)))
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) :
    ⁅upsilonOf B x, Subgroup.zpowers b⁆ ≤ GLAPPrimeCoreOf 3 (upsilonOf B x) := by
  refine Subgroup.commutator_le.2 fun u hu g hg => ?_
  rw [commutatorElement_def]
  exact part_ii_elt iUps i23 i14 hS hC4 hB0 hA hx hx1 (Subgroup.zpowers_le.2 hb hg)
    (fun a ha ha1 => Subgroup.zpowers_le.2 (hcore a ha ha1) hg) u hu

end PartII

end Lemma55Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem lemma55_of_inputs (hFT : InputFeitThompson) (iFA : Lemma55Ns.InputFieldAutTwo)
    (iUps : Lemma55Ns.InputUpsilonType) (i23 : Lemma55Ns.Input23_26)
    (i14 : Lemma55Ns.Input14_5Three) : Lemma55 := by
  intro G _ _ m hS hC4 B hBe hB4 b hb hb1 A hA L hL hfield hcore
  have hrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B := by
    rw [hC4.2.1]; exact hB4
  have hAB : A ≤ B := hA.1
  have hA3 : IsPGroup 3 (A ⊔ Subgroup.zpowers b : Subgroup G) :=
    (GL83.isPGroup_of_isElemAbelian hBe).to_le (sup_le hAB (Subgroup.zpowers_le.2 hb))
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hBe (hAB ha) hb)
  have hT := Lemma55Ns.exists_twoGroup_of_field hFT iFA hL hA3 hAC hfield
  have hB0 := Lemma55Ns.isBZeroMax_of_twoGroup hS hBe hrank hb hb1 hA hT hcore
  exact ⟨hB0, fun x hx hx1 =>
    Lemma55Ns.part_ii iUps i23 i14 hS hC4 hB0 hA hb hcore hx hx1⟩

end CFSG.HardMathSupport.Solomon.LocalBalance

