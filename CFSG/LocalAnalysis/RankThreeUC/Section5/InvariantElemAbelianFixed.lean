module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace
import CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane
import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commSpace_eq_top_of_normal {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (hfaith : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    {N : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥) :
    BinaryRepresentations.commSpace ρ N = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := BinaryRepresentations.commSpace ρ N
      apply_mem_toSubmodule := by
        intro g v hv
        induction hv using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨x, hx, u, rfl⟩ := hw
          have h1 : ρ (g * x * g⁻¹) (ρ g u) = ρ g (ρ x u) := by
            rw [← BinaryRepresentations.rho_mul_apply, ← BinaryRepresentations.rho_mul_apply]
            congr 1
            group
          rw [map_sub, ← h1]
          exact Submodule.subset_span ⟨g * x * g⁻¹, hN.conj_mem x hx g, ρ g u, rfl⟩
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha }
  rcases hirr.eq_bot_or_eq_top S with h | h
  · have hbot : BinaryRepresentations.commSpace ρ N = ⊥ := congrArg Subrepresentation.toSubmodule h
    refine absurd (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hfaith ?_)) hN1
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have hv : ρ x v - v ∈ BinaryRepresentations.commSpace ρ N := Submodule.subset_span ⟨x, hx, v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
    simpa using hv
  · exact congrArg Subrepresentation.toSubmodule h

open Classical in
theorem isInternal_fixedSubmodule {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {Z : Subgroup G}
    (hZ : CFSG.Open.IsElemAbelian p Z) (hcomm : BinaryRepresentations.commSpace ρ Z = ⊤) :
    DirectSum.IsInternal (fun E : ↥(Delta p Z ρ) => fixedSubmodule ρ (E : Subgroup G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : ∀ D : Subgroup G, fixedSubmodule ρ D = BinaryRepresentations.fixedSpace ρ D := fun D => rfl
  obtain ⟨hind, hsup⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    (BinaryRepresentations.coprime_hyperplane_decomposition hp2 ρ Z hZ hcomm)
  simp only [hfix]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · have hmem : ∀ D : ↥(Delta p Z ρ), (D : Subgroup G) ∈ BinaryRepresentations.hyperplanes p Z := fun D => by
      obtain ⟨h1, h2, _⟩ := (mem_Delta_iff p Z ρ D.1).1 D.2
      exact ⟨h1, h2⟩
    exact hind.comp (f := fun D : ↥(Delta p Z ρ) => (⟨(D : Subgroup G), hmem D⟩ :
      ↥(BinaryRepresentations.hyperplanes p Z)))
      (fun D₁ D₂ h => Subtype.ext (by simpa using congrArg Subtype.val h))
  · rw [eq_top_iff, ← hsup]
    refine iSup_le fun D => ?_
    obtain ⟨h1, h2⟩ := D.2
    by_cases h : BinaryRepresentations.fixedSpace ρ D.1 = ⊥
    · rw [h]; exact bot_le
    · exact le_iSup_of_le (⟨D.1, (mem_Delta_iff p Z ρ D.1).2 ⟨h1, h2, h⟩⟩ : ↥(Delta p Z ρ)) le_rfl

theorem orbit_stable {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Z : Subgroup G} (hZn : Z.Normal)
    (hU : iSupIndep (fun E : ↥(Delta p Z ρ) => fixedSubmodule ρ (E : Subgroup G)))
    {E : Subgroup G} (hE : E ∈ Delta p Z ρ) :
    ∀ b ∈ B, ∀ s ∈ twoCoreCommutator T B, ∃ t ∈ twoCoreCommutator T B,
      (E.map (MulAut.conj s).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        E.map (MulAut.conj t).toMonoidHom := by
  classical
  letI : MulAction G (Delta p Z ρ) := MulAction.compHom _ (DeltaConjugationAction.act (p := p) hZn ρ)
  have hperm : ∀ (g : G) (i : Delta p Z ρ),
      (fixedSubmodule ρ i.1).map (ρ g) = fixedSubmodule ρ (g • i).1 :=
    fun g i => DeltaConjugationAction.fixed_map hZn ρ g i
  set S : Subgroup G := twoCoreCommutator T B with hSdef
  have hS2 : IsPGroup 2 S := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact hK.to_le (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  let i : Delta p Z ρ := ⟨E, hE⟩
  let Wsp : Submodule (ZMod 2) V := ⨆ s : S, fixedSubmodule ρ (s.val • i).1
  let ρS : Representation (ZMod 2) S V := ρ.comp S.subtype
  have hWinv : ∀ g : S, Wsp ≤ Wsp.comap (ρS g) := by
    intro g
    refine iSup_le fun s => ?_
    intro v hv
    have hv' : ρ g.val v ∈ (fixedSubmodule ρ (s.val • i).1).map (ρ g.val) :=
      Submodule.mem_map_of_mem hv
    rw [hperm] at hv'
    have : (g.val • (s.val • i)) = (g * s).val • i := by
      rw [← mul_smul]; rfl
    rw [this] at hv'
    exact Submodule.mem_iSup_of_mem (g * s) hv'
  have hWne : Wsp ≠ ⊥ := by
    intro h
    have h1 : fixedSubmodule ρ (((1 : S).val • i : Delta p Z ρ)).1 ≤ Wsp :=
      le_iSup (fun s : S => fixedSubmodule ρ (s.val • i).1) 1
    rw [h] at h1
    have : fixedSubmodule ρ E = ⊥ := by
      rw [eq_bot_iff]
      simpa using h1
    exact hE.2.2 this
  obtain ⟨w, hwW, hw0, hwfix⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors.exists_fixed (H := S) hS2 ρS Wsp hWinv hWne
  have hB : ∀ b : B, ρ b.val w = w := by
    intro b
    have hwS : w ∈ fixedSubmodule ρ ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), B⁆ := by
      rw [fixedSubmodule, Representation.mem_invariants]
      intro x
      exact hwfix ⟨x.1, x.2⟩
    have hchar : ∀ φ : ↥B ≃* ↥B,
        Subgroup.map φ.toMonoidHom (B.subgroupOf B) = B.subgroupOf B := by
      intro φ
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 φ.surjective
    exact (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants
      hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction B le_rfl hchar).1 b.val b.2 w hwS
  have key := CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitFixedVectorOrbitStable.orbit_stable
    (fun D : Delta p Z ρ => fixedSubmodule ρ D.1) hU ρ hperm S B i w hw0 hwW
    (fun s => hwfix s) hB
  intro b hb s hs
  obtain ⟨t, ht⟩ := key ⟨b, hb⟩ ⟨s, hs⟩
  exact ⟨t.val, t.2, congrArg Subtype.val ht⟩

theorem exists_fixed_member {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Z : Subgroup G} (hZn : Z.Normal)
    (hU : iSupIndep (fun E : ↥(Delta p Z ρ) => fixedSubmodule ρ (E : Subgroup G)))
    {E : Subgroup G} (hE : E ∈ Delta p Z ρ) :
    ∃ s ∈ twoCoreCommutator T B, ∀ b ∈ B,
      b ∈ Subgroup.normalizer ((E.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  classical
  letI : MulAction G (Delta p Z ρ) :=
    MulAction.compHom _ (DeltaConjugationAction.act (p := p) hZn ρ)
  have hsmul : ∀ (g : G) (i : Delta p Z ρ), ((g • i : Delta p Z ρ) : Subgroup G) =
      i.1.map (MulAut.conj g).toMonoidHom := fun g i => rfl
  have hstable := orbit_stable hc hZn hU hE
  set S : Subgroup G := twoCoreCommutator T B with hSdef
  have hS2 : IsPGroup 2 S := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact hK.to_le (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  have hBnorm : B ≤ Subgroup.normalizer (S : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (CoprimeStarSubgroupStructure.Xs_generated hc.oddPrimeClassTwoAction).le
  let i : Delta p Z ρ := ⟨E, hE⟩
  have hB : ∀ b ∈ B, ∀ s ∈ S, ∃ t ∈ S, b • (s • i) = t • i := by
    intro b hb s hs
    obtain ⟨t, ht, h⟩ := hstable b hb s hs
    exact ⟨t, ht, Subtype.ext (by rw [hsmul, hsmul, hsmul]; exact h)⟩
  set H : Subgroup G := B ⊔ S with hH
  let O : Set (Delta p Z ρ) := {x | ∃ s ∈ S, x = s • i}
  have hOB : ∀ b ∈ B, b • O = O := by
    intro b hb
    have hsub : b • O ⊆ O := by
      rintro _ ⟨x, ⟨s, hs, rfl⟩, rfl⟩
      obtain ⟨t, ht, e⟩ := hB b hb s hs
      exact ⟨t, ht, e⟩
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective b)]
  have hOS : ∀ s ∈ S, s • O = O := by
    intro s hs
    ext x
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨s * t, S.mul_mem hs ht, by rw [mul_smul]⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(s⁻¹ * t) • i, ⟨s⁻¹ * t, S.mul_mem (S.inv_mem hs) ht, rfl⟩, ?_⟩
      show s • ((s⁻¹ * t) • i) = _
      rw [← mul_smul]; simp
  have hHle : H ≤ MulAction.stabilizer G O := by
    refine sup_le (fun b hb => ?_) (fun s hs => ?_)
    · exact hOB b hb
    · exact hOS s hs
  let X : SubMulAction H (Delta p Z ρ) :=
    { carrier := O
      smul_mem' := by
        intro h x hx
        have h2 : (h : G) • O = O := hHle h.2
        rw [← h2]
        exact Set.smul_mem_smul_set hx }
  haveI : Nonempty X := ⟨⟨i, 1, S.one_mem, by simp⟩⟩
  haveI hN : (S.subgroupOf H).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBnorm
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS2.comap_subtype
  have hB' : Odd (Nat.card (B.subgroupOf H)) := by
    have : Nat.card (B.subgroupOf H) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [this]; exact hc.oddPrimeClassTwoAction.setting.oddOrder
  have hSB : S.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_right,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left, Subgroup.map_top, Subgroup.range_subtype,
      sup_comm]
  have htrans : ∀ x y : X, ∃ s : S.subgroupOf H, (s.val : H) • x = y := by
    have key : ∀ x : X, ∃ s ∈ S, x.1 = s • i := fun x => x.2
    intro x y
    obtain ⟨s1, hs1, hx⟩ := key x
    obtain ⟨s2, hs2, hy⟩ := key y
    refine ⟨⟨⟨s2 * s1⁻¹, le_sup_right (b := S) |> fun h => h (S.mul_mem hs2 (S.inv_mem hs1))⟩,
      S.mul_mem hs2 (S.inv_mem hs1)⟩, ?_⟩
    apply Subtype.ext
    show (s2 * s1⁻¹) • x.1 = y.1
    rw [hx, hy, ← mul_smul]; simp
  obtain ⟨x, hx⟩ := CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints.exists_fixed
    (S.subgroupOf H) (B.subgroupOf H) hS' hB' hSB X htrans
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ S, x.1 = s • i := x.2
  refine ⟨s, hs, fun b hb => ?_⟩
  have hbx := hx ⟨⟨b, le_sup_left (b := S) hb⟩, hb⟩
  have h1 : (b • x.1 : Delta p Z ρ) = x.1 := congrArg Subtype.val hbx
  rw [hxs] at h1
  have h2 := congrArg Subtype.val h1
  rw [hsmul, hsmul] at h2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact h2

theorem inf_mem_Delta {p : ℕ} (hp : p.Prime) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {P Z : Subgroup G} (hPp : IsPGroup p P) (hPZ : P ≤ Z)
    (hP0 : fixedSubmodule ρ P = ⊥) {E : Subgroup G} (hE : E ∈ Delta p Z ρ) :
    E ⊓ P ∈ Delta p P ρ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hidx, hne⟩ := (mem_Delta_iff p Z ρ E).1 hE
  have hanti : ∀ {D D' : Subgroup G}, D ≤ D' → fixedSubmodule ρ D' ≤ fixedSubmodule ρ D :=
    fun {D D'} h v hv => (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ D v).2 fun n hn =>
      (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ D' v).1 hv n (h hn)
  have hPE : ¬ P ≤ E := fun h => hne (eq_bot_iff.2 ((hanti h).trans hP0.le))
  refine (mem_Delta_iff p P ρ _).2 ⟨inf_le_right, ?_, fun h => hne (eq_bot_iff.2 ((hanti inf_le_left).trans h.le))⟩
  rw [Subgroup.inf_relIndex_right]
  have hle : E.relIndex P ≤ p := hidx ▸ Subgroup.relIndex_le_of_le_right hPZ (by rw [hidx]; exact hp.ne_zero)
  have hne1 : E.relIndex P ≠ 1 := fun h => hPE (Subgroup.relIndex_eq_one.1 h)
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (hn ▸ Subgroup.relIndex_dvd_card E P)
  rw [hk] at hle hne1 ⊢
  have hk0 : k ≠ 0 := by rintro rfl; exact hne1 (pow_zero p)
  have hk1 : k ≤ 1 := by
    by_contra h
    have := Nat.pow_lt_pow_right hp.one_lt (show 1 < k by omega)
    rw [pow_one] at this
    omega
  rw [show k = 1 by omega, pow_one]

theorem commutator_le {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Z : Subgroup G}
    (hZ : CFSG.Open.IsElemAbelian p Z) (hPZ : P ≤ Z) (hP0 : fixedSubmodule ρ P = ⊥)
    {E : Subgroup G} (hE : E ∈ Delta p Z ρ) (hBE : B ≤ Subgroup.normalizer (E : Set G)) :
    ⁅B, Z⁆ ≤ E := by
  have hS := hc.oddPrimeClassTwoAction.setting
  have hp := hS.prime
  obtain ⟨hEZ, hidx, hne⟩ := (mem_Delta_iff p Z ρ E).1 hE
  have hcommZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZ.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPnE : P ≤ Subgroup.normalizer (E : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun y hy => hcommZ y (hEZ hy) x (hPZ hx))
  have hEnP : E ≤ Subgroup.normalizer (P : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun y hy => hcommZ y (hPZ hy) x (hEZ hx))
  have hEP := inf_mem_Delta hp hS.pGroup hPZ hP0 hE
  have hBEP : B ≤ Subgroup.normalizer ((E ⊓ P : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.1 (hBE hb) h,
      ← Subgroup.mem_normalizer_iff.1 (hS.normB hb) h]
  have hcan : E ⊓ P = ⁅B, P⁆ := (CanonicalBFixedHyperplane.canonical hc).2.2 _ hEP hBEP
  have hPE : ¬ P ≤ E := by
    intro h
    have hle : fixedSubmodule ρ E ≤ fixedSubmodule ρ P := fun v hv =>
      (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ P v).2 fun n hn =>
        (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ E v).1 hv n (h hn)
    exact hne (eq_bot_iff.2 (hle.trans hP0.le))
  have hZle : Z ≤ P ⊔ E := by
    have h1 := Subgroup.relIndex_mul_relIndex E (P ⊔ E) Z le_sup_right (sup_le hPZ hEZ)
    rw [hidx] at h1
    have hdvd : (P ⊔ E).relIndex Z ∣ p := ⟨_, by rw [← h1]; ring⟩
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact Subgroup.relIndex_eq_one.1 h
    · exfalso
      rw [h] at h1
      have h2 : E.relIndex (P ⊔ E) = 1 := by
        have := hp.pos
        nlinarith
      exact hPE (le_sup_left.trans (Subgroup.relIndex_eq_one.1 h2))
  rw [Subgroup.commutator_le]
  intro b hb z hz
  have hz' : z ∈ ((P ⊔ E : Subgroup G) : Set G) := hZle hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P E hEnP] at hz'
  obtain ⟨x, hx, y, hy, rfl⟩ := hz'
  have hc1 : b * x * b⁻¹ * x⁻¹ ∈ E := by
    have : b * x * b⁻¹ * x⁻¹ ∈ ⁅B, P⁆ := Subgroup.commutator_mem_commutator hb hx
    rw [← hcan] at this
    exact this.1
  have hc2 : b * y * b⁻¹ * y⁻¹ ∈ E :=
    E.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBE hb) y).1 hy) (E.inv_mem hy)
  have hc3 : x * (b * y * b⁻¹ * y⁻¹) * x⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.1 (hPnE hx) _).1 hc2
  have := E.mul_mem hc1 hc3
  rw [commutatorElement_def]
  convert this using 1
  group

theorem le_normalizer_of_forall_conj_mem {K W : Subgroup G}
    (h : ∀ g ∈ K, ∀ w ∈ W, g * w * g⁻¹ ∈ W) : K ≤ Subgroup.normalizer (W : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h g hg w, fun hw => ?_⟩
  have := h g⁻¹ (K.inv_mem hg) _ hw
  simpa [mul_assoc] using this

theorem exists_complement {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Z : Subgroup G} (hZn : Z.Normal)
    (hZ : CFSG.Open.IsElemAbelian p Z) (hPZ : P ≤ Z) :
    ∃ W : Subgroup G, W ≤ Z ∧ P ⊓ W = ⊥ ∧ Z ≤ P ⊔ W ∧
      twoCoreCommutator T B ≤ Subgroup.normalizer (W : Set G) ∧
      B ≤ Subgroup.normalizer (W : Set G) := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hp2 : p ≠ 2 := by
    intro h
    have hodd := hS.odd
    rw [h] at hodd
    exact absurd hodd (by decide)
  set S : Subgroup G := twoCoreCommutator T B with hSdef
  have hS2 : IsPGroup 2 S := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact hK.to_le (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (CoprimeStarSubgroupStructure.Xs_generated hc.oddPrimeClassTwoAction).le
  set H : Subgroup G := S ⊔ B with hH
  haveI : Z.Normal := hZn
  haveI : IsElementaryAbelian p ↥Z :=
    { toIsMulCommutative := hZ.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hZ.2 x x.2) }
  letI : MulDistribMulAction ↥H ↥Z :=
    MulDistribMulAction.compHom ↥Z ((MulAut.conjNormal : G →* MulAut ↥Z).comp H.subtype)
  have hsmul : ∀ (a : ↥H) (z : ↥Z), ((a • z : ↥Z) : G) = (a : G) * z * (a : G)⁻¹ := fun a z =>
    MulAut.conjNormal_apply (a : G) z
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hcop : ¬ p ∣ Fintype.card ↥H := by
    rw [Fintype.card_eq_nat_card]
    intro hdvd
    have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
      S B hBS
    rcases (Nat.Prime.dvd_mul hS.prime).1 (hdvd.trans h1) with h | h
    · obtain ⟨k, hk⟩ := hS2.exists_card_eq
      rw [hk] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hS.prime Nat.prime_two).1 (hS.prime.dvd_of_dvd_pow h))
    · exact (three_lt_pRank_and_prime_not_dvd_card_actor hc).2 ⟨hS.prime, h⟩
  obtain ⟨W', hW'c, hW'inv⟩ := CFSG.RankThree.Coprime.exists_isCompl_invariant_subgroup_of_coprime
    hcop (P.subgroupOf Z) (fun a z hz => by
      rw [Subgroup.mem_subgroupOf, hsmul]
      exact hc.faithfulBinaryIrreducibleAction.normal.conj_mem _ hz _)
  have hinv : ∀ g ∈ H, ∀ w ∈ W'.map Z.subtype, g * w * g⁻¹ ∈ W'.map Z.subtype := by
    rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨(⟨g, hg⟩ : ↥H) • w, hW'inv _ _ hw, hsmul _ _⟩
  refine ⟨W'.map Z.subtype, Subgroup.map_subtype_le _, ?_, ?_,
    le_normalizer_of_forall_conj_mem fun g hg => hinv g (Subgroup.mem_sup_left hg),
    le_normalizer_of_forall_conj_mem fun g hg => hinv g (Subgroup.mem_sup_right hg)⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxP, ⟨w, hw, rfl⟩⟩
    have : w ∈ P.subgroupOf Z ⊓ W' := ⟨Subgroup.mem_subgroupOf.2 hxP, hw⟩
    rw [hW'c.inf_eq_bot, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  · intro z hz
    have h1 : (⟨z, hz⟩ : ↥Z) ∈ P.subgroupOf Z ⊔ W' := by rw [hW'c.sup_eq_top]; trivial
    have h2 := Subgroup.mem_map_of_mem Z.subtype h1
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPZ] at h2

theorem inf_centralizer_eq {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Z : Subgroup G} (hPZ : P ≤ Z)
    (hZexp : ∀ x ∈ Z, x ^ p = 1) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hcyc : IsCyclic ↥(Z ⊓ Subgroup.centralizer ({b} : Set G))) :
    P ⊓ Subgroup.centralizer ({b} : Set G) = Z ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hS := hc.oddPrimeClassTwoAction.setting
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hcan := CanonicalBFixedHyperplane.canonical hc
  have hQ0 : P ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
    rw [hcan.2.1.2 b hb hb1]; exact hcan.2.1.1
  refine Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hPZ) ?_
  have hle : Nat.card ↥(Z ⊓ Subgroup.centralizer ({b} : Set G)) ≤ p := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd hS.prime.pos (orderOf_dvd_of_pow_eq_one ?_)
    exact Subtype.ext (hZexp g.1 (Subgroup.mem_inf.1 g.2).1)
  obtain ⟨k, hk⟩ := (hS.pGroup.to_le
    (inf_le_left : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ P)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hQ0 hk
  calc Nat.card ↥(Z ⊓ Subgroup.centralizer ({b} : Set G)) ≤ p := hle
    _ ≤ p ^ k := Nat.le_self_pow hk0 p
    _ = _ := hk.symm

theorem fixedSubmodule_eq_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) : fixedSubmodule ρ P = ⊥ := by
  have hS := hc.oddPrimeClassTwoAction.setting
  haveI : Fact p.Prime := ⟨hS.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by
    intro h
    have hodd := hS.odd
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hcan := CanonicalBFixedHyperplane.canonical hc
  have hP1 : P ≠ ⊥ := fun h => hcan.2.1.1 (by rw [h, bot_inf_eq])
  exact BinaryRepresentations.fixedSpace_eq_bot_of_hyp hp2 ρ P
    (isElemAbelian_of_binary_rank_counterexample hc)
    (commSpace_eq_top_of_normal hc.faithfulBinaryIrreducibleAction.faithful
      hc.faithfulBinaryIrreducibleAction.irreducible hc.faithfulBinaryIrreducibleAction.normal hP1)

theorem eq_of_normal_of_le {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Z : Subgroup G} (hZn : Z.Normal)
    (hZ : CFSG.Open.IsElemAbelian p Z) (hPZ : P ≤ Z)
    (hZcyc : ∀ b ∈ B, b ≠ 1 → IsCyclic ↥(Z ⊓ Subgroup.centralizer ({b} : Set G))) : Z = P := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  haveI : Fact p.Prime := ⟨hS.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by
    intro h
    have hodd := hS.odd
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hfaith := hc.faithfulBinaryIrreducibleAction.faithful
  have hirr := hc.faithfulBinaryIrreducibleAction.irreducible
  have hcan := CanonicalBFixedHyperplane.canonical hc
  have hP1 : P ≠ ⊥ := fun h => hcan.2.1.1 (by rw [h, bot_inf_eq])
  have hZ1 : Z ≠ ⊥ := fun h => hP1 (eq_bot_iff.2 (h ▸ hPZ))
  have hP0 : fixedSubmodule ρ P = ⊥ := fixedSubmodule_eq_bot hc
  have hint := isInternal_fixedSubmodule hp2 ρ hZ (commSpace_eq_top_of_normal hfaith hirr hZn hZ1)
  have hcommZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZ.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcop : (Nat.card B).Coprime p := by
    have h19 := (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
    by_contra h
    apply h19
    refine ⟨hS.prime, ?_⟩
    by_contra hd
    exact h ((Nat.Prime.coprime_iff_not_dvd hS.prime).2 hd).symm
  obtain ⟨W, hWZ, hPW, hZPW, hSW, hBW⟩ := exists_complement hc hZn hZ hPZ
  obtain ⟨b0, hb0, hb01⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.oddPrimeClassTwoAction.actor_ne_bot
    exact ⟨b, b.2, fun h => hb (Subtype.ext h)⟩
  have hCZ := inf_centralizer_eq hc hPZ hZ.2 hb0 hb01 (hZcyc b0 hb0 hb01)
  have hCW : Z ⊓ Subgroup.centralizer (B : Set G) ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨hwZ, hwB⟩, hwW⟩
    have hw0 : w ∈ Z ⊓ Subgroup.centralizer ({b0} : Set G) :=
      ⟨hwZ, Subgroup.centralizer_le (by simpa using hb0) hwB⟩
    rw [← hCZ] at hw0
    have : w ∈ P ⊓ W := ⟨hw0.1, hwW⟩
    rwa [hPW] at this
  have hWBZ : W ≤ ⁅B, Z⁆ :=
    CanonicalBFixedHyperplane.le_commutator hS.prime hcommZ hZ.2 hcop
      (fun b _ => by rw [Subgroup.normalizer_eq_top_iff.2 hZn]; trivial) hWZ hBW hCW
  have hWE : ∀ E ∈ Delta p Z ρ, W ≤ E := by
    intro E hE
    obtain ⟨s, hs, hsB⟩ := exists_fixed_member hc hZn hint.submodule_iSupIndep hE
    have hE' := DeltaConjugationAction.map_mem (p := p) hZn ρ s hE
    have h1 : W ≤ E.map (MulAut.conj s).toMonoidHom :=
      hWBZ.trans (commutator_le hc hZ hPZ hP0 hE' hsB)
    intro w hw
    obtain ⟨y, hy, hyw⟩ := h1 ((Subgroup.mem_normalizer_iff.1 (hSW hs) w).1 hw)
    have : y = w := by
      have h2 : s * y * s⁻¹ = s * w * s⁻¹ := hyw
      simpa using h2
    exact this ▸ hy
  have hWtriv : ∀ w ∈ W, ρ w = 1 := by
    intro w hw
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ ⨆ E : ↥(Delta p Z ρ), fixedSubmodule ρ (E : Subgroup G) := by
      rw [hint.submodule_iSup_eq_top]; trivial
    rw [Module.End.one_apply]
    refine Submodule.iSup_induction _ (motive := fun v => ρ w v = v) hv ?_ ?_ ?_
    · intro E u hu
      exact (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ _ u).1 hu w (hWE E.1 E.2 hw)
    · simp
    · intro a b ha hb
      rw [map_add, ha, hb]
  have hW1 : W = ⊥ :=
    eq_bot_iff.2 fun w hw => Subgroup.mem_bot.2 (hfaith (by rw [map_one]; exact hWtriv w hw))
  refine le_antisymm (fun z hz => ?_) hPZ
  have := hZPW hz
  rwa [hW1, sup_bot_eq] at this

end CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed
