module

public import CFSG.LieType.SemisimpleCentralizers.PComponentProduct
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.SemisimpleCentralizers
  CFSG.LieType.SemisimpleCentralizers.Held Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem sq_ne_two_three (t : ℕ) : t ^ 2 ≠ 2 ∧ t ^ 2 ≠ 3 := by
  constructor
  · intro h
    have : t ≤ 2 := by nlinarith
    interval_cases t <;> norm_num at h
  · intro h
    have : t ≤ 2 := by nlinarith
    interval_cases t <;> norm_num at h

theorem statedSU_qs_or_solv {a Q : ℕ} {M : Type} [Field M] [Finite M] (hK : Nat.card M = Q ^ 2) :
    Group.IsSolvable ↥(StatedSU a Q M) ∨ CFSG.Open.IsQuasisimple ↥(StatedSU a Q M) := by
  obtain ⟨p, hchar, k, hp, rfl⟩ := hct_exists_char_pow hK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hchar
  rcases Nat.lt_or_ge a 2 with ha | ha
  · left
    haveI : Subsingleton ↥(StatedSU a (p ^ k) M) := by
      haveI := hct_subsingleton_statedSL_of_le_one (K := M) (d := a) (by omega)
      refine ⟨fun x y => ?_⟩
      have h := Subsingleton.elim (α := ↥(StatedSL a M))
        ⟨x.1, statedSU_le_statedSL a (p ^ k) M x.2⟩ ⟨y.1, statedSU_le_statedSL a (p ^ k) M y.2⟩
      exact Subtype.ext (Subtype.mk.inj h)
    infer_instance
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  ·
    have ha2 : a = 2 := by omega
    subst ha2
    rcases Nat.lt_or_ge (p ^ k) 4 with hsmall | hbig
    · left
      have hcard : Nat.card (StatedSU 2 (p ^ k) M) = p ^ k * ((p ^ k) ^ 2 - 1) :=
        CFSG.RankThree.SubgroupLists.card_statedSU_two (K := M) (r := p) (f := k) hK
      have hQ2 : 2 ≤ p ^ k := by
        have h1 : 1 < Nat.card M := Finite.one_lt_card
        rw [hK] at h1
        by_contra hlt
        have hle1 : p ^ k ≤ 1 := by omega
        have := Nat.pow_le_pow_left hle1 2
        rw [one_pow] at this
        omega
      have hQ : p ^ k = 2 ∨ p ^ k = 3 := by omega
      rcases hQ with h | h
      · have hs : Group.IsSolvable ↥(StatedSU 2 (p ^ k) M) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two
            Nat.prime_three (by norm_num) (by rw [hcard, h] <;> norm_num)
        exact hs
      · have hs : Group.IsSolvable ↥(StatedSU 2 (p ^ k) M) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two
            Nat.prime_three (by norm_num) (by rw [hcard, h] <;> norm_num)
        exact hs
    · right
      have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield M p k) = p ^ k :=
        CFSG.LieType.Steinberg.card_fixedSubfield hK
      obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := M) (r := p) (f := k) hK
      have hSL : CFSG.Open.IsQuasisimple (StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
        hct_isQuasisimple_statedSL _ (by norm_num) (Or.inr (by rw [hF]; omega))
          (Or.inr (by rw [hF]; omega))
      let e' : ↥(StatedSU 2 (p ^ k) M) ≃*
          ↥(StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield M p k)) :=
        e.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 _)
      exact CFSG.Open.IsQuasisimple.of_mulEquiv e' hSL
  · by_cases h32 : a = 3 ∧ p ^ k = 2
    ·
      left
      obtain ⟨rfl, h2⟩ := h32
      have hF : Nat.card M = (2 ^ 1) ^ 2 := by rw [hK, h2] <;> norm_num
      have hcard : Nat.card (StatedSU 3 (2 ^ 1) M) = 216 := by
        rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hF]
        norm_num
      have hcard' : Nat.card (StatedSU 3 (p ^ k) M) = 216 := by
        rw [h2]
        simpa using hcard
      have hs : Group.IsSolvable ↥(StatedSU 3 (p ^ k) M) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two
          Nat.prime_three (by norm_num) (by rw [hcard'] <;> norm_num)
      exact hs
    · right
      have hnq : (a, p ^ k) ≠ (3, 2) := fun h => h32 ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
      obtain ⟨hperf, hsimp, -⟩ :=
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := p) (f := k) hK ha3 hnq).1
      exact ⟨Group.isPerfect_def.mp hperf, hsimp⟩

theorem heldSU_qs_or_solv {a Q : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hK : Nat.card M = Q ^ 2) :
    Group.IsSolvable ↥(heldSU a M τ hτ) ∨ CFSG.Open.IsQuasisimple ↥(heldSU a M τ hτ) := by
  rw [hct_heldSU_eq_statedSU (hτ := hτ) hτQ]
  exact statedSU_qs_or_solv hK

theorem sl_block_qs_or_solv {b : ℕ} {M : Type} [Field M] [Finite M] {t : ℕ} (ht : Nat.card M = t ^ 2) :
    Group.IsSolvable ↥(StatedSL b M) ∨ CFSG.Open.IsQuasisimple ↥(StatedSL b M) := by
  rcases Nat.lt_or_ge b 2 with hb | hb
  · left
    haveI := hct_subsingleton_statedSL_of_le_one (K := M) (d := b) (by omega)
    infer_instance
  · right
    have h2 : Nat.card M ≠ 2 := by rw [ht]; exact (sq_ne_two_three t).1
    have h3 : Nat.card M ≠ 3 := by rw [ht]; exact (sq_ne_two_three t).2
    exact hct_isQuasisimple_statedSL M hb (Or.inr h2) (Or.inr h3)

theorem uni_mulSingle_inj {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] (i : ι) :
    Function.Injective (MonoidHom.mulSingle H i) := by
  intro a b hab
  have := congrFun hab i
  simpa [MonoidHom.mulSingle_apply] using this

theorem uni_mem_iSup_of_mulSingle_mem {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, Group (M i)] (S : ι → Subgroup (∀ j, M j)) (z : ∀ j, M j)
    (h : ∀ i, MonoidHom.mulSingle M i (z i) ∈ S i) : z ∈ ⨆ i, S i := by
  rw [← Finset.noncommProd_mulSingle z]
  exact Subgroup.noncommProd_mem _ _ (fun i _ => Subgroup.mem_iSup_of_mem i (h i))

theorem uni_commute_mulSingle_of_ne {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)]
    {i j : ι} (hij : i ≠ j) (u : M i) (v : M j) :
    Commute (MonoidHom.mulSingle M i u) (MonoidHom.mulSingle M j v) := by
  show MonoidHom.mulSingle M i u * MonoidHom.mulSingle M j v =
    MonoidHom.mulSingle M j v * MonoidHom.mulSingle M i u
  ext k
  by_cases hki : k = i
  · subst hki
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hki]
    · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]

theorem uni_mulSingle_conj {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)] (i : Fin r) (g : ∀ j, H j)
    (w : H i) :
    g * MonoidHom.mulSingle H i w * g⁻¹ = MonoidHom.mulSingle H i (g i * w * (g i)⁻¹) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [MonoidHom.mulSingle_apply]
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]

theorem uni_isSolvable_of_le {G : Type} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    [Group.IsSolvable ↥B] : Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

theorem uni_pcomp_core {L : Type} [Field L] [Finite L] {n r : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (H : Fin r → Type) [∀ k, Group (H k)] [∀ k, Finite (H k)]
    (θ : (∀ k, H k) →* GL (Fin n) L) (hθ : Function.Injective θ)
    (hθG : ∀ w, θ w ∈ heldGU n L τ hτ)
    (S : ∀ k, Subgroup (H k)) (hS : ∀ k (x y : H k), ⁅x, y⁆ ∈ S k) (hSn : ∀ k, (S k).Normal)
    (hqs : ∀ k, CFSG.Open.IsQuasisimple ↥(S k) ∨ Group.IsSolvable ↥(S k))
    {p : ℕ} (M : Subgroup (GL (Fin n) L))
    (hM : GLAPComponent p (((heldSU n L τ hτ).comap θ).map θ) M) :
    IsComponentOf M (((heldSU n L τ hτ).comap θ).map θ) := by
  classical
  haveI hSLn : (StatedSL n L).Normal := by
    rw [statedSL_eq_ker_det]
    infer_instance
  obtain ⟨KP, hKP⟩ : ∃ KP : Subgroup (∀ k, H k), KP = (heldSU n L τ hτ).comap θ := ⟨_, rfl⟩
  have memKP : ∀ w, w ∈ KP ↔ θ w ∈ heldSU n L τ hτ := fun w => by rw [hKP]; rfl
  haveI hKPn : KP.Normal := by
    refine ⟨fun k hk w => ?_⟩
    rw [memKP] at hk ⊢
    rw [map_mul, map_mul, map_inv]
    exact heldSU_normal_in_heldGU hτ (θ w) (hθG w) (θ k) hk
  obtain ⟨T, hT⟩ : ∃ T : Fin r → Subgroup (∀ k, H k),
      ∀ i, T i = (S i).map (MonoidHom.mulSingle H i) ⊓ KP :=
    ⟨fun i => (S i).map (MonoidHom.mulSingle H i) ⊓ KP, fun i => rfl⟩
  have hfacN : ∀ i, ((S i).map (MonoidHom.mulSingle H i)).Normal := by
    intro i
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    rw [uni_mulSingle_conj]
    exact Subgroup.mem_map.mpr ⟨_, (hSn i).conj_mem s hs (g i), rfl⟩
  haveI hTn : ∀ i, (T i).Normal := fun i => by
    rw [hT i]
    haveI := hfacN i
    infer_instance
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (∀ k, H k), Q = ⨆ i, T i := ⟨_, rfl⟩
  haveI hQn : Q.Normal := by rw [hQ]; infer_instance
  have hQKP : Q ≤ KP := by
    rw [hQ]
    exact iSup_le fun i => by rw [hT i]; exact inf_le_right
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (GL (Fin n) L), E = Q.map θ := ⟨_, rfl⟩
  obtain ⟨Lf, hL⟩ : ∃ Lf : Fin r → Subgroup (GL (Fin n) L),
      ∀ i, Lf i = (T i).map θ := ⟨fun i => (T i).map θ, fun i => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup (GL (Fin n) L), X = KP.map θ := ⟨_, rfl⟩
  rw [← hKP, ← hX] at hM ⊢
  have memX : ∀ y, y ∈ X ↔ ∃ k ∈ KP, θ k = y := by
    intro y
    rw [hX, Subgroup.mem_map]
  have hEX : E ≤ X := by
    rw [hE, hX]
    exact Subgroup.map_mono hQKP
  have hcommKP : ∀ i (x y : H i), MonoidHom.mulSingle H i ⁅x, y⁆ ∈ KP := by
    intro i x y
    rw [memKP]
    have hxy : MonoidHom.mulSingle H i ⁅x, y⁆ =
        ⁅MonoidHom.mulSingle H i x, MonoidHom.mulSingle H i y⁆ :=
      map_commutatorElement _ _ _
    rw [hxy, map_commutatorElement]
    exact commutatorElement_mem_heldSU (hθG _) (hθG _)
  have hcommQ : ∀ k l : (∀ j, H j), ⁅k, l⁆ ∈ Q := by
    intro k l
    rw [hQ]
    apply uni_mem_iSup_of_mulSingle_mem T
    intro i
    have hmul : MonoidHom.mulSingle H i (⁅k, l⁆ i) =
        ⁅MonoidHom.mulSingle H i (k i), MonoidHom.mulSingle H i (l i)⁆ := by
      rw [← map_commutatorElement]
      congr 1
    rw [hmul, hT i, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map.mpr ⟨⁅k i, l i⁆, hS i _ _, ?_⟩, ?_⟩
    · rw [map_commutatorElement]
    · rw [memKP, map_commutatorElement]
      exact commutatorElement_mem_heldSU (hθG _) (hθG _)
  have hEn : (E.subgroupOf X).Normal := by
    refine ⟨fun e he g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    obtain ⟨k, -, hkg⟩ := (memX _).mp g.2
    rw [hE] at he ⊢
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp he
    refine Subgroup.mem_map.mpr ⟨k * q * k⁻¹, hQn.conj_mem q hq k, ?_⟩
    simp [map_mul, map_inv, hkg, hqe]
  haveI hEn' : (E.subgroupOf X).Normal := hEn
  have hsolv : Group.IsSolvable (X ⧸ E.subgroupOf X) := by
    apply Group.isSolvable_of_comm
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    obtain ⟨k, -, hkx⟩ := (memX _).mp x.2
    obtain ⟨l, -, hly⟩ := (memX _).mp y.2
    have hc : ((x : GL (Fin n) L) * (y : GL (Fin n) L))⁻¹ *
        ((y : GL (Fin n) L) * (x : GL (Fin n) L)) = θ ⁅l⁻¹, k⁻¹⁆ := by
      rw [← hkx, ← hly]
      simp only [map_commutatorElement, map_inv, map_mul, commutatorElement_def]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, hE]
    exact Subgroup.mem_map.mpr ⟨_, hcommQ l⁻¹ k⁻¹, rfl⟩
  have hE_eq : E = ⨆ i, Lf i := by
    rw [hE, hQ, Subgroup.map_iSup]
    simp only [hL]
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Lf i, ∀ y ∈ Lf j, Commute x y := by
    intro i j hij x hx y hy
    rw [hL i] at hx
    rw [hL j] at hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hT i] at ha
    rw [hT j] at hb
    obtain ⟨hfa, -⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨hfb, -⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hfa
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hfb
    exact (uni_commute_mulSingle_of_ne hij u v).map θ
  have hLq : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i) ∨ Group.IsSolvable ↥(Lf i) := by
    intro i
    have eF : ↥(S i) ≃* ↥((S i).map (MonoidHom.mulSingle H i)) :=
      Subgroup.equivMapOfInjective (S i) (MonoidHom.mulSingle H i) (uni_mulSingle_inj i)
    rcases hqs i with hq | hsol
    · left
      have hle : (S i).map (MonoidHom.mulSingle H i) ≤ KP := by
        intro w hw
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hw
        have hle' : (⊤ : Subgroup ↥(S i)) ≤ (KP.comap (MonoidHom.mulSingle H i)).subgroupOf (S i) := by
          rw [← hq.1]
          refine Subgroup.commutator_le.mpr (fun x _ y _ => ?_)
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
          have e : ((⁅x, y⁆ : ↥(S i)) : H i) = ⁅(x : H i), (y : H i)⁆ := by
            simp [commutatorElement_def]
          rw [e]
          exact hcommKP i _ _
        have := Subgroup.mem_subgroupOf.mp (hle' (Subgroup.mem_top ⟨s, hs⟩))
        exact Subgroup.mem_comap.mp this
      have hTi : T i = (S i).map (MonoidHom.mulSingle H i) := by
        rw [hT i]
        exact inf_eq_left.mpr hle
      have hLi : Lf i = ((S i).map (MonoidHom.mulSingle H i)).map θ := by
        rw [hL i, hTi]
      have e2 : ↥((S i).map (MonoidHom.mulSingle H i)) ≃* ↥(Lf i) :=
        (Subgroup.equivMapOfInjective _ θ hθ).trans (MulEquiv.subgroupCongr hLi).symm
      exact CFSG.Open.IsQuasisimple.of_mulEquiv (eF.trans e2).symm hq
    · right
      haveI := hsol
      have hF : Group.IsSolvable ↥((S i).map (MonoidHom.mulSingle H i)) :=
        Group.isSolvable_of_isSolvable_injective (f := eF.symm.toMonoidHom) eF.symm.injective
      have hTle : T i ≤ (S i).map (MonoidHom.mulSingle H i) := by
        rw [hT i]
        exact inf_le_left
      have hLle : Lf i ≤ ((S i).map (MonoidHom.mulSingle H i)).map θ := by
        rw [hL i]
        exact Subgroup.map_mono hTle
      haveI hFmap : Group.IsSolvable ↥(((S i).map (MonoidHom.mulSingle H i)).map θ) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.equivMapOfInjective _ θ hθ).symm.toMonoidHom)
          (Subgroup.equivMapOfInjective _ θ hθ).symm.injective
      exact uni_isSolvable_of_le hLle
  have hLX : ∀ i, Lf i ≤ X := by
    intro i y hy
    rw [hL i] at hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hT i] at ht
    obtain ⟨-, htK⟩ := Subgroup.mem_inf.mp ht
    exact (memX _).mpr ⟨t, htK, rfl⟩
  obtain ⟨i, hMi, hqi⟩ := largeEvenPComponent_eq_of_commuting_product (p := p) Lf hEX hEn'
    hsolv hE_eq hcomm (fun j => (hLq j).elim (fun h => Or.inl h) (fun h => Or.inr h))
    ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p X M).mpr hM)
  rw [hMi]
  have hsub : CFSG.Open.IsSubnormal (Lf i) X := by
    refine CFSG.Open.IsSubnormal.step (hLX i) ?_ (CFSG.Open.IsSubnormal.refl X)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, -, hkg⟩ := (memX _).mp g.2
    rw [hL i] at hn ⊢
    obtain ⟨t, ht, htn⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨k * t * k⁻¹, (hTn i).conj_mem t ht k, ?_⟩
    simp [map_mul, map_inv, hkg, htn]
  exact ⟨hLX i, hsub, hqi⟩

theorem uniPCompIsComp_holds :
    ∀ (K : Type) [Field K] [Finite K] (Q n p : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x),
      (∀ x, τ x = x ^ Q) → Nat.card K = Q ^ 2 → p.Prime → ∀ s : GL (Fin n) K, s ∈ heldGU n K τ hτ →
        (orderOf s : K) ≠ 0 → ∀ M : Subgroup (GL (Fin n) K),
          GLAPComponent p (Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ StatedSU n Q K) M →
            IsComponentOf M (Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ StatedSU n Q K) := by
  intro K _ _ Q n p τ hτ hτQ hK _hp s hs hord M hM
  rw [← hct_heldSU_eq_statedSU (a := n) (hτ := hτ) hτQ] at hM ⊢
  obtain ⟨r, H, hgrp, hfinH, hblk, ⟨ε⟩⟩ := centralizerDecomposition_gu hτ hτQ hK s hs hord
  have hbl : ∀ k, ∃ S : Subgroup (H k), (∀ x y : H k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧ S.Normal ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
          (∀ x : M, τ x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
            Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nat.card M = Q ^ (2 * e) ∧
          Nonempty (S ≃* StatedSL b M))) :=
    fun k => exists_blockSub_sized SUComponentsTrivial_holds SLComponentsTrivial_holds (hblk k)
  choose S hS _hSt hSn hty using hbl
  have hqs : ∀ k, CFSG.Open.IsQuasisimple ↥(S k) ∨ Group.IsSolvable ↥(S k) := by
    intro k
    rcases hty k with ⟨a, d, M', hM'F, hM'fin, τ', hτ', hτ'Q, hcard', ⟨eS⟩⟩ |
      ⟨b, e, M', hM'F, hM'fin, hcard', ⟨eS⟩⟩
    · rcases heldSU_qs_or_solv (a := a) hτ' hτ'Q hcard' with hsol | hq
      · haveI := hsol
        exact Or.inr (Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective)
      · exact Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv eS hq)
    · rcases sl_block_qs_or_solv (b := b) (t := Q ^ e) (by rw [hcard', ← pow_mul, mul_comm]) with hsol | hq
      · haveI := hsol
        exact Or.inr (Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective)
      · exact Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv eS hq)
  let C : Subgroup (GL (Fin n) K) := Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ heldGU n K τ hτ
  let θ : (∀ k, H k) →* GL (Fin n) K := C.subtype.comp ε.symm.toMonoidHom
  have hθinj : Function.Injective θ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hθG : ∀ w, θ w ∈ heldGU n K τ hτ := fun w => (Subgroup.mem_inf.mp (ε.symm w).2).2
  have hrange : θ.range = C := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (ε.symm w).2
    · intro hx
      exact ⟨ε ⟨x, hx⟩, by simp [θ]⟩
  have hCeq : Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ heldSU n K τ hτ =
      ((heldSU n K τ hτ).comap θ).map θ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxr : x ∈ θ.range := by
        rw [hrange]
        exact ⟨hx1, (Subgroup.mem_inf.mp hx2).1⟩
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
      exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨?_, hw⟩
      have hc : θ w ∈ C := by
        rw [← hrange]
        exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
      exact hc.1
  rw [hCeq] at hM ⊢
  exact uni_pcomp_core hτ H θ hθinj hθG S hS hSn hqs M hM

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
