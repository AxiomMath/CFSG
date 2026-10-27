module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorus

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Small

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y}

theorem centralizer_le_sup_of_oneSmallFacts {K : Subgroup Y} [K.Normal]
    (T₁ : Sylow p K) (hF : OneSmallFacts p K T₁)
    {V : Subgroup Y} (hVT : V ≤ (T₁ : Subgroup K).map K.subtype) (hV : V ≠ ⊥)
    (hNV : K ⊓ Subgroup.normalizer (((T₁ : Subgroup K).map K.subtype : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (V : Set Y)) :
    Subgroup.centralizer (V : Set Y) ≤
        (T₁ : Subgroup K).map K.subtype ⊔ Subgroup.centralizer (K : Set Y) ∨
      (V = centerOf ((T₁ : Subgroup K).map K.subtype) ∧
        centerOf ((T₁ : Subgroup K).map K.subtype) ≠ (T₁ : Subgroup K).map K.subtype) := by
  have hVK : V ≤ K := hVT.trans (Subgroup.map_subtype_le _)
  have hVmap : (V.subgroupOf K).map K.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVK
  have hV'T : V.subgroupOf K ≤ T₁ := by
    intro v hv
    obtain ⟨t, ht, htv⟩ := hVT (Subgroup.mem_subgroupOf.mp hv)
    rwa [← Subtype.ext htv]
  have hV'1 : V.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hV
    rw [← hVmap, hbot, Subgroup.map_bot]
  have hNV' : Subgroup.normalizer ((T₁ : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K) := fun n hn =>
    Subgroup.le_normalizer_comap K.subtype (hNV (coe_mem_normalizer_map hn))
  rcases hF.centralizer _ hV'T hV'1 hNV' with hall | ⟨hcen, hne⟩
  · refine Or.inl fun y hy => ?_
    obtain ⟨t, ht, hyt⟩ := hall (MulAut.conjNormal y) fun v hv => by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply,
        ← Subgroup.mem_centralizer_iff.mp hy (v : Y) (Subgroup.mem_subgroupOf.mp hv)]
      group
    have e : y = (t : Y) * ((t : Y)⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨t, ht, rfl⟩ (inv_mul_mem_centralizer_of_conjNormal_eq hyt)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [← hVmap, hcen, map_subtype_centerOf]
    · rw [← map_subtype_centerOf]
      exact fun h => hne (Subgroup.map_injective K.subtype_injective h)

theorem le_sup_of_oneSmallFacts {K : Subgroup Y} [K.Normal]
    (T₁ : Sylow p K) (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (hF : OneSmallFacts p K T₁) {W : Subgroup Y} (hW : IsPGroup p W) (hWR : W ≤ Rb)
    (hWn : K ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ≤
      Subgroup.normalizer (W : Set Y)) :
    W ≤ ((Rb : Subgroup Y) ⊓ K) ⊔ ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)) := by
  have key : ∀ (f : MulAut K) (t : K), f * MulAut.conj t * f⁻¹ = MulAut.conj (f t) := by
    intro f t
    ext k
    simp [MulAut.mul_apply, MulAut.inv_def]
  have hmem : W.map (MulAut.conjNormal (H := K)) ≤
      (T₁ : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
    refine hF.pSubgroup_le _ (hW.map _) ?_ ?_
    · refine le_normalizer_of_forall_mul_mul_inv_mem ?_
      rintro _ ⟨w, hw, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [key]
      have htY : (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
      have hwt : w * t * w⁻¹ ∈ (T₁ : Subgroup K).map K.subtype := by
        rw [hT₁]
        exact ⟨Rb.mul_mem (Rb.mul_mem (hWR hw) htY.1) (Rb.inv_mem (hWR hw)),
          ‹K.Normal›.conj_mem _ htY.2 w⟩
      obtain ⟨s, hs, hsw⟩ := hwt
      refine ⟨s, hs, congrArg MulAut.conj (Subtype.ext ?_)⟩
      rw [MulAut.conjNormal_apply]
      exact hsw
    · rintro _ ⟨n, hn, rfl⟩
      have hnW : (n : Y) ∈ Subgroup.normalizer (W : Set Y) :=
        hWn (hT₁ ▸ coe_mem_normalizer_map hn)
      rw [← MulAut.conjNormal_val]
      exact Subgroup.le_normalizer_map _ ⟨n, hnW, rfl⟩
  intro w hw
  obtain ⟨t, ht, hwt⟩ := hmem ⟨w, hw, rfl⟩
  have htR : (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
  have e : w = (t : Y) * ((t : Y)⁻¹ * w) := by group
  rw [e]
  exact Subgroup.mul_mem_sup htR ⟨Rb.mul_mem (Rb.inv_mem htR.1) (hWR hw),
    inv_mul_mem_centralizer_of_conjNormal_eq hwt.symm⟩

theorem le_inf_centralizer_of_inf_eq_bot (hp : p.Prime) {K : Subgroup Y} [K.Normal]
    (T₀ : Subgroup Y) (hT₀K : T₀ ≤ K ⊓ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) :
      Set Y)) (hT₀p : p.Coprime (Nat.card T₀))
    (hT₀C : (Rb : Subgroup Y) ⊓ K ⊓ Subgroup.centralizer (T₀ : Set Y) = ⊥)
    {W : Subgroup Y} (hW : IsPGroup p W)
    (hWle : W ≤ ((Rb : Subgroup Y) ⊓ K) ⊔ ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)))
    (hWn : T₀ ≤ Subgroup.normalizer (W : Set Y)) (hWT : W ⊓ K = ⊥) (hWR : W ≤ Rb) :
    W ≤ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdec : ∀ w ∈ W, ∃ t ∈ (Rb : Subgroup Y) ⊓ K, ∃ c ∈ Subgroup.centralizer (K : Set Y),
      t * c = w := by
    intro w hw
    have hw' : w ∈ ((((Rb : Subgroup Y) ⊓ K) ⊔ Subgroup.centralizer (K : Set Y) : Subgroup Y) :
        Set Y) := (hWle.trans (sup_le_sup_left inf_le_right _)) hw
    rw [Subgroup.mul_normal] at hw'
    obtain ⟨t, ht, c, hc, htc⟩ := hw'
    exact ⟨t, ht, c, hc, htc⟩
  have hcomm : ⁅W, T₀⁆ = ⊥ := by
    rw [eq_bot_iff, ← hWT, Subgroup.commutator_le]
    intro w hw a ha
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 := (Subgroup.mem_normalizer_iff.mp (hWn ha) (w⁻¹)).mp (W.inv_mem hw)
      simpa [mul_assoc] using W.mul_mem hw h1
    · obtain ⟨t, ht, c, hc, rfl⟩ := hdec w hw
      rw [commutatorElement_def, mul_mul_commutator_eq hc (hT₀K ha).1]
      exact K.mul_mem ht.2 (‹K.Normal›.conj_mem _ (K.inv_mem ht.2) a)
  have hfix : W ⊓ Subgroup.centralizer (T₀ : Set Y) ≤ Subgroup.centralizer (K : Set Y) := by
    rintro w ⟨hw, hwA⟩
    obtain ⟨t, ht, c, hc, rfl⟩ := hdec w hw
    have htA : t ∈ Subgroup.centralizer (T₀ : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : a * (t * c) = t * c * a := Subgroup.mem_centralizer_iff.mp hwA a ha
      have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc a (hT₀K ha).1
      have h2 : a * t * c = t * a * c := by
        calc a * t * c = a * (t * c) := by group
          _ = t * c * a := h1
          _ = t * (c * a) := by group
          _ = t * (a * c) := by rw [← hca]
          _ = t * a * c := by group
      exact mul_right_cancel h2
    have ht1 : t = 1 := by
      have hmem : t ∈ (Rb : Subgroup Y) ⊓ K ⊓ Subgroup.centralizer (T₀ : Set Y) := ⟨ht, htA⟩
      rwa [hT₀C, Subgroup.mem_bot] at hmem
    rw [ht1, one_mul]
    exact hc
  have hcop : Nat.Coprime (Nat.card T₀) (Nat.card W) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
    rw [hk]
    exact Nat.Coprime.pow_right k hT₀p.symm
  have hsolv : Group.IsSolvable W := by
    have := hW.isNilpotent
    infer_instance
  have hle := le_commutator_sup_inf_centralizer_of_coprime hWn hcop hsolv
  rw [hcomm, bot_sup_eq] at hle
  exact le_inf hWR (hle.trans hfix)

theorem le_inf_centralizer_of_torus (hp : p.Prime) {K : Subgroup Y} [K.Normal]
    (T₁ : Sylow p K) (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (T₀ : Subgroup K) (hT₀N : T₀ ≤ Subgroup.normalizer ((T₁ : Subgroup K) : Set K))
    (hT₀p : p.Coprime (Nat.card T₀))
    (hT₀C : (T₁ : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥)
    {W : Subgroup Y} (hW : IsPGroup p W)
    (hWle : W ≤ ((Rb : Subgroup Y) ⊓ K) ⊔ ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)))
    (hWn : K ⊓ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (W : Set Y)) (hWT : W ⊓ K = ⊥) (hWR : W ≤ Rb) :
    W ≤ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) := by
  have hAKN : T₀.map K.subtype ≤
      K ⊓ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hT₁]
    exact coe_mem_normalizer_map (hT₀N ha)
  have hAp : p.Coprime (Nat.card (T₀.map K.subtype)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hT₀p
  have hAC : (Rb : Subgroup Y) ⊓ K ⊓
      Subgroup.centralizer ((T₀.map K.subtype : Subgroup Y) : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨ht, htA⟩
    rw [← hT₁] at ht
    obtain ⟨t₁, ht₁, rfl⟩ := ht
    have hmem : t₁ ∈ (T₁ : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) :=
      ⟨ht₁, Subgroup.mem_centralizer_iff.mpr fun s hs =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp htA _ ⟨s, hs, rfl⟩)⟩
    rw [hT₀C, Subgroup.mem_bot] at hmem
    rw [hmem, Subgroup.mem_bot]
    rfl
  exact le_inf_centralizer_of_inf_eq_bot hp _ hAKN hAp hAC hW hWle (hAKN.trans hWn) hWT hWR

end Small

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.commutator_nclIn_le (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) :
    ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H :=
  hd.toCore.commutator_nclIn_le h3 h84 hD2 hY

theorem D1OneSmallData.d1MapPCore_facts (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) :
    IsPGroup p (d1MapPCore p M H) ∧
      d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∧
      K ⊓ Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      (pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ ↔
        d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥) :=
  hd.toCore.d1MapPCore_facts h3 h84 hD2

theorem D1OneSmallData.inf_le_sup_glbPrimeCore (h3 : D1PhaseThree p P M H R)
    (hd : D1OneSmallData p P M H R Rbar K)
    (hC : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    pCoreCentralizerPreimage p M ⊓ H ≤ R ⊔ GLBPrimeCore p H :=
  hd.toCore.inf_le_sup_glbPrimeCore h3 hC

theorem D1OneSmallData.inf_eq_glbCore_of_exc (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hE : (p = 3 ∧ IsLinThreeFour K) ∨ (p = 5 ∧ IsFi22 K)) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      (d1X0 p M H).subgroupOf K = GLBCore p 1 (T₁ : Subgroup K) ∧
      ∀ N : Subgroup K, N ≤ GLBCore p 1 (T₁ : Subgroup K) →
        (N.subgroupOf (GLBCore p 1 (T₁ : Subgroup K))).Normal → p.Coprime (Nat.card N) →
          N = ⊥ := by
  obtain ⟨T, hT, -, -, -, -, hΓ, hΓX₀⟩ := hd.exists_sylow
  obtain ⟨hmax, hcore⟩ := hUE K p hE T hΓ
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hΓsub : GLBCore p 1 (T : Subgroup K) ≤ (d1X0 p M H).subgroupOf K :=
    fun k hk => hΓX₀ ⟨k, hk, rfl⟩
  refine ⟨T, hT, ?_, hcore⟩
  rcases hmax _ hΓsub with h | h
  · exact h
  · exact absurd (fun x hx => (show (⟨x, hx⟩ : K) ∈ (d1X0 p M H).subgroupOf K from
      h ▸ Subgroup.mem_top _)) hKX₀

theorem D1OneSmallData.toPhaseThree_of_exc (hUE : KFactUPrimeExc)
    (hd : D1OneSmallData p P M H R Rbar K) (hE : (p = 3 ∧ IsLinThreeFour K) ∨ (p = 5 ∧ IsFi22 K))
    (hU2 : ¬ D1SmallU2Fails p M H K) : D1PhaseThree p P M H R := by
  obtain ⟨T, -, hY, hcore⟩ := hd.inf_eq_glbCore_of_exc hUE hE
  refine hd.cfg.toPhaseThree fun L hL hLX₀ => ?_
  by_cases hLK : L = K
  swap
  · exact absurd (hd.cfg.red.le_of_ne_component hL hd.comp hLK
      (two_le_pRank_of_isPGroup_not_isCyclic hd.cfg.red.prime hd.cfg.red.ne_two
        (Rbar.isPGroup'.to_le inf_le_left) hd.noncyclic)) hLX₀
  subst hLK
  have hmem : ∀ k : L, k ∈ GLBCore p 1 (T : Subgroup L) →
      (k : H ⧸ primeComplementCore (G := H) p) ∈ d1X0 p M H ⊓ L :=
    fun k hk => ⟨(by rw [hY]; exact hk : k ∈ (d1X0 p M H).subgroupOf L), k.2⟩
  refine ⟨fun N hN hNn hNp => ?_, fun w hwN hwC => ?_⟩
  · have hNL : N ≤ L := hN.trans inf_le_right
    have hN'Γ : N.subgroupOf L ≤ GLBCore p 1 (T : Subgroup L) := fun k hk => by
      rw [← hY]
      exact (hN hk).1
    have hN'n : ((N.subgroupOf L).subgroupOf (GLBCore p 1 (T : Subgroup L))).Normal :=
      ⟨fun n hn g => hNn.conj_mem ⟨_, hmem _ n.2⟩ hn ⟨_, hmem _ g.2⟩⟩
    have hcard : Nat.card (N.subgroupOf L) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
    have hbot := hcore _ hN'Γ hN'n (hcard ▸ hNp)
    rw [← Subgroup.map_subgroupOf_eq_of_le hNL, hbot, Subgroup.map_bot]
  · by_contra hwK
    exact hU2 ⟨w, hwN, hwC, hwK⟩

end Config

end CFSG.AGLEmbedding
